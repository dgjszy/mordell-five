import Mordell.LocalCertificate

namespace Mordell

noncomputable def goldenP : ℝ := (Real.sqrt 5 - 1)/4
noncomputable def goldenQ : ℝ := -(Real.sqrt 5 + 1)/4
noncomputable def goldenA : ℝ := Real.sqrt (1-goldenP^2)
noncomputable def goldenB : ℝ := Real.sqrt (1-goldenQ^2)
noncomputable def goldenCoordinates : Fin 6 → ℝ :=
  ![goldenP,goldenQ,goldenQ,-goldenA,-goldenB,goldenB]
noncomputable def goldenConfiguration : Configuration :=
  ![1,⟨goldenP,-goldenA⟩,⟨goldenQ,-goldenB⟩,⟨goldenQ,goldenB⟩,⟨goldenP,goldenA⟩]

theorem golden_r_bounds : (2236/1000 : ℝ) ≤ Real.sqrt 5 ∧ Real.sqrt 5 ≤ 2237/1000 := by
  have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have hn := Real.sqrt_nonneg (5 : ℝ)
  constructor <;> nlinarith

theorem golden_pq : goldenP + goldenQ = -1/2 ∧ goldenP*goldenQ = -1/4 := by
  have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  dsimp [goldenP, goldenQ]
  constructor
  · ring
  · nlinarith

theorem golden_ab_sq : goldenA^2 = 1-goldenP^2 ∧ goldenB^2 = 1-goldenQ^2 := by
  have hr := golden_r_bounds
  have hp : 0 ≤ 1-goldenP^2 := by dsimp [goldenP]; nlinarith [hr.1,hr.2]
  have hq : 0 ≤ 1-goldenQ^2 := by dsimp [goldenQ]; nlinarith [hr.1,hr.2]
  exact ⟨Real.sq_sqrt hp, Real.sq_sqrt hq⟩

theorem golden_values : goldenConfiguration 0 = 1 ∧
    goldenConfiguration 1 = ⟨goldenP,-goldenA⟩ ∧
    goldenConfiguration 2 = ⟨goldenQ,-goldenB⟩ ∧
    goldenConfiguration 3 = ⟨goldenQ,goldenB⟩ ∧
    goldenConfiguration 4 = ⟨goldenP,goldenA⟩ := ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem golden_coordinate_configuration : coordinateConfiguration goldenCoordinates = goldenConfiguration := by
  funext i
  fin_cases i
  · simpa only [Rat.cast_one] using CExpr.eval_const goldenCoordinates 1
  · rfl
  · rfl
  · rfl
  · apply Complex.ext
    · change ((-1 : ℚ) : ℝ) - goldenP - goldenQ - goldenQ = goldenP
      norm_num
      linarith [golden_pq.1]
    · change ((0 : ℚ) : ℝ) - -goldenA - -goldenB - goldenB = goldenA
      norm_num

theorem golden_unit : ∀ i, Complex.normSq (goldenConfiguration i) = 1 := by
  intro i
  fin_cases i <;> norm_num [goldenConfiguration, Complex.normSq_apply] <;>
    nlinarith [golden_ab_sq.1,golden_ab_sq.2]

theorem powerSum_expand (z : Configuration) (k : ℕ) :
    powerSum z k = z 0^k + z 1^k + z 2^k + z 3^k + z 4^k := by
  simp [powerSum, Fin.sum_univ_succ]
  ring

theorem golden_powerSums : powerSum goldenConfiguration 1 = 0 ∧
    powerSum goldenConfiguration 2 = 0 ∧ powerSum goldenConfiguration 3 = 0 := by
  have hs := golden_pq.1
  have hp := golden_pq.2
  have h2 : goldenP^2 + goldenQ^2 = 3/4 := by nlinarith [sq_nonneg (goldenP+goldenQ)]
  have h3 : goldenP^3 + goldenQ^3 = -1/2 := by
    calc
      _ = (goldenP+goldenQ)*(goldenP^2+goldenQ^2-goldenP*goldenQ) := by ring
      _ = -1/2 := by rw [show goldenP^2+goldenQ^2-goldenP*goldenQ = 1 from by linarith]; rw [hs]; ring
  have ha := golden_ab_sq.1
  have hb := golden_ab_sq.2
  refine ⟨?_,?_,?_⟩
  all_goals
    rw [powerSum_expand]
    simp only [golden_values.1,golden_values.2.1,golden_values.2.2.1,
      golden_values.2.2.2.1,golden_values.2.2.2.2]
    apply Complex.ext <;> norm_num [pow_succ, Complex.mul_re, Complex.mul_im]
  all_goals
    ring_nf
    try simp only [ha,hb]
    all_goals nlinarith [hs,h2,h3]

theorem golden_moment_equations : ∀ i, (momentEquations i).eval goldenCoordinates = 0 := by
  apply (momentEquations_correspondence goldenCoordinates).mpr
  rw [golden_coordinate_configuration]
  have hm : ∀ k, mixedMoment goldenConfiguration k = powerSum goldenConfiguration k := by
    intro k
    simp [mixedMoment, powerSum, golden_unit]
  simp only [NormalizedMomentSystem, hm, golden_powerSums.1, golden_powerSums.2.1,
    golden_powerSums.2.2, mul_zero, sub_zero, and_self]

theorem golden_in_pentagonBox : pentagonBox.Mem goldenCoordinates := by
  have hr := golden_r_bounds
  have hp : (309/1000 : ℝ) ≤ goldenP ∧ goldenP ≤ 30925/100000 := by
    dsimp [goldenP]; constructor <;> linarith [hr.1,hr.2]
  have hq : (-80925/100000 : ℝ) ≤ goldenQ ∧ goldenQ ≤ -809/1000 := by
    dsimp [goldenQ]; constructor <;> linarith [hr.1,hr.2]
  have ha : (9508/10000 : ℝ) ≤ goldenA ∧ goldenA ≤ 9513/10000 := by
    have han : 0 ≤ goldenA := Real.sqrt_nonneg _
    constructor <;> nlinarith [golden_ab_sq.1,hp.1,hp.2]
  have hb : (5874/10000 : ℝ) ≤ goldenB ∧ goldenB ≤ 588/1000 := by
    have hbn : 0 ≤ goldenB := Real.sqrt_nonneg _
    constructor <;> nlinarith [golden_ab_sq.2,hq.1,hq.2]
  intro i
  fin_cases i <;> norm_num [pentagonBox, goldenCoordinates, Interval.Mem] <;>
    constructor <;> linarith [hp.1,hp.2,hq.1,hq.2,ha.1,ha.2,hb.1,hb.2]

/-- Every real zero in the isolating box equals the exact radical configuration. -/
theorem pentagon_local_zero_identified {x : Fin 6 → ℝ} (hx : pentagonBox.Mem x)
    (hf : ∀ i, (momentEquations i).eval x = 0) : x = goldenCoordinates :=
  pentagon_local_moment_unique hx golden_in_pentagonBox hf golden_moment_equations

end Mordell
