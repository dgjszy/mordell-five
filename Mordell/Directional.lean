import Mordell.Stationarity
import Mathlib.Analysis.Calculus.Deriv.Mul

namespace Mordell

noncomputable def motion (z h : Configuration) (t : ℝ) : Configuration :=
  fun i => z i + (t : ℂ) * h i

noncomputable def pairSum (z h : Configuration) : ℂ :=
  ∑ p ∈ pairs, (h p.1 - h p.2) / (z p.1 - z p.2)

noncomputable def innerMoment (z h : Configuration) : ℂ := ∑ i, star (z i) * h i

theorem hasDerivAt_relative_product {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℝ → ℝ) (r : ι → ℝ)
    (h : ∀ i ∈ s, HasDerivAt (f i) (f i 0 * r i) 0) :
    HasDerivAt (fun t => ∏ i ∈ s, f i t)
      ((∏ i ∈ s, f i 0) * ∑ i ∈ s, r i) 0 := by
  induction s using Finset.induction_on with
  | empty => simpa using hasDerivAt_const (0 : ℝ) (1 : ℝ)
  | @insert a s ha ih =>
    have hs := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    have hd := (h a (Finset.mem_insert_self a s)).mul hs
    simpa only [Finset.prod_insert ha, Finset.sum_insert ha] using
      hd.congr_deriv (by ring)

theorem hasDerivAt_normSq_motion (d h : ℂ) :
    HasDerivAt (fun t : ℝ => Complex.normSq (d + (t : ℂ) * h))
      (2 * (d.re * h.re + d.im * h.im)) 0 := by
  have hr := ((hasDerivAt_id (0 : ℝ)).mul_const h.re).const_add d.re
  have hi := ((hasDerivAt_id (0 : ℝ)).mul_const h.im).const_add d.im
  convert (hr.mul hr).add (hi.mul hi) using 1
  · funext t
    simp [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im]
  · simp
    ring

theorem normSq_relative_derivative (d h : ℂ) :
    2 * (d.re * h.re + d.im * h.im) =
      Complex.normSq d * (2 * (h / d).re) := by
  by_cases hd : d = 0
  · simp [hd]
  · have hn : Complex.normSq d ≠ 0 := mt Complex.normSq_eq_zero.mp hd
    rw [Complex.div_re]
    field_simp

theorem hasDerivAt_normSum_motion (z h : Configuration) :
    HasDerivAt (fun t => normSum (motion z h t)) (2 * (innerMoment z h).re) 0 := by
  have hd := HasDerivAt.sum (u := Finset.univ)
    (fun i _ => hasDerivAt_normSq_motion (z i) (h i))
  convert hd using 1
  simp [innerMoment, Complex.mul_re, ← Finset.mul_sum]

theorem hasDerivAt_discriminant_motion (z h : Configuration) :
    HasDerivAt (fun t => discriminant (motion z h t))
      (discriminant z * (2 * (pairSum z h).re)) 0 := by
  let f := fun p : Fin 5 × Fin 5 => fun t : ℝ =>
    Complex.normSq ((z p.1 - z p.2) + (t : ℂ) * (h p.1 - h p.2))
  let r := fun p : Fin 5 × Fin 5 =>
    2 * ((h p.1 - h p.2) / (z p.1 - z p.2)).re
  have hd := hasDerivAt_relative_product pairs f r (by
    intro p _
    convert hasDerivAt_normSq_motion (z p.1 - z p.2) (h p.1 - h p.2) using 1
    simp only [f, r, Complex.ofReal_zero, zero_mul, add_zero]
    exact (normSq_relative_derivative _ _).symm)
  convert hd using 1
  · funext t
    apply Finset.prod_congr rfl
    intro p _
    congr 1
    dsimp [motion]
    ring
  · simp [f, r, discriminant, pairSum, ← Finset.mul_sum]

theorem global_maximum_pairSum_real {z : Configuration} (hz : IsGlobalMaximum z)
    (h : Configuration) : (pairSum z h).re = 2 * (innerMoment z h).re := by
  have he := global_maximum_stationarity hz (motion z h) (by ext i; simp [motion])
    _ _ (hasDerivAt_normSum_motion z h) (hasDerivAt_discriminant_motion z h)
  have hp := global_maximum_positive hz
  nlinarith

theorem pairSum_mul (z h : Configuration) (c : ℂ) :
    pairSum z (fun i => c * h i) = c * pairSum z h := by
  unfold pairSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  ring

theorem innerMoment_mul (z h : Configuration) (c : ℂ) :
    innerMoment z (fun i => c * h i) = c * innerMoment z h := by
  unfold innerMoment
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem global_maximum_pairSum {z : Configuration} (hz : IsGlobalMaximum z)
    (h : Configuration) : pairSum z h = 2 * innerMoment z h := by
  have hre := global_maximum_pairSum_real hz h
  have him := global_maximum_pairSum_real hz (fun i => Complex.I * h i)
  rw [pairSum_mul, innerMoment_mul] at him
  apply Complex.ext
  · simpa using hre
  · simpa using him

end Mordell
