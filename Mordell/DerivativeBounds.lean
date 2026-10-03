import Mordell.Differentiation
import Mordell.Cover
import Mordell.Krawczyk

namespace Mordell

def Interval.absBound (a : Interval) : ℚ := max |a.lo| |a.hi|

theorem Interval.abs_le_absBound {a : Interval} {x : ℝ} (hx : a.Mem x) :
    |x| ≤ (a.absBound : ℝ) := by
  rw [abs_le]
  simp only [Interval.absBound, Rat.cast_max, Rat.cast_abs]
  constructor
  · exact (neg_le_neg (le_max_left |(a.lo : ℝ)| |(a.hi : ℝ)|)).trans
      ((neg_abs_le (a.lo : ℝ)).trans hx.1)
  · exact hx.2.trans ((le_abs_self (a.hi : ℝ)).trans (le_max_right _ _))

noncomputable def matrixMap {n : ℕ} (Y : Fin n → Fin n → ℚ) :
    (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi fun i => ∑ j, (Y i j : ℝ) • ContinuousLinearMap.proj j

theorem matrixMap_apply {n : ℕ} (Y : Fin n → Fin n → ℚ) (v : Fin n → ℝ) (i : Fin n) :
    matrixMap Y v i = ∑ j, (Y i j : ℝ) * v j := by simp [matrixMap]

noncomputable def systemMap {n : ℕ} (f : Fin n → Expr n) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => (f i).eval x

noncomputable def systemDerivative {n : ℕ} (f : Fin n → Expr n) (x : Fin n → ℝ) :
    (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi fun i => (f i).derivative x

theorem system_hasFDerivAt {n : ℕ} (f : Fin n → Expr n) (x : Fin n → ℝ) :
    HasFDerivAt (systemMap f) (systemDerivative f x) x :=
  hasFDerivAt_pi.mpr fun i => (f i).hasFDerivAt_eval x

def krawczykEntry {n : ℕ} (f : Fin n → Expr n) (Y : Fin n → Fin n → ℚ)
    (i j : Fin n) : Expr n :=
  Expr.sub (.const (if i = j then 1 else 0))
    (Expr.sumFin fun k => .mul (.const (Y i k)) ((f k).diff j))

theorem krawczykDerivative_apply {n : ℕ} (f : Fin n → Expr n)
    (Y : Fin n → Fin n → ℚ) (x v : Fin n → ℝ) (i : Fin n) :
    (ContinuousLinearMap.id ℝ (Fin n → ℝ) - (matrixMap Y).comp (systemDerivative f x)) v i =
      ∑ j, (krawczykEntry f Y i j).eval x * v j := by
  simp only [ContinuousLinearMap.sub_apply, Pi.sub_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.comp_apply, matrixMap_apply, systemDerivative,
    ContinuousLinearMap.pi_apply, Expr.derivative_apply]
  simp only [krawczykEntry, Expr.sub, Expr.eval, Expr.eval_sumFin, apply_ite,
    Rat.cast_one, Rat.cast_zero, sub_eq_add_neg, add_mul, neg_mul, Finset.sum_add_distrib,
    Finset.sum_neg_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    if_true]
  congr 1
  simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

theorem opNorm_le_of_rows {n : ℕ} (A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (a : Fin n → Fin n → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (ha : ∀ v i, A v i = ∑ j, a i j * v j)
    (hrow : ∀ i, ∑ j, |a i j| ≤ c) : ‖A‖ ≤ c := by
  apply A.opNorm_le_bound hc
  intro v
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hc (norm_nonneg v))).mpr
  intro i
  rw [ha]
  calc
    ‖∑ j, a i j * v j‖ ≤ ∑ j, ‖a i j * v j‖ := norm_sum_le _ _
    _ = ∑ j, |a i j| * ‖v j‖ := by simp [norm_mul, Real.norm_eq_abs]
    _ ≤ ∑ j, |a i j| * ‖v‖ := Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_left (norm_le_pi_norm v j) (abs_nonneg _)
    _ = (∑ j, |a i j|) * ‖v‖ := by rw [Finset.sum_mul]
    _ ≤ c * ‖v‖ := mul_le_mul_of_nonneg_right (hrow i) (norm_nonneg v)

def localUniqueCheck {n : ℕ} (f : Fin n → Expr n) (Y : Fin n → Fin n → ℚ)
    (b : Box n) (c : ℚ) : Bool :=
  decide (0 ≤ c ∧ c < 1 ∧ ∀ i, ∑ j, ((krawczykEntry f Y i j).range b).absBound ≤ c)

theorem Box.convex {n : ℕ} (b : Box n) : Convex ℝ {x : Fin n → ℝ | b.Mem x} := by
  have he : {x : Fin n → ℝ | b.Mem x} =
      Set.pi Set.univ (fun i => Set.Icc ((b i).lo : ℝ) ((b i).hi : ℝ)) := by
    ext x
    simp only [Set.mem_setOf_eq, Box.Mem, Interval.Mem, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
  rw [he]
  exact convex_pi fun _ _ => convex_Icc _ _

/-- The computable rational row bounds imply uniqueness of every real zero in the entire box. -/
theorem localUniqueCheck_sound {n : ℕ} (f : Fin n → Expr n) (Y : Fin n → Fin n → ℚ)
    (b : Box n) (c : ℚ) (hcheck : localUniqueCheck f Y b c = true)
    {x y : Fin n → ℝ} (hx : b.Mem x) (hy : b.Mem y)
    (hfx : ∀ i, (f i).eval x = 0) (hfy : ∀ i, (f i).eval y = 0) : x = y := by
  have hh : 0 ≤ c ∧ c < 1 ∧ ∀ i, ∑ j, ((krawczykEntry f Y i j).range b).absBound ≤ c :=
    of_decide_eq_true hcheck
  have hc : (0 : ℝ) ≤ c := by exact_mod_cast hh.1
  have hc1 : (c : ℝ) < 1 := by exact_mod_cast hh.2.1
  apply zeros_unique_of_derivative_bound (systemMap f) (matrixMap Y)
    (systemDerivative f) {x | b.Mem x} c b.convex hc1
    (fun p _ => system_hasFDerivAt f p) _ hx hy (funext hfx) (funext hfy)
  intro p hp
  apply opNorm_le_of_rows _ (fun i j => (krawczykEntry f Y i j).eval p) c hc
    (fun v i => krawczykDerivative_apply f Y p v i)
  intro i
  calc
    _ ≤ ∑ j, ((((krawczykEntry f Y i j).range b).absBound : ℚ) : ℝ) :=
      Finset.sum_le_sum fun j _ => Interval.abs_le_absBound
        ((krawczykEntry f Y i j).eval_mem_range b p hp)
    _ ≤ (c : ℝ) := by exact_mod_cast hh.2.2 i

end Mordell
