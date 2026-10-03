import Mordell.CoefficientData
import Mathlib.FieldTheory.IsAlgClosed.Basic

namespace Mordell
open Polynomial

 theorem quintic_scale {z : Configuration} {a b c d : ℂ}
    (hp : rootPolynomial z = quintic a b c d) (t : ℂ) :
    rootPolynomial (fun i => t*z i) = quintic (a*t^2) (b*t^3) (c*t^4) (d*t^5) := by
  ext n
  rw [rootPolynomial_scale_coeff, hp]
  rw [ResultantAlgebra.quintic_coefficient,ResultantAlgebra.quintic_coefficient]
  by_cases hn : n ≤ 5
  · interval_cases n <;> norm_num <;> ring
  · have hn0 : n ≠ 0 := by omega
    have hn1 : n ≠ 1 := by omega
    have hn2 : n ≠ 2 := by omega
    have hn3 : n ≠ 3 := by omega
    have hn5 : n ≠ 5 := by omega
    simp [hn0,hn1,hn2,hn3,hn5]

 theorem normalize_nonzero (a : ℂ) (ha : a ≠ 0) (n : ℕ) (hn : 0 < n) :
    ∃ t : ℂ, t ≠ 0 ∧ a*t^n = 1 := by
  obtain ⟨t,ht⟩ := IsAlgClosed.exists_pow_nat_eq a⁻¹ hn
  have ht0 : t ≠ 0 := by
    intro he
    rw [he,zero_pow (by omega)] at ht
    exact (inv_ne_zero ha) ht.symm
  exact ⟨t,ht0,by rw [ht,mul_inv_cancel₀ ha]⟩

end Mordell
