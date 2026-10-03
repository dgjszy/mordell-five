import Mordell.PairMoments

namespace Mordell
open Polynomial

noncomputable def quinticCofactor (a b c r : ℂ) : ℂ[X] :=
  X^4 + C r * X^3 + C (r^2+a) * X^2 + C (r^3+a*r+b) * X +
    C (r^4+a*r^2+b*r+c)

theorem quintic_division (a b c d r : ℂ) :
    quintic a b c d = (X-C r) * quinticCofactor a b c r +
      C ((quintic a b c d).eval r) := by
  simp only [quintic, quinticCofactor, eval_add, eval_mul, eval_pow,
    eval_X, eval_C, map_add, map_mul, map_pow]
  ring

theorem rootCofactor_quintic {z : Configuration} (hz : ∑ i, z i = 0)
    (i : Fin 5) : rootCofactor z i = quinticCofactor
      ((rootPolynomial z).coeff 3) ((rootPolynomial z).coeff 2)
      ((rootPolynomial z).coeff 1) (z i) := by
  apply mul_left_cancel₀ ((monic_X_sub_C (z i)).ne_zero)
  rw [← rootPolynomial_factor]
  have he := quintic_division ((rootPolynomial z).coeff 3)
    ((rootPolynomial z).coeff 2) ((rootPolynomial z).coeff 1)
    ((rootPolynomial z).coeff 0) (z i)
  rw [← rootPolynomial_quintic hz, rootPolynomial_eval, C_0, add_zero] at he
  exact he

theorem rootPolynomial_expand (z : Configuration) :
    rootPolynomial z = (X-C (z 0))*((X-C (z 1))*((X-C (z 2))*
      ((X-C (z 3))*(X-C (z 4))))) := by
  simp only [rootPolynomial, Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
  rfl

theorem coefficient_power_two (z : Configuration) :
    2 * (rootPolynomial z).coeff 3 = (∑ i, z i)^2 - powerSum z 2 := by
  rw [rootPolynomial_expand, sum_expand, powerSum_expand]
  norm_num [coeff_mul, coeff_sub, coeff_X, coeff_C, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ]
  ring

theorem coefficient_power_three (z : Configuration) :
    3 * (rootPolynomial z).coeff 2 =
      -(rootPolynomial z).coeff 3 * (∑ i, z i) +
      (∑ i, z i) * powerSum z 2 - powerSum z 3 := by
  rw [rootPolynomial_expand, sum_expand, powerSum_expand, powerSum_expand]
  norm_num [coeff_mul, coeff_sub, coeff_X, coeff_C, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ]
  ring

end Mordell
