import Mordell.RootPolynomial
import Mathlib.RingTheory.Polynomial.ScaleRoots

namespace Mordell
open Polynomial

noncomputable def quintic (a b c d : ℂ) : ℂ[X] :=
  X^5 + C a * X^3 + C b * X^2 + C c * X + C d

theorem rootPolynomial_monic (z : Configuration) : (rootPolynomial z).Monic := by
  exact monic_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)

theorem rootPolynomial_natDegree (z : Configuration) : (rootPolynomial z).natDegree = 5 := by
  unfold rootPolynomial
  rw [natDegree_prod_of_monic (Finset.univ : Finset (Fin 5)) (fun i => X - C (z i)) (fun i _ => monic_X_sub_C (z i))]
  simp

theorem rootPolynomial_coeff_four (z : Configuration) :
    (rootPolynomial z).coeff 4 = -∑ i, z i := by
  simpa only [rootPolynomial, Finset.card_univ, Fintype.card_fin] using
    prod_X_sub_C_coeff_card_pred Finset.univ z (by decide)

theorem rootPolynomial_quintic {z : Configuration} (hz : ∑ i, z i = 0) :
    rootPolynomial z = quintic ((rootPolynomial z).coeff 3)
      ((rootPolynomial z).coeff 2) ((rootPolynomial z).coeff 1)
      ((rootPolynomial z).coeff 0) := by
  have h5 : (rootPolynomial z).coeff 5 = 1 := by
    rw [← rootPolynomial_natDegree z]
    exact (rootPolynomial_monic z).coeff_natDegree
  have h4 : (rootPolynomial z).coeff 4 = 0 := by rw [rootPolynomial_coeff_four, hz, neg_zero]
  ext n
  by_cases hn : n ≤ 5
  · interval_cases n <;> simp [quintic, h5, h4]
  · have hn' : (rootPolynomial z).natDegree < n := by rw [rootPolynomial_natDegree]; omega
    rw [coeff_eq_zero_of_natDegree_lt hn']
    simp only [quintic, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
    have hn0 : n ≠ 0 := by omega
    have hn1 : n ≠ 1 := by omega
    have hn2 : n ≠ 2 := by omega
    have hn3 : n ≠ 3 := by omega
    have hn5 : n ≠ 5 := by omega
    simp [hn0, hn1, hn2, hn3, hn5, Ne.symm hn1]

theorem rootPolynomial_scale (z : Configuration) (t : ℂ) :
    rootPolynomial (fun i => t * z i) = (rootPolynomial z).scaleRoots t := by
  unfold rootPolynomial
  induction (Finset.univ : Finset (Fin 5)) using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      mul_scaleRoots_of_noZeroDivisors, X_sub_C_scaleRoots, ih]
    simp only [mul_comm (z a) t]

theorem rootPolynomial_scale_coeff (z : Configuration) (t : ℂ) (j : ℕ) :
    (rootPolynomial (fun i => t * z i)).coeff j =
      (rootPolynomial z).coeff j * t^(5-j) := by
  rw [rootPolynomial_scale, coeff_scaleRoots, rootPolynomial_natDegree]

end Mordell
