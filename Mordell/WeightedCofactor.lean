import Mordell.Cofactor

namespace Mordell
open Polynomial

noncomputable def weightedCofactor (z h : Configuration) (Y : ℂ) : ℂ :=
  ∑ i, h i * (rootCofactor z i).eval Y

theorem weightedCofactor_formula {z h : Configuration} (hz : ∑ i, z i = 0)
    (h0 : ∑ i, h i = 0) (h1 : ∑ i, h i * z i = 20)
    (h2 : ∑ i, h i * z i^2 = 0)
    (h3 : ∑ i, h i * z i^3 = -14 * (rootPolynomial z).coeff 3)
    (h4 : ∑ i, h i * z i^4 = -18 * (rootPolynomial z).coeff 2) (Y : ℂ) :
    weightedCofactor z h Y = 20*Y^3 +
      6*(rootPolynomial z).coeff 3*Y + 2*(rootPolynomial z).coeff 2 := by
  have he : weightedCofactor z h Y =
      (∑ i, h i)*Y^4 + (∑ i, h i*z i)*Y^3 +
      ((∑ i, h i*z i^2) + (rootPolynomial z).coeff 3*(∑ i, h i))*Y^2 +
      ((∑ i, h i*z i^3) + (rootPolynomial z).coeff 3*(∑ i, h i*z i) +
        (rootPolynomial z).coeff 2*(∑ i, h i))*Y +
      (∑ i, h i*z i^4) + (rootPolynomial z).coeff 3*(∑ i, h i*z i^2) +
      (rootPolynomial z).coeff 2*(∑ i, h i*z i) +
      (rootPolynomial z).coeff 1*(∑ i, h i) := by
    unfold weightedCofactor
    simp_rw [rootCofactor_quintic hz]
    simp only [quinticCofactor, eval_add, eval_mul, eval_pow, eval_X, eval_C]
    simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he, h0, h1, h2, h3, h4]
  ring

theorem stationaryPair_weightedCofactor {x y : Configuration} (h : StationaryPair x y)
    (Y : ℂ) :
    weightedCofactor (fun i => 4*y i) x Y = 20*Y^3 +
      6*(rootPolynomial (fun i => 4*y i)).coeff 3*Y +
      2*(rootPolynomial (fun i => 4*y i)).coeff 2 := by
  have hy := h.2.2.2.1
  obtain ⟨hm1,hm2,hm3,hm4⟩ := stationaryPair_moments h
  have hw : (∑ i, 4*y i) = 0 := by rw [← Finset.mul_sum, hy, mul_zero]
  apply weightedCofactor_formula hw h.2.2.1
  · calc
      (∑ i, x i * (4*y i)) = 4 * ∑ i, x i*y i := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
      _ = 20 := by rw [hm1]; norm_num
  · calc
      (∑ i, x i * (4*y i)^2) = 16 * ∑ i, x i*y i^2 := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
      _ = 0 := by rw [hm2]; norm_num
  · have hn := coefficient_power_two y
    rw [hy] at hn
    rw [rootPolynomial_scale_coeff]
    simp only [Nat.reduceSub]
    have he : (∑ i, x i * (4*y i)^3) = 64 * ∑ i, x i*y i^3 := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
    rw [he]
    linear_combination (16 : ℂ) * hm3 + (112 : ℂ) * hn
  · have hn := coefficient_power_three y
    rw [hy] at hn
    rw [rootPolynomial_scale_coeff]
    simp only [Nat.reduceSub]
    have he : (∑ i, x i * (4*y i)^4) = 256 * ∑ i, x i*y i^4 := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
    rw [he]
    linear_combination (128 : ℂ) * hm4 + (384 : ℂ) * hn

end Mordell
