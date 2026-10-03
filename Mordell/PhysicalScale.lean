import Mordell.ResultantBridge

namespace Mordell
open Polynomial

noncomputable def physicalScale (t : ℂ) : ℝ := (Complex.normSq t)⁻¹

theorem physicalScale_pos {t : ℂ} (ht : t ≠ 0) : 0 < physicalScale t :=
  inv_pos.mpr (Complex.normSq_pos.mpr ht)

theorem dualScale_physical (z : Configuration) {t : ℂ} (ht : t ≠ 0) (i : Fin 5) :
    dualScale z t i = (physicalScale t : ℂ) * star (t * z i) := by
  have hn : Complex.normSq t ≠ 0 := mt Complex.normSq_eq_zero.mp ht
  have hs : star t ≠ 0 := star_ne_zero.mpr ht
  simp only [dualScale, physicalScale, Complex.ofReal_inv, star_mul]
  rw [Complex.normSq_eq_conj_mul_self, Complex.star_def]
  have hc : (starRingEnd ℂ) t ≠ 0 := hs
  field_simp [hc]

 theorem rootPolynomial_star (z : Configuration) :
    rootPolynomial (fun i => star (z i)) = (rootPolynomial z).map (starRingEnd ℂ) := by
  simp only [rootPolynomial, Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X,
    Polynomial.map_C, starRingEnd_apply]

 theorem rootPolynomial_star_coeff (z : Configuration) (j : ℕ) :
    (rootPolynomial (fun i => star (z i))).coeff j = star ((rootPolynomial z).coeff j) := by
  rw [rootPolynomial_star, coeff_map]
  rfl

 theorem dualScale_coeff (z : Configuration) {t : ℂ} (ht : t ≠ 0) (j : ℕ) :
    (rootPolynomial (dualScale z t)).coeff j =
      star ((rootPolynomial (fun i => t*z i)).coeff j) *
        (physicalScale t : ℂ)^(5-j) := by
  have he : dualScale z t = fun i => (physicalScale t : ℂ) * star (t*z i) := by
    ext i
    exact dualScale_physical z ht i
  rw [he, rootPolynomial_scale_coeff, rootPolynomial_star_coeff]

 theorem physical_discriminant {z : Configuration} {t : ℂ} (ht : t ≠ 0) :
    physicalScale t^20 * Complex.normSq (complexDiscriminant (fun i => t*z i)) =
      discriminant z^2 := by
  rw [complexDiscriminant_normSq, discriminant_scale]
  unfold physicalScale
  have hn : Complex.normSq t ≠ 0 := mt Complex.normSq_eq_zero.mp ht
  field_simp <;> ring

end Mordell
