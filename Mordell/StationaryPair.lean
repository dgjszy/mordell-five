import Mordell.Quintic
import Mordell.MaximumMoments

namespace Mordell

noncomputable def dualScale (z : Configuration) (t : ℂ) : Configuration :=
  fun i => star (z i) / t

def StationaryPair (x y : Configuration) : Prop :=
  Function.Injective x ∧ Function.Injective y ∧
  (∑ i, x i = 0) ∧ (∑ i, y i = 0) ∧
  (∀ i, force x i = 2 * y i) ∧ (∀ i, force y i = 2 * x i)

theorem force_scale (z : Configuration) {t : ℂ} (ht : t ≠ 0) (i : Fin 5) :
    force (fun j => t * z j) i = force z i / t := by
  unfold force
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j = i
  · simp [hj]
  · simp only [if_neg hj]
    rw [← mul_sub]
    field_simp

theorem force_star (z : Configuration) (i : Fin 5) :
    force (fun j => star (z j)) i = star (force z i) := by
  unfold force
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j = i <;> simp [hj]

theorem maximum_stationaryPair {z : Configuration} (hz : IsGlobalMaximum z)
    {t : ℂ} (ht : t ≠ 0) : StationaryPair (fun i => t * z i) (dualScale z t) := by
  have hi := injective_of_discriminant_pos (global_maximum_positive hz)
  have hc := global_maximum_centered hz
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    exact hi ((mul_left_cancel₀ ht) hij)
  · intro i j hij
    apply hi
    have he : star (z i) = star (z j) := (div_left_inj' ht).mp hij
    exact star_injective he
  · rw [← Finset.mul_sum, hc, mul_zero]
  · simp only [dualScale, ← Finset.sum_div, ← star_sum, hc, star_zero, zero_div]
  · intro i
    rw [force_scale z ht, global_maximum_force hz]
    unfold dualScale
    ring
  · intro i
    have he : dualScale z t = fun j => t⁻¹ * star (z j) := by ext j; simp [dualScale, div_eq_mul_inv, mul_comm]
    rw [he, force_scale _ (inv_ne_zero ht), force_star, global_maximum_force hz]
    simp only [star_mul, star_ofNat, star_star, div_inv_eq_mul]
    ring

theorem stationaryPair_root_equation {x y : Configuration} (h : StationaryPair x y)
    (i : Fin 5) :
    (rootPolynomial x).derivative.derivative.eval (x i) =
      4 * y i * (rootPolynomial x).derivative.eval (x i) := by
  rw [rootPolynomial_second_derivative_eval h.1, h.2.2.2.2.1 i]
  ring

end Mordell
