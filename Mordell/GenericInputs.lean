import Mordell.CoefficientData
import Mordell.Branches

namespace Mordell
open ResultantAlgebra

set_option maxHeartbeats 0

theorem generic_delta (b c k : ℂ) :
    delta 1 b c (b*k) = Branches.delta (b^2) c k := by
  dsimp only [delta, Branches.delta]
  ring

theorem generic_r3 (b c k : ℂ) :
    r3 1 b c (b*k) = Branches.r3 (b^2) c k := by
  dsimp only [r3, Branches.r3]
  ring

theorem generic_r2 (b c k : ℂ) :
    r2 1 b c (b*k) = b * Branches.r2Factor (b^2) c k := by
  dsimp only [r2, Branches.r2Factor]
  ring

theorem generic_equation2 (ss b c k : ℂ) :
    s2 1 b c (b*k) = 4*b*Elimination.g0 ss k c (b^2) := by
  dsimp only [s2, Elimination.g0]
  ring

theorem generic_equation1 (ss b c k : ℂ) :
    s1 1 b c (b*k) - 6*r3 1 b c (b*k) = 24*Elimination.g1 ss k c (b^2) := by
  dsimp only [s1, r3, Elimination.g1]
  ring

theorem generic_equation0 (ss b c k : ℂ) :
    s0 1 b c (b*k) - 2*r2 1 b c (b*k) = 16*b*Elimination.g2 ss k c (b^2) := by
  dsimp only [s0, r2, Elimination.g2]
  ring

theorem generic_saturation (ss b c k : ℂ) :
    Elimination.g3 ss k c (b^2) = ss * b^2 * Branches.delta (b^2) c k - 1 := by
  dsimp only [Elimination.g3, Branches.delta]
  ring

theorem generic_inputs {b c k : ℂ} {κ D : ℝ}
    (h : CoefficientData 1 b c (b*k) κ D) (hb : b ≠ 0) :
    ∃ ss : ℂ, Elimination.g0 ss k c (b^2) = 0 ∧
      Elimination.g1 ss k c (b^2) = 0 ∧ Elimination.g2 ss k c (b^2) = 0 ∧
      Elimination.g3 ss k c (b^2) = 0 := by
  let ss := (b^2 * Branches.delta (b^2) c k)⁻¹
  have hd : Branches.delta (b^2) c k ≠ 0 := by
    rw [← generic_delta]
    exact h.delta_ne
  refine ⟨ss, ?_, ?_, ?_, ?_⟩
  · have he := h.equation2
    rw [generic_equation2 ss] at he
    exact (mul_eq_zero.mp he).resolve_left (mul_ne_zero (by norm_num) hb)
  · have he : s1 1 b c (b*k) - 6*r3 1 b c (b*k) = 0 := sub_eq_zero.mpr h.equation1
    rw [generic_equation1 ss] at he
    exact (mul_eq_zero.mp he).resolve_left (by norm_num)
  · have he : s0 1 b c (b*k) - 2*r2 1 b c (b*k) = 0 := sub_eq_zero.mpr h.equation0
    rw [generic_equation0 ss] at he
    exact (mul_eq_zero.mp he).resolve_left (mul_ne_zero (by norm_num) hb)
  · rw [generic_saturation]
    dsimp only [ss]
    have hn := mul_ne_zero (pow_ne_zero 2 hb) hd
    rw [mul_assoc, inv_mul_cancel₀ hn, sub_self]

end Mordell
