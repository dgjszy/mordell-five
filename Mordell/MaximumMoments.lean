import Mordell.Directional
import Mordell.LocalRoot
import Mordell.Pentagon

namespace Mordell

theorem innerMoment_power (z : Configuration) (k : ℕ) :
    innerMoment z (fun i => z i ^ (k+1)) = mixedMoment z k := by
  unfold innerMoment mixedMoment
  apply Finset.sum_congr rfl
  intro i _
  dsimp only
  rw [Complex.normSq_eq_conj_mul_self, Complex.star_def, pow_succ]
  ring

theorem pairSum_power_two {z : Configuration} (hz : Function.Injective z) :
    pairSum z (fun i => z i ^ 2) = 4 * powerSum z 1 := by
  have hterm (a b : Fin 5) (hab : a ≠ b) :
      (z a ^ 2 - z b ^ 2) / (z a - z b) = z a + z b := by
    have hn : z a - z b ≠ 0 := sub_ne_zero.mpr (hz.ne hab)
    field_simp
    ring
  unfold pairSum
  dsimp only
  rw [pairs_explicit]
  repeat' (rw [Finset.sum_insert] <;> try decide)
  simp only [Finset.sum_singleton]
  rw [hterm 0 1 (by decide), hterm 0 2 (by decide), hterm 0 3 (by decide),
    hterm 0 4 (by decide), hterm 1 2 (by decide), hterm 1 3 (by decide),
    hterm 1 4 (by decide), hterm 2 3 (by decide), hterm 2 4 (by decide),
    hterm 3 4 (by decide), powerSum_expand]
  ring

theorem pairSum_power_three {z : Configuration} (hz : Function.Injective z) :
    pairSum z (fun i => z i ^ 3) = (7 * powerSum z 2 + powerSum z 1 ^ 2) / 2 := by
  have hterm (a b : Fin 5) (hab : a ≠ b) :
      (z a ^ 3 - z b ^ 3) / (z a - z b) = z a ^ 2 + z a * z b + z b ^ 2 := by
    have hn : z a - z b ≠ 0 := sub_ne_zero.mpr (hz.ne hab)
    field_simp
    ring
  unfold pairSum
  dsimp only
  rw [pairs_explicit]
  repeat' (rw [Finset.sum_insert] <;> try decide)
  simp only [Finset.sum_singleton]
  rw [hterm 0 1 (by decide), hterm 0 2 (by decide), hterm 0 3 (by decide),
    hterm 0 4 (by decide), hterm 1 2 (by decide), hterm 1 3 (by decide),
    hterm 1 4 (by decide), hterm 2 3 (by decide), hterm 2 4 (by decide),
    hterm 3 4 (by decide), powerSum_expand, powerSum_expand]
  ring

theorem pairSum_power_four {z : Configuration} (hz : Function.Injective z) :
    pairSum z (fun i => z i ^ 4) = 3 * powerSum z 3 + powerSum z 1 * powerSum z 2 := by
  have hterm (a b : Fin 5) (hab : a ≠ b) :
      (z a ^ 4 - z b ^ 4) / (z a - z b) =
        z a ^ 3 + z a ^ 2 * z b + z a * z b ^ 2 + z b ^ 3 := by
    have hn : z a - z b ≠ 0 := sub_ne_zero.mpr (hz.ne hab)
    field_simp
    ring
  unfold pairSum
  dsimp only
  rw [pairs_explicit]
  repeat' (rw [Finset.sum_insert] <;> try decide)
  simp only [Finset.sum_singleton]
  rw [hterm 0 1 (by decide), hterm 0 2 (by decide), hterm 0 3 (by decide),
    hterm 0 4 (by decide), hterm 1 2 (by decide), hterm 1 3 (by decide),
    hterm 1 4 (by decide), hterm 2 3 (by decide), hterm 2 4 (by decide),
    hterm 3 4 (by decide), powerSum_expand, powerSum_expand, powerSum_expand]
  ring

theorem global_maximum_moments {z : Configuration} (hz : IsGlobalMaximum z) :
    mixedMoment z 1 = 0 ∧ 4 * mixedMoment z 2 = 7 * powerSum z 2 ∧
      2 * mixedMoment z 3 = 3 * powerSum z 3 := by
  have hinj := injective_of_discriminant_pos (global_maximum_positive hz)
  have hcenter : powerSum z 1 = 0 := by
    simpa [powerSum] using global_maximum_centered hz
  have h2 := global_maximum_pairSum hz (fun i => z i ^ 2)
  have h3 := global_maximum_pairSum hz (fun i => z i ^ 3)
  have h4 := global_maximum_pairSum hz (fun i => z i ^ 4)
  rw [pairSum_power_two hinj, hcenter, innerMoment_power z 1] at h2
  rw [pairSum_power_three hinj, hcenter, innerMoment_power z 2] at h3
  rw [pairSum_power_four hinj, hcenter, innerMoment_power z 3] at h4
  constructor
  · linear_combination (-1/2 : ℂ) * h2
  constructor
  · linear_combination (-2 : ℂ) * h3
  · linear_combination (-1 : ℂ) * h4

theorem global_maximum_normalized_moments {z : Configuration} (hz : IsGlobalMaximum z) :
    NormalizedMomentSystem z := by
  obtain ⟨h1,h2,h3⟩ := global_maximum_moments hz
  refine ⟨h1, ?_, ?_⟩
  · simp only [hz.1, Complex.ofReal_ofNat]
    linear_combination (5 : ℂ) * h2
  · simp only [hz.1, Complex.ofReal_ofNat]
    linear_combination (5 : ℂ) * h3

end Mordell
