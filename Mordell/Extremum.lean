import Mordell.Compactness
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Mordell

def IsGlobalMaximum (z : Configuration) : Prop :=
  normSum z = 5 ∧ ∀ w : Configuration, normSum w = 5 → discriminant w ≤ discriminant z

theorem discriminant_pos_of_injective {z : Configuration} (hz : Function.Injective z) :
    0 < discriminant z := by
  apply Finset.prod_pos
  intro p hp
  apply Complex.normSq_pos.mpr
  intro h
  have hij := hz (sub_eq_zero.mp h)
  have hlt : p.1 < p.2 := (Finset.mem_filter.mp hp).2
  exact (ne_of_lt hlt) hij

theorem injective_of_discriminant_pos {z : Configuration} (hz : 0 < discriminant z) :
    Function.Injective z := by
  intro i j hij
  by_contra hne
  have hzero : discriminant z = 0 := by
    unfold discriminant
    apply Finset.prod_eq_zero_iff.mpr
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · refine ⟨(i,j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩, ?_⟩
      simp [hij]
    · refine ⟨(j,i), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt⟩, ?_⟩
      simp [hij]
  exact (ne_of_gt hz) hzero

noncomputable def positiveWitness : Configuration := ![1, -1, Complex.I, -Complex.I, ⟨3/5,4/5⟩]

theorem positiveWitness_constraint : normSum positiveWitness = 5 := by
  rw [normSum_expand]
  change Complex.normSq (1 : ℂ) + Complex.normSq (-1 : ℂ) +
    Complex.normSq Complex.I + Complex.normSq (-Complex.I) +
    Complex.normSq (⟨3/5,4/5⟩ : ℂ) = 5
  norm_num [Complex.normSq_apply]

theorem positiveWitness_injective : Function.Injective positiveWitness := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    norm_num [positiveWitness, Complex.ext_iff] at *

theorem global_maximum_positive {z : Configuration} (hz : IsGlobalMaximum z) :
    0 < discriminant z :=
  (discriminant_pos_of_injective positiveWitness_injective).trans_le
    (hz.2 _ positiveWitness_constraint)

theorem normSum_pos_of_discriminant_pos {z : Configuration} (hz : 0 < discriminant z) :
    0 < normSum z := by
  by_contra hp
  have hn : normSum z = 0 := le_antisymm (not_lt.mp hp) (normSum_nonneg z)
  have hall : ∀ i, z i = 0 := by
    intro i
    apply Complex.normSq_eq_zero.mp
    exact le_antisymm (by simpa [hn] using normSq_le_normSum z i)
      (Complex.normSq_nonneg _)
  have hi := injective_of_discriminant_pos hz
  have h01 : (0 : Fin 5) = 1 := hi (by rw [hall, hall])
  exact (by decide : (0 : Fin 5) ≠ 1) h01

/-- Translation and rescaling strictly improve an uncentered positive maximum. -/
theorem global_maximum_centered {z : Configuration} (hz : IsGlobalMaximum z) :
    ∑ i, z i = 0 := by
  have hd := global_maximum_positive hz
  have ht : discriminant (center z) = discriminant z := discriminant_translate z _
  have hs : 0 < normSum (center z) := normSum_pos_of_discriminant_pos (ht ▸ hd)
  by_contra hsum
  have hcent : 0 < Complex.normSq (∑ i, z i) := Complex.normSq_pos.mpr hsum
  have hs5 : normSum (center z) < 5 := by rw [normSum_center, hz.1]; linarith
  let a : ℝ := Real.sqrt (5 / normSum (center z))
  have ha2 : a * a = 5 / normSum (center z) := by
    exact Real.mul_self_sqrt (le_of_lt (div_pos (by norm_num) hs))
  have hn : Complex.normSq (a : ℂ) = 5 / normSum (center z) := by
    rw [Complex.normSq_ofReal, ha2]
  have hnorm : normSum (fun i => (a : ℂ) * center z i) = 5 := by
    rw [normSum_scale, hn]
    exact div_mul_cancel₀ _ (ne_of_gt hs)
  have hratio : 1 < 5 / normSum (center z) := (lt_div_iff₀ hs).mpr (by simpa using hs5)
  have hpow : 1 < (5 / normSum (center z)) ^ 10 := by
    simpa using pow_lt_pow_left₀ hratio (by norm_num : (0 : ℝ) ≤ 1) (by decide : 10 ≠ 0)
  have hmax := hz.2 _ hnorm
  rw [discriminant_scale, hn, ht] at hmax
  nlinarith [mul_lt_mul_of_pos_right hpow hd]

theorem exists_centered_distinct_global_maximum :
    ∃ z : Configuration, IsGlobalMaximum z ∧ (∑ i, z i = 0) ∧ Function.Injective z := by
  obtain ⟨z, hz, hm⟩ := exists_global_maximum
  have hmax : IsGlobalMaximum z := ⟨hz, hm⟩
  exact ⟨z, hmax, global_maximum_centered hmax,
    injective_of_discriminant_pos (global_maximum_positive hmax)⟩

end Mordell
