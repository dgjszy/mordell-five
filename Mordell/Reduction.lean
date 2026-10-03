import Mordell.Extremum
import Mordell.Pentagon

namespace Mordell

noncomputable def orderedDiscriminant (z : Configuration) : ℝ :=
  ∏ i, ∏ j, if i ≠ j then Complex.normSq (z i-z j) else 1

theorem orderedDiscriminant_eq_square (z : Configuration) :
    orderedDiscriminant z = discriminant z ^ 2 := by
  rw [discriminant_expand]
  unfold orderedDiscriminant
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  norm_num only [ne_eq, Fin.succ, Fin.ext_iff, Fin.val_zero, Fin.val_mk, ite_true, ite_false, mul_one, one_mul]
  change (Complex.normSq (z 0-z 1) * (Complex.normSq (z 0-z 2) * (Complex.normSq (z 0-z 3) * (Complex.normSq (z 0-z 4))))) * ((Complex.normSq (z 1-z 0) * (Complex.normSq (z 1-z 2) * (Complex.normSq (z 1-z 3) * (Complex.normSq (z 1-z 4))))) * ((Complex.normSq (z 2-z 0) * (Complex.normSq (z 2-z 1) * (Complex.normSq (z 2-z 3) * (Complex.normSq (z 2-z 4))))) * ((Complex.normSq (z 3-z 0) * (Complex.normSq (z 3-z 1) * (Complex.normSq (z 3-z 2) * (Complex.normSq (z 3-z 4))))) * ((Complex.normSq (z 4-z 0) * (Complex.normSq (z 4-z 1) * (Complex.normSq (z 4-z 2) * (Complex.normSq (z 4-z 3))))))))) = (Complex.normSq (z 0-z 1) * Complex.normSq (z 0-z 2) * Complex.normSq (z 0-z 3) * Complex.normSq (z 0-z 4) * Complex.normSq (z 1-z 2) * Complex.normSq (z 1-z 3) * Complex.normSq (z 1-z 4) * Complex.normSq (z 2-z 3) * Complex.normSq (z 2-z 4) * Complex.normSq (z 3-z 4)) ^ 2
  rw [normSq_sub_comm (z 1) (z 0), normSq_sub_comm (z 2) (z 0),
    normSq_sub_comm (z 3) (z 0), normSq_sub_comm (z 4) (z 0),
    normSq_sub_comm (z 2) (z 1), normSq_sub_comm (z 3) (z 1),
    normSq_sub_comm (z 4) (z 1), normSq_sub_comm (z 3) (z 2),
    normSq_sub_comm (z 4) (z 2), normSq_sub_comm (z 4) (z 3)]
  ring

theorem normSum_relabel (z : Configuration) (σ : Equiv.Perm (Fin 5)) :
    normSum (fun i => z (σ i)) = normSum z :=
  Equiv.sum_comp σ (fun i => Complex.normSq (z i))

theorem orderedDiscriminant_relabel (z : Configuration) (σ : Equiv.Perm (Fin 5)) :
    orderedDiscriminant (fun i => z (σ i)) = orderedDiscriminant z := by
  unfold orderedDiscriminant
  apply Fintype.prod_equiv σ
  intro i
  rw [← Equiv.prod_comp σ (fun j => if σ i ≠ j then Complex.normSq (z (σ i)-z j) else 1)]
  simp only [σ.injective.ne_iff]

theorem discriminant_relabel (z : Configuration) (σ : Equiv.Perm (Fin 5)) :
    discriminant (fun i => z (σ i)) = discriminant z := by
  have h := orderedDiscriminant_relabel z σ
  rw [orderedDiscriminant_eq_square, orderedDiscriminant_eq_square] at h
  nlinarith [discriminant_nonneg (fun i => z (σ i)), discriminant_nonneg z]

theorem regular_pentagon_sharp {z : Configuration} (hz : RegularPentagon z) :
    normSum z = 5 ∧ discriminant z = 3125 := by
  obtain ⟨u, ω, hu, hω, σ, hz⟩ := hz
  have he : z = fun i => u * ω ^ (σ i).val := funext hz
  rw [he]
  constructor
  · rw [normSum_scale, hu, one_mul, normSum_relabel (fun i : Fin 5 => ω^i.val) σ]
    exact power_pentagon_constraint hω
  · rw [discriminant_scale, hu, one_pow, one_mul, discriminant_relabel (fun i : Fin 5 => ω^i.val) σ]
    exact power_pentagon_discriminant hω

theorem global_maximum_lower_bound {z : Configuration} (hz : IsGlobalMaximum z) :
    3125 ≤ discriminant z := by
  obtain ⟨w, hw, hd⟩ := exists_sharp_configuration
  exact hd ▸ hz.2 w hw

/-- The remaining mathematical target. This is a definition, not an axiom or theorem. -/
def MaximaClassification : Prop :=
  ∀ z : Configuration, IsGlobalMaximum z → RegularPentagon z

/-- Closing MaximaClassification suffices for the exact original bound and equality cases. -/
theorem original_of_maxima_classification (hclass : MaximaClassification) : OriginalStatement := by
  intro z hz
  obtain ⟨w, hw, hm⟩ := exists_global_maximum
  have hmax : IsGlobalMaximum w := ⟨hw, hm⟩
  have hwsharp := (regular_pentagon_sharp (hclass w hmax)).2
  have hbound : discriminant z ≤ 3125 := hwsharp ▸ hm z hz
  refine ⟨hbound, ?_⟩
  constructor
  · intro heq
    apply hclass z
    refine ⟨hz, fun v hv => ?_⟩
    rw [heq]
    exact hwsharp ▸ hm v hv
  · intro hregular
    exact (regular_pentagon_sharp hregular).2

end Mordell
