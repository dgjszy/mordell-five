import Mordell.Algebra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact

namespace Mordell

theorem continuous_normSum : Continuous normSum := by
  unfold normSum
  exact continuous_finsetSum _ fun i _ =>
    Complex.continuous_normSq.comp (continuous_apply i)

theorem continuous_discriminant : Continuous discriminant := by
  unfold discriminant
  exact continuous_finsetProd _ fun p _ =>
    Complex.continuous_normSq.comp ((continuous_apply p.1).sub (continuous_apply p.2))

theorem normSq_le_normSum (z : Configuration) (i : Fin 5) :
    Complex.normSq (z i) ≤ normSum z := by
  exact Finset.single_le_sum (fun j _ => Complex.normSq_nonneg (z j)) (Finset.mem_univ i)

theorem isCompact_constraint : IsCompact {z : Configuration | normSum z = 5} := by
  have hc : IsClosed {z : Configuration | normSum z = 5} :=
    isClosed_eq continuous_normSum continuous_const
  apply (isCompact_closedBall (0 : Configuration) 3).of_isClosed_subset hc
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)).2
  intro i
  have h := normSq_le_normSum z i
  rw [hz, Complex.normSq_eq_norm_sq] at h
  nlinarith [norm_nonneg (z i)]

theorem constraint_nonempty : ({z : Configuration | normSum z = 5} : Set Configuration).Nonempty := by
  refine ⟨fun _ => 1, ?_⟩
  norm_num [normSum, Complex.normSq_apply]

/-- An actual maximum exists on the original, uncentered constraint set. -/
theorem exists_global_maximum :
    ∃ z : Configuration, normSum z = 5 ∧
      ∀ w : Configuration, normSum w = 5 → discriminant w ≤ discriminant z := by
  obtain ⟨z, hz, hm⟩ := isCompact_constraint.exists_isMaxOn constraint_nonempty
    continuous_discriminant.continuousOn
  exact ⟨z, hz, fun w hw => hm hw⟩

end Mordell
