import Mordell.Extremum
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow

namespace Mordell

theorem discriminant_zero_of_normSum_zero {w : Configuration} (hw : normSum w = 0) :
    discriminant w = 0 := by
  have hall : ∀ i, w i = 0 := by
    intro i
    apply Complex.normSq_eq_zero.mp
    exact le_antisymm (by simpa [hw] using normSq_le_normSum w i)
      (Complex.normSq_nonneg _)
  have he : w = fun _ => 0 := funext hall
  rw [he]
  simp [discriminant, Finset.prod_const, pairs_card]

/-- A global maximum bounds the homogeneous polynomial on every configuration, even at zero. -/
theorem global_maximum_polynomial_envelope {z : Configuration} (hz : IsGlobalMaximum z)
    (w : Configuration) :
    (5 : ℝ)^10 * discriminant w ≤ discriminant z * normSum w ^ 10 := by
  rcases (normSum_nonneg w).eq_or_lt with hs | hs
  · rw [← hs, discriminant_zero_of_normSum_zero hs.symm]
    norm_num
  · let a : ℝ := Real.sqrt (5 / normSum w)
    have hn : Complex.normSq (a : ℂ) = 5 / normSum w := by
      rw [Complex.normSq_ofReal]
      exact Real.mul_self_sqrt (le_of_lt (div_pos (by norm_num) hs))
    have hconstraint : normSum (fun i => (a : ℂ) * w i) = 5 := by
      rw [normSum_scale, hn]
      exact div_mul_cancel₀ _ (ne_of_gt hs)
    have h := hz.2 _ hconstraint
    rw [discriminant_scale, hn, div_pow, div_mul_eq_mul_div] at h
    exact (div_le_iff₀ (pow_pos hs 10)).mp h

/-- Fermat's theorem applied to the polynomial envelope gives exact first-order stationarity. -/
theorem global_maximum_stationarity {z : Configuration} (hz : IsGlobalMaximum z)
    (w : ℝ → Configuration) (hw : w 0 = z) (s' d' : ℝ)
    (hs : HasDerivAt (fun t => normSum (w t)) s' 0)
    (hd : HasDerivAt (fun t => discriminant (w t)) d' 0) :
    5*d' = 10*discriminant z*s' := by
  let H : ℝ → ℝ := fun t => discriminant z * normSum (w t)^10 - 5^10 * discriminant (w t)
  have hzero : H 0 = 0 := by dsimp [H]; rw [hw, hz.1]; ring
  have hmin : IsLocalMin H 0 := by
    apply Filter.Eventually.of_forall
    intro t
    rw [hzero]
    exact sub_nonneg.mpr (global_maximum_polynomial_envelope hz (w t))
  have hderiv := ((hs.pow 10).const_mul (discriminant z)).sub (hd.const_mul (5^10))
  have heq := hmin.hasDerivAt_eq_zero hderiv
  norm_num [hw, hz.1] at heq
  nlinarith

end Mordell
