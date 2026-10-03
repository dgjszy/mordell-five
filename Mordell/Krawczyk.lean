import Mathlib.Analysis.Calculus.MeanValue

namespace Mordell

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def krawczykMap (F : E → E) (Y : E →L[ℝ] E) (x : E) : E := x - Y (F x)

theorem krawczykMap_fixed_of_zero (F : E → E) (Y : E →L[ℝ] E) (x : E)
    (hx : F x = 0) : krawczykMap F Y x = x := by simp [krawczykMap, hx]

theorem krawczykMap_hasFDerivAt (F : E → E) (Y : E →L[ℝ] E)
    (x : E) (A : E →L[ℝ] E) (hF : HasFDerivAt F A x) :
    HasFDerivAt (krawczykMap F Y) (ContinuousLinearMap.id ℝ E - Y.comp A) x := by
  exact (hasFDerivAt_id x).sub (Y.hasFDerivAt.comp x hF)

/-- A norm bound below one excludes two distinct zeros; no inverse assumption on Y is needed. -/
theorem zeros_unique_of_derivative_bound (F : E → E) (Y : E →L[ℝ] E)
    (A : E → E →L[ℝ] E) (s : Set E) (c : ℝ)
    (hs : Convex ℝ s) (hc : c < 1)
    (hF : ∀ x ∈ s, HasFDerivAt F (A x) x)
    (hbound : ∀ x ∈ s, ‖ContinuousLinearMap.id ℝ E - Y.comp (A x)‖ ≤ c)
    {x y : E} (hx : x ∈ s) (hy : y ∈ s) (hfx : F x = 0) (hfy : F y = 0) : x = y := by
  have hk : ∀ p ∈ s, HasFDerivWithinAt (krawczykMap F Y)
      (ContinuousLinearMap.id ℝ E - Y.comp (A p)) s p :=
    fun p hp => (krawczykMap_hasFDerivAt F Y p (A p) (hF p hp)).hasFDerivWithinAt
  have hm := hs.norm_image_sub_le_of_norm_hasFDerivWithin_le hk hbound hx hy
  rw [krawczykMap_fixed_of_zero F Y x hfx, krawczykMap_fixed_of_zero F Y y hfy] at hm
  have hn : ‖y-x‖ = 0 := by nlinarith [norm_nonneg (y-x)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hn)).symm

/-- Every zero in the convex box lies in the Krawczyk ball around the image of its midpoint. -/
theorem zero_in_krawczyk_ball (F : E → E) (Y : E →L[ℝ] E)
    (A : E → E →L[ℝ] E) (s : Set E) (c r : ℝ) (m : E)
    (hs : Convex ℝ s) (hc : 0 ≤ c) (hm : m ∈ s)
    (hF : ∀ x ∈ s, HasFDerivAt F (A x) x)
    (hbound : ∀ x ∈ s, ‖ContinuousLinearMap.id ℝ E - Y.comp (A x)‖ ≤ c)
    {x : E} (hx : x ∈ s) (hfx : F x = 0) (hr : ‖x-m‖ ≤ r) :
    ‖x-krawczykMap F Y m‖ ≤ c*r := by
  have hk : ∀ p ∈ s, HasFDerivWithinAt (krawczykMap F Y)
      (ContinuousLinearMap.id ℝ E - Y.comp (A p)) s p :=
    fun p hp => (krawczykMap_hasFDerivAt F Y p (A p) (hF p hp)).hasFDerivWithinAt
  have h := hs.norm_image_sub_le_of_norm_hasFDerivWithin_le hk hbound hm hx
  rw [krawczykMap_fixed_of_zero F Y x hfx] at h
  exact h.trans (mul_le_mul_of_nonneg_left hr hc)

end Mordell
