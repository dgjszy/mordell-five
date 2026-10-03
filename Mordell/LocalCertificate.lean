import Mordell.LocalData

set_option maxRecDepth 10000
set_option maxHeartbeats 3000000
namespace Mordell
theorem pentagon_local_check : localUniqueCheck momentEquations pentagonPreconditioner pentagonBox (3/4) = true := by
  decide +kernel

/-- At most one zero of the exact six moment polynomials lies in the original isolating box. -/
theorem pentagon_local_moment_unique {x y : Fin 6 → ℝ}
    (hx : pentagonBox.Mem x) (hy : pentagonBox.Mem y)
    (hfx : ∀ i, (momentEquations i).eval x = 0)
    (hfy : ∀ i, (momentEquations i).eval y = 0) : x = y :=
  localUniqueCheck_sound momentEquations pentagonPreconditioner pentagonBox (3/4)
    pentagon_local_check hx hy hfx hfy

end Mordell
