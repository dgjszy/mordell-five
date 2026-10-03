import Mordell.Directional
import Mordell.Pentagon

namespace Mordell

noncomputable def force (z : Configuration) (i : Fin 5) : ℂ :=
  ∑ j, if j = i then 0 else 1 / (z i - z j)

noncomputable def impulse (i : Fin 5) : Configuration :=
  fun j => if j = i then 1 else 0

theorem innerMoment_impulse (z : Configuration) (i : Fin 5) :
    innerMoment z (impulse i) = star (z i) := by
  simp [innerMoment, impulse]

theorem pairSum_impulse (z : Configuration) (i : Fin 5) :
    pairSum z (impulse i) = force z i := by
  unfold pairSum force impulse
  rw [pairs_explicit]
  repeat' (rw [Finset.sum_insert] <;> try decide)
  simp only [Finset.sum_singleton]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  fin_cases i
  · norm_num [Fin.ext_iff, Fin.succ]
    change (z 0 - z 2)⁻¹ + ((z 0 - z 3)⁻¹ + ((z 0 - z 4)⁻¹)) = (z 0 - z 2)⁻¹ + ((z 0 - z 3)⁻¹ + ((z 0 - z 4)⁻¹))
    rfl
  · norm_num [Fin.ext_iff, Fin.succ]
    change -1 / (z 0 - z 1) + ((z 1 - z 2)⁻¹ + ((z 1 - z 3)⁻¹ + ((z 1 - z 4)⁻¹))) = (z 1 - z 0)⁻¹ + ((z 1 - z 2)⁻¹ + ((z 1 - z 3)⁻¹ + ((z 1 - z 4)⁻¹)))
    rw [show z 1 - z 0 = -(z 0 - z 1) from by ring]
    simp only [inv_neg, neg_div, one_div]
  · norm_num [Fin.ext_iff, Fin.succ]
    change -1 / (z 0 - z 2) + (-1 / (z 1 - z 2) + ((z 2 - z 3)⁻¹ + ((z 2 - z 4)⁻¹))) = (z 2 - z 0)⁻¹ + ((z 2 - z 1)⁻¹ + ((z 2 - z 3)⁻¹ + ((z 2 - z 4)⁻¹)))
    rw [show z 2 - z 0 = -(z 0 - z 2) from by ring, show z 2 - z 1 = -(z 1 - z 2) from by ring]
    simp only [inv_neg, neg_div, one_div]
  · norm_num [Fin.ext_iff, Fin.succ]
    change -1 / (z 0 - z 3) + (-1 / (z 1 - z 3) + (-1 / (z 2 - z 3) + ((z 3 - z 4)⁻¹))) = (z 3 - z 0)⁻¹ + ((z 3 - z 1)⁻¹ + ((z 3 - z 2)⁻¹ + ((z 3 - z 4)⁻¹)))
    rw [show z 3 - z 0 = -(z 0 - z 3) from by ring, show z 3 - z 1 = -(z 1 - z 3) from by ring, show z 3 - z 2 = -(z 2 - z 3) from by ring]
    simp only [inv_neg, neg_div, one_div]
  · norm_num [Fin.ext_iff, Fin.succ]
    change -1 / (z 0 - z 4) + (-1 / (z 1 - z 4) + (-1 / (z 2 - z 4) + (-1 / (z 3 - z 4)))) = (z 4 - z 0)⁻¹ + ((z 4 - z 1)⁻¹ + ((z 4 - z 2)⁻¹ + ((z 4 - z 3)⁻¹)))
    rw [show z 4 - z 0 = -(z 0 - z 4) from by ring, show z 4 - z 1 = -(z 1 - z 4) from by ring, show z 4 - z 2 = -(z 2 - z 4) from by ring, show z 4 - z 3 = -(z 3 - z 4) from by ring]
    simp only [inv_neg, neg_div, one_div]

theorem global_maximum_force {z : Configuration} (hz : IsGlobalMaximum z)
    (i : Fin 5) : force z i = 2 * star (z i) := by
  simpa only [pairSum_impulse, innerMoment_impulse] using
    global_maximum_pairSum hz (impulse i)

end Mordell
