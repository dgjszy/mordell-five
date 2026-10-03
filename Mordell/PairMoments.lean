import Mordell.StationaryPair

namespace Mordell

theorem pairSum_sum (z : Configuration) {ι : Type*} (s : Finset ι)
    (h : ι → Configuration) :
    pairSum z (fun i => ∑ j ∈ s, h j i) = ∑ j ∈ s, pairSum z (h j) := by
  unfold pairSum
  simp_rw [← Finset.sum_sub_distrib, Finset.sum_div]
  rw [Finset.sum_comm]

theorem pairSum_force (z h : Configuration) :
    pairSum z h = ∑ i, h i * force z i := by
  have he : h = fun i => ∑ j : Fin 5, h j * impulse j i := by
    ext i
    simp [impulse]
  rw [he, pairSum_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [pairSum_mul, pairSum_impulse]
  simp [impulse]

theorem stationaryPair_pairSum {x y : Configuration} (h : StationaryPair x y)
    (v : Configuration) : pairSum x v = 2 * ∑ i, y i * v i := by
  rw [pairSum_force, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [h.2.2.2.2.1 i]
  ring

theorem pairSum_identity {z : Configuration} (hz : Function.Injective z) :
    pairSum z z = 10 := by
  unfold pairSum
  have he : ∀ p ∈ pairs, (z p.1 - z p.2) / (z p.1 - z p.2) = 1 := by
    intro p hp
    apply div_self
    exact sub_ne_zero.mpr (hz.ne (ne_of_lt (Finset.mem_filter.mp hp).2))
  norm_num [Finset.sum_congr rfl he, Finset.sum_const, pairs_card, nsmul_eq_mul]

theorem stationaryPair_moments {x y : Configuration} (h : StationaryPair x y) :
    (∑ i, x i * y i = 5) ∧
    (∑ i, x i * y i^2 = 0) ∧
    (4 * ∑ i, x i * y i^3 = 7 * powerSum y 2) ∧
    (2 * ∑ i, x i * y i^4 = 3 * powerSum y 3) := by
  have hy : StationaryPair y x :=
    ⟨h.2.1, h.1, h.2.2.2.1, h.2.2.1, h.2.2.2.2.2, h.2.2.2.2.1⟩
  have hp1 : powerSum y 1 = 0 := by simpa [powerSum] using h.2.2.2.1
  have h1 := stationaryPair_pairSum hy y
  rw [pairSum_identity h.2.1] at h1
  have h2 := stationaryPair_pairSum hy (fun i => y i^2)
  rw [pairSum_power_two h.2.1, hp1] at h2
  have h3 := stationaryPair_pairSum hy (fun i => y i^3)
  rw [pairSum_power_three h.2.1, hp1] at h3
  have h4 := stationaryPair_pairSum hy (fun i => y i^4)
  rw [pairSum_power_four h.2.1, hp1] at h4
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination (-1/2 : ℂ) * h1
  · linear_combination (-1/2 : ℂ) * h2
  · linear_combination (-2 : ℂ) * h3
  · linear_combination (-1 : ℂ) * h4

end Mordell
