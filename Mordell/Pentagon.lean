import Mordell.Algebra
import Mathlib.RingTheory.RootsOfUnity.Complex

namespace Mordell

theorem pairs_explicit : pairs =
    {(0,1), (0,2), (0,3), (0,4), (1,2), (1,3), (1,4), (2,3), (2,4), (3,4)} := by
  decide

theorem discriminant_expand (z : Configuration) :
    discriminant z =
    Complex.normSq (z 0-z 1) * Complex.normSq (z 0-z 2) *
    Complex.normSq (z 0-z 3) * Complex.normSq (z 0-z 4) *
    Complex.normSq (z 1-z 2) * Complex.normSq (z 1-z 3) *
    Complex.normSq (z 1-z 4) * Complex.normSq (z 2-z 3) *
    Complex.normSq (z 2-z 4) * Complex.normSq (z 3-z 4) := by
  unfold discriminant
  rw [pairs_explicit]
  repeat' (rw [Finset.prod_insert] <;> try decide)
  simp only [Finset.prod_singleton]
  ring

theorem primitive_normSq {ω : ℂ} (hω : IsPrimitiveRoot ω 5) : Complex.normSq ω = 1 := by
  rw [Complex.normSq_eq_norm_sq, hω.norm'_eq_one (by decide)]
  norm_num

theorem primitive_power_normSq {ω : ℂ} (hω : IsPrimitiveRoot ω 5) (k : ℕ) :
    Complex.normSq (ω ^ k) = 1 := by
  rw [map_pow, primitive_normSq hω, one_pow]

theorem normSq_sub_comm (a b : ℂ) : Complex.normSq (a-b) = Complex.normSq (b-a) := by
  rw [← Complex.normSq_neg (a-b)]
  congr 1
  ring

theorem primitive_distance {ω : ℂ} (hω : IsPrimitiveRoot ω 5)
    (i j : ℕ) (hij : i ≤ j) :
    Complex.normSq (ω^i - ω^j) = Complex.normSq (1-ω^(j-i)) := by
  have hpow : ω^j = ω^i * ω^(j-i) := by
    rw [← pow_add, Nat.add_sub_of_le hij]
  rw [hpow]
  have he : ω^i - ω^i * ω^(j-i) = ω^i * (1-ω^(j-i)) := by ring
  rw [he, Complex.normSq_mul, primitive_power_normSq hω, one_mul]

theorem primitive_distance_complement {ω : ℂ} (hω : IsPrimitiveRoot ω 5)
    (k : ℕ) (hk : k ≤ 5) :
    Complex.normSq (1-ω^(5-k)) = Complex.normSq (1-ω^k) := by
  have hmul : ω^k * (1-ω^(5-k)) = ω^k-1 := by
    rw [mul_sub, mul_one, ← pow_add, Nat.add_sub_of_le hk, hω.pow_eq_one]
  have hn := congrArg Complex.normSq hmul
  rw [Complex.normSq_mul, primitive_power_normSq hω, one_mul] at hn
  exact hn.trans (normSq_sub_comm _ _)

theorem primitive_chord_product {ω : ℂ} (hω : IsPrimitiveRoot ω 5) :
    Complex.normSq (1-ω) * Complex.normSq (1-ω^2) = 5 := by
  have hgeom : 1 + ω + ω^2 + ω^3 + ω^4 = 0 := by
    have h := hω.geom_sum_eq_zero (by decide : 1 < 5)
    norm_num [Finset.sum_range_succ] at h
    linear_combination h
  have hprod : (1-ω)*(1-ω^2)*(1-ω^3)*(1-ω^4) = 5 := by
    linear_combination (ω^6 - 2*ω^5 + ω^3 + 3*ω - 4) * hgeom
  have hn := congrArg Complex.normSq hprod
  simp only [Complex.normSq_mul] at hn
  rw [show Complex.normSq (1-ω^3) = Complex.normSq (1-ω^2) from
      primitive_distance_complement hω 2 (by decide),
    show Complex.normSq (1-ω^4) = Complex.normSq (1-ω) from
      by simpa using primitive_distance_complement hω 1 (by decide)] at hn
  norm_num at hn
  nlinarith [mul_nonneg (Complex.normSq_nonneg (1-ω)) (Complex.normSq_nonneg (1-ω^2))]

theorem power_pentagon_constraint {ω : ℂ} (hω : IsPrimitiveRoot ω 5) :
    normSum (fun i : Fin 5 => ω^i.val) = 5 := by
  simp [normSum, primitive_power_normSq hω]

/-- The sharp value at every primitive fifth root, with no numerical approximation. -/
theorem power_pentagon_discriminant {ω : ℂ} (hω : IsPrimitiveRoot ω 5) :
    discriminant (fun i : Fin 5 => ω^i.val) = 3125 := by
  rw [discriminant_expand]
  change Complex.normSq (ω^0-ω^1) * Complex.normSq (ω^0-ω^2) * Complex.normSq (ω^0-ω^3) * Complex.normSq (ω^0-ω^4) * Complex.normSq (ω^1-ω^2) * Complex.normSq (ω^1-ω^3) * Complex.normSq (ω^1-ω^4) * Complex.normSq (ω^2-ω^3) * Complex.normSq (ω^2-ω^4) * Complex.normSq (ω^3-ω^4) = 3125
  rw [primitive_distance hω 0 1 (by decide),
    primitive_distance hω 0 2 (by decide), primitive_distance hω 0 3 (by decide),
    primitive_distance hω 0 4 (by decide), primitive_distance hω 1 2 (by decide),
    primitive_distance hω 1 3 (by decide), primitive_distance hω 1 4 (by decide),
    primitive_distance hω 2 3 (by decide), primitive_distance hω 2 4 (by decide),
    primitive_distance hω 3 4 (by decide)]
  norm_num only [Nat.reduceSub]
  rw [show Complex.normSq (1-ω^3) = Complex.normSq (1-ω^2) from
      primitive_distance_complement hω 2 (by decide),
    show Complex.normSq (1-ω^4) = Complex.normSq (1-ω) from
      by simpa using primitive_distance_complement hω 1 (by decide)]
  simp only [pow_one]
  have h := primitive_chord_product hω
  calc
    _ = (Complex.normSq (1-ω) * Complex.normSq (1-ω^2))^5 := by ring
    _ = 3125 := by rw [h]; norm_num

theorem exists_sharp_configuration :
    ∃ z : Configuration, normSum z = 5 ∧ discriminant z = 3125 := by
  let ω := Complex.exp (2 * Real.pi * Complex.I / 5)
  have hω : IsPrimitiveRoot ω 5 := Complex.isPrimitiveRoot_exp 5 (by decide)
  exact ⟨fun i => ω^i.val, power_pentagon_constraint hω, power_pentagon_discriminant hω⟩

end Mordell
