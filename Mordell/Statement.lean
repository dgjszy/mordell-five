import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

namespace Mordell

/-- Five labelled complex points. -/
abbrev Configuration := Fin 5 → ℂ

/-- The original constraint, with no centering or symmetry hypothesis. -/
def normSum (z : Configuration) : ℝ := ∑ i, Complex.normSq (z i)

/-- Each unordered pair occurs exactly once. -/
def pairs : Finset (Fin 5 × Fin 5) := Finset.univ.filter (fun p => p.1 < p.2)

def discriminant (z : Configuration) : ℝ :=
  ∏ p ∈ pairs, Complex.normSq (z p.1 - z p.2)

/-- A unit regular pentagon, with arbitrary rotation and labelling. -/
def RegularPentagon (z : Configuration) : Prop :=
  ∃ u ω : ℂ, Complex.normSq u = 1 ∧ IsPrimitiveRoot ω 5 ∧
    ∃ σ : Equiv.Perm (Fin 5), ∀ i, z i = u * ω ^ (σ i).val

/-- Exact requested theorem contract; this definition is not a proof. -/
def OriginalStatement : Prop :=
  ∀ z : Configuration, normSum z = 5 →
    discriminant z ≤ 3125 ∧
      (discriminant z = 3125 ↔ RegularPentagon z)

theorem pairs_card : pairs.card = 10 := by decide

theorem discriminant_nonneg (z : Configuration) : 0 ≤ discriminant z := by
  unfold discriminant
  exact Finset.prod_nonneg fun _ _ => Complex.normSq_nonneg _

theorem normSum_nonneg (z : Configuration) : 0 ≤ normSum z := by
  exact Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

end Mordell
