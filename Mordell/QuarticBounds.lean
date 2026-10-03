import Mordell.AlgebraicBounds
import Mathlib.Analysis.Polynomial.CauchyBound
import Mathlib.Tactic.ComputeDegree

set_option maxRecDepth 10000

namespace Mordell.AlgebraicBounds
open Polynomial

noncomputable def realP1 : ℝ[X] := 125*X^4 + 7900*X^3 - 37040*X^2 + 44608*X + 512
noncomputable def realP2 : ℝ[X] := 2500*X^4 - 114000*X^3 + 338925*X^2 - 11000*X + 6912

theorem realP1_degree : realP1.natDegree = 4 := by
  unfold realP1
  compute_degree <;> norm_num

theorem realP2_degree : realP2.natDegree = 4 := by
  unfold realP2
  compute_degree <;> norm_num

theorem realP1_bound : realP1.cauchyBound < 1000 := by
  have hl : realP1.leadingCoeff = 125 := by
    rw [leadingCoeff, realP1_degree]
    norm_num [realP1, coeff_X]
  rw [cauchyBound, realP1_degree, hl]
  have hrange : Finset.range 4 = {0, 1, 2, 3} := by decide
  rw [hrange]
  apply (NNReal.coe_lt_coe).mp
  norm_num [Finset.sup_insert, realP1, coeff_X, Real.norm_eq_abs]

theorem realP2_bound : realP2.cauchyBound < 1000 := by
  have hl : realP2.leadingCoeff = 2500 := by
    rw [leadingCoeff, realP2_degree]
    norm_num [realP2, coeff_X]
  rw [cauchyBound, realP2_degree, hl]
  have hrange : Finset.range 4 = {0, 1, 2, 3} := by decide
  rw [hrange]
  apply (NNReal.coe_lt_coe).mp
  norm_num [Finset.sup_insert, realP2, coeff_X, Real.norm_eq_abs]

theorem root1_bounds (B : ℝ) (hp : p1.eval (fun _ => B) = 0) :
    -1000 ≤ B ∧ B ≤ 1000 := by
  have hr : realP1.IsRoot B := by
    simp only [p1, Expr.eval] at hp
    simp only [IsRoot.def, realP1, eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_ofNat]
    linear_combination hp
  have hn : realP1 ≠ 0 := by
    intro he
    have hd := realP1_degree
    rw [he, natDegree_zero] at hd
    norm_num at hd
  have he := hr.norm_lt_cauchyBound hn
  have hs : ‖B‖₊ < (1000 : NNReal) := he.trans realP1_bound
  have ha : |B| ≤ 1000 := by exact_mod_cast le_of_lt hs
  exact abs_le.mp ha

theorem root2_bounds (B : ℝ) (hp : p2.eval (fun _ => B) = 0) :
    -1000 ≤ B ∧ B ≤ 1000 := by
  have hr : realP2.IsRoot B := by
    simp only [p2, Expr.eval] at hp
    simp only [IsRoot.def, realP2, eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_ofNat]
    linear_combination hp
  have hn : realP2 ≠ 0 := by
    intro he
    have hd := realP2_degree
    rw [he, natDegree_zero] at hd
    norm_num at hd
  have he := hr.norm_lt_cauchyBound hn
  have hs : ‖B‖₊ < (1000 : NNReal) := he.trans realP2_bound
  have ha : |B| ≤ 1000 := by exact_mod_cast le_of_lt hs
  exact abs_le.mp ha

theorem root1_value (B : ℝ) (hp : p1.eval (fun _ => B) = 0) :
    -3125 < v1.eval (fun _ => B) ∧ v1.eval (fun _ => B) < 3125 :=
  bound1 B (root1_bounds B hp) hp

theorem root2_value (B : ℝ) (hp : p2.eval (fun _ => B) = 0) :
    -3125 < v2.eval (fun _ => B) ∧ v2.eval (fun _ => B) < 3125 :=
  bound2 B (root2_bounds B hp) hp

end Mordell.AlgebraicBounds
