import Mordell.Force
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.RingTheory.Polynomial.Resultant.Basic

namespace Mordell
open Polynomial

noncomputable def rootPolynomial (z : Configuration) : ℂ[X] :=
  ∏ i, (X - C (z i))

noncomputable def rootCofactor (z : Configuration) (i : Fin 5) : ℂ[X] :=
  ∏ j ∈ Finset.univ.erase i, (X - C (z j))

theorem rootPolynomial_factor (z : Configuration) (i : Fin 5) :
    rootPolynomial z = (X - C (z i)) * rootCofactor z i := by
  exact (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm

theorem rootPolynomial_eval (z : Configuration) (i : Fin 5) :
    (rootPolynomial z).eval (z i) = 0 := by
  rw [rootPolynomial_factor z i]
  simp

theorem rootCofactor_eval_ne {z : Configuration} (hz : Function.Injective z)
    (i : Fin 5) : (rootCofactor z i).eval (z i) ≠ 0 := by
  simp only [rootCofactor, eval_prod, eval_sub, eval_X, eval_C]
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  exact sub_ne_zero.mpr (hz.ne (Finset.ne_of_mem_erase hj).symm)

theorem eval_derivative_prod_relative {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℂ[X]) (t : ℂ)
    (h : ∀ i ∈ s, (f i).eval t ≠ 0) :
    (∏ i ∈ s, f i).derivative.eval t =
      (∏ i ∈ s, (f i).eval t) * ∑ i ∈ s, (f i).derivative.eval t / (f i).eval t := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hs := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    have hfa := h a (Finset.mem_insert_self a s)
    simp only [Finset.prod_insert ha, Finset.sum_insert ha, derivative_mul,
      eval_add, eval_mul, eval_prod, hs]
    field_simp

theorem rootCofactor_logDerivative {z : Configuration} (hz : Function.Injective z)
    (i : Fin 5) :
    (rootCofactor z i).derivative.eval (z i) =
      (rootCofactor z i).eval (z i) * force z i := by
  have he := eval_derivative_prod_relative (Finset.univ.erase i)
    (fun j => X - C (z j)) (z i) (by
      intro j hj
      simpa using sub_ne_zero.mpr (hz.ne (Finset.ne_of_mem_erase hj).symm))
  have hs : (∑ j ∈ Finset.univ.erase i, 1 / (z i - z j)) = force z i := by
    unfold force
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    simp only [ite_true, add_zero]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [if_neg (Finset.ne_of_mem_erase hj)]
  simpa only [rootCofactor, derivative_sub, derivative_X, derivative_C,
    sub_zero, eval_one, eval_sub, eval_X, eval_C, eval_prod, hs] using he

theorem rootPolynomial_derivative_eval (z : Configuration) (i : Fin 5) :
    (rootPolynomial z).derivative.eval (z i) = (rootCofactor z i).eval (z i) := by
  rw [rootPolynomial_factor z i]
  simp

theorem rootPolynomial_second_derivative_eval {z : Configuration}
    (hz : Function.Injective z) (i : Fin 5) :
    (rootPolynomial z).derivative.derivative.eval (z i) =
      2 * (rootPolynomial z).derivative.eval (z i) * force z i := by
  rw [rootPolynomial_factor z i]
  simp only [derivative_mul, derivative_add, derivative_sub, derivative_X,
    derivative_C, sub_zero, derivative_one, eval_add, eval_mul, eval_zero,
    eval_one, eval_sub, eval_X, eval_C, sub_self, zero_mul, one_mul, zero_add,
    add_zero]
  rw [rootCofactor_logDerivative hz i]
  ring

theorem global_maximum_root_equation {z : Configuration} (hz : IsGlobalMaximum z)
    (i : Fin 5) :
    (rootPolynomial z).derivative.derivative.eval (z i) =
      4 * star (z i) * (rootPolynomial z).derivative.eval (z i) := by
  rw [rootPolynomial_second_derivative_eval
    (injective_of_discriminant_pos (global_maximum_positive hz)), global_maximum_force hz]
  ring

end Mordell
