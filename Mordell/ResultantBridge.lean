import Mordell.StationaryPair
import Mordell.Reduction

namespace Mordell
open Polynomial

noncomputable def complexDiscriminant (x : Configuration) : ℂ :=
  ∏ i, (rootPolynomial x).derivative.eval (x i)

theorem rootPolynomial_resultant (x : Configuration) (q : ℂ[X]) (n : ℕ)
    (hq : q.natDegree ≤ n) :
    (rootPolynomial x).resultant q 5 n = ∏ i, q.eval (x i) := by
  have hd := rootPolynomial_natDegree x
  unfold rootPolynomial at hd ⊢
  have he := resultant_prod_left (Finset.univ : Finset (Fin 5))
    (fun i => X - C (x i)) q n (by simp) hq
  rw [hd] at he
  simpa only [natDegree_X_sub_C, resultant_X_sub_C_left q n _ hq] using he

theorem complexDiscriminant_ne {x : Configuration} (hx : Function.Injective x) :
    complexDiscriminant x ≠ 0 := by
  unfold complexDiscriminant
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  rw [rootPolynomial_derivative_eval]
  exact rootCofactor_eval_ne hx i

theorem complexDiscriminant_normSq (x : Configuration) :
    Complex.normSq (complexDiscriminant x) = discriminant x ^ 2 := by
  rw [← orderedDiscriminant_eq_square]
  unfold complexDiscriminant orderedDiscriminant
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [rootPolynomial_derivative_eval]
  simp only [rootCofactor, eval_prod, eval_sub, eval_X, eval_C, map_prod]
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  simp only [ne_eq, not_true_eq_false, if_false, mul_one]
  apply Finset.prod_congr rfl
  intro j hj
  simp only [if_pos (Finset.ne_of_mem_erase hj).symm]

theorem stationaryPair_resultant {x y : Configuration} (h : StationaryPair x y)
    (Y T : ℂ) :
    (rootPolynomial x).resultant
      ((C Y + C T * X) * (rootPolynomial x).derivative -
        (rootPolynomial x).derivative.derivative) 5 5 =
      complexDiscriminant x * ∏ i, (Y + T * x i - 4 * y i) := by
  rw [rootPolynomial_resultant]
  · simp only [eval_sub, eval_mul, eval_add, eval_C, eval_X,
      stationaryPair_root_equation h]
    unfold complexDiscriminant
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    ring
  · have hd : (rootPolynomial x).derivative.natDegree ≤ 4 := by
      have he := natDegree_derivative_le (p := rootPolynomial x)
      simpa only [rootPolynomial_natDegree] using he
    have he := natDegree_sub_le ((C Y + C T * X) * (rootPolynomial x).derivative)
      (rootPolynomial x).derivative.derivative
    apply he.trans
    apply max_le
    · apply (natDegree_mul_le).trans
      have hlin : (C Y + C T * X).natDegree ≤ 1 := by
        apply (natDegree_add_le (C Y) (C T * X)).trans
        apply max_le
        · simp
        · exact natDegree_C_mul_le _ _ |>.trans (by simp)
      omega
    · have he := natDegree_derivative_le (p := (rootPolynomial x).derivative)
      omega

end Mordell
