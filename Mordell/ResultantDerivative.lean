import Mordell.ResultantAlgebra
import Mordell.WeightedCofactor

namespace Mordell
open Polynomial
open ResultantAlgebra

set_option maxHeartbeats 0

 theorem value_hasDerivAt (a b c d Y : ℂ) :
    HasDerivAt (fun t : ℝ => Determinants.value273 a b c d Y (t : ℂ))
      (F1 a b c d Y) 0 := by
  have hc := (hasDerivAt_id (0 : ℝ)).ofReal_comp
  have hd := (((((hasDerivAt_const (0 : ℝ) (F0 a b c d Y)).add
    (hc.mul_const (F1 a b c d Y))).add
    ((hc.pow 2).mul_const (F2 a b c d Y))).add
    ((hc.pow 3).mul_const (F3 a b c d Y))).add
    ((hc.pow 4).mul_const (F4 a b c d Y))).add
    ((hc.pow 5).mul_const (F5 a b c d Y))
  convert hd using 1
  · funext t
    exact value_coefficients a b c d Y (t : ℂ)
  · simp

 theorem root_product_hasDerivAt (x y : Configuration) (Y : ℂ) :
    HasDerivAt
      (fun t : ℝ => complexDiscriminant x * ∏ i, (Y + (t : ℂ)*x i - 4*y i))
      (complexDiscriminant x * weightedCofactor (fun i => 4*y i) x Y) 0 := by
  have hc := (hasDerivAt_id (0 : ℝ)).ofReal_comp
  have hd := HasDerivAt.fun_finset_prod (u := Finset.univ)
    (fun i _ => ((hc.mul_const (x i)).const_add Y).sub_const (4*y i))
  convert HasDerivAt.const_mul (complexDiscriminant x) hd using 1
  simp only [weightedCofactor, rootCofactor, id_eq, Complex.ofReal_zero, Complex.ofReal_one, one_mul, zero_mul,
    add_zero, smul_eq_mul, eval_prod, eval_sub, eval_X, eval_C, mul_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

 theorem stationaryPair_F0 {x y : Configuration} (h : StationaryPair x y)
    {a b c d : ℂ} (hp : rootPolynomial x = quintic a b c d) (Y : ℂ) :
    F0 a b c d Y = complexDiscriminant x * (rootPolynomial (fun i => 4*y i)).eval Y := by
  have he := stationaryPair_resultant h Y 0
  rw [hp, resultant_formula, value_coefficients] at he
  simp only [zero_mul, add_zero, zero_pow (by decide : 2 ≠ 0),
    zero_pow (by decide : 3 ≠ 0), zero_pow (by decide : 4 ≠ 0),
    zero_pow (by decide : 5 ≠ 0), mul_zero] at he
  simpa only [rootPolynomial, eval_prod, eval_sub, eval_X, eval_C] using he

 theorem stationaryPair_F1 {x y : Configuration} (h : StationaryPair x y)
    {a b c d : ℂ} (hp : rootPolynomial x = quintic a b c d) (Y : ℂ) :
    F1 a b c d Y = complexDiscriminant x *
      (20*Y^3 + 6*(rootPolynomial (fun i => 4*y i)).coeff 3*Y +
        2*(rootPolynomial (fun i => 4*y i)).coeff 2) := by
  have hfun (t : ℝ) : Determinants.value273 a b c d Y (t : ℂ) =
      complexDiscriminant x * ∏ i, (Y + (t : ℂ)*x i - 4*y i) := by
    have he := stationaryPair_resultant h Y (t : ℂ)
    rw [hp, resultant_formula] at he
    exact he
  have hd : HasDerivAt
      (fun t : ℝ => complexDiscriminant x * ∏ i, (Y + (t : ℂ)*x i - 4*y i))
      (F1 a b c d Y) 0 := by
    convert value_hasDerivAt a b c d Y using 1
    funext t
    exact (hfun t).symm
  have he := hd.unique (root_product_hasDerivAt x y Y)
  rw [stationaryPair_weightedCofactor h] at he
  exact he

end Mordell
