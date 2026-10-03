import Mordell.Expression
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod

namespace Mordell.Expr

noncomputable def derivative {n : ℕ} (x : Fin n → ℝ) :
    Expr n → ((Fin n → ℝ) →L[ℝ] ℝ)
  | .const _ => 0
  | .var i => ContinuousLinearMap.proj i
  | .add a b => derivative x a + derivative x b
  | .neg a => -derivative x a
  | .mul a b => a.eval x • derivative x b + b.eval x • derivative x a
  | .sqr a => a.eval x • derivative x a + a.eval x • derivative x a

/-- The polynomial evaluator has the stated derivative at every real point. -/
theorem hasFDerivAt_eval {n : ℕ} (x : Fin n → ℝ) (e : Expr n) :
    HasFDerivAt (fun y => e.eval y) (e.derivative x) x := by
  induction e with
  | const q => exact hasFDerivAt_const (q : ℝ) x
  | var i => exact ((ContinuousLinearMap.proj i) : (Fin n → ℝ) →L[ℝ] ℝ).hasFDerivAt
  | add a b ha hb => exact ha.add hb
  | neg a ha => exact ha.neg
  | mul a b ha hb => exact ha.mul hb
  | sqr a ha => exact ha.mul ha

def diff {n : ℕ} (i : Fin n) : Expr n → Expr n
  | .const _ => .const 0
  | .var j => .const (if i = j then 1 else 0)
  | .add a b => .add (diff i a) (diff i b)
  | .neg a => .neg (diff i a)
  | .mul a b => .add (.mul a (diff i b)) (.mul b (diff i a))
  | .sqr a => .add (.mul a (diff i a)) (.mul a (diff i a))

theorem derivative_apply {n : ℕ} (x v : Fin n → ℝ) (e : Expr n) :
    e.derivative x v = ∑ i, (e.diff i).eval x * v i := by
  induction e with
  | const q => simp [derivative, diff, eval]
  | var j => simp [derivative, diff, eval, apply_ite]
  | add a b ha hb =>
    simp [derivative, diff, eval, ha, hb, add_mul, Finset.sum_add_distrib]
  | neg a ha => simp [derivative, diff, eval, ha, neg_mul, Finset.sum_neg_distrib]
  | mul a b ha hb =>
    simp [derivative, diff, eval, ha, hb, add_mul, Finset.sum_add_distrib, ← Finset.mul_sum, mul_assoc]
  | sqr a ha =>
    simp [derivative, diff, eval, ha, add_mul, Finset.sum_add_distrib, ← Finset.mul_sum, mul_assoc]

end Mordell.Expr
