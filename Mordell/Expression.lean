import Mordell.Interval

namespace Mordell

/-- The polynomial expression language used by the certificate checker. -/
inductive Expr (n : ℕ) where
  | const : ℚ → Expr n
  | var : Fin n → Expr n
  | add : Expr n → Expr n → Expr n
  | neg : Expr n → Expr n
  | mul : Expr n → Expr n → Expr n
  | sqr : Expr n → Expr n
  deriving Repr, DecidableEq

namespace Expr

def sub {n : ℕ} (a b : Expr n) : Expr n := .add a (.neg b)

def sumFin {n : ℕ} : {m : ℕ} → (Fin m → Expr n) → Expr n
  | 0, _ => .const 0
  | m+1, f => .add (f 0) (sumFin (fun i : Fin m => f i.succ))

def eval {n : ℕ} (x : Fin n → ℝ) : Expr n → ℝ
  | .const q => q
  | .var i => x i
  | .add a b => eval x a + eval x b
  | .neg a => -eval x a
  | .mul a b => eval x a * eval x b
  | .sqr a => eval x a * eval x a

def range {n : ℕ} (b : Fin n → Interval) : Expr n → Interval
  | .const q => Interval.point q
  | .var i => b i
  | .add a c => Interval.add (range b a) (range b c)
  | .neg a => Interval.neg (range b a)
  | .mul a c => Interval.mul (range b a) (range b c)
  | .sqr a => Interval.square (range b a)

/-- This theorem is the bridge from computable rational arithmetic to real polynomials. -/
theorem eval_mem_range {n : ℕ} (b : Fin n → Interval) (x : Fin n → ℝ)
    (hx : ∀ i, Interval.Mem (b i) (x i)) (e : Expr n) :
    Interval.Mem (range b e) (eval x e) := by
  induction e with
  | const q => exact Interval.mem_point q
  | var i => exact hx i
  | add a c ha hc => exact Interval.mem_add ha hc
  | neg a ha => exact Interval.mem_neg ha
  | mul a c ha hc => exact Interval.mem_mul ha hc
  | sqr a ha => exact Interval.mem_square ha

theorem eval_sumFin {n m : ℕ} (x : Fin n → ℝ) (f : Fin m → Expr n) :
    (sumFin f).eval x = ∑ i, (f i).eval x := by
  induction m with
  | zero => simp [sumFin, eval]
  | succ m ih => simp [sumFin, eval, ih, Fin.sum_univ_succ]

end Expr
end Mordell
