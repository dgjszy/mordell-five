import Mordell.Algebra
import Mordell.Expression

namespace Mordell

structure CExpr (n : ℕ) where
  re : Expr n
  im : Expr n
  deriving Repr

namespace CExpr

def const {n : ℕ} (q : ℚ) : CExpr n := ⟨.const q, .const 0⟩
def add {n : ℕ} (a b : CExpr n) : CExpr n := ⟨.add a.re b.re, .add a.im b.im⟩
def neg {n : ℕ} (a : CExpr n) : CExpr n := ⟨.neg a.re, .neg a.im⟩
def sub {n : ℕ} (a b : CExpr n) : CExpr n := add a (neg b)
def mul {n : ℕ} (a b : CExpr n) : CExpr n :=
  ⟨Expr.sub (.mul a.re b.re) (.mul a.im b.im),
    .add (.mul a.re b.im) (.mul a.im b.re)⟩
def scale {n : ℕ} (r : Expr n) (a : CExpr n) : CExpr n :=
  ⟨.mul r a.re, .mul r a.im⟩
def pow {n : ℕ} (a : CExpr n) : ℕ → CExpr n
  | 0 => const 1
  | k+1 => mul (pow a k) a
def normSq {n : ℕ} (a : CExpr n) : Expr n := .add (.sqr a.re) (.sqr a.im)
def sum5 {n : ℕ} (v : Fin 5 → CExpr n) : CExpr n :=
  add (add (add (add (v 0) (v 1)) (v 2)) (v 3)) (v 4)

noncomputable def eval {n : ℕ} (x : Fin n → ℝ) (a : CExpr n) : ℂ :=
  ⟨a.re.eval x, a.im.eval x⟩

theorem eval_const {n : ℕ} (x : Fin n → ℝ) (q : ℚ) :
    eval x (const q) = (q : ℂ) := by apply Complex.ext <;> simp [eval, const, Expr.eval]

theorem eval_add {n : ℕ} (x : Fin n → ℝ) (a b : CExpr n) :
    eval x (add a b) = eval x a + eval x b := by rfl

theorem eval_neg {n : ℕ} (x : Fin n → ℝ) (a : CExpr n) :
    eval x (neg a) = -eval x a := by rfl

theorem eval_sub {n : ℕ} (x : Fin n → ℝ) (a b : CExpr n) :
    eval x (sub a b) = eval x a - eval x b := by rfl

theorem eval_mul {n : ℕ} (x : Fin n → ℝ) (a b : CExpr n) :
    eval x (mul a b) = eval x a * eval x b := by
  apply Complex.ext <;> simp [eval, mul, Expr.eval, Expr.sub, sub_eq_add_neg]

theorem eval_scale {n : ℕ} (x : Fin n → ℝ) (r : Expr n) (a : CExpr n) :
    eval x (scale r a) = (r.eval x : ℂ) * eval x a := by
  apply Complex.ext <;> simp [eval, scale, Expr.eval]

theorem eval_pow {n : ℕ} (x : Fin n → ℝ) (a : CExpr n) (k : ℕ) :
    eval x (pow a k) = eval x a ^ k := by
  induction k with
  | zero => simp [pow, eval_const]
  | succ k ih => rw [pow, eval_mul, ih, pow_succ]

theorem eval_normSq {n : ℕ} (x : Fin n → ℝ) (a : CExpr n) :
    (normSq a).eval x = Complex.normSq (eval x a) := by rfl

theorem eval_sum5 {n : ℕ} (x : Fin n → ℝ) (v : Fin 5 → CExpr n) :
    eval x (sum5 v) = ∑ i, eval x (v i) := by
  simp only [sum5, eval_add, Fin.sum_univ_succ, Fin.sum_univ_zero]
  simp
  ring

end CExpr

/-- Coordinate order is x₁,x₂,x₃,y₁,y₂,y₃; the first point is 1 and the sum is zero. -/
def coordinateExpr : Fin 5 → CExpr 6 :=
  let a : CExpr 6 := ⟨.var 0, .var 3⟩
  let b : CExpr 6 := ⟨.var 1, .var 4⟩
  let c : CExpr 6 := ⟨.var 2, .var 5⟩
  ![CExpr.const 1, a, b, c, CExpr.sub (CExpr.sub (CExpr.sub (CExpr.const (-1)) a) b) c]

noncomputable def coordinateConfiguration (x : Fin 6 → ℝ) : Configuration :=
  fun i => (coordinateExpr i).eval x

theorem coordinate_sum (x : Fin 6 → ℝ) : ∑ i, coordinateConfiguration x i = 0 := by
  rw [sum_expand]
  change (CExpr.const 1).eval x + (⟨.var 0,.var 3⟩ : CExpr 6).eval x +
    (⟨.var 1,.var 4⟩ : CExpr 6).eval x + (⟨.var 2,.var 5⟩ : CExpr 6).eval x +
    (CExpr.sub (CExpr.sub (CExpr.sub (CExpr.const (-1)) ⟨.var 0,.var 3⟩)
      ⟨.var 1,.var 4⟩) ⟨.var 2,.var 5⟩).eval x = 0
  simp only [CExpr.eval_sub, CExpr.eval_const]
  norm_num

noncomputable def powerSum (z : Configuration) (k : ℕ) : ℂ := ∑ i, z i ^ k
noncomputable def mixedMoment (z : Configuration) (k : ℕ) : ℂ :=
  ∑ i, (Complex.normSq (z i) : ℂ) * z i ^ k

def powerSumExpr (k : ℕ) : CExpr 6 := CExpr.sum5 fun i => (coordinateExpr i).pow k
def mixedMomentExpr (k : ℕ) : CExpr 6 := CExpr.sum5 fun i =>
  CExpr.scale (coordinateExpr i).normSq ((coordinateExpr i).pow k)
def normSumExpr : Expr 6 :=
  .add (.add (.add (.add (coordinateExpr 0).normSq (coordinateExpr 1).normSq)
    (coordinateExpr 2).normSq) (coordinateExpr 3).normSq) (coordinateExpr 4).normSq

theorem eval_powerSumExpr (x : Fin 6 → ℝ) (k : ℕ) :
    (powerSumExpr k).eval x = powerSum (coordinateConfiguration x) k := by
  simp [powerSumExpr, CExpr.eval_sum5, CExpr.eval_pow, powerSum, coordinateConfiguration]

theorem eval_mixedMomentExpr (x : Fin 6 → ℝ) (k : ℕ) :
    (mixedMomentExpr k).eval x = mixedMoment (coordinateConfiguration x) k := by
  simp [mixedMomentExpr, CExpr.eval_sum5, CExpr.eval_pow, CExpr.eval_scale,
    CExpr.eval_normSq, mixedMoment, coordinateConfiguration]

theorem eval_normSumExpr (x : Fin 6 → ℝ) :
    normSumExpr.eval x = normSum (coordinateConfiguration x) := by
  rw [normSum_expand]
  rfl

def residualExpr (k : Fin 3) : CExpr 6 :=
  ![mixedMomentExpr 1,
    CExpr.sub (CExpr.scale (.const 20) (mixedMomentExpr 2))
      (CExpr.scale (.mul (.const 7) normSumExpr) (powerSumExpr 2)),
    CExpr.sub (CExpr.scale (.const 10) (mixedMomentExpr 3))
      (CExpr.scale (.mul (.const 3) normSumExpr) (powerSumExpr 3))] k

def momentEquations : Fin 6 → Expr 6 :=
  ![(residualExpr 0).re, (residualExpr 0).im, (residualExpr 1).re,
    (residualExpr 1).im, (residualExpr 2).re, (residualExpr 2).im]

def NormalizedMomentSystem (z : Configuration) : Prop :=
  mixedMoment z 1 = 0 ∧
  20 * mixedMoment z 2 - 7 * (normSum z : ℂ) * powerSum z 2 = 0 ∧
  10 * mixedMoment z 3 - 3 * (normSum z : ℂ) * powerSum z 3 = 0

theorem momentEquations_correspondence (x : Fin 6 → ℝ) :
    (∀ i, (momentEquations i).eval x = 0) ↔
    NormalizedMomentSystem (coordinateConfiguration x) := by
  have he : (∀ i, (momentEquations i).eval x = 0) ↔
      (residualExpr 0).eval x = 0 ∧ (residualExpr 1).eval x = 0 ∧
        (residualExpr 2).eval x = 0 := by
    constructor
    · intro h
      exact ⟨Complex.ext (h 0) (h 1), Complex.ext (h 2) (h 3), Complex.ext (h 4) (h 5)⟩
    · rintro ⟨h0,h1,h2⟩ i
      fin_cases i
      · exact congrArg Complex.re h0
      · exact congrArg Complex.im h0
      · exact congrArg Complex.re h1
      · exact congrArg Complex.im h1
      · exact congrArg Complex.re h2
      · exact congrArg Complex.im h2
  rw [he]
  change (mixedMomentExpr 1).eval x = 0 ∧
    (CExpr.sub (CExpr.scale (.const 20) (mixedMomentExpr 2))
      (CExpr.scale (.mul (.const 7) normSumExpr) (powerSumExpr 2))).eval x = 0 ∧
    (CExpr.sub (CExpr.scale (.const 10) (mixedMomentExpr 3))
      (CExpr.scale (.mul (.const 3) normSumExpr) (powerSumExpr 3))).eval x = 0 ↔ _
  simp only [CExpr.eval_sub, CExpr.eval_scale, Expr.eval, eval_mixedMomentExpr,
    eval_powerSumExpr, eval_normSumExpr, Complex.ofReal_mul,
    NormalizedMomentSystem, mul_assoc]
  norm_num

end Mordell
