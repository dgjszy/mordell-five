import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Mordell

/-- Computable rational endpoints, interpreted over the real numbers. -/
structure Interval where
  lo : ℚ
  hi : ℚ
  deriving DecidableEq, Repr

namespace Interval

def Mem (a : Interval) (x : ℝ) : Prop := (a.lo : ℝ) ≤ x ∧ x ≤ (a.hi : ℝ)
def point (q : ℚ) : Interval := ⟨q, q⟩
def add (a b : Interval) : Interval := ⟨a.lo + b.lo, a.hi + b.hi⟩
def neg (a : Interval) : Interval := ⟨-a.hi, -a.lo⟩
def sub (a b : Interval) : Interval := add a (neg b)
def mul (a b : Interval) : Interval :=
  ⟨min (min (a.lo*b.lo) (a.lo*b.hi)) (min (a.hi*b.lo) (a.hi*b.hi)),
   max (max (a.lo*b.lo) (a.lo*b.hi)) (max (a.hi*b.lo) (a.hi*b.hi))⟩

def intersect (a b : Interval) : Interval := ⟨max a.lo b.lo, min a.hi b.hi⟩

def square (a : Interval) : Interval :=
  if a.hi ≤ 0 then ⟨a.hi*a.hi, a.lo*a.lo⟩
  else if 0 ≤ a.lo then ⟨a.lo*a.lo, a.hi*a.hi⟩
  else ⟨0, max (a.lo*a.lo) (a.hi*a.hi)⟩

theorem mem_intersect {a b : Interval} {x : ℝ} (ha : Mem a x) (hb : Mem b x) :
    Mem (intersect a b) x := by
  simp only [Mem, intersect, Rat.cast_min, Rat.cast_max]
  exact ⟨max_le ha.1 hb.1, le_min ha.2 hb.2⟩

theorem mem_square {a : Interval} {x : ℝ} (hx : Mem a x) :
    Mem (square a) (x*x) := by
  unfold square
  split_ifs with hn hp
  · have hn' : (a.hi : ℝ) ≤ 0 := by exact_mod_cast hn
    simp only [Mem, Rat.cast_mul]
    constructor <;> nlinarith [hx.1, hx.2]
  · have hp' : (0 : ℝ) ≤ a.lo := by exact_mod_cast hp
    simp only [Mem, Rat.cast_mul]
    constructor <;> nlinarith [hx.1, hx.2]
  · simp only [Mem, Rat.cast_zero, Rat.cast_max, Rat.cast_mul]
    constructor
    · exact mul_self_nonneg x
    · by_cases h : 0 ≤ x
      · exact (by nlinarith [hx.2] : x*x ≤ (a.hi : ℝ)*(a.hi : ℝ)).trans (le_max_right _ _)
      · exact (by nlinarith [hx.1] : x*x ≤ (a.lo : ℝ)*(a.lo : ℝ)).trans (le_max_left _ _)

theorem mem_point (q : ℚ) : Mem (point q) (q : ℝ) := by simp [Mem, point]

theorem mem_add {a b : Interval} {x y : ℝ} (hx : Mem a x) (hy : Mem b y) :
    Mem (add a b) (x+y) := by
  simp only [Mem, add, Rat.cast_add] at *
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

theorem mem_neg {a : Interval} {x : ℝ} (hx : Mem a x) : Mem (neg a) (-x) := by
  simp only [Mem, neg, Rat.cast_neg] at *
  constructor <;> linarith [hx.1, hx.2]

theorem mem_sub {a b : Interval} {x y : ℝ} (hx : Mem a x) (hy : Mem b y) :
    Mem (sub a b) (x-y) := by
  simpa [sub, sub_eq_add_neg] using mem_add hx (mem_neg hy)

private theorem fixed_mul_bounds {l h y : ℝ} (hl : l ≤ y) (hh : y ≤ h) (a : ℝ) :
    min (a*l) (a*h) ≤ a*y ∧ a*y ≤ max (a*l) (a*h) := by
  rcases le_total 0 a with ha | ha
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_left hl ha),
      (mul_le_mul_of_nonneg_left hh ha).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_left hh ha),
      (mul_le_mul_of_nonpos_left hl ha).trans (le_max_left _ _)⟩

private theorem four_corner_bounds {l h a b x y : ℝ}
    (hx : l ≤ x ∧ x ≤ h) (hy : a ≤ y ∧ y ≤ b) :
    min (min (l*a) (l*b)) (min (h*a) (h*b)) ≤ x*y ∧
      x*y ≤ max (max (l*a) (l*b)) (max (h*a) (h*b)) := by
  have hl := fixed_mul_bounds hy.1 hy.2 l
  have hh := fixed_mul_bounds hy.1 hy.2 h
  have hxy := fixed_mul_bounds hx.1 hx.2 y
  simp only [mul_comm y] at hxy
  constructor
  · apply le_trans _ hxy.1
    exact le_min ((min_le_left _ _).trans hl.1) ((min_le_right _ _).trans hh.1)
  · apply le_trans hxy.2
    exact max_le (hl.2.trans (le_max_left _ _)) (hh.2.trans (le_max_right _ _))

theorem mem_mul {a b : Interval} {x y : ℝ} (hx : Mem a x) (hy : Mem b y) :
    Mem (mul a b) (x*y) := by
  simp only [Mem, mul, Rat.cast_min, Rat.cast_max, Rat.cast_mul] at *
  exact four_corner_bounds hx hy

/-- An interval range that excludes zero really excludes a real zero. -/
theorem nonzero_of_range {a : Interval} {x : ℝ} (hx : Mem a x)
    (h : 0 < a.lo ∨ a.hi < 0) : x ≠ 0 := by
  rcases h with h | h
  · have h' : (0 : ℝ) < a.lo := by exact_mod_cast h
    exact ne_of_gt (h'.trans_le hx.1)
  · have h' : (a.hi : ℝ) < 0 := by exact_mod_cast h
    exact ne_of_lt (hx.2.trans_lt h')

end Interval
end Mordell
