import Mordell.Cover

namespace Mordell

inductive ValueCover where
  | leaf : ValueCover
  | split : ℚ → ValueCover → ValueCover → ValueCover
  deriving Repr

def ValueCover.check (p v : Expr 1) (limit : ℚ) (b : Box 1) : ValueCover → Bool
  | .leaf => decide (0 < (p.range b).lo ∨ (p.range b).hi < 0 ∨
      (-limit < (v.range b).lo ∧ (v.range b).hi < limit))
  | .split t a c => check p v limit (b.left 0 t) a && check p v limit (b.right 0 t) c

theorem ValueCover.check_sound (p v : Expr 1) (limit : ℚ) (c : ValueCover) :
    ∀ b x, c.check p v limit b = true → b.Mem x → p.eval x = 0 →
      -(limit : ℝ) < v.eval x ∧ v.eval x < limit := by
  induction c with
  | leaf =>
    intro b x hc hx hp
    have hc : 0 < (p.range b).lo ∨ (p.range b).hi < 0 ∨
      (-limit < (v.range b).lo ∧ (v.range b).hi < limit) := of_decide_eq_true hc
    rcases hc with hl | hr | hv
    · exact False.elim ((Interval.nonzero_of_range (p.eval_mem_range b x hx) (Or.inl hl)) hp)
    · exact False.elim ((Interval.nonzero_of_range (p.eval_mem_range b x hx) (Or.inr hr)) hp)
    · have he := v.eval_mem_range b x hx
      have hlo : -(limit : ℝ) < ((v.range b).lo : ℝ) := by exact_mod_cast hv.1
      have hhi : ((v.range b).hi : ℝ) < (limit : ℝ) := by exact_mod_cast hv.2
      exact ⟨hlo.trans_le he.1, he.2.trans_lt hhi⟩
  | split t a c ha hc =>
    intro b x hcheck hx hp
    have hh : a.check p v limit (b.left 0 t) = true ∧
        c.check p v limit (b.right 0 t) = true := by
      simpa only [ValueCover.check, Bool.and_eq_true] using hcheck
    rcases Box.split_covers hx 0 t with hl | hr
    · exact ha _ x hh.1 hl hp
    · exact hc _ x hh.2 hr hp

end Mordell
