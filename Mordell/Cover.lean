import Mordell.Expression

namespace Mordell

abbrev Box (n : ℕ) := Fin n → Interval

def Box.Mem {n : ℕ} (b : Box n) (x : Fin n → ℝ) : Prop :=
  ∀ i, Interval.Mem (b i) (x i)

def Box.left {n : ℕ} (b : Box n) (i : Fin n) (t : ℚ) : Box n :=
  Function.update b i ⟨(b i).lo, min (b i).hi t⟩

def Box.right {n : ℕ} (b : Box n) (i : Fin n) (t : ℚ) : Box n :=
  Function.update b i ⟨max (b i).lo t, (b i).hi⟩

def Box.restrict {n : ℕ} (b : Box n) (i : Fin n) (a : Interval) : Box n :=
  Function.update b i (Interval.intersect (b i) a)

theorem Box.mem_restrict {n : ℕ} {b : Box n} {x : Fin n → ℝ} {i : Fin n}
    {a : Interval} (hx : b.Mem x) (hi : Interval.Mem a (x i)) :
    (b.restrict i a).Mem x := by
  intro j
  by_cases hj : j = i
  · subst j
    simpa only [Box.restrict, Function.update_self] using Interval.mem_intersect (hx i) hi
  · simpa only [Box.restrict, Function.update_of_ne hj] using hx j

def Box.Subset {n : ℕ} (a b : Box n) : Prop :=
  ∀ i, (b i).lo ≤ (a i).lo ∧ (a i).hi ≤ (b i).hi

instance {n : ℕ} (a b : Box n) : Decidable (Box.Subset a b) :=
  inferInstanceAs (Decidable (∀ i, (b i).lo ≤ (a i).lo ∧ (a i).hi ≤ (b i).hi))

theorem Box.mem_of_subset {n : ℕ} {a b : Box n} {x : Fin n → ℝ}
    (h : Box.Subset a b) (hx : a.Mem x) : b.Mem x := by
  intro i
  have hlo : ((b i).lo : ℝ) ≤ (a i).lo := by exact_mod_cast (h i).1
  have hhi : ((a i).hi : ℝ) ≤ (b i).hi := by exact_mod_cast (h i).2
  exact ⟨hlo.trans (hx i).1, (hx i).2.trans hhi⟩

/-- Closed-box splitting never loses a real point, including the splitting face. -/
theorem Box.split_covers {n : ℕ} {b : Box n} {x : Fin n → ℝ}
    (hx : b.Mem x) (i : Fin n) (t : ℚ) :
    (b.left i t).Mem x ∨ (b.right i t).Mem x := by
  rcases le_total (x i) (t : ℝ) with ht | ht
  · left
    intro j
    by_cases hj : j = i
    · subst j
      simp only [Box.left, Function.update_self, Interval.Mem, Rat.cast_min]
      exact ⟨(hx i).1, le_min (hx i).2 ht⟩
    · simpa only [Box.left, Function.update_of_ne hj] using hx j
  · right
    intro j
    by_cases hj : j = i
    · subst j
      simp only [Box.right, Function.update_self, Interval.Mem, Rat.cast_max]
      exact ⟨max_le (hx i).1 ht, (hx i).2⟩
    · simpa only [Box.right, Function.update_of_ne hj] using hx j

/-- A finite, explicit cover certificate. No external executable result is a proof constructor. -/
inductive CoverCert (n m k : ℕ) where
  | empty : Fin n → CoverCert n m k
  | equation : Fin m → CoverCert n m k
  | inequality : Fin k → CoverCert n m k
  | enclosed : CoverCert n m k
  | split : Fin n → ℚ → CoverCert n m k → CoverCert n m k → CoverCert n m k
  | solve : Fin n → Fin m → Expr n → CoverCert n m k → CoverCert n m k
  | upper : Fin n → Fin k → Expr n → CoverCert n m k → CoverCert n m k
  | lower : Fin n → Fin k → Expr n → CoverCert n m k → CoverCert n m k
  deriving Repr

def Candidate {n m k : ℕ} (f : Fin m → Expr n) (g : Fin k → Expr n)
    (x : Fin n → ℝ) : Prop :=
  (∀ i, (f i).eval x = 0) ∧ (∀ i, 0 ≤ (g i).eval x)

def CoverCert.check {n m k : ℕ} (f : Fin m → Expr n) (g : Fin k → Expr n)
    (localBox : Box n) (b : Box n) : CoverCert n m k → Bool
  | .empty i => decide ((b i).hi < (b i).lo)
  | .equation i =>
      decide (0 < ((f i).range b).lo ∨ ((f i).range b).hi < 0)
  | .inequality i => decide (((g i).range b).hi < 0)
  | .enclosed => decide (Box.Subset b localBox)
  | .split i t a c =>
      check f g localBox (b.left i t) a && check f g localBox (b.right i t) c
  | .solve i j e c => decide (f j = Expr.sub (.var i) e) &&
      check f g localBox (b.restrict i (e.range b)) c
  | .upper i j e c => decide (g j = Expr.sub e (.var i)) &&
      check f g localBox (b.restrict i ⟨(b i).lo, (e.range b).hi⟩) c
  | .lower i j e c => decide (g j = Expr.sub (.var i) e) &&
      check f g localBox (b.restrict i ⟨(e.range b).lo, (b i).hi⟩) c

/-- Accepted rational certificates cover every real candidate in the initial box. -/
theorem CoverCert.check_sound {n m k : ℕ} (f : Fin m → Expr n)
    (g : Fin k → Expr n) (localBox : Box n) (c : CoverCert n m k) :
    ∀ (b : Box n) (x : Fin n → ℝ), c.check f g localBox b = true →
      b.Mem x → Candidate f g x → localBox.Mem x := by
  induction c with
  | empty i =>
    intro b x hc hx _
    have hc : (b i).hi < (b i).lo := of_decide_eq_true hc
    have hr : ((b i).hi : ℝ) < (b i).lo := by exact_mod_cast hc
    exact False.elim (not_lt_of_ge ((hx i).1.trans (hx i).2) hr)
  | equation i =>
    intro b x hc hx hp
    have hc : 0 < ((f i).range b).lo ∨ ((f i).range b).hi < 0 :=
      of_decide_eq_true hc
    have hn := Interval.nonzero_of_range ((f i).eval_mem_range b x hx) hc
    exact False.elim (hn (hp.1 i))
  | inequality i =>
    intro b x hc hx hp
    have hc : ((g i).range b).hi < 0 := of_decide_eq_true hc
    have hr : ((((g i).range b).hi : ℚ) : ℝ) < 0 := by exact_mod_cast hc
    have he := (g i).eval_mem_range b x hx
    exact False.elim (not_lt_of_ge (hp.2 i) (he.2.trans_lt hr))
  | enclosed =>
    intro b x hc hx _
    exact Box.mem_of_subset (of_decide_eq_true hc) hx
  | split i t a c ha hc =>
    intro b x hcheck hx hp
    have hab : a.check f g localBox (b.left i t) = true ∧
        c.check f g localBox (b.right i t) = true := by
      simpa only [CoverCert.check, Bool.and_eq_true] using hcheck
    rcases Box.split_covers hx i t with hl | hr
    · exact ha _ x hab.1 hl hp
    · exact hc _ x hab.2 hr hp
  | solve i j e c ih =>
    intro b x hcheck hx hp
    have hh : decide (f j = Expr.sub (.var i) e) = true ∧
        c.check f g localBox (b.restrict i (e.range b)) = true :=
      by simpa only [CoverCert.check, Bool.and_eq_true] using hcheck
    have he : x i = e.eval x := by
      have hf := hp.1 j
      rw [of_decide_eq_true hh.1] at hf
      change x i + -e.eval x = 0 at hf
      linarith
    apply ih _ x hh.2 (Box.mem_restrict hx _) hp
    rw [he]
    exact e.eval_mem_range b x hx
  | upper i j e c ih =>
    intro b x hcheck hx hp
    have hh : decide (g j = Expr.sub e (.var i)) = true ∧
        c.check f g localBox (b.restrict i ⟨(b i).lo, (e.range b).hi⟩) = true :=
      by simpa only [CoverCert.check, Bool.and_eq_true] using hcheck
    have hg := hp.2 j
    rw [of_decide_eq_true hh.1] at hg
    change 0 ≤ e.eval x + -x i at hg
    have he := e.eval_mem_range b x hx
    apply ih _ x hh.2 (Box.mem_restrict hx _) hp
    exact ⟨(hx i).1, by change x i ≤ ((e.range b).hi : ℝ); linarith [he.2]⟩
  | lower i j e c ih =>
    intro b x hcheck hx hp
    have hh : decide (g j = Expr.sub (.var i) e) = true ∧
        c.check f g localBox (b.restrict i ⟨(e.range b).lo, (b i).hi⟩) = true :=
      by simpa only [CoverCert.check, Bool.and_eq_true] using hcheck
    have hg := hp.2 j
    rw [of_decide_eq_true hh.1] at hg
    change 0 ≤ x i + -e.eval x at hg
    have he := e.eval_mem_range b x hx
    apply ih _ x hh.2 (Box.mem_restrict hx _) hp
    exact ⟨by change (((e.range b).lo : ℚ) : ℝ) ≤ x i; linarith [he.1], (hx i).2⟩

end Mordell
