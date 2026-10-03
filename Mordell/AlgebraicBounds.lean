import Mordell.ValueCover

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Mordell.AlgebraicBounds

def p1 : Expr 1 := (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.const (125)) (.var 0)) (.const (7900))) (.var 0)) (.const (-37040))) (.var 0)) (.const (44608))) (.var 0)) (.const (512)))
def v1 : Expr 1 := (.add (.mul (.add (.mul (.add (.mul (.const (2838375/2097152)) (.var 0)) (.const (41181075/524288))) (.var 0)) (.const (-109276155/131072))) (.var 0)) (.const (25821909/32768)))
def certificate1 : ValueCover := (.split (0) (.split (-500) .leaf (.split (-250) .leaf (.split (-125) .leaf (.split (-125/2) (.split (-375/4) .leaf (.split (-625/8) .leaf (.split (-1125/16) .leaf (.split (-2125/32) (.split (-4375/64) .leaf (.split (-8625/128) (.split (-17375/256) .leaf (.split (-34625/512) (.split (-69375/1024) .leaf .leaf) .leaf)) .leaf)) .leaf)))) (.split (-125/4) .leaf (.split (-125/8) .leaf (.split (-125/16) .leaf (.split (-125/32) .leaf (.split (-125/64) .leaf .leaf))))))))) (.split (500) (.split (250) (.split (125) (.split (125/2) (.split (125/4) (.split (125/8) (.split (125/16) (.split (125/32) .leaf .leaf) .leaf) .leaf) .leaf) .leaf) .leaf) .leaf) .leaf))
theorem checked1 : certificate1.check p1 v1 3125 (fun _ => ⟨-1000,1000⟩) = true := by
  decide +kernel

theorem bound1 (B : ℝ) (hB : -1000 ≤ B ∧ B ≤ 1000)
    (hp : p1.eval (fun _ => B) = 0) :
    -3125 < v1.eval (fun _ => B) ∧ v1.eval (fun _ => B) < 3125 := by
  exact ValueCover.check_sound p1 v1 3125 certificate1 _ _ checked1
    (fun _ => by simpa [Interval.Mem] using hB) hp

def p2 : Expr 1 := (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.const (2500)) (.var 0)) (.const (-114000))) (.var 0)) (.const (338925))) (.var 0)) (.const (-11000))) (.var 0)) (.const (6912)))
def v2 : Expr 1 := (.add (.mul (.add (.mul (.add (.mul (.const (208919281640625/992170999808)) (.var 0)) (.const (-2378884787578125/248042749952))) (.var 0)) (.const (111393859432078125/3968683999232))) (.var 0)) (.const (725183548903125/496085499904)))
def certificate2 : ValueCover := (.split (0) .leaf (.split (500) (.split (250) (.split (125) (.split (125/2) (.split (125/4) (.split (125/8) (.split (125/16) (.split (125/32) (.split (125/64) (.split (125/128) (.split (125/256) .leaf .leaf) .leaf) (.split (375/128) .leaf (.split (875/256) (.split (1625/512) (.split (3125/1024) .leaf (.split (6375/2048) .leaf .leaf)) (.split (3375/1024) .leaf .leaf)) .leaf))) .leaf) .leaf) .leaf) (.split (375/8) (.split (625/16) .leaf (.split (1375/32) (.split (2625/64) .leaf (.split (5375/128) .leaf (.split (10875/256) (.split (21625/512) .leaf (.split (43375/1024) .leaf (.split (86875/2048) (.split (173625/4096) .leaf (.split (347375/8192) (.split (694625/16384) .leaf .leaf) (.split (694875/16384) (.split (1389625/32768) (.split (2779125/65536) .leaf .leaf) .leaf) .leaf))) .leaf))) .leaf))) .leaf)) .leaf)) .leaf) .leaf) .leaf) .leaf))
theorem checked2 : certificate2.check p2 v2 3125 (fun _ => ⟨-1000,1000⟩) = true := by
  decide +kernel

theorem bound2 (B : ℝ) (hB : -1000 ≤ B ∧ B ≤ 1000)
    (hp : p2.eval (fun _ => B) = 0) :
    -3125 < v2.eval (fun _ => B) ∧ v2.eval (fun _ => B) < 3125 := by
  exact ValueCover.check_sound p2 v2 3125 certificate2 _ _ checked2
    (fun _ => by simpa [Interval.Mem] using hB) hp

end Mordell.AlgebraicBounds
