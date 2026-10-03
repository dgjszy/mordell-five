import Mordell.Force

set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace Mordell.Elimination

def g0 (s k c B : ℂ) : ℂ :=
  (-12 * c^2 + 224 * c^3 + 320 * c^4 - 5625 * k^3 * B - 960 * k * c^2 - 144 * c^2 * B - 135 * k * B^2 - 36 * k * B + 4 * c * B + 27 * c * B^2 + 108 * k * c + 1125 * k^2 * B + 1600 * k * c^3 + 3375 * k^2 * B^2 - 2700 * k * c^2 * B + 495 * k * c * B + 1500 * k^2 * c * B + 12500 * k^3 * c * B)

def g1 (s k c B : ℂ) : ℂ :=
  (-512 * c^3 + 8 * B^2 + 48 * c^2 + 54 * B^3 + 1280 * c^4 - 3375 * k^2 * B^2 - 900 * k^2 * B - 800 * c^3 * B - 369 * c * B^2 - 44 * c * B + 36 * k * B + 195 * k * B^2 + 712 * c^2 * B + 6250 * k^3 * B^2 - 2800 * k * c^2 * B + 220 * k * c * B + 2250 * k * c * B^2 + 4000 * k^2 * c * B)

def g2 (s k c B : ℂ) : ℂ :=
  (-5440 * c^3 - 216 * c + 48 * B + 351 * B^2 + 648 * k + 1968 * c^2 - 37125 * k^2 * B - 5805 * k * c - 2067 * c * B - 2000 * k * c^3 - 675 * k * B^2 + 180 * c^2 * B + 5085 * k * B + 13800 * k * c^2 + 37500 * k^3 * B + 7500 * k^2 * c * B + 15600 * k * c * B)

def g3 (s k c B : ℂ) : ℂ :=
  (-1 - 128 * s * c^4 * B + 16 * s * c^3 * B + 256 * s * c^5 * B - 3750 * s * k^3 * B^3 - 27 * s * c^2 * B^3 - 4 * s * c^2 * B^2 + 16 * s * k * B^3 + 108 * s * k^2 * B^2 + 108 * s * k * B^4 + 144 * s * c^3 * B^2 + 825 * s * k^2 * B^3 + 3125 * s * k^4 * B^3 - 1600 * s * k * c^3 * B^2 - 900 * s * k^2 * c * B^2 - 630 * s * k * c * B^3 - 72 * s * k * c * B^2 + 560 * s * k * c^2 * B^2 + 2000 * s * k^2 * c^2 * B^2 + 2250 * s * k^2 * c * B^3)

def g4 (s k c B : ℂ) : ℂ :=
  (12500 * k^3 * c * B + 1600 * k * c^3 + 320 * c^4 - 5625 * k^3 * B + 1500 * k^2 * c * B - 2700 * k * c^2 * B + 3375 * k^2 * B^2 - 960 * k * c^2 + 224 * c^3 + 1125 * k^2 * B + 495 * k * c * B - 144 * c^2 * B - 135 * k * B^2 + 27 * c * B^2 + 108 * k * c - 12 * c^2 - 36 * k * B + 4 * c * B)

theorem step4 (s k c B : ℂ) :
    1 * g4 s k c B = (1) * g0 s k c B := by
  dsimp only [g4, g0] <;> ring

theorem zero4 (s k c B : ℂ) (h0 : g0 s k c B = 0) (h1 : g1 s k c B = 0) (h2 : g2 s k c B = 0) (h3 : g3 s k c B = 0) :
    g4 s k c B = 0 := by
  have he := step4 s k c B
  simp only [h0, mul_zero, add_zero] at he
  exact (mul_eq_zero.mp he).resolve_left (by norm_num)

def g5 (s k c B : ℂ) : ℂ :=
  (6250 * k^3 * B^2 + 1280 * c^4 + 4000 * k^2 * c * B - 2800 * k * c^2 * B - 800 * c^3 * B - 3375 * k^2 * B^2 + 2250 * k * c * B^2 - 512 * c^3 - 900 * k^2 * B + 220 * k * c * B + 712 * c^2 * B + 195 * k * B^2 - 369 * c * B^2 + 54 * B^3 + 48 * c^2 + 36 * k * B - 44 * c * B + 8 * B^2)

theorem step5 (s k c B : ℂ) :
    1 * g5 s k c B = (1) * g1 s k c B := by
  dsimp only [g5, g1] <;> ring

theorem zero5 (s k c B : ℂ) (h0 : g0 s k c B = 0) (h1 : g1 s k c B = 0) (h2 : g2 s k c B = 0) (h3 : g3 s k c B = 0) :
    g5 s k c B = 0 := by
  have he := step5 s k c B
  simp only [h1, mul_zero, add_zero] at he
  exact (mul_eq_zero.mp he).resolve_left (by norm_num)

def g6 (s k c B : ℂ) : ℂ :=
  (2000 * k * c^3 - 37500 * k^3 * B - 7500 * k^2 * c * B - 13800 * k * c^2 + 5440 * c^3 + 37125 * k^2 * B - 15600 * k * c * B - 180 * c^2 * B + 675 * k * B^2 + 5805 * k * c - 1968 * c^2 - 5085 * k * B + 2067 * c * B - 351 * B^2 - 648 * k + 216 * c - 48 * B)

theorem step6 (s k c B : ℂ) :
    1 * g6 s k c B = (-1) * g2 s k c B := by
  dsimp only [g6, g2] <;> ring

theorem zero6 (s k c B : ℂ) (h0 : g0 s k c B = 0) (h1 : g1 s k c B = 0) (h2 : g2 s k c B = 0) (h3 : g3 s k c B = 0) :
    g6 s k c B = 0 := by
  have he := step6 s k c B
  simp only [h2, mul_zero, add_zero] at he
  exact (mul_eq_zero.mp he).resolve_left (by norm_num)

def g7 (s k c B : ℂ) : ℂ :=
  (128000 * s * c^5 * B + 500000 * s * k^2 * c^2 * B^2 - 1687500 * s * k^2 * c * B^3 + 3500800 * s * c^4 * B + 9695000 * s * k^2 * c * B^2 - 13548000 * s * k * c^2 * B^2 + 103200 * s * c^3 * B^2 + 6759375 * s * k^2 * B^3 - 373500 * s * k * c * B^3 - 67500 * s * c^2 * B^3 + 243000 * s * k * B^4 + 5145600 * s * c^4 + 16080000 * s * k^2 * c * B - 19046400 * s * k * c^2 * B - 1183040 * s * c^3 * B + 7317000 * s * k^2 * B^2 + 1422200 * s * k * c * B^2 + 950200 * s * c^2 * B^2 - 812325 * s * k * B^3 - 146025 * s * c * B^3 + 810 * s * B^4 - 2058240 * s * c^3 - 3618000 * s * k^2 * B + 4277760 * s * k * c * B + 1819344 * s * c^2 * B - 2370240 * s * k * B^2 - 286816 * s * c * B^2 + 10608 * s * B^3 + 192960 * s * c^2 - 238896 * s * k * B - 49008 * s * c * B + 3744 * s * B^2 - 500)

theorem step7 (s k c B : ℂ) :
    1 * g7 s k c B = (500) * g3 s k c B + (560 * s * B) * g0 s k c B + (-250 * s * k * B + 1965 * s * B + 4020 * s) * g1 s k c B + (-160 * s * c * B - 300 * s * B^2 - 592 * s * B) * g2 s k c B := by
  dsimp only [g7, g3, g0, g1, g2] <;> ring

theorem zero7 (s k c B : ℂ) (h0 : g0 s k c B = 0) (h1 : g1 s k c B = 0) (h2 : g2 s k c B = 0) (h3 : g3 s k c B = 0) :
    g7 s k c B = 0 := by
  have he := step7 s k c B
  simp only [h3, h0, h1, h2, mul_zero, add_zero] at he
  exact (mul_eq_zero.mp he).resolve_left (by norm_num)

def g8 (s k c B : ℂ) : ℂ :=
  (128000 * s * c^5 * B + 500000 * s * k^2 * c^2 * B^2 - 1687500 * s * k^2 * c * B^3 + 3500800 * s * c^4 * B + 9695000 * s * k^2 * c * B^2 - 13548000 * s * k * c^2 * B^2 + 103200 * s * c^3 * B^2 + 6759375 * s * k^2 * B^3 - 373500 * s * k * c * B^3 - 67500 * s * c^2 * B^3 + 243000 * s * k * B^4 + 5145600 * s * c^4 + 16080000 * s * k^2 * c * B - 19046400 * s * k * c^2 * B - 1183040 * s * c^3 * B + 7317000 * s * k^2 * B^2 + 1422200 * s * k * c * B^2 + 950200 * s * c^2 * B^2 - 812325 * s * k * B^3 - 146025 * s * c * B^3 + 810 * s * B^4 - 2058240 * s * c^3 - 3618000 * s * k^2 * B + 4277760 * s * k * c * B + 1819344 * s * c^2 * B - 2370240 * s * k * B^2 - 286816 * s * c * B^2 + 10608 * s * B^3 + 192960 * s * c^2 - 238896 * s * k * B - 49008 * s * c * B + 3744 * s * B^2 - 500)

theorem step8 (s k c B : ℂ) :
    1 * g8 s k c B = (1) * g7 s k c B := by
  dsimp only [g8, g7] <;> ring

theorem zero8 (s k c B : ℂ) (h0 : g0 s k c B = 0) (h1 : g1 s k c B = 0) (h2 : g2 s k c B = 0) (h3 : g3 s k c B = 0) :
    g8 s k c B = 0 := by
  have he := step8 s k c B
  have h7 := zero7 s k c B h0 h1 h2 h3
  simp only [h7, mul_zero, add_zero] at he
  exact (mul_eq_zero.mp he).resolve_left (by norm_num)

def g9 (s k c B : ℂ) : ℂ :=
  (7200 * k * c^3 * B + 1920 * c^4 * B - 5625 * k^3 * B^2 + 8250 * k^2 * c * B^2 - 7200 * k * c^2 * B^2 + 3375 * k^2 * B^3 - 1400 * k * c^2 * B - 1200 * c^3 * B + 1125 * k^2 * B^2 + 105 * k * c * B^2 + 594 * c^2 * B^2 - 135 * k * B^3 - 81 * c * B^3 + 36 * k * c * B + 76 * c^2 * B - 36 * k * B^2 - 12 * c * B^2 - 2560 * c^5 - 8000 * k^2 * c^2 * B + 1024 * c^4 + 1800 * k^2 * c * B - 96 * c^3)

theorem step9 (s k c B : ℂ) :
    1 * g9 s k c B = (1 * B) * g4 s k c B + (-2 * c) * g5 s k c B := by
  dsimp only [g9, g4, g5] <;> ring

theorem zero9 (s k c B : ℂ) (h0 : g0 s k c B = 0) (h1 : g1 s k c B = 0) (h2 : g2 s k c B = 0) (h3 : g3 s k c B = 0) :
    g9 s k c B = 0 := by
  have he := step9 s k c B
  have h4 := zero4 s k c B h0 h1 h2 h3
  have h5 := zero5 s k c B h0 h1 h2 h3
  simp only [h4, h5, mul_zero, add_zero] at he
  exact (mul_eq_zero.mp he).resolve_left (by norm_num)

def g10 (s k c B : ℂ) : ℂ :=
  (-25600 * c^5 - 80000 * k^2 * c^2 * B + 19200 * c^4 * B + 352500 * k^2 * c * B^2 - 72000 * k * c^2 * B^2 + 33750 * k^2 * B^3 - 254720 * c^4 - 810000 * k^2 * c * B + 1062400 * k * c^2 * B - 42240 * c^3 * B - 626625 * k^2 * B^2 + 96900 * k * c * B^2 + 12420 * c^2 * B^2 - 25650 * k * B^3 - 810 * c * B^3 + 105024 * c^3 + 186300 * k^2 * B - 254160 * k * c * B - 75776 * c^2 * B + 142335 * k * B^2 + 1851 * c * B^2 + 1458 * B^3 - 9936 * c^2 + 15876 * k * B + 1332 * c * B + 72 * B^2)

theorem step10 (s k c B : ℂ) :
    1 * g10 s k c B = (10) * g9 s k c B + (-36 * B) * g6 s k c B + (-207) * g5 s k c B := by
  dsimp only [g10, g9, g6, g5] <;> ring

theorem zero10 (s k c B : ℂ) (h0 : g0 s k c B = 0) (h1 : g1 s k c B = 0) (h2 : g2 s k c B = 0) (h3 : g3 s k c B = 0) :
    g10 s k c B = 0 := by
  have he := step10 s k c B
  have h9 := zero9 s k c B h0 h1 h2 h3
  have h6 := zero6 s k c B h0 h1 h2 h3
  have h5 := zero5 s k c B h0 h1 h2 h3
  simp only [h9, h6, h5, mul_zero, add_zero] at he
  exact (mul_eq_zero.mp he).resolve_left (by norm_num)

def g11 (s k c B : ℂ) : ℂ :=
  (25600 * c^5 + 80000 * k^2 * c^2 * B - 19200 * c^4 * B - 352500 * k^2 * c * B^2 + 72000 * k * c^2 * B^2 - 33750 * k^2 * B^3 + 254720 * c^4 + 810000 * k^2 * c * B - 1062400 * k * c^2 * B + 42240 * c^3 * B + 626625 * k^2 * B^2 - 96900 * k * c * B^2 - 12420 * c^2 * B^2 + 25650 * k * B^3 + 810 * c * B^3 - 105024 * c^3 - 186300 * k^2 * B + 254160 * k * c * B + 75776 * c^2 * B - 142335 * k * B^2 - 1851 * c * B^2 - 1458 * B^3 + 9936 * c^2 - 15876 * k * B - 1332 * c * B - 72 * B^2)

theorem step11 (s k c B : ℂ) :
    1 * g11 s k c B = (-1) * g10 s k c B := by
  dsimp only [g11, g10] <;> ring

theorem zero11 (s k c B : ℂ) (h0 : g0 s k c B = 0) (h1 : g1 s k c B = 0) (h2 : g2 s k c B = 0) (h3 : g3 s k c B = 0) :
    g11 s k c B = 0 := by
  have he := step11 s k c B
  have h10 := zero10 s k c B h0 h1 h2 h3
  simp only [h10, mul_zero, add_zero] at he
  exact (mul_eq_zero.mp he).resolve_left (by norm_num)

def g12 (s k c B : ℂ) : ℂ :=
  (2800000 * k^3 * c^2 * B - 96000 * k * c^4 * B - 1762500 * k^3 * c * B^2 + 360000 * k^2 * c^2 * B^2 - 168750 * k^3 * B^3 + 2156800 * k * c^4 + 4050000 * k^3 * c * B - 7688000 * k^2 * c^2 * B + 1209600 * k * c^3 * B + 3133125 * k^3 * B^2 - 484500 * k^2 * c * B^2 - 105300 * k * c^2 * B^2 + 128250 * k^2 * B^3 + 4050 * k * c * B^3 - 896640 * k * c^3 - 931500 * k^3 * B + 1270800 * k^2 * c * B + 704320 * k * c^2 * B - 711675 * k^2 * B^2 - 9255 * k * c * B^2 - 7290 * k * B^3 + 91152 * k * c^2 - 79380 * k^2 * B - 6660 * k * c * B - 360 * k * B^2 + 480000 * k^2 * c^3 * B - 348160 * c^5 + 11520 * c^4 * B + 125952 * c^4 - 132288 * c^3 * B + 22464 * c^2 * B^2 - 13824 * c^3 + 3072 * c^2 * B)

theorem step12 (s k c B : ℂ) :
    1 * g12 s k c B = (5 * k) * g11 s k c B + (-64 * c^2) * g6 s k c B := by
  dsimp only [g12, g11, g6] <;> ring

theorem zero12 (s k c B : ℂ) (h0 : g0 s k c B = 0) (h1 : g1 s k c B = 0) (h2 : g2 s k c B = 0) (h3 : g3 s k c B = 0) :
    g12 s k c B = 0 := by
  have he := step12 s k c B
  have h11 := zero11 s k c B h0 h1 h2 h3
  have h6 := zero6 s k c B h0 h1 h2 h3
  simp only [h11, h6, mul_zero, add_zero] at he
  exact (mul_eq_zero.mp he).resolve_left (by norm_num)

def g13 (s k c B : ℂ) : ℂ :=
  (5800000 * k^2 * c^2 * B + 468000 * c^4 * B + 2175000 * k^2 * c * B^2 - 1080000 * k * c^2 * B^2 - 378000 * c^3 * B^2 - 2531250 * k^2 * B^3 + 1215000 * k * c * B^3 + 726400 * c^4 - 23400000 * k^3 * B - 4320000 * k^2 * c * B + 1168000 * k * c^2 * B - 1232400 * c^3 * B - 3296250 * k^2 * B^2 + 2683500 * k * c * B^2 + 262800 * c^2 * B^2 - 87750 * k * B^3 - 121500 * c * B^3 + 18225 * B^4 - 7257600 * k * c^2 + 2821440 * c^3 + 22288500 * k^2 * B - 11084400 * k * c * B + 789010 * c^2 * B + 1580625 * k * B^2 - 616935 * c * B^2 + 95040 * B^3 + 3162240 * k * c - 1043496 * c^2 - 2680020 * k * B + 1076364 * c * B - 181152 * B^2 - 357696 * k + 119232 * c - 26496 * B)

theorem step13 (s k c B : ℂ) :
    4 * g13 s k c B = (50) * g12 s k c B + (-12000 * k * B + 2400 * c * B + 1120 * c - 5220 * B + 2208) * g6 s k c B + (-72000 * k + 14100 * c + 1350 * B - 23985) * g5 s k c B + (-11200 * c + 5160) * g4 s k c B + (115) * g11 s k c B := by
  dsimp only [g13, g12, g6, g5, g4, g11] <;> ring

theorem zero13 (s k c B : ℂ) (h0 : g0 s k c B = 0) (h1 : g1 s k c B = 0) (h2 : g2 s k c B = 0) (h3 : g3 s k c B = 0) :
    g13 s k c B = 0 := by
  have he := step13 s k c B
  have h12 := zero12 s k c B h0 h1 h2 h3
  have h6 := zero6 s k c B h0 h1 h2 h3
  have h5 := zero5 s k c B h0 h1 h2 h3
  have h4 := zero4 s k c B h0 h1 h2 h3
  have h11 := zero11 s k c B h0 h1 h2 h3
  simp only [h12, h6, h5, h4, h11, mul_zero, add_zero] at he
  exact (mul_eq_zero.mp he).resolve_left (by norm_num)

def g14 (s k c B : ℂ) : ℂ :=
  (5800000 * k^2 * c^2 * B + 468000 * c^4 * B + 2175000 * k^2 * c * B^2 - 1080000 * k * c^2 * B^2 - 378000 * c^3 * B^2 - 2531250 * k^2 * B^3 + 1215000 * k * c * B^3 + 726400 * c^4 - 23400000 * k^3 * B - 4320000 * k^2 * c * B + 1168000 * k * c^2 * B - 1232400 * c^3 * B - 3296250 * k^2 * B^2 + 2683500 * k * c * B^2 + 262800 * c^2 * B^2 - 87750 * k * B^3 - 121500 * c * B^3 + 18225 * B^4 - 7257600 * k * c^2 + 2821440 * c^3 + 22288500 * k^2 * B - 11084400 * k * c * B + 789010 * c^2 * B + 1580625 * k * B^2 - 616935 * c * B^2 + 95040 * B^3 + 3162240 * k * c - 1043496 * c^2 - 2680020 * k * B + 1076364 * c * B - 181152 * B^2 - 357696 * k + 119232 * c - 26496 * B)

theorem step14 (s k c B : ℂ) :
    1 * g14 s k c B = (1) * g13 s k c B := by
  dsimp only [g14, g13] <;> ring

theorem zero14 (s k c B : ℂ) (h0 : g0 s k c B = 0) (h1 : g1 s k c B = 0) (h2 : g2 s k c B = 0) (h3 : g3 s k c B = 0) :
    g14 s k c B = 0 := by
  have he := step14 s k c B
  have h13 := zero13 s k c B h0 h1 h2 h3
  simp only [h13, mul_zero, add_zero] at he
  exact (mul_eq_zero.mp he).resolve_left (by norm_num)

end Mordell.Elimination
