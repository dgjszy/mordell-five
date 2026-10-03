import Mordell.CoefficientData

set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Mordell.Exceptional

namespace Ten

def g0 (ss d c : ℂ) : ℂ := (-5625 * d^3 - 960 * d * c^2 + 108 * d * c + 1600 * d * c^3 + 12500 * d^3 * c)

def g1 (ss d c : ℂ) : ℂ := (-225 * d^2 - 128 * c^3 + 12 * c^2 + 320 * c^4 + 1000 * d^2 * c)

def g2 (ss d c : ℂ) : ℂ := (648 * d + 37500 * d^3 - 5805 * d * c - 2000 * d * c^3 + 13800 * d * c^2)

def g3 (ss d c : ℂ) : ℂ := (-3125 * d^3 + 27 * d - 2000 * d * c^3 - 315 * d * c + 1200 * d * c^2)

def g4 (ss d c : ℂ) : ℂ := (-1 - 128 * ss * c^4 + 16 * ss * c^3 + 108 * ss * d^2 + 256 * ss * c^5 + 3125 * ss * d^4 - 900 * ss * d^2 * c + 2000 * ss * d^2 * c^2)

def g5 (ss d c : ℂ) : ℂ := (12500 * d^3 * c + 1600 * d * c^3 - 5625 * d^3 - 960 * d * c^2 + 108 * d * c)

theorem step5 (ss d c : ℂ) : 1*g5 ss d c = (1) * g0 ss d c := by
  dsimp only [g5, g0] <;> ring

theorem zero5 (ss d c : ℂ) (h0 : g0 ss d c = 0) (h1 : g1 ss d c = 0) (h2 : g2 ss d c = 0) (h3 : g3 ss d c = 0) (h4 : g4 ss d c = 0) : g5 ss d c = 0 := by
  have he := step5 ss d c
  simp only [h0, mul_zero, add_zero] at he
  exact (mul_eq_zero.mp he).resolve_left (by norm_num)

def g6 (ss d c : ℂ) : ℂ := (320 * c^4 + 1000 * d^2 * c - 128 * c^3 - 225 * d^2 + 12 * c^2)

theorem step6 (ss d c : ℂ) : 1*g6 ss d c = (1) * g1 ss d c := by
  dsimp only [g6, g1] <;> ring

theorem zero6 (ss d c : ℂ) (h0 : g0 ss d c = 0) (h1 : g1 ss d c = 0) (h2 : g2 ss d c = 0) (h3 : g3 ss d c = 0) (h4 : g4 ss d c = 0) : g6 ss d c = 0 := by
  have he := step6 ss d c
  simp only [h1, mul_zero, add_zero] at he
  exact (mul_eq_zero.mp he).resolve_left (by norm_num)

def g7 (ss d c : ℂ) : ℂ := (2000 * d * c^3 - 37500 * d^3 - 13800 * d * c^2 + 5805 * d * c - 648 * d)

theorem step7 (ss d c : ℂ) : 1*g7 ss d c = (-1) * g2 ss d c := by
  dsimp only [g7, g2] <;> ring

theorem zero7 (ss d c : ℂ) (h0 : g0 ss d c = 0) (h1 : g1 ss d c = 0) (h2 : g2 ss d c = 0) (h3 : g3 ss d c = 0) (h4 : g4 ss d c = 0) : g7 ss d c = 0 := by
  have he := step7 ss d c
  simp only [h2, mul_zero, add_zero] at he
  exact (mul_eq_zero.mp he).resolve_left (by norm_num)

def g8 (ss d c : ℂ) : ℂ := (-40625 * d^3 - 12600 * d * c^2 + 5490 * d * c - 621 * d)

theorem step8 (ss d c : ℂ) : 1*g8 ss d c = (1) * g3 ss d c + (-1) * g2 ss d c := by
  dsimp only [g8, g3, g2] <;> ring

theorem zero8 (ss d c : ℂ) (h0 : g0 ss d c = 0) (h1 : g1 ss d c = 0) (h2 : g2 ss d c = 0) (h3 : g3 ss d c = 0) (h4 : g4 ss d c = 0) : g8 ss d c = 0 := by
  have he := step8 ss d c
  simp only [h3, h2, mul_zero, add_zero] at he
  exact (mul_eq_zero.mp he).resolve_left (by norm_num)

def g9 (ss d c : ℂ) : ℂ := (40625 * d^3 + 12600 * d * c^2 - 5490 * d * c + 621 * d)

theorem step9 (ss d c : ℂ) : 1*g9 ss d c = (-1) * g8 ss d c := by
  dsimp only [g9, g8] <;> ring

theorem zero9 (ss d c : ℂ) (h0 : g0 ss d c = 0) (h1 : g1 ss d c = 0) (h2 : g2 ss d c = 0) (h3 : g3 ss d c = 0) (h4 : g4 ss d c = 0) : g9 ss d c = 0 := by
  have he := step9 ss d c
  have h8 := zero8 ss d c h0 h1 h2 h3 h4
  simp only [h8, mul_zero, add_zero] at he
  exact (mul_eq_zero.mp he).resolve_left (by norm_num)

def g10 (ss d c : ℂ) : ℂ := (78125 * ss * d^4 + 30000 * ss * d^2 * c^2 - 16000 * ss * d^2 * c - 96 * ss * c^3 + 2250 * ss * d^2 + 24 * ss * c^2 - 25)

theorem step10 (ss d c : ℂ) : 1*g10 ss d c = (25) * g4 ss d c + (-20 * ss * c + 2 * ss) * g1 ss d c := by
  dsimp only [g10, g4, g1] <;> ring

theorem zero10 (ss d c : ℂ) (h0 : g0 ss d c = 0) (h1 : g1 ss d c = 0) (h2 : g2 ss d c = 0) (h3 : g3 ss d c = 0) (h4 : g4 ss d c = 0) : g10 ss d c = 0 := by
  have he := step10 ss d c
  simp only [h4, h1, mul_zero, add_zero] at he
  exact (mul_eq_zero.mp he).resolve_left (by norm_num)

def g11 (ss d c : ℂ) : ℂ := (78125 * ss * d^4 + 30000 * ss * d^2 * c^2 - 16000 * ss * d^2 * c - 96 * ss * c^3 + 2250 * ss * d^2 + 24 * ss * c^2 - 25)

theorem step11 (ss d c : ℂ) : 1*g11 ss d c = (1) * g10 ss d c := by
  dsimp only [g11, g10] <;> ring

theorem zero11 (ss d c : ℂ) (h0 : g0 ss d c = 0) (h1 : g1 ss d c = 0) (h2 : g2 ss d c = 0) (h3 : g3 ss d c = 0) (h4 : g4 ss d c = 0) : g11 ss d c = 0 := by
  have he := step11 ss d c
  have h10 := zero10 ss d c h0 h1 h2 h3 h4
  simp only [h10, mul_zero, add_zero] at he
  exact (mul_eq_zero.mp he).resolve_left (by norm_num)

def g12 (ss d c : ℂ) : ℂ := (75000 * ss * d^2 * c^2 - 70750 * ss * d^2 * c - 1248 * ss * c^3 + 13725 * ss * d^2 + 312 * ss * c^2 - 325)

theorem step12 (ss d c : ℂ) : 1*g12 ss d c = (13) * g11 ss d c + (-25 * ss * d) * g9 ss d c := by
  dsimp only [g12, g11, g9] <;> ring

theorem zero12 (ss d c : ℂ) (h0 : g0 ss d c = 0) (h1 : g1 ss d c = 0) (h2 : g2 ss d c = 0) (h3 : g3 ss d c = 0) (h4 : g4 ss d c = 0) : g12 ss d c = 0 := by
  have he := step12 ss d c
  have h11 := zero11 ss d c h0 h1 h2 h3 h4
  have h9 := zero9 ss d c h0 h1 h2 h3 h4
  simp only [h11, h9, mul_zero, add_zero] at he
  exact (mul_eq_zero.mp he).resolve_left (by norm_num)

def g13 (ss d c : ℂ) : ℂ := (75000 * ss * d^2 * c^2 - 70750 * ss * d^2 * c - 1248 * ss * c^3 + 13725 * ss * d^2 + 312 * ss * c^2 - 325)

theorem step13 (ss d c : ℂ) : 1*g13 ss d c = (1) * g12 ss d c := by
  dsimp only [g13, g12] <;> ring

theorem zero13 (ss d c : ℂ) (h0 : g0 ss d c = 0) (h1 : g1 ss d c = 0) (h2 : g2 ss d c = 0) (h3 : g3 ss d c = 0) (h4 : g4 ss d c = 0) : g13 ss d c = 0 := by
  have he := step13 ss d c
  have h12 := zero12 ss d c h0 h1 h2 h3 h4
  simp only [h12, mul_zero, add_zero] at he
  exact (mul_eq_zero.mp he).resolve_left (by norm_num)

def g14 (ss d c : ℂ) : ℂ := (-5920 * d * c^3 - 14625 * d^3 + 1896 * d * c^2 - 216 * d * c)

theorem step14 (ss d c : ℂ) : 5*g14 ss d c = (13) * g5 ss d c + (-4 * c) * g9 ss d c := by
  dsimp only [g14, g5, g9] <;> ring

theorem zero14 (ss d c : ℂ) (h0 : g0 ss d c = 0) (h1 : g1 ss d c = 0) (h2 : g2 ss d c = 0) (h3 : g3 ss d c = 0) (h4 : g4 ss d c = 0) : g14 ss d c = 0 := by
  have he := step14 ss d c
  have h5 := zero5 ss d c h0 h1 h2 h3 h4
  have h9 := zero9 ss d c h0 h1 h2 h3 h4
  simp only [h5, h9, mul_zero, add_zero] at he
  exact (mul_eq_zero.mp he).resolve_left (by norm_num)

def g15 (ss d c : ℂ) : ℂ := (400 * d * c^2 - 360 * d * c + 81 * d)

theorem step15 (ss d c : ℂ) : 9*g15 ss d c = (325) * g14 ss d c + (1005) * g9 ss d c + (962) * g7 ss d c := by
  dsimp only [g15, g14, g9, g7] <;> ring

theorem zero15 (ss d c : ℂ) (h0 : g0 ss d c = 0) (h1 : g1 ss d c = 0) (h2 : g2 ss d c = 0) (h3 : g3 ss d c = 0) (h4 : g4 ss d c = 0) : g15 ss d c = 0 := by
  have he := step15 ss d c
  have h14 := zero14 ss d c h0 h1 h2 h3 h4
  have h9 := zero9 ss d c h0 h1 h2 h3 h4
  have h7 := zero7 ss d c h0 h1 h2 h3 h4
  simp only [h14, h9, h7, mul_zero, add_zero] at he
  exact (mul_eq_zero.mp he).resolve_left (by norm_num)

def g16 (ss d c : ℂ) : ℂ := (400 * d * c^2 - 360 * d * c + 81 * d)

theorem step16 (ss d c : ℂ) : 1*g16 ss d c = (1) * g15 ss d c := by
  dsimp only [g16, g15] <;> ring

theorem zero16 (ss d c : ℂ) (h0 : g0 ss d c = 0) (h1 : g1 ss d c = 0) (h2 : g2 ss d c = 0) (h3 : g3 ss d c = 0) (h4 : g4 ss d c = 0) : g16 ss d c = 0 := by
  have he := step16 ss d c
  have h15 := zero15 ss d c h0 h1 h2 h3 h4
  simp only [h15, mul_zero, add_zero] at he
  exact (mul_eq_zero.mp he).resolve_left (by norm_num)

def g20 (ss d c : ℂ) : ℂ := (500 * ss * d^2 * c + 225 * ss * d^2 + 192 * ss * c^3 - 48 * ss * c^2 + 50)

theorem step20 (ss d c : ℂ) : 13*g20 ss d c = (375 * ss * d) * g16 ss d c + (-2) * g13 ss d c := by
  dsimp only [g20, g16, g13] <;> ring

theorem zero20 (ss d c : ℂ) (h0 : g0 ss d c = 0) (h1 : g1 ss d c = 0) (h2 : g2 ss d c = 0) (h3 : g3 ss d c = 0) (h4 : g4 ss d c = 0) : g20 ss d c = 0 := by
  have he := step20 ss d c
  have h16 := zero16 ss d c h0 h1 h2 h3 h4
  have h13 := zero13 ss d c h0 h1 h2 h3 h4
  simp only [h16, h13, mul_zero, add_zero] at he
  exact (mul_eq_zero.mp he).resolve_left (by norm_num)

def g21 (ss d c : ℂ) : ℂ := (500 * ss * d^2 * c + 192 * ss * c^3 + 225 * ss * d^2 - 48 * ss * c^2 + 50)

theorem step21 (ss d c : ℂ) : 1*g21 ss d c = (1) * g20 ss d c := by
  dsimp only [g21, g20] <;> ring

theorem zero21 (ss d c : ℂ) (h0 : g0 ss d c = 0) (h1 : g1 ss d c = 0) (h2 : g2 ss d c = 0) (h3 : g3 ss d c = 0) (h4 : g4 ss d c = 0) : g21 ss d c = 0 := by
  have he := step21 ss d c
  have h20 := zero20 ss d c h0 h1 h2 h3 h4
  simp only [h20, mul_zero, add_zero] at he
  exact (mul_eq_zero.mp he).resolve_left (by norm_num)

def g22 (ss d c : ℂ) : ℂ := (768 * ss * c^4 + 2700 * ss * d^2 * c - 192 * ss * c^3 + 200 * c - 405 * ss * d^2)

theorem step22 (ss d c : ℂ) : 1*g22 ss d c = (4 * c) * g21 ss d c + (-5 * ss * d) * g16 ss d c := by
  dsimp only [g22, g21, g16] <;> ring

theorem zero22 (ss d c : ℂ) (h0 : g0 ss d c = 0) (h1 : g1 ss d c = 0) (h2 : g2 ss d c = 0) (h3 : g3 ss d c = 0) (h4 : g4 ss d c = 0) : g22 ss d c = 0 := by
  have he := step22 ss d c
  have h21 := zero21 ss d c h0 h1 h2 h3 h4
  have h16 := zero16 ss d c h0 h1 h2 h3 h4
  simp only [h21, h16, mul_zero, add_zero] at he
  exact (mul_eq_zero.mp he).resolve_left (by norm_num)

def g23 (ss d c : ℂ) : ℂ := (20 * c - 3)

theorem step23 (ss d c : ℂ) : 50*g23 ss d c = (5) * g22 ss d c + (-12 * ss) * g6 ss d c + (-3) * g21 ss d c := by
  dsimp only [g23, g22, g6, g21] <;> ring

theorem zero23 (ss d c : ℂ) (h0 : g0 ss d c = 0) (h1 : g1 ss d c = 0) (h2 : g2 ss d c = 0) (h3 : g3 ss d c = 0) (h4 : g4 ss d c = 0) : g23 ss d c = 0 := by
  have he := step23 ss d c
  have h22 := zero22 ss d c h0 h1 h2 h3 h4
  have h6 := zero6 ss d c h0 h1 h2 h3 h4
  have h21 := zero21 ss d c h0 h1 h2 h3 h4
  simp only [h22, h6, h21, mul_zero, add_zero] at he
  exact (mul_eq_zero.mp he).resolve_left (by norm_num)

def g24 (ss d c : ℂ) : ℂ := (20 * c - 3)

theorem step24 (ss d c : ℂ) : 1*g24 ss d c = (1) * g23 ss d c := by
  dsimp only [g24, g23] <;> ring

theorem zero24 (ss d c : ℂ) (h0 : g0 ss d c = 0) (h1 : g1 ss d c = 0) (h2 : g2 ss d c = 0) (h3 : g3 ss d c = 0) (h4 : g4 ss d c = 0) : g24 ss d c = 0 := by
  have he := step24 ss d c
  have h23 := zero23 ss d c h0 h1 h2 h3 h4
  simp only [h23, mul_zero, add_zero] at he
  exact (mul_eq_zero.mp he).resolve_left (by norm_num)

def g25 (ss d c : ℂ) : ℂ := (100 * d * c - 27 * d)

theorem step25 (ss d c : ℂ) : 3*g25 ss d c = (20 * d * c) * g24 ss d c + (-1) * g16 ss d c := by
  dsimp only [g25, g24, g16] <;> ring

theorem zero25 (ss d c : ℂ) (h0 : g0 ss d c = 0) (h1 : g1 ss d c = 0) (h2 : g2 ss d c = 0) (h3 : g3 ss d c = 0) (h4 : g4 ss d c = 0) : g25 ss d c = 0 := by
  have he := step25 ss d c
  have h24 := zero24 ss d c h0 h1 h2 h3 h4
  have h16 := zero16 ss d c h0 h1 h2 h3 h4
  simp only [h24, h16, mul_zero, add_zero] at he
  exact (mul_eq_zero.mp he).resolve_left (by norm_num)

def g26 (ss d c : ℂ) : ℂ := (-1 * d)

theorem step26 (ss d c : ℂ) : 12*g26 ss d c = (1) * g25 ss d c + (-5 * d) * g24 ss d c := by
  dsimp only [g26, g25, g24] <;> ring

theorem zero26 (ss d c : ℂ) (h0 : g0 ss d c = 0) (h1 : g1 ss d c = 0) (h2 : g2 ss d c = 0) (h3 : g3 ss d c = 0) (h4 : g4 ss d c = 0) : g26 ss d c = 0 := by
  have he := step26 ss d c
  have h25 := zero25 ss d c h0 h1 h2 h3 h4
  have h24 := zero24 ss d c h0 h1 h2 h3 h4
  simp only [h25, h24, mul_zero, add_zero] at he
  exact (mul_eq_zero.mp he).resolve_left (by norm_num)

def g27 (ss d c : ℂ) : ℂ := (1 * d)

theorem step27 (ss d c : ℂ) : 1*g27 ss d c = (-1) * g26 ss d c := by
  dsimp only [g27, g26] <;> ring

theorem zero27 (ss d c : ℂ) (h0 : g0 ss d c = 0) (h1 : g1 ss d c = 0) (h2 : g2 ss d c = 0) (h3 : g3 ss d c = 0) (h4 : g4 ss d c = 0) : g27 ss d c = 0 := by
  have he := step27 ss d c
  have h26 := zero26 ss d c h0 h1 h2 h3 h4
  simp only [h26, mul_zero, add_zero] at he
  exact (mul_eq_zero.mp he).resolve_left (by norm_num)

end Ten

namespace One

def g0 (ss d c : ℂ) : ℂ := (27 * c + 320 * c^4 + 3375 * d^2 - 2700 * d * c^2 + 12500 * d^3 * c)

def g1 (ss d c : ℂ) : ℂ := (27 - 400 * c^3 + 3125 * d^3 + 1125 * d * c)

def g2 (ss d c : ℂ) : ℂ := (-135 * d + 36 * c^2 - 400 * d * c^3 + 1500 * d^2 * c)

def g3 (ss d c : ℂ) : ℂ := (27 - 6250 * d^3 - 40 * c^3 - 450 * d * c + 5000 * d^2 * c^2)

def g4 (ss d c : ℂ) : ℂ := (-1 - 27 * ss * c^2 + 108 * ss * d + 256 * ss * c^5 + 3125 * ss * d^4 - 1600 * ss * d * c^3 + 2250 * ss * d^2 * c)

def g5 (ss d c : ℂ) : ℂ := (12500 * d^3 * c + 320 * c^4 - 2700 * d * c^2 + 3375 * d^2 + 27 * c)

theorem step5 (ss d c : ℂ) : 1*g5 ss d c = (1) * g0 ss d c := by
  dsimp only [g5, g0] <;> ring

theorem zero5 (ss d c : ℂ) (h0 : g0 ss d c = 0) (h1 : g1 ss d c = 0) (h2 : g2 ss d c = 0) (h3 : g3 ss d c = 0) (h4 : g4 ss d c = 0) : g5 ss d c = 0 := by
  have he := step5 ss d c
  simp only [h0, mul_zero, add_zero] at he
  exact (mul_eq_zero.mp he).resolve_left (by norm_num)

def g6 (ss d c : ℂ) : ℂ := (3125 * d^3 - 400 * c^3 + 1125 * d * c + 27)

theorem step6 (ss d c : ℂ) : 1*g6 ss d c = (1) * g1 ss d c := by
  dsimp only [g6, g1] <;> ring

theorem zero6 (ss d c : ℂ) (h0 : g0 ss d c = 0) (h1 : g1 ss d c = 0) (h2 : g2 ss d c = 0) (h3 : g3 ss d c = 0) (h4 : g4 ss d c = 0) : g6 ss d c = 0 := by
  have he := step6 ss d c
  simp only [h1, mul_zero, add_zero] at he
  exact (mul_eq_zero.mp he).resolve_left (by norm_num)

def g7 (ss d c : ℂ) : ℂ := (400 * d * c^3 - 1500 * d^2 * c - 36 * c^2 + 135 * d)

theorem step7 (ss d c : ℂ) : 1*g7 ss d c = (-1) * g2 ss d c := by
  dsimp only [g7, g2] <;> ring

theorem zero7 (ss d c : ℂ) (h0 : g0 ss d c = 0) (h1 : g1 ss d c = 0) (h2 : g2 ss d c = 0) (h3 : g3 ss d c = 0) (h4 : g4 ss d c = 0) : g7 ss d c = 0 := by
  have he := step7 ss d c
  simp only [h2, mul_zero, add_zero] at he
  exact (mul_eq_zero.mp he).resolve_left (by norm_num)

def g10 (ss d c : ℂ) : ℂ := (256 * ss * c^5 - 3375 * ss * d^2 * c - 135 * ss * c^2 + 486 * ss * d - 1)

theorem step10 (ss d c : ℂ) : 1*g10 ss d c = (1) * g4 ss d c + (-1 * ss * d) * g1 ss d c + (-3 * ss) * g2 ss d c := by
  dsimp only [g10, g4, g1, g2] <;> ring

theorem zero10 (ss d c : ℂ) (h0 : g0 ss d c = 0) (h1 : g1 ss d c = 0) (h2 : g2 ss d c = 0) (h3 : g3 ss d c = 0) (h4 : g4 ss d c = 0) : g10 ss d c = 0 := by
  have he := step10 ss d c
  simp only [h4, h1, h2, mul_zero, add_zero] at he
  exact (mul_eq_zero.mp he).resolve_left (by norm_num)

def g11 (ss d c : ℂ) : ℂ := (256 * ss * c^5 - 3375 * ss * d^2 * c - 135 * ss * c^2 + 486 * ss * d - 1)

theorem step11 (ss d c : ℂ) : 1*g11 ss d c = (1) * g10 ss d c := by
  dsimp only [g11, g10] <;> ring

theorem zero11 (ss d c : ℂ) (h0 : g0 ss d c = 0) (h1 : g1 ss d c = 0) (h2 : g2 ss d c = 0) (h3 : g3 ss d c = 0) (h4 : g4 ss d c = 0) : g11 ss d c = 0 := by
  have he := step11 ss d c
  have h10 := zero10 ss d c h0 h1 h2 h3 h4
  simp only [h10, mul_zero, add_zero] at he
  exact (mul_eq_zero.mp he).resolve_left (by norm_num)

def g12 (ss d c : ℂ) : ℂ := (640 * c^4 - 2400 * d * c^2 + 1125 * d^2 - 27 * c)

theorem step12 (ss d c : ℂ) : 3*g12 ss d c = (1) * g5 ss d c + (-4 * c) * g6 ss d c := by
  dsimp only [g12, g5, g6] <;> ring

theorem zero12 (ss d c : ℂ) (h0 : g0 ss d c = 0) (h1 : g1 ss d c = 0) (h2 : g2 ss d c = 0) (h3 : g3 ss d c = 0) (h4 : g4 ss d c = 0) : g12 ss d c = 0 := by
  have he := step12 ss d c
  have h5 := zero5 ss d c h0 h1 h2 h3 h4
  have h6 := zero6 ss d c h0 h1 h2 h3 h4
  simp only [h5, h6, mul_zero, add_zero] at he
  exact (mul_eq_zero.mp he).resolve_left (by norm_num)

def g13 (ss d c : ℂ) : ℂ := (640 * c^4 - 2400 * d * c^2 + 1125 * d^2 - 27 * c)

theorem step13 (ss d c : ℂ) : 1*g13 ss d c = (1) * g12 ss d c := by
  dsimp only [g13, g12] <;> ring

theorem zero13 (ss d c : ℂ) (h0 : g0 ss d c = 0) (h1 : g1 ss d c = 0) (h2 : g2 ss d c = 0) (h3 : g3 ss d c = 0) (h4 : g4 ss d c = 0) : g13 ss d c = 0 := by
  have he := step13 ss d c
  have h12 := zero12 ss d c h0 h1 h2 h3 h4
  simp only [h12, mul_zero, add_zero] at he
  exact (mul_eq_zero.mp he).resolve_left (by norm_num)

def g14 (ss d c : ℂ) : ℂ := (625 * d^3 - 135 * d * c + 32 * c^3)

theorem step14 (ss d c : ℂ) : 9*g14 ss d c = (5 * d) * g13 ss d c + (-8 * c) * g7 ss d c := by
  dsimp only [g14, g13, g7] <;> ring

theorem zero14 (ss d c : ℂ) (h0 : g0 ss d c = 0) (h1 : g1 ss d c = 0) (h2 : g2 ss d c = 0) (h3 : g3 ss d c = 0) (h4 : g4 ss d c = 0) : g14 ss d c = 0 := by
  have he := step14 ss d c
  have h13 := zero13 ss d c h0 h1 h2 h3 h4
  have h7 := zero7 ss d c h0 h1 h2 h3 h4
  simp only [h13, h7, mul_zero, add_zero] at he
  exact (mul_eq_zero.mp he).resolve_left (by norm_num)

def g15 (ss d c : ℂ) : ℂ := (560 * c^3 - 1800 * d * c - 27)

theorem step15 (ss d c : ℂ) : 1*g15 ss d c = (5) * g14 ss d c + (-1) * g6 ss d c := by
  dsimp only [g15, g14, g6] <;> ring

theorem zero15 (ss d c : ℂ) (h0 : g0 ss d c = 0) (h1 : g1 ss d c = 0) (h2 : g2 ss d c = 0) (h3 : g3 ss d c = 0) (h4 : g4 ss d c = 0) : g15 ss d c = 0 := by
  have he := step15 ss d c
  have h14 := zero14 ss d c h0 h1 h2 h3 h4
  have h6 := zero6 ss d c h0 h1 h2 h3 h4
  simp only [h14, h6, mul_zero, add_zero] at he
  exact (mul_eq_zero.mp he).resolve_left (by norm_num)

def g16 (ss d c : ℂ) : ℂ := (560 * c^3 - 1800 * d * c - 27)

theorem step16 (ss d c : ℂ) : 1*g16 ss d c = (1) * g15 ss d c := by
  dsimp only [g16, g15] <;> ring

theorem zero16 (ss d c : ℂ) (h0 : g0 ss d c = 0) (h1 : g1 ss d c = 0) (h2 : g2 ss d c = 0) (h3 : g3 ss d c = 0) (h4 : g4 ss d c = 0) : g16 ss d c = 0 := by
  have he := step16 ss d c
  have h15 := zero15 ss d c h0 h1 h2 h3 h4
  simp only [h15, mul_zero, add_zero] at he
  exact (mul_eq_zero.mp he).resolve_left (by norm_num)

def g19 (ss d c : ℂ) : ℂ := (125 * d^2 * c - 90 * d + 21 * c^2)

theorem step19 (ss d c : ℂ) : 12*g19 ss d c = (5 * d) * g16 ss d c + (-7) * g7 ss d c := by
  dsimp only [g19, g16, g7] <;> ring

theorem zero19 (ss d c : ℂ) (h0 : g0 ss d c = 0) (h1 : g1 ss d c = 0) (h2 : g2 ss d c = 0) (h3 : g3 ss d c = 0) (h4 : g4 ss d c = 0) : g19 ss d c = 0 := by
  have he := step19 ss d c
  have h16 := zero16 ss d c h0 h1 h2 h3 h4
  have h7 := zero7 ss d c h0 h1 h2 h3 h4
  simp only [h16, h7, mul_zero, add_zero] at he
  exact (mul_eq_zero.mp he).resolve_left (by norm_num)

def g20 (ss d c : ℂ) : ℂ := (125 * d^2 * c + 21 * c^2 - 90 * d)

theorem step20 (ss d c : ℂ) : 1*g20 ss d c = (1) * g19 ss d c := by
  dsimp only [g20, g19] <;> ring

theorem zero20 (ss d c : ℂ) (h0 : g0 ss d c = 0) (h1 : g1 ss d c = 0) (h2 : g2 ss d c = 0) (h3 : g3 ss d c = 0) (h4 : g4 ss d c = 0) : g20 ss d c = 0 := by
  have he := step20 ss d c
  have h19 := zero19 ss d c h0 h1 h2 h3 h4
  simp only [h19, mul_zero, add_zero] at he
  exact (mul_eq_zero.mp he).resolve_left (by norm_num)

def g25 (ss d c : ℂ) : ℂ := (-4800 * ss * d * c^3 + 19125 * ss * d^2 * c + 621 * ss * c^2 - 2430 * ss * d + 5)

theorem step25 (ss d c : ℂ) : 1*g25 ss d c = (2 * ss * c) * g13 ss d c + (-5) * g11 ss d c := by
  dsimp only [g25, g13, g11] <;> ring

theorem zero25 (ss d c : ℂ) (h0 : g0 ss d c = 0) (h1 : g1 ss d c = 0) (h2 : g2 ss d c = 0) (h3 : g3 ss d c = 0) (h4 : g4 ss d c = 0) : g25 ss d c = 0 := by
  have he := step25 ss d c
  have h13 := zero13 ss d c h0 h1 h2 h3 h4
  have h11 := zero11 ss d c h0 h1 h2 h3 h4
  simp only [h13, h11, mul_zero, add_zero] at he
  exact (mul_eq_zero.mp he).resolve_left (by norm_num)

def g26 (ss d c : ℂ) : ℂ := (1)

theorem step26 (ss d c : ℂ) : 35*g26 ss d c = (7) * g25 ss d c + (60 * ss * d) * g16 ss d c + (-207 * ss) * g20 ss d c := by
  dsimp only [g26, g25, g16, g20] <;> ring

theorem zero26 (ss d c : ℂ) (h0 : g0 ss d c = 0) (h1 : g1 ss d c = 0) (h2 : g2 ss d c = 0) (h3 : g3 ss d c = 0) (h4 : g4 ss d c = 0) : g26 ss d c = 0 := by
  have he := step26 ss d c
  have h25 := zero25 ss d c h0 h1 h2 h3 h4
  have h16 := zero16 ss d c h0 h1 h2 h3 h4
  have h20 := zero20 ss d c h0 h1 h2 h3 h4
  simp only [h25, h16, h20, mul_zero, add_zero] at he
  exact (mul_eq_zero.mp he).resolve_left (by norm_num)

def g27 (ss d c : ℂ) : ℂ := (1)

theorem step27 (ss d c : ℂ) : 1*g27 ss d c = (1) * g26 ss d c := by
  dsimp only [g27, g26] <;> ring

theorem zero27 (ss d c : ℂ) (h0 : g0 ss d c = 0) (h1 : g1 ss d c = 0) (h2 : g2 ss d c = 0) (h3 : g3 ss d c = 0) (h4 : g4 ss d c = 0) : g27 ss d c = 0 := by
  have he := step27 ss d c
  have h26 := zero26 ss d c h0 h1 h2 h3 h4
  simp only [h26, mul_zero, add_zero] at he
  exact (mul_eq_zero.mp he).resolve_left (by norm_num)

end One

end Mordell.Exceptional
