import Mordell.Determinants.Part10

set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Mordell.Determinants

def minor165 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (5 * Y)
    | 0, 1 => ((-20) + ((-2) * T * a))
    | 0, 2 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 1, 1 => (5 * Y)
    | 1, 2 => (((-3) * T * b) + (3 * Y * a))
    | 1, 3 => 1
    | 2, 2 => ((-20) + ((-2) * T * a))
    | 3, 2 => (5 * Y)
    | _, _ => 0
def value165 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant165 (a b c d Y T : ℂ) :
    (minor165 a b c d Y T).det = value165 a b c d Y T := by
  have hm0 : (minor165 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove =
      minor75 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor165 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove =
      minor129 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor165 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove =
      minor163 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (5 * Y) * ((minor165 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * ((-20) + ((-2) * T * a)) * ((minor165 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor165 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * 0 * ((minor165 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value165 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant75, hm1, determinant129, hm2, determinant163]
  dsimp only [value165, value75, value129, value163] <;> ring

def minor166 (a b c d Y T : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => ((-20) + ((-2) * T * a))
    | 0, 1 => (((-3) * T * b) + (3 * Y * a))
    | 0, 2 => (((-2) * b) + (Y * c) + ((-5) * T * d))
    | 0, 3 => a
    | 0, 4 => c
    | 1, 0 => (5 * Y)
    | 1, 1 => ((-20) + ((-2) * T * a))
    | 1, 2 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 1, 4 => b
    | 2, 1 => (5 * Y)
    | 2, 2 => (((-3) * T * b) + (3 * Y * a))
    | 2, 3 => 1
    | 2, 4 => a
    | 3, 2 => ((-20) + ((-2) * T * a))
    | 4, 2 => (5 * Y)
    | 4, 4 => 1
    | _, _ => 0
def value166 (a b c d Y T : ℂ) : ℂ := (8000 + (8 * (T^3) * (a^3)) + (200 * a * (Y^2)) + (240 * (T^2) * (a^2)) + (2400 * T * a) + (20 * T * (Y^2) * (a^2)) + (300 * T * Y * b) + (30 * Y * a * b * (T^2)))

theorem determinant166 (a b c d Y T : ℂ) :
    (minor166 a b c d Y T).det = value166 a b c d Y T := by
  have hm0 : (minor166 a b c d Y T).submatrix Fin.succ (0 : Fin 5).succAbove =
      minor76 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor166 a b c d Y T).submatrix Fin.succ (1 : Fin 5).succAbove =
      minor130 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor166 a b c d Y T).submatrix Fin.succ (2 : Fin 5).succAbove =
      minor164 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor166 a b c d Y T).submatrix Fin.succ (3 : Fin 5).succAbove =
      minor153 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm4 : (minor166 a b c d Y T).submatrix Fin.succ (4 : Fin 5).succAbove =
      minor165 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * ((-20) + ((-2) * T * a)) * ((minor166 a b c d Y T).submatrix Fin.succ (0 : Fin 5).succAbove).det + ((-1 : ℂ)^1 * (((-3) * T * b) + (3 * Y * a)) * ((minor166 a b c d Y T).submatrix Fin.succ (1 : Fin 5).succAbove).det + ((-1 : ℂ)^2 * (((-2) * b) + (Y * c) + ((-5) * T * d)) * ((minor166 a b c d Y T).submatrix Fin.succ (2 : Fin 5).succAbove).det + ((-1 : ℂ)^3 * a * ((minor166 a b c d Y T).submatrix Fin.succ (3 : Fin 5).succAbove).det + ((-1 : ℂ)^4 * c * ((minor166 a b c d Y T).submatrix Fin.succ (4 : Fin 5).succAbove).det + (0))))) = value166 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant76, hm1, determinant130, hm2, determinant164, hm3, determinant153, hm4, determinant165]
  dsimp only [value166, value76, value130, value164, value153, value165] <;> ring

def minor167 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (5 * Y)
    | 0, 1 => ((-20) + ((-2) * T * a))
    | 0, 2 => (((-3) * T * b) + (3 * Y * a))
    | 1, 1 => (5 * Y)
    | 1, 2 => ((-20) + ((-2) * T * a))
    | 1, 3 => 1
    | 2, 2 => (5 * Y)
    | _, _ => 0
def value167 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant167 (a b c d Y T : ℂ) :
    (minor167 a b c d Y T).det = value167 a b c d Y T := by
  have hm0 : (minor167 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove =
      minor87 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor167 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove =
      minor141 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor167 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove =
      minor163 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (5 * Y) * ((minor167 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * ((-20) + ((-2) * T * a)) * ((minor167 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * (((-3) * T * b) + (3 * Y * a)) * ((minor167 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * 0 * ((minor167 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value167 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant87, hm1, determinant141, hm2, determinant163]
  dsimp only [value167, value87, value141, value163] <;> ring

def minor168 (a b c d Y T : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => ((-20) + ((-2) * T * a))
    | 0, 1 => (((-3) * T * b) + (3 * Y * a))
    | 0, 2 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 0, 3 => (((-2) * b) + (Y * c) + ((-5) * T * d))
    | 0, 4 => a
    | 1, 0 => (5 * Y)
    | 1, 1 => ((-20) + ((-2) * T * a))
    | 1, 2 => (((-3) * T * b) + (3 * Y * a))
    | 1, 3 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 2, 1 => (5 * Y)
    | 2, 2 => ((-20) + ((-2) * T * a))
    | 2, 3 => (((-3) * T * b) + (3 * Y * a))
    | 2, 4 => 1
    | 3, 2 => (5 * Y)
    | 3, 3 => ((-20) + ((-2) * T * a))
    | 4, 3 => (5 * Y)
    | _, _ => 0
def value168 (a b c d Y T : ℂ) : ℂ := ((10000 * (Y^2)) + (250 * a * (Y^4)) + (100 * (T^2) * (Y^2) * (a^2)) + (375 * T * b * (Y^3)) + (2000 * T * a * (Y^2)))

theorem determinant168 (a b c d Y T : ℂ) :
    (minor168 a b c d Y T).det = value168 a b c d Y T := by
  have hm0 : (minor168 a b c d Y T).submatrix Fin.succ (0 : Fin 5).succAbove =
      minor89 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor168 a b c d Y T).submatrix Fin.succ (1 : Fin 5).succAbove =
      minor143 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor168 a b c d Y T).submatrix Fin.succ (2 : Fin 5).succAbove =
      minor165 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor168 a b c d Y T).submatrix Fin.succ (3 : Fin 5).succAbove =
      minor167 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm4 : (minor168 a b c d Y T).submatrix Fin.succ (4 : Fin 5).succAbove =
      minor158 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * ((-20) + ((-2) * T * a)) * ((minor168 a b c d Y T).submatrix Fin.succ (0 : Fin 5).succAbove).det + ((-1 : ℂ)^1 * (((-3) * T * b) + (3 * Y * a)) * ((minor168 a b c d Y T).submatrix Fin.succ (1 : Fin 5).succAbove).det + ((-1 : ℂ)^2 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor168 a b c d Y T).submatrix Fin.succ (2 : Fin 5).succAbove).det + ((-1 : ℂ)^3 * (((-2) * b) + (Y * c) + ((-5) * T * d)) * ((minor168 a b c d Y T).submatrix Fin.succ (3 : Fin 5).succAbove).det + ((-1 : ℂ)^4 * a * ((minor168 a b c d Y T).submatrix Fin.succ (4 : Fin 5).succAbove).det + (0))))) = value168 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant89, hm1, determinant143, hm2, determinant165, hm3, determinant167, hm4, determinant158]
  dsimp only [value168, value89, value143, value165, value167, value158] <;> ring

def minor169 (a b c d Y T : ℂ) : Matrix (Fin 6) (Fin 6) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (((-3) * T * b) + (3 * Y * a))
    | 0, 1 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 0, 2 => (((-2) * b) + (Y * c) + ((-5) * T * d))
    | 0, 4 => b
    | 0, 5 => d
    | 1, 0 => ((-20) + ((-2) * T * a))
    | 1, 1 => (((-3) * T * b) + (3 * Y * a))
    | 1, 2 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 1, 3 => (((-2) * b) + (Y * c) + ((-5) * T * d))
    | 1, 4 => a
    | 1, 5 => c
    | 2, 0 => (5 * Y)
    | 2, 1 => ((-20) + ((-2) * T * a))
    | 2, 2 => (((-3) * T * b) + (3 * Y * a))
    | 2, 3 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 2, 5 => b
    | 3, 1 => (5 * Y)
    | 3, 2 => ((-20) + ((-2) * T * a))
    | 3, 3 => (((-3) * T * b) + (3 * Y * a))
    | 3, 4 => 1
    | 3, 5 => a
    | 4, 2 => (5 * Y)
    | 4, 3 => ((-20) + ((-2) * T * a))
    | 5, 3 => (5 * Y)
    | 5, 5 => 1
    | _, _ => 0
def value169 (a b c d Y T : ℂ) : ℂ := ((144000 * b) + ((-40000) * T * d) + ((-10000) * d * (Y^2)) + ((-540) * (T^3) * (b^3)) + (120 * (Y^3) * (a^3)) + (450 * (Y^3) * (b^2)) + (4800 * Y * (a^2)) + (8000 * Y * c) + ((-12000) * a * d * (T^2)) + ((-1200) * d * (T^3) * (a^2)) + ((-400) * a * c * (Y^3)) + ((-250) * a * d * (Y^4)) + ((-54) * a * (T^4) * (b^3)) + ((-40) * d * (T^4) * (a^3)) + ((-8) * b * (T^4) * (a^4)) + (24 * T * (Y^3) * (a^4)) + (24 * Y * (T^3) * (a^5)) + (40 * b * (Y^4) * (a^2)) + (48 * b * (T^3) * (a^3)) + (90 * (T^2) * (Y^2) * (b^3)) + (300 * b * c * (Y^4)) + (400 * T * (Y^3) * (c^2)) + (456 * Y * (T^2) * (a^4)) + (2640 * T * Y * (a^3)) + (3200 * Y * (T^2) * (c^2)) + (4300 * a * b * (Y^2)) + (4800 * b * (T^2) * (a^2)) + (9600 * b * c * (T^2)) + (13200 * T * Y * (b^2)) + (49600 * T * a * b) + ((-5600) * T * Y * a * c) + ((-3750) * T * a * d * (Y^2)) + ((-2320) * Y * c * (T^2) * (a^2)) + ((-350) * d * (T^2) * (Y^2) * (a^2)) + ((-180) * T * c * (Y^3) * (a^2)) + ((-180) * Y * c * (T^3) * (b^2)) + ((-168) * Y * c * (T^3) * (a^3)) + (56 * b * (T^2) * (Y^2) * (a^3)) + (96 * b * c * (T^4) * (a^2)) + (114 * Y * (T^3) * (a^2) * (b^2)) + (150 * T * a * (Y^3) * (b^2)) + (320 * Y * a * (T^3) * (c^2)) + (500 * c * d * (T^2) * (Y^2)) + (600 * T * b * (Y^2) * (a^2)) + (1920 * a * b * c * (T^3)) + (2190 * Y * a * (T^2) * (b^2)) + (4500 * T * b * c * (Y^2)) + (190 * a * b * c * (T^2) * (Y^2)))

theorem determinant169 (a b c d Y T : ℂ) :
    (minor169 a b c d Y T).det = value169 a b c d Y T := by
  have hm0 : (minor169 a b c d Y T).submatrix Fin.succ (0 : Fin 6).succAbove =
      minor90 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor169 a b c d Y T).submatrix Fin.succ (1 : Fin 6).succAbove =
      minor144 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor169 a b c d Y T).submatrix Fin.succ (2 : Fin 6).succAbove =
      minor166 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm4 : (minor169 a b c d Y T).submatrix Fin.succ (4 : Fin 6).succAbove =
      minor159 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm5 : (minor169 a b c d Y T).submatrix Fin.succ (5 : Fin 6).succAbove =
      minor168 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (((-3) * T * b) + (3 * Y * a)) * ((minor169 a b c d Y T).submatrix Fin.succ (0 : Fin 6).succAbove).det + ((-1 : ℂ)^1 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor169 a b c d Y T).submatrix Fin.succ (1 : Fin 6).succAbove).det + ((-1 : ℂ)^2 * (((-2) * b) + (Y * c) + ((-5) * T * d)) * ((minor169 a b c d Y T).submatrix Fin.succ (2 : Fin 6).succAbove).det + ((-1 : ℂ)^3 * 0 * ((minor169 a b c d Y T).submatrix Fin.succ (3 : Fin 6).succAbove).det + ((-1 : ℂ)^4 * b * ((minor169 a b c d Y T).submatrix Fin.succ (4 : Fin 6).succAbove).det + ((-1 : ℂ)^5 * d * ((minor169 a b c d Y T).submatrix Fin.succ (5 : Fin 6).succAbove).det + (0)))))) = value169 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant90, hm1, determinant144, hm2, determinant166, hm4, determinant159, hm5, determinant168]
  dsimp only [value169, value90, value144, value166, value159, value168] <;> ring

def minor170 (a b c d Y T : ℂ) : Matrix (Fin 7) (Fin 7) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 0, 1 => (((-2) * b) + (Y * c) + ((-5) * T * d))
    | 0, 4 => c
    | 0, 5 => d
    | 1, 0 => (((-3) * T * b) + (3 * Y * a))
    | 1, 1 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 1, 2 => (((-2) * b) + (Y * c) + ((-5) * T * d))
    | 1, 4 => b
    | 1, 5 => c
    | 1, 6 => d
    | 2, 0 => ((-20) + ((-2) * T * a))
    | 2, 1 => (((-3) * T * b) + (3 * Y * a))
    | 2, 2 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 2, 3 => (((-2) * b) + (Y * c) + ((-5) * T * d))
    | 2, 4 => a
    | 2, 5 => b
    | 2, 6 => c
    | 3, 0 => (5 * Y)
    | 3, 1 => ((-20) + ((-2) * T * a))
    | 3, 2 => (((-3) * T * b) + (3 * Y * a))
    | 3, 3 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 3, 5 => a
    | 3, 6 => b
    | 4, 1 => (5 * Y)
    | 4, 2 => ((-20) + ((-2) * T * a))
    | 4, 3 => (((-3) * T * b) + (3 * Y * a))
    | 4, 4 => 1
    | 4, 6 => a
    | 5, 2 => (5 * Y)
    | 5, 3 => ((-20) + ((-2) * T * a))
    | 5, 5 => 1
    | 6, 3 => (5 * Y)
    | 6, 6 => 1
    | _, _ => 0
def value170 (a b c d Y T : ℂ) : ℂ := ((7056 * (a^4)) + (160000 * (c^2)) + ((-144000) * b * d) + ((-67200) * c * (a^2)) + ((-11880) * Y * (b^3)) + ((-54) * (Y^4) * (b^4)) + (36 * (T^2) * (b^4)) + (144 * (T^2) * (a^6)) + (144 * (Y^2) * (a^5)) + (256 * (T^4) * (c^4)) + (320 * (Y^4) * (c^3)) + (2016 * T * (a^5)) + (10000 * (Y^2) * (d^2)) + (12800 * (T^2) * (c^3)) + (40000 * T * (d^2)) + (48960 * a * (b^2)) + ((-48000) * Y * c * d) + ((-17664) * T * c * (a^3)) + ((-3584) * (T^2) * (a^2) * (c^2)) + ((-1440) * Y * b * (a^3)) + ((-972) * T * (Y^2) * (b^4)) + ((-768) * (T^3) * (a^3) * (c^2)) + ((-504) * c * (Y^2) * (a^3)) + ((-480) * c * (T^2) * (a^4)) + ((-288) * (T^3) * (b^2) * (c^2)) + ((-216) * a * (T^3) * (b^4)) + ((-200) * (T^3) * (a^2) * (d^2)) + ((-176) * (Y^4) * (a^2) * (c^2)) + ((-160) * a * (Y^2) * (c^2)) + ((-128) * (T^4) * (a^2) * (c^3)) + ((-60) * (T^4) * (a^3) * (d^2)) + ((-32) * (T^3) * (a^4) * (b^2)) + ((-27) * c * (T^4) * (b^4)) + ((-8) * (Y^4) * (a^3) * (b^2)) + (16 * (T^4) * (a^4) * (c^2)) + (24 * c * (Y^4) * (a^4)) + (54 * Y * (T^3) * (b^5)) + (96 * c * (T^3) * (a^5)) + (225 * (T^4) * (b^2) * (d^2)) + (250 * a * (Y^4) * (d^2)) + (625 * Y * (T^3) * (d^3)) + (720 * d * (T^3) * (b^3)) + (868 * (Y^2) * (a^2) * (b^2)) + (956 * (T^2) * (a^3) * (b^2)) + (1536 * a * (T^3) * (c^3)) + (3360 * c * (Y^2) * (b^2)) + (3600 * Y * d * (a^2)) + (4000 * c * (T^3) * (d^2)) + (5760 * T * (Y^2) * (c^3)) + (6240 * T * c * (b^2)) + (8000 * a * (T^2) * (d^2)) + (13768 * T * (a^2) * (b^2)) + (38400 * T * a * (c^2)) + ((-48800) * T * a * b * d) + ((-12400) * b * c * d * (T^2)) + ((-8600) * a * b * d * (Y^2)) + ((-5250) * Y * b * (T^2) * (d^2)) + ((-5140) * b * d * (T^2) * (a^2)) + ((-5100) * T * Y * d * (b^2)) + ((-3168) * T * (Y^2) * (a^2) * (c^2)) + ((-720) * b * d * (T^4) * (c^2)) + ((-600) * b * c * d * (Y^4)) + ((-378) * Y * c * (T^2) * (b^3)) + ((-375) * T * b * (Y^3) * (d^2)) + ((-368) * Y * b * (T^3) * (c^3)) + ((-184) * (T^2) * (Y^2) * (a^3) * (c^2)) + ((-144) * T * (Y^2) * (a^3) * (b^2)) + ((-128) * b * d * (T^3) * (a^3)) + ((-81) * a * d * (T^4) * (b^3)) + ((-80) * b * d * (Y^4) * (a^2)) + ((-54) * a * (T^2) * (Y^2) * (b^4)) + ((-36) * (T^2) * (Y^2) * (b^2) * (c^2)) + ((-27) * T * c * (Y^3) * (b^3)) + ((-12) * b * d * (T^4) * (a^4)) + ((-8) * (T^2) * (Y^2) * (a^4) * (b^2)) + ((-4) * c * (T^4) * (a^3) * (b^2)) + (8 * Y * (T^3) * (a^3) * (b^3)) + (24 * c * (T^2) * (Y^2) * (a^5)) + (36 * T * d * (Y^3) * (a^4)) + (36 * Y * d * (T^3) * (a^5)) + (90 * d * (T^2) * (Y^2) * (b^3)) + (100 * (T^2) * (Y^2) * (a^2) * (d^2)) + (144 * T * Y * b * (a^4)) + (144 * a * (T^4) * (b^2) * (c^2)) + (234 * a * c * (Y^4) * (b^2)) + (352 * a * (T^2) * (Y^2) * (c^3)) + (400 * T * d * (Y^3) * (c^2)) + (400 * a * c * (T^4) * (d^2)) + (432 * T * c * (Y^2) * (a^4)) + (500 * c * (T^2) * (Y^2) * (d^2)) + (504 * Y * d * (T^2) * (a^4)) + (708 * T * Y * a * (b^3)) + (936 * c * (T^3) * (a^2) * (b^2)) + (1620 * T * Y * d * (a^3)) + (4500 * T * a * (Y^2) * (d^2)) + (5200 * a * c * (T^2) * (b^2)) + (5600 * Y * d * (T^2) * (c^2)) + (8560 * T * Y * b * (c^2)) + (20640 * Y * a * b * c) + ((-11600) * T * Y * a * c * d) + ((-10800) * T * b * c * d * (Y^2)) + ((-3640) * Y * c * d * (T^2) * (a^2)) + ((-2560) * a * b * c * d * (T^3)) + ((-1440) * T * b * d * (Y^2) * (a^2)) + ((-1050) * Y * a * b * (T^3) * (d^2)) + ((-364) * T * Y * b * c * (a^2)) + ((-272) * Y * c * d * (T^3) * (a^3)) + ((-261) * Y * a * c * (T^3) * (b^3)) + ((-260) * T * c * d * (Y^3) * (a^2)) + ((-56) * Y * b * c * (T^2) * (a^3)) + ((-56) * b * d * (T^2) * (Y^2) * (a^3)) + ((-28) * Y * b * c * (T^3) * (a^4)) + ((-4) * T * b * c * (Y^3) * (a^3)) + (48 * T * a * b * (Y^3) * (c^2)) + (84 * b * c * d * (T^4) * (a^2)) + (195 * T * a * d * (Y^3) * (b^2)) + (220 * Y * b * (T^3) * (a^2) * (c^2)) + (234 * c * (T^2) * (Y^2) * (a^2) * (b^2)) + (291 * Y * d * (T^3) * (a^2) * (b^2)) + (480 * Y * a * d * (T^3) * (c^2)) + (672 * Y * a * b * (T^2) * (c^2)) + (765 * Y * c * d * (T^3) * (b^2)) + (2730 * Y * a * d * (T^2) * (b^2)) + (4212 * T * a * c * (Y^2) * (b^2)) + ((-620) * a * b * c * d * (T^2) * (Y^2)))

theorem determinant170 (a b c d Y T : ℂ) :
    (minor170 a b c d Y T).det = value170 a b c d Y T := by
  have hm0 : (minor170 a b c d Y T).submatrix Fin.succ (0 : Fin 7).succAbove =
      minor93 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor170 a b c d Y T).submatrix Fin.succ (1 : Fin 7).succAbove =
      minor147 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm4 : (minor170 a b c d Y T).submatrix Fin.succ (4 : Fin 7).succAbove =
      minor162 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm5 : (minor170 a b c d Y T).submatrix Fin.succ (5 : Fin 7).succAbove =
      minor169 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor170 a b c d Y T).submatrix Fin.succ (0 : Fin 7).succAbove).det + ((-1 : ℂ)^1 * (((-2) * b) + (Y * c) + ((-5) * T * d)) * ((minor170 a b c d Y T).submatrix Fin.succ (1 : Fin 7).succAbove).det + ((-1 : ℂ)^2 * 0 * ((minor170 a b c d Y T).submatrix Fin.succ (2 : Fin 7).succAbove).det + ((-1 : ℂ)^3 * 0 * ((minor170 a b c d Y T).submatrix Fin.succ (3 : Fin 7).succAbove).det + ((-1 : ℂ)^4 * c * ((minor170 a b c d Y T).submatrix Fin.succ (4 : Fin 7).succAbove).det + ((-1 : ℂ)^5 * d * ((minor170 a b c d Y T).submatrix Fin.succ (5 : Fin 7).succAbove).det + ((-1 : ℂ)^6 * 0 * ((minor170 a b c d Y T).submatrix Fin.succ (6 : Fin 7).succAbove).det + (0))))))) = value170 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant93, hm1, determinant147, hm4, determinant162, hm5, determinant169]
  dsimp only [value170, value93, value147, value162, value169] <;> ring

def minor171 (a b c d Y T : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => match i.val, j.val with
    | _, _ => 0
def value171 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant171 (a b c d Y T : ℂ) :
    (minor171 a b c d Y T).det = value171 a b c d Y T := by
  rw [show value171 a b c d Y T = 0 by rfl]
  apply Matrix.det_eq_zero_of_row_eq_zero 0
  intro j
  fin_cases j <;> rfl

def minor172 (a b c d Y T : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 2 => a
    | 2, 2 => 1
    | _, _ => 0
def value172 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant172 (a b c d Y T : ℂ) :
    (minor172 a b c d Y T).det = value172 a b c d Y T := by
  have hm2 : (minor172 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove =
      minor171 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * 0 * ((minor172 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove).det + ((-1 : ℂ)^1 * 0 * ((minor172 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove).det + ((-1 : ℂ)^2 * a * ((minor172 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove).det + (0))) = value172 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm2, determinant171]
  dsimp only [value172, value171] <;> ring

def minor173 (a b c d Y T : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => match i.val, j.val with
    | 1, 2 => 1
    | _, _ => 0
def value173 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant173 (a b c d Y T : ℂ) :
    (minor173 a b c d Y T).det = value173 a b c d Y T := by
  rw [show value173 a b c d Y T = 0 by rfl]
  apply Matrix.det_eq_zero_of_row_eq_zero 0
  intro j
  fin_cases j <;> rfl

def minor174 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (5 * Y)
    | 0, 1 => 1
    | 0, 2 => a
    | 0, 3 => b
    | 1, 3 => a
    | 2, 2 => 1
    | 3, 3 => 1
    | _, _ => 0
def value174 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant174 (a b c d Y T : ℂ) :
    (minor174 a b c d Y T).det = value174 a b c d Y T := by
  have hm0 : (minor174 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove =
      minor13 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor174 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove =
      minor124 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor174 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove =
      minor172 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor174 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove =
      minor173 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (5 * Y) * ((minor174 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * 1 * ((minor174 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * a * ((minor174 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * b * ((minor174 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value174 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant13, hm1, determinant124, hm2, determinant172, hm3, determinant173]
  dsimp only [value174, value13, value124, value172, value173] <;> ring

def minor175 (a b c d Y T : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 1 => (((-3) * T * b) + (3 * Y * a))
    | 1, 1 => ((-20) + ((-2) * T * a))
    | 2, 1 => (5 * Y)
    | _, _ => 0
def value175 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant175 (a b c d Y T : ℂ) :
    (minor175 a b c d Y T).det = value175 a b c d Y T := by
  have hm1 : (minor175 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove =
      minor171 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * 0 * ((minor175 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove).det + ((-1 : ℂ)^1 * (((-3) * T * b) + (3 * Y * a)) * ((minor175 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove).det + ((-1 : ℂ)^2 * 0 * ((minor175 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove).det + (0))) = value175 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm1, determinant171]
  dsimp only [value175, value171] <;> ring

def minor176 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (5 * Y)
    | 0, 1 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 0, 2 => 1
    | 0, 3 => b
    | 1, 1 => (((-3) * T * b) + (3 * Y * a))
    | 1, 3 => a
    | 2, 1 => ((-20) + ((-2) * T * a))
    | 3, 1 => (5 * Y)
    | 3, 3 => 1
    | _, _ => 0
def value176 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant176 (a b c d Y T : ℂ) :
    (minor176 a b c d Y T).det = value176 a b c d Y T := by
  have hm0 : (minor176 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove =
      minor19 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor176 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove =
      minor172 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor176 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove =
      minor126 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor176 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove =
      minor175 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (5 * Y) * ((minor176 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor176 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * 1 * ((minor176 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * b * ((minor176 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value176 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant19, hm1, determinant172, hm2, determinant126, hm3, determinant175]
  dsimp only [value176, value19, value172, value126, value175] <;> ring

def minor177 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (5 * Y)
    | 0, 1 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 0, 2 => 1
    | 0, 3 => a
    | 1, 1 => (((-3) * T * b) + (3 * Y * a))
    | 2, 1 => ((-20) + ((-2) * T * a))
    | 2, 3 => 1
    | 3, 1 => (5 * Y)
    | _, _ => 0
def value177 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant177 (a b c d Y T : ℂ) :
    (minor177 a b c d Y T).det = value177 a b c d Y T := by
  have hm0 : (minor177 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove =
      minor20 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor177 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove =
      minor173 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor177 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove =
      minor127 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor177 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove =
      minor175 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (5 * Y) * ((minor177 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor177 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * 1 * ((minor177 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * a * ((minor177 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value177 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant20, hm1, determinant173, hm2, determinant127, hm3, determinant175]
  dsimp only [value177, value20, value173, value127, value175] <;> ring

def minor178 (a b c d Y T : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => ((-20) + ((-2) * T * a))
    | 0, 1 => (((-2) * b) + (Y * c) + ((-5) * T * d))
    | 0, 3 => b
    | 0, 4 => c
    | 1, 0 => (5 * Y)
    | 1, 1 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 1, 2 => 1
    | 1, 3 => a
    | 1, 4 => b
    | 2, 1 => (((-3) * T * b) + (3 * Y * a))
    | 2, 4 => a
    | 3, 1 => ((-20) + ((-2) * T * a))
    | 3, 3 => 1
    | 4, 1 => (5 * Y)
    | 4, 4 => 1
    | _, _ => 0
def value178 (a b c d Y T : ℂ) : ℂ := (((-60) * T * b) + ((-40) * Y * a) + ((-6) * a * b * (T^2)) + ((-4) * T * Y * (a^2)))

theorem determinant178 (a b c d Y T : ℂ) :
    (minor178 a b c d Y T).det = value178 a b c d Y T := by
  have hm0 : (minor178 a b c d Y T).submatrix Fin.succ (0 : Fin 5).succAbove =
      minor21 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor178 a b c d Y T).submatrix Fin.succ (1 : Fin 5).succAbove =
      minor174 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor178 a b c d Y T).submatrix Fin.succ (3 : Fin 5).succAbove =
      minor176 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm4 : (minor178 a b c d Y T).submatrix Fin.succ (4 : Fin 5).succAbove =
      minor177 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * ((-20) + ((-2) * T * a)) * ((minor178 a b c d Y T).submatrix Fin.succ (0 : Fin 5).succAbove).det + ((-1 : ℂ)^1 * (((-2) * b) + (Y * c) + ((-5) * T * d)) * ((minor178 a b c d Y T).submatrix Fin.succ (1 : Fin 5).succAbove).det + ((-1 : ℂ)^2 * 0 * ((minor178 a b c d Y T).submatrix Fin.succ (2 : Fin 5).succAbove).det + ((-1 : ℂ)^3 * b * ((minor178 a b c d Y T).submatrix Fin.succ (3 : Fin 5).succAbove).det + ((-1 : ℂ)^4 * c * ((minor178 a b c d Y T).submatrix Fin.succ (4 : Fin 5).succAbove).det + (0))))) = value178 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant21, hm1, determinant174, hm3, determinant176, hm4, determinant177]
  dsimp only [value178, value21, value174, value176, value177] <;> ring

def minor179 (a b c d Y T : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 1 => ((-20) + ((-2) * T * a))
    | 1, 1 => (5 * Y)
    | _, _ => 0
def value179 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant179 (a b c d Y T : ℂ) :
    (minor179 a b c d Y T).det = value179 a b c d Y T := by
  have hm1 : (minor179 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove =
      minor171 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * 0 * ((minor179 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove).det + ((-1 : ℂ)^1 * ((-20) + ((-2) * T * a)) * ((minor179 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove).det + ((-1 : ℂ)^2 * 0 * ((minor179 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove).det + (0))) = value179 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm1, determinant171]
  dsimp only [value179, value171] <;> ring

end Mordell.Determinants
