import Mordell.Determinants.Part8

set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Mordell.Determinants

def minor135 (a b c d Y T : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 1 => ((-20) + ((-2) * T * a))
    | 1, 1 => (5 * Y)
    | 1, 2 => 1
    | _, _ => 0
def value135 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant135 (a b c d Y T : ℂ) :
    (minor135 a b c d Y T).det = value135 a b c d Y T := by
  have hm1 : (minor135 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove =
      minor121 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * 0 * ((minor135 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove).det + ((-1 : ℂ)^1 * ((-20) + ((-2) * T * a)) * ((minor135 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove).det + ((-1 : ℂ)^2 * 0 * ((minor135 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove).det + (0))) = value135 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm1, determinant121]
  dsimp only [value135, value121] <;> ring

def minor136 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (5 * Y)
    | 0, 1 => (((-3) * T * b) + (3 * Y * a))
    | 0, 2 => a
    | 0, 3 => b
    | 1, 1 => ((-20) + ((-2) * T * a))
    | 1, 3 => a
    | 2, 1 => (5 * Y)
    | 2, 2 => 1
    | 3, 3 => 1
    | _, _ => 0
def value136 (a b c d Y T : ℂ) : ℂ := (((-100) * Y) + ((-10) * T * Y * a))

theorem determinant136 (a b c d Y T : ℂ) :
    (minor136 a b c d Y T).det = value136 a b c d Y T := by
  have hm0 : (minor136 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove =
      minor39 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor136 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove =
      minor124 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor136 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove =
      minor134 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor136 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove =
      minor135 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (5 * Y) * ((minor136 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * (((-3) * T * b) + (3 * Y * a)) * ((minor136 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * a * ((minor136 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * b * ((minor136 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value136 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant39, hm1, determinant124, hm2, determinant134, hm3, determinant135]
  dsimp only [value136, value39, value124, value134, value135] <;> ring

def minor137 (a b c d Y T : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 1 => ((-20) + ((-2) * T * a))
    | 0, 2 => (((-3) * T * b) + (3 * Y * a))
    | 1, 1 => (5 * Y)
    | 1, 2 => ((-20) + ((-2) * T * a))
    | 2, 2 => (5 * Y)
    | _, _ => 0
def value137 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant137 (a b c d Y T : ℂ) :
    (minor137 a b c d Y T).det = value137 a b c d Y T := by
  have hm1 : (minor137 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove =
      minor125 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor137 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove =
      minor133 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * 0 * ((minor137 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove).det + ((-1 : ℂ)^1 * ((-20) + ((-2) * T * a)) * ((minor137 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove).det + ((-1 : ℂ)^2 * (((-3) * T * b) + (3 * Y * a)) * ((minor137 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove).det + (0))) = value137 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm1, determinant125, hm2, determinant133]
  dsimp only [value137, value125, value133] <;> ring

def minor138 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (5 * Y)
    | 0, 1 => (((-3) * T * b) + (3 * Y * a))
    | 0, 2 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 0, 3 => b
    | 1, 1 => ((-20) + ((-2) * T * a))
    | 1, 2 => (((-3) * T * b) + (3 * Y * a))
    | 1, 3 => a
    | 2, 1 => (5 * Y)
    | 2, 2 => ((-20) + ((-2) * T * a))
    | 3, 2 => (5 * Y)
    | 3, 3 => 1
    | _, _ => 0
def value138 (a b c d Y T : ℂ) : ℂ := ((2000 * Y) + (50 * a * (Y^3)) + (20 * Y * (T^2) * (a^2)) + (75 * T * b * (Y^2)) + (400 * T * Y * a))

theorem determinant138 (a b c d Y T : ℂ) :
    (minor138 a b c d Y T).det = value138 a b c d Y T := by
  have hm0 : (minor138 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove =
      minor41 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor138 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove =
      minor126 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor138 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove =
      minor134 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor138 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove =
      minor137 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (5 * Y) * ((minor138 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * (((-3) * T * b) + (3 * Y * a)) * ((minor138 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor138 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * b * ((minor138 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value138 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant41, hm1, determinant126, hm2, determinant134, hm3, determinant137]
  dsimp only [value138, value41, value126, value134, value137] <;> ring

def minor139 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (5 * Y)
    | 0, 1 => (((-3) * T * b) + (3 * Y * a))
    | 0, 2 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 0, 3 => a
    | 1, 1 => ((-20) + ((-2) * T * a))
    | 1, 2 => (((-3) * T * b) + (3 * Y * a))
    | 2, 1 => (5 * Y)
    | 2, 2 => ((-20) + ((-2) * T * a))
    | 2, 3 => 1
    | 3, 2 => (5 * Y)
    | _, _ => 0
def value139 (a b c d Y T : ℂ) : ℂ := ((500 * (Y^2)) + (50 * T * a * (Y^2)))

theorem determinant139 (a b c d Y T : ℂ) :
    (minor139 a b c d Y T).det = value139 a b c d Y T := by
  have hm0 : (minor139 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove =
      minor42 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor139 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove =
      minor127 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor139 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove =
      minor135 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor139 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove =
      minor137 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (5 * Y) * ((minor139 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * (((-3) * T * b) + (3 * Y * a)) * ((minor139 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor139 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * a * ((minor139 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value139 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant42, hm1, determinant127, hm2, determinant135, hm3, determinant137]
  dsimp only [value139, value42, value127, value135, value137] <;> ring

def minor140 (a b c d Y T : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => ((-20) + ((-2) * T * a))
    | 0, 1 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 0, 2 => (((-2) * b) + (Y * c) + ((-5) * T * d))
    | 0, 3 => b
    | 0, 4 => c
    | 1, 0 => (5 * Y)
    | 1, 1 => (((-3) * T * b) + (3 * Y * a))
    | 1, 2 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 1, 3 => a
    | 1, 4 => b
    | 2, 1 => ((-20) + ((-2) * T * a))
    | 2, 2 => (((-3) * T * b) + (3 * Y * a))
    | 2, 4 => a
    | 3, 1 => (5 * Y)
    | 3, 2 => ((-20) + ((-2) * T * a))
    | 3, 3 => 1
    | 4, 2 => (5 * Y)
    | 4, 4 => 1
    | _, _ => 0
def value140 (a b c d Y T : ℂ) : ℂ := (((-5600) * a) + ((-1920) * T * (a^2)) + ((-600) * Y * b) + ((-216) * (T^2) * (a^3)) + ((-180) * (T^2) * (b^2)) + ((-140) * (Y^2) * (a^2)) + ((-8) * (T^3) * (a^4)) + (400 * c * (Y^2)) + (1600 * T * c) + ((-45) * T * (Y^2) * (b^2)) + ((-30) * a * b * (Y^3)) + ((-18) * a * (T^3) * (b^2)) + ((-8) * T * (Y^2) * (a^3)) + (16 * c * (T^3) * (a^2)) + (320 * a * c * (T^2)) + (500 * T * Y * d) + ((-470) * T * Y * a * b) + ((-60) * Y * b * c * (T^2)) + ((-32) * Y * b * (T^2) * (a^2)) + (50 * Y * a * d * (T^2)))

theorem determinant140 (a b c d Y T : ℂ) :
    (minor140 a b c d Y T).det = value140 a b c d Y T := by
  have hm0 : (minor140 a b c d Y T).submatrix Fin.succ (0 : Fin 5).succAbove =
      minor43 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor140 a b c d Y T).submatrix Fin.succ (1 : Fin 5).succAbove =
      minor128 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor140 a b c d Y T).submatrix Fin.succ (2 : Fin 5).succAbove =
      minor136 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor140 a b c d Y T).submatrix Fin.succ (3 : Fin 5).succAbove =
      minor138 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm4 : (minor140 a b c d Y T).submatrix Fin.succ (4 : Fin 5).succAbove =
      minor139 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * ((-20) + ((-2) * T * a)) * ((minor140 a b c d Y T).submatrix Fin.succ (0 : Fin 5).succAbove).det + ((-1 : ℂ)^1 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor140 a b c d Y T).submatrix Fin.succ (1 : Fin 5).succAbove).det + ((-1 : ℂ)^2 * (((-2) * b) + (Y * c) + ((-5) * T * d)) * ((minor140 a b c d Y T).submatrix Fin.succ (2 : Fin 5).succAbove).det + ((-1 : ℂ)^3 * b * ((minor140 a b c d Y T).submatrix Fin.succ (3 : Fin 5).succAbove).det + ((-1 : ℂ)^4 * c * ((minor140 a b c d Y T).submatrix Fin.succ (4 : Fin 5).succAbove).det + (0))))) = value140 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant43, hm1, determinant128, hm2, determinant136, hm3, determinant138, hm4, determinant139]
  dsimp only [value140, value43, value128, value136, value138, value139] <;> ring

def minor141 (a b c d Y T : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 1 => ((-20) + ((-2) * T * a))
    | 0, 2 => 1
    | 1, 1 => (5 * Y)
    | _, _ => 0
def value141 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant141 (a b c d Y T : ℂ) :
    (minor141 a b c d Y T).det = value141 a b c d Y T := by
  have hm1 : (minor141 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove =
      minor118 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor141 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove =
      minor133 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * 0 * ((minor141 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove).det + ((-1 : ℂ)^1 * ((-20) + ((-2) * T * a)) * ((minor141 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove).det + ((-1 : ℂ)^2 * 1 * ((minor141 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove).det + (0))) = value141 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm1, determinant118, hm2, determinant133]
  dsimp only [value141, value118, value133] <;> ring

def minor142 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (5 * Y)
    | 0, 1 => (((-3) * T * b) + (3 * Y * a))
    | 0, 3 => b
    | 1, 1 => ((-20) + ((-2) * T * a))
    | 1, 2 => 1
    | 1, 3 => a
    | 2, 1 => (5 * Y)
    | 3, 3 => 1
    | _, _ => 0
def value142 (a b c d Y T : ℂ) : ℂ := ((-25) * (Y^2))

theorem determinant142 (a b c d Y T : ℂ) :
    (minor142 a b c d Y T).det = value142 a b c d Y T := by
  have hm0 : (minor142 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove =
      minor34 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor142 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove =
      minor119 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor142 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove =
      minor141 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (5 * Y) * ((minor142 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * (((-3) * T * b) + (3 * Y * a)) * ((minor142 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * 0 * ((minor142 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * b * ((minor142 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value142 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant34, hm1, determinant119, hm3, determinant141]
  dsimp only [value142, value34, value119, value141] <;> ring

def minor143 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (5 * Y)
    | 0, 1 => (((-3) * T * b) + (3 * Y * a))
    | 0, 2 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 1, 1 => ((-20) + ((-2) * T * a))
    | 1, 2 => (((-3) * T * b) + (3 * Y * a))
    | 1, 3 => 1
    | 2, 1 => (5 * Y)
    | 2, 2 => ((-20) + ((-2) * T * a))
    | 3, 2 => (5 * Y)
    | _, _ => 0
def value143 (a b c d Y T : ℂ) : ℂ := (125 * (Y^3))

theorem determinant143 (a b c d Y T : ℂ) :
    (minor143 a b c d Y T).det = value143 a b c d Y T := by
  have hm0 : (minor143 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove =
      minor44 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor143 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove =
      minor129 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor143 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove =
      minor141 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (5 * Y) * ((minor143 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * (((-3) * T * b) + (3 * Y * a)) * ((minor143 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor143 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * 0 * ((minor143 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value143 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant44, hm1, determinant129, hm2, determinant141]
  dsimp only [value143, value44, value129, value141] <;> ring

def minor144 (a b c d Y T : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => ((-20) + ((-2) * T * a))
    | 0, 1 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 0, 2 => (((-2) * b) + (Y * c) + ((-5) * T * d))
    | 0, 3 => a
    | 0, 4 => c
    | 1, 0 => (5 * Y)
    | 1, 1 => (((-3) * T * b) + (3 * Y * a))
    | 1, 2 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 1, 4 => b
    | 2, 1 => ((-20) + ((-2) * T * a))
    | 2, 2 => (((-3) * T * b) + (3 * Y * a))
    | 2, 3 => 1
    | 2, 4 => a
    | 3, 1 => (5 * Y)
    | 3, 2 => ((-20) + ((-2) * T * a))
    | 4, 2 => (5 * Y)
    | 4, 4 => 1
    | _, _ => 0
def value144 (a b c d Y T : ℂ) : ℂ := (((-2000) * Y * a) + ((-50) * (Y^3) * (a^2)) + (100 * c * (Y^3)) + (150 * b * (Y^2)) + (1200 * T * b) + ((-520) * T * Y * (a^2)) + ((-32) * Y * (T^2) * (a^3)) + (12 * b * (T^3) * (a^2)) + (125 * T * d * (Y^2)) + (240 * a * b * (T^2)) + (800 * T * Y * c) + ((-65) * T * a * b * (Y^2)) + (80 * Y * a * c * (T^2)))

theorem determinant144 (a b c d Y T : ℂ) :
    (minor144 a b c d Y T).det = value144 a b c d Y T := by
  have hm0 : (minor144 a b c d Y T).submatrix Fin.succ (0 : Fin 5).succAbove =
      minor45 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor144 a b c d Y T).submatrix Fin.succ (1 : Fin 5).succAbove =
      minor130 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor144 a b c d Y T).submatrix Fin.succ (2 : Fin 5).succAbove =
      minor142 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor144 a b c d Y T).submatrix Fin.succ (3 : Fin 5).succAbove =
      minor138 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm4 : (minor144 a b c d Y T).submatrix Fin.succ (4 : Fin 5).succAbove =
      minor143 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * ((-20) + ((-2) * T * a)) * ((minor144 a b c d Y T).submatrix Fin.succ (0 : Fin 5).succAbove).det + ((-1 : ℂ)^1 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor144 a b c d Y T).submatrix Fin.succ (1 : Fin 5).succAbove).det + ((-1 : ℂ)^2 * (((-2) * b) + (Y * c) + ((-5) * T * d)) * ((minor144 a b c d Y T).submatrix Fin.succ (2 : Fin 5).succAbove).det + ((-1 : ℂ)^3 * a * ((minor144 a b c d Y T).submatrix Fin.succ (3 : Fin 5).succAbove).det + ((-1 : ℂ)^4 * c * ((minor144 a b c d Y T).submatrix Fin.succ (4 : Fin 5).succAbove).det + (0))))) = value144 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant45, hm1, determinant130, hm2, determinant142, hm3, determinant138, hm4, determinant143]
  dsimp only [value144, value45, value130, value142, value138, value143] <;> ring

def minor145 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (5 * Y)
    | 0, 1 => (((-3) * T * b) + (3 * Y * a))
    | 0, 3 => a
    | 1, 1 => ((-20) + ((-2) * T * a))
    | 1, 2 => 1
    | 2, 1 => (5 * Y)
    | 2, 3 => 1
    | _, _ => 0
def value145 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant145 (a b c d Y T : ℂ) :
    (minor145 a b c d Y T).det = value145 a b c d Y T := by
  have hm0 : (minor145 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove =
      minor37 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor145 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove =
      minor122 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor145 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove =
      minor141 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (5 * Y) * ((minor145 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * (((-3) * T * b) + (3 * Y * a)) * ((minor145 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * 0 * ((minor145 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * a * ((minor145 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value145 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant37, hm1, determinant122, hm3, determinant141]
  dsimp only [value145, value37, value122, value141] <;> ring

def minor146 (a b c d Y T : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => ((-20) + ((-2) * T * a))
    | 0, 1 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 0, 2 => (((-2) * b) + (Y * c) + ((-5) * T * d))
    | 0, 3 => a
    | 0, 4 => b
    | 1, 0 => (5 * Y)
    | 1, 1 => (((-3) * T * b) + (3 * Y * a))
    | 1, 2 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 1, 4 => a
    | 2, 1 => ((-20) + ((-2) * T * a))
    | 2, 2 => (((-3) * T * b) + (3 * Y * a))
    | 2, 3 => 1
    | 3, 1 => (5 * Y)
    | 3, 2 => ((-20) + ((-2) * T * a))
    | 3, 4 => 1
    | 4, 2 => (5 * Y)
    | _, _ => 0
def value146 (a b c d Y T : ℂ) : ℂ := (((-150) * a * (Y^2)) + (75 * b * (Y^3)) + ((-30) * T * (Y^2) * (a^2)) + (100 * T * c * (Y^2)) + (300 * T * Y * b) + (30 * Y * a * b * (T^2)))

theorem determinant146 (a b c d Y T : ℂ) :
    (minor146 a b c d Y T).det = value146 a b c d Y T := by
  have hm0 : (minor146 a b c d Y T).submatrix Fin.succ (0 : Fin 5).succAbove =
      minor46 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor146 a b c d Y T).submatrix Fin.succ (1 : Fin 5).succAbove =
      minor131 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor146 a b c d Y T).submatrix Fin.succ (2 : Fin 5).succAbove =
      minor145 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor146 a b c d Y T).submatrix Fin.succ (3 : Fin 5).succAbove =
      minor139 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm4 : (minor146 a b c d Y T).submatrix Fin.succ (4 : Fin 5).succAbove =
      minor143 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * ((-20) + ((-2) * T * a)) * ((minor146 a b c d Y T).submatrix Fin.succ (0 : Fin 5).succAbove).det + ((-1 : ℂ)^1 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor146 a b c d Y T).submatrix Fin.succ (1 : Fin 5).succAbove).det + ((-1 : ℂ)^2 * (((-2) * b) + (Y * c) + ((-5) * T * d)) * ((minor146 a b c d Y T).submatrix Fin.succ (2 : Fin 5).succAbove).det + ((-1 : ℂ)^3 * a * ((minor146 a b c d Y T).submatrix Fin.succ (3 : Fin 5).succAbove).det + ((-1 : ℂ)^4 * b * ((minor146 a b c d Y T).submatrix Fin.succ (4 : Fin 5).succAbove).det + (0))))) = value146 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant46, hm1, determinant131, hm2, determinant145, hm3, determinant139, hm4, determinant143]
  dsimp only [value146, value46, value131, value145, value139, value143] <;> ring

def minor147 (a b c d Y T : ℂ) : Matrix (Fin 6) (Fin 6) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (((-3) * T * b) + (3 * Y * a))
    | 0, 1 => (((-2) * b) + (Y * c) + ((-5) * T * d))
    | 0, 3 => b
    | 0, 4 => c
    | 0, 5 => d
    | 1, 0 => ((-20) + ((-2) * T * a))
    | 1, 1 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 1, 2 => (((-2) * b) + (Y * c) + ((-5) * T * d))
    | 1, 3 => a
    | 1, 4 => b
    | 1, 5 => c
    | 2, 0 => (5 * Y)
    | 2, 1 => (((-3) * T * b) + (3 * Y * a))
    | 2, 2 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 2, 4 => a
    | 2, 5 => b
    | 3, 1 => ((-20) + ((-2) * T * a))
    | 3, 2 => (((-3) * T * b) + (3 * Y * a))
    | 3, 3 => 1
    | 3, 5 => a
    | 4, 1 => (5 * Y)
    | 4, 2 => ((-20) + ((-2) * T * a))
    | 4, 4 => 1
    | 5, 2 => (5 * Y)
    | 5, 5 => 1
    | _, _ => 0
def value147 (a b c d Y T : ℂ) : ℂ := ((12 * (Y^3) * (a^4)) + (18 * (T^2) * (b^3)) + (80 * (Y^3) * (c^2)) + (540 * Y * (b^2)) + (588 * Y * (a^3)) + (5040 * a * b) + ((-1720) * Y * a * c) + ((-1400) * T * a * d) + ((-340) * d * (T^2) * (a^2)) + ((-240) * T * b * c) + ((-180) * b * c * (Y^2)) + ((-75) * b * d * (Y^3)) + ((-64) * c * (Y^3) * (a^2)) + ((-48) * b * (T^3) * (c^2)) + ((-27) * a * (T^3) * (b^3)) + ((-24) * b * (Y^2) * (a^2)) + ((-20) * d * (T^3) * (a^3)) + ((-4) * b * (T^3) * (a^4)) + (12 * Y * (T^2) * (a^5)) + (18 * T * (Y^2) * (b^3)) + (40 * b * (T^2) * (a^3)) + (45 * d * (T^3) * (b^2)) + (57 * a * (Y^3) * (b^2)) + (125 * Y * (T^2) * (d^2)) + (150 * a * d * (Y^2)) + (168 * T * Y * (a^4)) + (400 * c * d * (T^2)) + (720 * T * Y * (c^2)) + (1196 * T * b * (a^2)) + ((-900) * T * Y * b * d) + ((-788) * T * Y * c * (a^2)) + ((-76) * Y * c * (T^2) * (a^3)) + ((-50) * T * d * (Y^2) * (a^2)) + (8 * T * b * (Y^2) * (a^3)) + (24 * Y * c * (T^2) * (b^2)) + (40 * a * c * d * (T^3)) + (44 * b * c * (T^3) * (a^2)) + (65 * Y * (T^2) * (a^2) * (b^2)) + (100 * T * c * d * (Y^2)) + (120 * Y * a * (T^2) * (c^2)) + (272 * a * b * c * (T^2)) + (738 * T * Y * a * (b^2)) + ((-190) * Y * a * b * d * (T^2)) + (14 * T * a * b * c * (Y^2)))

theorem determinant147 (a b c d Y T : ℂ) :
    (minor147 a b c d Y T).det = value147 a b c d Y T := by
  have hm0 : (minor147 a b c d Y T).submatrix Fin.succ (0 : Fin 6).succAbove =
      minor47 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor147 a b c d Y T).submatrix Fin.succ (1 : Fin 6).succAbove =
      minor132 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor147 a b c d Y T).submatrix Fin.succ (3 : Fin 6).succAbove =
      minor140 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm4 : (minor147 a b c d Y T).submatrix Fin.succ (4 : Fin 6).succAbove =
      minor144 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm5 : (minor147 a b c d Y T).submatrix Fin.succ (5 : Fin 6).succAbove =
      minor146 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (((-3) * T * b) + (3 * Y * a)) * ((minor147 a b c d Y T).submatrix Fin.succ (0 : Fin 6).succAbove).det + ((-1 : ℂ)^1 * (((-2) * b) + (Y * c) + ((-5) * T * d)) * ((minor147 a b c d Y T).submatrix Fin.succ (1 : Fin 6).succAbove).det + ((-1 : ℂ)^2 * 0 * ((minor147 a b c d Y T).submatrix Fin.succ (2 : Fin 6).succAbove).det + ((-1 : ℂ)^3 * b * ((minor147 a b c d Y T).submatrix Fin.succ (3 : Fin 6).succAbove).det + ((-1 : ℂ)^4 * c * ((minor147 a b c d Y T).submatrix Fin.succ (4 : Fin 6).succAbove).det + ((-1 : ℂ)^5 * d * ((minor147 a b c d Y T).submatrix Fin.succ (5 : Fin 6).succAbove).det + (0)))))) = value147 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant47, hm1, determinant132, hm3, determinant140, hm4, determinant144, hm5, determinant146]
  dsimp only [value147, value47, value132, value140, value144, value146] <;> ring

def minor148 (a b c d Y T : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => match i.val, j.val with
    | _, _ => 0
def value148 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant148 (a b c d Y T : ℂ) :
    (minor148 a b c d Y T).det = value148 a b c d Y T := by
  rw [show value148 a b c d Y T = 0 by rfl]
  apply Matrix.det_eq_zero_of_row_eq_zero 0
  intro j
  fin_cases j <;> rfl

def minor149 (a b c d Y T : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 1 => (5 * Y)
    | 0, 2 => a
    | 2, 2 => 1
    | _, _ => 0
def value149 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant149 (a b c d Y T : ℂ) :
    (minor149 a b c d Y T).det = value149 a b c d Y T := by
  have hm1 : (minor149 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove =
      minor117 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor149 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove =
      minor148 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * 0 * ((minor149 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove).det + ((-1 : ℂ)^1 * (5 * Y) * ((minor149 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove).det + ((-1 : ℂ)^2 * a * ((minor149 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove).det + (0))) = value149 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm1, determinant117, hm2, determinant148]
  dsimp only [value149, value117, value148] <;> ring

end Mordell.Determinants
