import Mordell.Determinants.Part16

set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Mordell.Determinants

def minor255 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 1 => (5 * Y)
    | 0, 2 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 0, 3 => a
    | 1, 2 => (((-3) * T * b) + (3 * Y * a))
    | 2, 2 => ((-20) + ((-2) * T * a))
    | 2, 3 => 1
    | 3, 2 => (5 * Y)
    | _, _ => 0
def value255 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant255 (a b c d Y T : ℂ) :
    (minor255 a b c d Y T).det = value255 a b c d Y T := by
  have hm1 : (minor255 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove =
      minor205 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor255 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove =
      minor251 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor255 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove =
      minor253 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * 0 * ((minor255 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * (5 * Y) * ((minor255 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor255 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * a * ((minor255 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value255 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm1, determinant205, hm2, determinant251, hm3, determinant253]
  dsimp only [value255, value205, value251, value253] <;> ring

def minor256 (a b c d Y T : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (5 * Y)
    | 0, 1 => ((-20) + ((-2) * T * a))
    | 0, 2 => (((-2) * b) + (Y * c) + ((-5) * T * d))
    | 0, 3 => b
    | 0, 4 => c
    | 1, 1 => (5 * Y)
    | 1, 2 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 1, 3 => a
    | 1, 4 => b
    | 2, 2 => (((-3) * T * b) + (3 * Y * a))
    | 2, 4 => a
    | 3, 2 => ((-20) + ((-2) * T * a))
    | 3, 3 => 1
    | 4, 2 => (5 * Y)
    | 4, 4 => 1
    | _, _ => 0
def value256 (a b c d Y T : ℂ) : ℂ := (((-50) * a * (Y^3)) + ((-75) * T * b * (Y^2)))

theorem determinant256 (a b c d Y T : ℂ) :
    (minor256 a b c d Y T).det = value256 a b c d Y T := by
  have hm0 : (minor256 a b c d Y T).submatrix Fin.succ (0 : Fin 5).succAbove =
      minor128 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor256 a b c d Y T).submatrix Fin.succ (1 : Fin 5).succAbove =
      minor206 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor256 a b c d Y T).submatrix Fin.succ (2 : Fin 5).succAbove =
      minor252 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor256 a b c d Y T).submatrix Fin.succ (3 : Fin 5).succAbove =
      minor254 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm4 : (minor256 a b c d Y T).submatrix Fin.succ (4 : Fin 5).succAbove =
      minor255 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (5 * Y) * ((minor256 a b c d Y T).submatrix Fin.succ (0 : Fin 5).succAbove).det + ((-1 : ℂ)^1 * ((-20) + ((-2) * T * a)) * ((minor256 a b c d Y T).submatrix Fin.succ (1 : Fin 5).succAbove).det + ((-1 : ℂ)^2 * (((-2) * b) + (Y * c) + ((-5) * T * d)) * ((minor256 a b c d Y T).submatrix Fin.succ (2 : Fin 5).succAbove).det + ((-1 : ℂ)^3 * b * ((minor256 a b c d Y T).submatrix Fin.succ (3 : Fin 5).succAbove).det + ((-1 : ℂ)^4 * c * ((minor256 a b c d Y T).submatrix Fin.succ (4 : Fin 5).succAbove).det + (0))))) = value256 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant128, hm1, determinant206, hm2, determinant252, hm3, determinant254, hm4, determinant255]
  dsimp only [value256, value128, value206, value252, value254, value255] <;> ring

def minor257 (a b c d Y T : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 2 => ((-20) + ((-2) * T * a))
    | 1, 2 => (5 * Y)
    | _, _ => 0
def value257 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant257 (a b c d Y T : ℂ) :
    (minor257 a b c d Y T).det = value257 a b c d Y T := by
  have hm2 : (minor257 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove =
      minor249 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * 0 * ((minor257 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove).det + ((-1 : ℂ)^1 * 0 * ((minor257 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove).det + ((-1 : ℂ)^2 * ((-20) + ((-2) * T * a)) * ((minor257 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove).det + (0))) = value257 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm2, determinant249]
  dsimp only [value257, value249] <;> ring

def minor258 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 1 => (5 * Y)
    | 0, 2 => (((-3) * T * b) + (3 * Y * a))
    | 0, 3 => b
    | 1, 2 => ((-20) + ((-2) * T * a))
    | 1, 3 => a
    | 2, 2 => (5 * Y)
    | 3, 3 => 1
    | _, _ => 0
def value258 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant258 (a b c d Y T : ℂ) :
    (minor258 a b c d Y T).det = value258 a b c d Y T := by
  have hm1 : (minor258 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove =
      minor212 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor258 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove =
      minor250 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor258 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove =
      minor257 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * 0 * ((minor258 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * (5 * Y) * ((minor258 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * (((-3) * T * b) + (3 * Y * a)) * ((minor258 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * b * ((minor258 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value258 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm1, determinant212, hm2, determinant250, hm3, determinant257]
  dsimp only [value258, value212, value250, value257] <;> ring

def minor259 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 1 => (5 * Y)
    | 0, 2 => (((-3) * T * b) + (3 * Y * a))
    | 0, 3 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 1, 2 => ((-20) + ((-2) * T * a))
    | 1, 3 => (((-3) * T * b) + (3 * Y * a))
    | 2, 2 => (5 * Y)
    | 2, 3 => ((-20) + ((-2) * T * a))
    | 3, 3 => (5 * Y)
    | _, _ => 0
def value259 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant259 (a b c d Y T : ℂ) :
    (minor259 a b c d Y T).det = value259 a b c d Y T := by
  have hm1 : (minor259 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove =
      minor215 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor259 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove =
      minor253 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor259 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove =
      minor257 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * 0 * ((minor259 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * (5 * Y) * ((minor259 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * (((-3) * T * b) + (3 * Y * a)) * ((minor259 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor259 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value259 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm1, determinant215, hm2, determinant253, hm3, determinant257]
  dsimp only [value259, value215, value253, value257] <;> ring

def minor260 (a b c d Y T : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (5 * Y)
    | 0, 1 => ((-20) + ((-2) * T * a))
    | 0, 2 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 0, 3 => (((-2) * b) + (Y * c) + ((-5) * T * d))
    | 0, 4 => c
    | 1, 1 => (5 * Y)
    | 1, 2 => (((-3) * T * b) + (3 * Y * a))
    | 1, 3 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 1, 4 => b
    | 2, 2 => ((-20) + ((-2) * T * a))
    | 2, 3 => (((-3) * T * b) + (3 * Y * a))
    | 2, 4 => a
    | 3, 2 => (5 * Y)
    | 3, 3 => ((-20) + ((-2) * T * a))
    | 4, 3 => (5 * Y)
    | 4, 4 => 1
    | _, _ => 0
def value260 (a b c d Y T : ℂ) : ℂ := ((10000 * (Y^2)) + (250 * a * (Y^4)) + (100 * (T^2) * (Y^2) * (a^2)) + (375 * T * b * (Y^3)) + (2000 * T * a * (Y^2)))

theorem determinant260 (a b c d Y T : ℂ) :
    (minor260 a b c d Y T).det = value260 a b c d Y T := by
  have hm0 : (minor260 a b c d Y T).submatrix Fin.succ (0 : Fin 5).succAbove =
      minor138 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor260 a b c d Y T).submatrix Fin.succ (1 : Fin 5).succAbove =
      minor216 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor260 a b c d Y T).submatrix Fin.succ (2 : Fin 5).succAbove =
      minor254 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor260 a b c d Y T).submatrix Fin.succ (3 : Fin 5).succAbove =
      minor258 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm4 : (minor260 a b c d Y T).submatrix Fin.succ (4 : Fin 5).succAbove =
      minor259 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (5 * Y) * ((minor260 a b c d Y T).submatrix Fin.succ (0 : Fin 5).succAbove).det + ((-1 : ℂ)^1 * ((-20) + ((-2) * T * a)) * ((minor260 a b c d Y T).submatrix Fin.succ (1 : Fin 5).succAbove).det + ((-1 : ℂ)^2 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor260 a b c d Y T).submatrix Fin.succ (2 : Fin 5).succAbove).det + ((-1 : ℂ)^3 * (((-2) * b) + (Y * c) + ((-5) * T * d)) * ((minor260 a b c d Y T).submatrix Fin.succ (3 : Fin 5).succAbove).det + ((-1 : ℂ)^4 * c * ((minor260 a b c d Y T).submatrix Fin.succ (4 : Fin 5).succAbove).det + (0))))) = value260 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant138, hm1, determinant216, hm2, determinant254, hm3, determinant258, hm4, determinant259]
  dsimp only [value260, value138, value216, value254, value258, value259] <;> ring

def minor261 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 1 => (5 * Y)
    | 0, 2 => (((-3) * T * b) + (3 * Y * a))
    | 0, 3 => a
    | 1, 2 => ((-20) + ((-2) * T * a))
    | 2, 2 => (5 * Y)
    | 2, 3 => 1
    | _, _ => 0
def value261 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant261 (a b c d Y T : ℂ) :
    (minor261 a b c d Y T).det = value261 a b c d Y T := by
  have hm1 : (minor261 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove =
      minor213 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor261 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove =
      minor251 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor261 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove =
      minor257 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * 0 * ((minor261 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * (5 * Y) * ((minor261 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * (((-3) * T * b) + (3 * Y * a)) * ((minor261 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * a * ((minor261 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value261 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm1, determinant213, hm2, determinant251, hm3, determinant257]
  dsimp only [value261, value213, value251, value257] <;> ring

def minor262 (a b c d Y T : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (5 * Y)
    | 0, 1 => ((-20) + ((-2) * T * a))
    | 0, 2 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 0, 3 => (((-2) * b) + (Y * c) + ((-5) * T * d))
    | 0, 4 => b
    | 1, 1 => (5 * Y)
    | 1, 2 => (((-3) * T * b) + (3 * Y * a))
    | 1, 3 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 1, 4 => a
    | 2, 2 => ((-20) + ((-2) * T * a))
    | 2, 3 => (((-3) * T * b) + (3 * Y * a))
    | 3, 2 => (5 * Y)
    | 3, 3 => ((-20) + ((-2) * T * a))
    | 3, 4 => 1
    | 4, 3 => (5 * Y)
    | _, _ => 0
def value262 (a b c d Y T : ℂ) : ℂ := ((2500 * (Y^3)) + (250 * T * a * (Y^3)))

theorem determinant262 (a b c d Y T : ℂ) :
    (minor262 a b c d Y T).det = value262 a b c d Y T := by
  have hm0 : (minor262 a b c d Y T).submatrix Fin.succ (0 : Fin 5).succAbove =
      minor139 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor262 a b c d Y T).submatrix Fin.succ (1 : Fin 5).succAbove =
      minor217 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor262 a b c d Y T).submatrix Fin.succ (2 : Fin 5).succAbove =
      minor255 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor262 a b c d Y T).submatrix Fin.succ (3 : Fin 5).succAbove =
      minor261 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm4 : (minor262 a b c d Y T).submatrix Fin.succ (4 : Fin 5).succAbove =
      minor259 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (5 * Y) * ((minor262 a b c d Y T).submatrix Fin.succ (0 : Fin 5).succAbove).det + ((-1 : ℂ)^1 * ((-20) + ((-2) * T * a)) * ((minor262 a b c d Y T).submatrix Fin.succ (1 : Fin 5).succAbove).det + ((-1 : ℂ)^2 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor262 a b c d Y T).submatrix Fin.succ (2 : Fin 5).succAbove).det + ((-1 : ℂ)^3 * (((-2) * b) + (Y * c) + ((-5) * T * d)) * ((minor262 a b c d Y T).submatrix Fin.succ (3 : Fin 5).succAbove).det + ((-1 : ℂ)^4 * b * ((minor262 a b c d Y T).submatrix Fin.succ (4 : Fin 5).succAbove).det + (0))))) = value262 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant139, hm1, determinant217, hm2, determinant255, hm3, determinant261, hm4, determinant259]
  dsimp only [value262, value139, value217, value255, value261, value259] <;> ring

def minor263 (a b c d Y T : ℂ) : Matrix (Fin 6) (Fin 6) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => ((-20) + ((-2) * T * a))
    | 0, 1 => (((-3) * T * b) + (3 * Y * a))
    | 0, 2 => (((-2) * b) + (Y * c) + ((-5) * T * d))
    | 0, 4 => c
    | 0, 5 => d
    | 1, 0 => (5 * Y)
    | 1, 1 => ((-20) + ((-2) * T * a))
    | 1, 2 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 1, 3 => (((-2) * b) + (Y * c) + ((-5) * T * d))
    | 1, 4 => b
    | 1, 5 => c
    | 2, 1 => (5 * Y)
    | 2, 2 => (((-3) * T * b) + (3 * Y * a))
    | 2, 3 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 2, 4 => a
    | 2, 5 => b
    | 3, 2 => ((-20) + ((-2) * T * a))
    | 3, 3 => (((-3) * T * b) + (3 * Y * a))
    | 3, 5 => a
    | 4, 2 => (5 * Y)
    | 4, 3 => ((-20) + ((-2) * T * a))
    | 4, 4 => 1
    | 5, 3 => (5 * Y)
    | 5, 5 => 1
    | _, _ => 0
def value263 (a b c d Y T : ℂ) : ℂ := ((112000 * a) + ((-32000) * T * c) + ((-2500) * d * (Y^3)) + ((-1400) * (Y^2) * (a^2)) + ((-60) * (Y^4) * (a^3)) + (16 * (T^4) * (a^5)) + (592 * (T^3) * (a^4)) + (2000 * c * (Y^2)) + (3600 * (T^2) * (b^2)) + (8160 * (T^2) * (a^3)) + (12000 * Y * b) + (49600 * T * (a^2)) + ((-10000) * T * Y * d) + ((-9600) * a * c * (T^2)) + ((-960) * c * (T^3) * (a^2)) + ((-580) * T * (Y^2) * (a^3)) + ((-44) * (T^2) * (Y^2) * (a^4)) + ((-32) * c * (T^4) * (a^3)) + (36 * (T^4) * (a^2) * (b^2)) + (135 * Y * (T^3) * (b^3)) + (150 * T * (Y^2) * (b^2)) + (200 * a * c * (Y^4)) + (720 * a * (T^3) * (b^2)) + (1600 * a * b * (Y^3)) + ((-2000) * Y * a * d * (T^2)) + ((-100) * Y * d * (T^3) * (a^2)) + (30 * T * b * (Y^3) * (a^2)) + (45 * a * (T^2) * (Y^2) * (b^2)) + (124 * Y * b * (T^3) * (a^3)) + (220 * c * (T^2) * (Y^2) * (a^2)) + (300 * T * b * c * (Y^3)) + (375 * b * d * (T^2) * (Y^2)) + (2400 * T * a * c * (Y^2)) + (2600 * Y * b * (T^2) * (a^2)) + (14800 * T * Y * a * b))

theorem determinant263 (a b c d Y T : ℂ) :
    (minor263 a b c d Y T).det = value263 a b c d Y T := by
  have hm0 : (minor263 a b c d Y T).submatrix Fin.succ (0 : Fin 6).succAbove =
      minor140 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor263 a b c d Y T).submatrix Fin.succ (1 : Fin 6).succAbove =
      minor218 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor263 a b c d Y T).submatrix Fin.succ (2 : Fin 6).succAbove =
      minor256 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm4 : (minor263 a b c d Y T).submatrix Fin.succ (4 : Fin 6).succAbove =
      minor260 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm5 : (minor263 a b c d Y T).submatrix Fin.succ (5 : Fin 6).succAbove =
      minor262 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * ((-20) + ((-2) * T * a)) * ((minor263 a b c d Y T).submatrix Fin.succ (0 : Fin 6).succAbove).det + ((-1 : ℂ)^1 * (((-3) * T * b) + (3 * Y * a)) * ((minor263 a b c d Y T).submatrix Fin.succ (1 : Fin 6).succAbove).det + ((-1 : ℂ)^2 * (((-2) * b) + (Y * c) + ((-5) * T * d)) * ((minor263 a b c d Y T).submatrix Fin.succ (2 : Fin 6).succAbove).det + ((-1 : ℂ)^3 * 0 * ((minor263 a b c d Y T).submatrix Fin.succ (3 : Fin 6).succAbove).det + ((-1 : ℂ)^4 * c * ((minor263 a b c d Y T).submatrix Fin.succ (4 : Fin 6).succAbove).det + ((-1 : ℂ)^5 * d * ((minor263 a b c d Y T).submatrix Fin.succ (5 : Fin 6).succAbove).det + (0)))))) = value263 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant140, hm1, determinant218, hm2, determinant256, hm4, determinant260, hm5, determinant262]
  dsimp only [value263, value140, value218, value256, value260, value262] <;> ring

def minor264 (a b c d Y T : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 2 => (5 * Y)
    | _, _ => 0
def value264 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant264 (a b c d Y T : ℂ) :
    (minor264 a b c d Y T).det = value264 a b c d Y T := by
  have hm2 : (minor264 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove =
      minor249 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * 0 * ((minor264 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove).det + ((-1 : ℂ)^1 * 0 * ((minor264 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove).det + ((-1 : ℂ)^2 * (5 * Y) * ((minor264 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove).det + (0))) = value264 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm2, determinant249]
  dsimp only [value264, value249] <;> ring

def minor265 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 1 => (5 * Y)
    | 0, 2 => ((-20) + ((-2) * T * a))
    | 0, 3 => b
    | 1, 2 => (5 * Y)
    | 1, 3 => a
    | 3, 3 => 1
    | _, _ => 0
def value265 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant265 (a b c d Y T : ℂ) :
    (minor265 a b c d Y T).det = value265 a b c d Y T := by
  have hm1 : (minor265 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove =
      minor227 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor265 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove =
      minor250 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor265 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove =
      minor264 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * 0 * ((minor265 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * (5 * Y) * ((minor265 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * ((-20) + ((-2) * T * a)) * ((minor265 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * b * ((minor265 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value265 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm1, determinant227, hm2, determinant250, hm3, determinant264]
  dsimp only [value265, value227, value250, value264] <;> ring

def minor266 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 1 => (5 * Y)
    | 0, 2 => ((-20) + ((-2) * T * a))
    | 0, 3 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 1, 2 => (5 * Y)
    | 1, 3 => (((-3) * T * b) + (3 * Y * a))
    | 2, 3 => ((-20) + ((-2) * T * a))
    | 3, 3 => (5 * Y)
    | _, _ => 0
def value266 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant266 (a b c d Y T : ℂ) :
    (minor266 a b c d Y T).det = value266 a b c d Y T := by
  have hm1 : (minor266 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove =
      minor230 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor266 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove =
      minor253 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor266 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove =
      minor264 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * 0 * ((minor266 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * (5 * Y) * ((minor266 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * ((-20) + ((-2) * T * a)) * ((minor266 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor266 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value266 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm1, determinant230, hm2, determinant253, hm3, determinant264]
  dsimp only [value266, value230, value253, value264] <;> ring

def minor267 (a b c d Y T : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (5 * Y)
    | 0, 1 => ((-20) + ((-2) * T * a))
    | 0, 2 => (((-3) * T * b) + (3 * Y * a))
    | 0, 3 => (((-2) * b) + (Y * c) + ((-5) * T * d))
    | 0, 4 => c
    | 1, 1 => (5 * Y)
    | 1, 2 => ((-20) + ((-2) * T * a))
    | 1, 3 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 1, 4 => b
    | 2, 2 => (5 * Y)
    | 2, 3 => (((-3) * T * b) + (3 * Y * a))
    | 2, 4 => a
    | 3, 3 => ((-20) + ((-2) * T * a))
    | 4, 3 => (5 * Y)
    | 4, 4 => 1
    | _, _ => 0
def value267 (a b c d Y T : ℂ) : ℂ := (((-2500) * (Y^3)) + ((-250) * T * a * (Y^3)))

theorem determinant267 (a b c d Y T : ℂ) :
    (minor267 a b c d Y T).det = value267 a b c d Y T := by
  have hm0 : (minor267 a b c d Y T).submatrix Fin.succ (0 : Fin 5).succAbove =
      minor153 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor267 a b c d Y T).submatrix Fin.succ (1 : Fin 5).succAbove =
      minor231 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor267 a b c d Y T).submatrix Fin.succ (2 : Fin 5).succAbove =
      minor254 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor267 a b c d Y T).submatrix Fin.succ (3 : Fin 5).succAbove =
      minor265 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm4 : (minor267 a b c d Y T).submatrix Fin.succ (4 : Fin 5).succAbove =
      minor266 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (5 * Y) * ((minor267 a b c d Y T).submatrix Fin.succ (0 : Fin 5).succAbove).det + ((-1 : ℂ)^1 * ((-20) + ((-2) * T * a)) * ((minor267 a b c d Y T).submatrix Fin.succ (1 : Fin 5).succAbove).det + ((-1 : ℂ)^2 * (((-3) * T * b) + (3 * Y * a)) * ((minor267 a b c d Y T).submatrix Fin.succ (2 : Fin 5).succAbove).det + ((-1 : ℂ)^3 * (((-2) * b) + (Y * c) + ((-5) * T * d)) * ((minor267 a b c d Y T).submatrix Fin.succ (3 : Fin 5).succAbove).det + ((-1 : ℂ)^4 * c * ((minor267 a b c d Y T).submatrix Fin.succ (4 : Fin 5).succAbove).det + (0))))) = value267 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant153, hm1, determinant231, hm2, determinant254, hm3, determinant265, hm4, determinant266]
  dsimp only [value267, value153, value231, value254, value265, value266] <;> ring

def minor268 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 1 => (5 * Y)
    | 0, 2 => ((-20) + ((-2) * T * a))
    | 0, 3 => (((-3) * T * b) + (3 * Y * a))
    | 1, 2 => (5 * Y)
    | 1, 3 => ((-20) + ((-2) * T * a))
    | 2, 3 => (5 * Y)
    | _, _ => 0
def value268 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant268 (a b c d Y T : ℂ) :
    (minor268 a b c d Y T).det = value268 a b c d Y T := by
  have hm1 : (minor268 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove =
      minor234 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor268 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove =
      minor257 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor268 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove =
      minor264 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * 0 * ((minor268 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * (5 * Y) * ((minor268 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * ((-20) + ((-2) * T * a)) * ((minor268 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * (((-3) * T * b) + (3 * Y * a)) * ((minor268 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value268 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm1, determinant234, hm2, determinant257, hm3, determinant264]
  dsimp only [value268, value234, value257, value264] <;> ring

def minor269 (a b c d Y T : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (5 * Y)
    | 0, 1 => ((-20) + ((-2) * T * a))
    | 0, 2 => (((-3) * T * b) + (3 * Y * a))
    | 0, 3 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 0, 4 => (((-2) * b) + (Y * c) + ((-5) * T * d))
    | 1, 1 => (5 * Y)
    | 1, 2 => ((-20) + ((-2) * T * a))
    | 1, 3 => (((-3) * T * b) + (3 * Y * a))
    | 1, 4 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 2, 2 => (5 * Y)
    | 2, 3 => ((-20) + ((-2) * T * a))
    | 2, 4 => (((-3) * T * b) + (3 * Y * a))
    | 3, 3 => (5 * Y)
    | 3, 4 => ((-20) + ((-2) * T * a))
    | 4, 4 => (5 * Y)
    | _, _ => 0
def value269 (a b c d Y T : ℂ) : ℂ := (3125 * (Y^5))

theorem determinant269 (a b c d Y T : ℂ) :
    (minor269 a b c d Y T).det = value269 a b c d Y T := by
  have hm0 : (minor269 a b c d Y T).submatrix Fin.succ (0 : Fin 5).succAbove =
      minor158 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor269 a b c d Y T).submatrix Fin.succ (1 : Fin 5).succAbove =
      minor236 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor269 a b c d Y T).submatrix Fin.succ (2 : Fin 5).succAbove =
      minor259 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor269 a b c d Y T).submatrix Fin.succ (3 : Fin 5).succAbove =
      minor266 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm4 : (minor269 a b c d Y T).submatrix Fin.succ (4 : Fin 5).succAbove =
      minor268 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (5 * Y) * ((minor269 a b c d Y T).submatrix Fin.succ (0 : Fin 5).succAbove).det + ((-1 : ℂ)^1 * ((-20) + ((-2) * T * a)) * ((minor269 a b c d Y T).submatrix Fin.succ (1 : Fin 5).succAbove).det + ((-1 : ℂ)^2 * (((-3) * T * b) + (3 * Y * a)) * ((minor269 a b c d Y T).submatrix Fin.succ (2 : Fin 5).succAbove).det + ((-1 : ℂ)^3 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor269 a b c d Y T).submatrix Fin.succ (3 : Fin 5).succAbove).det + ((-1 : ℂ)^4 * (((-2) * b) + (Y * c) + ((-5) * T * d)) * ((minor269 a b c d Y T).submatrix Fin.succ (4 : Fin 5).succAbove).det + (0))))) = value269 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant158, hm1, determinant236, hm2, determinant259, hm3, determinant266, hm4, determinant268]
  dsimp only [value269, value158, value236, value259, value266, value268] <;> ring

end Mordell.Determinants
