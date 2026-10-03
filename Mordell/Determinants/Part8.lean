import Mordell.Determinants.Part7

set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Mordell.Determinants

def minor120 (a b c d Y T : ℂ) : Matrix (Fin 1) (Fin 1) ℂ :=
  fun i j => match i.val, j.val with
    | _, _ => 0
def value120 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant120 (a b c d Y T : ℂ) :
    (minor120 a b c d Y T).det = value120 a b c d Y T := by
  simp [Matrix.det_unique, minor120, value120]

def minor121 (a b c d Y T : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 1 => 1
    | _, _ => 0
def value121 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant121 (a b c d Y T : ℂ) :
    (minor121 a b c d Y T).det = value121 a b c d Y T := by
  have hm1 : (minor121 a b c d Y T).submatrix Fin.succ (1 : Fin 2).succAbove =
      minor120 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * 0 * ((minor121 a b c d Y T).submatrix Fin.succ (0 : Fin 2).succAbove).det + ((-1 : ℂ)^1 * 1 * ((minor121 a b c d Y T).submatrix Fin.succ (1 : Fin 2).succAbove).det + (0)) = value121 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm1, determinant120]
  dsimp only [value121, value120] <;> ring

def minor122 (a b c d Y T : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 1 => 1
    | 1, 2 => 1
    | _, _ => 0
def value122 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant122 (a b c d Y T : ℂ) :
    (minor122 a b c d Y T).det = value122 a b c d Y T := by
  have hm1 : (minor122 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove =
      minor121 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * 0 * ((minor122 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove).det + ((-1 : ℂ)^1 * 1 * ((minor122 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove).det + ((-1 : ℂ)^2 * 0 * ((minor122 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove).det + (0))) = value122 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm1, determinant121]
  dsimp only [value122, value121] <;> ring

def minor123 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (5 * Y)
    | 0, 2 => a
    | 0, 3 => b
    | 1, 1 => 1
    | 1, 3 => a
    | 2, 2 => 1
    | 3, 3 => 1
    | _, _ => 0
def value123 (a b c d Y T : ℂ) : ℂ := (5 * Y)

theorem determinant123 (a b c d Y T : ℂ) :
    (minor123 a b c d Y T).det = value123 a b c d Y T := by
  have hm0 : (minor123 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove =
      minor5 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor123 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove =
      minor119 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor123 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove =
      minor122 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (5 * Y) * ((minor123 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * 0 * ((minor123 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * a * ((minor123 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * b * ((minor123 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value123 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant5, hm2, determinant119, hm3, determinant122]
  dsimp only [value123, value5, value119, value122] <;> ring

def minor124 (a b c d Y T : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 2 => a
    | 1, 1 => 1
    | 2, 2 => 1
    | _, _ => 0
def value124 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant124 (a b c d Y T : ℂ) :
    (minor124 a b c d Y T).det = value124 a b c d Y T := by
  have hm2 : (minor124 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove =
      minor121 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * 0 * ((minor124 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove).det + ((-1 : ℂ)^1 * 0 * ((minor124 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove).det + ((-1 : ℂ)^2 * a * ((minor124 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove).det + (0))) = value124 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm2, determinant121]
  dsimp only [value124, value121] <;> ring

def minor125 (a b c d Y T : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 1 => ((-20) + ((-2) * T * a))
    | 1, 1 => (5 * Y)
    | _, _ => 0
def value125 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant125 (a b c d Y T : ℂ) :
    (minor125 a b c d Y T).det = value125 a b c d Y T := by
  have hm1 : (minor125 a b c d Y T).submatrix Fin.succ (1 : Fin 2).succAbove =
      minor120 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * 0 * ((minor125 a b c d Y T).submatrix Fin.succ (0 : Fin 2).succAbove).det + ((-1 : ℂ)^1 * ((-20) + ((-2) * T * a)) * ((minor125 a b c d Y T).submatrix Fin.succ (1 : Fin 2).succAbove).det + (0)) = value125 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm1, determinant120]
  dsimp only [value125, value120] <;> ring

def minor126 (a b c d Y T : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 1 => (((-3) * T * b) + (3 * Y * a))
    | 0, 2 => a
    | 1, 1 => ((-20) + ((-2) * T * a))
    | 2, 1 => (5 * Y)
    | 2, 2 => 1
    | _, _ => 0
def value126 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant126 (a b c d Y T : ℂ) :
    (minor126 a b c d Y T).det = value126 a b c d Y T := by
  have hm1 : (minor126 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove =
      minor117 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor126 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove =
      minor125 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * 0 * ((minor126 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove).det + ((-1 : ℂ)^1 * (((-3) * T * b) + (3 * Y * a)) * ((minor126 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove).det + ((-1 : ℂ)^2 * a * ((minor126 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove).det + (0))) = value126 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm1, determinant117, hm2, determinant125]
  dsimp only [value126, value117, value125] <;> ring

def minor127 (a b c d Y T : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 1 => (((-3) * T * b) + (3 * Y * a))
    | 1, 1 => ((-20) + ((-2) * T * a))
    | 1, 2 => 1
    | 2, 1 => (5 * Y)
    | _, _ => 0
def value127 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant127 (a b c d Y T : ℂ) :
    (minor127 a b c d Y T).det = value127 a b c d Y T := by
  have hm1 : (minor127 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove =
      minor121 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * 0 * ((minor127 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove).det + ((-1 : ℂ)^1 * (((-3) * T * b) + (3 * Y * a)) * ((minor127 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove).det + ((-1 : ℂ)^2 * 0 * ((minor127 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove).det + (0))) = value127 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm1, determinant121]
  dsimp only [value127, value121] <;> ring

def minor128 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (5 * Y)
    | 0, 1 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 0, 2 => a
    | 0, 3 => b
    | 1, 1 => (((-3) * T * b) + (3 * Y * a))
    | 1, 3 => a
    | 2, 1 => ((-20) + ((-2) * T * a))
    | 2, 2 => 1
    | 3, 1 => (5 * Y)
    | 3, 3 => 1
    | _, _ => 0
def value128 (a b c d Y T : ℂ) : ℂ := (((-10) * a * (Y^2)) + ((-15) * T * Y * b))

theorem determinant128 (a b c d Y T : ℂ) :
    (minor128 a b c d Y T).det = value128 a b c d Y T := by
  have hm0 : (minor128 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove =
      minor17 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor128 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove =
      minor124 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor128 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove =
      minor126 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor128 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove =
      minor127 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (5 * Y) * ((minor128 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor128 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * a * ((minor128 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * b * ((minor128 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value128 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant17, hm1, determinant124, hm2, determinant126, hm3, determinant127]
  dsimp only [value128, value17, value124, value126, value127] <;> ring

def minor129 (a b c d Y T : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 1 => (((-3) * T * b) + (3 * Y * a))
    | 0, 2 => 1
    | 1, 1 => ((-20) + ((-2) * T * a))
    | 2, 1 => (5 * Y)
    | _, _ => 0
def value129 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant129 (a b c d Y T : ℂ) :
    (minor129 a b c d Y T).det = value129 a b c d Y T := by
  have hm1 : (minor129 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove =
      minor118 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor129 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove =
      minor125 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * 0 * ((minor129 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove).det + ((-1 : ℂ)^1 * (((-3) * T * b) + (3 * Y * a)) * ((minor129 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove).det + ((-1 : ℂ)^2 * 1 * ((minor129 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove).det + (0))) = value129 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm1, determinant118, hm2, determinant125]
  dsimp only [value129, value118, value125] <;> ring

def minor130 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (5 * Y)
    | 0, 1 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 0, 3 => b
    | 1, 1 => (((-3) * T * b) + (3 * Y * a))
    | 1, 2 => 1
    | 1, 3 => a
    | 2, 1 => ((-20) + ((-2) * T * a))
    | 3, 1 => (5 * Y)
    | 3, 3 => 1
    | _, _ => 0
def value130 (a b c d Y T : ℂ) : ℂ := ((100 * Y) + (10 * T * Y * a))

theorem determinant130 (a b c d Y T : ℂ) :
    (minor130 a b c d Y T).det = value130 a b c d Y T := by
  have hm0 : (minor130 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove =
      minor25 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor130 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove =
      minor119 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor130 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove =
      minor129 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (5 * Y) * ((minor130 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor130 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * 0 * ((minor130 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * b * ((minor130 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value130 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant25, hm1, determinant119, hm3, determinant129]
  dsimp only [value130, value25, value119, value129] <;> ring

def minor131 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (5 * Y)
    | 0, 1 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 0, 3 => a
    | 1, 1 => (((-3) * T * b) + (3 * Y * a))
    | 1, 2 => 1
    | 2, 1 => ((-20) + ((-2) * T * a))
    | 2, 3 => 1
    | 3, 1 => (5 * Y)
    | _, _ => 0
def value131 (a b c d Y T : ℂ) : ℂ := (25 * (Y^2))

theorem determinant131 (a b c d Y T : ℂ) :
    (minor131 a b c d Y T).det = value131 a b c d Y T := by
  have hm0 : (minor131 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove =
      minor28 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor131 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove =
      minor122 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor131 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove =
      minor129 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (5 * Y) * ((minor131 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor131 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * 0 * ((minor131 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * a * ((minor131 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value131 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant28, hm1, determinant122, hm3, determinant129]
  dsimp only [value131, value28, value122, value129] <;> ring

def minor132 (a b c d Y T : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => ((-20) + ((-2) * T * a))
    | 0, 1 => (((-2) * b) + (Y * c) + ((-5) * T * d))
    | 0, 2 => a
    | 0, 3 => b
    | 0, 4 => c
    | 1, 0 => (5 * Y)
    | 1, 1 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 1, 3 => a
    | 1, 4 => b
    | 2, 1 => (((-3) * T * b) + (3 * Y * a))
    | 2, 2 => 1
    | 2, 4 => a
    | 3, 1 => ((-20) + ((-2) * T * a))
    | 3, 3 => 1
    | 4, 1 => (5 * Y)
    | 4, 4 => 1
    | _, _ => 0
def value132 (a b c d Y T : ℂ) : ℂ := (((-280) * a) + ((-68) * T * (a^2)) + ((-30) * Y * b) + ((-10) * (Y^2) * (a^2)) + ((-4) * (T^2) * (a^3)) + (20 * c * (Y^2)) + (80 * T * c) + (8 * a * c * (T^2)) + (25 * T * Y * d) + ((-19) * T * Y * a * b))

theorem determinant132 (a b c d Y T : ℂ) :
    (minor132 a b c d Y T).det = value132 a b c d Y T := by
  have hm0 : (minor132 a b c d Y T).submatrix Fin.succ (0 : Fin 5).succAbove =
      minor31 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor132 a b c d Y T).submatrix Fin.succ (1 : Fin 5).succAbove =
      minor123 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor132 a b c d Y T).submatrix Fin.succ (2 : Fin 5).succAbove =
      minor128 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor132 a b c d Y T).submatrix Fin.succ (3 : Fin 5).succAbove =
      minor130 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm4 : (minor132 a b c d Y T).submatrix Fin.succ (4 : Fin 5).succAbove =
      minor131 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * ((-20) + ((-2) * T * a)) * ((minor132 a b c d Y T).submatrix Fin.succ (0 : Fin 5).succAbove).det + ((-1 : ℂ)^1 * (((-2) * b) + (Y * c) + ((-5) * T * d)) * ((minor132 a b c d Y T).submatrix Fin.succ (1 : Fin 5).succAbove).det + ((-1 : ℂ)^2 * a * ((minor132 a b c d Y T).submatrix Fin.succ (2 : Fin 5).succAbove).det + ((-1 : ℂ)^3 * b * ((minor132 a b c d Y T).submatrix Fin.succ (3 : Fin 5).succAbove).det + ((-1 : ℂ)^4 * c * ((minor132 a b c d Y T).submatrix Fin.succ (4 : Fin 5).succAbove).det + (0))))) = value132 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant31, hm1, determinant123, hm2, determinant128, hm3, determinant130, hm4, determinant131]
  dsimp only [value132, value31, value123, value128, value130, value131] <;> ring

def minor133 (a b c d Y T : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 1 => (5 * Y)
    | _, _ => 0
def value133 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant133 (a b c d Y T : ℂ) :
    (minor133 a b c d Y T).det = value133 a b c d Y T := by
  have hm1 : (minor133 a b c d Y T).submatrix Fin.succ (1 : Fin 2).succAbove =
      minor120 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * 0 * ((minor133 a b c d Y T).submatrix Fin.succ (0 : Fin 2).succAbove).det + ((-1 : ℂ)^1 * (5 * Y) * ((minor133 a b c d Y T).submatrix Fin.succ (1 : Fin 2).succAbove).det + (0)) = value133 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm1, determinant120]
  dsimp only [value133, value120] <;> ring

def minor134 (a b c d Y T : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 1 => ((-20) + ((-2) * T * a))
    | 0, 2 => a
    | 1, 1 => (5 * Y)
    | 2, 2 => 1
    | _, _ => 0
def value134 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant134 (a b c d Y T : ℂ) :
    (minor134 a b c d Y T).det = value134 a b c d Y T := by
  have hm1 : (minor134 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove =
      minor117 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor134 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove =
      minor133 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * 0 * ((minor134 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove).det + ((-1 : ℂ)^1 * ((-20) + ((-2) * T * a)) * ((minor134 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove).det + ((-1 : ℂ)^2 * a * ((minor134 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove).det + (0))) = value134 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm1, determinant117, hm2, determinant133]
  dsimp only [value134, value117, value133] <;> ring

end Mordell.Determinants
