import Mordell.Determinants.Part0

set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Mordell.Determinants

def minor15 (a b c d Y T : ℂ) : Matrix (Fin 1) (Fin 1) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (5 * Y)
    | _, _ => 0
def value15 (a b c d Y T : ℂ) : ℂ := (5 * Y)

theorem determinant15 (a b c d Y T : ℂ) :
    (minor15 a b c d Y T).det = value15 a b c d Y T := by
  simp [Matrix.det_unique, minor15, value15]

def minor16 (a b c d Y T : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => ((-20) + ((-2) * T * a))
    | 0, 1 => 1
    | 1, 0 => (5 * Y)
    | _, _ => 0
def value16 (a b c d Y T : ℂ) : ℂ := ((-5) * Y)

theorem determinant16 (a b c d Y T : ℂ) :
    (minor16 a b c d Y T).det = value16 a b c d Y T := by
  have hm0 : (minor16 a b c d Y T).submatrix Fin.succ (0 : Fin 2).succAbove =
      minor14 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor16 a b c d Y T).submatrix Fin.succ (1 : Fin 2).succAbove =
      minor15 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * ((-20) + ((-2) * T * a)) * ((minor16 a b c d Y T).submatrix Fin.succ (0 : Fin 2).succAbove).det + ((-1 : ℂ)^1 * 1 * ((minor16 a b c d Y T).submatrix Fin.succ (1 : Fin 2).succAbove).det + (0)) = value16 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant14, hm1, determinant15]
  dsimp only [value16, value14, value15] <;> ring

def minor17 (a b c d Y T : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (((-3) * T * b) + (3 * Y * a))
    | 0, 2 => a
    | 1, 0 => ((-20) + ((-2) * T * a))
    | 1, 1 => 1
    | 2, 0 => (5 * Y)
    | 2, 2 => 1
    | _, _ => 0
def value17 (a b c d Y T : ℂ) : ℂ := (((-3) * T * b) + ((-2) * Y * a))

theorem determinant17 (a b c d Y T : ℂ) :
    (minor17 a b c d Y T).det = value17 a b c d Y T := by
  have hm0 : (minor17 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove =
      minor2 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor17 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove =
      minor16 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (((-3) * T * b) + (3 * Y * a)) * ((minor17 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove).det + ((-1 : ℂ)^1 * 0 * ((minor17 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove).det + ((-1 : ℂ)^2 * a * ((minor17 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove).det + (0))) = value17 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant2, hm2, determinant16]
  dsimp only [value17, value2, value16] <;> ring

def minor18 (a b c d Y T : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => ((-20) + ((-2) * T * a))
    | 1, 0 => (5 * Y)
    | _, _ => 0
def value18 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant18 (a b c d Y T : ℂ) :
    (minor18 a b c d Y T).det = value18 a b c d Y T := by
  have hm0 : (minor18 a b c d Y T).submatrix Fin.succ (0 : Fin 2).succAbove =
      minor9 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * ((-20) + ((-2) * T * a)) * ((minor18 a b c d Y T).submatrix Fin.succ (0 : Fin 2).succAbove).det + ((-1 : ℂ)^1 * 0 * ((minor18 a b c d Y T).submatrix Fin.succ (1 : Fin 2).succAbove).det + (0)) = value18 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant9]
  dsimp only [value18, value9] <;> ring

def minor19 (a b c d Y T : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (((-3) * T * b) + (3 * Y * a))
    | 0, 2 => a
    | 1, 0 => ((-20) + ((-2) * T * a))
    | 2, 0 => (5 * Y)
    | 2, 2 => 1
    | _, _ => 0
def value19 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant19 (a b c d Y T : ℂ) :
    (minor19 a b c d Y T).det = value19 a b c d Y T := by
  have hm0 : (minor19 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove =
      minor6 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor19 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove =
      minor18 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (((-3) * T * b) + (3 * Y * a)) * ((minor19 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove).det + ((-1 : ℂ)^1 * 0 * ((minor19 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove).det + ((-1 : ℂ)^2 * a * ((minor19 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove).det + (0))) = value19 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant6, hm2, determinant18]
  dsimp only [value19, value6, value18] <;> ring

def minor20 (a b c d Y T : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (((-3) * T * b) + (3 * Y * a))
    | 1, 0 => ((-20) + ((-2) * T * a))
    | 1, 2 => 1
    | 2, 0 => (5 * Y)
    | _, _ => 0
def value20 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant20 (a b c d Y T : ℂ) :
    (minor20 a b c d Y T).det = value20 a b c d Y T := by
  have hm0 : (minor20 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove =
      minor10 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (((-3) * T * b) + (3 * Y * a)) * ((minor20 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove).det + ((-1 : ℂ)^1 * 0 * ((minor20 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove).det + ((-1 : ℂ)^2 * 0 * ((minor20 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove).det + (0))) = value20 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant10]
  dsimp only [value20, value10] <;> ring

def minor21 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 0, 1 => 1
    | 0, 2 => a
    | 0, 3 => b
    | 1, 0 => (((-3) * T * b) + (3 * Y * a))
    | 1, 3 => a
    | 2, 0 => ((-20) + ((-2) * T * a))
    | 2, 2 => 1
    | 3, 0 => (5 * Y)
    | 3, 3 => 1
    | _, _ => 0
def value21 (a b c d Y T : ℂ) : ℂ := ((2 * Y * a) + (3 * T * b))

theorem determinant21 (a b c d Y T : ℂ) :
    (minor21 a b c d Y T).det = value21 a b c d Y T := by
  have hm0 : (minor21 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove =
      minor13 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor21 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove =
      minor17 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor21 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove =
      minor19 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor21 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove =
      minor20 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor21 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * 1 * ((minor21 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * a * ((minor21 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * b * ((minor21 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value21 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant13, hm1, determinant17, hm2, determinant19, hm3, determinant20]
  dsimp only [value21, value13, value17, value19, value20] <;> ring

def minor22 (a b c d Y T : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => match i.val, j.val with
    | 1, 1 => 1
    | _, _ => 0
def value22 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant22 (a b c d Y T : ℂ) :
    (minor22 a b c d Y T).det = value22 a b c d Y T := by
  rw [show value22 a b c d Y T = 0 by rfl]
  apply Matrix.det_eq_zero_of_row_eq_zero 0
  intro j
  fin_cases j <;> rfl

def minor23 (a b c d Y T : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => ((-20) + ((-2) * T * a))
    | 1, 0 => (5 * Y)
    | 1, 1 => 1
    | _, _ => 0
def value23 (a b c d Y T : ℂ) : ℂ := ((-20) + ((-2) * T * a))

theorem determinant23 (a b c d Y T : ℂ) :
    (minor23 a b c d Y T).det = value23 a b c d Y T := by
  have hm0 : (minor23 a b c d Y T).submatrix Fin.succ (0 : Fin 2).succAbove =
      minor1 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * ((-20) + ((-2) * T * a)) * ((minor23 a b c d Y T).submatrix Fin.succ (0 : Fin 2).succAbove).det + ((-1 : ℂ)^1 * 0 * ((minor23 a b c d Y T).submatrix Fin.succ (1 : Fin 2).succAbove).det + (0)) = value23 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant1]
  dsimp only [value23, value1] <;> ring

def minor24 (a b c d Y T : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => ((-20) + ((-2) * T * a))
    | 1, 0 => (5 * Y)
    | _, _ => 0
def value24 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant24 (a b c d Y T : ℂ) :
    (minor24 a b c d Y T).det = value24 a b c d Y T := by
  have hm0 : (minor24 a b c d Y T).submatrix Fin.succ (0 : Fin 2).succAbove =
      minor3 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * ((-20) + ((-2) * T * a)) * ((minor24 a b c d Y T).submatrix Fin.succ (0 : Fin 2).succAbove).det + ((-1 : ℂ)^1 * 0 * ((minor24 a b c d Y T).submatrix Fin.succ (1 : Fin 2).succAbove).det + (0)) = value24 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant3]
  dsimp only [value24, value3] <;> ring

def minor25 (a b c d Y T : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (((-3) * T * b) + (3 * Y * a))
    | 0, 1 => 1
    | 0, 2 => a
    | 1, 0 => ((-20) + ((-2) * T * a))
    | 2, 0 => (5 * Y)
    | 2, 2 => 1
    | _, _ => 0
def value25 (a b c d Y T : ℂ) : ℂ := (20 + (2 * T * a))

theorem determinant25 (a b c d Y T : ℂ) :
    (minor25 a b c d Y T).det = value25 a b c d Y T := by
  have hm0 : (minor25 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove =
      minor22 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor25 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove =
      minor23 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor25 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove =
      minor24 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (((-3) * T * b) + (3 * Y * a)) * ((minor25 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove).det + ((-1 : ℂ)^1 * 1 * ((minor25 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove).det + ((-1 : ℂ)^2 * a * ((minor25 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove).det + (0))) = value25 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant22, hm1, determinant23, hm2, determinant24]
  dsimp only [value25, value22, value23, value24] <;> ring

def minor26 (a b c d Y T : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (((-3) * T * b) + (3 * Y * a))
    | 0, 2 => 1
    | 1, 0 => ((-20) + ((-2) * T * a))
    | 2, 0 => (5 * Y)
    | _, _ => 0
def value26 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant26 (a b c d Y T : ℂ) :
    (minor26 a b c d Y T).det = value26 a b c d Y T := by
  have hm0 : (minor26 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove =
      minor7 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor26 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove =
      minor18 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (((-3) * T * b) + (3 * Y * a)) * ((minor26 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove).det + ((-1 : ℂ)^1 * 0 * ((minor26 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove).det + ((-1 : ℂ)^2 * 1 * ((minor26 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove).det + (0))) = value26 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant7, hm2, determinant18]
  dsimp only [value26, value7, value18] <;> ring

def minor27 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 0, 1 => 1
    | 0, 3 => b
    | 1, 0 => (((-3) * T * b) + (3 * Y * a))
    | 1, 2 => 1
    | 1, 3 => a
    | 2, 0 => ((-20) + ((-2) * T * a))
    | 3, 0 => (5 * Y)
    | 3, 3 => 1
    | _, _ => 0
def value27 (a b c d Y T : ℂ) : ℂ := ((-20) + ((-2) * T * a))

theorem determinant27 (a b c d Y T : ℂ) :
    (minor27 a b c d Y T).det = value27 a b c d Y T := by
  have hm0 : (minor27 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove =
      minor8 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor27 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove =
      minor25 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor27 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove =
      minor26 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor27 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * 1 * ((minor27 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * 0 * ((minor27 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * b * ((minor27 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value27 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant8, hm1, determinant25, hm3, determinant26]
  dsimp only [value27, value8, value25, value26] <;> ring

def minor28 (a b c d Y T : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (((-3) * T * b) + (3 * Y * a))
    | 0, 1 => 1
    | 1, 0 => ((-20) + ((-2) * T * a))
    | 1, 2 => 1
    | 2, 0 => (5 * Y)
    | _, _ => 0
def value28 (a b c d Y T : ℂ) : ℂ := (5 * Y)

theorem determinant28 (a b c d Y T : ℂ) :
    (minor28 a b c d Y T).det = value28 a b c d Y T := by
  have hm0 : (minor28 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove =
      minor4 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor28 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove =
      minor16 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (((-3) * T * b) + (3 * Y * a)) * ((minor28 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove).det + ((-1 : ℂ)^1 * 1 * ((minor28 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove).det + ((-1 : ℂ)^2 * 0 * ((minor28 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove).det + (0))) = value28 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant4, hm1, determinant16]
  dsimp only [value28, value4, value16] <;> ring

def minor29 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 0, 1 => 1
    | 0, 3 => a
    | 1, 0 => (((-3) * T * b) + (3 * Y * a))
    | 1, 2 => 1
    | 2, 0 => ((-20) + ((-2) * T * a))
    | 2, 3 => 1
    | 3, 0 => (5 * Y)
    | _, _ => 0
def value29 (a b c d Y T : ℂ) : ℂ := ((-5) * Y)

theorem determinant29 (a b c d Y T : ℂ) :
    (minor29 a b c d Y T).det = value29 a b c d Y T := by
  have hm0 : (minor29 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove =
      minor11 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor29 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove =
      minor28 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor29 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove =
      minor26 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor29 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * 1 * ((minor29 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * 0 * ((minor29 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * a * ((minor29 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value29 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant11, hm1, determinant28, hm3, determinant26]
  dsimp only [value29, value11, value28, value26] <;> ring

end Mordell.Determinants
