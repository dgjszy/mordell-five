import Mordell.Quintic

set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Mordell.Determinants

def minor0 (a b c d Y T : ℂ) : Matrix (Fin 0) (Fin 0) ℂ :=
  fun i j => match i.val, j.val with
    | _, _ => 0
def value0 (a b c d Y T : ℂ) : ℂ := 1

theorem determinant0 (a b c d Y T : ℂ) :
    (minor0 a b c d Y T).det = value0 a b c d Y T := by
  simp [value0]

def minor1 (a b c d Y T : ℂ) : Matrix (Fin 1) (Fin 1) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => 1
    | _, _ => 0
def value1 (a b c d Y T : ℂ) : ℂ := 1

theorem determinant1 (a b c d Y T : ℂ) :
    (minor1 a b c d Y T).det = value1 a b c d Y T := by
  simp [Matrix.det_unique, minor1, value1]

def minor2 (a b c d Y T : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => 1
    | 1, 1 => 1
    | _, _ => 0
def value2 (a b c d Y T : ℂ) : ℂ := 1

theorem determinant2 (a b c d Y T : ℂ) :
    (minor2 a b c d Y T).det = value2 a b c d Y T := by
  have hm0 : (minor2 a b c d Y T).submatrix Fin.succ (0 : Fin 2).succAbove =
      minor1 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * 1 * ((minor2 a b c d Y T).submatrix Fin.succ (0 : Fin 2).succAbove).det + ((-1 : ℂ)^1 * 0 * ((minor2 a b c d Y T).submatrix Fin.succ (1 : Fin 2).succAbove).det + (0)) = value2 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant1]
  dsimp only [value2, value1] <;> ring

def minor3 (a b c d Y T : ℂ) : Matrix (Fin 1) (Fin 1) ℂ :=
  fun i j => match i.val, j.val with
    | _, _ => 0
def value3 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant3 (a b c d Y T : ℂ) :
    (minor3 a b c d Y T).det = value3 a b c d Y T := by
  simp [Matrix.det_unique, minor3, value3]

def minor4 (a b c d Y T : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 1 => 1
    | _, _ => 0
def value4 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant4 (a b c d Y T : ℂ) :
    (minor4 a b c d Y T).det = value4 a b c d Y T := by
  have hm1 : (minor4 a b c d Y T).submatrix Fin.succ (1 : Fin 2).succAbove =
      minor3 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * 0 * ((minor4 a b c d Y T).submatrix Fin.succ (0 : Fin 2).succAbove).det + ((-1 : ℂ)^1 * 1 * ((minor4 a b c d Y T).submatrix Fin.succ (1 : Fin 2).succAbove).det + (0)) = value4 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm1, determinant3]
  dsimp only [value4, value3] <;> ring

def minor5 (a b c d Y T : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => 1
    | 0, 2 => a
    | 1, 1 => 1
    | 2, 2 => 1
    | _, _ => 0
def value5 (a b c d Y T : ℂ) : ℂ := 1

theorem determinant5 (a b c d Y T : ℂ) :
    (minor5 a b c d Y T).det = value5 a b c d Y T := by
  have hm0 : (minor5 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove =
      minor2 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor5 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove =
      minor4 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * 1 * ((minor5 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove).det + ((-1 : ℂ)^1 * 0 * ((minor5 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove).det + ((-1 : ℂ)^2 * a * ((minor5 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove).det + (0))) = value5 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant2, hm2, determinant4]
  dsimp only [value5, value2, value4] <;> ring

def minor6 (a b c d Y T : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => match i.val, j.val with
    | 1, 1 => 1
    | _, _ => 0
def value6 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant6 (a b c d Y T : ℂ) :
    (minor6 a b c d Y T).det = value6 a b c d Y T := by
  rw [show value6 a b c d Y T = 0 by rfl]
  apply Matrix.det_eq_zero_of_row_eq_zero 0
  intro j
  fin_cases j <;> rfl

def minor7 (a b c d Y T : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => match i.val, j.val with
    | _, _ => 0
def value7 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant7 (a b c d Y T : ℂ) :
    (minor7 a b c d Y T).det = value7 a b c d Y T := by
  rw [show value7 a b c d Y T = 0 by rfl]
  apply Matrix.det_eq_zero_of_row_eq_zero 0
  intro j
  fin_cases j <;> rfl

def minor8 (a b c d Y T : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 1 => 1
    | 0, 2 => a
    | 2, 2 => 1
    | _, _ => 0
def value8 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant8 (a b c d Y T : ℂ) :
    (minor8 a b c d Y T).det = value8 a b c d Y T := by
  have hm1 : (minor8 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove =
      minor6 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor8 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove =
      minor7 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * 0 * ((minor8 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove).det + ((-1 : ℂ)^1 * 1 * ((minor8 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove).det + ((-1 : ℂ)^2 * a * ((minor8 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove).det + (0))) = value8 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm1, determinant6, hm2, determinant7]
  dsimp only [value8, value6, value7] <;> ring

def minor9 (a b c d Y T : ℂ) : Matrix (Fin 1) (Fin 1) ℂ :=
  fun i j => match i.val, j.val with
    | _, _ => 0
def value9 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant9 (a b c d Y T : ℂ) :
    (minor9 a b c d Y T).det = value9 a b c d Y T := by
  simp [Matrix.det_unique, minor9, value9]

def minor10 (a b c d Y T : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 1 => 1
    | _, _ => 0
def value10 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant10 (a b c d Y T : ℂ) :
    (minor10 a b c d Y T).det = value10 a b c d Y T := by
  have hm1 : (minor10 a b c d Y T).submatrix Fin.succ (1 : Fin 2).succAbove =
      minor9 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * 0 * ((minor10 a b c d Y T).submatrix Fin.succ (0 : Fin 2).succAbove).det + ((-1 : ℂ)^1 * 1 * ((minor10 a b c d Y T).submatrix Fin.succ (1 : Fin 2).succAbove).det + (0)) = value10 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm1, determinant9]
  dsimp only [value10, value9] <;> ring

def minor11 (a b c d Y T : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 1 => 1
    | 1, 2 => 1
    | _, _ => 0
def value11 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant11 (a b c d Y T : ℂ) :
    (minor11 a b c d Y T).det = value11 a b c d Y T := by
  have hm1 : (minor11 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove =
      minor10 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * 0 * ((minor11 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove).det + ((-1 : ℂ)^1 * 1 * ((minor11 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove).det + ((-1 : ℂ)^2 * 0 * ((minor11 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove).det + (0))) = value11 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm1, determinant10]
  dsimp only [value11, value10] <;> ring

def minor12 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => 1
    | 0, 2 => a
    | 0, 3 => b
    | 1, 1 => 1
    | 1, 3 => a
    | 2, 2 => 1
    | 3, 3 => 1
    | _, _ => 0
def value12 (a b c d Y T : ℂ) : ℂ := 1

theorem determinant12 (a b c d Y T : ℂ) :
    (minor12 a b c d Y T).det = value12 a b c d Y T := by
  have hm0 : (minor12 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove =
      minor5 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor12 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove =
      minor8 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor12 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove =
      minor11 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * 1 * ((minor12 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * 0 * ((minor12 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * a * ((minor12 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * b * ((minor12 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value12 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant5, hm2, determinant8, hm3, determinant11]
  dsimp only [value12, value5, value8, value11] <;> ring

def minor13 (a b c d Y T : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 2 => a
    | 1, 1 => 1
    | 2, 2 => 1
    | _, _ => 0
def value13 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant13 (a b c d Y T : ℂ) :
    (minor13 a b c d Y T).det = value13 a b c d Y T := by
  have hm2 : (minor13 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove =
      minor10 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * 0 * ((minor13 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove).det + ((-1 : ℂ)^1 * 0 * ((minor13 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove).det + ((-1 : ℂ)^2 * a * ((minor13 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove).det + (0))) = value13 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm2, determinant10]
  dsimp only [value13, value10] <;> ring

def minor14 (a b c d Y T : ℂ) : Matrix (Fin 1) (Fin 1) ℂ :=
  fun i j => match i.val, j.val with
    | _, _ => 0
def value14 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant14 (a b c d Y T : ℂ) :
    (minor14 a b c d Y T).det = value14 a b c d Y T := by
  simp [Matrix.det_unique, minor14, value14]

end Mordell.Determinants
