import Mordell.Determinants.Part4

set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Mordell.Determinants

def minor75 (a b c d Y T : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (5 * Y)
    | 0, 1 => (((-3) * T * b) + (3 * Y * a))
    | 0, 2 => 1
    | 1, 1 => ((-20) + ((-2) * T * a))
    | 2, 1 => (5 * Y)
    | _, _ => 0
def value75 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant75 (a b c d Y T : ℂ) :
    (minor75 a b c d Y T).det = value75 a b c d Y T := by
  have hm0 : (minor75 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove =
      minor24 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor75 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove =
      minor64 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor75 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove =
      minor71 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (5 * Y) * ((minor75 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove).det + ((-1 : ℂ)^1 * (((-3) * T * b) + (3 * Y * a)) * ((minor75 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove).det + ((-1 : ℂ)^2 * 1 * ((minor75 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove).det + (0))) = value75 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant24, hm1, determinant64, hm2, determinant71]
  dsimp only [value75, value24, value64, value71] <;> ring

def minor76 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => ((-20) + ((-2) * T * a))
    | 0, 1 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 0, 3 => b
    | 1, 0 => (5 * Y)
    | 1, 1 => (((-3) * T * b) + (3 * Y * a))
    | 1, 2 => 1
    | 1, 3 => a
    | 2, 1 => ((-20) + ((-2) * T * a))
    | 3, 1 => (5 * Y)
    | 3, 3 => 1
    | _, _ => 0
def value76 (a b c d Y T : ℂ) : ℂ := ((-400) + ((-80) * T * a) + ((-4) * (T^2) * (a^2)))

theorem determinant76 (a b c d Y T : ℂ) :
    (minor76 a b c d Y T).det = value76 a b c d Y T := by
  have hm0 : (minor76 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove =
      minor25 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor76 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove =
      minor65 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor76 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove =
      minor75 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * ((-20) + ((-2) * T * a)) * ((minor76 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor76 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * 0 * ((minor76 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * b * ((minor76 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value76 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant25, hm1, determinant65, hm3, determinant75]
  dsimp only [value76, value25, value65, value75] <;> ring

def minor77 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => ((-20) + ((-2) * T * a))
    | 0, 1 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 0, 3 => a
    | 1, 0 => (5 * Y)
    | 1, 1 => (((-3) * T * b) + (3 * Y * a))
    | 1, 2 => 1
    | 2, 1 => ((-20) + ((-2) * T * a))
    | 2, 3 => 1
    | 3, 1 => (5 * Y)
    | _, _ => 0
def value77 (a b c d Y T : ℂ) : ℂ := (((-100) * Y) + ((-10) * T * Y * a))

theorem determinant77 (a b c d Y T : ℂ) :
    (minor77 a b c d Y T).det = value77 a b c d Y T := by
  have hm0 : (minor77 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove =
      minor28 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor77 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove =
      minor68 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor77 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove =
      minor75 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * ((-20) + ((-2) * T * a)) * ((minor77 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor77 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * 0 * ((minor77 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * a * ((minor77 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value77 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant28, hm1, determinant68, hm3, determinant75]
  dsimp only [value77, value28, value68, value75] <;> ring

def minor78 (a b c d Y T : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (((-3) * T * b) + (3 * Y * a))
    | 0, 1 => (((-2) * b) + (Y * c) + ((-5) * T * d))
    | 0, 2 => a
    | 0, 3 => b
    | 0, 4 => c
    | 1, 0 => ((-20) + ((-2) * T * a))
    | 1, 1 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 1, 3 => a
    | 1, 4 => b
    | 2, 0 => (5 * Y)
    | 2, 1 => (((-3) * T * b) + (3 * Y * a))
    | 2, 2 => 1
    | 2, 4 => a
    | 3, 1 => ((-20) + ((-2) * T * a))
    | 3, 3 => 1
    | 4, 1 => (5 * Y)
    | 4, 4 => 1
    | _, _ => 0
def value78 (a b c d Y T : ℂ) : ℂ := ((360 * b) + ((-100) * T * d) + ((-80) * Y * c) + (12 * Y * (a^2)) + ((-10) * a * d * (T^2)) + (4 * b * (T^2) * (a^2)) + (6 * a * b * (Y^2)) + (9 * T * Y * (b^2)) + (12 * b * c * (T^2)) + (94 * T * a * b))

theorem determinant78 (a b c d Y T : ℂ) :
    (minor78 a b c d Y T).det = value78 a b c d Y T := by
  have hm0 : (minor78 a b c d Y T).submatrix Fin.succ (0 : Fin 5).succAbove =
      minor31 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor78 a b c d Y T).submatrix Fin.succ (1 : Fin 5).succAbove =
      minor69 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor78 a b c d Y T).submatrix Fin.succ (2 : Fin 5).succAbove =
      minor74 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor78 a b c d Y T).submatrix Fin.succ (3 : Fin 5).succAbove =
      minor76 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm4 : (minor78 a b c d Y T).submatrix Fin.succ (4 : Fin 5).succAbove =
      minor77 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (((-3) * T * b) + (3 * Y * a)) * ((minor78 a b c d Y T).submatrix Fin.succ (0 : Fin 5).succAbove).det + ((-1 : ℂ)^1 * (((-2) * b) + (Y * c) + ((-5) * T * d)) * ((minor78 a b c d Y T).submatrix Fin.succ (1 : Fin 5).succAbove).det + ((-1 : ℂ)^2 * a * ((minor78 a b c d Y T).submatrix Fin.succ (2 : Fin 5).succAbove).det + ((-1 : ℂ)^3 * b * ((minor78 a b c d Y T).submatrix Fin.succ (3 : Fin 5).succAbove).det + ((-1 : ℂ)^4 * c * ((minor78 a b c d Y T).submatrix Fin.succ (4 : Fin 5).succAbove).det + (0))))) = value78 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant31, hm1, determinant69, hm2, determinant74, hm3, determinant76, hm4, determinant77]
  dsimp only [value78, value31, value69, value74, value76, value77] <;> ring

def minor79 (a b c d Y T : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 1 => (5 * Y)
    | _, _ => 0
def value79 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant79 (a b c d Y T : ℂ) :
    (minor79 a b c d Y T).det = value79 a b c d Y T := by
  have hm1 : (minor79 a b c d Y T).submatrix Fin.succ (1 : Fin 2).succAbove =
      minor66 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * 0 * ((minor79 a b c d Y T).submatrix Fin.succ (0 : Fin 2).succAbove).det + ((-1 : ℂ)^1 * (5 * Y) * ((minor79 a b c d Y T).submatrix Fin.succ (1 : Fin 2).succAbove).det + (0)) = value79 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm1, determinant66]
  dsimp only [value79, value66] <;> ring

def minor80 (a b c d Y T : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (5 * Y)
    | 0, 1 => ((-20) + ((-2) * T * a))
    | 0, 2 => a
    | 1, 1 => (5 * Y)
    | 2, 2 => 1
    | _, _ => 0
def value80 (a b c d Y T : ℂ) : ℂ := (25 * (Y^2))

theorem determinant80 (a b c d Y T : ℂ) :
    (minor80 a b c d Y T).det = value80 a b c d Y T := by
  have hm0 : (minor80 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove =
      minor32 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor80 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove =
      minor63 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor80 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove =
      minor79 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (5 * Y) * ((minor80 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove).det + ((-1 : ℂ)^1 * ((-20) + ((-2) * T * a)) * ((minor80 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove).det + ((-1 : ℂ)^2 * a * ((minor80 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove).det + (0))) = value80 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant32, hm1, determinant63, hm2, determinant79]
  dsimp only [value80, value32, value63, value79] <;> ring

def minor81 (a b c d Y T : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (5 * Y)
    | 0, 1 => ((-20) + ((-2) * T * a))
    | 1, 1 => (5 * Y)
    | 1, 2 => 1
    | _, _ => 0
def value81 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant81 (a b c d Y T : ℂ) :
    (minor81 a b c d Y T).det = value81 a b c d Y T := by
  have hm0 : (minor81 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove =
      minor36 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor81 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove =
      minor67 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (5 * Y) * ((minor81 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove).det + ((-1 : ℂ)^1 * ((-20) + ((-2) * T * a)) * ((minor81 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove).det + ((-1 : ℂ)^2 * 0 * ((minor81 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove).det + (0))) = value81 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant36, hm1, determinant67]
  dsimp only [value81, value36, value67] <;> ring

def minor82 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => ((-20) + ((-2) * T * a))
    | 0, 1 => (((-3) * T * b) + (3 * Y * a))
    | 0, 2 => a
    | 0, 3 => b
    | 1, 0 => (5 * Y)
    | 1, 1 => ((-20) + ((-2) * T * a))
    | 1, 3 => a
    | 2, 1 => (5 * Y)
    | 2, 2 => 1
    | 3, 3 => 1
    | _, _ => 0
def value82 (a b c d Y T : ℂ) : ℂ := (400 + (4 * (T^2) * (a^2)) + (10 * a * (Y^2)) + (80 * T * a) + (15 * T * Y * b))

theorem determinant82 (a b c d Y T : ℂ) :
    (minor82 a b c d Y T).det = value82 a b c d Y T := by
  have hm0 : (minor82 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove =
      minor39 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor82 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove =
      minor70 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor82 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove =
      minor80 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor82 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove =
      minor81 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * ((-20) + ((-2) * T * a)) * ((minor82 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * (((-3) * T * b) + (3 * Y * a)) * ((minor82 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * a * ((minor82 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * b * ((minor82 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value82 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant39, hm1, determinant70, hm2, determinant80, hm3, determinant81]
  dsimp only [value82, value39, value70, value80, value81] <;> ring

def minor83 (a b c d Y T : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (5 * Y)
    | 0, 1 => ((-20) + ((-2) * T * a))
    | 0, 2 => (((-3) * T * b) + (3 * Y * a))
    | 1, 1 => (5 * Y)
    | 1, 2 => ((-20) + ((-2) * T * a))
    | 2, 2 => (5 * Y)
    | _, _ => 0
def value83 (a b c d Y T : ℂ) : ℂ := (125 * (Y^3))

theorem determinant83 (a b c d Y T : ℂ) :
    (minor83 a b c d Y T).det = value83 a b c d Y T := by
  have hm0 : (minor83 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove =
      minor40 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor83 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove =
      minor71 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor83 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove =
      minor79 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (5 * Y) * ((minor83 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove).det + ((-1 : ℂ)^1 * ((-20) + ((-2) * T * a)) * ((minor83 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove).det + ((-1 : ℂ)^2 * (((-3) * T * b) + (3 * Y * a)) * ((minor83 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove).det + (0))) = value83 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant40, hm1, determinant71, hm2, determinant79]
  dsimp only [value83, value40, value71, value79] <;> ring

def minor84 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => ((-20) + ((-2) * T * a))
    | 0, 1 => (((-3) * T * b) + (3 * Y * a))
    | 0, 2 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 0, 3 => b
    | 1, 0 => (5 * Y)
    | 1, 1 => ((-20) + ((-2) * T * a))
    | 1, 2 => (((-3) * T * b) + (3 * Y * a))
    | 1, 3 => a
    | 2, 1 => (5 * Y)
    | 2, 2 => ((-20) + ((-2) * T * a))
    | 3, 2 => (5 * Y)
    | 3, 3 => 1
    | _, _ => 0
def value84 (a b c d Y T : ℂ) : ℂ := ((-8000) + ((-2400) * T * a) + ((-240) * (T^2) * (a^2)) + ((-75) * b * (Y^3)) + ((-50) * a * (Y^2)) + ((-8) * (T^3) * (a^3)) + ((-600) * T * Y * b) + ((-100) * T * c * (Y^2)) + (10 * T * (Y^2) * (a^2)) + ((-60) * Y * a * b * (T^2)))

theorem determinant84 (a b c d Y T : ℂ) :
    (minor84 a b c d Y T).det = value84 a b c d Y T := by
  have hm0 : (minor84 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove =
      minor41 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor84 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove =
      minor72 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor84 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove =
      minor80 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor84 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove =
      minor83 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * ((-20) + ((-2) * T * a)) * ((minor84 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * (((-3) * T * b) + (3 * Y * a)) * ((minor84 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor84 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * b * ((minor84 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value84 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant41, hm1, determinant72, hm2, determinant80, hm3, determinant83]
  dsimp only [value84, value41, value72, value80, value83] <;> ring

def minor85 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => ((-20) + ((-2) * T * a))
    | 0, 1 => (((-3) * T * b) + (3 * Y * a))
    | 0, 2 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 0, 3 => a
    | 1, 0 => (5 * Y)
    | 1, 1 => ((-20) + ((-2) * T * a))
    | 1, 2 => (((-3) * T * b) + (3 * Y * a))
    | 2, 1 => (5 * Y)
    | 2, 2 => ((-20) + ((-2) * T * a))
    | 2, 3 => 1
    | 3, 2 => (5 * Y)
    | _, _ => 0
def value85 (a b c d Y T : ℂ) : ℂ := (((-2000) * Y) + ((-50) * a * (Y^3)) + ((-400) * T * Y * a) + ((-75) * T * b * (Y^2)) + ((-20) * Y * (T^2) * (a^2)))

theorem determinant85 (a b c d Y T : ℂ) :
    (minor85 a b c d Y T).det = value85 a b c d Y T := by
  have hm0 : (minor85 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove =
      minor42 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor85 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove =
      minor73 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor85 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove =
      minor81 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor85 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove =
      minor83 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * ((-20) + ((-2) * T * a)) * ((minor85 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * (((-3) * T * b) + (3 * Y * a)) * ((minor85 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor85 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * a * ((minor85 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value85 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant42, hm1, determinant73, hm2, determinant81, hm3, determinant83]
  dsimp only [value85, value42, value73, value81, value83] <;> ring

def minor86 (a b c d Y T : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (((-3) * T * b) + (3 * Y * a))
    | 0, 1 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 0, 2 => (((-2) * b) + (Y * c) + ((-5) * T * d))
    | 0, 3 => b
    | 0, 4 => c
    | 1, 0 => ((-20) + ((-2) * T * a))
    | 1, 1 => (((-3) * T * b) + (3 * Y * a))
    | 1, 2 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 1, 3 => a
    | 1, 4 => b
    | 2, 0 => (5 * Y)
    | 2, 1 => ((-20) + ((-2) * T * a))
    | 2, 2 => (((-3) * T * b) + (3 * Y * a))
    | 2, 4 => a
    | 3, 1 => (5 * Y)
    | 3, 2 => ((-20) + ((-2) * T * a))
    | 3, 3 => 1
    | 4, 2 => (5 * Y)
    | 4, 4 => 1
    | _, _ => 0
def value86 (a b c d Y T : ℂ) : ℂ := ((7200 * b) + ((-2000) * T * d) + ((-1600) * Y * c) + ((-27) * (T^3) * (b^3)) + (12 * (Y^3) * (a^3)) + (45 * (Y^3) * (b^2)) + (660 * Y * (a^2)) + ((-400) * a * d * (T^2)) + ((-40) * a * c * (Y^3)) + ((-20) * d * (T^3) * (a^2)) + ((-4) * b * (T^3) * (a^3)) + (12 * Y * (T^2) * (a^4)) + (64 * b * (T^2) * (a^2)) + (80 * Y * (T^2) * (c^2)) + (168 * T * Y * (a^3)) + (480 * b * c * (T^2)) + (630 * T * Y * (b^2)) + (1760 * T * a * b) + ((-560) * T * Y * a * c) + ((-75) * Y * b * d * (T^2)) + ((-64) * Y * c * (T^2) * (a^2)) + ((-50) * T * a * d * (Y^2)) + (8 * T * b * (Y^2) * (a^2)) + (48 * a * b * c * (T^3)) + (57 * Y * a * (T^2) * (b^2)) + (60 * T * b * c * (Y^2)))

theorem determinant86 (a b c d Y T : ℂ) :
    (minor86 a b c d Y T).det = value86 a b c d Y T := by
  have hm0 : (minor86 a b c d Y T).submatrix Fin.succ (0 : Fin 5).succAbove =
      minor43 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor86 a b c d Y T).submatrix Fin.succ (1 : Fin 5).succAbove =
      minor74 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor86 a b c d Y T).submatrix Fin.succ (2 : Fin 5).succAbove =
      minor82 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor86 a b c d Y T).submatrix Fin.succ (3 : Fin 5).succAbove =
      minor84 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm4 : (minor86 a b c d Y T).submatrix Fin.succ (4 : Fin 5).succAbove =
      minor85 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (((-3) * T * b) + (3 * Y * a)) * ((minor86 a b c d Y T).submatrix Fin.succ (0 : Fin 5).succAbove).det + ((-1 : ℂ)^1 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor86 a b c d Y T).submatrix Fin.succ (1 : Fin 5).succAbove).det + ((-1 : ℂ)^2 * (((-2) * b) + (Y * c) + ((-5) * T * d)) * ((minor86 a b c d Y T).submatrix Fin.succ (2 : Fin 5).succAbove).det + ((-1 : ℂ)^3 * b * ((minor86 a b c d Y T).submatrix Fin.succ (3 : Fin 5).succAbove).det + ((-1 : ℂ)^4 * c * ((minor86 a b c d Y T).submatrix Fin.succ (4 : Fin 5).succAbove).det + (0))))) = value86 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant43, hm1, determinant74, hm2, determinant82, hm3, determinant84, hm4, determinant85]
  dsimp only [value86, value43, value74, value82, value84, value85] <;> ring

def minor87 (a b c d Y T : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (5 * Y)
    | 0, 1 => ((-20) + ((-2) * T * a))
    | 0, 2 => 1
    | 1, 1 => (5 * Y)
    | _, _ => 0
def value87 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant87 (a b c d Y T : ℂ) :
    (minor87 a b c d Y T).det = value87 a b c d Y T := by
  have hm0 : (minor87 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove =
      minor33 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor87 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove =
      minor64 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor87 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove =
      minor79 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (5 * Y) * ((minor87 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove).det + ((-1 : ℂ)^1 * ((-20) + ((-2) * T * a)) * ((minor87 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove).det + ((-1 : ℂ)^2 * 1 * ((minor87 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove).det + (0))) = value87 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant33, hm1, determinant64, hm2, determinant79]
  dsimp only [value87, value33, value64, value79] <;> ring

def minor88 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => ((-20) + ((-2) * T * a))
    | 0, 1 => (((-3) * T * b) + (3 * Y * a))
    | 0, 3 => b
    | 1, 0 => (5 * Y)
    | 1, 1 => ((-20) + ((-2) * T * a))
    | 1, 2 => 1
    | 1, 3 => a
    | 2, 1 => (5 * Y)
    | 3, 3 => 1
    | _, _ => 0
def value88 (a b c d Y T : ℂ) : ℂ := ((100 * Y) + (10 * T * Y * a))

theorem determinant88 (a b c d Y T : ℂ) :
    (minor88 a b c d Y T).det = value88 a b c d Y T := by
  have hm0 : (minor88 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove =
      minor34 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor88 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove =
      minor65 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor88 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove =
      minor87 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * ((-20) + ((-2) * T * a)) * ((minor88 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * (((-3) * T * b) + (3 * Y * a)) * ((minor88 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * 0 * ((minor88 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * b * ((minor88 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value88 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant34, hm1, determinant65, hm3, determinant87]
  dsimp only [value88, value34, value65, value87] <;> ring

def minor89 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => ((-20) + ((-2) * T * a))
    | 0, 1 => (((-3) * T * b) + (3 * Y * a))
    | 0, 2 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 1, 0 => (5 * Y)
    | 1, 1 => ((-20) + ((-2) * T * a))
    | 1, 2 => (((-3) * T * b) + (3 * Y * a))
    | 1, 3 => 1
    | 2, 1 => (5 * Y)
    | 2, 2 => ((-20) + ((-2) * T * a))
    | 3, 2 => (5 * Y)
    | _, _ => 0
def value89 (a b c d Y T : ℂ) : ℂ := (((-500) * (Y^2)) + ((-50) * T * a * (Y^2)))

theorem determinant89 (a b c d Y T : ℂ) :
    (minor89 a b c d Y T).det = value89 a b c d Y T := by
  have hm0 : (minor89 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove =
      minor44 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor89 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove =
      minor75 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor89 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove =
      minor87 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * ((-20) + ((-2) * T * a)) * ((minor89 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * (((-3) * T * b) + (3 * Y * a)) * ((minor89 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor89 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * 0 * ((minor89 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value89 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant44, hm1, determinant75, hm2, determinant87]
  dsimp only [value89, value44, value75, value87] <;> ring

end Mordell.Determinants
