import Mordell.Determinants.Part1

set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Mordell.Determinants

def minor30 (a b c d Y T : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (((-2) * b) + (Y * c) + ((-5) * T * d))
    | 0, 2 => a
    | 0, 3 => b
    | 0, 4 => c
    | 1, 0 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 1, 1 => 1
    | 1, 3 => a
    | 1, 4 => b
    | 2, 0 => (((-3) * T * b) + (3 * Y * a))
    | 2, 2 => 1
    | 2, 4 => a
    | 3, 0 => ((-20) + ((-2) * T * a))
    | 3, 3 => 1
    | 4, 0 => (5 * Y)
    | 4, 4 => 1
    | _, _ => 0
def value30 (a b c d Y T : ℂ) : ℂ := ((18 * b) + ((-5) * T * d) + ((-4) * Y * c) + (2 * Y * (a^2)) + (5 * T * a * b))

theorem determinant30 (a b c d Y T : ℂ) :
    (minor30 a b c d Y T).det = value30 a b c d Y T := by
  have hm0 : (minor30 a b c d Y T).submatrix Fin.succ (0 : Fin 5).succAbove =
      minor12 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor30 a b c d Y T).submatrix Fin.succ (2 : Fin 5).succAbove =
      minor21 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor30 a b c d Y T).submatrix Fin.succ (3 : Fin 5).succAbove =
      minor27 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm4 : (minor30 a b c d Y T).submatrix Fin.succ (4 : Fin 5).succAbove =
      minor29 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (((-2) * b) + (Y * c) + ((-5) * T * d)) * ((minor30 a b c d Y T).submatrix Fin.succ (0 : Fin 5).succAbove).det + ((-1 : ℂ)^1 * 0 * ((minor30 a b c d Y T).submatrix Fin.succ (1 : Fin 5).succAbove).det + ((-1 : ℂ)^2 * a * ((minor30 a b c d Y T).submatrix Fin.succ (2 : Fin 5).succAbove).det + ((-1 : ℂ)^3 * b * ((minor30 a b c d Y T).submatrix Fin.succ (3 : Fin 5).succAbove).det + ((-1 : ℂ)^4 * c * ((minor30 a b c d Y T).submatrix Fin.succ (4 : Fin 5).succAbove).det + (0))))) = value30 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant12, hm2, determinant21, hm3, determinant27, hm4, determinant29]
  dsimp only [value30, value12, value21, value27, value29] <;> ring

def minor31 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 0, 2 => a
    | 0, 3 => b
    | 1, 0 => (((-3) * T * b) + (3 * Y * a))
    | 1, 1 => 1
    | 1, 3 => a
    | 2, 0 => ((-20) + ((-2) * T * a))
    | 2, 2 => 1
    | 3, 0 => (5 * Y)
    | 3, 3 => 1
    | _, _ => 0
def value31 (a b c d Y T : ℂ) : ℂ := ((14 * a) + ((-4) * T * c) + ((-3) * Y * b) + (2 * T * (a^2)))

theorem determinant31 (a b c d Y T : ℂ) :
    (minor31 a b c d Y T).det = value31 a b c d Y T := by
  have hm0 : (minor31 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove =
      minor5 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor31 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove =
      minor25 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor31 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove =
      minor28 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor31 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * 0 * ((minor31 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * a * ((minor31 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * b * ((minor31 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value31 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant5, hm2, determinant25, hm3, determinant28]
  dsimp only [value31, value5, value25, value28] <;> ring

def minor32 (a b c d Y T : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (5 * Y)
    | 1, 1 => 1
    | _, _ => 0
def value32 (a b c d Y T : ℂ) : ℂ := (5 * Y)

theorem determinant32 (a b c d Y T : ℂ) :
    (minor32 a b c d Y T).det = value32 a b c d Y T := by
  have hm0 : (minor32 a b c d Y T).submatrix Fin.succ (0 : Fin 2).succAbove =
      minor1 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (5 * Y) * ((minor32 a b c d Y T).submatrix Fin.succ (0 : Fin 2).succAbove).det + ((-1 : ℂ)^1 * 0 * ((minor32 a b c d Y T).submatrix Fin.succ (1 : Fin 2).succAbove).det + (0)) = value32 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant1]
  dsimp only [value32, value1] <;> ring

def minor33 (a b c d Y T : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (5 * Y)
    | _, _ => 0
def value33 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant33 (a b c d Y T : ℂ) :
    (minor33 a b c d Y T).det = value33 a b c d Y T := by
  have hm0 : (minor33 a b c d Y T).submatrix Fin.succ (0 : Fin 2).succAbove =
      minor3 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (5 * Y) * ((minor33 a b c d Y T).submatrix Fin.succ (0 : Fin 2).succAbove).det + ((-1 : ℂ)^1 * 0 * ((minor33 a b c d Y T).submatrix Fin.succ (1 : Fin 2).succAbove).det + (0)) = value33 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant3]
  dsimp only [value33, value3] <;> ring

def minor34 (a b c d Y T : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => ((-20) + ((-2) * T * a))
    | 0, 1 => 1
    | 0, 2 => a
    | 1, 0 => (5 * Y)
    | 2, 2 => 1
    | _, _ => 0
def value34 (a b c d Y T : ℂ) : ℂ := ((-5) * Y)

theorem determinant34 (a b c d Y T : ℂ) :
    (minor34 a b c d Y T).det = value34 a b c d Y T := by
  have hm0 : (minor34 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove =
      minor22 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor34 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove =
      minor32 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor34 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove =
      minor33 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * ((-20) + ((-2) * T * a)) * ((minor34 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove).det + ((-1 : ℂ)^1 * 1 * ((minor34 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove).det + ((-1 : ℂ)^2 * a * ((minor34 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove).det + (0))) = value34 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant22, hm1, determinant32, hm2, determinant33]
  dsimp only [value34, value22, value32, value33] <;> ring

def minor35 (a b c d Y T : ℂ) : Matrix (Fin 1) (Fin 1) ℂ :=
  fun i j => match i.val, j.val with
    | _, _ => 0
def value35 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant35 (a b c d Y T : ℂ) :
    (minor35 a b c d Y T).det = value35 a b c d Y T := by
  simp [Matrix.det_unique, minor35, value35]

def minor36 (a b c d Y T : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (5 * Y)
    | 0, 1 => 1
    | _, _ => 0
def value36 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant36 (a b c d Y T : ℂ) :
    (minor36 a b c d Y T).det = value36 a b c d Y T := by
  have hm0 : (minor36 a b c d Y T).submatrix Fin.succ (0 : Fin 2).succAbove =
      minor14 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor36 a b c d Y T).submatrix Fin.succ (1 : Fin 2).succAbove =
      minor35 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (5 * Y) * ((minor36 a b c d Y T).submatrix Fin.succ (0 : Fin 2).succAbove).det + ((-1 : ℂ)^1 * 1 * ((minor36 a b c d Y T).submatrix Fin.succ (1 : Fin 2).succAbove).det + (0)) = value36 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant14, hm1, determinant35]
  dsimp only [value36, value14, value35] <;> ring

def minor37 (a b c d Y T : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => ((-20) + ((-2) * T * a))
    | 0, 1 => 1
    | 1, 0 => (5 * Y)
    | 1, 2 => 1
    | _, _ => 0
def value37 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant37 (a b c d Y T : ℂ) :
    (minor37 a b c d Y T).det = value37 a b c d Y T := by
  have hm0 : (minor37 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove =
      minor4 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor37 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove =
      minor36 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * ((-20) + ((-2) * T * a)) * ((minor37 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove).det + ((-1 : ℂ)^1 * 1 * ((minor37 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove).det + ((-1 : ℂ)^2 * 0 * ((minor37 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove).det + (0))) = value37 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant4, hm1, determinant36]
  dsimp only [value37, value4, value36] <;> ring

def minor38 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (((-3) * T * b) + (3 * Y * a))
    | 0, 2 => a
    | 0, 3 => b
    | 1, 0 => ((-20) + ((-2) * T * a))
    | 1, 1 => 1
    | 1, 3 => a
    | 2, 0 => (5 * Y)
    | 2, 2 => 1
    | 3, 3 => 1
    | _, _ => 0
def value38 (a b c d Y T : ℂ) : ℂ := (((-3) * T * b) + ((-2) * Y * a))

theorem determinant38 (a b c d Y T : ℂ) :
    (minor38 a b c d Y T).det = value38 a b c d Y T := by
  have hm0 : (minor38 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove =
      minor5 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor38 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove =
      minor34 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor38 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove =
      minor37 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (((-3) * T * b) + (3 * Y * a)) * ((minor38 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * 0 * ((minor38 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * a * ((minor38 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * b * ((minor38 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value38 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant5, hm2, determinant34, hm3, determinant37]
  dsimp only [value38, value5, value34, value37] <;> ring

def minor39 (a b c d Y T : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => ((-20) + ((-2) * T * a))
    | 0, 2 => a
    | 1, 0 => (5 * Y)
    | 1, 1 => 1
    | 2, 2 => 1
    | _, _ => 0
def value39 (a b c d Y T : ℂ) : ℂ := ((-20) + ((-2) * T * a))

theorem determinant39 (a b c d Y T : ℂ) :
    (minor39 a b c d Y T).det = value39 a b c d Y T := by
  have hm0 : (minor39 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove =
      minor2 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor39 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove =
      minor36 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * ((-20) + ((-2) * T * a)) * ((minor39 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove).det + ((-1 : ℂ)^1 * 0 * ((minor39 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove).det + ((-1 : ℂ)^2 * a * ((minor39 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove).det + (0))) = value39 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant2, hm2, determinant36]
  dsimp only [value39, value2, value36] <;> ring

def minor40 (a b c d Y T : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (5 * Y)
    | 0, 1 => ((-20) + ((-2) * T * a))
    | 1, 1 => (5 * Y)
    | _, _ => 0
def value40 (a b c d Y T : ℂ) : ℂ := (25 * (Y^2))

theorem determinant40 (a b c d Y T : ℂ) :
    (minor40 a b c d Y T).det = value40 a b c d Y T := by
  have hm0 : (minor40 a b c d Y T).submatrix Fin.succ (0 : Fin 2).succAbove =
      minor15 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor40 a b c d Y T).submatrix Fin.succ (1 : Fin 2).succAbove =
      minor35 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (5 * Y) * ((minor40 a b c d Y T).submatrix Fin.succ (0 : Fin 2).succAbove).det + ((-1 : ℂ)^1 * ((-20) + ((-2) * T * a)) * ((minor40 a b c d Y T).submatrix Fin.succ (1 : Fin 2).succAbove).det + (0)) = value40 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant15, hm1, determinant35]
  dsimp only [value40, value15, value35] <;> ring

def minor41 (a b c d Y T : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => ((-20) + ((-2) * T * a))
    | 0, 1 => (((-3) * T * b) + (3 * Y * a))
    | 0, 2 => a
    | 1, 0 => (5 * Y)
    | 1, 1 => ((-20) + ((-2) * T * a))
    | 2, 1 => (5 * Y)
    | 2, 2 => 1
    | _, _ => 0
def value41 (a b c d Y T : ℂ) : ℂ := (400 + (4 * (T^2) * (a^2)) + (10 * a * (Y^2)) + (80 * T * a) + (15 * T * Y * b))

theorem determinant41 (a b c d Y T : ℂ) :
    (minor41 a b c d Y T).det = value41 a b c d Y T := by
  have hm0 : (minor41 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove =
      minor23 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor41 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove =
      minor32 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor41 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove =
      minor40 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * ((-20) + ((-2) * T * a)) * ((minor41 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove).det + ((-1 : ℂ)^1 * (((-3) * T * b) + (3 * Y * a)) * ((minor41 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove).det + ((-1 : ℂ)^2 * a * ((minor41 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove).det + (0))) = value41 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant23, hm1, determinant32, hm2, determinant40]
  dsimp only [value41, value23, value32, value40] <;> ring

def minor42 (a b c d Y T : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => ((-20) + ((-2) * T * a))
    | 0, 1 => (((-3) * T * b) + (3 * Y * a))
    | 1, 0 => (5 * Y)
    | 1, 1 => ((-20) + ((-2) * T * a))
    | 1, 2 => 1
    | 2, 1 => (5 * Y)
    | _, _ => 0
def value42 (a b c d Y T : ℂ) : ℂ := ((100 * Y) + (10 * T * Y * a))

theorem determinant42 (a b c d Y T : ℂ) :
    (minor42 a b c d Y T).det = value42 a b c d Y T := by
  have hm0 : (minor42 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove =
      minor16 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor42 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove =
      minor36 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * ((-20) + ((-2) * T * a)) * ((minor42 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove).det + ((-1 : ℂ)^1 * (((-3) * T * b) + (3 * Y * a)) * ((minor42 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove).det + ((-1 : ℂ)^2 * 0 * ((minor42 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove).det + (0))) = value42 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant16, hm1, determinant36]
  dsimp only [value42, value16, value36] <;> ring

def minor43 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (((-3) * T * b) + (3 * Y * a))
    | 0, 1 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 0, 2 => a
    | 0, 3 => b
    | 1, 0 => ((-20) + ((-2) * T * a))
    | 1, 1 => (((-3) * T * b) + (3 * Y * a))
    | 1, 3 => a
    | 2, 0 => (5 * Y)
    | 2, 1 => ((-20) + ((-2) * T * a))
    | 2, 2 => 1
    | 3, 1 => (5 * Y)
    | 3, 3 => 1
    | _, _ => 0
def value43 (a b c d Y T : ℂ) : ℂ := ((280 * a) + ((-80) * T * c) + ((-60) * Y * b) + (4 * (T^2) * (a^3)) + (4 * (Y^2) * (a^2)) + (9 * (T^2) * (b^2)) + (68 * T * (a^2)) + ((-8) * a * c * (T^2)) + (6 * T * Y * a * b))

theorem determinant43 (a b c d Y T : ℂ) :
    (minor43 a b c d Y T).det = value43 a b c d Y T := by
  have hm0 : (minor43 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove =
      minor17 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor43 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove =
      minor39 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor43 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove =
      minor41 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor43 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove =
      minor42 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (((-3) * T * b) + (3 * Y * a)) * ((minor43 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor43 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * a * ((minor43 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * b * ((minor43 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value43 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant17, hm1, determinant39, hm2, determinant41, hm3, determinant42]
  dsimp only [value43, value17, value39, value41, value42] <;> ring

def minor44 (a b c d Y T : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => ((-20) + ((-2) * T * a))
    | 0, 1 => (((-3) * T * b) + (3 * Y * a))
    | 0, 2 => 1
    | 1, 0 => (5 * Y)
    | 1, 1 => ((-20) + ((-2) * T * a))
    | 2, 1 => (5 * Y)
    | _, _ => 0
def value44 (a b c d Y T : ℂ) : ℂ := (25 * (Y^2))

theorem determinant44 (a b c d Y T : ℂ) :
    (minor44 a b c d Y T).det = value44 a b c d Y T := by
  have hm0 : (minor44 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove =
      minor24 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor44 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove =
      minor33 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor44 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove =
      minor40 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * ((-20) + ((-2) * T * a)) * ((minor44 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove).det + ((-1 : ℂ)^1 * (((-3) * T * b) + (3 * Y * a)) * ((minor44 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove).det + ((-1 : ℂ)^2 * 1 * ((minor44 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove).det + (0))) = value44 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant24, hm1, determinant33, hm2, determinant40]
  dsimp only [value44, value24, value33, value40] <;> ring

end Mordell.Determinants
