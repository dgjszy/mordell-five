import Mordell.Determinants.Part13

set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Mordell.Determinants

def minor210 (a b c d Y T : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (5 * Y)
    | 0, 1 => (((-2) * b) + (Y * c) + ((-5) * T * d))
    | 0, 2 => a
    | 0, 3 => b
    | 0, 4 => c
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
def value210 (a b c d Y T : ℂ) : ℂ := (((-15) * b * (Y^2)) + (70 * Y * a) + ((-20) * T * Y * c) + (10 * T * Y * (a^2)))

theorem determinant210 (a b c d Y T : ℂ) :
    (minor210 a b c d Y T).det = value210 a b c d Y T := by
  have hm0 : (minor210 a b c d Y T).submatrix Fin.succ (0 : Fin 5).succAbove =
      minor31 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor210 a b c d Y T).submatrix Fin.succ (1 : Fin 5).succAbove =
      minor201 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor210 a b c d Y T).submatrix Fin.succ (2 : Fin 5).succAbove =
      minor206 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor210 a b c d Y T).submatrix Fin.succ (3 : Fin 5).succAbove =
      minor208 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm4 : (minor210 a b c d Y T).submatrix Fin.succ (4 : Fin 5).succAbove =
      minor209 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (5 * Y) * ((minor210 a b c d Y T).submatrix Fin.succ (0 : Fin 5).succAbove).det + ((-1 : ℂ)^1 * (((-2) * b) + (Y * c) + ((-5) * T * d)) * ((minor210 a b c d Y T).submatrix Fin.succ (1 : Fin 5).succAbove).det + ((-1 : ℂ)^2 * a * ((minor210 a b c d Y T).submatrix Fin.succ (2 : Fin 5).succAbove).det + ((-1 : ℂ)^3 * b * ((minor210 a b c d Y T).submatrix Fin.succ (3 : Fin 5).succAbove).det + ((-1 : ℂ)^4 * c * ((minor210 a b c d Y T).submatrix Fin.succ (4 : Fin 5).succAbove).det + (0))))) = value210 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant31, hm1, determinant201, hm2, determinant206, hm3, determinant208, hm4, determinant209]
  dsimp only [value210, value31, value201, value206, value208, value209] <;> ring

def minor211 (a b c d Y T : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 1 => (5 * Y)
    | _, _ => 0
def value211 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant211 (a b c d Y T : ℂ) :
    (minor211 a b c d Y T).det = value211 a b c d Y T := by
  have hm1 : (minor211 a b c d Y T).submatrix Fin.succ (1 : Fin 2).succAbove =
      minor198 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * 0 * ((minor211 a b c d Y T).submatrix Fin.succ (0 : Fin 2).succAbove).det + ((-1 : ℂ)^1 * (5 * Y) * ((minor211 a b c d Y T).submatrix Fin.succ (1 : Fin 2).succAbove).det + (0)) = value211 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm1, determinant198]
  dsimp only [value211, value198] <;> ring

def minor212 (a b c d Y T : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 1 => ((-20) + ((-2) * T * a))
    | 0, 2 => a
    | 1, 1 => (5 * Y)
    | 2, 2 => 1
    | _, _ => 0
def value212 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant212 (a b c d Y T : ℂ) :
    (minor212 a b c d Y T).det = value212 a b c d Y T := by
  have hm1 : (minor212 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove =
      minor195 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor212 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove =
      minor211 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * 0 * ((minor212 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove).det + ((-1 : ℂ)^1 * ((-20) + ((-2) * T * a)) * ((minor212 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove).det + ((-1 : ℂ)^2 * a * ((minor212 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove).det + (0))) = value212 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm1, determinant195, hm2, determinant211]
  dsimp only [value212, value195, value211] <;> ring

def minor213 (a b c d Y T : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 1 => ((-20) + ((-2) * T * a))
    | 1, 1 => (5 * Y)
    | 1, 2 => 1
    | _, _ => 0
def value213 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant213 (a b c d Y T : ℂ) :
    (minor213 a b c d Y T).det = value213 a b c d Y T := by
  have hm1 : (minor213 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove =
      minor199 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * 0 * ((minor213 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove).det + ((-1 : ℂ)^1 * ((-20) + ((-2) * T * a)) * ((minor213 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove).det + ((-1 : ℂ)^2 * 0 * ((minor213 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove).det + (0))) = value213 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm1, determinant199]
  dsimp only [value213, value199] <;> ring

def minor214 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 1 => (((-3) * T * b) + (3 * Y * a))
    | 0, 2 => a
    | 0, 3 => b
    | 1, 1 => ((-20) + ((-2) * T * a))
    | 1, 3 => a
    | 2, 1 => (5 * Y)
    | 2, 2 => 1
    | 3, 3 => 1
    | _, _ => 0
def value214 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant214 (a b c d Y T : ℂ) :
    (minor214 a b c d Y T).det = value214 a b c d Y T := by
  have hm1 : (minor214 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove =
      minor202 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor214 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove =
      minor212 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor214 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove =
      minor213 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * 0 * ((minor214 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * (((-3) * T * b) + (3 * Y * a)) * ((minor214 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * a * ((minor214 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * b * ((minor214 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value214 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm1, determinant202, hm2, determinant212, hm3, determinant213]
  dsimp only [value214, value202, value212, value213] <;> ring

def minor215 (a b c d Y T : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 1 => ((-20) + ((-2) * T * a))
    | 0, 2 => (((-3) * T * b) + (3 * Y * a))
    | 1, 1 => (5 * Y)
    | 1, 2 => ((-20) + ((-2) * T * a))
    | 2, 2 => (5 * Y)
    | _, _ => 0
def value215 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant215 (a b c d Y T : ℂ) :
    (minor215 a b c d Y T).det = value215 a b c d Y T := by
  have hm1 : (minor215 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove =
      minor203 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor215 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove =
      minor211 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * 0 * ((minor215 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove).det + ((-1 : ℂ)^1 * ((-20) + ((-2) * T * a)) * ((minor215 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove).det + ((-1 : ℂ)^2 * (((-3) * T * b) + (3 * Y * a)) * ((minor215 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove).det + (0))) = value215 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm1, determinant203, hm2, determinant211]
  dsimp only [value215, value203, value211] <;> ring

def minor216 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
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
def value216 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant216 (a b c d Y T : ℂ) :
    (minor216 a b c d Y T).det = value216 a b c d Y T := by
  have hm1 : (minor216 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove =
      minor204 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor216 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove =
      minor212 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor216 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove =
      minor215 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * 0 * ((minor216 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * (((-3) * T * b) + (3 * Y * a)) * ((minor216 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor216 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * b * ((minor216 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value216 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm1, determinant204, hm2, determinant212, hm3, determinant215]
  dsimp only [value216, value204, value212, value215] <;> ring

def minor217 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
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
def value217 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant217 (a b c d Y T : ℂ) :
    (minor217 a b c d Y T).det = value217 a b c d Y T := by
  have hm1 : (minor217 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove =
      minor205 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor217 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove =
      minor213 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor217 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove =
      minor215 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * 0 * ((minor217 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * (((-3) * T * b) + (3 * Y * a)) * ((minor217 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor217 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * a * ((minor217 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value217 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm1, determinant205, hm2, determinant213, hm3, determinant215]
  dsimp only [value217, value205, value213, value215] <;> ring

def minor218 (a b c d Y T : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (5 * Y)
    | 0, 1 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 0, 2 => (((-2) * b) + (Y * c) + ((-5) * T * d))
    | 0, 3 => b
    | 0, 4 => c
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
def value218 (a b c d Y T : ℂ) : ℂ := (((-300) * b * (Y^2)) + (20 * (Y^3) * (a^2)) + (1400 * Y * a) + ((-400) * T * Y * c) + (20 * Y * (T^2) * (a^3)) + (45 * Y * (T^2) * (b^2)) + (340 * T * Y * (a^2)) + ((-40) * Y * a * c * (T^2)) + (30 * T * a * b * (Y^2)))

theorem determinant218 (a b c d Y T : ℂ) :
    (minor218 a b c d Y T).det = value218 a b c d Y T := by
  have hm0 : (minor218 a b c d Y T).submatrix Fin.succ (0 : Fin 5).succAbove =
      minor43 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor218 a b c d Y T).submatrix Fin.succ (1 : Fin 5).succAbove =
      minor206 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor218 a b c d Y T).submatrix Fin.succ (2 : Fin 5).succAbove =
      minor214 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor218 a b c d Y T).submatrix Fin.succ (3 : Fin 5).succAbove =
      minor216 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm4 : (minor218 a b c d Y T).submatrix Fin.succ (4 : Fin 5).succAbove =
      minor217 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (5 * Y) * ((minor218 a b c d Y T).submatrix Fin.succ (0 : Fin 5).succAbove).det + ((-1 : ℂ)^1 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor218 a b c d Y T).submatrix Fin.succ (1 : Fin 5).succAbove).det + ((-1 : ℂ)^2 * (((-2) * b) + (Y * c) + ((-5) * T * d)) * ((minor218 a b c d Y T).submatrix Fin.succ (2 : Fin 5).succAbove).det + ((-1 : ℂ)^3 * b * ((minor218 a b c d Y T).submatrix Fin.succ (3 : Fin 5).succAbove).det + ((-1 : ℂ)^4 * c * ((minor218 a b c d Y T).submatrix Fin.succ (4 : Fin 5).succAbove).det + (0))))) = value218 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant43, hm1, determinant206, hm2, determinant214, hm3, determinant216, hm4, determinant217]
  dsimp only [value218, value43, value206, value214, value216, value217] <;> ring

def minor219 (a b c d Y T : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 1 => ((-20) + ((-2) * T * a))
    | 0, 2 => 1
    | 1, 1 => (5 * Y)
    | _, _ => 0
def value219 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant219 (a b c d Y T : ℂ) :
    (minor219 a b c d Y T).det = value219 a b c d Y T := by
  have hm1 : (minor219 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove =
      minor196 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor219 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove =
      minor211 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * 0 * ((minor219 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove).det + ((-1 : ℂ)^1 * ((-20) + ((-2) * T * a)) * ((minor219 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove).det + ((-1 : ℂ)^2 * 1 * ((minor219 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove).det + (0))) = value219 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm1, determinant196, hm2, determinant211]
  dsimp only [value219, value196, value211] <;> ring

def minor220 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 1 => (((-3) * T * b) + (3 * Y * a))
    | 0, 3 => b
    | 1, 1 => ((-20) + ((-2) * T * a))
    | 1, 2 => 1
    | 1, 3 => a
    | 2, 1 => (5 * Y)
    | 3, 3 => 1
    | _, _ => 0
def value220 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant220 (a b c d Y T : ℂ) :
    (minor220 a b c d Y T).det = value220 a b c d Y T := by
  have hm1 : (minor220 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove =
      minor197 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor220 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove =
      minor219 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * 0 * ((minor220 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * (((-3) * T * b) + (3 * Y * a)) * ((minor220 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * 0 * ((minor220 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * b * ((minor220 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value220 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm1, determinant197, hm3, determinant219]
  dsimp only [value220, value197, value219] <;> ring

def minor221 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 1 => (((-3) * T * b) + (3 * Y * a))
    | 0, 2 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 1, 1 => ((-20) + ((-2) * T * a))
    | 1, 2 => (((-3) * T * b) + (3 * Y * a))
    | 1, 3 => 1
    | 2, 1 => (5 * Y)
    | 2, 2 => ((-20) + ((-2) * T * a))
    | 3, 2 => (5 * Y)
    | _, _ => 0
def value221 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant221 (a b c d Y T : ℂ) :
    (minor221 a b c d Y T).det = value221 a b c d Y T := by
  have hm1 : (minor221 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove =
      minor207 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor221 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove =
      minor219 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * 0 * ((minor221 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * (((-3) * T * b) + (3 * Y * a)) * ((minor221 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor221 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * 0 * ((minor221 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value221 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm1, determinant207, hm2, determinant219]
  dsimp only [value221, value207, value219] <;> ring

def minor222 (a b c d Y T : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (5 * Y)
    | 0, 1 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 0, 2 => (((-2) * b) + (Y * c) + ((-5) * T * d))
    | 0, 3 => a
    | 0, 4 => c
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
def value222 (a b c d Y T : ℂ) : ℂ := (((-75) * b * (Y^3)) + (150 * a * (Y^2)) + ((-300) * T * Y * b) + ((-100) * T * c * (Y^2)) + (30 * T * (Y^2) * (a^2)) + ((-30) * Y * a * b * (T^2)))

theorem determinant222 (a b c d Y T : ℂ) :
    (minor222 a b c d Y T).det = value222 a b c d Y T := by
  have hm0 : (minor222 a b c d Y T).submatrix Fin.succ (0 : Fin 5).succAbove =
      minor45 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor222 a b c d Y T).submatrix Fin.succ (1 : Fin 5).succAbove =
      minor208 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor222 a b c d Y T).submatrix Fin.succ (2 : Fin 5).succAbove =
      minor220 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor222 a b c d Y T).submatrix Fin.succ (3 : Fin 5).succAbove =
      minor216 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm4 : (minor222 a b c d Y T).submatrix Fin.succ (4 : Fin 5).succAbove =
      minor221 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (5 * Y) * ((minor222 a b c d Y T).submatrix Fin.succ (0 : Fin 5).succAbove).det + ((-1 : ℂ)^1 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor222 a b c d Y T).submatrix Fin.succ (1 : Fin 5).succAbove).det + ((-1 : ℂ)^2 * (((-2) * b) + (Y * c) + ((-5) * T * d)) * ((minor222 a b c d Y T).submatrix Fin.succ (2 : Fin 5).succAbove).det + ((-1 : ℂ)^3 * a * ((minor222 a b c d Y T).submatrix Fin.succ (3 : Fin 5).succAbove).det + ((-1 : ℂ)^4 * c * ((minor222 a b c d Y T).submatrix Fin.succ (4 : Fin 5).succAbove).det + (0))))) = value222 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant45, hm1, determinant208, hm2, determinant220, hm3, determinant216, hm4, determinant221]
  dsimp only [value222, value45, value208, value220, value216, value221] <;> ring

def minor223 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 1 => (((-3) * T * b) + (3 * Y * a))
    | 0, 3 => a
    | 1, 1 => ((-20) + ((-2) * T * a))
    | 1, 2 => 1
    | 2, 1 => (5 * Y)
    | 2, 3 => 1
    | _, _ => 0
def value223 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant223 (a b c d Y T : ℂ) :
    (minor223 a b c d Y T).det = value223 a b c d Y T := by
  have hm1 : (minor223 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove =
      minor200 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor223 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove =
      minor219 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * 0 * ((minor223 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * (((-3) * T * b) + (3 * Y * a)) * ((minor223 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * 0 * ((minor223 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * a * ((minor223 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value223 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm1, determinant200, hm3, determinant219]
  dsimp only [value223, value200, value219] <;> ring

def minor224 (a b c d Y T : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (5 * Y)
    | 0, 1 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 0, 2 => (((-2) * b) + (Y * c) + ((-5) * T * d))
    | 0, 3 => a
    | 0, 4 => b
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
def value224 (a b c d Y T : ℂ) : ℂ := (((-50) * a * (Y^3)) + ((-75) * T * b * (Y^2)))

theorem determinant224 (a b c d Y T : ℂ) :
    (minor224 a b c d Y T).det = value224 a b c d Y T := by
  have hm0 : (minor224 a b c d Y T).submatrix Fin.succ (0 : Fin 5).succAbove =
      minor46 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor224 a b c d Y T).submatrix Fin.succ (1 : Fin 5).succAbove =
      minor209 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor224 a b c d Y T).submatrix Fin.succ (2 : Fin 5).succAbove =
      minor223 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor224 a b c d Y T).submatrix Fin.succ (3 : Fin 5).succAbove =
      minor217 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm4 : (minor224 a b c d Y T).submatrix Fin.succ (4 : Fin 5).succAbove =
      minor221 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (5 * Y) * ((minor224 a b c d Y T).submatrix Fin.succ (0 : Fin 5).succAbove).det + ((-1 : ℂ)^1 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor224 a b c d Y T).submatrix Fin.succ (1 : Fin 5).succAbove).det + ((-1 : ℂ)^2 * (((-2) * b) + (Y * c) + ((-5) * T * d)) * ((minor224 a b c d Y T).submatrix Fin.succ (2 : Fin 5).succAbove).det + ((-1 : ℂ)^3 * a * ((minor224 a b c d Y T).submatrix Fin.succ (3 : Fin 5).succAbove).det + ((-1 : ℂ)^4 * b * ((minor224 a b c d Y T).submatrix Fin.succ (4 : Fin 5).succAbove).det + (0))))) = value224 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant46, hm1, determinant209, hm2, determinant223, hm3, determinant217, hm4, determinant221]
  dsimp only [value224, value46, value209, value223, value217, value221] <;> ring

end Mordell.Determinants
