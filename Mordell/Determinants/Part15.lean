import Mordell.Determinants.Part14

set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Mordell.Determinants

def minor225 (a b c d Y T : ℂ) : Matrix (Fin 6) (Fin 6) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => ((-20) + ((-2) * T * a))
    | 0, 1 => (((-2) * b) + (Y * c) + ((-5) * T * d))
    | 0, 3 => b
    | 0, 4 => c
    | 0, 5 => d
    | 1, 0 => (5 * Y)
    | 1, 1 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 1, 2 => (((-2) * b) + (Y * c) + ((-5) * T * d))
    | 1, 3 => a
    | 1, 4 => b
    | 1, 5 => c
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
def value225 (a b c d Y T : ℂ) : ℂ := (((-3920) * (a^2)) + ((-1512) * T * (a^3)) + ((-1080) * T * (b^2)) + ((-320) * (T^2) * (c^2)) + ((-192) * (T^2) * (a^4)) + ((-80) * (Y^2) * (a^3)) + ((-8) * (T^3) * (a^5)) + (90 * (Y^2) * (b^2)) + ((-408) * a * (T^2) * (b^2)) + ((-300) * Y * a * b) + ((-80) * T * (Y^2) * (c^2)) + ((-60) * b * c * (Y^3)) + ((-45) * Y * (T^2) * (b^3)) + ((-32) * a * (T^3) * (c^2)) + ((-30) * (T^3) * (a^2) * (b^2)) + ((-20) * b * (Y^3) * (a^2)) + ((-8) * T * (Y^2) * (a^4)) + (32 * c * (T^3) * (a^3)) + (50 * a * d * (Y^3)) + (240 * a * c * (Y^2)) + (300 * b * d * (T^2)) + (544 * c * (T^2) * (a^2)) + (2240 * T * a * c) + ((-304) * T * Y * b * (a^2)) + ((-180) * T * Y * b * c) + ((-100) * Y * c * d * (T^2)) + ((-48) * T * a * (Y^2) * (b^2)) + ((-28) * Y * b * (T^2) * (a^3)) + (30 * a * b * d * (T^3)) + (36 * T * c * (Y^2) * (a^2)) + (70 * Y * d * (T^2) * (a^2)) + (550 * T * Y * a * d) + ((-14) * Y * a * b * c * (T^2)))

theorem determinant225 (a b c d Y T : ℂ) :
    (minor225 a b c d Y T).det = value225 a b c d Y T := by
  have hm0 : (minor225 a b c d Y T).submatrix Fin.succ (0 : Fin 6).succAbove =
      minor47 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor225 a b c d Y T).submatrix Fin.succ (1 : Fin 6).succAbove =
      minor210 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor225 a b c d Y T).submatrix Fin.succ (3 : Fin 6).succAbove =
      minor218 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm4 : (minor225 a b c d Y T).submatrix Fin.succ (4 : Fin 6).succAbove =
      minor222 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm5 : (minor225 a b c d Y T).submatrix Fin.succ (5 : Fin 6).succAbove =
      minor224 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * ((-20) + ((-2) * T * a)) * ((minor225 a b c d Y T).submatrix Fin.succ (0 : Fin 6).succAbove).det + ((-1 : ℂ)^1 * (((-2) * b) + (Y * c) + ((-5) * T * d)) * ((minor225 a b c d Y T).submatrix Fin.succ (1 : Fin 6).succAbove).det + ((-1 : ℂ)^2 * 0 * ((minor225 a b c d Y T).submatrix Fin.succ (2 : Fin 6).succAbove).det + ((-1 : ℂ)^3 * b * ((minor225 a b c d Y T).submatrix Fin.succ (3 : Fin 6).succAbove).det + ((-1 : ℂ)^4 * c * ((minor225 a b c d Y T).submatrix Fin.succ (4 : Fin 6).succAbove).det + ((-1 : ℂ)^5 * d * ((minor225 a b c d Y T).submatrix Fin.succ (5 : Fin 6).succAbove).det + (0)))))) = value225 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant47, hm1, determinant210, hm3, determinant218, hm4, determinant222, hm5, determinant224]
  dsimp only [value225, value47, value210, value218, value222, value224] <;> ring

def minor226 (a b c d Y T : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => match i.val, j.val with
    | _, _ => 0
def value226 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant226 (a b c d Y T : ℂ) :
    (minor226 a b c d Y T).det = value226 a b c d Y T := by
  rw [show value226 a b c d Y T = 0 by rfl]
  apply Matrix.det_eq_zero_of_row_eq_zero 0
  intro j
  fin_cases j <;> rfl

def minor227 (a b c d Y T : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 1 => (5 * Y)
    | 0, 2 => a
    | 2, 2 => 1
    | _, _ => 0
def value227 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant227 (a b c d Y T : ℂ) :
    (minor227 a b c d Y T).det = value227 a b c d Y T := by
  have hm1 : (minor227 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove =
      minor195 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor227 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove =
      minor226 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * 0 * ((minor227 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove).det + ((-1 : ℂ)^1 * (5 * Y) * ((minor227 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove).det + ((-1 : ℂ)^2 * a * ((minor227 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove).det + (0))) = value227 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm1, determinant195, hm2, determinant226]
  dsimp only [value227, value195, value226] <;> ring

def minor228 (a b c d Y T : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 1 => (5 * Y)
    | 1, 2 => 1
    | _, _ => 0
def value228 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant228 (a b c d Y T : ℂ) :
    (minor228 a b c d Y T).det = value228 a b c d Y T := by
  have hm1 : (minor228 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove =
      minor199 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * 0 * ((minor228 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove).det + ((-1 : ℂ)^1 * (5 * Y) * ((minor228 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove).det + ((-1 : ℂ)^2 * 0 * ((minor228 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove).det + (0))) = value228 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm1, determinant199]
  dsimp only [value228, value199] <;> ring

def minor229 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 1 => ((-20) + ((-2) * T * a))
    | 0, 2 => a
    | 0, 3 => b
    | 1, 1 => (5 * Y)
    | 1, 3 => a
    | 2, 2 => 1
    | 3, 3 => 1
    | _, _ => 0
def value229 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant229 (a b c d Y T : ℂ) :
    (minor229 a b c d Y T).det = value229 a b c d Y T := by
  have hm1 : (minor229 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove =
      minor202 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor229 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove =
      minor227 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor229 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove =
      minor228 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * 0 * ((minor229 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * ((-20) + ((-2) * T * a)) * ((minor229 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * a * ((minor229 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * b * ((minor229 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value229 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm1, determinant202, hm2, determinant227, hm3, determinant228]
  dsimp only [value229, value202, value227, value228] <;> ring

def minor230 (a b c d Y T : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 1 => (5 * Y)
    | 0, 2 => (((-3) * T * b) + (3 * Y * a))
    | 1, 2 => ((-20) + ((-2) * T * a))
    | 2, 2 => (5 * Y)
    | _, _ => 0
def value230 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant230 (a b c d Y T : ℂ) :
    (minor230 a b c d Y T).det = value230 a b c d Y T := by
  have hm1 : (minor230 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove =
      minor203 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor230 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove =
      minor226 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * 0 * ((minor230 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove).det + ((-1 : ℂ)^1 * (5 * Y) * ((minor230 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove).det + ((-1 : ℂ)^2 * (((-3) * T * b) + (3 * Y * a)) * ((minor230 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove).det + (0))) = value230 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm1, determinant203, hm2, determinant226]
  dsimp only [value230, value203, value226] <;> ring

def minor231 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 1 => ((-20) + ((-2) * T * a))
    | 0, 2 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 0, 3 => b
    | 1, 1 => (5 * Y)
    | 1, 2 => (((-3) * T * b) + (3 * Y * a))
    | 1, 3 => a
    | 2, 2 => ((-20) + ((-2) * T * a))
    | 3, 2 => (5 * Y)
    | 3, 3 => 1
    | _, _ => 0
def value231 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant231 (a b c d Y T : ℂ) :
    (minor231 a b c d Y T).det = value231 a b c d Y T := by
  have hm1 : (minor231 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove =
      minor204 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor231 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove =
      minor227 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor231 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove =
      minor230 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * 0 * ((minor231 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * ((-20) + ((-2) * T * a)) * ((minor231 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor231 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * b * ((minor231 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value231 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm1, determinant204, hm2, determinant227, hm3, determinant230]
  dsimp only [value231, value204, value227, value230] <;> ring

def minor232 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 1 => ((-20) + ((-2) * T * a))
    | 0, 2 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 0, 3 => a
    | 1, 1 => (5 * Y)
    | 1, 2 => (((-3) * T * b) + (3 * Y * a))
    | 2, 2 => ((-20) + ((-2) * T * a))
    | 2, 3 => 1
    | 3, 2 => (5 * Y)
    | _, _ => 0
def value232 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant232 (a b c d Y T : ℂ) :
    (minor232 a b c d Y T).det = value232 a b c d Y T := by
  have hm1 : (minor232 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove =
      minor205 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor232 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove =
      minor228 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor232 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove =
      minor230 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * 0 * ((minor232 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * ((-20) + ((-2) * T * a)) * ((minor232 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor232 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * a * ((minor232 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value232 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm1, determinant205, hm2, determinant228, hm3, determinant230]
  dsimp only [value232, value205, value228, value230] <;> ring

def minor233 (a b c d Y T : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (5 * Y)
    | 0, 1 => (((-3) * T * b) + (3 * Y * a))
    | 0, 2 => (((-2) * b) + (Y * c) + ((-5) * T * d))
    | 0, 3 => b
    | 0, 4 => c
    | 1, 1 => ((-20) + ((-2) * T * a))
    | 1, 2 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 1, 3 => a
    | 1, 4 => b
    | 2, 1 => (5 * Y)
    | 2, 2 => (((-3) * T * b) + (3 * Y * a))
    | 2, 4 => a
    | 3, 2 => ((-20) + ((-2) * T * a))
    | 3, 3 => 1
    | 4, 2 => (5 * Y)
    | 4, 4 => 1
    | _, _ => 0
def value233 (a b c d Y T : ℂ) : ℂ := (((-150) * a * (Y^2)) + (75 * b * (Y^3)) + ((-30) * T * (Y^2) * (a^2)) + (100 * T * c * (Y^2)) + (300 * T * Y * b) + (30 * Y * a * b * (T^2)))

theorem determinant233 (a b c d Y T : ℂ) :
    (minor233 a b c d Y T).det = value233 a b c d Y T := by
  have hm0 : (minor233 a b c d Y T).submatrix Fin.succ (0 : Fin 5).succAbove =
      minor74 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor233 a b c d Y T).submatrix Fin.succ (1 : Fin 5).succAbove =
      minor206 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor233 a b c d Y T).submatrix Fin.succ (2 : Fin 5).succAbove =
      minor229 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor233 a b c d Y T).submatrix Fin.succ (3 : Fin 5).succAbove =
      minor231 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm4 : (minor233 a b c d Y T).submatrix Fin.succ (4 : Fin 5).succAbove =
      minor232 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (5 * Y) * ((minor233 a b c d Y T).submatrix Fin.succ (0 : Fin 5).succAbove).det + ((-1 : ℂ)^1 * (((-3) * T * b) + (3 * Y * a)) * ((minor233 a b c d Y T).submatrix Fin.succ (1 : Fin 5).succAbove).det + ((-1 : ℂ)^2 * (((-2) * b) + (Y * c) + ((-5) * T * d)) * ((minor233 a b c d Y T).submatrix Fin.succ (2 : Fin 5).succAbove).det + ((-1 : ℂ)^3 * b * ((minor233 a b c d Y T).submatrix Fin.succ (3 : Fin 5).succAbove).det + ((-1 : ℂ)^4 * c * ((minor233 a b c d Y T).submatrix Fin.succ (4 : Fin 5).succAbove).det + (0))))) = value233 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant74, hm1, determinant206, hm2, determinant229, hm3, determinant231, hm4, determinant232]
  dsimp only [value233, value74, value206, value229, value231, value232] <;> ring

def minor234 (a b c d Y T : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 1 => (5 * Y)
    | 0, 2 => ((-20) + ((-2) * T * a))
    | 1, 2 => (5 * Y)
    | _, _ => 0
def value234 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant234 (a b c d Y T : ℂ) :
    (minor234 a b c d Y T).det = value234 a b c d Y T := by
  have hm1 : (minor234 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove =
      minor211 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor234 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove =
      minor226 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * 0 * ((minor234 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove).det + ((-1 : ℂ)^1 * (5 * Y) * ((minor234 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove).det + ((-1 : ℂ)^2 * ((-20) + ((-2) * T * a)) * ((minor234 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove).det + (0))) = value234 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm1, determinant211, hm2, determinant226]
  dsimp only [value234, value211, value226] <;> ring

def minor235 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 1 => ((-20) + ((-2) * T * a))
    | 0, 2 => (((-3) * T * b) + (3 * Y * a))
    | 0, 3 => b
    | 1, 1 => (5 * Y)
    | 1, 2 => ((-20) + ((-2) * T * a))
    | 1, 3 => a
    | 2, 2 => (5 * Y)
    | 3, 3 => 1
    | _, _ => 0
def value235 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant235 (a b c d Y T : ℂ) :
    (minor235 a b c d Y T).det = value235 a b c d Y T := by
  have hm1 : (minor235 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove =
      minor212 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor235 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove =
      minor227 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor235 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove =
      minor234 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * 0 * ((minor235 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * ((-20) + ((-2) * T * a)) * ((minor235 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * (((-3) * T * b) + (3 * Y * a)) * ((minor235 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * b * ((minor235 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value235 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm1, determinant212, hm2, determinant227, hm3, determinant234]
  dsimp only [value235, value212, value227, value234] <;> ring

def minor236 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 1 => ((-20) + ((-2) * T * a))
    | 0, 2 => (((-3) * T * b) + (3 * Y * a))
    | 0, 3 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 1, 1 => (5 * Y)
    | 1, 2 => ((-20) + ((-2) * T * a))
    | 1, 3 => (((-3) * T * b) + (3 * Y * a))
    | 2, 2 => (5 * Y)
    | 2, 3 => ((-20) + ((-2) * T * a))
    | 3, 3 => (5 * Y)
    | _, _ => 0
def value236 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant236 (a b c d Y T : ℂ) :
    (minor236 a b c d Y T).det = value236 a b c d Y T := by
  have hm1 : (minor236 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove =
      minor215 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor236 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove =
      minor230 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor236 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove =
      minor234 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * 0 * ((minor236 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * ((-20) + ((-2) * T * a)) * ((minor236 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * (((-3) * T * b) + (3 * Y * a)) * ((minor236 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor236 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value236 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm1, determinant215, hm2, determinant230, hm3, determinant234]
  dsimp only [value236, value215, value230, value234] <;> ring

def minor237 (a b c d Y T : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (5 * Y)
    | 0, 1 => (((-3) * T * b) + (3 * Y * a))
    | 0, 2 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 0, 3 => (((-2) * b) + (Y * c) + ((-5) * T * d))
    | 0, 4 => c
    | 1, 1 => ((-20) + ((-2) * T * a))
    | 1, 2 => (((-3) * T * b) + (3 * Y * a))
    | 1, 3 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 1, 4 => b
    | 2, 1 => (5 * Y)
    | 2, 2 => ((-20) + ((-2) * T * a))
    | 2, 3 => (((-3) * T * b) + (3 * Y * a))
    | 2, 4 => a
    | 3, 2 => (5 * Y)
    | 3, 3 => ((-20) + ((-2) * T * a))
    | 4, 3 => (5 * Y)
    | 4, 4 => 1
    | _, _ => 0
def value237 (a b c d Y T : ℂ) : ℂ := (((-40000) * Y) + ((-375) * b * (Y^4)) + ((-250) * a * (Y^3)) + ((-12000) * T * Y * a) + ((-3000) * T * b * (Y^2)) + ((-1200) * Y * (T^2) * (a^2)) + ((-500) * T * c * (Y^3)) + ((-40) * Y * (T^3) * (a^3)) + (50 * T * (Y^3) * (a^2)) + ((-300) * a * b * (T^2) * (Y^2)))

theorem determinant237 (a b c d Y T : ℂ) :
    (minor237 a b c d Y T).det = value237 a b c d Y T := by
  have hm0 : (minor237 a b c d Y T).submatrix Fin.succ (0 : Fin 5).succAbove =
      minor84 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor237 a b c d Y T).submatrix Fin.succ (1 : Fin 5).succAbove =
      minor216 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor237 a b c d Y T).submatrix Fin.succ (2 : Fin 5).succAbove =
      minor231 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor237 a b c d Y T).submatrix Fin.succ (3 : Fin 5).succAbove =
      minor235 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm4 : (minor237 a b c d Y T).submatrix Fin.succ (4 : Fin 5).succAbove =
      minor236 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (5 * Y) * ((minor237 a b c d Y T).submatrix Fin.succ (0 : Fin 5).succAbove).det + ((-1 : ℂ)^1 * (((-3) * T * b) + (3 * Y * a)) * ((minor237 a b c d Y T).submatrix Fin.succ (1 : Fin 5).succAbove).det + ((-1 : ℂ)^2 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor237 a b c d Y T).submatrix Fin.succ (2 : Fin 5).succAbove).det + ((-1 : ℂ)^3 * (((-2) * b) + (Y * c) + ((-5) * T * d)) * ((minor237 a b c d Y T).submatrix Fin.succ (3 : Fin 5).succAbove).det + ((-1 : ℂ)^4 * c * ((minor237 a b c d Y T).submatrix Fin.succ (4 : Fin 5).succAbove).det + (0))))) = value237 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant84, hm1, determinant216, hm2, determinant231, hm3, determinant235, hm4, determinant236]
  dsimp only [value237, value84, value216, value231, value235, value236] <;> ring

def minor238 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 1 => ((-20) + ((-2) * T * a))
    | 0, 2 => (((-3) * T * b) + (3 * Y * a))
    | 0, 3 => a
    | 1, 1 => (5 * Y)
    | 1, 2 => ((-20) + ((-2) * T * a))
    | 2, 2 => (5 * Y)
    | 2, 3 => 1
    | _, _ => 0
def value238 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant238 (a b c d Y T : ℂ) :
    (minor238 a b c d Y T).det = value238 a b c d Y T := by
  have hm1 : (minor238 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove =
      minor213 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor238 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove =
      minor228 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor238 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove =
      minor234 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * 0 * ((minor238 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * ((-20) + ((-2) * T * a)) * ((minor238 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * (((-3) * T * b) + (3 * Y * a)) * ((minor238 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * a * ((minor238 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value238 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm1, determinant213, hm2, determinant228, hm3, determinant234]
  dsimp only [value238, value213, value228, value234] <;> ring

def minor239 (a b c d Y T : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (5 * Y)
    | 0, 1 => (((-3) * T * b) + (3 * Y * a))
    | 0, 2 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 0, 3 => (((-2) * b) + (Y * c) + ((-5) * T * d))
    | 0, 4 => b
    | 1, 1 => ((-20) + ((-2) * T * a))
    | 1, 2 => (((-3) * T * b) + (3 * Y * a))
    | 1, 3 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 1, 4 => a
    | 2, 1 => (5 * Y)
    | 2, 2 => ((-20) + ((-2) * T * a))
    | 2, 3 => (((-3) * T * b) + (3 * Y * a))
    | 3, 2 => (5 * Y)
    | 3, 3 => ((-20) + ((-2) * T * a))
    | 3, 4 => 1
    | 4, 3 => (5 * Y)
    | _, _ => 0
def value239 (a b c d Y T : ℂ) : ℂ := (((-10000) * (Y^2)) + ((-250) * a * (Y^4)) + ((-2000) * T * a * (Y^2)) + ((-375) * T * b * (Y^3)) + ((-100) * (T^2) * (Y^2) * (a^2)))

theorem determinant239 (a b c d Y T : ℂ) :
    (minor239 a b c d Y T).det = value239 a b c d Y T := by
  have hm0 : (minor239 a b c d Y T).submatrix Fin.succ (0 : Fin 5).succAbove =
      minor85 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor239 a b c d Y T).submatrix Fin.succ (1 : Fin 5).succAbove =
      minor217 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor239 a b c d Y T).submatrix Fin.succ (2 : Fin 5).succAbove =
      minor232 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor239 a b c d Y T).submatrix Fin.succ (3 : Fin 5).succAbove =
      minor238 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm4 : (minor239 a b c d Y T).submatrix Fin.succ (4 : Fin 5).succAbove =
      minor236 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (5 * Y) * ((minor239 a b c d Y T).submatrix Fin.succ (0 : Fin 5).succAbove).det + ((-1 : ℂ)^1 * (((-3) * T * b) + (3 * Y * a)) * ((minor239 a b c d Y T).submatrix Fin.succ (1 : Fin 5).succAbove).det + ((-1 : ℂ)^2 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor239 a b c d Y T).submatrix Fin.succ (2 : Fin 5).succAbove).det + ((-1 : ℂ)^3 * (((-2) * b) + (Y * c) + ((-5) * T * d)) * ((minor239 a b c d Y T).submatrix Fin.succ (3 : Fin 5).succAbove).det + ((-1 : ℂ)^4 * b * ((minor239 a b c d Y T).submatrix Fin.succ (4 : Fin 5).succAbove).det + (0))))) = value239 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant85, hm1, determinant217, hm2, determinant232, hm3, determinant238, hm4, determinant236]
  dsimp only [value239, value85, value217, value232, value238, value236] <;> ring

end Mordell.Determinants
