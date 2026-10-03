import Mordell.Determinants.Part12

set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Mordell.Determinants

def minor195 (a b c d Y T : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => match i.val, j.val with
    | 1, 1 => 1
    | _, _ => 0
def value195 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant195 (a b c d Y T : ℂ) :
    (minor195 a b c d Y T).det = value195 a b c d Y T := by
  rw [show value195 a b c d Y T = 0 by rfl]
  apply Matrix.det_eq_zero_of_row_eq_zero 0
  intro j
  fin_cases j <;> rfl

def minor196 (a b c d Y T : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => match i.val, j.val with
    | _, _ => 0
def value196 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant196 (a b c d Y T : ℂ) :
    (minor196 a b c d Y T).det = value196 a b c d Y T := by
  rw [show value196 a b c d Y T = 0 by rfl]
  apply Matrix.det_eq_zero_of_row_eq_zero 0
  intro j
  fin_cases j <;> rfl

def minor197 (a b c d Y T : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 1 => 1
    | 0, 2 => a
    | 2, 2 => 1
    | _, _ => 0
def value197 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant197 (a b c d Y T : ℂ) :
    (minor197 a b c d Y T).det = value197 a b c d Y T := by
  have hm1 : (minor197 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove =
      minor195 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor197 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove =
      minor196 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * 0 * ((minor197 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove).det + ((-1 : ℂ)^1 * 1 * ((minor197 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove).det + ((-1 : ℂ)^2 * a * ((minor197 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove).det + (0))) = value197 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm1, determinant195, hm2, determinant196]
  dsimp only [value197, value195, value196] <;> ring

def minor198 (a b c d Y T : ℂ) : Matrix (Fin 1) (Fin 1) ℂ :=
  fun i j => match i.val, j.val with
    | _, _ => 0
def value198 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant198 (a b c d Y T : ℂ) :
    (minor198 a b c d Y T).det = value198 a b c d Y T := by
  simp [Matrix.det_unique, minor198, value198]

def minor199 (a b c d Y T : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 1 => 1
    | _, _ => 0
def value199 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant199 (a b c d Y T : ℂ) :
    (minor199 a b c d Y T).det = value199 a b c d Y T := by
  have hm1 : (minor199 a b c d Y T).submatrix Fin.succ (1 : Fin 2).succAbove =
      minor198 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * 0 * ((minor199 a b c d Y T).submatrix Fin.succ (0 : Fin 2).succAbove).det + ((-1 : ℂ)^1 * 1 * ((minor199 a b c d Y T).submatrix Fin.succ (1 : Fin 2).succAbove).det + (0)) = value199 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm1, determinant198]
  dsimp only [value199, value198] <;> ring

def minor200 (a b c d Y T : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 1 => 1
    | 1, 2 => 1
    | _, _ => 0
def value200 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant200 (a b c d Y T : ℂ) :
    (minor200 a b c d Y T).det = value200 a b c d Y T := by
  have hm1 : (minor200 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove =
      minor199 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * 0 * ((minor200 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove).det + ((-1 : ℂ)^1 * 1 * ((minor200 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove).det + ((-1 : ℂ)^2 * 0 * ((minor200 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove).det + (0))) = value200 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm1, determinant199]
  dsimp only [value200, value199] <;> ring

def minor201 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 2 => a
    | 0, 3 => b
    | 1, 1 => 1
    | 1, 3 => a
    | 2, 2 => 1
    | 3, 3 => 1
    | _, _ => 0
def value201 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant201 (a b c d Y T : ℂ) :
    (minor201 a b c d Y T).det = value201 a b c d Y T := by
  have hm2 : (minor201 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove =
      minor197 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor201 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove =
      minor200 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * 0 * ((minor201 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * 0 * ((minor201 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * a * ((minor201 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * b * ((minor201 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value201 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm2, determinant197, hm3, determinant200]
  dsimp only [value201, value197, value200] <;> ring

def minor202 (a b c d Y T : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 2 => a
    | 1, 1 => 1
    | 2, 2 => 1
    | _, _ => 0
def value202 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant202 (a b c d Y T : ℂ) :
    (minor202 a b c d Y T).det = value202 a b c d Y T := by
  have hm2 : (minor202 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove =
      minor199 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * 0 * ((minor202 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove).det + ((-1 : ℂ)^1 * 0 * ((minor202 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove).det + ((-1 : ℂ)^2 * a * ((minor202 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove).det + (0))) = value202 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm2, determinant199]
  dsimp only [value202, value199] <;> ring

def minor203 (a b c d Y T : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 1 => ((-20) + ((-2) * T * a))
    | 1, 1 => (5 * Y)
    | _, _ => 0
def value203 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant203 (a b c d Y T : ℂ) :
    (minor203 a b c d Y T).det = value203 a b c d Y T := by
  have hm1 : (minor203 a b c d Y T).submatrix Fin.succ (1 : Fin 2).succAbove =
      minor198 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * 0 * ((minor203 a b c d Y T).submatrix Fin.succ (0 : Fin 2).succAbove).det + ((-1 : ℂ)^1 * ((-20) + ((-2) * T * a)) * ((minor203 a b c d Y T).submatrix Fin.succ (1 : Fin 2).succAbove).det + (0)) = value203 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm1, determinant198]
  dsimp only [value203, value198] <;> ring

def minor204 (a b c d Y T : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 1 => (((-3) * T * b) + (3 * Y * a))
    | 0, 2 => a
    | 1, 1 => ((-20) + ((-2) * T * a))
    | 2, 1 => (5 * Y)
    | 2, 2 => 1
    | _, _ => 0
def value204 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant204 (a b c d Y T : ℂ) :
    (minor204 a b c d Y T).det = value204 a b c d Y T := by
  have hm1 : (minor204 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove =
      minor195 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor204 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove =
      minor203 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * 0 * ((minor204 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove).det + ((-1 : ℂ)^1 * (((-3) * T * b) + (3 * Y * a)) * ((minor204 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove).det + ((-1 : ℂ)^2 * a * ((minor204 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove).det + (0))) = value204 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm1, determinant195, hm2, determinant203]
  dsimp only [value204, value195, value203] <;> ring

def minor205 (a b c d Y T : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 1 => (((-3) * T * b) + (3 * Y * a))
    | 1, 1 => ((-20) + ((-2) * T * a))
    | 1, 2 => 1
    | 2, 1 => (5 * Y)
    | _, _ => 0
def value205 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant205 (a b c d Y T : ℂ) :
    (minor205 a b c d Y T).det = value205 a b c d Y T := by
  have hm1 : (minor205 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove =
      minor199 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * 0 * ((minor205 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove).det + ((-1 : ℂ)^1 * (((-3) * T * b) + (3 * Y * a)) * ((minor205 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove).det + ((-1 : ℂ)^2 * 0 * ((minor205 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove).det + (0))) = value205 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm1, determinant199]
  dsimp only [value205, value199] <;> ring

def minor206 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
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
def value206 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant206 (a b c d Y T : ℂ) :
    (minor206 a b c d Y T).det = value206 a b c d Y T := by
  have hm1 : (minor206 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove =
      minor202 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor206 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove =
      minor204 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor206 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove =
      minor205 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * 0 * ((minor206 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor206 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * a * ((minor206 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * b * ((minor206 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value206 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm1, determinant202, hm2, determinant204, hm3, determinant205]
  dsimp only [value206, value202, value204, value205] <;> ring

def minor207 (a b c d Y T : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 1 => (((-3) * T * b) + (3 * Y * a))
    | 0, 2 => 1
    | 1, 1 => ((-20) + ((-2) * T * a))
    | 2, 1 => (5 * Y)
    | _, _ => 0
def value207 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant207 (a b c d Y T : ℂ) :
    (minor207 a b c d Y T).det = value207 a b c d Y T := by
  have hm1 : (minor207 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove =
      minor196 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor207 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove =
      minor203 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * 0 * ((minor207 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove).det + ((-1 : ℂ)^1 * (((-3) * T * b) + (3 * Y * a)) * ((minor207 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove).det + ((-1 : ℂ)^2 * 1 * ((minor207 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove).det + (0))) = value207 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm1, determinant196, hm2, determinant203]
  dsimp only [value207, value196, value203] <;> ring

def minor208 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 1 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 0, 3 => b
    | 1, 1 => (((-3) * T * b) + (3 * Y * a))
    | 1, 2 => 1
    | 1, 3 => a
    | 2, 1 => ((-20) + ((-2) * T * a))
    | 3, 1 => (5 * Y)
    | 3, 3 => 1
    | _, _ => 0
def value208 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant208 (a b c d Y T : ℂ) :
    (minor208 a b c d Y T).det = value208 a b c d Y T := by
  have hm1 : (minor208 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove =
      minor197 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor208 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove =
      minor207 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * 0 * ((minor208 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor208 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * 0 * ((minor208 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * b * ((minor208 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value208 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm1, determinant197, hm3, determinant207]
  dsimp only [value208, value197, value207] <;> ring

def minor209 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 1 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 0, 3 => a
    | 1, 1 => (((-3) * T * b) + (3 * Y * a))
    | 1, 2 => 1
    | 2, 1 => ((-20) + ((-2) * T * a))
    | 2, 3 => 1
    | 3, 1 => (5 * Y)
    | _, _ => 0
def value209 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant209 (a b c d Y T : ℂ) :
    (minor209 a b c d Y T).det = value209 a b c d Y T := by
  have hm1 : (minor209 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove =
      minor200 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor209 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove =
      minor207 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * 0 * ((minor209 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor209 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * 0 * ((minor209 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * a * ((minor209 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value209 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm1, determinant200, hm3, determinant207]
  dsimp only [value209, value200, value207] <;> ring

end Mordell.Determinants
