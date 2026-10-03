import Mordell.Determinants.Part11

set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Mordell.Determinants

def minor180 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (5 * Y)
    | 0, 1 => (((-3) * T * b) + (3 * Y * a))
    | 0, 2 => 1
    | 0, 3 => b
    | 1, 1 => ((-20) + ((-2) * T * a))
    | 1, 3 => a
    | 2, 1 => (5 * Y)
    | 3, 3 => 1
    | _, _ => 0
def value180 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant180 (a b c d Y T : ℂ) :
    (minor180 a b c d Y T).det = value180 a b c d Y T := by
  have hm0 : (minor180 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove =
      minor49 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor180 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove =
      minor172 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor180 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove =
      minor134 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor180 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove =
      minor179 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (5 * Y) * ((minor180 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * (((-3) * T * b) + (3 * Y * a)) * ((minor180 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * 1 * ((minor180 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * b * ((minor180 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value180 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant49, hm1, determinant172, hm2, determinant134, hm3, determinant179]
  dsimp only [value180, value49, value172, value134, value179] <;> ring

def minor181 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (5 * Y)
    | 0, 1 => (((-3) * T * b) + (3 * Y * a))
    | 0, 2 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 0, 3 => 1
    | 1, 1 => ((-20) + ((-2) * T * a))
    | 1, 2 => (((-3) * T * b) + (3 * Y * a))
    | 2, 1 => (5 * Y)
    | 2, 2 => ((-20) + ((-2) * T * a))
    | 3, 2 => (5 * Y)
    | _, _ => 0
def value181 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant181 (a b c d Y T : ℂ) :
    (minor181 a b c d Y T).det = value181 a b c d Y T := by
  have hm0 : (minor181 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove =
      minor52 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor181 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove =
      minor175 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor181 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove =
      minor179 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor181 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove =
      minor137 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (5 * Y) * ((minor181 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * (((-3) * T * b) + (3 * Y * a)) * ((minor181 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor181 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * 1 * ((minor181 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value181 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant52, hm1, determinant175, hm2, determinant179, hm3, determinant137]
  dsimp only [value181, value52, value175, value179, value137] <;> ring

def minor182 (a b c d Y T : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => ((-20) + ((-2) * T * a))
    | 0, 1 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 0, 2 => (((-2) * b) + (Y * c) + ((-5) * T * d))
    | 0, 4 => c
    | 1, 0 => (5 * Y)
    | 1, 1 => (((-3) * T * b) + (3 * Y * a))
    | 1, 2 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 1, 3 => 1
    | 1, 4 => b
    | 2, 1 => ((-20) + ((-2) * T * a))
    | 2, 2 => (((-3) * T * b) + (3 * Y * a))
    | 2, 4 => a
    | 3, 1 => (5 * Y)
    | 3, 2 => ((-20) + ((-2) * T * a))
    | 4, 2 => (5 * Y)
    | 4, 4 => 1
    | _, _ => 0
def value182 (a b c d Y T : ℂ) : ℂ := ((-8000) + ((-2400) * T * a) + ((-240) * (T^2) * (a^2)) + ((-200) * a * (Y^2)) + ((-8) * (T^3) * (a^3)) + ((-300) * T * Y * b) + ((-20) * T * (Y^2) * (a^2)) + ((-30) * Y * a * b * (T^2)))

theorem determinant182 (a b c d Y T : ℂ) :
    (minor182 a b c d Y T).det = value182 a b c d Y T := by
  have hm0 : (minor182 a b c d Y T).submatrix Fin.succ (0 : Fin 5).succAbove =
      minor53 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor182 a b c d Y T).submatrix Fin.succ (1 : Fin 5).succAbove =
      minor176 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor182 a b c d Y T).submatrix Fin.succ (2 : Fin 5).succAbove =
      minor180 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm4 : (minor182 a b c d Y T).submatrix Fin.succ (4 : Fin 5).succAbove =
      minor181 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * ((-20) + ((-2) * T * a)) * ((minor182 a b c d Y T).submatrix Fin.succ (0 : Fin 5).succAbove).det + ((-1 : ℂ)^1 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor182 a b c d Y T).submatrix Fin.succ (1 : Fin 5).succAbove).det + ((-1 : ℂ)^2 * (((-2) * b) + (Y * c) + ((-5) * T * d)) * ((minor182 a b c d Y T).submatrix Fin.succ (2 : Fin 5).succAbove).det + ((-1 : ℂ)^3 * 0 * ((minor182 a b c d Y T).submatrix Fin.succ (3 : Fin 5).succAbove).det + ((-1 : ℂ)^4 * c * ((minor182 a b c d Y T).submatrix Fin.succ (4 : Fin 5).succAbove).det + (0))))) = value182 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant53, hm1, determinant176, hm2, determinant180, hm4, determinant181]
  dsimp only [value182, value53, value176, value180, value181] <;> ring

def minor183 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (5 * Y)
    | 0, 1 => (((-3) * T * b) + (3 * Y * a))
    | 0, 2 => 1
    | 0, 3 => a
    | 1, 1 => ((-20) + ((-2) * T * a))
    | 2, 1 => (5 * Y)
    | 2, 3 => 1
    | _, _ => 0
def value183 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant183 (a b c d Y T : ℂ) :
    (minor183 a b c d Y T).det = value183 a b c d Y T := by
  have hm0 : (minor183 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove =
      minor50 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor183 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove =
      minor173 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor183 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove =
      minor135 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor183 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove =
      minor179 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (5 * Y) * ((minor183 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * (((-3) * T * b) + (3 * Y * a)) * ((minor183 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * 1 * ((minor183 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * a * ((minor183 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value183 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant50, hm1, determinant173, hm2, determinant135, hm3, determinant179]
  dsimp only [value183, value50, value173, value135, value179] <;> ring

def minor184 (a b c d Y T : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => ((-20) + ((-2) * T * a))
    | 0, 1 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 0, 2 => (((-2) * b) + (Y * c) + ((-5) * T * d))
    | 0, 4 => b
    | 1, 0 => (5 * Y)
    | 1, 1 => (((-3) * T * b) + (3 * Y * a))
    | 1, 2 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 1, 3 => 1
    | 1, 4 => a
    | 2, 1 => ((-20) + ((-2) * T * a))
    | 2, 2 => (((-3) * T * b) + (3 * Y * a))
    | 3, 1 => (5 * Y)
    | 3, 2 => ((-20) + ((-2) * T * a))
    | 3, 4 => 1
    | 4, 2 => (5 * Y)
    | _, _ => 0
def value184 (a b c d Y T : ℂ) : ℂ := (((-2000) * Y) + ((-400) * T * Y * a) + ((-20) * Y * (T^2) * (a^2)))

theorem determinant184 (a b c d Y T : ℂ) :
    (minor184 a b c d Y T).det = value184 a b c d Y T := by
  have hm0 : (minor184 a b c d Y T).submatrix Fin.succ (0 : Fin 5).succAbove =
      minor54 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor184 a b c d Y T).submatrix Fin.succ (1 : Fin 5).succAbove =
      minor177 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor184 a b c d Y T).submatrix Fin.succ (2 : Fin 5).succAbove =
      minor183 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm4 : (minor184 a b c d Y T).submatrix Fin.succ (4 : Fin 5).succAbove =
      minor181 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * ((-20) + ((-2) * T * a)) * ((minor184 a b c d Y T).submatrix Fin.succ (0 : Fin 5).succAbove).det + ((-1 : ℂ)^1 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor184 a b c d Y T).submatrix Fin.succ (1 : Fin 5).succAbove).det + ((-1 : ℂ)^2 * (((-2) * b) + (Y * c) + ((-5) * T * d)) * ((minor184 a b c d Y T).submatrix Fin.succ (2 : Fin 5).succAbove).det + ((-1 : ℂ)^3 * 0 * ((minor184 a b c d Y T).submatrix Fin.succ (3 : Fin 5).succAbove).det + ((-1 : ℂ)^4 * b * ((minor184 a b c d Y T).submatrix Fin.succ (4 : Fin 5).succAbove).det + (0))))) = value184 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant54, hm1, determinant177, hm2, determinant183, hm4, determinant181]
  dsimp only [value184, value54, value177, value183, value181] <;> ring

def minor185 (a b c d Y T : ℂ) : Matrix (Fin 6) (Fin 6) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (((-3) * T * b) + (3 * Y * a))
    | 0, 1 => (((-2) * b) + (Y * c) + ((-5) * T * d))
    | 0, 3 => a
    | 0, 4 => c
    | 0, 5 => d
    | 1, 0 => ((-20) + ((-2) * T * a))
    | 1, 1 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 1, 2 => (((-2) * b) + (Y * c) + ((-5) * T * d))
    | 1, 4 => b
    | 1, 5 => c
    | 2, 0 => (5 * Y)
    | 2, 1 => (((-3) * T * b) + (3 * Y * a))
    | 2, 2 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 2, 3 => 1
    | 2, 4 => a
    | 2, 5 => b
    | 3, 1 => ((-20) + ((-2) * T * a))
    | 3, 2 => (((-3) * T * b) + (3 * Y * a))
    | 3, 5 => a
    | 4, 1 => (5 * Y)
    | 4, 2 => ((-20) + ((-2) * T * a))
    | 4, 4 => 1
    | 5, 2 => (5 * Y)
    | 5, 5 => 1
    | _, _ => 0
def value185 (a b c d Y T : ℂ) : ℂ := (((-8000) * c) + (5600 * (a^2)) + (8 * (T^3) * (a^5)) + (104 * (Y^2) * (a^3)) + (216 * (T^2) * (a^4)) + (960 * T * (b^2)) + (1920 * T * (a^3)) + (2000 * Y * d) + ((-4000) * T * a * c) + ((-600) * b * d * (T^2)) + ((-560) * Y * a * b) + ((-560) * c * (T^2) * (a^2)) + ((-320) * a * c * (Y^2)) + ((-24) * c * (T^3) * (a^3)) + (8 * T * (Y^2) * (a^4)) + (12 * b * (Y^3) * (a^2)) + (27 * Y * (T^2) * (b^3)) + (30 * (T^3) * (a^2) * (b^2)) + (36 * c * (T^3) * (b^2)) + (450 * a * (T^2) * (b^2)) + ((-480) * T * Y * b * c) + ((-60) * a * b * d * (T^3)) + ((-20) * Y * d * (T^2) * (a^2)) + ((-16) * T * c * (Y^2) * (a^2)) + (20 * Y * b * (T^2) * (a^3)) + (36 * T * a * (Y^2) * (b^2)) + (216 * T * Y * b * (a^2)))

theorem determinant185 (a b c d Y T : ℂ) :
    (minor185 a b c d Y T).det = value185 a b c d Y T := by
  have hm0 : (minor185 a b c d Y T).submatrix Fin.succ (0 : Fin 6).succAbove =
      minor55 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor185 a b c d Y T).submatrix Fin.succ (1 : Fin 6).succAbove =
      minor178 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor185 a b c d Y T).submatrix Fin.succ (3 : Fin 6).succAbove =
      minor140 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm4 : (minor185 a b c d Y T).submatrix Fin.succ (4 : Fin 6).succAbove =
      minor182 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm5 : (minor185 a b c d Y T).submatrix Fin.succ (5 : Fin 6).succAbove =
      minor184 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (((-3) * T * b) + (3 * Y * a)) * ((minor185 a b c d Y T).submatrix Fin.succ (0 : Fin 6).succAbove).det + ((-1 : ℂ)^1 * (((-2) * b) + (Y * c) + ((-5) * T * d)) * ((minor185 a b c d Y T).submatrix Fin.succ (1 : Fin 6).succAbove).det + ((-1 : ℂ)^2 * 0 * ((minor185 a b c d Y T).submatrix Fin.succ (2 : Fin 6).succAbove).det + ((-1 : ℂ)^3 * a * ((minor185 a b c d Y T).submatrix Fin.succ (3 : Fin 6).succAbove).det + ((-1 : ℂ)^4 * c * ((minor185 a b c d Y T).submatrix Fin.succ (4 : Fin 6).succAbove).det + ((-1 : ℂ)^5 * d * ((minor185 a b c d Y T).submatrix Fin.succ (5 : Fin 6).succAbove).det + (0)))))) = value185 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant55, hm1, determinant178, hm3, determinant140, hm4, determinant182, hm5, determinant184]
  dsimp only [value185, value55, value178, value140, value182, value184] <;> ring

def minor186 (a b c d Y T : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 1 => (5 * Y)
    | _, _ => 0
def value186 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant186 (a b c d Y T : ℂ) :
    (minor186 a b c d Y T).det = value186 a b c d Y T := by
  have hm1 : (minor186 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove =
      minor171 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * 0 * ((minor186 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove).det + ((-1 : ℂ)^1 * (5 * Y) * ((minor186 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove).det + ((-1 : ℂ)^2 * 0 * ((minor186 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove).det + (0))) = value186 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm1, determinant171]
  dsimp only [value186, value171] <;> ring

def minor187 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (5 * Y)
    | 0, 1 => ((-20) + ((-2) * T * a))
    | 0, 2 => 1
    | 0, 3 => b
    | 1, 1 => (5 * Y)
    | 1, 3 => a
    | 3, 3 => 1
    | _, _ => 0
def value187 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant187 (a b c d Y T : ℂ) :
    (minor187 a b c d Y T).det = value187 a b c d Y T := by
  have hm0 : (minor187 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove =
      minor95 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor187 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove =
      minor172 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor187 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove =
      minor149 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor187 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove =
      minor186 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (5 * Y) * ((minor187 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * ((-20) + ((-2) * T * a)) * ((minor187 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * 1 * ((minor187 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * b * ((minor187 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value187 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant95, hm1, determinant172, hm2, determinant149, hm3, determinant186]
  dsimp only [value187, value95, value172, value149, value186] <;> ring

def minor188 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (5 * Y)
    | 0, 1 => ((-20) + ((-2) * T * a))
    | 0, 2 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 0, 3 => 1
    | 1, 1 => (5 * Y)
    | 1, 2 => (((-3) * T * b) + (3 * Y * a))
    | 2, 2 => ((-20) + ((-2) * T * a))
    | 3, 2 => (5 * Y)
    | _, _ => 0
def value188 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant188 (a b c d Y T : ℂ) :
    (minor188 a b c d Y T).det = value188 a b c d Y T := by
  have hm0 : (minor188 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove =
      minor98 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor188 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove =
      minor175 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor188 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove =
      minor186 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor188 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove =
      minor152 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (5 * Y) * ((minor188 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * ((-20) + ((-2) * T * a)) * ((minor188 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor188 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * 1 * ((minor188 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value188 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant98, hm1, determinant175, hm2, determinant186, hm3, determinant152]
  dsimp only [value188, value98, value175, value186, value152] <;> ring

def minor189 (a b c d Y T : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => ((-20) + ((-2) * T * a))
    | 0, 1 => (((-3) * T * b) + (3 * Y * a))
    | 0, 2 => (((-2) * b) + (Y * c) + ((-5) * T * d))
    | 0, 4 => c
    | 1, 0 => (5 * Y)
    | 1, 1 => ((-20) + ((-2) * T * a))
    | 1, 2 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 1, 3 => 1
    | 1, 4 => b
    | 2, 1 => (5 * Y)
    | 2, 2 => (((-3) * T * b) + (3 * Y * a))
    | 2, 4 => a
    | 3, 2 => ((-20) + ((-2) * T * a))
    | 4, 2 => (5 * Y)
    | 4, 4 => 1
    | _, _ => 0
def value189 (a b c d Y T : ℂ) : ℂ := ((2000 * Y) + (20 * Y * (T^2) * (a^2)) + (400 * T * Y * a))

theorem determinant189 (a b c d Y T : ℂ) :
    (minor189 a b c d Y T).det = value189 a b c d Y T := by
  have hm0 : (minor189 a b c d Y T).submatrix Fin.succ (0 : Fin 5).succAbove =
      minor99 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor189 a b c d Y T).submatrix Fin.succ (1 : Fin 5).succAbove =
      minor176 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor189 a b c d Y T).submatrix Fin.succ (2 : Fin 5).succAbove =
      minor187 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm4 : (minor189 a b c d Y T).submatrix Fin.succ (4 : Fin 5).succAbove =
      minor188 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * ((-20) + ((-2) * T * a)) * ((minor189 a b c d Y T).submatrix Fin.succ (0 : Fin 5).succAbove).det + ((-1 : ℂ)^1 * (((-3) * T * b) + (3 * Y * a)) * ((minor189 a b c d Y T).submatrix Fin.succ (1 : Fin 5).succAbove).det + ((-1 : ℂ)^2 * (((-2) * b) + (Y * c) + ((-5) * T * d)) * ((minor189 a b c d Y T).submatrix Fin.succ (2 : Fin 5).succAbove).det + ((-1 : ℂ)^3 * 0 * ((minor189 a b c d Y T).submatrix Fin.succ (3 : Fin 5).succAbove).det + ((-1 : ℂ)^4 * c * ((minor189 a b c d Y T).submatrix Fin.succ (4 : Fin 5).succAbove).det + (0))))) = value189 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant99, hm1, determinant176, hm2, determinant187, hm4, determinant188]
  dsimp only [value189, value99, value176, value187, value188] <;> ring

def minor190 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (5 * Y)
    | 0, 1 => ((-20) + ((-2) * T * a))
    | 0, 2 => (((-3) * T * b) + (3 * Y * a))
    | 0, 3 => 1
    | 1, 1 => (5 * Y)
    | 1, 2 => ((-20) + ((-2) * T * a))
    | 2, 2 => (5 * Y)
    | _, _ => 0
def value190 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant190 (a b c d Y T : ℂ) :
    (minor190 a b c d Y T).det = value190 a b c d Y T := by
  have hm0 : (minor190 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove =
      minor102 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor190 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove =
      minor179 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor190 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove =
      minor186 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor190 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove =
      minor156 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (5 * Y) * ((minor190 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * ((-20) + ((-2) * T * a)) * ((minor190 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * (((-3) * T * b) + (3 * Y * a)) * ((minor190 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * 1 * ((minor190 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value190 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant102, hm1, determinant179, hm2, determinant186, hm3, determinant156]
  dsimp only [value190, value102, value179, value186, value156] <;> ring

def minor191 (a b c d Y T : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => ((-20) + ((-2) * T * a))
    | 0, 1 => (((-3) * T * b) + (3 * Y * a))
    | 0, 2 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 0, 3 => (((-2) * b) + (Y * c) + ((-5) * T * d))
    | 1, 0 => (5 * Y)
    | 1, 1 => ((-20) + ((-2) * T * a))
    | 1, 2 => (((-3) * T * b) + (3 * Y * a))
    | 1, 3 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 1, 4 => 1
    | 2, 1 => (5 * Y)
    | 2, 2 => ((-20) + ((-2) * T * a))
    | 2, 3 => (((-3) * T * b) + (3 * Y * a))
    | 3, 2 => (5 * Y)
    | 3, 3 => ((-20) + ((-2) * T * a))
    | 4, 3 => (5 * Y)
    | _, _ => 0
def value191 (a b c d Y T : ℂ) : ℂ := ((2500 * (Y^3)) + (250 * T * a * (Y^3)))

theorem determinant191 (a b c d Y T : ℂ) :
    (minor191 a b c d Y T).det = value191 a b c d Y T := by
  have hm0 : (minor191 a b c d Y T).submatrix Fin.succ (0 : Fin 5).succAbove =
      minor104 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor191 a b c d Y T).submatrix Fin.succ (1 : Fin 5).succAbove =
      minor181 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor191 a b c d Y T).submatrix Fin.succ (2 : Fin 5).succAbove =
      minor188 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor191 a b c d Y T).submatrix Fin.succ (3 : Fin 5).succAbove =
      minor190 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * ((-20) + ((-2) * T * a)) * ((minor191 a b c d Y T).submatrix Fin.succ (0 : Fin 5).succAbove).det + ((-1 : ℂ)^1 * (((-3) * T * b) + (3 * Y * a)) * ((minor191 a b c d Y T).submatrix Fin.succ (1 : Fin 5).succAbove).det + ((-1 : ℂ)^2 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor191 a b c d Y T).submatrix Fin.succ (2 : Fin 5).succAbove).det + ((-1 : ℂ)^3 * (((-2) * b) + (Y * c) + ((-5) * T * d)) * ((minor191 a b c d Y T).submatrix Fin.succ (3 : Fin 5).succAbove).det + ((-1 : ℂ)^4 * 0 * ((minor191 a b c d Y T).submatrix Fin.succ (4 : Fin 5).succAbove).det + (0))))) = value191 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant104, hm1, determinant181, hm2, determinant188, hm3, determinant190]
  dsimp only [value191, value104, value181, value188, value190] <;> ring

def minor192 (a b c d Y T : ℂ) : Matrix (Fin 6) (Fin 6) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (((-3) * T * b) + (3 * Y * a))
    | 0, 1 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 0, 2 => (((-2) * b) + (Y * c) + ((-5) * T * d))
    | 0, 4 => a
    | 0, 5 => d
    | 1, 0 => ((-20) + ((-2) * T * a))
    | 1, 1 => (((-3) * T * b) + (3 * Y * a))
    | 1, 2 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 1, 3 => (((-2) * b) + (Y * c) + ((-5) * T * d))
    | 1, 5 => c
    | 2, 0 => (5 * Y)
    | 2, 1 => ((-20) + ((-2) * T * a))
    | 2, 2 => (((-3) * T * b) + (3 * Y * a))
    | 2, 3 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 2, 4 => 1
    | 2, 5 => b
    | 3, 1 => (5 * Y)
    | 3, 2 => ((-20) + ((-2) * T * a))
    | 3, 3 => (((-3) * T * b) + (3 * Y * a))
    | 3, 5 => a
    | 4, 2 => (5 * Y)
    | 4, 3 => ((-20) + ((-2) * T * a))
    | 5, 3 => (5 * Y)
    | 5, 5 => 1
    | _, _ => 0
def value192 (a b c d Y T : ℂ) : ℂ := ((112000 * a) + ((-32000) * T * c) + ((-2500) * d * (Y^3)) + ((-1400) * (Y^2) * (a^2)) + ((-60) * (Y^4) * (a^3)) + (16 * (T^4) * (a^5)) + (592 * (T^3) * (a^4)) + (2000 * c * (Y^2)) + (3600 * (T^2) * (b^2)) + (8160 * (T^2) * (a^3)) + (12000 * Y * b) + (49600 * T * (a^2)) + ((-10000) * T * Y * d) + ((-9600) * a * c * (T^2)) + ((-960) * c * (T^3) * (a^2)) + ((-580) * T * (Y^2) * (a^3)) + ((-44) * (T^2) * (Y^2) * (a^4)) + ((-32) * c * (T^4) * (a^3)) + (36 * (T^4) * (a^2) * (b^2)) + (135 * Y * (T^3) * (b^3)) + (150 * T * (Y^2) * (b^2)) + (200 * a * c * (Y^4)) + (720 * a * (T^3) * (b^2)) + (1600 * a * b * (Y^3)) + ((-2000) * Y * a * d * (T^2)) + ((-100) * Y * d * (T^3) * (a^2)) + (30 * T * b * (Y^3) * (a^2)) + (45 * a * (T^2) * (Y^2) * (b^2)) + (124 * Y * b * (T^3) * (a^3)) + (220 * c * (T^2) * (Y^2) * (a^2)) + (300 * T * b * c * (Y^3)) + (375 * b * d * (T^2) * (Y^2)) + (2400 * T * a * c * (Y^2)) + (2600 * Y * b * (T^2) * (a^2)) + (14800 * T * Y * a * b))

theorem determinant192 (a b c d Y T : ℂ) :
    (minor192 a b c d Y T).det = value192 a b c d Y T := by
  have hm0 : (minor192 a b c d Y T).submatrix Fin.succ (0 : Fin 6).succAbove =
      minor105 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor192 a b c d Y T).submatrix Fin.succ (1 : Fin 6).succAbove =
      minor182 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor192 a b c d Y T).submatrix Fin.succ (2 : Fin 6).succAbove =
      minor189 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm4 : (minor192 a b c d Y T).submatrix Fin.succ (4 : Fin 6).succAbove =
      minor159 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm5 : (minor192 a b c d Y T).submatrix Fin.succ (5 : Fin 6).succAbove =
      minor191 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (((-3) * T * b) + (3 * Y * a)) * ((minor192 a b c d Y T).submatrix Fin.succ (0 : Fin 6).succAbove).det + ((-1 : ℂ)^1 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor192 a b c d Y T).submatrix Fin.succ (1 : Fin 6).succAbove).det + ((-1 : ℂ)^2 * (((-2) * b) + (Y * c) + ((-5) * T * d)) * ((minor192 a b c d Y T).submatrix Fin.succ (2 : Fin 6).succAbove).det + ((-1 : ℂ)^3 * 0 * ((minor192 a b c d Y T).submatrix Fin.succ (3 : Fin 6).succAbove).det + ((-1 : ℂ)^4 * a * ((minor192 a b c d Y T).submatrix Fin.succ (4 : Fin 6).succAbove).det + ((-1 : ℂ)^5 * d * ((minor192 a b c d Y T).submatrix Fin.succ (5 : Fin 6).succAbove).det + (0)))))) = value192 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant105, hm1, determinant182, hm2, determinant189, hm4, determinant159, hm5, determinant191]
  dsimp only [value192, value105, value182, value189, value159, value191] <;> ring

def minor193 (a b c d Y T : ℂ) : Matrix (Fin 7) (Fin 7) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 0, 1 => (((-2) * b) + (Y * c) + ((-5) * T * d))
    | 0, 4 => b
    | 0, 5 => d
    | 1, 0 => (((-3) * T * b) + (3 * Y * a))
    | 1, 1 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 1, 2 => (((-2) * b) + (Y * c) + ((-5) * T * d))
    | 1, 4 => a
    | 1, 5 => c
    | 1, 6 => d
    | 2, 0 => ((-20) + ((-2) * T * a))
    | 2, 1 => (((-3) * T * b) + (3 * Y * a))
    | 2, 2 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 2, 3 => (((-2) * b) + (Y * c) + ((-5) * T * d))
    | 2, 5 => b
    | 2, 6 => c
    | 3, 0 => (5 * Y)
    | 3, 1 => ((-20) + ((-2) * T * a))
    | 3, 2 => (((-3) * T * b) + (3 * Y * a))
    | 3, 3 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 3, 4 => 1
    | 3, 5 => a
    | 3, 6 => b
    | 4, 1 => (5 * Y)
    | 4, 2 => ((-20) + ((-2) * T * a))
    | 4, 3 => (((-3) * T * b) + (3 * Y * a))
    | 4, 6 => a
    | 5, 2 => (5 * Y)
    | 5, 3 => ((-20) + ((-2) * T * a))
    | 5, 5 => 1
    | 6, 3 => (5 * Y)
    | 6, 6 => 1
    | _, _ => 0
def value193 (a b c d Y T : ℂ) : ℂ := (((-112000) * a * d) + ((-17280) * T * (b^3)) + ((-180) * (Y^2) * (b^3)) + (72 * (Y^3) * (a^5)) + (81 * (T^4) * (b^5)) + (2500 * (Y^3) * (d^2)) + (3528 * Y * (a^4)) + (7840 * b * (a^2)) + (8000 * Y * (c^2)) + (144000 * b * c) + ((-48000) * Y * b * d) + ((-30000) * T * d * (a^2)) + ((-15920) * Y * c * (a^2)) + ((-8000) * T * c * d) + ((-4872) * a * (T^2) * (b^3)) + ((-4000) * c * d * (Y^2)) + ((-3000) * b * (T^3) * (d^2)) + ((-2016) * c * (T^3) * (b^3)) + ((-1422) * Y * (T^2) * (b^4)) + ((-624) * b * (T^2) * (a^4)) + ((-600) * d * (T^2) * (a^3)) + ((-504) * T * b * (a^3)) + ((-488) * c * (Y^3) * (a^3)) + ((-378) * (T^3) * (a^2) * (b^3)) + ((-225) * d * (Y^4) * (b^2)) + ((-192) * b * (T^4) * (c^3)) + ((-81) * T * (Y^3) * (b^4)) + ((-56) * b * (T^3) * (a^5)) + (12 * b * (Y^4) * (a^4)) + (12 * (T^4) * (a^3) * (b^3)) + (24 * d * (T^4) * (a^5)) + (28 * b * (Y^2) * (a^3)) + (60 * d * (Y^4) * (a^3)) + (72 * Y * (T^2) * (a^6)) + (81 * a * (Y^4) * (b^3)) + (240 * b * (Y^4) * (c^2)) + (320 * T * (Y^3) * (c^3)) + (368 * d * (T^3) * (a^4)) + (454 * (Y^3) * (a^2) * (b^2)) + (660 * c * (Y^3) * (b^2)) + (800 * a * (Y^3) * (c^2)) + (1008 * T * Y * (a^5)) + (1600 * d * (T^3) * (c^2)) + (2300 * d * (Y^2) * (a^2)) + (2880 * Y * (T^2) * (c^3)) + (5440 * b * (T^2) * (c^2)) + (12000 * d * (T^2) * (b^2)) + (20000 * T * Y * (d^2)) + (20040 * Y * a * (b^2)) + ((-13600) * a * c * d * (T^2)) + ((-4296) * T * Y * c * (a^3)) + ((-2960) * c * d * (T^3) * (a^2)) + ((-2850) * T * d * (Y^2) * (b^2)) + ((-2600) * a * b * d * (Y^3)) + ((-1872) * Y * (T^2) * (a^2) * (c^2)) + ((-1520) * a * b * c * (Y^2)) + ((-324) * Y * (T^3) * (b^2) * (c^2)) + ((-324) * a * c * (T^4) * (b^3)) + ((-300) * a * b * (T^4) * (d^2)) + ((-280) * Y * (T^3) * (a^3) * (c^2)) + ((-240) * T * (Y^3) * (a^2) * (c^2)) + ((-200) * a * c * d * (Y^4)) + ((-168) * c * d * (T^4) * (a^3)) + ((-162) * Y * a * (T^3) * (b^4)) + ((-124) * b * c * (Y^4) * (a^2)) + ((-63) * c * (T^2) * (Y^2) * (b^3)) + ((-32) * b * c * (T^4) * (a^4)) + ((-24) * Y * (T^3) * (a^4) * (b^2)) + ((-12) * T * (Y^3) * (a^3) * (b^2)) + (12 * b * (T^2) * (Y^2) * (a^5)) + (40 * T * c * (Y^3) * (a^4)) + (40 * Y * c * (T^3) * (a^5)) + (81 * (T^2) * (Y^2) * (a^2) * (b^3)) + (84 * d * (T^2) * (Y^2) * (a^4)) + (160 * a * d * (T^4) * (c^2)) + (184 * T * b * (Y^2) * (a^4)) + (234 * d * (T^4) * (a^2) * (b^2)) + (240 * b * (T^4) * (a^2) * (c^2)) + (248 * b * c * (T^3) * (a^3)) + (254 * Y * (T^2) * (a^3) * (b^2)) + (360 * Y * d * (T^3) * (b^3)) + (360 * c * d * (T^4) * (b^2)) + (400 * d * (T^2) * (Y^2) * (c^2)) + (480 * Y * a * (T^3) * (c^3)) + (500 * Y * c * (T^3) * (d^2)) + (800 * T * d * (Y^2) * (a^3)) + (1194 * T * a * (Y^2) * (b^3)) + (1440 * T * Y * a * (c^2)) + (2080 * a * b * (T^3) * (c^2)) + (2750 * Y * a * (T^2) * (d^2)) + (3520 * T * b * (Y^2) * (c^2)) + (4080 * a * d * (T^3) * (b^2)) + (6428 * T * Y * (a^2) * (b^2)) + (9136 * b * c * (T^2) * (a^2)) + (17520 * T * Y * c * (b^2)) + (61920 * T * a * b * c) + ((-38200) * T * Y * a * b * d) + ((-5020) * Y * b * d * (T^2) * (a^2)) + ((-2800) * T * a * c * d * (Y^2)) + ((-2200) * Y * b * c * d * (T^2)) + ((-1744) * T * b * c * (Y^2) * (a^2)) + ((-480) * c * d * (T^2) * (Y^2) * (a^2)) + ((-300) * T * b * c * d * (Y^3)) + ((-144) * Y * b * d * (T^3) * (a^3)) + ((-135) * a * d * (T^2) * (Y^2) * (b^2)) + ((-128) * b * c * (T^2) * (Y^2) * (a^3)) + ((-120) * T * b * d * (Y^3) * (a^2)) + (354 * T * a * c * (Y^3) * (b^2)) + (416 * a * b * (T^2) * (Y^2) * (c^2)) + (486 * Y * c * (T^3) * (a^2) * (b^2)) + (5782 * Y * a * c * (T^2) * (b^2)) + ((-380) * Y * a * b * c * d * (T^3)))

theorem determinant193 (a b c d Y T : ℂ) :
    (minor193 a b c d Y T).det = value193 a b c d Y T := by
  have hm0 : (minor193 a b c d Y T).submatrix Fin.succ (0 : Fin 7).succAbove =
      minor108 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor193 a b c d Y T).submatrix Fin.succ (1 : Fin 7).succAbove =
      minor185 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm4 : (minor193 a b c d Y T).submatrix Fin.succ (4 : Fin 7).succAbove =
      minor162 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm5 : (minor193 a b c d Y T).submatrix Fin.succ (5 : Fin 7).succAbove =
      minor192 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor193 a b c d Y T).submatrix Fin.succ (0 : Fin 7).succAbove).det + ((-1 : ℂ)^1 * (((-2) * b) + (Y * c) + ((-5) * T * d)) * ((minor193 a b c d Y T).submatrix Fin.succ (1 : Fin 7).succAbove).det + ((-1 : ℂ)^2 * 0 * ((minor193 a b c d Y T).submatrix Fin.succ (2 : Fin 7).succAbove).det + ((-1 : ℂ)^3 * 0 * ((minor193 a b c d Y T).submatrix Fin.succ (3 : Fin 7).succAbove).det + ((-1 : ℂ)^4 * b * ((minor193 a b c d Y T).submatrix Fin.succ (4 : Fin 7).succAbove).det + ((-1 : ℂ)^5 * d * ((minor193 a b c d Y T).submatrix Fin.succ (5 : Fin 7).succAbove).det + ((-1 : ℂ)^6 * 0 * ((minor193 a b c d Y T).submatrix Fin.succ (6 : Fin 7).succAbove).det + (0))))))) = value193 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant108, hm1, determinant185, hm4, determinant162, hm5, determinant192]
  dsimp only [value193, value108, value185, value162, value192] <;> ring

def minor194 (a b c d Y T : ℂ) : Matrix (Fin 8) (Fin 8) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (((-2) * b) + (Y * c) + ((-5) * T * d))
    | 0, 4 => c
    | 0, 5 => d
    | 1, 0 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 1, 1 => (((-2) * b) + (Y * c) + ((-5) * T * d))
    | 1, 4 => b
    | 1, 5 => c
    | 1, 6 => d
    | 2, 0 => (((-3) * T * b) + (3 * Y * a))
    | 2, 1 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 2, 2 => (((-2) * b) + (Y * c) + ((-5) * T * d))
    | 2, 4 => a
    | 2, 5 => b
    | 2, 6 => c
    | 2, 7 => d
    | 3, 0 => ((-20) + ((-2) * T * a))
    | 3, 1 => (((-3) * T * b) + (3 * Y * a))
    | 3, 2 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 3, 3 => (((-2) * b) + (Y * c) + ((-5) * T * d))
    | 3, 5 => a
    | 3, 6 => b
    | 3, 7 => c
    | 4, 0 => (5 * Y)
    | 4, 1 => ((-20) + ((-2) * T * a))
    | 4, 2 => (((-3) * T * b) + (3 * Y * a))
    | 4, 3 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 4, 4 => 1
    | 4, 6 => a
    | 4, 7 => b
    | 5, 1 => (5 * Y)
    | 5, 2 => ((-20) + ((-2) * T * a))
    | 5, 3 => (((-3) * T * b) + (3 * Y * a))
    | 5, 5 => 1
    | 5, 7 => a
    | 6, 2 => (5 * Y)
    | 6, 3 => ((-20) + ((-2) * T * a))
    | 6, 6 => 1
    | 7, 3 => (5 * Y)
    | 7, 7 => 1
    | _, _ => 0
def value194 (a b c d Y T : ℂ) : ℂ := (((-11664) * (b^4)) + (160000 * (c^3)) + ((-67200) * (a^2) * (c^2)) + ((-2500) * (Y^3) * (d^3)) + ((-1568) * (a^3) * (b^2)) + ((-54) * (Y^3) * (b^5)) + (54 * (T^3) * (b^6)) + (256 * (T^4) * (c^5)) + (256 * (Y^4) * (c^4)) + (625 * (T^4) * (d^4)) + (7056 * c * (a^4)) + (12800 * (T^2) * (c^4)) + (112000 * a * (d^2)) + ((-288000) * b * c * d) + ((-56000) * Y * d * (c^2)) + ((-20000) * T * Y * (d^3)) + ((-17664) * T * (a^3) * (c^2)) + ((-15680) * b * d * (a^2)) + ((-4320) * T * d * (b^3)) + ((-3584) * (T^2) * (a^2) * (c^3)) + ((-3528) * Y * d * (a^4)) + ((-3240) * T * a * (b^4)) + ((-2592) * Y * c * (b^3)) + ((-2300) * (Y^2) * (a^2) * (d^2)) + ((-2060) * (T^2) * (a^3) * (d^2)) + ((-2000) * b * (T^3) * (d^3)) + ((-972) * T * Y * (b^5)) + ((-896) * (Y^2) * (a^3) * (c^2)) + ((-864) * c * (T^2) * (b^4)) + ((-768) * (T^3) * (a^3) * (c^3)) + ((-512) * (T^3) * (b^2) * (c^3)) + ((-480) * (T^2) * (a^4) * (c^2)) + ((-448) * T * (a^4) * (b^2)) + ((-216) * a * (Y^2) * (b^4)) + ((-216) * (T^2) * (a^2) * (b^4)) + ((-128) * (T^4) * (a^2) * (c^4)) + ((-128) * (Y^4) * (a^2) * (c^3)) + ((-72) * Y * (a^2) * (b^3)) + ((-72) * d * (Y^3) * (a^5)) + ((-60) * (Y^4) * (a^3) * (d^2)) + ((-32) * (T^2) * (a^5) * (b^2)) + ((-32) * (Y^2) * (a^4) * (b^2)) + ((-27) * c * (Y^4) * (b^4)) + ((-27) * (T^4) * (b^4) * (c^2)) + ((-8) * (Y^3) * (a^3) * (b^3)) + (8 * (T^3) * (a^3) * (b^4)) + (16 * (T^4) * (a^4) * (c^3)) + (16 * (Y^4) * (a^4) * (c^2)) + (36 * (T^4) * (a^5) * (d^2)) + (54 * d * (T^4) * (b^5)) + (72 * (T^3) * (a^4) * (d^2)) + (96 * (T^3) * (a^5) * (c^2)) + (144 * c * (T^2) * (a^6)) + (144 * c * (Y^2) * (a^5)) + (225 * (Y^4) * (b^2) * (d^2)) + (512 * b * (Y^3) * (c^3)) + (864 * (Y^2) * (b^2) * (c^2)) + (900 * d * (Y^2) * (b^3)) + (1280 * a * (Y^2) * (c^3)) + (1536 * a * (T^3) * (c^4)) + (2016 * T * c * (a^5)) + (2880 * T * (b^2) * (c^2)) + (4800 * (T^2) * (b^2) * (d^2)) + (4800 * (T^3) * (c^2) * (d^2)) + (5120 * T * (Y^2) * (c^4)) + (10400 * T * (a^2) * (d^2)) + (14000 * c * (Y^2) * (d^2)) + (38400 * T * a * (c^3)) + (48000 * T * c * (d^2)) + (48000 * Y * b * (d^2)) + (69120 * a * c * (b^2)) + ((-25280) * b * d * (T^2) * (c^2)) + ((-23160) * Y * a * d * (b^2)) + ((-4480) * T * b * d * (a^3)) + ((-2560) * T * (Y^2) * (a^2) * (c^3)) + ((-1260) * c * d * (Y^3) * (b^2)) + ((-1200) * T * (Y^2) * (a^3) * (d^2)) + ((-1120) * a * d * (Y^3) * (c^2)) + ((-1088) * b * d * (T^4) * (c^3)) + ((-1050) * a * b * (T^4) * (d^3)) + ((-1008) * T * Y * d * (a^5)) + ((-984) * a * d * (T^2) * (b^3)) + ((-918) * Y * d * (T^2) * (b^4)) + ((-720) * b * d * (Y^4) * (c^2)) + ((-720) * c * (T^3) * (a^2) * (d^2)) + ((-540) * T * c * (Y^2) * (b^4)) + ((-534) * d * (Y^3) * (a^2) * (b^2)) + ((-450) * a * c * (T^3) * (b^4)) + ((-375) * b * (T^2) * (Y^2) * (d^3)) + ((-332) * c * (T^4) * (a^3) * (d^2)) + ((-320) * b * d * (T^2) * (a^4)) + ((-256) * Y * b * (T^3) * (c^4)) + ((-256) * b * (Y^3) * (a^2) * (c^2)) + ((-188) * b * d * (Y^2) * (a^3)) + ((-144) * T * Y * (a^3) * (b^3)) + ((-135) * Y * (T^3) * (b^3) * (d^2)) + ((-128) * (T^2) * (Y^2) * (a^3) * (c^3)) + ((-81) * a * d * (Y^4) * (b^3)) + ((-72) * Y * d * (T^2) * (a^6)) + ((-56) * c * (T^3) * (a^4) * (b^2)) + ((-54) * T * d * (Y^3) * (b^4)) + ((-54) * Y * a * (T^2) * (b^5)) + ((-24) * (T^2) * (Y^2) * (a^4) * (d^2)) + ((-12) * b * d * (Y^4) * (a^4)) + ((-8) * Y * (T^2) * (a^4) * (b^3)) + ((-4) * c * (Y^4) * (a^3) * (b^2)) + ((-4) * (T^4) * (a^3) * (b^2) * (c^2)) + (8 * d * (T^4) * (a^3) * (b^3)) + (16 * (T^2) * (Y^2) * (a^5) * (c^2)) + (27 * Y * c * (T^3) * (b^5)) + (32 * b * c * (Y^3) * (a^4)) + (48 * d * (T^3) * (a^2) * (b^3)) + (100 * Y * (T^3) * (a^2) * (d^3)) + (128 * Y * b * c * (a^3)) + (144 * a * (T^4) * (b^2) * (c^3)) + (144 * a * (Y^4) * (b^2) * (c^2)) + (250 * T * a * (Y^3) * (d^3)) + (256 * a * (T^2) * (Y^2) * (c^4)) + (288 * a * c * (Y^3) * (b^3)) + (291 * (T^4) * (a^2) * (b^2) * (d^2)) + (320 * T * d * (Y^3) * (c^3)) + (320 * T * (Y^2) * (a^4) * (c^2)) + (400 * a * c * (Y^4) * (d^2)) + (400 * (T^2) * (Y^2) * (c^2) * (d^2)) + (500 * Y * c * (T^3) * (d^3)) + (568 * c * d * (Y^3) * (a^3)) + (880 * a * (T^4) * (c^2) * (d^2)) + (936 * c * d * (T^3) * (b^3)) + (990 * a * (T^3) * (b^2) * (d^2)) + (990 * c * (T^4) * (b^2) * (d^2)) + (1120 * (T^3) * (a^2) * (b^2) * (c^2)) + (1132 * c * (T^2) * (a^3) * (b^2)) + (1224 * c * (Y^2) * (a^2) * (b^2)) + (1750 * Y * a * (T^2) * (d^3)) + (2700 * a * b * (Y^3) * (d^2)) + (4500 * T * (Y^2) * (b^2) * (d^2)) + (5440 * Y * d * (T^2) * (c^3)) + (5904 * a * (T^2) * (b^2) * (c^2)) + (7680 * Y * a * b * (c^2)) + (11520 * T * Y * b * (c^3)) + (18800 * a * c * (T^2) * (d^2)) + (19056 * T * c * (a^2) * (b^2)) + (23440 * Y * c * d * (a^2)) + ((-61440) * T * a * b * c * d) + ((-21120) * T * Y * c * d * (b^2)) + ((-19680) * T * Y * a * d * (c^2)) + ((-14400) * T * b * d * (Y^2) * (c^2)) + ((-10200) * Y * b * c * (T^2) * (d^2)) + ((-8096) * T * Y * d * (a^2) * (b^2)) + ((-4880) * a * b * c * d * (Y^2)) + ((-4224) * T * Y * b * (a^2) * (c^2)) + ((-4112) * Y * d * (T^2) * (a^2) * (c^2)) + ((-2624) * a * b * d * (T^3) * (c^2)) + ((-2448) * b * c * d * (T^2) * (a^2)) + ((-1620) * T * a * d * (Y^2) * (b^3)) + ((-670) * Y * d * (T^2) * (a^3) * (b^2)) + ((-600) * T * b * c * (Y^3) * (d^2)) + ((-342) * a * c * d * (T^4) * (b^3)) + ((-256) * Y * b * (T^2) * (a^3) * (c^2)) + ((-240) * T * b * d * (Y^2) * (a^4)) + ((-184) * Y * d * (T^3) * (a^3) * (c^2)) + ((-176) * T * d * (Y^3) * (a^2) * (c^2)) + ((-144) * Y * a * (T^3) * (b^3) * (c^2)) + ((-112) * b * c * d * (T^3) * (a^3)) + ((-81) * d * (T^2) * (Y^2) * (a^2) * (b^3)) + ((-80) * T * b * (Y^3) * (a^2) * (d^2)) + ((-80) * T * c * (Y^2) * (a^3) * (b^2)) + ((-40) * b * c * d * (T^4) * (a^4)) + ((-27) * a * c * (T^2) * (Y^2) * (b^4)) + ((-27) * c * d * (T^2) * (Y^2) * (b^3)) + ((-16) * Y * b * (T^3) * (a^4) * (c^2)) + ((-12) * b * d * (T^2) * (Y^2) * (a^5)) + ((-8) * T * d * (Y^3) * (a^3) * (b^2)) + ((-4) * c * (T^2) * (Y^2) * (a^4) * (b^2)) + (4 * Y * b * (T^3) * (a^3) * (d^2)) + (4 * Y * c * (T^3) * (a^3) * (b^3)) + (4 * Y * d * (T^3) * (a^4) * (b^2)) + (24 * T * c * d * (Y^3) * (a^4)) + (24 * Y * c * d * (T^3) * (a^5)) + (27 * Y * a * d * (T^3) * (b^4)) + (32 * Y * b * c * (T^2) * (a^5)) + (84 * b * c * d * (Y^4) * (a^2)) + (128 * Y * b * (T^3) * (a^2) * (c^3)) + (140 * c * (T^2) * (Y^2) * (a^2) * (d^2)) + (144 * (T^2) * (Y^2) * (a^2) * (b^2) * (c^2)) + (288 * Y * c * (T^2) * (a^2) * (b^3)) + (304 * b * d * (T^4) * (a^2) * (c^2)) + (352 * Y * a * d * (T^3) * (c^3)) + (420 * a * (T^2) * (Y^2) * (b^2) * (d^2)) + (512 * Y * a * b * (T^2) * (c^3)) + (592 * T * Y * b * c * (a^4)) + (684 * Y * d * (T^3) * (b^2) * (c^2)) + (976 * Y * c * d * (T^2) * (a^4)) + (1340 * Y * b * (T^2) * (a^2) * (d^2)) + (2880 * T * a * (Y^2) * (b^2) * (c^2)) + (5184 * T * Y * a * c * (b^3)) + (8000 * T * a * c * (Y^2) * (d^2)) + (8408 * T * Y * c * d * (a^3)) + (32200 * T * Y * a * b * (d^2)) + ((-1020) * Y * a * b * c * (T^3) * (d^2)) + ((-672) * a * b * d * (T^2) * (Y^2) * (c^2)) + (80 * b * c * d * (T^2) * (Y^2) * (a^3)) + (150 * Y * c * d * (T^3) * (a^2) * (b^2)) + (234 * T * a * c * d * (Y^3) * (b^2)) + (1680 * T * b * c * d * (Y^2) * (a^2)) + (2718 * Y * a * c * d * (T^2) * (b^2)))

theorem determinant194 (a b c d Y T : ℂ) :
    (minor194 a b c d Y T).det = value194 a b c d Y T := by
  have hm0 : (minor194 a b c d Y T).submatrix Fin.succ (0 : Fin 8).succAbove =
      minor116 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm4 : (minor194 a b c d Y T).submatrix Fin.succ (4 : Fin 8).succAbove =
      minor170 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm5 : (minor194 a b c d Y T).submatrix Fin.succ (5 : Fin 8).succAbove =
      minor193 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (((-2) * b) + (Y * c) + ((-5) * T * d)) * ((minor194 a b c d Y T).submatrix Fin.succ (0 : Fin 8).succAbove).det + ((-1 : ℂ)^1 * 0 * ((minor194 a b c d Y T).submatrix Fin.succ (1 : Fin 8).succAbove).det + ((-1 : ℂ)^2 * 0 * ((minor194 a b c d Y T).submatrix Fin.succ (2 : Fin 8).succAbove).det + ((-1 : ℂ)^3 * 0 * ((minor194 a b c d Y T).submatrix Fin.succ (3 : Fin 8).succAbove).det + ((-1 : ℂ)^4 * c * ((minor194 a b c d Y T).submatrix Fin.succ (4 : Fin 8).succAbove).det + ((-1 : ℂ)^5 * d * ((minor194 a b c d Y T).submatrix Fin.succ (5 : Fin 8).succAbove).det + ((-1 : ℂ)^6 * 0 * ((minor194 a b c d Y T).submatrix Fin.succ (6 : Fin 8).succAbove).det + ((-1 : ℂ)^7 * 0 * ((minor194 a b c d Y T).submatrix Fin.succ (7 : Fin 8).succAbove).det + (0)))))))) = value194 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant116, hm4, determinant170, hm5, determinant193]
  dsimp only [value194, value116, value170, value193] <;> ring

end Mordell.Determinants
