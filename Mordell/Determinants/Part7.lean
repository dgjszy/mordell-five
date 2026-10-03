import Mordell.Determinants.Part6

set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Mordell.Determinants

def minor105 (a b c d Y T : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (((-3) * T * b) + (3 * Y * a))
    | 0, 1 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 0, 2 => (((-2) * b) + (Y * c) + ((-5) * T * d))
    | 0, 4 => c
    | 1, 0 => ((-20) + ((-2) * T * a))
    | 1, 1 => (((-3) * T * b) + (3 * Y * a))
    | 1, 2 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 1, 3 => 1
    | 1, 4 => b
    | 2, 0 => (5 * Y)
    | 2, 1 => ((-20) + ((-2) * T * a))
    | 2, 2 => (((-3) * T * b) + (3 * Y * a))
    | 2, 4 => a
    | 3, 1 => (5 * Y)
    | 3, 2 => ((-20) + ((-2) * T * a))
    | 4, 2 => (5 * Y)
    | 4, 4 => 1
    | _, _ => 0
def value105 (a b c d Y T : ℂ) : ℂ := (((-1200) * T * b) + ((-100) * c * (Y^3)) + (30 * (Y^3) * (a^2)) + (150 * b * (Y^2)) + (600 * Y * a) + ((-400) * T * Y * c) + ((-240) * a * b * (T^2)) + ((-125) * T * d * (Y^2)) + ((-45) * Y * (T^2) * (b^2)) + ((-12) * b * (T^3) * (a^2)) + (12 * Y * (T^2) * (a^3)) + (180 * T * Y * (a^2)) + ((-40) * Y * a * c * (T^2)) + (35 * T * a * b * (Y^2)))

theorem determinant105 (a b c d Y T : ℂ) :
    (minor105 a b c d Y T).det = value105 a b c d Y T := by
  have hm0 : (minor105 a b c d Y T).submatrix Fin.succ (0 : Fin 5).succAbove =
      minor53 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor105 a b c d Y T).submatrix Fin.succ (1 : Fin 5).succAbove =
      minor99 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor105 a b c d Y T).submatrix Fin.succ (2 : Fin 5).succAbove =
      minor103 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm4 : (minor105 a b c d Y T).submatrix Fin.succ (4 : Fin 5).succAbove =
      minor104 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (((-3) * T * b) + (3 * Y * a)) * ((minor105 a b c d Y T).submatrix Fin.succ (0 : Fin 5).succAbove).det + ((-1 : ℂ)^1 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor105 a b c d Y T).submatrix Fin.succ (1 : Fin 5).succAbove).det + ((-1 : ℂ)^2 * (((-2) * b) + (Y * c) + ((-5) * T * d)) * ((minor105 a b c d Y T).submatrix Fin.succ (2 : Fin 5).succAbove).det + ((-1 : ℂ)^3 * 0 * ((minor105 a b c d Y T).submatrix Fin.succ (3 : Fin 5).succAbove).det + ((-1 : ℂ)^4 * c * ((minor105 a b c d Y T).submatrix Fin.succ (4 : Fin 5).succAbove).det + (0))))) = value105 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant53, hm1, determinant99, hm2, determinant103, hm4, determinant104]
  dsimp only [value105, value53, value99, value103, value104] <;> ring

def minor106 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => ((-20) + ((-2) * T * a))
    | 0, 1 => (((-3) * T * b) + (3 * Y * a))
    | 0, 2 => 1
    | 0, 3 => a
    | 1, 0 => (5 * Y)
    | 1, 1 => ((-20) + ((-2) * T * a))
    | 2, 1 => (5 * Y)
    | 2, 3 => 1
    | _, _ => 0
def value106 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant106 (a b c d Y T : ℂ) :
    (minor106 a b c d Y T).det = value106 a b c d Y T := by
  have hm0 : (minor106 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove =
      minor50 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor106 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove =
      minor96 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor106 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove =
      minor81 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor106 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove =
      minor102 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * ((-20) + ((-2) * T * a)) * ((minor106 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * (((-3) * T * b) + (3 * Y * a)) * ((minor106 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * 1 * ((minor106 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * a * ((minor106 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value106 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant50, hm1, determinant96, hm2, determinant81, hm3, determinant102]
  dsimp only [value106, value50, value96, value81, value102] <;> ring

def minor107 (a b c d Y T : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (((-3) * T * b) + (3 * Y * a))
    | 0, 1 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 0, 2 => (((-2) * b) + (Y * c) + ((-5) * T * d))
    | 0, 4 => b
    | 1, 0 => ((-20) + ((-2) * T * a))
    | 1, 1 => (((-3) * T * b) + (3 * Y * a))
    | 1, 2 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 1, 3 => 1
    | 1, 4 => a
    | 2, 0 => (5 * Y)
    | 2, 1 => ((-20) + ((-2) * T * a))
    | 2, 2 => (((-3) * T * b) + (3 * Y * a))
    | 3, 1 => (5 * Y)
    | 3, 2 => ((-20) + ((-2) * T * a))
    | 3, 4 => 1
    | 4, 2 => (5 * Y)
    | _, _ => 0
def value107 (a b c d Y T : ℂ) : ℂ := (((-75) * b * (Y^3)) + (150 * a * (Y^2)) + ((-300) * T * Y * b) + ((-100) * T * c * (Y^2)) + (30 * T * (Y^2) * (a^2)) + ((-30) * Y * a * b * (T^2)))

theorem determinant107 (a b c d Y T : ℂ) :
    (minor107 a b c d Y T).det = value107 a b c d Y T := by
  have hm0 : (minor107 a b c d Y T).submatrix Fin.succ (0 : Fin 5).succAbove =
      minor54 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor107 a b c d Y T).submatrix Fin.succ (1 : Fin 5).succAbove =
      minor100 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor107 a b c d Y T).submatrix Fin.succ (2 : Fin 5).succAbove =
      minor106 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm4 : (minor107 a b c d Y T).submatrix Fin.succ (4 : Fin 5).succAbove =
      minor104 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (((-3) * T * b) + (3 * Y * a)) * ((minor107 a b c d Y T).submatrix Fin.succ (0 : Fin 5).succAbove).det + ((-1 : ℂ)^1 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor107 a b c d Y T).submatrix Fin.succ (1 : Fin 5).succAbove).det + ((-1 : ℂ)^2 * (((-2) * b) + (Y * c) + ((-5) * T * d)) * ((minor107 a b c d Y T).submatrix Fin.succ (2 : Fin 5).succAbove).det + ((-1 : ℂ)^3 * 0 * ((minor107 a b c d Y T).submatrix Fin.succ (3 : Fin 5).succAbove).det + ((-1 : ℂ)^4 * b * ((minor107 a b c d Y T).submatrix Fin.succ (4 : Fin 5).succAbove).det + (0))))) = value107 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant54, hm1, determinant100, hm2, determinant106, hm4, determinant104]
  dsimp only [value107, value54, value100, value106, value104] <;> ring

def minor108 (a b c d Y T : ℂ) : Matrix (Fin 6) (Fin 6) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 0, 1 => (((-2) * b) + (Y * c) + ((-5) * T * d))
    | 0, 3 => a
    | 0, 4 => c
    | 0, 5 => d
    | 1, 0 => (((-3) * T * b) + (3 * Y * a))
    | 1, 1 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 1, 2 => (((-2) * b) + (Y * c) + ((-5) * T * d))
    | 1, 4 => b
    | 1, 5 => c
    | 2, 0 => ((-20) + ((-2) * T * a))
    | 2, 1 => (((-3) * T * b) + (3 * Y * a))
    | 2, 2 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 2, 3 => 1
    | 2, 4 => a
    | 2, 5 => b
    | 3, 0 => (5 * Y)
    | 3, 1 => ((-20) + ((-2) * T * a))
    | 3, 2 => (((-3) * T * b) + (3 * Y * a))
    | 3, 5 => a
    | 4, 1 => (5 * Y)
    | 4, 2 => ((-20) + ((-2) * T * a))
    | 4, 4 => 1
    | 5, 2 => (5 * Y)
    | 5, 5 => 1
    | _, _ => 0
def value108 (a b c d Y T : ℂ) : ℂ := (((-5040) * a * b) + ((-588) * Y * (a^3)) + ((-540) * Y * (b^2)) + ((-80) * (Y^3) * (c^2)) + ((-18) * (T^2) * (b^3)) + ((-12) * (Y^3) * (a^4)) + ((-1196) * T * b * (a^2)) + ((-720) * T * Y * (c^2)) + ((-400) * c * d * (T^2)) + ((-168) * T * Y * (a^4)) + ((-150) * a * d * (Y^2)) + ((-125) * Y * (T^2) * (d^2)) + ((-57) * a * (Y^3) * (b^2)) + ((-45) * d * (T^3) * (b^2)) + ((-40) * b * (T^2) * (a^3)) + ((-18) * T * (Y^2) * (b^3)) + ((-12) * Y * (T^2) * (a^5)) + (4 * b * (T^3) * (a^4)) + (20 * d * (T^3) * (a^3)) + (24 * b * (Y^2) * (a^2)) + (27 * a * (T^3) * (b^3)) + (48 * b * (T^3) * (c^2)) + (64 * c * (Y^3) * (a^2)) + (75 * b * d * (Y^3)) + (180 * b * c * (Y^2)) + (240 * T * b * c) + (340 * d * (T^2) * (a^2)) + (1400 * T * a * d) + (1720 * Y * a * c) + ((-738) * T * Y * a * (b^2)) + ((-272) * a * b * c * (T^2)) + ((-120) * Y * a * (T^2) * (c^2)) + ((-100) * T * c * d * (Y^2)) + ((-65) * Y * (T^2) * (a^2) * (b^2)) + ((-44) * b * c * (T^3) * (a^2)) + ((-40) * a * c * d * (T^3)) + ((-24) * Y * c * (T^2) * (b^2)) + ((-8) * T * b * (Y^2) * (a^3)) + (50 * T * d * (Y^2) * (a^2)) + (76 * Y * c * (T^2) * (a^3)) + (788 * T * Y * c * (a^2)) + (900 * T * Y * b * d) + ((-14) * T * a * b * c * (Y^2)) + (190 * Y * a * b * d * (T^2)))

theorem determinant108 (a b c d Y T : ℂ) :
    (minor108 a b c d Y T).det = value108 a b c d Y T := by
  have hm0 : (minor108 a b c d Y T).submatrix Fin.succ (0 : Fin 6).succAbove =
      minor55 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor108 a b c d Y T).submatrix Fin.succ (1 : Fin 6).succAbove =
      minor101 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor108 a b c d Y T).submatrix Fin.succ (3 : Fin 6).succAbove =
      minor86 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm4 : (minor108 a b c d Y T).submatrix Fin.succ (4 : Fin 6).succAbove =
      minor105 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm5 : (minor108 a b c d Y T).submatrix Fin.succ (5 : Fin 6).succAbove =
      minor107 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor108 a b c d Y T).submatrix Fin.succ (0 : Fin 6).succAbove).det + ((-1 : ℂ)^1 * (((-2) * b) + (Y * c) + ((-5) * T * d)) * ((minor108 a b c d Y T).submatrix Fin.succ (1 : Fin 6).succAbove).det + ((-1 : ℂ)^2 * 0 * ((minor108 a b c d Y T).submatrix Fin.succ (2 : Fin 6).succAbove).det + ((-1 : ℂ)^3 * a * ((minor108 a b c d Y T).submatrix Fin.succ (3 : Fin 6).succAbove).det + ((-1 : ℂ)^4 * c * ((minor108 a b c d Y T).submatrix Fin.succ (4 : Fin 6).succAbove).det + ((-1 : ℂ)^5 * d * ((minor108 a b c d Y T).submatrix Fin.succ (5 : Fin 6).succAbove).det + (0)))))) = value108 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant55, hm1, determinant101, hm3, determinant86, hm4, determinant105, hm5, determinant107]
  dsimp only [value108, value55, value101, value86, value105, value107] <;> ring

def minor109 (a b c d Y T : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (5 * Y)
    | 0, 2 => 1
    | _, _ => 0
def value109 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant109 (a b c d Y T : ℂ) :
    (minor109 a b c d Y T).det = value109 a b c d Y T := by
  have hm0 : (minor109 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove =
      minor7 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor109 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove =
      minor94 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (5 * Y) * ((minor109 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove).det + ((-1 : ℂ)^1 * 0 * ((minor109 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove).det + ((-1 : ℂ)^2 * 1 * ((minor109 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove).det + (0))) = value109 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant7, hm2, determinant94]
  dsimp only [value109, value7, value94] <;> ring

def minor110 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => ((-20) + ((-2) * T * a))
    | 0, 1 => 1
    | 0, 3 => b
    | 1, 0 => (5 * Y)
    | 1, 2 => 1
    | 1, 3 => a
    | 3, 3 => 1
    | _, _ => 0
def value110 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant110 (a b c d Y T : ℂ) :
    (minor110 a b c d Y T).det = value110 a b c d Y T := by
  have hm0 : (minor110 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove =
      minor8 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor110 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove =
      minor65 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor110 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove =
      minor109 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * ((-20) + ((-2) * T * a)) * ((minor110 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * 1 * ((minor110 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * 0 * ((minor110 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * b * ((minor110 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value110 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant8, hm1, determinant65, hm3, determinant109]
  dsimp only [value110, value8, value65, value109] <;> ring

def minor111 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => ((-20) + ((-2) * T * a))
    | 0, 1 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 0, 2 => 1
    | 1, 0 => (5 * Y)
    | 1, 1 => (((-3) * T * b) + (3 * Y * a))
    | 1, 3 => 1
    | 2, 1 => ((-20) + ((-2) * T * a))
    | 3, 1 => (5 * Y)
    | _, _ => 0
def value111 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant111 (a b c d Y T : ℂ) :
    (minor111 a b c d Y T).det = value111 a b c d Y T := by
  have hm0 : (minor111 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove =
      minor26 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor111 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove =
      minor109 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor111 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove =
      minor75 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * ((-20) + ((-2) * T * a)) * ((minor111 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor111 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * 1 * ((minor111 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * 0 * ((minor111 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value111 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant26, hm1, determinant109, hm2, determinant75]
  dsimp only [value111, value26, value109, value75] <;> ring

def minor112 (a b c d Y T : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (((-3) * T * b) + (3 * Y * a))
    | 0, 1 => (((-2) * b) + (Y * c) + ((-5) * T * d))
    | 0, 3 => a
    | 0, 4 => c
    | 1, 0 => ((-20) + ((-2) * T * a))
    | 1, 1 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 1, 2 => 1
    | 1, 4 => b
    | 2, 0 => (5 * Y)
    | 2, 1 => (((-3) * T * b) + (3 * Y * a))
    | 2, 3 => 1
    | 2, 4 => a
    | 3, 1 => ((-20) + ((-2) * T * a))
    | 4, 1 => (5 * Y)
    | 4, 4 => 1
    | _, _ => 0
def value112 (a b c d Y T : ℂ) : ℂ := ((40 * Y * a) + (60 * T * b) + (4 * T * Y * (a^2)) + (6 * a * b * (T^2)))

theorem determinant112 (a b c d Y T : ℂ) :
    (minor112 a b c d Y T).det = value112 a b c d Y T := by
  have hm0 : (minor112 a b c d Y T).submatrix Fin.succ (0 : Fin 5).succAbove =
      minor27 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor112 a b c d Y T).submatrix Fin.succ (1 : Fin 5).succAbove =
      minor110 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor112 a b c d Y T).submatrix Fin.succ (3 : Fin 5).succAbove =
      minor99 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm4 : (minor112 a b c d Y T).submatrix Fin.succ (4 : Fin 5).succAbove =
      minor111 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (((-3) * T * b) + (3 * Y * a)) * ((minor112 a b c d Y T).submatrix Fin.succ (0 : Fin 5).succAbove).det + ((-1 : ℂ)^1 * (((-2) * b) + (Y * c) + ((-5) * T * d)) * ((minor112 a b c d Y T).submatrix Fin.succ (1 : Fin 5).succAbove).det + ((-1 : ℂ)^2 * 0 * ((minor112 a b c d Y T).submatrix Fin.succ (2 : Fin 5).succAbove).det + ((-1 : ℂ)^3 * a * ((minor112 a b c d Y T).submatrix Fin.succ (3 : Fin 5).succAbove).det + ((-1 : ℂ)^4 * c * ((minor112 a b c d Y T).submatrix Fin.succ (4 : Fin 5).succAbove).det + (0))))) = value112 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant27, hm1, determinant110, hm3, determinant99, hm4, determinant111]
  dsimp only [value112, value27, value110, value99, value111] <;> ring

def minor113 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => ((-20) + ((-2) * T * a))
    | 0, 1 => (((-3) * T * b) + (3 * Y * a))
    | 0, 2 => 1
    | 1, 0 => (5 * Y)
    | 1, 1 => ((-20) + ((-2) * T * a))
    | 1, 3 => 1
    | 2, 1 => (5 * Y)
    | _, _ => 0
def value113 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant113 (a b c d Y T : ℂ) :
    (minor113 a b c d Y T).det = value113 a b c d Y T := by
  have hm0 : (minor113 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove =
      minor56 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor113 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove =
      minor109 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor113 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove =
      minor87 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * ((-20) + ((-2) * T * a)) * ((minor113 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * (((-3) * T * b) + (3 * Y * a)) * ((minor113 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * 1 * ((minor113 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * 0 * ((minor113 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value113 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant56, hm1, determinant109, hm2, determinant87]
  dsimp only [value113, value56, value109, value87] <;> ring

def minor114 (a b c d Y T : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (((-3) * T * b) + (3 * Y * a))
    | 0, 1 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 0, 2 => (((-2) * b) + (Y * c) + ((-5) * T * d))
    | 0, 4 => a
    | 1, 0 => ((-20) + ((-2) * T * a))
    | 1, 1 => (((-3) * T * b) + (3 * Y * a))
    | 1, 2 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 1, 3 => 1
    | 2, 0 => (5 * Y)
    | 2, 1 => ((-20) + ((-2) * T * a))
    | 2, 2 => (((-3) * T * b) + (3 * Y * a))
    | 2, 4 => 1
    | 3, 1 => (5 * Y)
    | 3, 2 => ((-20) + ((-2) * T * a))
    | 4, 2 => (5 * Y)
    | _, _ => 0
def value114 (a b c d Y T : ℂ) : ℂ := (((-50) * a * (Y^3)) + ((-75) * T * b * (Y^2)))

theorem determinant114 (a b c d Y T : ℂ) :
    (minor114 a b c d Y T).det = value114 a b c d Y T := by
  have hm0 : (minor114 a b c d Y T).submatrix Fin.succ (0 : Fin 5).succAbove =
      minor58 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor114 a b c d Y T).submatrix Fin.succ (1 : Fin 5).succAbove =
      minor111 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor114 a b c d Y T).submatrix Fin.succ (2 : Fin 5).succAbove =
      minor113 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm4 : (minor114 a b c d Y T).submatrix Fin.succ (4 : Fin 5).succAbove =
      minor104 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (((-3) * T * b) + (3 * Y * a)) * ((minor114 a b c d Y T).submatrix Fin.succ (0 : Fin 5).succAbove).det + ((-1 : ℂ)^1 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor114 a b c d Y T).submatrix Fin.succ (1 : Fin 5).succAbove).det + ((-1 : ℂ)^2 * (((-2) * b) + (Y * c) + ((-5) * T * d)) * ((minor114 a b c d Y T).submatrix Fin.succ (2 : Fin 5).succAbove).det + ((-1 : ℂ)^3 * 0 * ((minor114 a b c d Y T).submatrix Fin.succ (3 : Fin 5).succAbove).det + ((-1 : ℂ)^4 * a * ((minor114 a b c d Y T).submatrix Fin.succ (4 : Fin 5).succAbove).det + (0))))) = value114 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant58, hm1, determinant111, hm2, determinant113, hm4, determinant104]
  dsimp only [value114, value58, value111, value113, value104] <;> ring

def minor115 (a b c d Y T : ℂ) : Matrix (Fin 6) (Fin 6) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 0, 1 => (((-2) * b) + (Y * c) + ((-5) * T * d))
    | 0, 3 => a
    | 0, 4 => b
    | 0, 5 => d
    | 1, 0 => (((-3) * T * b) + (3 * Y * a))
    | 1, 1 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 1, 2 => (((-2) * b) + (Y * c) + ((-5) * T * d))
    | 1, 4 => a
    | 1, 5 => c
    | 2, 0 => ((-20) + ((-2) * T * a))
    | 2, 1 => (((-3) * T * b) + (3 * Y * a))
    | 2, 2 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 2, 3 => 1
    | 2, 5 => b
    | 3, 0 => (5 * Y)
    | 3, 1 => ((-20) + ((-2) * T * a))
    | 3, 2 => (((-3) * T * b) + (3 * Y * a))
    | 3, 4 => 1
    | 3, 5 => a
    | 4, 1 => (5 * Y)
    | 4, 2 => ((-20) + ((-2) * T * a))
    | 5, 2 => (5 * Y)
    | 5, 5 => 1
    | _, _ => 0
def value115 (a b c d Y T : ℂ) : ℂ := (((-3920) * (a^2)) + ((-1512) * T * (a^3)) + ((-1080) * T * (b^2)) + ((-320) * (T^2) * (c^2)) + ((-192) * (T^2) * (a^4)) + ((-80) * (Y^2) * (a^3)) + ((-8) * (T^3) * (a^5)) + (90 * (Y^2) * (b^2)) + ((-408) * a * (T^2) * (b^2)) + ((-300) * Y * a * b) + ((-80) * T * (Y^2) * (c^2)) + ((-60) * b * c * (Y^3)) + ((-45) * Y * (T^2) * (b^3)) + ((-32) * a * (T^3) * (c^2)) + ((-30) * (T^3) * (a^2) * (b^2)) + ((-20) * b * (Y^3) * (a^2)) + ((-8) * T * (Y^2) * (a^4)) + (32 * c * (T^3) * (a^3)) + (50 * a * d * (Y^3)) + (240 * a * c * (Y^2)) + (300 * b * d * (T^2)) + (544 * c * (T^2) * (a^2)) + (2240 * T * a * c) + ((-304) * T * Y * b * (a^2)) + ((-180) * T * Y * b * c) + ((-100) * Y * c * d * (T^2)) + ((-48) * T * a * (Y^2) * (b^2)) + ((-28) * Y * b * (T^2) * (a^3)) + (30 * a * b * d * (T^3)) + (36 * T * c * (Y^2) * (a^2)) + (70 * Y * d * (T^2) * (a^2)) + (550 * T * Y * a * d) + ((-14) * Y * a * b * c * (T^2)))

theorem determinant115 (a b c d Y T : ℂ) :
    (minor115 a b c d Y T).det = value115 a b c d Y T := by
  have hm0 : (minor115 a b c d Y T).submatrix Fin.succ (0 : Fin 6).succAbove =
      minor59 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor115 a b c d Y T).submatrix Fin.succ (1 : Fin 6).succAbove =
      minor112 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor115 a b c d Y T).submatrix Fin.succ (3 : Fin 6).succAbove =
      minor90 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm4 : (minor115 a b c d Y T).submatrix Fin.succ (4 : Fin 6).succAbove =
      minor105 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm5 : (minor115 a b c d Y T).submatrix Fin.succ (5 : Fin 6).succAbove =
      minor114 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor115 a b c d Y T).submatrix Fin.succ (0 : Fin 6).succAbove).det + ((-1 : ℂ)^1 * (((-2) * b) + (Y * c) + ((-5) * T * d)) * ((minor115 a b c d Y T).submatrix Fin.succ (1 : Fin 6).succAbove).det + ((-1 : ℂ)^2 * 0 * ((minor115 a b c d Y T).submatrix Fin.succ (2 : Fin 6).succAbove).det + ((-1 : ℂ)^3 * a * ((minor115 a b c d Y T).submatrix Fin.succ (3 : Fin 6).succAbove).det + ((-1 : ℂ)^4 * b * ((minor115 a b c d Y T).submatrix Fin.succ (4 : Fin 6).succAbove).det + ((-1 : ℂ)^5 * d * ((minor115 a b c d Y T).submatrix Fin.succ (5 : Fin 6).succAbove).det + (0)))))) = value115 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant59, hm1, determinant112, hm3, determinant90, hm4, determinant105, hm5, determinant114]
  dsimp only [value115, value59, value112, value90, value105, value114] <;> ring

def minor116 (a b c d Y T : ℂ) : Matrix (Fin 7) (Fin 7) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (((-2) * b) + (Y * c) + ((-5) * T * d))
    | 0, 3 => b
    | 0, 4 => c
    | 0, 5 => d
    | 1, 0 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 1, 1 => (((-2) * b) + (Y * c) + ((-5) * T * d))
    | 1, 3 => a
    | 1, 4 => b
    | 1, 5 => c
    | 1, 6 => d
    | 2, 0 => (((-3) * T * b) + (3 * Y * a))
    | 2, 1 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 2, 2 => (((-2) * b) + (Y * c) + ((-5) * T * d))
    | 2, 4 => a
    | 2, 5 => b
    | 2, 6 => c
    | 3, 0 => ((-20) + ((-2) * T * a))
    | 3, 1 => (((-3) * T * b) + (3 * Y * a))
    | 3, 2 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 3, 3 => 1
    | 3, 5 => a
    | 3, 6 => b
    | 4, 0 => (5 * Y)
    | 4, 1 => ((-20) + ((-2) * T * a))
    | 4, 2 => (((-3) * T * b) + (3 * Y * a))
    | 4, 4 => 1
    | 4, 6 => a
    | 5, 1 => (5 * Y)
    | 5, 2 => ((-20) + ((-2) * T * a))
    | 5, 5 => 1
    | 6, 2 => (5 * Y)
    | 6, 6 => 1
    | _, _ => 0
def value116 (a b c d Y T : ℂ) : ℂ := ((5832 * (b^3)) + ((-125) * (T^3) * (d^3)) + ((-64) * (Y^3) * (c^3)) + ((-27) * (T^3) * (b^5)) + (27 * (Y^3) * (b^4)) + (784 * b * (a^3)) + (3920 * d * (a^2)) + ((-10080) * a * b * c) + ((-3780) * T * d * (b^2)) + ((-1728) * Y * c * (b^2)) + ((-640) * T * Y * (c^3)) + ((-480) * d * (T^2) * (c^2)) + ((-392) * Y * c * (a^3)) + ((-360) * d * (Y^2) * (b^2)) + ((-88) * d * (T^2) * (a^4)) + ((-50) * a * (Y^3) * (d^2)) + ((-12) * d * (T^3) * (a^5)) + ((-8) * c * (Y^3) * (a^4)) + ((-4) * (T^3) * (a^3) * (b^3)) + (4 * (Y^3) * (a^3) * (b^2)) + (16 * b * (T^2) * (a^5)) + (16 * b * (Y^2) * (a^4)) + (36 * Y * (a^2) * (b^2)) + (48 * (Y^3) * (a^2) * (c^2)) + (80 * d * (Y^2) * (a^3)) + (108 * a * (Y^2) * (b^3)) + (108 * (T^2) * (a^2) * (b^3)) + (112 * b * (T^3) * (c^3)) + (224 * T * b * (a^4)) + (384 * b * (Y^2) * (c^2)) + (450 * c * (T^2) * (b^3)) + (486 * T * Y * (b^4)) + (532 * T * d * (a^3)) + (1050 * b * (T^2) * (d^2)) + (1440 * Y * a * (c^2)) + (1620 * T * a * (b^3)) + (1680 * T * b * (c^2)) + ((-2644) * T * b * c * (a^2)) + ((-1122) * a * d * (T^2) * (b^2)) + ((-900) * T * Y * a * (d^2)) + ((-352) * a * b * (T^2) * (c^2)) + ((-320) * a * c * d * (Y^2)) + ((-225) * c * d * (T^3) * (b^2)) + ((-160) * b * c * (Y^2) * (a^2)) + ((-128) * a * d * (T^3) * (c^2)) + ((-112) * T * Y * c * (a^4)) + ((-105) * d * (T^3) * (a^2) * (b^2)) + ((-100) * Y * c * (T^2) * (d^2)) + ((-96) * Y * a * (T^2) * (c^3)) + ((-92) * b * (T^3) * (a^2) * (c^2)) + ((-90) * a * c * (Y^3) * (b^2)) + ((-88) * b * c * (T^2) * (a^3)) + ((-80) * T * d * (Y^2) * (c^2)) + ((-45) * Y * d * (T^2) * (b^3)) + ((-20) * Y * (T^2) * (a^2) * (d^2)) + ((-12) * T * d * (Y^2) * (a^4)) + ((-8) * Y * c * (T^2) * (a^5)) + (4 * Y * (T^2) * (a^4) * (b^2)) + (12 * b * c * (T^3) * (a^4)) + (27 * T * c * (Y^2) * (b^3)) + (27 * Y * a * (T^2) * (b^4)) + (36 * Y * (T^2) * (b^2) * (c^2)) + (40 * b * d * (Y^3) * (a^2)) + (56 * Y * (T^2) * (a^3) * (c^2)) + (72 * T * Y * (a^3) * (b^2)) + (75 * T * b * (Y^2) * (d^2)) + (88 * c * d * (T^3) * (a^3)) + (117 * a * c * (T^3) * (b^3)) + (120 * b * c * d * (Y^3)) + (270 * a * b * (T^3) * (d^2)) + (560 * T * a * c * d) + (608 * T * Y * (a^2) * (c^2)) + (696 * c * d * (T^2) * (a^2)) + (1560 * Y * a * b * d) + ((-1428) * T * Y * a * c * (b^2)) + ((-90) * Y * c * (T^2) * (a^2) * (b^2)) + ((-57) * T * a * d * (Y^2) * (b^2)) + ((-48) * T * a * b * (Y^2) * (c^2)) + (4 * T * b * c * (Y^2) * (a^3)) + (28 * Y * b * d * (T^2) * (a^3)) + (84 * T * c * d * (Y^2) * (a^2)) + (744 * T * Y * b * d * (a^2)) + (1680 * T * Y * b * c * d) + (124 * Y * a * b * c * d * (T^2)))

theorem determinant116 (a b c d Y T : ℂ) :
    (minor116 a b c d Y T).det = value116 a b c d Y T := by
  have hm0 : (minor116 a b c d Y T).submatrix Fin.succ (0 : Fin 7).succAbove =
      minor62 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor116 a b c d Y T).submatrix Fin.succ (3 : Fin 7).succAbove =
      minor93 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm4 : (minor116 a b c d Y T).submatrix Fin.succ (4 : Fin 7).succAbove =
      minor108 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm5 : (minor116 a b c d Y T).submatrix Fin.succ (5 : Fin 7).succAbove =
      minor115 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (((-2) * b) + (Y * c) + ((-5) * T * d)) * ((minor116 a b c d Y T).submatrix Fin.succ (0 : Fin 7).succAbove).det + ((-1 : ℂ)^1 * 0 * ((minor116 a b c d Y T).submatrix Fin.succ (1 : Fin 7).succAbove).det + ((-1 : ℂ)^2 * 0 * ((minor116 a b c d Y T).submatrix Fin.succ (2 : Fin 7).succAbove).det + ((-1 : ℂ)^3 * b * ((minor116 a b c d Y T).submatrix Fin.succ (3 : Fin 7).succAbove).det + ((-1 : ℂ)^4 * c * ((minor116 a b c d Y T).submatrix Fin.succ (4 : Fin 7).succAbove).det + ((-1 : ℂ)^5 * d * ((minor116 a b c d Y T).submatrix Fin.succ (5 : Fin 7).succAbove).det + ((-1 : ℂ)^6 * 0 * ((minor116 a b c d Y T).submatrix Fin.succ (6 : Fin 7).succAbove).det + (0))))))) = value116 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant62, hm3, determinant93, hm4, determinant108, hm5, determinant115]
  dsimp only [value116, value62, value93, value108, value115] <;> ring

def minor117 (a b c d Y T : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => match i.val, j.val with
    | 1, 1 => 1
    | _, _ => 0
def value117 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant117 (a b c d Y T : ℂ) :
    (minor117 a b c d Y T).det = value117 a b c d Y T := by
  rw [show value117 a b c d Y T = 0 by rfl]
  apply Matrix.det_eq_zero_of_row_eq_zero 0
  intro j
  fin_cases j <;> rfl

def minor118 (a b c d Y T : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => match i.val, j.val with
    | _, _ => 0
def value118 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant118 (a b c d Y T : ℂ) :
    (minor118 a b c d Y T).det = value118 a b c d Y T := by
  rw [show value118 a b c d Y T = 0 by rfl]
  apply Matrix.det_eq_zero_of_row_eq_zero 0
  intro j
  fin_cases j <;> rfl

def minor119 (a b c d Y T : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 1 => 1
    | 0, 2 => a
    | 2, 2 => 1
    | _, _ => 0
def value119 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant119 (a b c d Y T : ℂ) :
    (minor119 a b c d Y T).det = value119 a b c d Y T := by
  have hm1 : (minor119 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove =
      minor117 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor119 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove =
      minor118 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * 0 * ((minor119 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove).det + ((-1 : ℂ)^1 * 1 * ((minor119 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove).det + ((-1 : ℂ)^2 * a * ((minor119 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove).det + (0))) = value119 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm1, determinant117, hm2, determinant118]
  dsimp only [value119, value117, value118] <;> ring

end Mordell.Determinants
