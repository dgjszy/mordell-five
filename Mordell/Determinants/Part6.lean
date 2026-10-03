import Mordell.Determinants.Part5

set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Mordell.Determinants

def minor90 (a b c d Y T : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (((-3) * T * b) + (3 * Y * a))
    | 0, 1 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 0, 2 => (((-2) * b) + (Y * c) + ((-5) * T * d))
    | 0, 3 => a
    | 0, 4 => c
    | 1, 0 => ((-20) + ((-2) * T * a))
    | 1, 1 => (((-3) * T * b) + (3 * Y * a))
    | 1, 2 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 1, 4 => b
    | 2, 0 => (5 * Y)
    | 2, 1 => ((-20) + ((-2) * T * a))
    | 2, 2 => (((-3) * T * b) + (3 * Y * a))
    | 2, 3 => 1
    | 2, 4 => a
    | 3, 1 => (5 * Y)
    | 3, 2 => ((-20) + ((-2) * T * a))
    | 4, 2 => (5 * Y)
    | 4, 4 => 1
    | _, _ => 0
def value90 (a b c d Y T : ℂ) : ℂ := ((5600 * a) + ((-1600) * T * c) + ((-400) * c * (Y^2)) + (8 * (T^3) * (a^4)) + (140 * (Y^2) * (a^2)) + (180 * (T^2) * (b^2)) + (216 * (T^2) * (a^3)) + (600 * Y * b) + (1920 * T * (a^2)) + ((-500) * T * Y * d) + ((-320) * a * c * (T^2)) + ((-16) * c * (T^3) * (a^2)) + (8 * T * (Y^2) * (a^3)) + (18 * a * (T^3) * (b^2)) + (30 * a * b * (Y^3)) + (45 * T * (Y^2) * (b^2)) + ((-50) * Y * a * d * (T^2)) + (32 * Y * b * (T^2) * (a^2)) + (60 * Y * b * c * (T^2)) + (470 * T * Y * a * b))

theorem determinant90 (a b c d Y T : ℂ) :
    (minor90 a b c d Y T).det = value90 a b c d Y T := by
  have hm0 : (minor90 a b c d Y T).submatrix Fin.succ (0 : Fin 5).succAbove =
      minor45 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor90 a b c d Y T).submatrix Fin.succ (1 : Fin 5).succAbove =
      minor76 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor90 a b c d Y T).submatrix Fin.succ (2 : Fin 5).succAbove =
      minor88 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor90 a b c d Y T).submatrix Fin.succ (3 : Fin 5).succAbove =
      minor84 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm4 : (minor90 a b c d Y T).submatrix Fin.succ (4 : Fin 5).succAbove =
      minor89 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (((-3) * T * b) + (3 * Y * a)) * ((minor90 a b c d Y T).submatrix Fin.succ (0 : Fin 5).succAbove).det + ((-1 : ℂ)^1 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor90 a b c d Y T).submatrix Fin.succ (1 : Fin 5).succAbove).det + ((-1 : ℂ)^2 * (((-2) * b) + (Y * c) + ((-5) * T * d)) * ((minor90 a b c d Y T).submatrix Fin.succ (2 : Fin 5).succAbove).det + ((-1 : ℂ)^3 * a * ((minor90 a b c d Y T).submatrix Fin.succ (3 : Fin 5).succAbove).det + ((-1 : ℂ)^4 * c * ((minor90 a b c d Y T).submatrix Fin.succ (4 : Fin 5).succAbove).det + (0))))) = value90 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant45, hm1, determinant76, hm2, determinant88, hm3, determinant84, hm4, determinant89]
  dsimp only [value90, value45, value76, value88, value84, value89] <;> ring

def minor91 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => ((-20) + ((-2) * T * a))
    | 0, 1 => (((-3) * T * b) + (3 * Y * a))
    | 0, 3 => a
    | 1, 0 => (5 * Y)
    | 1, 1 => ((-20) + ((-2) * T * a))
    | 1, 2 => 1
    | 2, 1 => (5 * Y)
    | 2, 3 => 1
    | _, _ => 0
def value91 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant91 (a b c d Y T : ℂ) :
    (minor91 a b c d Y T).det = value91 a b c d Y T := by
  have hm0 : (minor91 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove =
      minor37 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor91 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove =
      minor68 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor91 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove =
      minor87 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * ((-20) + ((-2) * T * a)) * ((minor91 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * (((-3) * T * b) + (3 * Y * a)) * ((minor91 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * 0 * ((minor91 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * a * ((minor91 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value91 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant37, hm1, determinant68, hm3, determinant87]
  dsimp only [value91, value37, value68, value87] <;> ring

def minor92 (a b c d Y T : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (((-3) * T * b) + (3 * Y * a))
    | 0, 1 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 0, 2 => (((-2) * b) + (Y * c) + ((-5) * T * d))
    | 0, 3 => a
    | 0, 4 => b
    | 1, 0 => ((-20) + ((-2) * T * a))
    | 1, 1 => (((-3) * T * b) + (3 * Y * a))
    | 1, 2 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 1, 4 => a
    | 2, 0 => (5 * Y)
    | 2, 1 => ((-20) + ((-2) * T * a))
    | 2, 2 => (((-3) * T * b) + (3 * Y * a))
    | 2, 3 => 1
    | 3, 1 => (5 * Y)
    | 3, 2 => ((-20) + ((-2) * T * a))
    | 3, 4 => 1
    | 4, 2 => (5 * Y)
    | _, _ => 0
def value92 (a b c d Y T : ℂ) : ℂ := (((-300) * b * (Y^2)) + (20 * (Y^3) * (a^2)) + (1400 * Y * a) + ((-400) * T * Y * c) + (20 * Y * (T^2) * (a^3)) + (45 * Y * (T^2) * (b^2)) + (340 * T * Y * (a^2)) + ((-40) * Y * a * c * (T^2)) + (30 * T * a * b * (Y^2)))

theorem determinant92 (a b c d Y T : ℂ) :
    (minor92 a b c d Y T).det = value92 a b c d Y T := by
  have hm0 : (minor92 a b c d Y T).submatrix Fin.succ (0 : Fin 5).succAbove =
      minor46 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor92 a b c d Y T).submatrix Fin.succ (1 : Fin 5).succAbove =
      minor77 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor92 a b c d Y T).submatrix Fin.succ (2 : Fin 5).succAbove =
      minor91 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor92 a b c d Y T).submatrix Fin.succ (3 : Fin 5).succAbove =
      minor85 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm4 : (minor92 a b c d Y T).submatrix Fin.succ (4 : Fin 5).succAbove =
      minor89 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (((-3) * T * b) + (3 * Y * a)) * ((minor92 a b c d Y T).submatrix Fin.succ (0 : Fin 5).succAbove).det + ((-1 : ℂ)^1 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor92 a b c d Y T).submatrix Fin.succ (1 : Fin 5).succAbove).det + ((-1 : ℂ)^2 * (((-2) * b) + (Y * c) + ((-5) * T * d)) * ((minor92 a b c d Y T).submatrix Fin.succ (2 : Fin 5).succAbove).det + ((-1 : ℂ)^3 * a * ((minor92 a b c d Y T).submatrix Fin.succ (3 : Fin 5).succAbove).det + ((-1 : ℂ)^4 * b * ((minor92 a b c d Y T).submatrix Fin.succ (4 : Fin 5).succAbove).det + (0))))) = value92 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant46, hm1, determinant77, hm2, determinant91, hm3, determinant85, hm4, determinant89]
  dsimp only [value92, value46, value77, value91, value85, value89] <;> ring

def minor93 (a b c d Y T : ℂ) : Matrix (Fin 6) (Fin 6) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 0, 1 => (((-2) * b) + (Y * c) + ((-5) * T * d))
    | 0, 3 => b
    | 0, 4 => c
    | 0, 5 => d
    | 1, 0 => (((-3) * T * b) + (3 * Y * a))
    | 1, 1 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 1, 2 => (((-2) * b) + (Y * c) + ((-5) * T * d))
    | 1, 3 => a
    | 1, 4 => b
    | 1, 5 => c
    | 2, 0 => ((-20) + ((-2) * T * a))
    | 2, 1 => (((-3) * T * b) + (3 * Y * a))
    | 2, 2 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 2, 4 => a
    | 2, 5 => b
    | 3, 0 => (5 * Y)
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
def value93 (a b c d Y T : ℂ) : ℂ := (((-6480) * (b^2)) + ((-1176) * (a^3)) + ((-1600) * T * (c^2)) + ((-500) * (T^2) * (d^2)) + ((-336) * T * (a^4)) + ((-320) * (Y^2) * (c^2)) + ((-64) * (T^3) * (c^3)) + ((-27) * (Y^3) * (b^3)) + ((-24) * (T^2) * (a^5)) + ((-24) * (Y^2) * (a^4)) + (27 * (T^3) * (b^4)) + (5600 * a * c) + ((-1896) * T * a * (b^2)) + ((-1400) * Y * a * d) + ((-504) * T * Y * (b^3)) + ((-492) * c * (T^2) * (b^2)) + ((-146) * (T^2) * (a^2) * (b^2)) + ((-138) * a * (Y^2) * (b^2)) + ((-50) * a * (T^3) * (d^2)) + ((-20) * d * (Y^3) * (a^2)) + ((-8) * c * (T^3) * (a^4)) + ((-4) * b * (Y^3) * (a^3)) + (4 * (T^3) * (a^3) * (b^2)) + (32 * a * (T^2) * (c^2)) + (44 * Y * b * (a^2)) + (48 * (T^3) * (a^2) * (c^2)) + (88 * c * (T^2) * (a^3)) + (176 * c * (Y^2) * (a^2)) + (300 * b * d * (Y^2)) + (1680 * Y * b * c) + (1808 * T * c * (a^2)) + (3600 * T * b * d) + ((-400) * T * Y * c * d) + ((-220) * T * Y * d * (a^2)) + ((-90) * a * c * (T^3) * (b^2)) + ((-80) * T * Y * b * (a^3)) + ((-48) * Y * b * (T^2) * (c^2)) + ((-36) * T * c * (Y^2) * (b^2)) + ((-27) * Y * a * (T^2) * (b^3)) + ((-20) * Y * d * (T^2) * (a^3)) + ((-8) * T * c * (Y^2) * (a^3)) + ((-4) * Y * b * (T^2) * (a^4)) + (32 * T * a * (Y^2) * (c^2)) + (40 * b * d * (T^3) * (a^2)) + (45 * Y * d * (T^2) * (b^2)) + (48 * a * b * c * (Y^3)) + (120 * b * c * d * (T^3)) + (940 * a * b * d * (T^2)) + (30 * T * a * b * d * (Y^2)) + (40 * Y * a * c * d * (T^2)) + (44 * Y * b * c * (T^2) * (a^2)) + (832 * T * Y * a * b * c))

theorem determinant93 (a b c d Y T : ℂ) :
    (minor93 a b c d Y T).det = value93 a b c d Y T := by
  have hm0 : (minor93 a b c d Y T).submatrix Fin.succ (0 : Fin 6).succAbove =
      minor47 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor93 a b c d Y T).submatrix Fin.succ (1 : Fin 6).succAbove =
      minor78 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor93 a b c d Y T).submatrix Fin.succ (3 : Fin 6).succAbove =
      minor86 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm4 : (minor93 a b c d Y T).submatrix Fin.succ (4 : Fin 6).succAbove =
      minor90 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm5 : (minor93 a b c d Y T).submatrix Fin.succ (5 : Fin 6).succAbove =
      minor92 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor93 a b c d Y T).submatrix Fin.succ (0 : Fin 6).succAbove).det + ((-1 : ℂ)^1 * (((-2) * b) + (Y * c) + ((-5) * T * d)) * ((minor93 a b c d Y T).submatrix Fin.succ (1 : Fin 6).succAbove).det + ((-1 : ℂ)^2 * 0 * ((minor93 a b c d Y T).submatrix Fin.succ (2 : Fin 6).succAbove).det + ((-1 : ℂ)^3 * b * ((minor93 a b c d Y T).submatrix Fin.succ (3 : Fin 6).succAbove).det + ((-1 : ℂ)^4 * c * ((minor93 a b c d Y T).submatrix Fin.succ (4 : Fin 6).succAbove).det + ((-1 : ℂ)^5 * d * ((minor93 a b c d Y T).submatrix Fin.succ (5 : Fin 6).succAbove).det + (0)))))) = value93 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant47, hm1, determinant78, hm3, determinant86, hm4, determinant90, hm5, determinant92]
  dsimp only [value93, value47, value78, value86, value90, value92] <;> ring

def minor94 (a b c d Y T : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => match i.val, j.val with
    | _, _ => 0
def value94 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant94 (a b c d Y T : ℂ) :
    (minor94 a b c d Y T).det = value94 a b c d Y T := by
  rw [show value94 a b c d Y T = 0 by rfl]
  apply Matrix.det_eq_zero_of_row_eq_zero 0
  intro j
  fin_cases j <;> rfl

def minor95 (a b c d Y T : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (5 * Y)
    | 0, 2 => a
    | 2, 2 => 1
    | _, _ => 0
def value95 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant95 (a b c d Y T : ℂ) :
    (minor95 a b c d Y T).det = value95 a b c d Y T := by
  have hm0 : (minor95 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove =
      minor6 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor95 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove =
      minor94 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (5 * Y) * ((minor95 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove).det + ((-1 : ℂ)^1 * 0 * ((minor95 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove).det + ((-1 : ℂ)^2 * a * ((minor95 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove).det + (0))) = value95 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant6, hm2, determinant94]
  dsimp only [value95, value6, value94] <;> ring

def minor96 (a b c d Y T : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (5 * Y)
    | 1, 2 => 1
    | _, _ => 0
def value96 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant96 (a b c d Y T : ℂ) :
    (minor96 a b c d Y T).det = value96 a b c d Y T := by
  have hm0 : (minor96 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove =
      minor10 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (5 * Y) * ((minor96 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove).det + ((-1 : ℂ)^1 * 0 * ((minor96 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove).det + ((-1 : ℂ)^2 * 0 * ((minor96 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove).det + (0))) = value96 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant10]
  dsimp only [value96, value10] <;> ring

def minor97 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => ((-20) + ((-2) * T * a))
    | 0, 1 => 1
    | 0, 2 => a
    | 0, 3 => b
    | 1, 0 => (5 * Y)
    | 1, 3 => a
    | 2, 2 => 1
    | 3, 3 => 1
    | _, _ => 0
def value97 (a b c d Y T : ℂ) : ℂ := ((-5) * Y)

theorem determinant97 (a b c d Y T : ℂ) :
    (minor97 a b c d Y T).det = value97 a b c d Y T := by
  have hm0 : (minor97 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove =
      minor13 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor97 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove =
      minor70 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor97 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove =
      minor95 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor97 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove =
      minor96 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * ((-20) + ((-2) * T * a)) * ((minor97 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * 1 * ((minor97 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * a * ((minor97 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * b * ((minor97 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value97 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant13, hm1, determinant70, hm2, determinant95, hm3, determinant96]
  dsimp only [value97, value13, value70, value95, value96] <;> ring

def minor98 (a b c d Y T : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (5 * Y)
    | 0, 1 => (((-3) * T * b) + (3 * Y * a))
    | 1, 1 => ((-20) + ((-2) * T * a))
    | 2, 1 => (5 * Y)
    | _, _ => 0
def value98 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant98 (a b c d Y T : ℂ) :
    (minor98 a b c d Y T).det = value98 a b c d Y T := by
  have hm0 : (minor98 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove =
      minor18 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor98 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove =
      minor94 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (5 * Y) * ((minor98 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove).det + ((-1 : ℂ)^1 * (((-3) * T * b) + (3 * Y * a)) * ((minor98 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove).det + ((-1 : ℂ)^2 * 0 * ((minor98 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove).det + (0))) = value98 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant18, hm1, determinant94]
  dsimp only [value98, value18, value94] <;> ring

def minor99 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => ((-20) + ((-2) * T * a))
    | 0, 1 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 0, 2 => 1
    | 0, 3 => b
    | 1, 0 => (5 * Y)
    | 1, 1 => (((-3) * T * b) + (3 * Y * a))
    | 1, 3 => a
    | 2, 1 => ((-20) + ((-2) * T * a))
    | 3, 1 => (5 * Y)
    | 3, 3 => 1
    | _, _ => 0
def value99 (a b c d Y T : ℂ) : ℂ := (((-100) * Y) + ((-10) * T * Y * a))

theorem determinant99 (a b c d Y T : ℂ) :
    (minor99 a b c d Y T).det = value99 a b c d Y T := by
  have hm0 : (minor99 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove =
      minor19 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor99 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove =
      minor95 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor99 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove =
      minor72 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor99 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove =
      minor98 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * ((-20) + ((-2) * T * a)) * ((minor99 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor99 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * 1 * ((minor99 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * b * ((minor99 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value99 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant19, hm1, determinant95, hm2, determinant72, hm3, determinant98]
  dsimp only [value99, value19, value95, value72, value98] <;> ring

def minor100 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => ((-20) + ((-2) * T * a))
    | 0, 1 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 0, 2 => 1
    | 0, 3 => a
    | 1, 0 => (5 * Y)
    | 1, 1 => (((-3) * T * b) + (3 * Y * a))
    | 2, 1 => ((-20) + ((-2) * T * a))
    | 2, 3 => 1
    | 3, 1 => (5 * Y)
    | _, _ => 0
def value100 (a b c d Y T : ℂ) : ℂ := ((-25) * (Y^2))

theorem determinant100 (a b c d Y T : ℂ) :
    (minor100 a b c d Y T).det = value100 a b c d Y T := by
  have hm0 : (minor100 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove =
      minor20 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor100 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove =
      minor96 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor100 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove =
      minor73 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor100 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove =
      minor98 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * ((-20) + ((-2) * T * a)) * ((minor100 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor100 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * 1 * ((minor100 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * a * ((minor100 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value100 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant20, hm1, determinant96, hm2, determinant73, hm3, determinant98]
  dsimp only [value100, value20, value96, value73, value98] <;> ring

def minor101 (a b c d Y T : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (((-3) * T * b) + (3 * Y * a))
    | 0, 1 => (((-2) * b) + (Y * c) + ((-5) * T * d))
    | 0, 3 => b
    | 0, 4 => c
    | 1, 0 => ((-20) + ((-2) * T * a))
    | 1, 1 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 1, 2 => 1
    | 1, 3 => a
    | 1, 4 => b
    | 2, 0 => (5 * Y)
    | 2, 1 => (((-3) * T * b) + (3 * Y * a))
    | 2, 4 => a
    | 3, 1 => ((-20) + ((-2) * T * a))
    | 3, 3 => 1
    | 4, 1 => (5 * Y)
    | 4, 4 => 1
    | _, _ => 0
def value101 (a b c d Y T : ℂ) : ℂ := (((-20) * c * (Y^2)) + ((-9) * (T^2) * (b^2)) + (6 * (Y^2) * (a^2)) + (90 * Y * b) + ((-25) * T * Y * d) + (13 * T * Y * a * b))

theorem determinant101 (a b c d Y T : ℂ) :
    (minor101 a b c d Y T).det = value101 a b c d Y T := by
  have hm0 : (minor101 a b c d Y T).submatrix Fin.succ (0 : Fin 5).succAbove =
      minor21 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor101 a b c d Y T).submatrix Fin.succ (1 : Fin 5).succAbove =
      minor97 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor101 a b c d Y T).submatrix Fin.succ (3 : Fin 5).succAbove =
      minor99 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm4 : (minor101 a b c d Y T).submatrix Fin.succ (4 : Fin 5).succAbove =
      minor100 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (((-3) * T * b) + (3 * Y * a)) * ((minor101 a b c d Y T).submatrix Fin.succ (0 : Fin 5).succAbove).det + ((-1 : ℂ)^1 * (((-2) * b) + (Y * c) + ((-5) * T * d)) * ((minor101 a b c d Y T).submatrix Fin.succ (1 : Fin 5).succAbove).det + ((-1 : ℂ)^2 * 0 * ((minor101 a b c d Y T).submatrix Fin.succ (2 : Fin 5).succAbove).det + ((-1 : ℂ)^3 * b * ((minor101 a b c d Y T).submatrix Fin.succ (3 : Fin 5).succAbove).det + ((-1 : ℂ)^4 * c * ((minor101 a b c d Y T).submatrix Fin.succ (4 : Fin 5).succAbove).det + (0))))) = value101 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant21, hm1, determinant97, hm3, determinant99, hm4, determinant100]
  dsimp only [value101, value21, value97, value99, value100] <;> ring

def minor102 (a b c d Y T : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (5 * Y)
    | 0, 1 => ((-20) + ((-2) * T * a))
    | 1, 1 => (5 * Y)
    | _, _ => 0
def value102 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant102 (a b c d Y T : ℂ) :
    (minor102 a b c d Y T).det = value102 a b c d Y T := by
  have hm0 : (minor102 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove =
      minor48 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor102 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove =
      minor94 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (5 * Y) * ((minor102 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove).det + ((-1 : ℂ)^1 * ((-20) + ((-2) * T * a)) * ((minor102 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove).det + ((-1 : ℂ)^2 * 0 * ((minor102 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove).det + (0))) = value102 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant48, hm1, determinant94]
  dsimp only [value102, value48, value94] <;> ring

def minor103 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => ((-20) + ((-2) * T * a))
    | 0, 1 => (((-3) * T * b) + (3 * Y * a))
    | 0, 2 => 1
    | 0, 3 => b
    | 1, 0 => (5 * Y)
    | 1, 1 => ((-20) + ((-2) * T * a))
    | 1, 3 => a
    | 2, 1 => (5 * Y)
    | 3, 3 => 1
    | _, _ => 0
def value103 (a b c d Y T : ℂ) : ℂ := (25 * (Y^2))

theorem determinant103 (a b c d Y T : ℂ) :
    (minor103 a b c d Y T).det = value103 a b c d Y T := by
  have hm0 : (minor103 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove =
      minor49 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor103 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove =
      minor95 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor103 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove =
      minor80 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor103 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove =
      minor102 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * ((-20) + ((-2) * T * a)) * ((minor103 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * (((-3) * T * b) + (3 * Y * a)) * ((minor103 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * 1 * ((minor103 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * b * ((minor103 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value103 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant49, hm1, determinant95, hm2, determinant80, hm3, determinant102]
  dsimp only [value103, value49, value95, value80, value102] <;> ring

def minor104 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => ((-20) + ((-2) * T * a))
    | 0, 1 => (((-3) * T * b) + (3 * Y * a))
    | 0, 2 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 0, 3 => 1
    | 1, 0 => (5 * Y)
    | 1, 1 => ((-20) + ((-2) * T * a))
    | 1, 2 => (((-3) * T * b) + (3 * Y * a))
    | 2, 1 => (5 * Y)
    | 2, 2 => ((-20) + ((-2) * T * a))
    | 3, 2 => (5 * Y)
    | _, _ => 0
def value104 (a b c d Y T : ℂ) : ℂ := ((-125) * (Y^3))

theorem determinant104 (a b c d Y T : ℂ) :
    (minor104 a b c d Y T).det = value104 a b c d Y T := by
  have hm0 : (minor104 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove =
      minor52 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor104 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove =
      minor98 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor104 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove =
      minor102 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor104 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove =
      minor83 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * ((-20) + ((-2) * T * a)) * ((minor104 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * (((-3) * T * b) + (3 * Y * a)) * ((minor104 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor104 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * 1 * ((minor104 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value104 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant52, hm1, determinant98, hm2, determinant102, hm3, determinant83]
  dsimp only [value104, value52, value98, value102, value83] <;> ring

end Mordell.Determinants
