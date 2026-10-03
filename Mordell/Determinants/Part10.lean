import Mordell.Determinants.Part9

set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Mordell.Determinants

def minor150 (a b c d Y T : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 1 => (5 * Y)
    | 1, 2 => 1
    | _, _ => 0
def value150 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant150 (a b c d Y T : ℂ) :
    (minor150 a b c d Y T).det = value150 a b c d Y T := by
  have hm1 : (minor150 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove =
      minor121 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * 0 * ((minor150 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove).det + ((-1 : ℂ)^1 * (5 * Y) * ((minor150 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove).det + ((-1 : ℂ)^2 * 0 * ((minor150 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove).det + (0))) = value150 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm1, determinant121]
  dsimp only [value150, value121] <;> ring

def minor151 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (5 * Y)
    | 0, 1 => ((-20) + ((-2) * T * a))
    | 0, 2 => a
    | 0, 3 => b
    | 1, 1 => (5 * Y)
    | 1, 3 => a
    | 2, 2 => 1
    | 3, 3 => 1
    | _, _ => 0
def value151 (a b c d Y T : ℂ) : ℂ := (25 * (Y^2))

theorem determinant151 (a b c d Y T : ℂ) :
    (minor151 a b c d Y T).det = value151 a b c d Y T := by
  have hm0 : (minor151 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove =
      minor70 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor151 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove =
      minor124 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor151 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove =
      minor149 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor151 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove =
      minor150 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (5 * Y) * ((minor151 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * ((-20) + ((-2) * T * a)) * ((minor151 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * a * ((minor151 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * b * ((minor151 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value151 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant70, hm1, determinant124, hm2, determinant149, hm3, determinant150]
  dsimp only [value151, value70, value124, value149, value150] <;> ring

def minor152 (a b c d Y T : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 1 => (5 * Y)
    | 0, 2 => (((-3) * T * b) + (3 * Y * a))
    | 1, 2 => ((-20) + ((-2) * T * a))
    | 2, 2 => (5 * Y)
    | _, _ => 0
def value152 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant152 (a b c d Y T : ℂ) :
    (minor152 a b c d Y T).det = value152 a b c d Y T := by
  have hm1 : (minor152 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove =
      minor125 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor152 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove =
      minor148 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * 0 * ((minor152 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove).det + ((-1 : ℂ)^1 * (5 * Y) * ((minor152 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove).det + ((-1 : ℂ)^2 * (((-3) * T * b) + (3 * Y * a)) * ((minor152 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove).det + (0))) = value152 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm1, determinant125, hm2, determinant148]
  dsimp only [value152, value125, value148] <;> ring

def minor153 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (5 * Y)
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
def value153 (a b c d Y T : ℂ) : ℂ := (((-500) * (Y^2)) + ((-50) * T * a * (Y^2)))

theorem determinant153 (a b c d Y T : ℂ) :
    (minor153 a b c d Y T).det = value153 a b c d Y T := by
  have hm0 : (minor153 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove =
      minor72 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor153 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove =
      minor126 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor153 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove =
      minor149 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor153 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove =
      minor152 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (5 * Y) * ((minor153 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * ((-20) + ((-2) * T * a)) * ((minor153 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor153 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * b * ((minor153 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value153 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant72, hm1, determinant126, hm2, determinant149, hm3, determinant152]
  dsimp only [value153, value72, value126, value149, value152] <;> ring

def minor154 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (5 * Y)
    | 0, 1 => ((-20) + ((-2) * T * a))
    | 0, 2 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 0, 3 => a
    | 1, 1 => (5 * Y)
    | 1, 2 => (((-3) * T * b) + (3 * Y * a))
    | 2, 2 => ((-20) + ((-2) * T * a))
    | 2, 3 => 1
    | 3, 2 => (5 * Y)
    | _, _ => 0
def value154 (a b c d Y T : ℂ) : ℂ := ((-125) * (Y^3))

theorem determinant154 (a b c d Y T : ℂ) :
    (minor154 a b c d Y T).det = value154 a b c d Y T := by
  have hm0 : (minor154 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove =
      minor73 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor154 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove =
      minor127 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor154 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove =
      minor150 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor154 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove =
      minor152 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (5 * Y) * ((minor154 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * ((-20) + ((-2) * T * a)) * ((minor154 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor154 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * a * ((minor154 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value154 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant73, hm1, determinant127, hm2, determinant150, hm3, determinant152]
  dsimp only [value154, value73, value127, value150, value152] <;> ring

def minor155 (a b c d Y T : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => ((-20) + ((-2) * T * a))
    | 0, 1 => (((-3) * T * b) + (3 * Y * a))
    | 0, 2 => (((-2) * b) + (Y * c) + ((-5) * T * d))
    | 0, 3 => b
    | 0, 4 => c
    | 1, 0 => (5 * Y)
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
def value155 (a b c d Y T : ℂ) : ℂ := (((-1200) * T * b) + ((-100) * c * (Y^3)) + (30 * (Y^3) * (a^2)) + (150 * b * (Y^2)) + (600 * Y * a) + ((-400) * T * Y * c) + ((-240) * a * b * (T^2)) + ((-125) * T * d * (Y^2)) + ((-45) * Y * (T^2) * (b^2)) + ((-12) * b * (T^3) * (a^2)) + (12 * Y * (T^2) * (a^3)) + (180 * T * Y * (a^2)) + ((-40) * Y * a * c * (T^2)) + (35 * T * a * b * (Y^2)))

theorem determinant155 (a b c d Y T : ℂ) :
    (minor155 a b c d Y T).det = value155 a b c d Y T := by
  have hm0 : (minor155 a b c d Y T).submatrix Fin.succ (0 : Fin 5).succAbove =
      minor74 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor155 a b c d Y T).submatrix Fin.succ (1 : Fin 5).succAbove =
      minor128 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor155 a b c d Y T).submatrix Fin.succ (2 : Fin 5).succAbove =
      minor151 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor155 a b c d Y T).submatrix Fin.succ (3 : Fin 5).succAbove =
      minor153 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm4 : (minor155 a b c d Y T).submatrix Fin.succ (4 : Fin 5).succAbove =
      minor154 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * ((-20) + ((-2) * T * a)) * ((minor155 a b c d Y T).submatrix Fin.succ (0 : Fin 5).succAbove).det + ((-1 : ℂ)^1 * (((-3) * T * b) + (3 * Y * a)) * ((minor155 a b c d Y T).submatrix Fin.succ (1 : Fin 5).succAbove).det + ((-1 : ℂ)^2 * (((-2) * b) + (Y * c) + ((-5) * T * d)) * ((minor155 a b c d Y T).submatrix Fin.succ (2 : Fin 5).succAbove).det + ((-1 : ℂ)^3 * b * ((minor155 a b c d Y T).submatrix Fin.succ (3 : Fin 5).succAbove).det + ((-1 : ℂ)^4 * c * ((minor155 a b c d Y T).submatrix Fin.succ (4 : Fin 5).succAbove).det + (0))))) = value155 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant74, hm1, determinant128, hm2, determinant151, hm3, determinant153, hm4, determinant154]
  dsimp only [value155, value74, value128, value151, value153, value154] <;> ring

def minor156 (a b c d Y T : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 1 => (5 * Y)
    | 0, 2 => ((-20) + ((-2) * T * a))
    | 1, 2 => (5 * Y)
    | _, _ => 0
def value156 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant156 (a b c d Y T : ℂ) :
    (minor156 a b c d Y T).det = value156 a b c d Y T := by
  have hm1 : (minor156 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove =
      minor133 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor156 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove =
      minor148 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * 0 * ((minor156 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove).det + ((-1 : ℂ)^1 * (5 * Y) * ((minor156 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove).det + ((-1 : ℂ)^2 * ((-20) + ((-2) * T * a)) * ((minor156 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove).det + (0))) = value156 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm1, determinant133, hm2, determinant148]
  dsimp only [value156, value133, value148] <;> ring

def minor157 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (5 * Y)
    | 0, 1 => ((-20) + ((-2) * T * a))
    | 0, 2 => (((-3) * T * b) + (3 * Y * a))
    | 0, 3 => b
    | 1, 1 => (5 * Y)
    | 1, 2 => ((-20) + ((-2) * T * a))
    | 1, 3 => a
    | 2, 2 => (5 * Y)
    | 3, 3 => 1
    | _, _ => 0
def value157 (a b c d Y T : ℂ) : ℂ := (125 * (Y^3))

theorem determinant157 (a b c d Y T : ℂ) :
    (minor157 a b c d Y T).det = value157 a b c d Y T := by
  have hm0 : (minor157 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove =
      minor80 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor157 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove =
      minor134 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor157 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove =
      minor149 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor157 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove =
      minor156 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (5 * Y) * ((minor157 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * ((-20) + ((-2) * T * a)) * ((minor157 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * (((-3) * T * b) + (3 * Y * a)) * ((minor157 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * b * ((minor157 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value157 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant80, hm1, determinant134, hm2, determinant149, hm3, determinant156]
  dsimp only [value157, value80, value134, value149, value156] <;> ring

def minor158 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (5 * Y)
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
def value158 (a b c d Y T : ℂ) : ℂ := (625 * (Y^4))

theorem determinant158 (a b c d Y T : ℂ) :
    (minor158 a b c d Y T).det = value158 a b c d Y T := by
  have hm0 : (minor158 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove =
      minor83 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor158 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove =
      minor137 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor158 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove =
      minor152 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor158 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove =
      minor156 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (5 * Y) * ((minor158 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * ((-20) + ((-2) * T * a)) * ((minor158 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * (((-3) * T * b) + (3 * Y * a)) * ((minor158 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor158 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value158 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant83, hm1, determinant137, hm2, determinant152, hm3, determinant156]
  dsimp only [value158, value83, value137, value152, value156] <;> ring

def minor159 (a b c d Y T : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => ((-20) + ((-2) * T * a))
    | 0, 1 => (((-3) * T * b) + (3 * Y * a))
    | 0, 2 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 0, 3 => (((-2) * b) + (Y * c) + ((-5) * T * d))
    | 0, 4 => c
    | 1, 0 => (5 * Y)
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
def value159 (a b c d Y T : ℂ) : ℂ := (160000 + ((-2000) * a * (Y^2)) + ((-150) * (Y^4) * (a^2)) + (16 * (T^4) * (a^4)) + (500 * c * (Y^4)) + (640 * (T^3) * (a^3)) + (750 * b * (Y^3)) + (9600 * (T^2) * (a^2)) + (64000 * T * a) + ((-1000) * T * (Y^2) * (a^2)) + ((-80) * (T^2) * (Y^2) * (a^3)) + (225 * (T^2) * (Y^2) * (b^2)) + (625 * T * d * (Y^3)) + (4000 * T * c * (Y^2)) + (18000 * T * Y * b) + ((-25) * T * a * b * (Y^3)) + (180 * Y * b * (T^3) * (a^2)) + (400 * a * c * (T^2) * (Y^2)) + (3600 * Y * a * b * (T^2)))

theorem determinant159 (a b c d Y T : ℂ) :
    (minor159 a b c d Y T).det = value159 a b c d Y T := by
  have hm0 : (minor159 a b c d Y T).submatrix Fin.succ (0 : Fin 5).succAbove =
      minor84 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor159 a b c d Y T).submatrix Fin.succ (1 : Fin 5).succAbove =
      minor138 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor159 a b c d Y T).submatrix Fin.succ (2 : Fin 5).succAbove =
      minor153 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor159 a b c d Y T).submatrix Fin.succ (3 : Fin 5).succAbove =
      minor157 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm4 : (minor159 a b c d Y T).submatrix Fin.succ (4 : Fin 5).succAbove =
      minor158 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * ((-20) + ((-2) * T * a)) * ((minor159 a b c d Y T).submatrix Fin.succ (0 : Fin 5).succAbove).det + ((-1 : ℂ)^1 * (((-3) * T * b) + (3 * Y * a)) * ((minor159 a b c d Y T).submatrix Fin.succ (1 : Fin 5).succAbove).det + ((-1 : ℂ)^2 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor159 a b c d Y T).submatrix Fin.succ (2 : Fin 5).succAbove).det + ((-1 : ℂ)^3 * (((-2) * b) + (Y * c) + ((-5) * T * d)) * ((minor159 a b c d Y T).submatrix Fin.succ (3 : Fin 5).succAbove).det + ((-1 : ℂ)^4 * c * ((minor159 a b c d Y T).submatrix Fin.succ (4 : Fin 5).succAbove).det + (0))))) = value159 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant84, hm1, determinant138, hm2, determinant153, hm3, determinant157, hm4, determinant158]
  dsimp only [value159, value84, value138, value153, value157, value158] <;> ring

def minor160 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (5 * Y)
    | 0, 1 => ((-20) + ((-2) * T * a))
    | 0, 2 => (((-3) * T * b) + (3 * Y * a))
    | 0, 3 => a
    | 1, 1 => (5 * Y)
    | 1, 2 => ((-20) + ((-2) * T * a))
    | 2, 2 => (5 * Y)
    | 2, 3 => 1
    | _, _ => 0
def value160 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant160 (a b c d Y T : ℂ) :
    (minor160 a b c d Y T).det = value160 a b c d Y T := by
  have hm0 : (minor160 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove =
      minor81 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor160 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove =
      minor135 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor160 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove =
      minor150 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor160 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove =
      minor156 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (5 * Y) * ((minor160 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * ((-20) + ((-2) * T * a)) * ((minor160 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * (((-3) * T * b) + (3 * Y * a)) * ((minor160 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * a * ((minor160 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value160 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant81, hm1, determinant135, hm2, determinant150, hm3, determinant156]
  dsimp only [value160, value81, value135, value150, value156] <;> ring

def minor161 (a b c d Y T : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => ((-20) + ((-2) * T * a))
    | 0, 1 => (((-3) * T * b) + (3 * Y * a))
    | 0, 2 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 0, 3 => (((-2) * b) + (Y * c) + ((-5) * T * d))
    | 0, 4 => b
    | 1, 0 => (5 * Y)
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
def value161 (a b c d Y T : ℂ) : ℂ := ((40000 * Y) + (250 * a * (Y^3)) + (375 * b * (Y^4)) + ((-50) * T * (Y^3) * (a^2)) + (40 * Y * (T^3) * (a^3)) + (500 * T * c * (Y^3)) + (1200 * Y * (T^2) * (a^2)) + (3000 * T * b * (Y^2)) + (12000 * T * Y * a) + (300 * a * b * (T^2) * (Y^2)))

theorem determinant161 (a b c d Y T : ℂ) :
    (minor161 a b c d Y T).det = value161 a b c d Y T := by
  have hm0 : (minor161 a b c d Y T).submatrix Fin.succ (0 : Fin 5).succAbove =
      minor85 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor161 a b c d Y T).submatrix Fin.succ (1 : Fin 5).succAbove =
      minor139 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor161 a b c d Y T).submatrix Fin.succ (2 : Fin 5).succAbove =
      minor154 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor161 a b c d Y T).submatrix Fin.succ (3 : Fin 5).succAbove =
      minor160 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm4 : (minor161 a b c d Y T).submatrix Fin.succ (4 : Fin 5).succAbove =
      minor158 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * ((-20) + ((-2) * T * a)) * ((minor161 a b c d Y T).submatrix Fin.succ (0 : Fin 5).succAbove).det + ((-1 : ℂ)^1 * (((-3) * T * b) + (3 * Y * a)) * ((minor161 a b c d Y T).submatrix Fin.succ (1 : Fin 5).succAbove).det + ((-1 : ℂ)^2 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor161 a b c d Y T).submatrix Fin.succ (2 : Fin 5).succAbove).det + ((-1 : ℂ)^3 * (((-2) * b) + (Y * c) + ((-5) * T * d)) * ((minor161 a b c d Y T).submatrix Fin.succ (3 : Fin 5).succAbove).det + ((-1 : ℂ)^4 * b * ((minor161 a b c d Y T).submatrix Fin.succ (4 : Fin 5).succAbove).det + (0))))) = value161 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant85, hm1, determinant139, hm2, determinant154, hm3, determinant160, hm4, determinant158]
  dsimp only [value161, value85, value139, value154, value160, value158] <;> ring

def minor162 (a b c d Y T : ℂ) : Matrix (Fin 6) (Fin 6) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (((-3) * T * b) + (3 * Y * a))
    | 0, 1 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 0, 2 => (((-2) * b) + (Y * c) + ((-5) * T * d))
    | 0, 4 => c
    | 0, 5 => d
    | 1, 0 => ((-20) + ((-2) * T * a))
    | 1, 1 => (((-3) * T * b) + (3 * Y * a))
    | 1, 2 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 1, 3 => (((-2) * b) + (Y * c) + ((-5) * T * d))
    | 1, 4 => b
    | 1, 5 => c
    | 2, 0 => (5 * Y)
    | 2, 1 => ((-20) + ((-2) * T * a))
    | 2, 2 => (((-3) * T * b) + (3 * Y * a))
    | 2, 3 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 2, 4 => a
    | 2, 5 => b
    | 3, 1 => (5 * Y)
    | 3, 2 => ((-20) + ((-2) * T * a))
    | 3, 3 => (((-3) * T * b) + (3 * Y * a))
    | 3, 5 => a
    | 4, 2 => (5 * Y)
    | 4, 3 => ((-20) + ((-2) * T * a))
    | 4, 4 => 1
    | 5, 3 => (5 * Y)
    | 5, 5 => 1
    | _, _ => 0
def value162 (a b c d Y T : ℂ) : ℂ := (((-33600) * (a^2)) + (160000 * c) + ((-40000) * Y * d) + ((-19200) * T * (b^2)) + ((-11520) * T * (a^3)) + ((-1296) * (T^2) * (a^4)) + ((-48) * (T^3) * (a^5)) + (36 * (Y^4) * (a^4)) + (81 * (T^4) * (b^4)) + (400 * (Y^4) * (c^2)) + (900 * (Y^2) * (b^2)) + (1140 * (Y^2) * (a^3)) + (6400 * (T^2) * (c^2)) + ((-5880) * a * (T^2) * (b^2)) + ((-3800) * a * c * (Y^2)) + ((-2160) * c * (T^3) * (b^2)) + ((-1440) * Y * (T^2) * (b^3)) + ((-375) * b * d * (Y^4)) + ((-276) * (T^3) * (a^2) * (b^2)) + ((-250) * a * d * (Y^3)) + ((-240) * c * (Y^4) * (a^2)) + ((-128) * c * (T^3) * (a^3)) + ((-45) * T * (Y^3) * (b^3)) + ((-16) * c * (T^4) * (a^4)) + (12 * (T^4) * (a^3) * (b^2)) + (36 * (T^2) * (Y^2) * (a^5)) + (40 * b * (Y^3) * (a^2)) + (64 * (T^4) * (a^2) * (c^2)) + (195 * a * (Y^4) * (b^2)) + (300 * b * c * (Y^3)) + (456 * T * (Y^2) * (a^4)) + (625 * (T^2) * (Y^2) * (d^2)) + (1280 * a * (T^3) * (c^2)) + (3840 * c * (T^2) * (a^2)) + (5200 * T * (Y^2) * (c^2)) + (12000 * b * d * (T^2)) + (28000 * Y * a * b) + (51200 * T * a * c) + ((-18000) * T * Y * a * d) + ((-4500) * T * b * d * (Y^2)) + ((-3060) * T * c * (Y^2) * (a^2)) + ((-3000) * Y * d * (T^2) * (a^2)) + ((-480) * Y * b * (T^3) * (c^2)) + ((-292) * c * (T^2) * (Y^2) * (a^3)) + ((-250) * T * d * (Y^3) * (a^2)) + ((-216) * Y * a * (T^3) * (b^3)) + ((-216) * a * c * (T^4) * (b^2)) + ((-160) * Y * d * (T^3) * (a^3)) + ((-96) * Y * b * (T^2) * (a^3)) + ((-60) * c * (T^2) * (Y^2) * (b^2)) + ((-32) * Y * b * (T^3) * (a^4)) + (4 * T * b * (Y^3) * (a^3)) + (120 * b * d * (T^4) * (a^2)) + (211 * (T^2) * (Y^2) * (a^2) * (b^2)) + (450 * Y * d * (T^3) * (b^2)) + (500 * T * c * d * (Y^3)) + (600 * a * (T^2) * (Y^2) * (c^2)) + (2400 * a * b * d * (T^3)) + (2490 * T * a * (Y^2) * (b^2)) + (3960 * T * Y * b * (a^2)) + (4000 * Y * c * d * (T^2)) + (16800 * T * Y * b * c) + ((-650) * a * b * d * (T^2) * (Y^2)) + (190 * T * a * b * c * (Y^3)) + (344 * Y * b * c * (T^3) * (a^2)) + (400 * Y * a * c * d * (T^3)) + (3680 * Y * a * b * c * (T^2)))

theorem determinant162 (a b c d Y T : ℂ) :
    (minor162 a b c d Y T).det = value162 a b c d Y T := by
  have hm0 : (minor162 a b c d Y T).submatrix Fin.succ (0 : Fin 6).succAbove =
      minor86 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor162 a b c d Y T).submatrix Fin.succ (1 : Fin 6).succAbove =
      minor140 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor162 a b c d Y T).submatrix Fin.succ (2 : Fin 6).succAbove =
      minor155 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm4 : (minor162 a b c d Y T).submatrix Fin.succ (4 : Fin 6).succAbove =
      minor159 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm5 : (minor162 a b c d Y T).submatrix Fin.succ (5 : Fin 6).succAbove =
      minor161 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (((-3) * T * b) + (3 * Y * a)) * ((minor162 a b c d Y T).submatrix Fin.succ (0 : Fin 6).succAbove).det + ((-1 : ℂ)^1 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor162 a b c d Y T).submatrix Fin.succ (1 : Fin 6).succAbove).det + ((-1 : ℂ)^2 * (((-2) * b) + (Y * c) + ((-5) * T * d)) * ((minor162 a b c d Y T).submatrix Fin.succ (2 : Fin 6).succAbove).det + ((-1 : ℂ)^3 * 0 * ((minor162 a b c d Y T).submatrix Fin.succ (3 : Fin 6).succAbove).det + ((-1 : ℂ)^4 * c * ((minor162 a b c d Y T).submatrix Fin.succ (4 : Fin 6).succAbove).det + ((-1 : ℂ)^5 * d * ((minor162 a b c d Y T).submatrix Fin.succ (5 : Fin 6).succAbove).det + (0)))))) = value162 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant86, hm1, determinant140, hm2, determinant155, hm4, determinant159, hm5, determinant161]
  dsimp only [value162, value86, value140, value155, value159, value161] <;> ring

def minor163 (a b c d Y T : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 1 => (5 * Y)
    | 0, 2 => 1
    | _, _ => 0
def value163 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant163 (a b c d Y T : ℂ) :
    (minor163 a b c d Y T).det = value163 a b c d Y T := by
  have hm1 : (minor163 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove =
      minor118 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor163 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove =
      minor148 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * 0 * ((minor163 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove).det + ((-1 : ℂ)^1 * (5 * Y) * ((minor163 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove).det + ((-1 : ℂ)^2 * 1 * ((minor163 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove).det + (0))) = value163 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm1, determinant118, hm2, determinant148]
  dsimp only [value163, value118, value148] <;> ring

def minor164 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (5 * Y)
    | 0, 1 => ((-20) + ((-2) * T * a))
    | 0, 3 => b
    | 1, 1 => (5 * Y)
    | 1, 2 => 1
    | 1, 3 => a
    | 3, 3 => 1
    | _, _ => 0
def value164 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant164 (a b c d Y T : ℂ) :
    (minor164 a b c d Y T).det = value164 a b c d Y T := by
  have hm0 : (minor164 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove =
      minor65 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor164 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove =
      minor119 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor164 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove =
      minor163 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (5 * Y) * ((minor164 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * ((-20) + ((-2) * T * a)) * ((minor164 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * 0 * ((minor164 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * b * ((minor164 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value164 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant65, hm1, determinant119, hm3, determinant163]
  dsimp only [value164, value65, value119, value163] <;> ring

end Mordell.Determinants
