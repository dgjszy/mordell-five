import Mordell.Determinants.Part2

set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Mordell.Determinants

def minor45 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (((-3) * T * b) + (3 * Y * a))
    | 0, 1 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 0, 3 => b
    | 1, 0 => ((-20) + ((-2) * T * a))
    | 1, 1 => (((-3) * T * b) + (3 * Y * a))
    | 1, 2 => 1
    | 1, 3 => a
    | 2, 0 => (5 * Y)
    | 2, 1 => ((-20) + ((-2) * T * a))
    | 3, 1 => (5 * Y)
    | 3, 3 => 1
    | _, _ => 0
def value45 (a b c d Y T : ℂ) : ℂ := (((-60) * T * b) + ((-15) * b * (Y^2)) + (30 * Y * a) + ((-20) * T * Y * c) + ((-6) * a * b * (T^2)) + (6 * T * Y * (a^2)))

theorem determinant45 (a b c d Y T : ℂ) :
    (minor45 a b c d Y T).det = value45 a b c d Y T := by
  have hm0 : (minor45 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove =
      minor25 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor45 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove =
      minor34 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor45 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove =
      minor44 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (((-3) * T * b) + (3 * Y * a)) * ((minor45 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor45 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * 0 * ((minor45 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * b * ((minor45 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value45 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant25, hm1, determinant34, hm3, determinant44]
  dsimp only [value45, value25, value34, value44] <;> ring

def minor46 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (((-3) * T * b) + (3 * Y * a))
    | 0, 1 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 0, 3 => a
    | 1, 0 => ((-20) + ((-2) * T * a))
    | 1, 1 => (((-3) * T * b) + (3 * Y * a))
    | 1, 2 => 1
    | 2, 0 => (5 * Y)
    | 2, 1 => ((-20) + ((-2) * T * a))
    | 2, 3 => 1
    | 3, 1 => (5 * Y)
    | _, _ => 0
def value46 (a b c d Y T : ℂ) : ℂ := (((-10) * a * (Y^2)) + ((-15) * T * Y * b))

theorem determinant46 (a b c d Y T : ℂ) :
    (minor46 a b c d Y T).det = value46 a b c d Y T := by
  have hm0 : (minor46 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove =
      minor28 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor46 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove =
      minor37 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor46 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove =
      minor44 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (((-3) * T * b) + (3 * Y * a)) * ((minor46 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor46 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * 0 * ((minor46 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * a * ((minor46 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value46 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant28, hm1, determinant37, hm3, determinant44]
  dsimp only [value46, value28, value37, value44] <;> ring

def minor47 (a b c d Y T : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 0, 1 => (((-2) * b) + (Y * c) + ((-5) * T * d))
    | 0, 2 => a
    | 0, 3 => b
    | 0, 4 => c
    | 1, 0 => (((-3) * T * b) + (3 * Y * a))
    | 1, 1 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 1, 3 => a
    | 1, 4 => b
    | 2, 0 => ((-20) + ((-2) * T * a))
    | 2, 1 => (((-3) * T * b) + (3 * Y * a))
    | 2, 2 => 1
    | 2, 4 => a
    | 3, 0 => (5 * Y)
    | 3, 1 => ((-20) + ((-2) * T * a))
    | 3, 3 => 1
    | 4, 1 => (5 * Y)
    | 4, 4 => 1
    | _, _ => 0
def value47 (a b c d Y T : ℂ) : ℂ := ((196 * (a^2)) + (4 * (T^2) * (a^4)) + (4 * (Y^2) * (a^3)) + (9 * (Y^2) * (b^2)) + (16 * (T^2) * (c^2)) + (54 * T * (b^2)) + (56 * T * (a^3)) + ((-112) * T * a * c) + ((-48) * Y * a * b) + ((-16) * c * (T^2) * (a^2)) + ((-15) * b * d * (T^2)) + ((-8) * a * c * (Y^2)) + (15 * a * (T^2) * (b^2)) + ((-10) * T * Y * a * d) + (4 * T * Y * b * (a^2)) + (12 * T * Y * b * c))

theorem determinant47 (a b c d Y T : ℂ) :
    (minor47 a b c d Y T).det = value47 a b c d Y T := by
  have hm0 : (minor47 a b c d Y T).submatrix Fin.succ (0 : Fin 5).succAbove =
      minor31 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor47 a b c d Y T).submatrix Fin.succ (1 : Fin 5).succAbove =
      minor38 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor47 a b c d Y T).submatrix Fin.succ (2 : Fin 5).succAbove =
      minor43 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor47 a b c d Y T).submatrix Fin.succ (3 : Fin 5).succAbove =
      minor45 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm4 : (minor47 a b c d Y T).submatrix Fin.succ (4 : Fin 5).succAbove =
      minor46 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor47 a b c d Y T).submatrix Fin.succ (0 : Fin 5).succAbove).det + ((-1 : ℂ)^1 * (((-2) * b) + (Y * c) + ((-5) * T * d)) * ((minor47 a b c d Y T).submatrix Fin.succ (1 : Fin 5).succAbove).det + ((-1 : ℂ)^2 * a * ((minor47 a b c d Y T).submatrix Fin.succ (2 : Fin 5).succAbove).det + ((-1 : ℂ)^3 * b * ((minor47 a b c d Y T).submatrix Fin.succ (3 : Fin 5).succAbove).det + ((-1 : ℂ)^4 * c * ((minor47 a b c d Y T).submatrix Fin.succ (4 : Fin 5).succAbove).det + (0))))) = value47 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant31, hm1, determinant38, hm2, determinant43, hm3, determinant45, hm4, determinant46]
  dsimp only [value47, value31, value38, value43, value45, value46] <;> ring

def minor48 (a b c d Y T : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (5 * Y)
    | _, _ => 0
def value48 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant48 (a b c d Y T : ℂ) :
    (minor48 a b c d Y T).det = value48 a b c d Y T := by
  have hm0 : (minor48 a b c d Y T).submatrix Fin.succ (0 : Fin 2).succAbove =
      minor9 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (5 * Y) * ((minor48 a b c d Y T).submatrix Fin.succ (0 : Fin 2).succAbove).det + ((-1 : ℂ)^1 * 0 * ((minor48 a b c d Y T).submatrix Fin.succ (1 : Fin 2).succAbove).det + (0)) = value48 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant9]
  dsimp only [value48, value9] <;> ring

def minor49 (a b c d Y T : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => ((-20) + ((-2) * T * a))
    | 0, 2 => a
    | 1, 0 => (5 * Y)
    | 2, 2 => 1
    | _, _ => 0
def value49 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant49 (a b c d Y T : ℂ) :
    (minor49 a b c d Y T).det = value49 a b c d Y T := by
  have hm0 : (minor49 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove =
      minor6 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor49 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove =
      minor48 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * ((-20) + ((-2) * T * a)) * ((minor49 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove).det + ((-1 : ℂ)^1 * 0 * ((minor49 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove).det + ((-1 : ℂ)^2 * a * ((minor49 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove).det + (0))) = value49 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant6, hm2, determinant48]
  dsimp only [value49, value6, value48] <;> ring

def minor50 (a b c d Y T : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => ((-20) + ((-2) * T * a))
    | 1, 0 => (5 * Y)
    | 1, 2 => 1
    | _, _ => 0
def value50 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant50 (a b c d Y T : ℂ) :
    (minor50 a b c d Y T).det = value50 a b c d Y T := by
  have hm0 : (minor50 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove =
      minor10 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * ((-20) + ((-2) * T * a)) * ((minor50 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove).det + ((-1 : ℂ)^1 * 0 * ((minor50 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove).det + ((-1 : ℂ)^2 * 0 * ((minor50 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove).det + (0))) = value50 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant10]
  dsimp only [value50, value10] <;> ring

def minor51 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (((-3) * T * b) + (3 * Y * a))
    | 0, 1 => 1
    | 0, 2 => a
    | 0, 3 => b
    | 1, 0 => ((-20) + ((-2) * T * a))
    | 1, 3 => a
    | 2, 0 => (5 * Y)
    | 2, 2 => 1
    | 3, 3 => 1
    | _, _ => 0
def value51 (a b c d Y T : ℂ) : ℂ := (20 + (2 * T * a))

theorem determinant51 (a b c d Y T : ℂ) :
    (minor51 a b c d Y T).det = value51 a b c d Y T := by
  have hm0 : (minor51 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove =
      minor13 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor51 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove =
      minor39 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor51 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove =
      minor49 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor51 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove =
      minor50 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (((-3) * T * b) + (3 * Y * a)) * ((minor51 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * 1 * ((minor51 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * a * ((minor51 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * b * ((minor51 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value51 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant13, hm1, determinant39, hm2, determinant49, hm3, determinant50]
  dsimp only [value51, value13, value39, value49, value50] <;> ring

def minor52 (a b c d Y T : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => ((-20) + ((-2) * T * a))
    | 0, 1 => (((-3) * T * b) + (3 * Y * a))
    | 1, 0 => (5 * Y)
    | 1, 1 => ((-20) + ((-2) * T * a))
    | 2, 1 => (5 * Y)
    | _, _ => 0
def value52 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant52 (a b c d Y T : ℂ) :
    (minor52 a b c d Y T).det = value52 a b c d Y T := by
  have hm0 : (minor52 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove =
      minor18 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor52 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove =
      minor48 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * ((-20) + ((-2) * T * a)) * ((minor52 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove).det + ((-1 : ℂ)^1 * (((-3) * T * b) + (3 * Y * a)) * ((minor52 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove).det + ((-1 : ℂ)^2 * 0 * ((minor52 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove).det + (0))) = value52 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant18, hm1, determinant48]
  dsimp only [value52, value18, value48] <;> ring

def minor53 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (((-3) * T * b) + (3 * Y * a))
    | 0, 1 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 0, 2 => 1
    | 0, 3 => b
    | 1, 0 => ((-20) + ((-2) * T * a))
    | 1, 1 => (((-3) * T * b) + (3 * Y * a))
    | 1, 3 => a
    | 2, 0 => (5 * Y)
    | 2, 1 => ((-20) + ((-2) * T * a))
    | 3, 1 => (5 * Y)
    | 3, 3 => 1
    | _, _ => 0
def value53 (a b c d Y T : ℂ) : ℂ := (400 + (4 * (T^2) * (a^2)) + (10 * a * (Y^2)) + (80 * T * a) + (15 * T * Y * b))

theorem determinant53 (a b c d Y T : ℂ) :
    (minor53 a b c d Y T).det = value53 a b c d Y T := by
  have hm0 : (minor53 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove =
      minor19 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor53 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove =
      minor49 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor53 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove =
      minor41 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor53 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove =
      minor52 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (((-3) * T * b) + (3 * Y * a)) * ((minor53 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor53 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * 1 * ((minor53 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * b * ((minor53 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value53 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant19, hm1, determinant49, hm2, determinant41, hm3, determinant52]
  dsimp only [value53, value19, value49, value41, value52] <;> ring

def minor54 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (((-3) * T * b) + (3 * Y * a))
    | 0, 1 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 0, 2 => 1
    | 0, 3 => a
    | 1, 0 => ((-20) + ((-2) * T * a))
    | 1, 1 => (((-3) * T * b) + (3 * Y * a))
    | 2, 0 => (5 * Y)
    | 2, 1 => ((-20) + ((-2) * T * a))
    | 2, 3 => 1
    | 3, 1 => (5 * Y)
    | _, _ => 0
def value54 (a b c d Y T : ℂ) : ℂ := ((100 * Y) + (10 * T * Y * a))

theorem determinant54 (a b c d Y T : ℂ) :
    (minor54 a b c d Y T).det = value54 a b c d Y T := by
  have hm0 : (minor54 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove =
      minor20 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor54 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove =
      minor50 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor54 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove =
      minor42 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor54 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove =
      minor52 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (((-3) * T * b) + (3 * Y * a)) * ((minor54 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor54 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * 1 * ((minor54 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * a * ((minor54 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value54 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant20, hm1, determinant50, hm2, determinant42, hm3, determinant52]
  dsimp only [value54, value20, value50, value42, value52] <;> ring

def minor55 (a b c d Y T : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 0, 1 => (((-2) * b) + (Y * c) + ((-5) * T * d))
    | 0, 3 => b
    | 0, 4 => c
    | 1, 0 => (((-3) * T * b) + (3 * Y * a))
    | 1, 1 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 1, 2 => 1
    | 1, 3 => a
    | 1, 4 => b
    | 2, 0 => ((-20) + ((-2) * T * a))
    | 2, 1 => (((-3) * T * b) + (3 * Y * a))
    | 2, 4 => a
    | 3, 0 => (5 * Y)
    | 3, 1 => ((-20) + ((-2) * T * a))
    | 3, 3 => 1
    | 4, 1 => (5 * Y)
    | 4, 4 => 1
    | _, _ => 0
def value55 (a b c d Y T : ℂ) : ℂ := (((-360) * b) + ((-12) * Y * (a^2)) + (80 * Y * c) + (100 * T * d) + ((-94) * T * a * b) + ((-12) * b * c * (T^2)) + ((-9) * T * Y * (b^2)) + ((-6) * a * b * (Y^2)) + ((-4) * b * (T^2) * (a^2)) + (10 * a * d * (T^2)))

theorem determinant55 (a b c d Y T : ℂ) :
    (minor55 a b c d Y T).det = value55 a b c d Y T := by
  have hm0 : (minor55 a b c d Y T).submatrix Fin.succ (0 : Fin 5).succAbove =
      minor21 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor55 a b c d Y T).submatrix Fin.succ (1 : Fin 5).succAbove =
      minor51 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor55 a b c d Y T).submatrix Fin.succ (3 : Fin 5).succAbove =
      minor53 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm4 : (minor55 a b c d Y T).submatrix Fin.succ (4 : Fin 5).succAbove =
      minor54 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor55 a b c d Y T).submatrix Fin.succ (0 : Fin 5).succAbove).det + ((-1 : ℂ)^1 * (((-2) * b) + (Y * c) + ((-5) * T * d)) * ((minor55 a b c d Y T).submatrix Fin.succ (1 : Fin 5).succAbove).det + ((-1 : ℂ)^2 * 0 * ((minor55 a b c d Y T).submatrix Fin.succ (2 : Fin 5).succAbove).det + ((-1 : ℂ)^3 * b * ((minor55 a b c d Y T).submatrix Fin.succ (3 : Fin 5).succAbove).det + ((-1 : ℂ)^4 * c * ((minor55 a b c d Y T).submatrix Fin.succ (4 : Fin 5).succAbove).det + (0))))) = value55 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant21, hm1, determinant51, hm3, determinant53, hm4, determinant54]
  dsimp only [value55, value21, value51, value53, value54] <;> ring

def minor56 (a b c d Y T : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => ((-20) + ((-2) * T * a))
    | 0, 2 => 1
    | 1, 0 => (5 * Y)
    | _, _ => 0
def value56 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant56 (a b c d Y T : ℂ) :
    (minor56 a b c d Y T).det = value56 a b c d Y T := by
  have hm0 : (minor56 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove =
      minor7 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor56 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove =
      minor48 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * ((-20) + ((-2) * T * a)) * ((minor56 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove).det + ((-1 : ℂ)^1 * 0 * ((minor56 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove).det + ((-1 : ℂ)^2 * 1 * ((minor56 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove).det + (0))) = value56 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant7, hm2, determinant48]
  dsimp only [value56, value7, value48] <;> ring

def minor57 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (((-3) * T * b) + (3 * Y * a))
    | 0, 1 => 1
    | 0, 3 => b
    | 1, 0 => ((-20) + ((-2) * T * a))
    | 1, 2 => 1
    | 1, 3 => a
    | 2, 0 => (5 * Y)
    | 3, 3 => 1
    | _, _ => 0
def value57 (a b c d Y T : ℂ) : ℂ := (5 * Y)

theorem determinant57 (a b c d Y T : ℂ) :
    (minor57 a b c d Y T).det = value57 a b c d Y T := by
  have hm0 : (minor57 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove =
      minor8 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor57 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove =
      minor34 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor57 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove =
      minor56 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (((-3) * T * b) + (3 * Y * a)) * ((minor57 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * 1 * ((minor57 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * 0 * ((minor57 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * b * ((minor57 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value57 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant8, hm1, determinant34, hm3, determinant56]
  dsimp only [value57, value8, value34, value56] <;> ring

def minor58 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (((-3) * T * b) + (3 * Y * a))
    | 0, 1 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 0, 2 => 1
    | 1, 0 => ((-20) + ((-2) * T * a))
    | 1, 1 => (((-3) * T * b) + (3 * Y * a))
    | 1, 3 => 1
    | 2, 0 => (5 * Y)
    | 2, 1 => ((-20) + ((-2) * T * a))
    | 3, 1 => (5 * Y)
    | _, _ => 0
def value58 (a b c d Y T : ℂ) : ℂ := (25 * (Y^2))

theorem determinant58 (a b c d Y T : ℂ) :
    (minor58 a b c d Y T).det = value58 a b c d Y T := by
  have hm0 : (minor58 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove =
      minor26 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor58 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove =
      minor56 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor58 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove =
      minor44 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (((-3) * T * b) + (3 * Y * a)) * ((minor58 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor58 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * 1 * ((minor58 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * 0 * ((minor58 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value58 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant26, hm1, determinant56, hm2, determinant44]
  dsimp only [value58, value26, value56, value44] <;> ring

def minor59 (a b c d Y T : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 0, 1 => (((-2) * b) + (Y * c) + ((-5) * T * d))
    | 0, 3 => a
    | 0, 4 => c
    | 1, 0 => (((-3) * T * b) + (3 * Y * a))
    | 1, 1 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 1, 2 => 1
    | 1, 4 => b
    | 2, 0 => ((-20) + ((-2) * T * a))
    | 2, 1 => (((-3) * T * b) + (3 * Y * a))
    | 2, 3 => 1
    | 2, 4 => a
    | 3, 0 => (5 * Y)
    | 3, 1 => ((-20) + ((-2) * T * a))
    | 4, 1 => (5 * Y)
    | 4, 4 => 1
    | _, _ => 0
def value59 (a b c d Y T : ℂ) : ℂ := (((-280) * a) + ((-68) * T * (a^2)) + ((-30) * Y * b) + ((-10) * (Y^2) * (a^2)) + ((-4) * (T^2) * (a^3)) + (20 * c * (Y^2)) + (80 * T * c) + (8 * a * c * (T^2)) + (25 * T * Y * d) + ((-19) * T * Y * a * b))

theorem determinant59 (a b c d Y T : ℂ) :
    (minor59 a b c d Y T).det = value59 a b c d Y T := by
  have hm0 : (minor59 a b c d Y T).submatrix Fin.succ (0 : Fin 5).succAbove =
      minor27 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor59 a b c d Y T).submatrix Fin.succ (1 : Fin 5).succAbove =
      minor57 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor59 a b c d Y T).submatrix Fin.succ (3 : Fin 5).succAbove =
      minor53 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm4 : (minor59 a b c d Y T).submatrix Fin.succ (4 : Fin 5).succAbove =
      minor58 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor59 a b c d Y T).submatrix Fin.succ (0 : Fin 5).succAbove).det + ((-1 : ℂ)^1 * (((-2) * b) + (Y * c) + ((-5) * T * d)) * ((minor59 a b c d Y T).submatrix Fin.succ (1 : Fin 5).succAbove).det + ((-1 : ℂ)^2 * 0 * ((minor59 a b c d Y T).submatrix Fin.succ (2 : Fin 5).succAbove).det + ((-1 : ℂ)^3 * a * ((minor59 a b c d Y T).submatrix Fin.succ (3 : Fin 5).succAbove).det + ((-1 : ℂ)^4 * c * ((minor59 a b c d Y T).submatrix Fin.succ (4 : Fin 5).succAbove).det + (0))))) = value59 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant27, hm1, determinant57, hm3, determinant53, hm4, determinant58]
  dsimp only [value59, value27, value57, value53, value58] <;> ring

end Mordell.Determinants
