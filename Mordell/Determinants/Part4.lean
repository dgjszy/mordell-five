import Mordell.Determinants.Part3

set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Mordell.Determinants

def minor60 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (((-3) * T * b) + (3 * Y * a))
    | 0, 1 => 1
    | 0, 3 => a
    | 1, 0 => ((-20) + ((-2) * T * a))
    | 1, 2 => 1
    | 2, 0 => (5 * Y)
    | 2, 3 => 1
    | _, _ => 0
def value60 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant60 (a b c d Y T : ℂ) :
    (minor60 a b c d Y T).det = value60 a b c d Y T := by
  have hm0 : (minor60 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove =
      minor11 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor60 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove =
      minor37 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor60 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove =
      minor56 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (((-3) * T * b) + (3 * Y * a)) * ((minor60 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * 1 * ((minor60 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * 0 * ((minor60 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * a * ((minor60 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value60 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant11, hm1, determinant37, hm3, determinant56]
  dsimp only [value60, value11, value37, value56] <;> ring

def minor61 (a b c d Y T : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 0, 1 => (((-2) * b) + (Y * c) + ((-5) * T * d))
    | 0, 3 => a
    | 0, 4 => b
    | 1, 0 => (((-3) * T * b) + (3 * Y * a))
    | 1, 1 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 1, 2 => 1
    | 1, 4 => a
    | 2, 0 => ((-20) + ((-2) * T * a))
    | 2, 1 => (((-3) * T * b) + (3 * Y * a))
    | 2, 3 => 1
    | 3, 0 => (5 * Y)
    | 3, 1 => ((-20) + ((-2) * T * a))
    | 3, 4 => 1
    | 4, 1 => (5 * Y)
    | _, _ => 0
def value61 (a b c d Y T : ℂ) : ℂ := (((-70) * Y * a) + (15 * b * (Y^2)) + ((-10) * T * Y * (a^2)) + (20 * T * Y * c))

theorem determinant61 (a b c d Y T : ℂ) :
    (minor61 a b c d Y T).det = value61 a b c d Y T := by
  have hm0 : (minor61 a b c d Y T).submatrix Fin.succ (0 : Fin 5).succAbove =
      minor29 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor61 a b c d Y T).submatrix Fin.succ (1 : Fin 5).succAbove =
      minor60 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor61 a b c d Y T).submatrix Fin.succ (3 : Fin 5).succAbove =
      minor54 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm4 : (minor61 a b c d Y T).submatrix Fin.succ (4 : Fin 5).succAbove =
      minor58 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor61 a b c d Y T).submatrix Fin.succ (0 : Fin 5).succAbove).det + ((-1 : ℂ)^1 * (((-2) * b) + (Y * c) + ((-5) * T * d)) * ((minor61 a b c d Y T).submatrix Fin.succ (1 : Fin 5).succAbove).det + ((-1 : ℂ)^2 * 0 * ((minor61 a b c d Y T).submatrix Fin.succ (2 : Fin 5).succAbove).det + ((-1 : ℂ)^3 * a * ((minor61 a b c d Y T).submatrix Fin.succ (3 : Fin 5).succAbove).det + ((-1 : ℂ)^4 * b * ((minor61 a b c d Y T).submatrix Fin.succ (4 : Fin 5).succAbove).det + (0))))) = value61 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant29, hm1, determinant60, hm3, determinant54, hm4, determinant58]
  dsimp only [value61, value29, value60, value54, value58] <;> ring

def minor62 (a b c d Y T : ℂ) : Matrix (Fin 6) (Fin 6) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (((-2) * b) + (Y * c) + ((-5) * T * d))
    | 0, 2 => a
    | 0, 3 => b
    | 0, 4 => c
    | 0, 5 => d
    | 1, 0 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 1, 1 => (((-2) * b) + (Y * c) + ((-5) * T * d))
    | 1, 3 => a
    | 1, 4 => b
    | 1, 5 => c
    | 2, 0 => (((-3) * T * b) + (3 * Y * a))
    | 2, 1 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 2, 2 => 1
    | 2, 4 => a
    | 2, 5 => b
    | 3, 0 => ((-20) + ((-2) * T * a))
    | 3, 1 => (((-3) * T * b) + (3 * Y * a))
    | 3, 3 => 1
    | 3, 5 => a
    | 4, 0 => (5 * Y)
    | 4, 1 => ((-20) + ((-2) * T * a))
    | 4, 4 => 1
    | 5, 1 => (5 * Y)
    | 5, 5 => 1
    | _, _ => 0
def value62 (a b c d Y T : ℂ) : ℂ := ((196 * (a^3)) + (324 * (b^2)) + ((-280) * a * c) + (4 * (T^2) * (a^5)) + (4 * (Y^2) * (a^4)) + (16 * (Y^2) * (c^2)) + (25 * (T^2) * (d^2)) + (56 * T * (a^4)) + (80 * T * (c^2)) + ((-180) * T * b * d) + ((-180) * T * c * (a^2)) + ((-84) * Y * b * c) + ((-40) * Y * b * (a^2)) + ((-20) * c * (T^2) * (a^3)) + ((-16) * c * (Y^2) * (a^2)) + ((-15) * b * d * (Y^2)) + (9 * T * Y * (b^3)) + (12 * c * (T^2) * (b^2)) + (15 * a * (Y^2) * (b^2)) + (19 * (T^2) * (a^2) * (b^2)) + (24 * a * (T^2) * (c^2)) + (70 * Y * a * d) + (138 * T * a * (b^2)) + ((-50) * a * b * d * (T^2)) + ((-10) * T * Y * d * (a^2)) + (4 * T * Y * b * (a^3)) + (20 * T * Y * c * d) + ((-2) * T * Y * a * b * c))

theorem determinant62 (a b c d Y T : ℂ) :
    (minor62 a b c d Y T).det = value62 a b c d Y T := by
  have hm0 : (minor62 a b c d Y T).submatrix Fin.succ (0 : Fin 6).succAbove =
      minor30 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor62 a b c d Y T).submatrix Fin.succ (2 : Fin 6).succAbove =
      minor47 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor62 a b c d Y T).submatrix Fin.succ (3 : Fin 6).succAbove =
      minor55 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm4 : (minor62 a b c d Y T).submatrix Fin.succ (4 : Fin 6).succAbove =
      minor59 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm5 : (minor62 a b c d Y T).submatrix Fin.succ (5 : Fin 6).succAbove =
      minor61 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (((-2) * b) + (Y * c) + ((-5) * T * d)) * ((minor62 a b c d Y T).submatrix Fin.succ (0 : Fin 6).succAbove).det + ((-1 : ℂ)^1 * 0 * ((minor62 a b c d Y T).submatrix Fin.succ (1 : Fin 6).succAbove).det + ((-1 : ℂ)^2 * a * ((minor62 a b c d Y T).submatrix Fin.succ (2 : Fin 6).succAbove).det + ((-1 : ℂ)^3 * b * ((minor62 a b c d Y T).submatrix Fin.succ (3 : Fin 6).succAbove).det + ((-1 : ℂ)^4 * c * ((minor62 a b c d Y T).submatrix Fin.succ (4 : Fin 6).succAbove).det + ((-1 : ℂ)^5 * d * ((minor62 a b c d Y T).submatrix Fin.succ (5 : Fin 6).succAbove).det + (0)))))) = value62 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant30, hm2, determinant47, hm3, determinant55, hm4, determinant59, hm5, determinant61]
  dsimp only [value62, value30, value47, value55, value59, value61] <;> ring

def minor63 (a b c d Y T : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => match i.val, j.val with
    | 1, 1 => 1
    | _, _ => 0
def value63 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant63 (a b c d Y T : ℂ) :
    (minor63 a b c d Y T).det = value63 a b c d Y T := by
  rw [show value63 a b c d Y T = 0 by rfl]
  apply Matrix.det_eq_zero_of_row_eq_zero 0
  intro j
  fin_cases j <;> rfl

def minor64 (a b c d Y T : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => match i.val, j.val with
    | _, _ => 0
def value64 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant64 (a b c d Y T : ℂ) :
    (minor64 a b c d Y T).det = value64 a b c d Y T := by
  rw [show value64 a b c d Y T = 0 by rfl]
  apply Matrix.det_eq_zero_of_row_eq_zero 0
  intro j
  fin_cases j <;> rfl

def minor65 (a b c d Y T : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (5 * Y)
    | 0, 1 => 1
    | 0, 2 => a
    | 2, 2 => 1
    | _, _ => 0
def value65 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant65 (a b c d Y T : ℂ) :
    (minor65 a b c d Y T).det = value65 a b c d Y T := by
  have hm0 : (minor65 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove =
      minor22 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor65 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove =
      minor63 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor65 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove =
      minor64 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (5 * Y) * ((minor65 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove).det + ((-1 : ℂ)^1 * 1 * ((minor65 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove).det + ((-1 : ℂ)^2 * a * ((minor65 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove).det + (0))) = value65 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant22, hm1, determinant63, hm2, determinant64]
  dsimp only [value65, value22, value63, value64] <;> ring

def minor66 (a b c d Y T : ℂ) : Matrix (Fin 1) (Fin 1) ℂ :=
  fun i j => match i.val, j.val with
    | _, _ => 0
def value66 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant66 (a b c d Y T : ℂ) :
    (minor66 a b c d Y T).det = value66 a b c d Y T := by
  simp [Matrix.det_unique, minor66, value66]

def minor67 (a b c d Y T : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 1 => 1
    | _, _ => 0
def value67 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant67 (a b c d Y T : ℂ) :
    (minor67 a b c d Y T).det = value67 a b c d Y T := by
  have hm1 : (minor67 a b c d Y T).submatrix Fin.succ (1 : Fin 2).succAbove =
      minor66 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * 0 * ((minor67 a b c d Y T).submatrix Fin.succ (0 : Fin 2).succAbove).det + ((-1 : ℂ)^1 * 1 * ((minor67 a b c d Y T).submatrix Fin.succ (1 : Fin 2).succAbove).det + (0)) = value67 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm1, determinant66]
  dsimp only [value67, value66] <;> ring

def minor68 (a b c d Y T : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (5 * Y)
    | 0, 1 => 1
    | 1, 2 => 1
    | _, _ => 0
def value68 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant68 (a b c d Y T : ℂ) :
    (minor68 a b c d Y T).det = value68 a b c d Y T := by
  have hm0 : (minor68 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove =
      minor4 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor68 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove =
      minor67 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (5 * Y) * ((minor68 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove).det + ((-1 : ℂ)^1 * 1 * ((minor68 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove).det + ((-1 : ℂ)^2 * 0 * ((minor68 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove).det + (0))) = value68 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant4, hm1, determinant67]
  dsimp only [value68, value4, value67] <;> ring

def minor69 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => ((-20) + ((-2) * T * a))
    | 0, 2 => a
    | 0, 3 => b
    | 1, 0 => (5 * Y)
    | 1, 1 => 1
    | 1, 3 => a
    | 2, 2 => 1
    | 3, 3 => 1
    | _, _ => 0
def value69 (a b c d Y T : ℂ) : ℂ := ((-20) + ((-2) * T * a))

theorem determinant69 (a b c d Y T : ℂ) :
    (minor69 a b c d Y T).det = value69 a b c d Y T := by
  have hm0 : (minor69 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove =
      minor5 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor69 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove =
      minor65 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor69 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove =
      minor68 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * ((-20) + ((-2) * T * a)) * ((minor69 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * 0 * ((minor69 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * a * ((minor69 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * b * ((minor69 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value69 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant5, hm2, determinant65, hm3, determinant68]
  dsimp only [value69, value5, value65, value68] <;> ring

def minor70 (a b c d Y T : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (5 * Y)
    | 0, 2 => a
    | 1, 1 => 1
    | 2, 2 => 1
    | _, _ => 0
def value70 (a b c d Y T : ℂ) : ℂ := (5 * Y)

theorem determinant70 (a b c d Y T : ℂ) :
    (minor70 a b c d Y T).det = value70 a b c d Y T := by
  have hm0 : (minor70 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove =
      minor2 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor70 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove =
      minor67 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (5 * Y) * ((minor70 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove).det + ((-1 : ℂ)^1 * 0 * ((minor70 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove).det + ((-1 : ℂ)^2 * a * ((minor70 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove).det + (0))) = value70 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant2, hm2, determinant67]
  dsimp only [value70, value2, value67] <;> ring

def minor71 (a b c d Y T : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 1 => ((-20) + ((-2) * T * a))
    | 1, 1 => (5 * Y)
    | _, _ => 0
def value71 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant71 (a b c d Y T : ℂ) :
    (minor71 a b c d Y T).det = value71 a b c d Y T := by
  have hm1 : (minor71 a b c d Y T).submatrix Fin.succ (1 : Fin 2).succAbove =
      minor66 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * 0 * ((minor71 a b c d Y T).submatrix Fin.succ (0 : Fin 2).succAbove).det + ((-1 : ℂ)^1 * ((-20) + ((-2) * T * a)) * ((minor71 a b c d Y T).submatrix Fin.succ (1 : Fin 2).succAbove).det + (0)) = value71 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm1, determinant66]
  dsimp only [value71, value66] <;> ring

def minor72 (a b c d Y T : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (5 * Y)
    | 0, 1 => (((-3) * T * b) + (3 * Y * a))
    | 0, 2 => a
    | 1, 1 => ((-20) + ((-2) * T * a))
    | 2, 1 => (5 * Y)
    | 2, 2 => 1
    | _, _ => 0
def value72 (a b c d Y T : ℂ) : ℂ := (((-100) * Y) + ((-10) * T * Y * a))

theorem determinant72 (a b c d Y T : ℂ) :
    (minor72 a b c d Y T).det = value72 a b c d Y T := by
  have hm0 : (minor72 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove =
      minor23 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor72 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove =
      minor63 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor72 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove =
      minor71 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (5 * Y) * ((minor72 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove).det + ((-1 : ℂ)^1 * (((-3) * T * b) + (3 * Y * a)) * ((minor72 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove).det + ((-1 : ℂ)^2 * a * ((minor72 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove).det + (0))) = value72 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant23, hm1, determinant63, hm2, determinant71]
  dsimp only [value72, value23, value63, value71] <;> ring

def minor73 (a b c d Y T : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (5 * Y)
    | 0, 1 => (((-3) * T * b) + (3 * Y * a))
    | 1, 1 => ((-20) + ((-2) * T * a))
    | 1, 2 => 1
    | 2, 1 => (5 * Y)
    | _, _ => 0
def value73 (a b c d Y T : ℂ) : ℂ := ((-25) * (Y^2))

theorem determinant73 (a b c d Y T : ℂ) :
    (minor73 a b c d Y T).det = value73 a b c d Y T := by
  have hm0 : (minor73 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove =
      minor16 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor73 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove =
      minor67 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (5 * Y) * ((minor73 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove).det + ((-1 : ℂ)^1 * (((-3) * T * b) + (3 * Y * a)) * ((minor73 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove).det + ((-1 : ℂ)^2 * 0 * ((minor73 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove).det + (0))) = value73 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant16, hm1, determinant67]
  dsimp only [value73, value16, value67] <;> ring

def minor74 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => ((-20) + ((-2) * T * a))
    | 0, 1 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 0, 2 => a
    | 0, 3 => b
    | 1, 0 => (5 * Y)
    | 1, 1 => (((-3) * T * b) + (3 * Y * a))
    | 1, 3 => a
    | 2, 1 => ((-20) + ((-2) * T * a))
    | 2, 2 => 1
    | 3, 1 => (5 * Y)
    | 3, 3 => 1
    | _, _ => 0
def value74 (a b c d Y T : ℂ) : ℂ := (((-30) * Y * a) + (15 * b * (Y^2)) + (60 * T * b) + ((-6) * T * Y * (a^2)) + (6 * a * b * (T^2)) + (20 * T * Y * c))

theorem determinant74 (a b c d Y T : ℂ) :
    (minor74 a b c d Y T).det = value74 a b c d Y T := by
  have hm0 : (minor74 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove =
      minor17 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor74 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove =
      minor70 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor74 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove =
      minor72 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor74 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove =
      minor73 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * ((-20) + ((-2) * T * a)) * ((minor74 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor74 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * a * ((minor74 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * b * ((minor74 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value74 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant17, hm1, determinant70, hm2, determinant72, hm3, determinant73]
  dsimp only [value74, value17, value70, value72, value73] <;> ring

end Mordell.Determinants
