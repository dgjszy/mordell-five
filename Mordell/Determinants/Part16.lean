import Mordell.Determinants.Part15

set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Mordell.Determinants

def minor240 (a b c d Y T : ℂ) : Matrix (Fin 6) (Fin 6) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => ((-20) + ((-2) * T * a))
    | 0, 1 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 0, 2 => (((-2) * b) + (Y * c) + ((-5) * T * d))
    | 0, 4 => c
    | 0, 5 => d
    | 1, 0 => (5 * Y)
    | 1, 1 => (((-3) * T * b) + (3 * Y * a))
    | 1, 2 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 1, 3 => (((-2) * b) + (Y * c) + ((-5) * T * d))
    | 1, 4 => b
    | 1, 5 => c
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
def value240 (a b c d Y T : ℂ) : ℂ := (((-144000) * b) + ((-8000) * Y * c) + ((-4800) * Y * (a^2)) + ((-450) * (Y^3) * (b^2)) + ((-120) * (Y^3) * (a^3)) + (540 * (T^3) * (b^3)) + (10000 * d * (Y^2)) + (40000 * T * d) + ((-49600) * T * a * b) + ((-13200) * T * Y * (b^2)) + ((-9600) * b * c * (T^2)) + ((-4800) * b * (T^2) * (a^2)) + ((-4300) * a * b * (Y^2)) + ((-3200) * Y * (T^2) * (c^2)) + ((-2640) * T * Y * (a^3)) + ((-456) * Y * (T^2) * (a^4)) + ((-400) * T * (Y^3) * (c^2)) + ((-300) * b * c * (Y^4)) + ((-90) * (T^2) * (Y^2) * (b^3)) + ((-48) * b * (T^3) * (a^3)) + ((-40) * b * (Y^4) * (a^2)) + ((-24) * T * (Y^3) * (a^4)) + ((-24) * Y * (T^3) * (a^5)) + (8 * b * (T^4) * (a^4)) + (40 * d * (T^4) * (a^3)) + (54 * a * (T^4) * (b^3)) + (250 * a * d * (Y^4)) + (400 * a * c * (Y^3)) + (1200 * d * (T^3) * (a^2)) + (12000 * a * d * (T^2)) + ((-4500) * T * b * c * (Y^2)) + ((-2190) * Y * a * (T^2) * (b^2)) + ((-1920) * a * b * c * (T^3)) + ((-600) * T * b * (Y^2) * (a^2)) + ((-500) * c * d * (T^2) * (Y^2)) + ((-320) * Y * a * (T^3) * (c^2)) + ((-150) * T * a * (Y^3) * (b^2)) + ((-114) * Y * (T^3) * (a^2) * (b^2)) + ((-96) * b * c * (T^4) * (a^2)) + ((-56) * b * (T^2) * (Y^2) * (a^3)) + (168 * Y * c * (T^3) * (a^3)) + (180 * T * c * (Y^3) * (a^2)) + (180 * Y * c * (T^3) * (b^2)) + (350 * d * (T^2) * (Y^2) * (a^2)) + (2320 * Y * c * (T^2) * (a^2)) + (3750 * T * a * d * (Y^2)) + (5600 * T * Y * a * c) + ((-190) * a * b * c * (T^2) * (Y^2)))

theorem determinant240 (a b c d Y T : ℂ) :
    (minor240 a b c d Y T).det = value240 a b c d Y T := by
  have hm0 : (minor240 a b c d Y T).submatrix Fin.succ (0 : Fin 6).succAbove =
      minor86 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor240 a b c d Y T).submatrix Fin.succ (1 : Fin 6).succAbove =
      minor218 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor240 a b c d Y T).submatrix Fin.succ (2 : Fin 6).succAbove =
      minor233 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm4 : (minor240 a b c d Y T).submatrix Fin.succ (4 : Fin 6).succAbove =
      minor237 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm5 : (minor240 a b c d Y T).submatrix Fin.succ (5 : Fin 6).succAbove =
      minor239 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * ((-20) + ((-2) * T * a)) * ((minor240 a b c d Y T).submatrix Fin.succ (0 : Fin 6).succAbove).det + ((-1 : ℂ)^1 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor240 a b c d Y T).submatrix Fin.succ (1 : Fin 6).succAbove).det + ((-1 : ℂ)^2 * (((-2) * b) + (Y * c) + ((-5) * T * d)) * ((minor240 a b c d Y T).submatrix Fin.succ (2 : Fin 6).succAbove).det + ((-1 : ℂ)^3 * 0 * ((minor240 a b c d Y T).submatrix Fin.succ (3 : Fin 6).succAbove).det + ((-1 : ℂ)^4 * c * ((minor240 a b c d Y T).submatrix Fin.succ (4 : Fin 6).succAbove).det + ((-1 : ℂ)^5 * d * ((minor240 a b c d Y T).submatrix Fin.succ (5 : Fin 6).succAbove).det + (0)))))) = value240 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant86, hm1, determinant218, hm2, determinant233, hm4, determinant237, hm5, determinant239]
  dsimp only [value240, value86, value218, value233, value237, value239] <;> ring

def minor241 (a b c d Y T : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 1 => (5 * Y)
    | 0, 2 => 1
    | _, _ => 0
def value241 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant241 (a b c d Y T : ℂ) :
    (minor241 a b c d Y T).det = value241 a b c d Y T := by
  have hm1 : (minor241 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove =
      minor196 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor241 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove =
      minor226 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * 0 * ((minor241 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove).det + ((-1 : ℂ)^1 * (5 * Y) * ((minor241 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove).det + ((-1 : ℂ)^2 * 1 * ((minor241 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove).det + (0))) = value241 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm1, determinant196, hm2, determinant226]
  dsimp only [value241, value196, value226] <;> ring

def minor242 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 1 => ((-20) + ((-2) * T * a))
    | 0, 3 => b
    | 1, 1 => (5 * Y)
    | 1, 2 => 1
    | 1, 3 => a
    | 3, 3 => 1
    | _, _ => 0
def value242 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant242 (a b c d Y T : ℂ) :
    (minor242 a b c d Y T).det = value242 a b c d Y T := by
  have hm1 : (minor242 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove =
      minor197 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor242 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove =
      minor241 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * 0 * ((minor242 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * ((-20) + ((-2) * T * a)) * ((minor242 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * 0 * ((minor242 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * b * ((minor242 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value242 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm1, determinant197, hm3, determinant241]
  dsimp only [value242, value197, value241] <;> ring

def minor243 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 1 => ((-20) + ((-2) * T * a))
    | 0, 2 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 1, 1 => (5 * Y)
    | 1, 2 => (((-3) * T * b) + (3 * Y * a))
    | 1, 3 => 1
    | 2, 2 => ((-20) + ((-2) * T * a))
    | 3, 2 => (5 * Y)
    | _, _ => 0
def value243 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant243 (a b c d Y T : ℂ) :
    (minor243 a b c d Y T).det = value243 a b c d Y T := by
  have hm1 : (minor243 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove =
      minor207 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor243 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove =
      minor241 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * 0 * ((minor243 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * ((-20) + ((-2) * T * a)) * ((minor243 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor243 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * 0 * ((minor243 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value243 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm1, determinant207, hm2, determinant241]
  dsimp only [value243, value207, value241] <;> ring

def minor244 (a b c d Y T : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (5 * Y)
    | 0, 1 => (((-3) * T * b) + (3 * Y * a))
    | 0, 2 => (((-2) * b) + (Y * c) + ((-5) * T * d))
    | 0, 3 => a
    | 0, 4 => c
    | 1, 1 => ((-20) + ((-2) * T * a))
    | 1, 2 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 1, 4 => b
    | 2, 1 => (5 * Y)
    | 2, 2 => (((-3) * T * b) + (3 * Y * a))
    | 2, 3 => 1
    | 2, 4 => a
    | 3, 2 => ((-20) + ((-2) * T * a))
    | 4, 2 => (5 * Y)
    | 4, 4 => 1
    | _, _ => 0
def value244 (a b c d Y T : ℂ) : ℂ := (((-2000) * Y) + ((-400) * T * Y * a) + ((-20) * Y * (T^2) * (a^2)))

theorem determinant244 (a b c d Y T : ℂ) :
    (minor244 a b c d Y T).det = value244 a b c d Y T := by
  have hm0 : (minor244 a b c d Y T).submatrix Fin.succ (0 : Fin 5).succAbove =
      minor76 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor244 a b c d Y T).submatrix Fin.succ (1 : Fin 5).succAbove =
      minor208 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor244 a b c d Y T).submatrix Fin.succ (2 : Fin 5).succAbove =
      minor242 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor244 a b c d Y T).submatrix Fin.succ (3 : Fin 5).succAbove =
      minor231 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm4 : (minor244 a b c d Y T).submatrix Fin.succ (4 : Fin 5).succAbove =
      minor243 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (5 * Y) * ((minor244 a b c d Y T).submatrix Fin.succ (0 : Fin 5).succAbove).det + ((-1 : ℂ)^1 * (((-3) * T * b) + (3 * Y * a)) * ((minor244 a b c d Y T).submatrix Fin.succ (1 : Fin 5).succAbove).det + ((-1 : ℂ)^2 * (((-2) * b) + (Y * c) + ((-5) * T * d)) * ((minor244 a b c d Y T).submatrix Fin.succ (2 : Fin 5).succAbove).det + ((-1 : ℂ)^3 * a * ((minor244 a b c d Y T).submatrix Fin.succ (3 : Fin 5).succAbove).det + ((-1 : ℂ)^4 * c * ((minor244 a b c d Y T).submatrix Fin.succ (4 : Fin 5).succAbove).det + (0))))) = value244 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant76, hm1, determinant208, hm2, determinant242, hm3, determinant231, hm4, determinant243]
  dsimp only [value244, value76, value208, value242, value231, value243] <;> ring

def minor245 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 1 => ((-20) + ((-2) * T * a))
    | 0, 2 => (((-3) * T * b) + (3 * Y * a))
    | 1, 1 => (5 * Y)
    | 1, 2 => ((-20) + ((-2) * T * a))
    | 1, 3 => 1
    | 2, 2 => (5 * Y)
    | _, _ => 0
def value245 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant245 (a b c d Y T : ℂ) :
    (minor245 a b c d Y T).det = value245 a b c d Y T := by
  have hm1 : (minor245 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove =
      minor219 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor245 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove =
      minor241 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * 0 * ((minor245 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * ((-20) + ((-2) * T * a)) * ((minor245 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * (((-3) * T * b) + (3 * Y * a)) * ((minor245 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * 0 * ((minor245 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value245 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm1, determinant219, hm2, determinant241]
  dsimp only [value245, value219, value241] <;> ring

def minor246 (a b c d Y T : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (5 * Y)
    | 0, 1 => (((-3) * T * b) + (3 * Y * a))
    | 0, 2 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 0, 3 => (((-2) * b) + (Y * c) + ((-5) * T * d))
    | 0, 4 => a
    | 1, 1 => ((-20) + ((-2) * T * a))
    | 1, 2 => (((-3) * T * b) + (3 * Y * a))
    | 1, 3 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 2, 1 => (5 * Y)
    | 2, 2 => ((-20) + ((-2) * T * a))
    | 2, 3 => (((-3) * T * b) + (3 * Y * a))
    | 2, 4 => 1
    | 3, 2 => (5 * Y)
    | 3, 3 => ((-20) + ((-2) * T * a))
    | 4, 3 => (5 * Y)
    | _, _ => 0
def value246 (a b c d Y T : ℂ) : ℂ := (((-2500) * (Y^3)) + ((-250) * T * a * (Y^3)))

theorem determinant246 (a b c d Y T : ℂ) :
    (minor246 a b c d Y T).det = value246 a b c d Y T := by
  have hm0 : (minor246 a b c d Y T).submatrix Fin.succ (0 : Fin 5).succAbove =
      minor89 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor246 a b c d Y T).submatrix Fin.succ (1 : Fin 5).succAbove =
      minor221 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor246 a b c d Y T).submatrix Fin.succ (2 : Fin 5).succAbove =
      minor243 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor246 a b c d Y T).submatrix Fin.succ (3 : Fin 5).succAbove =
      minor245 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm4 : (minor246 a b c d Y T).submatrix Fin.succ (4 : Fin 5).succAbove =
      minor236 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (5 * Y) * ((minor246 a b c d Y T).submatrix Fin.succ (0 : Fin 5).succAbove).det + ((-1 : ℂ)^1 * (((-3) * T * b) + (3 * Y * a)) * ((minor246 a b c d Y T).submatrix Fin.succ (1 : Fin 5).succAbove).det + ((-1 : ℂ)^2 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor246 a b c d Y T).submatrix Fin.succ (2 : Fin 5).succAbove).det + ((-1 : ℂ)^3 * (((-2) * b) + (Y * c) + ((-5) * T * d)) * ((minor246 a b c d Y T).submatrix Fin.succ (3 : Fin 5).succAbove).det + ((-1 : ℂ)^4 * a * ((minor246 a b c d Y T).submatrix Fin.succ (4 : Fin 5).succAbove).det + (0))))) = value246 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant89, hm1, determinant221, hm2, determinant243, hm3, determinant245, hm4, determinant236]
  dsimp only [value246, value89, value221, value243, value245, value236] <;> ring

def minor247 (a b c d Y T : ℂ) : Matrix (Fin 6) (Fin 6) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => ((-20) + ((-2) * T * a))
    | 0, 1 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 0, 2 => (((-2) * b) + (Y * c) + ((-5) * T * d))
    | 0, 4 => b
    | 0, 5 => d
    | 1, 0 => (5 * Y)
    | 1, 1 => (((-3) * T * b) + (3 * Y * a))
    | 1, 2 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 1, 3 => (((-2) * b) + (Y * c) + ((-5) * T * d))
    | 1, 4 => a
    | 1, 5 => c
    | 2, 1 => ((-20) + ((-2) * T * a))
    | 2, 2 => (((-3) * T * b) + (3 * Y * a))
    | 2, 3 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 2, 5 => b
    | 3, 1 => (5 * Y)
    | 3, 2 => ((-20) + ((-2) * T * a))
    | 3, 3 => (((-3) * T * b) + (3 * Y * a))
    | 3, 4 => 1
    | 3, 5 => a
    | 4, 2 => (5 * Y)
    | 4, 3 => ((-20) + ((-2) * T * a))
    | 5, 3 => (5 * Y)
    | 5, 5 => 1
    | _, _ => 0
def value247 (a b c d Y T : ℂ) : ℂ := (((-112000) * a) + ((-49600) * T * (a^2)) + ((-48000) * Y * b) + ((-8160) * (T^2) * (a^3)) + ((-3600) * (T^2) * (b^2)) + ((-1900) * (Y^2) * (a^2)) + ((-592) * (T^3) * (a^4)) + ((-225) * (Y^4) * (b^2)) + ((-16) * (T^4) * (a^5)) + (2500 * d * (Y^3)) + (6000 * c * (Y^2)) + (32000 * T * c) + ((-3300) * T * (Y^2) * (b^2)) + ((-1600) * a * b * (Y^3)) + ((-720) * a * (T^3) * (b^2)) + ((-400) * (T^2) * (Y^2) * (c^2)) + ((-260) * T * (Y^2) * (a^3)) + ((-36) * (T^4) * (a^2) * (b^2)) + ((-16) * (T^2) * (Y^2) * (a^4)) + (32 * c * (T^4) * (a^3)) + (960 * c * (T^3) * (a^2)) + (9600 * a * c * (T^2)) + (20000 * T * Y * d) + ((-23600) * T * Y * a * b) + ((-2920) * Y * b * (T^2) * (a^2)) + ((-2400) * Y * b * c * (T^2)) + ((-600) * T * b * c * (Y^3)) + ((-330) * a * (T^2) * (Y^2) * (b^2)) + ((-104) * Y * b * (T^3) * (a^3)) + ((-70) * T * b * (Y^3) * (a^2)) + (100 * c * (T^2) * (Y^2) * (a^2)) + (200 * Y * d * (T^3) * (a^2)) + (250 * T * a * d * (Y^3)) + (400 * T * a * c * (Y^2)) + (4000 * Y * a * d * (T^2)) + ((-240) * Y * a * b * c * (T^3)))

theorem determinant247 (a b c d Y T : ℂ) :
    (minor247 a b c d Y T).det = value247 a b c d Y T := by
  have hm0 : (minor247 a b c d Y T).submatrix Fin.succ (0 : Fin 6).succAbove =
      minor90 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor247 a b c d Y T).submatrix Fin.succ (1 : Fin 6).succAbove =
      minor222 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor247 a b c d Y T).submatrix Fin.succ (2 : Fin 6).succAbove =
      minor244 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm4 : (minor247 a b c d Y T).submatrix Fin.succ (4 : Fin 6).succAbove =
      minor237 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm5 : (minor247 a b c d Y T).submatrix Fin.succ (5 : Fin 6).succAbove =
      minor246 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * ((-20) + ((-2) * T * a)) * ((minor247 a b c d Y T).submatrix Fin.succ (0 : Fin 6).succAbove).det + ((-1 : ℂ)^1 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor247 a b c d Y T).submatrix Fin.succ (1 : Fin 6).succAbove).det + ((-1 : ℂ)^2 * (((-2) * b) + (Y * c) + ((-5) * T * d)) * ((minor247 a b c d Y T).submatrix Fin.succ (2 : Fin 6).succAbove).det + ((-1 : ℂ)^3 * 0 * ((minor247 a b c d Y T).submatrix Fin.succ (3 : Fin 6).succAbove).det + ((-1 : ℂ)^4 * b * ((minor247 a b c d Y T).submatrix Fin.succ (4 : Fin 6).succAbove).det + ((-1 : ℂ)^5 * d * ((minor247 a b c d Y T).submatrix Fin.succ (5 : Fin 6).succAbove).det + (0)))))) = value247 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant90, hm1, determinant222, hm2, determinant244, hm4, determinant237, hm5, determinant246]
  dsimp only [value247, value90, value222, value244, value237, value246] <;> ring

def minor248 (a b c d Y T : ℂ) : Matrix (Fin 7) (Fin 7) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 0 => (((-3) * T * b) + (3 * Y * a))
    | 0, 1 => (((-2) * b) + (Y * c) + ((-5) * T * d))
    | 0, 4 => c
    | 0, 5 => d
    | 1, 0 => ((-20) + ((-2) * T * a))
    | 1, 1 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 1, 2 => (((-2) * b) + (Y * c) + ((-5) * T * d))
    | 1, 4 => b
    | 1, 5 => c
    | 1, 6 => d
    | 2, 0 => (5 * Y)
    | 2, 1 => (((-3) * T * b) + (3 * Y * a))
    | 2, 2 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 2, 3 => (((-2) * b) + (Y * c) + ((-5) * T * d))
    | 2, 4 => a
    | 2, 5 => b
    | 2, 6 => c
    | 3, 1 => ((-20) + ((-2) * T * a))
    | 3, 2 => (((-3) * T * b) + (3 * Y * a))
    | 3, 3 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 3, 5 => a
    | 3, 6 => b
    | 4, 1 => (5 * Y)
    | 4, 2 => ((-20) + ((-2) * T * a))
    | 4, 3 => (((-3) * T * b) + (3 * Y * a))
    | 4, 4 => 1
    | 4, 6 => a
    | 5, 2 => (5 * Y)
    | 5, 3 => ((-20) + ((-2) * T * a))
    | 5, 5 => 1
    | 6, 3 => (5 * Y)
    | 6, 6 => 1
    | _, _ => 0
def value248 (a b c d Y T : ℂ) : ℂ := (((-144000) * b * c) + ((-8000) * Y * (c^2)) + ((-7840) * b * (a^2)) + ((-3528) * Y * (a^4)) + ((-2500) * (Y^3) * (d^2)) + ((-81) * (T^4) * (b^5)) + ((-72) * (Y^3) * (a^5)) + (180 * (Y^2) * (b^3)) + (17280 * T * (b^3)) + (112000 * a * d) + ((-20040) * Y * a * (b^2)) + ((-20000) * T * Y * (d^2)) + ((-12000) * d * (T^2) * (b^2)) + ((-5440) * b * (T^2) * (c^2)) + ((-2880) * Y * (T^2) * (c^3)) + ((-2300) * d * (Y^2) * (a^2)) + ((-1600) * d * (T^3) * (c^2)) + ((-1008) * T * Y * (a^5)) + ((-800) * a * (Y^3) * (c^2)) + ((-660) * c * (Y^3) * (b^2)) + ((-454) * (Y^3) * (a^2) * (b^2)) + ((-368) * d * (T^3) * (a^4)) + ((-320) * T * (Y^3) * (c^3)) + ((-240) * b * (Y^4) * (c^2)) + ((-81) * a * (Y^4) * (b^3)) + ((-72) * Y * (T^2) * (a^6)) + ((-60) * d * (Y^4) * (a^3)) + ((-28) * b * (Y^2) * (a^3)) + ((-24) * d * (T^4) * (a^5)) + ((-12) * b * (Y^4) * (a^4)) + ((-12) * (T^4) * (a^3) * (b^3)) + (56 * b * (T^3) * (a^5)) + (81 * T * (Y^3) * (b^4)) + (192 * b * (T^4) * (c^3)) + (225 * d * (Y^4) * (b^2)) + (378 * (T^3) * (a^2) * (b^3)) + (488 * c * (Y^3) * (a^3)) + (504 * T * b * (a^3)) + (600 * d * (T^2) * (a^3)) + (624 * b * (T^2) * (a^4)) + (1422 * Y * (T^2) * (b^4)) + (2016 * c * (T^3) * (b^3)) + (3000 * b * (T^3) * (d^2)) + (4000 * c * d * (Y^2)) + (4872 * a * (T^2) * (b^3)) + (8000 * T * c * d) + (15920 * Y * c * (a^2)) + (30000 * T * d * (a^2)) + (48000 * Y * b * d) + ((-61920) * T * a * b * c) + ((-17520) * T * Y * c * (b^2)) + ((-9136) * b * c * (T^2) * (a^2)) + ((-6428) * T * Y * (a^2) * (b^2)) + ((-4080) * a * d * (T^3) * (b^2)) + ((-3520) * T * b * (Y^2) * (c^2)) + ((-2750) * Y * a * (T^2) * (d^2)) + ((-2080) * a * b * (T^3) * (c^2)) + ((-1440) * T * Y * a * (c^2)) + ((-1194) * T * a * (Y^2) * (b^3)) + ((-800) * T * d * (Y^2) * (a^3)) + ((-500) * Y * c * (T^3) * (d^2)) + ((-480) * Y * a * (T^3) * (c^3)) + ((-400) * d * (T^2) * (Y^2) * (c^2)) + ((-360) * Y * d * (T^3) * (b^3)) + ((-360) * c * d * (T^4) * (b^2)) + ((-254) * Y * (T^2) * (a^3) * (b^2)) + ((-248) * b * c * (T^3) * (a^3)) + ((-240) * b * (T^4) * (a^2) * (c^2)) + ((-234) * d * (T^4) * (a^2) * (b^2)) + ((-184) * T * b * (Y^2) * (a^4)) + ((-160) * a * d * (T^4) * (c^2)) + ((-84) * d * (T^2) * (Y^2) * (a^4)) + ((-81) * (T^2) * (Y^2) * (a^2) * (b^3)) + ((-40) * T * c * (Y^3) * (a^4)) + ((-40) * Y * c * (T^3) * (a^5)) + ((-12) * b * (T^2) * (Y^2) * (a^5)) + (12 * T * (Y^3) * (a^3) * (b^2)) + (24 * Y * (T^3) * (a^4) * (b^2)) + (32 * b * c * (T^4) * (a^4)) + (63 * c * (T^2) * (Y^2) * (b^3)) + (124 * b * c * (Y^4) * (a^2)) + (162 * Y * a * (T^3) * (b^4)) + (168 * c * d * (T^4) * (a^3)) + (200 * a * c * d * (Y^4)) + (240 * T * (Y^3) * (a^2) * (c^2)) + (280 * Y * (T^3) * (a^3) * (c^2)) + (300 * a * b * (T^4) * (d^2)) + (324 * Y * (T^3) * (b^2) * (c^2)) + (324 * a * c * (T^4) * (b^3)) + (1520 * a * b * c * (Y^2)) + (1872 * Y * (T^2) * (a^2) * (c^2)) + (2600 * a * b * d * (Y^3)) + (2850 * T * d * (Y^2) * (b^2)) + (2960 * c * d * (T^3) * (a^2)) + (4296 * T * Y * c * (a^3)) + (13600 * a * c * d * (T^2)) + ((-5782) * Y * a * c * (T^2) * (b^2)) + ((-486) * Y * c * (T^3) * (a^2) * (b^2)) + ((-416) * a * b * (T^2) * (Y^2) * (c^2)) + ((-354) * T * a * c * (Y^3) * (b^2)) + (120 * T * b * d * (Y^3) * (a^2)) + (128 * b * c * (T^2) * (Y^2) * (a^3)) + (135 * a * d * (T^2) * (Y^2) * (b^2)) + (144 * Y * b * d * (T^3) * (a^3)) + (300 * T * b * c * d * (Y^3)) + (480 * c * d * (T^2) * (Y^2) * (a^2)) + (1744 * T * b * c * (Y^2) * (a^2)) + (2200 * Y * b * c * d * (T^2)) + (2800 * T * a * c * d * (Y^2)) + (5020 * Y * b * d * (T^2) * (a^2)) + (38200 * T * Y * a * b * d) + (380 * Y * a * b * c * d * (T^3)))

theorem determinant248 (a b c d Y T : ℂ) :
    (minor248 a b c d Y T).det = value248 a b c d Y T := by
  have hm0 : (minor248 a b c d Y T).submatrix Fin.succ (0 : Fin 7).succAbove =
      minor93 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (minor248 a b c d Y T).submatrix Fin.succ (1 : Fin 7).succAbove =
      minor225 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm4 : (minor248 a b c d Y T).submatrix Fin.succ (4 : Fin 7).succAbove =
      minor240 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm5 : (minor248 a b c d Y T).submatrix Fin.succ (5 : Fin 7).succAbove =
      minor247 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * (((-3) * T * b) + (3 * Y * a)) * ((minor248 a b c d Y T).submatrix Fin.succ (0 : Fin 7).succAbove).det + ((-1 : ℂ)^1 * (((-2) * b) + (Y * c) + ((-5) * T * d)) * ((minor248 a b c d Y T).submatrix Fin.succ (1 : Fin 7).succAbove).det + ((-1 : ℂ)^2 * 0 * ((minor248 a b c d Y T).submatrix Fin.succ (2 : Fin 7).succAbove).det + ((-1 : ℂ)^3 * 0 * ((minor248 a b c d Y T).submatrix Fin.succ (3 : Fin 7).succAbove).det + ((-1 : ℂ)^4 * c * ((minor248 a b c d Y T).submatrix Fin.succ (4 : Fin 7).succAbove).det + ((-1 : ℂ)^5 * d * ((minor248 a b c d Y T).submatrix Fin.succ (5 : Fin 7).succAbove).det + ((-1 : ℂ)^6 * 0 * ((minor248 a b c d Y T).submatrix Fin.succ (6 : Fin 7).succAbove).det + (0))))))) = value248 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm0, determinant93, hm1, determinant225, hm4, determinant240, hm5, determinant247]
  dsimp only [value248, value93, value225, value240, value247] <;> ring

def minor249 (a b c d Y T : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => match i.val, j.val with
    | _, _ => 0
def value249 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant249 (a b c d Y T : ℂ) :
    (minor249 a b c d Y T).det = value249 a b c d Y T := by
  rw [show value249 a b c d Y T = 0 by rfl]
  apply Matrix.det_eq_zero_of_row_eq_zero 0
  intro j
  fin_cases j <;> rfl

def minor250 (a b c d Y T : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 2 => a
    | 2, 2 => 1
    | _, _ => 0
def value250 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant250 (a b c d Y T : ℂ) :
    (minor250 a b c d Y T).det = value250 a b c d Y T := by
  have hm2 : (minor250 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove =
      minor249 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * 0 * ((minor250 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove).det + ((-1 : ℂ)^1 * 0 * ((minor250 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove).det + ((-1 : ℂ)^2 * a * ((minor250 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove).det + (0))) = value250 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm2, determinant249]
  dsimp only [value250, value249] <;> ring

def minor251 (a b c d Y T : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => match i.val, j.val with
    | 1, 2 => 1
    | _, _ => 0
def value251 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant251 (a b c d Y T : ℂ) :
    (minor251 a b c d Y T).det = value251 a b c d Y T := by
  rw [show value251 a b c d Y T = 0 by rfl]
  apply Matrix.det_eq_zero_of_row_eq_zero 0
  intro j
  fin_cases j <;> rfl

def minor252 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 1 => (5 * Y)
    | 0, 2 => a
    | 0, 3 => b
    | 1, 3 => a
    | 2, 2 => 1
    | 3, 3 => 1
    | _, _ => 0
def value252 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant252 (a b c d Y T : ℂ) :
    (minor252 a b c d Y T).det = value252 a b c d Y T := by
  have hm1 : (minor252 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove =
      minor202 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor252 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove =
      minor250 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor252 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove =
      minor251 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * 0 * ((minor252 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * (5 * Y) * ((minor252 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * a * ((minor252 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * b * ((minor252 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value252 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm1, determinant202, hm2, determinant250, hm3, determinant251]
  dsimp only [value252, value202, value250, value251] <;> ring

def minor253 (a b c d Y T : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 2 => (((-3) * T * b) + (3 * Y * a))
    | 1, 2 => ((-20) + ((-2) * T * a))
    | 2, 2 => (5 * Y)
    | _, _ => 0
def value253 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant253 (a b c d Y T : ℂ) :
    (minor253 a b c d Y T).det = value253 a b c d Y T := by
  have hm2 : (minor253 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove =
      minor249 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * 0 * ((minor253 a b c d Y T).submatrix Fin.succ (0 : Fin 3).succAbove).det + ((-1 : ℂ)^1 * 0 * ((minor253 a b c d Y T).submatrix Fin.succ (1 : Fin 3).succAbove).det + ((-1 : ℂ)^2 * (((-3) * T * b) + (3 * Y * a)) * ((minor253 a b c d Y T).submatrix Fin.succ (2 : Fin 3).succAbove).det + (0))) = value253 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm2, determinant249]
  dsimp only [value253, value249] <;> ring

def minor254 (a b c d Y T : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => match i.val, j.val with
    | 0, 1 => (5 * Y)
    | 0, 2 => (((-6) * a) + ((-4) * T * c) + (2 * Y * b))
    | 0, 3 => b
    | 1, 2 => (((-3) * T * b) + (3 * Y * a))
    | 1, 3 => a
    | 2, 2 => ((-20) + ((-2) * T * a))
    | 3, 2 => (5 * Y)
    | 3, 3 => 1
    | _, _ => 0
def value254 (a b c d Y T : ℂ) : ℂ := 0

theorem determinant254 (a b c d Y T : ℂ) :
    (minor254 a b c d Y T).det = value254 a b c d Y T := by
  have hm1 : (minor254 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove =
      minor204 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (minor254 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove =
      minor250 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (minor254 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove =
      minor253 a b c d Y T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (-1 : ℂ)^0 * 0 * ((minor254 a b c d Y T).submatrix Fin.succ (0 : Fin 4).succAbove).det + ((-1 : ℂ)^1 * (5 * Y) * ((minor254 a b c d Y T).submatrix Fin.succ (1 : Fin 4).succAbove).det + ((-1 : ℂ)^2 * (((-6) * a) + ((-4) * T * c) + (2 * Y * b)) * ((minor254 a b c d Y T).submatrix Fin.succ (2 : Fin 4).succAbove).det + ((-1 : ℂ)^3 * b * ((minor254 a b c d Y T).submatrix Fin.succ (3 : Fin 4).succAbove).det + (0)))) = value254 a b c d Y T
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [hm1, determinant204, hm2, determinant250, hm3, determinant253]
  dsimp only [value254, value204, value250, value253] <;> ring

end Mordell.Determinants
