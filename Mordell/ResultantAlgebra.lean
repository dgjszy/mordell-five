import Mordell.Determinants.Part18
import Mordell.ResultantBridge
import Mathlib.Tactic.ComputeDegree
import Mathlib.Analysis.Complex.RealDeriv

set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

namespace Mordell.ResultantAlgebra
open Polynomial

def delta (a b c d : ℂ) : ℂ := ((256 * (c^5)) + (3125 * (d^4)) + ((-128) * (a^2) * (c^4)) + ((-27) * (b^4) * (c^2)) + (16 * (a^4) * (c^3)) + (108 * d * (b^5)) + (108 * (a^5) * (d^2)) + ((-3750) * a * b * (d^3)) + ((-1600) * b * d * (c^3)) + ((-900) * c * (a^3) * (d^2)) + ((-4) * (a^3) * (b^2) * (c^2)) + (16 * d * (a^3) * (b^3)) + (144 * a * (b^2) * (c^3)) + (825 * (a^2) * (b^2) * (d^2)) + (2000 * a * (c^2) * (d^2)) + (2250 * c * (b^2) * (d^2)) + ((-630) * a * c * d * (b^3)) + ((-72) * b * c * d * (a^4)) + (560 * b * d * (a^2) * (c^2)))

def r3 (a b c d : ℂ) : ℂ := ((108 * (b^6)) + ((-25000) * b * (d^3)) + ((-896) * (a^3) * (c^3)) + ((-160) * (b^2) * (c^3)) + (16 * (a^3) * (b^4)) + (144 * (a^5) * (c^2)) + (1280 * a * (c^4)) + (2700 * (a^4) * (d^2)) + (20000 * (c^2) * (d^2)) + ((-15000) * c * (a^2) * (d^2)) + ((-1800) * c * d * (b^3)) + ((-792) * a * c * (b^4)) + ((-96) * c * (a^4) * (b^2)) + (240 * d * (a^2) * (b^3)) + (1736 * (a^2) * (b^2) * (c^2)) + (12000 * a * (b^2) * (d^2)) + ((-1320) * b * c * d * (a^3)) + (800 * a * b * d * (c^2)))

def r2 (a b c d : ℂ) : ℂ := (((-100000) * a * (d^3)) + ((-64000) * d * (c^3)) + ((-4320) * (b^3) * (c^2)) + (64 * (a^4) * (b^3)) + (432 * a * (b^5)) + (864 * d * (a^6)) + (21600 * d * (b^4)) + ((-10080) * c * d * (a^4)) + ((-2520) * c * (a^2) * (b^3)) + ((-288) * b * c * (a^5)) + (1920 * b * (a^3) * (c^2)) + (5120 * a * b * (c^3)) + (8520 * d * (a^3) * (b^2)) + (21000 * b * (a^2) * (d^2)) + (38400 * d * (a^2) * (c^2)) + (180000 * b * c * (d^2)) + ((-57600) * a * c * d * (b^2)))

def r1 (a b c d : ℂ) : ℂ := ((160000 * (c^4)) + ((-108000) * (a^3) * (d^2)) + ((-67200) * (a^2) * (c^3)) + ((-6480) * c * (b^4)) + (144 * (a^2) * (b^4)) + (7056 * (a^4) * (c^2)) + (360000 * (b^2) * (d^2)) + ((-624000) * b * d * (c^2)) + ((-82800) * a * d * (b^3)) + ((-8640) * b * d * (a^4)) + ((-1824) * c * (a^3) * (b^2)) + (53760 * a * (b^2) * (c^2)) + (480000 * a * c * (d^2)) + (156000 * b * c * d * (a^2)))

def r0 (a b c d : ℂ) : ℂ := ((23328 * (b^5)) + (3200000 * (d^3)) + ((-320000) * b * (c^3)) + (3136 * (a^3) * (b^3)) + (42336 * d * (a^5)) + ((-2400000) * a * b * (d^2)) + ((-403200) * c * d * (a^3)) + ((-138240) * a * c * (b^3)) + ((-14112) * b * c * (a^4)) + (134400 * b * (a^2) * (c^2)) + (340800 * d * (a^2) * (b^2)) + (864000 * c * d * (b^2)) + (960000 * a * d * (c^2)))

def s2 (a b c d : ℂ) : ℂ := (((-22500) * (a^2) * (d^3)) + (108 * c * (b^5)) + (1280 * b * (c^4)) + (13500 * (b^3) * (d^2)) + (50000 * c * (d^3)) + ((-10800) * d * (b^2) * (c^2)) + ((-3840) * d * (a^3) * (c^2)) + ((-576) * a * (b^3) * (c^2)) + ((-540) * a * d * (b^4)) + ((-144) * d * (a^4) * (b^2)) + ((-48) * b * (a^4) * (c^2)) + (16 * c * (a^3) * (b^3)) + (432 * c * d * (a^5)) + (896 * b * (a^2) * (c^3)) + (4500 * b * (a^3) * (d^2)) + (6400 * a * d * (c^3)) + (1980 * c * d * (a^2) * (b^2)) + (6000 * a * b * c * (d^2)))

def s1 (a b c d : ℂ) : ℂ := ((1944 * (b^6)) + ((-20160) * (b^2) * (c^3)) + ((-17664) * (a^3) * (c^3)) + ((-5400) * (a^4) * (d^2)) + (288 * (a^3) * (b^4)) + (2016 * (a^5) * (c^2)) + (38400 * a * (c^4)) + (120000 * (c^2) * (d^2)) + ((-13608) * a * c * (b^4)) + ((-9000) * a * (b^2) * (d^2)) + ((-1632) * c * (a^4) * (b^2)) + (864 * b * d * (a^5)) + (6000 * c * (a^2) * (d^2)) + (6120 * d * (a^2) * (b^3)) + (27504 * (a^2) * (b^2) * (c^2)) + (43200 * c * d * (b^3)) + ((-62400) * a * b * d * (c^2)) + ((-2640) * b * c * d * (a^3)))

def s0 (a b c d : ℂ) : ℂ := (((-160000) * d * (c^3)) + ((-5760) * (b^3) * (c^2)) + (896 * (a^4) * (b^3)) + (6480 * a * (b^5)) + (12096 * d * (a^6)) + (32400 * d * (b^4)) + (400000 * a * (d^3)) + ((-552000) * b * (a^2) * (d^2)) + ((-113040) * c * d * (a^4)) + ((-76800) * a * b * (c^3)) + ((-38112) * c * (a^2) * (b^3)) + ((-4032) * b * c * (a^5)) + (35328 * b * (a^3) * (c^2)) + (98400 * d * (a^3) * (b^2)) + (297600 * d * (a^2) * (c^2)) + (480000 * b * c * (d^2)) + (134400 * a * c * d * (b^2)))

def F0 (a b c d Y : ℂ) : ℂ := delta a b c d * Y^5 + r3 a b c d * Y^3 + r2 a b c d * Y^2 + r1 a b c d * Y + r0 a b c d

def F1 (a b c d Y : ℂ) : ℂ := 20 * delta a b c d * Y^3 + s2 a b c d * Y^2 + s1 a b c d * Y + s0 a b c d

def F2 (a b c d Y : ℂ) : ℂ := (((-25600) * b * (c^4)) + ((-10000) * (a^2) * (d^3)) + (64 * (a^5) * (b^3)) + (432 * (a^2) * (b^5)) + (864 * d * (a^7)) + (1728 * c * (b^5)) + (12800 * Y * (c^5)) + (200000 * c * (d^3)) + (250000 * Y * (d^4)) + ((-18600) * b * (a^3) * (d^2)) + ((-11808) * a * (b^3) * (c^2)) + ((-4896) * c * d * (a^5)) + ((-3840) * d * (a^3) * (c^2)) + ((-3584) * Y * (a^2) * (c^4)) + ((-2264) * c * (a^3) * (b^3)) + ((-864) * Y * (b^4) * (c^2)) + ((-480) * Y * (a^4) * (c^3)) + ((-288) * b * c * (a^6)) + ((-128) * (Y^3) * (a^3) * (c^4)) + (16 * Y * (a^4) * (b^4)) + (16 * (Y^3) * (a^5) * (c^3)) + (108 * Y * a * (b^6)) + (108 * (Y^3) * (a^6) * (d^2)) + (144 * Y * (a^6) * (c^2)) + (256 * a * (Y^3) * (c^5)) + (960 * b * (a^4) * (c^2)) + (3125 * a * (Y^3) * (d^4)) + (3780 * Y * d * (b^5)) + (6480 * Y * (a^5) * (d^2)) + (7168 * b * (a^2) * (c^3)) + (7368 * d * (a^4) * (b^2)) + (8640 * a * d * (b^4)) + (38400 * a * d * (c^3)) + (72000 * d * (b^2) * (c^2)) + ((-257500) * Y * a * b * (d^3)) + ((-108000) * a * b * c * (d^2)) + ((-84800) * Y * b * d * (c^3)) + ((-57300) * Y * c * (a^3) * (d^2)) + ((-3750) * b * (Y^3) * (a^2) * (d^3)) + ((-900) * c * (Y^3) * (a^4) * (d^2)) + ((-792) * Y * c * (a^2) * (b^4)) + ((-96) * Y * c * (a^5) * (b^2)) + ((-27) * a * (Y^3) * (b^4) * (c^2)) + ((-4) * (Y^3) * (a^4) * (b^2) * (c^2)) + (16 * d * (Y^3) * (a^4) * (b^3)) + (108 * a * d * (Y^3) * (b^5)) + (144 * (Y^3) * (a^2) * (b^2) * (c^3)) + (656 * Y * d * (a^3) * (b^3)) + (825 * (Y^3) * (a^3) * (b^2) * (d^2)) + (1644 * Y * (a^3) * (b^2) * (c^2)) + (2000 * (Y^3) * (a^2) * (c^2) * (d^2)) + (4880 * Y * a * (b^2) * (c^3)) + (14160 * c * d * (a^2) * (b^2)) + (48300 * Y * (a^2) * (b^2) * (d^2)) + (126000 * Y * c * (b^2) * (d^2)) + (138000 * Y * a * (c^2) * (d^2)) + ((-25740) * Y * a * c * d * (b^3)) + ((-3408) * Y * b * c * d * (a^4)) + ((-1600) * a * b * d * (Y^3) * (c^3)) + ((-630) * c * d * (Y^3) * (a^2) * (b^3)) + ((-72) * b * c * d * (Y^3) * (a^5)) + (560 * b * d * (Y^3) * (a^3) * (c^2)) + (2250 * a * c * (Y^3) * (b^2) * (d^2)) + (23760 * Y * b * d * (a^2) * (c^2)))

def F3 (a b c d Y : ℂ) : ℂ := (((-108) * (b^7)) + ((-20000) * (b^2) * (d^3)) + ((-12800) * d * (c^4)) + ((-16) * (a^3) * (b^5)) + (1024 * (b^3) * (c^3)) + (4500 * (a^3) * (d^3)) + ((-10000) * a * c * (d^3)) + ((-4128) * d * (a^4) * (c^2)) + ((-3125) * b * (Y^2) * (d^4)) + ((-3072) * a * b * (c^4)) + ((-2240) * (a^2) * (b^3) * (c^2)) + ((-1440) * c * d * (b^4)) + ((-1068) * d * (a^2) * (b^4)) + ((-768) * Y * (a^3) * (c^4)) + ((-256) * b * (Y^2) * (c^5)) + ((-192) * b * (a^5) * (c^2)) + ((-144) * d * (a^5) * (b^2)) + ((-108) * d * (Y^2) * (b^6)) + (27 * (Y^2) * (b^5) * (c^2)) + (96 * Y * (a^5) * (c^3)) + (112 * c * (a^4) * (b^3)) + (432 * c * d * (a^6)) + (648 * Y * (a^6) * (d^2)) + (720 * b * (a^4) * (d^2)) + (900 * a * c * (b^5)) + (1536 * Y * a * (c^5)) + (1536 * b * (a^3) * (c^3)) + (10500 * a * (b^3) * (d^2)) + (12800 * d * (a^2) * (c^3)) + (18750 * Y * a * (d^4)) + (40000 * b * (c^2) * (d^2)) + ((-22800) * b * c * (a^2) * (d^2)) + ((-22500) * Y * b * (a^2) * (d^3)) + ((-5400) * Y * c * (a^4) * (d^2)) + ((-2250) * c * (Y^2) * (b^3) * (d^2)) + ((-1040) * a * d * (b^2) * (c^2)) + ((-825) * (Y^2) * (a^2) * (b^3) * (d^2)) + ((-162) * Y * a * (b^4) * (c^2)) + ((-144) * a * (Y^2) * (b^3) * (c^3)) + ((-108) * b * (Y^2) * (a^5) * (d^2)) + ((-24) * Y * (a^4) * (b^2) * (c^2)) + ((-16) * b * (Y^2) * (a^4) * (c^3)) + ((-16) * d * (Y^2) * (a^3) * (b^4)) + (4 * (Y^2) * (a^3) * (b^3) * (c^2)) + (96 * Y * d * (a^4) * (b^3)) + (128 * b * (Y^2) * (a^2) * (c^4)) + (648 * Y * a * d * (b^5)) + (864 * Y * (a^2) * (b^2) * (c^3)) + (1600 * d * (Y^2) * (b^2) * (c^3)) + (3750 * a * (Y^2) * (b^2) * (d^3)) + (4500 * c * d * (a^3) * (b^2)) + (4950 * Y * (a^3) * (b^2) * (d^2)) + (12000 * Y * (a^2) * (c^2) * (d^2)) + ((-9600) * Y * a * b * d * (c^3)) + ((-3780) * Y * c * d * (a^2) * (b^3)) + ((-2000) * a * b * (Y^2) * (c^2) * (d^2)) + ((-560) * d * (Y^2) * (a^2) * (b^2) * (c^2)) + ((-432) * Y * b * c * d * (a^5)) + (72 * c * d * (Y^2) * (a^4) * (b^2)) + (630 * a * c * d * (Y^2) * (b^4)) + (900 * b * c * (Y^2) * (a^3) * (d^2)) + (3360 * Y * b * d * (a^3) * (c^2)) + (13500 * Y * a * c * (b^2) * (d^2)))

def F4 (a b c d Y : ℂ) : ℂ := (((-6250) * b * (d^4)) + ((-512) * b * (c^5)) + ((-216) * d * (b^6)) + (54 * (b^5) * (c^2)) + (256 * Y * (c^6)) + ((-4500) * c * (b^3) * (d^2)) + ((-1650) * (a^2) * (b^3) * (d^2)) + ((-288) * a * (b^3) * (c^3)) + ((-216) * b * (a^5) * (d^2)) + ((-128) * Y * (a^2) * (c^5)) + ((-32) * b * (a^4) * (c^3)) + ((-32) * d * (a^3) * (b^4)) + ((-27) * Y * (b^4) * (c^3)) + (8 * (a^3) * (b^3) * (c^2)) + (16 * Y * (a^4) * (c^4)) + (256 * b * (a^2) * (c^4)) + (3125 * Y * c * (d^4)) + (3200 * d * (b^2) * (c^3)) + (7500 * a * (b^2) * (d^3)) + ((-4000) * a * b * (c^2) * (d^2)) + ((-1600) * Y * b * d * (c^4)) + ((-1120) * d * (a^2) * (b^2) * (c^2)) + ((-900) * Y * (a^3) * (c^2) * (d^2)) + ((-4) * Y * (a^3) * (b^2) * (c^3)) + (108 * Y * c * d * (b^5)) + (108 * Y * c * (a^5) * (d^2)) + (144 * Y * a * (b^2) * (c^4)) + (144 * c * d * (a^4) * (b^2)) + (1260 * a * c * d * (b^4)) + (1800 * b * c * (a^3) * (d^2)) + (2000 * Y * a * (c^3) * (d^2)) + (2250 * Y * (b^2) * (c^2) * (d^2)) + ((-3750) * Y * a * b * c * (d^3)) + ((-630) * Y * a * d * (b^3) * (c^2)) + ((-72) * Y * b * d * (a^4) * (c^2)) + (16 * Y * c * d * (a^3) * (b^3)) + (560 * Y * b * d * (a^2) * (c^3)) + (825 * Y * c * (a^2) * (b^2) * (d^2)))

def F5 (a b c d Y : ℂ) : ℂ := (((-3125) * (d^5)) + ((-256) * d * (c^5)) + ((-108) * (a^5) * (d^3)) + ((-108) * (b^5) * (d^2)) + ((-2250) * c * (b^2) * (d^3)) + ((-2000) * a * (c^2) * (d^3)) + ((-825) * (a^2) * (b^2) * (d^3)) + ((-16) * d * (a^4) * (c^3)) + ((-16) * (a^3) * (b^3) * (d^2)) + (27 * d * (b^4) * (c^2)) + (128 * d * (a^2) * (c^4)) + (900 * c * (a^3) * (d^3)) + (1600 * b * (c^3) * (d^2)) + (3750 * a * b * (d^4)) + ((-560) * b * (a^2) * (c^2) * (d^2)) + ((-144) * a * d * (b^2) * (c^3)) + (4 * d * (a^3) * (b^2) * (c^2)) + (72 * b * c * (a^4) * (d^2)) + (630 * a * c * (b^3) * (d^2)))

noncomputable def reduced (a b c d Y T : ℂ) : ℂ[X] :=
  C (5*Y)*X^4 + C (-2*a*T-20)*X^3 + C (3*a*Y-3*b*T)*X^2 +
    C (2*b*Y-4*c*T-6*a)*X + C (c*Y-5*d*T-2*b)

theorem reduced_degree (a b c d Y T : ℂ) : (reduced a b c d Y T).natDegree ≤ 4 := by
  unfold reduced
  compute_degree <;> norm_num

theorem quintic_degree (a b c d : ℂ) : (quintic a b c d).natDegree = 5 := by
  unfold quintic
  compute_degree <;> norm_num

theorem quintic_coeff_five (a b c d : ℂ) : (quintic a b c d).coeff 5 = 1 := by
  norm_num [quintic, coeff_X]

theorem reduced_coefficient (a b c d Y T : ℂ) (n : ℕ) :
    (reduced a b c d Y T).coeff n =
      (if n = 4 then 5*Y else 0) + (if n = 3 then -2*a*T-20 else 0) +
      (if n = 2 then 3*a*Y-3*b*T else 0) +
      (if n = 1 then 2*b*Y-4*c*T-6*a else 0) +
      (if n = 0 then c*Y-5*d*T-2*b else 0) := by
  dsimp only [reduced]
  simp only [coeff_add, coeff_C_mul_X_pow, coeff_C_mul, coeff_X, coeff_C]
  by_cases hn : n = 1
  · simp [hn]
  · simp [hn, Ne.symm hn]

theorem quintic_coefficient (a b c d : ℂ) (n : ℕ) :
    (quintic a b c d).coeff n =
      (if n = 5 then 1 else 0) + (if n = 3 then a else 0) +
      (if n = 2 then b else 0) + (if n = 1 then c else 0) +
      (if n = 0 then d else 0) := by
  dsimp only [quintic]
  simp only [coeff_add, coeff_C_mul_X_pow, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]
  by_cases hn : n = 1
  · simp [hn]
  · simp [hn, Ne.symm hn]

theorem reduced_matrix (a b c d Y T : ℂ) :
    Polynomial.sylvester (quintic a b c d) (reduced a b c d Y T) 5 4 =
      Determinants.minor273 a b c d Y T := by
  ext i j
  fin_cases i <;> fin_cases j
  · change (reduced a b c d Y T).coeff 0 = Determinants.minor273 a b c d Y T 0 0
    rw [reduced_coefficient]
    norm_num [Determinants.minor273] <;> ring
  · change (0 : ℂ) = 0
    rfl
  · change (0 : ℂ) = 0
    rfl
  · change (0 : ℂ) = 0
    rfl
  · change (0 : ℂ) = 0
    rfl
  · change (quintic a b c d).coeff 0 = Determinants.minor273 a b c d Y T 0 5
    rw [quintic_coefficient]
    norm_num [Determinants.minor273] <;> ring
  · change (0 : ℂ) = 0
    rfl
  · change (0 : ℂ) = 0
    rfl
  · change (0 : ℂ) = 0
    rfl
  · change (reduced a b c d Y T).coeff 1 = Determinants.minor273 a b c d Y T 1 0
    rw [reduced_coefficient]
    norm_num [Determinants.minor273] <;> ring
  · change (reduced a b c d Y T).coeff 0 = Determinants.minor273 a b c d Y T 1 1
    rw [reduced_coefficient]
    norm_num [Determinants.minor273] <;> ring
  · change (0 : ℂ) = 0
    rfl
  · change (0 : ℂ) = 0
    rfl
  · change (0 : ℂ) = 0
    rfl
  · change (quintic a b c d).coeff 1 = Determinants.minor273 a b c d Y T 1 5
    rw [quintic_coefficient]
    norm_num [Determinants.minor273] <;> ring
  · change (quintic a b c d).coeff 0 = Determinants.minor273 a b c d Y T 1 6
    rw [quintic_coefficient]
    norm_num [Determinants.minor273] <;> ring
  · change (0 : ℂ) = 0
    rfl
  · change (0 : ℂ) = 0
    rfl
  · change (reduced a b c d Y T).coeff 2 = Determinants.minor273 a b c d Y T 2 0
    rw [reduced_coefficient]
    norm_num [Determinants.minor273] <;> ring
  · change (reduced a b c d Y T).coeff 1 = Determinants.minor273 a b c d Y T 2 1
    rw [reduced_coefficient]
    norm_num [Determinants.minor273] <;> ring
  · change (reduced a b c d Y T).coeff 0 = Determinants.minor273 a b c d Y T 2 2
    rw [reduced_coefficient]
    norm_num [Determinants.minor273] <;> ring
  · change (0 : ℂ) = 0
    rfl
  · change (0 : ℂ) = 0
    rfl
  · change (quintic a b c d).coeff 2 = Determinants.minor273 a b c d Y T 2 5
    rw [quintic_coefficient]
    norm_num [Determinants.minor273] <;> ring
  · change (quintic a b c d).coeff 1 = Determinants.minor273 a b c d Y T 2 6
    rw [quintic_coefficient]
    norm_num [Determinants.minor273] <;> ring
  · change (quintic a b c d).coeff 0 = Determinants.minor273 a b c d Y T 2 7
    rw [quintic_coefficient]
    norm_num [Determinants.minor273] <;> ring
  · change (0 : ℂ) = 0
    rfl
  · change (reduced a b c d Y T).coeff 3 = Determinants.minor273 a b c d Y T 3 0
    rw [reduced_coefficient]
    norm_num [Determinants.minor273] <;> ring
  · change (reduced a b c d Y T).coeff 2 = Determinants.minor273 a b c d Y T 3 1
    rw [reduced_coefficient]
    norm_num [Determinants.minor273] <;> ring
  · change (reduced a b c d Y T).coeff 1 = Determinants.minor273 a b c d Y T 3 2
    rw [reduced_coefficient]
    norm_num [Determinants.minor273] <;> ring
  · change (reduced a b c d Y T).coeff 0 = Determinants.minor273 a b c d Y T 3 3
    rw [reduced_coefficient]
    norm_num [Determinants.minor273] <;> ring
  · change (0 : ℂ) = 0
    rfl
  · change (quintic a b c d).coeff 3 = Determinants.minor273 a b c d Y T 3 5
    rw [quintic_coefficient]
    norm_num [Determinants.minor273] <;> ring
  · change (quintic a b c d).coeff 2 = Determinants.minor273 a b c d Y T 3 6
    rw [quintic_coefficient]
    norm_num [Determinants.minor273] <;> ring
  · change (quintic a b c d).coeff 1 = Determinants.minor273 a b c d Y T 3 7
    rw [quintic_coefficient]
    norm_num [Determinants.minor273] <;> ring
  · change (quintic a b c d).coeff 0 = Determinants.minor273 a b c d Y T 3 8
    rw [quintic_coefficient]
    norm_num [Determinants.minor273] <;> ring
  · change (reduced a b c d Y T).coeff 4 = Determinants.minor273 a b c d Y T 4 0
    rw [reduced_coefficient]
    norm_num [Determinants.minor273] <;> ring
  · change (reduced a b c d Y T).coeff 3 = Determinants.minor273 a b c d Y T 4 1
    rw [reduced_coefficient]
    norm_num [Determinants.minor273] <;> ring
  · change (reduced a b c d Y T).coeff 2 = Determinants.minor273 a b c d Y T 4 2
    rw [reduced_coefficient]
    norm_num [Determinants.minor273] <;> ring
  · change (reduced a b c d Y T).coeff 1 = Determinants.minor273 a b c d Y T 4 3
    rw [reduced_coefficient]
    norm_num [Determinants.minor273] <;> ring
  · change (reduced a b c d Y T).coeff 0 = Determinants.minor273 a b c d Y T 4 4
    rw [reduced_coefficient]
    norm_num [Determinants.minor273] <;> ring
  · change (quintic a b c d).coeff 4 = Determinants.minor273 a b c d Y T 4 5
    rw [quintic_coefficient]
    norm_num [Determinants.minor273] <;> ring
  · change (quintic a b c d).coeff 3 = Determinants.minor273 a b c d Y T 4 6
    rw [quintic_coefficient]
    norm_num [Determinants.minor273] <;> ring
  · change (quintic a b c d).coeff 2 = Determinants.minor273 a b c d Y T 4 7
    rw [quintic_coefficient]
    norm_num [Determinants.minor273] <;> ring
  · change (quintic a b c d).coeff 1 = Determinants.minor273 a b c d Y T 4 8
    rw [quintic_coefficient]
    norm_num [Determinants.minor273] <;> ring
  · change (0 : ℂ) = 0
    rfl
  · change (reduced a b c d Y T).coeff 4 = Determinants.minor273 a b c d Y T 5 1
    rw [reduced_coefficient]
    norm_num [Determinants.minor273] <;> ring
  · change (reduced a b c d Y T).coeff 3 = Determinants.minor273 a b c d Y T 5 2
    rw [reduced_coefficient]
    norm_num [Determinants.minor273] <;> ring
  · change (reduced a b c d Y T).coeff 2 = Determinants.minor273 a b c d Y T 5 3
    rw [reduced_coefficient]
    norm_num [Determinants.minor273] <;> ring
  · change (reduced a b c d Y T).coeff 1 = Determinants.minor273 a b c d Y T 5 4
    rw [reduced_coefficient]
    norm_num [Determinants.minor273] <;> ring
  · change (quintic a b c d).coeff 5 = Determinants.minor273 a b c d Y T 5 5
    rw [quintic_coefficient]
    norm_num [Determinants.minor273] <;> ring
  · change (quintic a b c d).coeff 4 = Determinants.minor273 a b c d Y T 5 6
    rw [quintic_coefficient]
    norm_num [Determinants.minor273] <;> ring
  · change (quintic a b c d).coeff 3 = Determinants.minor273 a b c d Y T 5 7
    rw [quintic_coefficient]
    norm_num [Determinants.minor273] <;> ring
  · change (quintic a b c d).coeff 2 = Determinants.minor273 a b c d Y T 5 8
    rw [quintic_coefficient]
    norm_num [Determinants.minor273] <;> ring
  · change (0 : ℂ) = 0
    rfl
  · change (0 : ℂ) = 0
    rfl
  · change (reduced a b c d Y T).coeff 4 = Determinants.minor273 a b c d Y T 6 2
    rw [reduced_coefficient]
    norm_num [Determinants.minor273] <;> ring
  · change (reduced a b c d Y T).coeff 3 = Determinants.minor273 a b c d Y T 6 3
    rw [reduced_coefficient]
    norm_num [Determinants.minor273] <;> ring
  · change (reduced a b c d Y T).coeff 2 = Determinants.minor273 a b c d Y T 6 4
    rw [reduced_coefficient]
    norm_num [Determinants.minor273] <;> ring
  · change (0 : ℂ) = 0
    rfl
  · change (quintic a b c d).coeff 5 = Determinants.minor273 a b c d Y T 6 6
    rw [quintic_coefficient]
    norm_num [Determinants.minor273] <;> ring
  · change (quintic a b c d).coeff 4 = Determinants.minor273 a b c d Y T 6 7
    rw [quintic_coefficient]
    norm_num [Determinants.minor273] <;> ring
  · change (quintic a b c d).coeff 3 = Determinants.minor273 a b c d Y T 6 8
    rw [quintic_coefficient]
    norm_num [Determinants.minor273] <;> ring
  · change (0 : ℂ) = 0
    rfl
  · change (0 : ℂ) = 0
    rfl
  · change (0 : ℂ) = 0
    rfl
  · change (reduced a b c d Y T).coeff 4 = Determinants.minor273 a b c d Y T 7 3
    rw [reduced_coefficient]
    norm_num [Determinants.minor273] <;> ring
  · change (reduced a b c d Y T).coeff 3 = Determinants.minor273 a b c d Y T 7 4
    rw [reduced_coefficient]
    norm_num [Determinants.minor273] <;> ring
  · change (0 : ℂ) = 0
    rfl
  · change (0 : ℂ) = 0
    rfl
  · change (quintic a b c d).coeff 5 = Determinants.minor273 a b c d Y T 7 7
    rw [quintic_coefficient]
    norm_num [Determinants.minor273] <;> ring
  · change (quintic a b c d).coeff 4 = Determinants.minor273 a b c d Y T 7 8
    rw [quintic_coefficient]
    norm_num [Determinants.minor273] <;> ring
  · change (0 : ℂ) = 0
    rfl
  · change (0 : ℂ) = 0
    rfl
  · change (0 : ℂ) = 0
    rfl
  · change (0 : ℂ) = 0
    rfl
  · change (reduced a b c d Y T).coeff 4 = Determinants.minor273 a b c d Y T 8 4
    rw [reduced_coefficient]
    norm_num [Determinants.minor273] <;> ring
  · change (0 : ℂ) = 0
    rfl
  · change (0 : ℂ) = 0
    rfl
  · change (0 : ℂ) = 0
    rfl
  · change (quintic a b c d).coeff 5 = Determinants.minor273 a b c d Y T 8 8
    rw [quintic_coefficient]
    norm_num [Determinants.minor273] <;> ring

theorem reduced_resultant (a b c d Y T : ℂ) :
    (quintic a b c d).resultant (reduced a b c d Y T) 5 4 =
      Determinants.value273 a b c d Y T := by
  unfold Polynomial.resultant
  rw [reduced_matrix, Determinants.determinant273]

theorem reduced_identity (a b c d Y T : ℂ) :
    (C Y + C T * X) * (quintic a b c d).derivative -
      (quintic a b c d).derivative.derivative =
        reduced a b c d Y T + quintic a b c d * C (5*T) := by
  simp [quintic, reduced, derivative_pow, map_add, map_mul, map_pow, C_ofNat] <;> ring

theorem resultant_formula (a b c d Y T : ℂ) :
    (quintic a b c d).resultant
      ((C Y + C T * X) * (quintic a b c d).derivative -
        (quintic a b c d).derivative.derivative) 5 5 =
      Determinants.value273 a b c d Y T := by
  rw [reduced_identity, resultant_add_mul_right]
  · have he := resultant_add_right_deg (quintic a b c d) (reduced a b c d Y T) 5 4 1
      (reduced_degree a b c d Y T)
    simp only [Nat.reduceAdd, quintic_coeff_five, pow_one, one_mul] at he
    exact he.trans (reduced_resultant a b c d Y T)
  · rw [natDegree_C] <;> norm_num
  · rw [quintic_degree]

theorem value_coefficients (a b c d Y T : ℂ) :
    Determinants.value273 a b c d Y T =
      F0 a b c d Y + T * F1 a b c d Y + T^2 * F2 a b c d Y +
      T^3 * F3 a b c d Y + T^4 * F4 a b c d Y + T^5 * F5 a b c d Y := by
  dsimp only [Determinants.value273, F0, F1, F2, F3, F4, F5, delta, r3, r2, r1, r0, s2, s1, s0]
  ring

end Mordell.ResultantAlgebra
