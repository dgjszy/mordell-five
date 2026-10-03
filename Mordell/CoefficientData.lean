import Mordell.ResultantDerivative
import Mordell.PhysicalScale

namespace Mordell
open Polynomial
open ResultantAlgebra

noncomputable def resultantZeroPolynomial (a b c d : ℂ) : ℂ[X] :=
  C (delta a b c d)*X^5 + C (r3 a b c d)*X^3 + C (r2 a b c d)*X^2 +
    C (r1 a b c d)*X + C (r0 a b c d)

noncomputable def resultantFirstPolynomial (a b c d : ℂ) : ℂ[X] :=
  C (20*delta a b c d)*X^3 + C (s2 a b c d)*X^2 +
    C (s1 a b c d)*X + C (s0 a b c d)

theorem stationaryPair_zero_polynomial {x y : Configuration} (h : StationaryPair x y)
    {a b c d : ℂ} (hp : rootPolynomial x = quintic a b c d) :
    resultantZeroPolynomial a b c d =
      C (complexDiscriminant x) * rootPolynomial (fun i => 4*y i) := by
  apply Polynomial.funext
  intro Y
  simpa only [resultantZeroPolynomial, F0, eval_add, eval_mul, eval_C, eval_pow,
    eval_X] using stationaryPair_F0 h hp Y

theorem stationaryPair_first_polynomial {x y : Configuration} (h : StationaryPair x y)
    {a b c d : ℂ} (hp : rootPolynomial x = quintic a b c d) :
    resultantFirstPolynomial a b c d = C (complexDiscriminant x) *
      (20*X^3 + C (6*(rootPolynomial (fun i => 4*y i)).coeff 3)*X +
        C (2*(rootPolynomial (fun i => 4*y i)).coeff 2)) := by
  apply Polynomial.funext
  intro Y
  simpa only [resultantFirstPolynomial, F1, eval_add, eval_mul, eval_C, eval_pow,
    eval_X, eval_ofNat] using stationaryPair_F1 h hp Y

theorem rootPolynomial_coeff_five (x : Configuration) :
    (rootPolynomial x).coeff 5 = 1 := by
  simpa only [rootPolynomial_natDegree] using (rootPolynomial_monic x).coeff_natDegree

 theorem stationaryPair_coefficients {x y : Configuration} (h : StationaryPair x y)
    {a b c d : ℂ} (hp : rootPolynomial x = quintic a b c d) :
    delta a b c d = complexDiscriminant x ∧
    r3 a b c d = 16 * delta a b c d * (rootPolynomial y).coeff 3 ∧
    r2 a b c d = 64 * delta a b c d * (rootPolynomial y).coeff 2 ∧
    r1 a b c d = 256 * delta a b c d * (rootPolynomial y).coeff 1 ∧
    r0 a b c d = 1024 * delta a b c d * (rootPolynomial y).coeff 0 ∧
    s2 a b c d = 0 ∧ s1 a b c d = 6*r3 a b c d ∧
    s0 a b c d = 2*r2 a b c d := by
  have h0 := stationaryPair_zero_polynomial h hp
  have h1 := stationaryPair_first_polynomial h hp
  have hd := congrArg (fun p : ℂ[X] => p.coeff 5) h0
  simp only [resultantZeroPolynomial, coeff_add, coeff_C_mul_X_pow, coeff_C_mul,
    coeff_C, coeff_X, rootPolynomial_coeff_five] at hd
  norm_num at hd
  have hr3 := congrArg (fun p : ℂ[X] => p.coeff 3) h0
  have hr2 := congrArg (fun p : ℂ[X] => p.coeff 2) h0
  have hr1 := congrArg (fun p : ℂ[X] => p.coeff 1) h0
  have hr0 := congrArg (fun p : ℂ[X] => p.coeff 0) h0
  have hs2 := congrArg (fun p : ℂ[X] => p.coeff 2) h1
  have hs1 := congrArg (fun p : ℂ[X] => p.coeff 1) h1
  have hs0 := congrArg (fun p : ℂ[X] => p.coeff 0) h1
  simp only [resultantZeroPolynomial, resultantFirstPolynomial, coeff_add,
    coeff_C_mul_X_pow, coeff_C_mul, coeff_C, coeff_X, coeff_mul, coeff_X_pow,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ] at hr3 hr2 hr1 hr0 hs2 hs1 hs0
  norm_num at hr3 hr2 hr1 hr0 hs2 hs1 hs0
  rw [← hd] at hr3 hr2 hr1 hr0 hs1 hs0
  refine ⟨hd, ?_, ?_, ?_, ?_, hs2, ?_, ?_⟩
  · rw [rootPolynomial_scale_coeff] at hr3
    norm_num at hr3
    linear_combination hr3
  · rw [rootPolynomial_scale_coeff] at hr2
    norm_num at hr2
    linear_combination hr2
  · rw [rootPolynomial_scale_coeff] at hr1
    norm_num at hr1
    linear_combination hr1
  · rw [rootPolynomial_scale_coeff] at hr0
    norm_num at hr0
    linear_combination hr0
  · linear_combination hs1 - (6 : ℂ)*hr3
  · linear_combination hs0 - (2 : ℂ)*hr2

structure CoefficientData (a b c d : ℂ) (κ D : ℝ) : Prop where
  kappa_pos : 0 < κ
  delta_ne : delta a b c d ≠ 0
  equation2 : s2 a b c d = 0
  equation1 : s1 a b c d = 6*r3 a b c d
  equation0 : s0 a b c d = 2*r2 a b c d
  dual3 : r3 a b c d = 16*delta a b c d*(κ : ℂ)^2*star a
  dual2 : r2 a b c d = 64*delta a b c d*(κ : ℂ)^3*star b
  dual1 : r1 a b c d = 256*delta a b c d*(κ : ℂ)^4*star c
  dual0 : r0 a b c d = 1024*delta a b c d*(κ : ℂ)^5*star d
  norm_relation : κ^20 * Complex.normSq (delta a b c d) = D^2

 theorem global_maximum_coefficientData {z : Configuration} (hz : IsGlobalMaximum z)
    {t a b c d : ℂ} (ht : t ≠ 0)
    (hp : rootPolynomial (fun i => t*z i) = quintic a b c d) :
    CoefficientData a b c d (physicalScale t) (discriminant z) := by
  have hpair := maximum_stationaryPair hz ht
  obtain ⟨hd,hr3,hr2,hr1,hr0,he2,he1,he0⟩ := stationaryPair_coefficients hpair hp
  refine ⟨physicalScale_pos ht, ?_, he2, he1, he0, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hd]
    exact complexDiscriminant_ne hpair.1
  · rw [dualScale_coeff z ht, hp] at hr3
    norm_num [quintic, coeff_X] at hr3
    change r3 a b c d = 16*delta a b c d*(star a*(physicalScale t : ℂ)^2) at hr3
    linear_combination hr3
  · rw [dualScale_coeff z ht, hp] at hr2
    norm_num [quintic, coeff_X] at hr2
    change r2 a b c d = 64*delta a b c d*(star b*(physicalScale t : ℂ)^3) at hr2
    linear_combination hr2
  · rw [dualScale_coeff z ht, hp] at hr1
    norm_num [quintic, coeff_X] at hr1
    change r1 a b c d = 256*delta a b c d*(star c*(physicalScale t : ℂ)^4) at hr1
    linear_combination hr1
  · rw [dualScale_coeff z ht, hp] at hr0
    norm_num [quintic, coeff_X] at hr0
    change r0 a b c d = 1024*delta a b c d*(star d*(physicalScale t : ℂ)^5) at hr0
    linear_combination hr0
  · rw [hd]
    exact physical_discriminant ht

end Mordell
