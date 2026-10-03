import Mordell.GenericBound
import Mordell.ExceptionalBound
import Mordell.NormalizeCoefficients
import Mordell.RootPentagon

namespace Mordell
open ResultantAlgebra
set_option maxHeartbeats 0
set_option maxRecDepth 10000

/-- Every global maximizer is a rotated and relabeled unit regular pentagon. -/
theorem maxima_classification : MaximaClassification := by
  intro z hz
  let a := (rootPolynomial z).coeff 3
  let b := (rootPolynomial z).coeff 2
  let c := (rootPolynomial z).coeff 1
  let d := (rootPolynomial z).coeff 0
  have hp : rootPolynomial z = quintic a b c d :=
    rootPolynomial_quintic (global_maximum_centered hz)
  have hlo := global_maximum_lower_bound hz
  have hnonneg := discriminant_nonneg z
  by_cases ha : a = 0
  · by_cases hb : b = 0
    · rw [ha,hb] at hp
      have hdata : CoefficientData 0 0 c d (physicalScale 1) (discriminant z) := by
        apply global_maximum_coefficientData hz (by norm_num : (1 : ℂ) ≠ 0)
        simpa only [one_mul] using hp
      rcases exceptional_zero_cd hdata with hc | hd
      · have hd' : d ≠ 0 := by
          intro he
          have hh := hdata.delta_ne
          rw [hc,he] at hh
          norm_num [delta] at hh
        rw [hc] at hp
        exact rootPolynomial_pentagon hz.1
          (injective_of_discriminant_pos (global_maximum_positive hz)) hd' hp
      · rw [hd] at hdata
        have hsmall := exceptional_square_bound hdata hnonneg
        linarith
    · obtain ⟨t,ht,he⟩ := normalize_nonzero b hb 3 (by decide)
      have hp' := quintic_scale hp t
      rw [ha,zero_mul,he] at hp'
      have hdata := global_maximum_coefficientData hz ht hp'
      exact (exceptional_one_impossible hdata).elim
  · obtain ⟨t,ht,he⟩ := normalize_nonzero a ha 2 (by decide)
    have hp' := quintic_scale hp t
    rw [he] at hp'
    have hdata := global_maximum_coefficientData hz ht hp'
    by_cases hb : b*t^3 = 0
    · rw [hb] at hdata
      have hsmall := exceptional_ten_bound hdata hnonneg
      linarith
    · let k := (d*t^5)/(b*t^3)
      have he' : d*t^5 = (b*t^3)*k := by
        dsimp only [k]
        rw [mul_div_cancel₀ _ hb]
      rw [he'] at hdata
      have hsmall := generic_bound hdata hb hnonneg
      linarith

/-- Mordell's five-point inequality, including its exact equality characterization. -/
theorem original : OriginalStatement :=
  original_of_maxima_classification maxima_classification

end Mordell
