import Mordell.Exceptional

namespace Mordell
open ResultantAlgebra
set_option maxHeartbeats 0
set_option maxRecDepth 10000

 theorem exceptional_ten_equations (ss c d : ℂ) :
    s2 1 0 c d = 4*Exceptional.Ten.g0 ss d c ∧
    s1 1 0 c d - 6*r3 1 0 c d = 96*Exceptional.Ten.g1 ss d c ∧
    s0 1 0 c d - 2*r2 1 0 c d = 16*Exceptional.Ten.g2 ss d c ∧
    r2 1 0 c d = 32*Exceptional.Ten.g3 ss d c ∧
    Exceptional.Ten.g4 ss d c = ss*delta 1 0 c d - 1 := by
  dsimp only [s2,s1,s0,r3,r2,delta,Exceptional.Ten.g0,Exceptional.Ten.g1,
    Exceptional.Ten.g2,Exceptional.Ten.g3,Exceptional.Ten.g4]
  refine ⟨?_,?_,?_,?_,?_⟩ <;> ring

 theorem exceptional_one_equations (ss c d : ℂ) :
    s2 0 1 c d = 4*Exceptional.One.g0 ss d c ∧
    s1 0 1 c d - 6*r3 0 1 c d = 48*Exceptional.One.g1 ss d c ∧
    s0 0 1 c d - 2*r2 0 1 c d = 80*Exceptional.One.g2 ss d c ∧
    r3 0 1 c d = 4*Exceptional.One.g3 ss d c ∧
    Exceptional.One.g4 ss d c = ss*delta 0 1 c d - 1 := by
  dsimp only [s2,s1,s0,r3,r2,delta,Exceptional.One.g0,Exceptional.One.g1,
    Exceptional.One.g2,Exceptional.One.g3,Exceptional.One.g4]
  refine ⟨?_,?_,?_,?_,?_⟩ <;> ring

 theorem exceptional_ten_coefficients {c d : ℂ} {κ D : ℝ}
    (h : CoefficientData 1 0 c d κ D) : c = 3/20 ∧ d = 0 := by
  let ss := (delta 1 0 c d)⁻¹
  obtain ⟨e0,e1,e2,e3,e4⟩ := exceptional_ten_equations ss c d
  have h0 : Exceptional.Ten.g0 ss d c = 0 := by
    rw [h.equation2] at e0
    exact (mul_eq_zero.mp e0.symm).resolve_left (by norm_num)
  have h1 : Exceptional.Ten.g1 ss d c = 0 := by
    rw [h.equation1, sub_self] at e1
    exact (mul_eq_zero.mp e1.symm).resolve_left (by norm_num)
  have h2 : Exceptional.Ten.g2 ss d c = 0 := by
    rw [h.equation0, sub_self] at e2
    exact (mul_eq_zero.mp e2.symm).resolve_left (by norm_num)
  have h3 : Exceptional.Ten.g3 ss d c = 0 := by
    have hz := h.dual2
    simp only [star_zero, mul_zero] at hz
    rw [hz] at e3
    exact (mul_eq_zero.mp e3.symm).resolve_left (by norm_num)
  have h4 : Exceptional.Ten.g4 ss d c = 0 := by
    rw [e4]
    simp only [ss, inv_mul_cancel₀ h.delta_ne, sub_self]
  have hc := Exceptional.Ten.zero24 ss d c h0 h1 h2 h3 h4
  have hd := Exceptional.Ten.zero27 ss d c h0 h1 h2 h3 h4
  simp only [Exceptional.Ten.g24] at hc
  simp only [Exceptional.Ten.g27] at hd
  constructor
  · linear_combination hc / (20 : ℂ)
  · simpa only [one_mul] using hd

 theorem exceptional_one_impossible {c d : ℂ} {κ D : ℝ}
    (h : CoefficientData 0 1 c d κ D) : False := by
  let ss := (delta 0 1 c d)⁻¹
  obtain ⟨e0,e1,e2,e3,e4⟩ := exceptional_one_equations ss c d
  have h0 : Exceptional.One.g0 ss d c = 0 := by
    rw [h.equation2] at e0
    exact (mul_eq_zero.mp e0.symm).resolve_left (by norm_num)
  have h1 : Exceptional.One.g1 ss d c = 0 := by
    rw [h.equation1, sub_self] at e1
    exact (mul_eq_zero.mp e1.symm).resolve_left (by norm_num)
  have h2 : Exceptional.One.g2 ss d c = 0 := by
    rw [h.equation0, sub_self] at e2
    exact (mul_eq_zero.mp e2.symm).resolve_left (by norm_num)
  have h3 : Exceptional.One.g3 ss d c = 0 := by
    have hz := h.dual3
    simp only [star_zero, mul_zero] at hz
    rw [hz] at e3
    exact (mul_eq_zero.mp e3.symm).resolve_left (by norm_num)
  have h4 : Exceptional.One.g4 ss d c = 0 := by
    rw [e4]
    simp only [ss, inv_mul_cancel₀ h.delta_ne, sub_self]
  have he := Exceptional.One.zero27 ss d c h0 h1 h2 h3 h4
  norm_num [Exceptional.One.g27] at he

 theorem exceptional_ten_bound {c d : ℂ} {κ D : ℝ}
    (h : CoefficientData 1 0 c d κ D) (hD : 0 ≤ D) : D < 3125 := by
  obtain ⟨hc,hd⟩ := exceptional_ten_coefficients h
  rw [hc,hd] at h
  have he := h.dual3
  norm_num [r3,delta] at he
  have hk : κ^2 = 25/4 := by
    have hz : (κ : ℂ)^2 = 25/4 := by linear_combination -he * (3125/432 : ℂ)
    have hz' : ((κ^2 : ℝ) : ℂ) = ((25/4 : ℝ) : ℂ) := by simpa only [Complex.ofReal_pow,Complex.ofReal_div,Complex.ofReal_ofNat] using hz
    exact Complex.ofReal_injective hz'
  have hn := h.norm_relation
  norm_num [delta, Complex.normSq] at hn
  have hpow : κ^20 = (25/4 : ℝ)^10 := by
    rw [show 20 = 2*10 by decide, pow_mul,hk]
  rw [hpow] at hn
  norm_num at hn
  nlinarith

 theorem exceptional_zero_cd {c d : ℂ} {κ D : ℝ}
    (h : CoefficientData 0 0 c d κ D) : c = 0 ∨ d = 0 := by
  have he : 50000*c*d^3 = 0 := by
    have hh := h.equation2
    dsimp only [s2] at hh
    linear_combination hh
  rcases mul_eq_zero.mp he with he | he
  · left
    exact (mul_eq_zero.mp he).resolve_left (by norm_num)
  · right
    exact eq_zero_of_pow_eq_zero he

 theorem exceptional_square_bound {c : ℂ} {κ D : ℝ}
    (h : CoefficientData 0 0 c 0 κ D) (hD : 0 ≤ D) : D < 3125 := by
  have hd : delta 0 0 c 0 = 256*c^5 := by simp [delta]
  have hc : c ≠ 0 := by
    intro he
    have hh := h.delta_ne
    rw [hd,he] at hh
    norm_num at hh
  have he := h.dual1
  have he' : c^4 * (160000 - 65536*(κ : ℂ)^4*c*star c) = 0 := by
    dsimp only [r1,delta] at he
    linear_combination he
  have hh := (mul_eq_zero.mp he').resolve_left (pow_ne_zero _ hc)
  have hn : (κ : ℂ)^4 * (Complex.normSq c : ℂ) = 625/256 := by
    rw [Complex.normSq_eq_conj_mul_self]
    change (κ : ℂ)^4 * (star c*c) = 625/256
    linear_combination -hh / (65536 : ℂ)
  have hn' : κ^4 * Complex.normSq c = 625/256 := by
    apply Complex.ofReal_injective
    simpa only [Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_div,Complex.ofReal_ofNat] using hn
  have hs := h.norm_relation
  rw [hd] at hs
  simp only [map_mul,map_pow] at hs
  norm_num at hs
  have hp : κ^20 * (Complex.normSq c)^5 = (625/256 : ℝ)^5 := by
    rw [← hn',mul_pow,←pow_mul]
  have hsq : D^2 = 65536*(625/256 : ℝ)^5 := by nlinarith [hs,hp]
  norm_num at hsq
  nlinarith

end Mordell
