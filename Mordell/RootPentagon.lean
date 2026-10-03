import Mordell.Quintic
import Mordell.Reduction

namespace Mordell
open Polynomial

 theorem equal_fifth_powers_regular {z : Configuration} (hs : normSum z = 5)
    (hi : Function.Injective z) {w : ℂ} (hw : w ≠ 0)
    (hp : ∀ i, z i^5 = w) : RegularPentagon z := by
  classical
  let u := z 0
  have hu : u ≠ 0 := by
    intro he
    have hh := hp 0
    simp only [u] at he
    rw [he, zero_pow (by decide)] at hh
    exact hw hh.symm
  let ω := Complex.exp (2*Real.pi*Complex.I/5)
  have hω : IsPrimitiveRoot ω 5 := Complex.isPrimitiveRoot_exp 5 (by decide)
  have hzpow (i : Fin 5) : (z i/u)^5 = 1 := by
    rw [div_pow, hp i, show u^5 = w from hp 0]
    exact div_self hw
  have hchoose (i : Fin 5) : ∃ j : Fin 5, ω^j.val = z i/u := by
    obtain ⟨j,hj,he⟩ := hω.eq_pow_of_pow_eq_one (hzpow i)
    exact ⟨⟨j,hj⟩,he⟩
  let f : Fin 5 → Fin 5 := fun i => Classical.choose (hchoose i)
  have hf (i : Fin 5) : ω^(f i).val = z i/u := Classical.choose_spec (hchoose i)
  have he (i : Fin 5) : z i = u*ω^(f i).val := by
    rw [hf, mul_div_cancel₀ _ hu]
  have hfi : Function.Injective f := by
    intro i j hij
    apply hi
    rw [he i, he j, hij]
  let σ : Equiv.Perm (Fin 5) := Equiv.ofBijective f
    ⟨hfi, Finite.surjective_of_injective hfi⟩
  have he' (i : Fin 5) : z i = u*ω^(σ i).val := he i
  have hnorm : Complex.normSq u = 1 := by
    have hx : z = fun i => u*ω^(σ i).val := funext he'
    rw [hx, normSum_scale, normSum_relabel (fun i : Fin 5 => ω^i.val) σ, power_pentagon_constraint hω] at hs
    linarith
  exact ⟨u,ω,hnorm,hω,σ,he'⟩

 theorem rootPolynomial_pentagon {z : Configuration} (hs : normSum z = 5)
    (hi : Function.Injective z) {d : ℂ} (hd : d ≠ 0)
    (hp : rootPolynomial z = quintic 0 0 0 d) : RegularPentagon z := by
  apply equal_fifth_powers_regular hs hi (neg_ne_zero.mpr hd)
  intro i
  have he := rootPolynomial_eval z i
  rw [hp] at he
  norm_num [quintic] at he
  linear_combination he

end Mordell
