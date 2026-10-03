import Mordell.GenericInputs

namespace Mordell
open ResultantAlgebra
set_option maxHeartbeats 0
set_option maxRecDepth 10000

 theorem physical_B_real {b c k : ℂ} {κ D : ℝ}
    (h : CoefficientData 1 b c (b*k) κ D)
    (hr : delta 1 b c (b*k) * (r2 1 b c (b*k))^2 = b^2 * (r3 1 b c (b*k))^3) :
    b^2 = ((b^2).re : ℂ) := by
  have hk : (κ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt h.kappa_pos
  have he : (4096 * (delta 1 b c (b*k))^3 * (κ : ℂ)^6) *
      ((star b)^2 - b^2) = 0 := by
    rw [h.dual2, h.dual3] at hr
    simp only [star_one] at hr
    linear_combination hr
  have hs : (star b)^2 = b^2 := sub_eq_zero.mp
    ((mul_eq_zero.mp he).resolve_left
      (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ h.delta_ne)) (pow_ne_zero _ hk)))
  have hh : star (b^2) = b^2 := by simpa only [star_pow] using hs
  have hi := congrArg Complex.im hh
  simp only [Complex.star_def, Complex.conj_im] at hi
  apply Complex.ext
  · simp
  · simp only [Complex.ofReal_im]
    linarith

 theorem physical_value_bound {b c k A V : ℂ} {κ D : ℝ}
    (h : CoefficientData 1 b c (b*k) κ D)
    (ha : 16*delta 1 b c (b*k)*A = r3 1 b c (b*k))
    (hv : A^5 * delta 1 b c (b*k) = V)
    {v : ℝ} (hvr : V = (v : ℂ)) (hbound : -3125 < v ∧ v < 3125)
    (hD : 0 ≤ D) : D < 3125 := by
  have he := h.dual3
  simp only [star_one, mul_one] at he
  have hA : A = (κ : ℂ)^2 := by
    apply (mul_left_cancel₀ (mul_ne_zero (by norm_num : (16 : ℂ) ≠ 0) h.delta_ne))
    exact ha.trans he
  have hv' : (κ : ℂ)^10 * delta 1 b c (b*k) = (v : ℂ) := by
    rw [hA, ← pow_mul] at hv
    exact hv.trans hvr
  have hn := congrArg Complex.normSq hv'
  simp only [map_mul, map_pow, Complex.normSq_ofReal] at hn
  have hsq : D^2 = v^2 := by
    rw [← h.norm_relation]
    nlinarith [hn]
  nlinarith [hbound.1,hbound.2]

 theorem generic_branch1 {ss b c k : ℂ} {κ D : ℝ}
    (h : CoefficientData 1 b c (b*k) κ D)
    (hc : Elimination.g259 ss k c (b^2) = 0)
    (hk : Elimination.g260 ss k c (b^2) = 0)
    (hp : Branches.P1 (b^2) = 0) (hD : 0 ≤ D) : D < 3125 := by
  have hcg := Branches.c_graph1 ss k c (b^2)
  have hkg := Branches.k_graph1 ss k c (b^2)
  rw [hc, hp] at hcg
  rw [hk, hp] at hkg
  have hc' : c = Branches.C1 (b^2) := by linear_combination hcg / (10910650458082468806374400 : ℂ)
  have hk' : k = Branches.K1 (b^2) := by linear_combination hkg / (72737669720549792042496000 : ℂ)
  have hd := Branches.delta_reduce1 ss k c (b^2)
  have hr := Branches.r3_reduce1 ss k c (b^2)
  have ht := Branches.r2_reduce1 ss k c (b^2)
  rw [hp, zero_mul] at hd hr ht
  have hd' : delta 1 b c (b*k) = Branches.D1 (b^2) := by
    rw [generic_delta, hc', hk']
    exact sub_eq_zero.mp hd
  have hr' : r3 1 b c (b*k) = Branches.R1 (b^2) := by
    rw [generic_r3, hc', hk']
    exact sub_eq_zero.mp hr
  have ht' : r2 1 b c (b*k) = b*Branches.T1 (b^2) := by
    rw [generic_r2, hc', hk', sub_eq_zero.mp ht]
  have hdual := Branches.dual_reduce1 ss k c (b^2)
  rw [hp, zero_mul] at hdual
  have hrel : delta 1 b c (b*k) * (r2 1 b c (b*k))^2 =
      b^2 * (r3 1 b c (b*k))^3 := by
    rw [hd', hr', ht']
    linear_combination b^2 * hdual
  have hreal := physical_B_real h hrel
  have har := Branches.ratio_reduce1 ss k c (b^2)
  have hvr := Branches.value_reduce1 ss k c (b^2)
  rw [hp, zero_mul] at har hvr
  have ha : 16*delta 1 b c (b*k)*Branches.A1 (b^2) = r3 1 b c (b*k) := by
    rw [hd',hr']
    exact sub_eq_zero.mp har
  have hv : (Branches.A1 (b^2))^5*delta 1 b c (b*k) = Branches.V1 (b^2) := by
    rw [hd']
    exact sub_eq_zero.mp hvr
  have hpc : Branches.P1 (((b^2).re : ℝ) : ℂ) =
      (AlgebraicBounds.p1.eval (fun _ => (b^2).re) : ℂ) := by
    simp only [Branches.P1, AlgebraicBounds.p1, Expr.eval]
    push_cast
    ring
  have hpr : AlgebraicBounds.p1.eval (fun _ => (b^2).re) = 0 := by
    rw [hreal, hpc] at hp
    exact_mod_cast hp
  have hvc : Branches.V1 (b^2) =
      (AlgebraicBounds.v1.eval (fun _ => (b^2).re) : ℂ) := by
    rw [hreal]
    simp only [Branches.V1, AlgebraicBounds.v1, Expr.eval,Complex.ofReal_re]
    push_cast
    ring
  exact physical_value_bound h ha hv hvc
    (AlgebraicBounds.root1_value (b^2).re hpr) hD

 theorem generic_branch2 {ss b c k : ℂ} {κ D : ℝ}
    (h : CoefficientData 1 b c (b*k) κ D)
    (hc : Elimination.g259 ss k c (b^2) = 0)
    (hk : Elimination.g260 ss k c (b^2) = 0)
    (hp : Branches.P2 (b^2) = 0) (hD : 0 ≤ D) : D < 3125 := by
  have hcg := Branches.c_graph2 ss k c (b^2)
  have hkg := Branches.k_graph2 ss k c (b^2)
  rw [hc, hp] at hcg
  rw [hk, hp] at hkg
  have hc' : c = Branches.C2 (b^2) := by linear_combination hcg / (10910650458082468806374400 : ℂ)
  have hk' : k = Branches.K2 (b^2) := by linear_combination hkg / (72737669720549792042496000 : ℂ)
  have hd := Branches.delta_reduce2 ss k c (b^2)
  have hr := Branches.r3_reduce2 ss k c (b^2)
  have ht := Branches.r2_reduce2 ss k c (b^2)
  rw [hp, zero_mul] at hd hr ht
  have hd' : delta 1 b c (b*k) = Branches.D2 (b^2) := by
    rw [generic_delta, hc', hk']
    exact sub_eq_zero.mp hd
  have hr' : r3 1 b c (b*k) = Branches.R2 (b^2) := by
    rw [generic_r3, hc', hk']
    exact sub_eq_zero.mp hr
  have ht' : r2 1 b c (b*k) = b*Branches.T2 (b^2) := by
    rw [generic_r2, hc', hk', sub_eq_zero.mp ht]
  have hdual := Branches.dual_reduce2 ss k c (b^2)
  rw [hp, zero_mul] at hdual
  have hrel : delta 1 b c (b*k) * (r2 1 b c (b*k))^2 =
      b^2 * (r3 1 b c (b*k))^3 := by
    rw [hd', hr', ht']
    linear_combination b^2 * hdual
  have hreal := physical_B_real h hrel
  have har := Branches.ratio_reduce2 ss k c (b^2)
  have hvr := Branches.value_reduce2 ss k c (b^2)
  rw [hp, zero_mul] at har hvr
  have ha : 16*delta 1 b c (b*k)*Branches.A2 (b^2) = r3 1 b c (b*k) := by
    rw [hd',hr']
    exact sub_eq_zero.mp har
  have hv : (Branches.A2 (b^2))^5*delta 1 b c (b*k) = Branches.V2 (b^2) := by
    rw [hd']
    exact sub_eq_zero.mp hvr
  have hpc : Branches.P2 (((b^2).re : ℝ) : ℂ) =
      (AlgebraicBounds.p2.eval (fun _ => (b^2).re) : ℂ) := by
    simp only [Branches.P2, AlgebraicBounds.p2, Expr.eval]
    push_cast
    ring
  have hpr : AlgebraicBounds.p2.eval (fun _ => (b^2).re) = 0 := by
    rw [hreal, hpc] at hp
    exact_mod_cast hp
  have hvc : Branches.V2 (b^2) =
      (AlgebraicBounds.v2.eval (fun _ => (b^2).re) : ℂ) := by
    rw [hreal]
    simp only [Branches.V2, AlgebraicBounds.v2, Expr.eval,Complex.ofReal_re]
    push_cast
    ring
  exact physical_value_bound h ha hv hvc
    (AlgebraicBounds.root2_value (b^2).re hpr) hD

 theorem generic_bound {b c k : ℂ} {κ D : ℝ}
    (h : CoefficientData 1 b c (b*k) κ D) (hb : b ≠ 0) (hD : 0 ≤ D) : D < 3125 := by
  obtain ⟨ss,h0,h1,h2,h3⟩ := generic_inputs h hb
  have hp := Elimination.projection ss k c (b^2) h0 h1 h2 h3
  have hc := Elimination.c_graph ss k c (b^2) h0 h1 h2 h3
  have hk := Elimination.k_graph ss k c (b^2) h0 h1 h2 h3
  have he : Elimination.g258 ss k c (b^2) = Branches.P1 (b^2)*Branches.P2 (b^2) := by
    dsimp only [Elimination.g258, Branches.P1, Branches.P2]
    ring
  rw [he] at hp
  rcases mul_eq_zero.mp hp with hp | hp
  · exact generic_branch1 h hc hk hp hD
  · exact generic_branch2 h hc hk hp hD

end Mordell
