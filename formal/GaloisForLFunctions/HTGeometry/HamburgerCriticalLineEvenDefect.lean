import GaloisForLFunctions.HTGeometry.HamburgerThetaDefect

/-!
# The even Hamburger relation on the critical line, with a defect

Let `f(s) = Σ a_n n^{-s}` and `E(s) = Γ_ℝ(s) f(s) - β Γ_ℝ(s - 1)`, continuous on
`1/2 ≤ Re s ≤ 3/2`, holomorphic inside and `O(1/(1 + t²))`.  Suppose that on the critical line

`E(s) - E(1 - s) = -β (Γ_ℝ(s - 1) - Γ_ℝ(-s)) + d(s)`.

For `d = 0` this says that `Γ_ℝ f` is even across the line, which is Riemann's functional equation
(with the pole of `ζ`).  In general `d` measures the failure of the functional equation on the line.

**Theorem** (`critical_line_even_theta_relation_defect`).  For every `x > 0`,

`θ(x) - x^{-1/2} θ(1/x) = β (x^{-1/2} - 1) + (1/2π) ∫ x^{-(1/4+it)} d(1/2 + 2it) dt`.

Both theta values are inverse Mellin integrals over the critical line
(`critical_line_inverse_mellin`).  After reflecting `t ↦ -t`, their difference sees only
`E(s) - E(1 - s)`.  The Gamma part of that difference is the Mellin transform of
`-β (t^{-1/2}(e^{-πt} - 1) - (e^{-π/t} - 1))`.
-/

open Complex MeasureTheory Filter Topology Set

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- **The even theta relation from the critical line, with a defect.** -/
theorem critical_line_even_theta_relation_defect {θ : ℝ → ℂ} {E d : ℂ → ℂ} {β : ℂ} {C : ℝ}
    (hθc : ContinuousOn θ (Ioi 0)) (hθm : MellinConvergent θ (3 / 4))
    (hEc : ContinuousOn E (verticalStrip (1 / 2) (3 / 2)))
    (hEd : DifferentiableOn ℂ E {s : ℂ | 1 / 2 < s.re ∧ s.re < 3 / 2})
    (hdecay : ∀ s ∈ verticalStrip (1 / 2) (3 / 2), ‖E s‖ ≤ C / (1 + s.im ^ 2))
    (hR : ∀ s : ℂ, s.re = 3 / 2 → mellin θ (s / 2) = E s + β * Complex.Gammaℝ (s - 1))
    (hC : ∀ s : ℂ, s.re = 1 / 2 →
      E s - E (1 - s) = -(β * (Complex.Gammaℝ (s - 1) - Complex.Gammaℝ (-s))) + d s)
    (hdint : Integrable fun t : ℝ => d (2 * (((1 / 4 : ℝ) : ℂ) + t * I)))
    {x : ℝ} (hx : 0 < x) :
    θ x - (x : ℂ) ^ (-(1 / 2 : ℂ)) * θ x⁻¹ = β * ((x : ℂ) ^ (-(1 / 2 : ℂ)) - 1) +
      ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ, (x : ℂ) ^ (-(((1 / 4 : ℝ) : ℂ) + t * I)) *
        d (2 * (((1 / 4 : ℝ) : ℂ) + t * I)) := by
  have hR1 := critical_line_inverse_mellin hθc hθm hEc hEd hdecay hR hx
  have hR2 := critical_line_inverse_mellin hθc hθm hEc hEd hdecay hR (inv_pos.mpr hx)
  rw [Complex.real_smul] at hR1 hR2
  set K : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ) with hK
  have hre : ∀ t : ℝ, (2 * (((1 / 4 : ℝ) : ℂ) + t * I)).re = 1 / 2 := by
    intro t; simp; norm_num
  have hint1 : Integrable fun t : ℝ => (x : ℂ) ^ (-(((1 / 4 : ℝ) : ℂ) + t * I)) *
      E (2 * (((1 / 4 : ℝ) : ℂ) + t * I)) :=
    integrable_cpow_mul_comp_line hEc hdecay (by norm_num) (by norm_num) hx
  have hpt : ∀ t : ℝ, (x : ℂ) ^ (-(1 / 2 : ℂ)) *
      (((x⁻¹ : ℝ) : ℂ) ^ (-(((1 / 4 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I)) *
        E (2 * (((1 / 4 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I))) =
      (x : ℂ) ^ (-(((1 / 4 : ℝ) : ℂ) + t * I)) * E (1 - 2 * (((1 / 4 : ℝ) : ℂ) + t * I)) := by
    intro t
    rw [ofReal_inv_cpow_eq hx, ← mul_assoc, ofReal_cpow_mul_ofReal_cpow hx]
    push_cast
    congr 2 <;> ring
  have hint2 : Integrable fun t : ℝ => (x : ℂ) ^ (-(((1 / 4 : ℝ) : ℂ) + t * I)) *
      E (1 - 2 * (((1 / 4 : ℝ) : ℂ) + t * I)) := by
    have h := (integrable_cpow_mul_comp_line hEc hdecay (σ := 1 / 4) (by norm_num) (by norm_num)
      (inv_pos.mpr hx)).comp_neg
    exact ((h.const_mul ((x : ℂ) ^ (-(1 / 2 : ℂ))))).congr
      (Eventually.of_forall fun t => hpt t)
  have hreflect : (x : ℂ) ^ (-(1 / 2 : ℂ)) * ∫ t : ℝ,
      ((x⁻¹ : ℝ) : ℂ) ^ (-(((1 / 4 : ℝ) : ℂ) + t * I)) * E (2 * (((1 / 4 : ℝ) : ℂ) + t * I)) =
      ∫ t : ℝ, (x : ℂ) ^ (-(((1 / 4 : ℝ) : ℂ) + t * I)) *
        E (1 - 2 * (((1 / 4 : ℝ) : ℂ) + t * I)) := by
    rw [← integral_const_mul, ← integral_neg_eq_self]
    exact integral_congr_ae (Eventually.of_forall fun t => hpt t)
  have hhalf : (x : ℂ) ^ (-(1 / 2 : ℂ)) * ((x⁻¹ : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) = 1 := by
    rw [ofReal_inv_cpow_eq hx, ofReal_cpow_mul_ofReal_cpow hx]
    norm_num
  -- the defect integral
  have hcpow_meas : AEStronglyMeasurable
      (fun t : ℝ => (x : ℂ) ^ (-(((1 / 4 : ℝ) : ℂ) + t * I))) volume :=
    (Continuous.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast hx.ne'))).aestronglyMeasurable
  have hcpow_bound : ∀ t : ℝ, ‖(x : ℂ) ^ (-(((1 / 4 : ℝ) : ℂ) + t * I))‖ ≤ x ^ (-(1 / 4 : ℝ)) := by
    intro t
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
    simp
  have hintd : Integrable fun t : ℝ => (x : ℂ) ^ (-(((1 / 4 : ℝ) : ℂ) + t * I)) *
      d (2 * (((1 / 4 : ℝ) : ℂ) + t * I)) :=
    hdint.bdd_mul hcpow_meas (Eventually.of_forall hcpow_bound)
  set D : ℂ := ∫ t : ℝ, (x : ℂ) ^ (-(((1 / 4 : ℝ) : ℂ) + t * I)) *
      d (2 * (((1 / 4 : ℝ) : ℂ) + t * I)) with hD
  -- the Gamma-difference integral
  set J : ℂ := ∫ t : ℝ, (x : ℂ) ^ (-(((1 / 4 : ℝ) : ℂ) + t * I)) *
      (Complex.Gammaℝ (2 * (((1 / 4 : ℝ) : ℂ) + t * I) - 1) -
        Complex.Gammaℝ (-(2 * (((1 / 4 : ℝ) : ℂ) + t * I)))) with hJ
  have hpole : ∀ k : ℕ, (-(1 / 2 : ℝ)) ≠ -(2 * (k : ℝ)) := by
    intro k h
    have hk : (4 * (k : ℝ)) = 1 := by linarith
    have hk' : (4 * k : ℕ) = 1 := by exact_mod_cast hk
    omega
  have hΓline : ∀ z : ℝ, 0 < z → Integrable fun t : ℝ => (z : ℂ) ^ (-(((1 / 4 : ℝ) : ℂ) + t * I)) *
      (Complex.Gammaℝ (2 * (((1 / 4 : ℝ) : ℂ) + t * I) - 1) -
        Complex.Gammaℝ (-(2 * (((1 / 4 : ℝ) : ℂ) + t * I)))) := by
    intro z hz
    have hA := integrable_cpow_mul_Gammaℝ_line (σ := 1 / 4) (a := -(1 / 2 : ℝ)) (c := 2)
      hz (by norm_num) hpole
    have hB := integrable_cpow_mul_Gammaℝ_line (σ := 1 / 4) (a := -(1 / 2 : ℝ)) (c := -2)
      hz (by norm_num) hpole
    refine (hA.sub hB).congr (Eventually.of_forall fun t => ?_)
    have e1 : ((-(1 / 2 : ℝ) : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * I =
        2 * (((1 / 4 : ℝ) : ℂ) + t * I) - 1 := by push_cast; ring
    have e2 : ((-(1 / 2 : ℝ) : ℝ) : ℂ) + ((-2 * t : ℝ) : ℂ) * I =
        -(2 * (((1 / 4 : ℝ) : ℂ) + t * I)) := by push_cast; ring
    simp only [Pi.sub_apply]
    rw [e1, e2, mul_sub]
  have hΓint := hΓline x hx
  have hdiffint : (∫ t : ℝ, (x : ℂ) ^ (-(((1 / 4 : ℝ) : ℂ) + t * I)) *
      E (2 * (((1 / 4 : ℝ) : ℂ) + t * I))) - (∫ t : ℝ, (x : ℂ) ^ (-(((1 / 4 : ℝ) : ℂ) + t * I)) *
        E (1 - 2 * (((1 / 4 : ℝ) : ℂ) + t * I))) = -β * J + D := by
    rw [← integral_sub hint1 hint2, hJ, hD, ← integral_const_mul, ← integral_add
      (hΓint.const_mul _) hintd]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    beta_reduce
    have h := hC _ (hre t)
    have hE : E (2 * (((1 / 4 : ℝ) : ℂ) + t * I)) - E (1 - 2 * (((1 / 4 : ℝ) : ℂ) + t * I)) =
        -(β * (Complex.Gammaℝ (2 * (((1 / 4 : ℝ) : ℂ) + t * I) - 1) -
          Complex.Gammaℝ (-(2 * (((1 / 4 : ℝ) : ℂ) + t * I))))) +
        d (2 * (((1 / 4 : ℝ) : ℂ) + t * I)) := h
    rw [← mul_sub, hE]
    ring
  have hsub : (θ x - β * ((x : ℂ) ^ (-(1 / 2 : ℂ)) * expNegPi x)) -
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * (θ x⁻¹ - β * (((x⁻¹ : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) * expNegPi x⁻¹))
      = K * (-β * J + D) := by
    rw [hR1, hR2, ← hdiffint, ← hreflect]
    ring
  -- the correction function and its inverse Mellin transform
  set f₃ : ℝ → ℂ := fun u => (u : ℂ) ^ (-(1 / 2 : ℂ)) * expNegSubOne (Real.pi * u) -
    expNegSubOne (Real.pi * u⁻¹) with hf₃
  have hdata₃ : ∀ t : ℝ, HasMellin f₃ (((1 / 4 : ℝ) : ℂ) + t * I)
      (Complex.Gammaℝ (2 * (((1 / 4 : ℝ) : ℂ) + t * I) - 1) -
        Complex.Gammaℝ (-(2 * (((1 / 4 : ℝ) : ℂ) + t * I)))) := by
    intro t
    have hs := hre t
    have h2w : 2 * (((1 / 4 : ℝ) : ℂ) + t * I) / 2 = ((1 / 4 : ℝ) : ℂ) + t * I := by ring
    have hA := hasMellin_halfPow_expNegSubOne_pi (s := 2 * (((1 / 4 : ℝ) : ℂ) + t * I))
      (by rw [hs]; norm_num) (by rw [hs]; norm_num)
    have hB := hasMellin_expNegSubOne_pi_inv (s := 2 * (((1 / 4 : ℝ) : ℂ) + t * I))
      (by rw [hs]; norm_num) (by rw [hs]; norm_num)
    rw [h2w] at hA hB
    have hC' := hasMellin_sub hA.1 hB.1
    refine ⟨hC'.1, ?_⟩
    have h := hC'.2
    rw [hA.2, hB.2] at h
    exact h
  have hJf : J = (2 * Real.pi) * f₃ x := by
    have hvert : VerticalIntegrable (mellin f₃) (1 / 4 : ℝ) := by
      refine (hΓline 1 one_pos).congr (Eventually.of_forall fun t => ?_)
      simp only [ofReal_one, one_cpow, one_mul]
      exact ((hdata₃ t).2).symm
    have hconv₃ : MellinConvergent f₃ ((1 / 4 : ℝ) : ℂ) := by simpa using (hdata₃ 0).1
    have hcont₃ : ContinuousAt f₃ x := by
      have h1 : ContinuousAt (fun u : ℝ => (u : ℂ) ^ (-(1 / 2 : ℂ))) x :=
        continuousAt_ofReal_cpow_const _ _ (Or.inr hx.ne')
      have h2 : ContinuousAt (fun u : ℝ => expNegSubOne (Real.pi * u)) x :=
        (continuous_expNegSubOne.comp (continuous_const.mul continuous_id)).continuousAt
      have h3 : ContinuousAt (fun u : ℝ => expNegSubOne (Real.pi * u⁻¹)) x :=
        continuous_expNegSubOne.continuousAt.comp
          (continuousAt_const.mul (continuousAt_inv₀ hx.ne'))
      exact (h1.mul h2).sub h3
    have hinv₃ := mellinInv_mellin_eq (1 / 4 : ℝ) f₃ hx hconv₃ hvert hcont₃
    unfold mellinInv at hinv₃
    rw [Complex.real_smul] at hinv₃
    have hJ' : J = ∫ t : ℝ, (x : ℂ) ^ (-(((1 / 4 : ℝ) : ℂ) + t * I)) •
        mellin f₃ (((1 / 4 : ℝ) : ℂ) + t * I) := by
      rw [hJ]
      refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      beta_reduce
      rw [smul_eq_mul, (hdata₃ t).2]
    have hc : ((1 / (2 * Real.pi) : ℝ) : ℂ) * (2 * Real.pi) = 1 := by
      have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      push_cast
      field_simp
    rw [← hinv₃, hJ']
    linear_combination (-(∫ t : ℝ, (x : ℂ) ^ (-(((1 / 4 : ℝ) : ℂ) + t * I)) •
      mellin f₃ (((1 / 4 : ℝ) : ℂ) + t * I))) * hc
  have hf₃x : f₃ x = (x : ℂ) ^ (-(1 / 2 : ℂ)) * (expNegPi x - 1) - (expNegPi x⁻¹ - 1) := by
    simp only [hf₃, expNegSubOne_pi_mul]
  have hK2 : K * (2 * Real.pi) = 1 := by
    rw [hK]
    push_cast
    field_simp
  have hmain : K * (-β * J + D) = -(β * f₃ x) + K * D := by
    rw [hJf]
    linear_combination (-(β * f₃ x)) * hK2
  rw [hmain, hf₃x] at hsub
  linear_combination hsub - β * expNegPi x⁻¹ * hhalf

end GaloisForLFunctions.HTGeometry
