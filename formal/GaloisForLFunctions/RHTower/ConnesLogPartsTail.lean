import GaloisForLFunctions.RHTower.ConnesSchwartzLogDecay

/-!
# Step 2, the tail: integration by parts on `[1, ∞)`

Step 2 of the route to the last §V identification of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

On `[1, ∞)` the primitive of `G'(u) log u + G(u)/u` is `G(u) log u`, which vanishes at `1`
(because `log 1 = 0`) and at `∞` (`ConnesSchwartzLogDecay`).  Hence

  `∫_{(1,∞)} (G'(u) log u + G(u)/u) du = 0`.
-/

open MeasureTheory Set Filter Topology Real
open scoped SchwartzMap

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- `deriv` of a Schwartz map is its `derivCLM`. -/
theorem connes_deriv_eq_derivCLM (G : 𝓢(ℝ, ℂ)) (u : ℝ) :
    deriv ((G : 𝓢(ℝ, ℂ)) : ℝ → ℂ) u = (SchwartzMap.derivCLM ℂ ℂ G) u := by
  rw [SchwartzMap.derivCLM_apply]

/-- A Schwartz function decays like every inverse power. -/
theorem connes_schwartz_le_pow (G : 𝓢(ℝ, ℂ)) (k : ℕ) {u : ℝ} (hu : 0 < u) :
    ‖(G : ℝ → ℂ) u‖ ≤ (SchwartzMap.seminorm ℂ k 0 G) / u ^ k := by
  have hsem := SchwartzMap.norm_pow_mul_le_seminorm ℂ G k u
  rw [Real.norm_eq_abs, abs_of_pos hu] at hsem
  rw [le_div_iff₀ (by positivity)]
  calc ‖(G : ℝ → ℂ) u‖ * u ^ k = u ^ k * ‖(G : ℝ → ℂ) u‖ := by ring
    _ ≤ _ := hsem

/-- The complex logarithm of a positive real, differentiated. -/
theorem connes_hasDerivAt_ofReal_log {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun u : ℝ => ((Real.log u : ℝ) : ℂ)) ((x⁻¹ : ℝ) : ℂ) x := by
  have h := Real.hasDerivAt_log hx
  exact Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x h

/-- The primitive on the tail. -/
theorem connes_hasDerivAt_mul_log (G : 𝓢(ℝ, ℂ)) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun u : ℝ => (G : ℝ → ℂ) u * ((Real.log u : ℝ) : ℂ))
      (deriv ((G : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x * ((Real.log x : ℝ) : ℂ)
        + (G : ℝ → ℂ) x * ((x⁻¹ : ℝ) : ℂ)) x := by
  have hG : HasDerivAt ((G : 𝓢(ℝ, ℂ)) : ℝ → ℂ) (deriv ((G : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x) x :=
    (G.differentiable.differentiableAt).hasDerivAt
  exact hG.mul (connes_hasDerivAt_ofReal_log hx)

/-- The tail integrand is integrable. -/
theorem connes_tail_integrand_integrable (G : 𝓢(ℝ, ℂ)) :
    IntegrableOn (fun u : ℝ => deriv ((G : 𝓢(ℝ, ℂ)) : ℝ → ℂ) u * ((Real.log u : ℝ) : ℂ)
      + (G : ℝ → ℂ) u * ((u⁻¹ : ℝ) : ℂ)) (Ioi (1 : ℝ)) volume := by
  set D : 𝓢(ℝ, ℂ) := SchwartzMap.derivCLM ℂ ℂ G with hD
  set σ₃ : ℝ := SchwartzMap.seminorm ℂ 3 0 D with hσ₃
  set σ₂ : ℝ := SchwartzMap.seminorm ℂ 2 0 G with hσ₂
  have hσ₃0 : (0 : ℝ) ≤ σ₃ := apply_nonneg _ D
  have hσ₂0 : (0 : ℝ) ≤ σ₂ := apply_nonneg _ G
  have hpow : IntegrableOn (fun u : ℝ => u ^ (-(2 : ℝ))) (Ioi (1 : ℝ)) volume :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos
  have hmaj : IntegrableOn (fun u : ℝ => (σ₃ + σ₂) * u ^ (-(2 : ℝ))) (Ioi (1 : ℝ)) volume :=
    hpow.const_mul _
  refine Integrable.mono' hmaj ?_ ?_
  · refine AEStronglyMeasurable.add ?_ ?_
    · refine AEStronglyMeasurable.restrict ?_
      refine AEStronglyMeasurable.mul ?_ ?_
      · exact ((SchwartzMap.derivCLM ℂ ℂ G).continuous.aestronglyMeasurable).congr
          (Filter.Eventually.of_forall fun u => (connes_deriv_eq_derivCLM G u).symm)
      · exact (Complex.measurable_ofReal.comp Real.measurable_log).aestronglyMeasurable
    · refine AEStronglyMeasurable.restrict ?_
      refine AEStronglyMeasurable.mul (G.continuous.aestronglyMeasurable) ?_
      exact (Complex.measurable_ofReal.comp (measurable_inv)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu1 : (1 : ℝ) < u := hu
    have hu0 : (0 : ℝ) < u := lt_trans zero_lt_one hu1
    have hlognn : (0 : ℝ) ≤ Real.log u := Real.log_nonneg hu1.le
    have hlogle : Real.log u ≤ u := by
      have := Real.log_le_sub_one_of_pos hu0
      linarith
    have hDeq : deriv ((G : 𝓢(ℝ, ℂ)) : ℝ → ℂ) u = (D : ℝ → ℂ) u := by
      rw [hD]
      exact connes_deriv_eq_derivCLM G u
    have hinv : (0 : ℝ) < u ^ (-(2 : ℝ)) := Real.rpow_pos_of_pos hu0 _
    have hu2 : u ^ (-(2 : ℝ)) = (u ^ 2)⁻¹ := by
      rw [Real.rpow_neg hu0.le, ← Real.rpow_natCast u 2]
      norm_num
    have h1 : ‖deriv ((G : 𝓢(ℝ, ℂ)) : ℝ → ℂ) u * ((Real.log u : ℝ) : ℂ)‖
        ≤ σ₃ * u ^ (-(2 : ℝ)) := by
      rw [hDeq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlognn, hu2]
      have hDb := connes_schwartz_le_pow D 3 hu0
      calc ‖(D : ℝ → ℂ) u‖ * Real.log u ≤ (σ₃ / u ^ 3) * u :=
            mul_le_mul hDb hlogle hlognn (by positivity)
        _ = σ₃ * (u ^ 2)⁻¹ := by field_simp
    have h2 : ‖(G : ℝ → ℂ) u * ((u⁻¹ : ℝ) : ℂ)‖ ≤ σ₂ * u ^ (-(2 : ℝ)) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity), hu2]
      have hGb := connes_schwartz_le_pow G 2 hu0
      have hle1 : u⁻¹ ≤ 1 := by
        rw [inv_le_one_iff₀]
        right
        exact hu1.le
      calc ‖(G : ℝ → ℂ) u‖ * u⁻¹ ≤ (σ₂ / u ^ 2) * 1 :=
            mul_le_mul hGb hle1 (by positivity) (by positivity)
        _ = σ₂ * (u ^ 2)⁻¹ := by field_simp
    calc ‖deriv ((G : 𝓢(ℝ, ℂ)) : ℝ → ℂ) u * ((Real.log u : ℝ) : ℂ)
          + (G : ℝ → ℂ) u * ((u⁻¹ : ℝ) : ℂ)‖
        ≤ ‖deriv ((G : 𝓢(ℝ, ℂ)) : ℝ → ℂ) u * ((Real.log u : ℝ) : ℂ)‖
          + ‖(G : ℝ → ℂ) u * ((u⁻¹ : ℝ) : ℂ)‖ := norm_add_le _ _
      _ ≤ σ₃ * u ^ (-(2 : ℝ)) + σ₂ * u ^ (-(2 : ℝ)) := add_le_add h1 h2
      _ = (σ₃ + σ₂) * u ^ (-(2 : ℝ)) := by ring

/-- **Step 2, the tail.**  `∫_{(1,∞)} (G'(u) log u + G(u)/u) du = 0`. -/
theorem connes_log_ftc_tail (G : 𝓢(ℝ, ℂ)) :
    (∫ u in Ioi (1 : ℝ), (deriv ((G : 𝓢(ℝ, ℂ)) : ℝ → ℂ) u * ((Real.log u : ℝ) : ℂ)
      + (G : ℝ → ℂ) u * ((u⁻¹ : ℝ) : ℂ))) = 0 := by
  have hcont : ContinuousWithinAt
      (fun u : ℝ => (G : ℝ → ℂ) u * ((Real.log u : ℝ) : ℂ)) (Ici (1 : ℝ)) 1 := by
    refine ContinuousAt.continuousWithinAt ?_
    refine (G.continuous.continuousAt).mul ?_
    exact (Complex.continuous_ofReal.continuousAt).comp
      (Real.continuousAt_log (by norm_num))
  have hderiv : ∀ x ∈ Ioi (1 : ℝ),
      HasDerivAt (fun u : ℝ => (G : ℝ → ℂ) u * ((Real.log u : ℝ) : ℂ))
        (deriv ((G : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x * ((Real.log x : ℝ) : ℂ)
          + (G : ℝ → ℂ) x * ((x⁻¹ : ℝ) : ℂ)) x := by
    intro x hx
    have hx0 : x ≠ 0 := by
      have : (1 : ℝ) < x := hx
      linarith
    exact connes_hasDerivAt_mul_log G hx0
  have h := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv
    (connes_tail_integrand_integrable G) (connes_schwartz_mul_log_atTop G)
  rw [h]
  simp

end

end GaloisForLFunctions.RHTower
