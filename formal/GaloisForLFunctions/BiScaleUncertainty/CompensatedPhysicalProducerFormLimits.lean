import GaloisForLFunctions.BiScaleUncertainty.CompensatedPhysicalProducerConvergence

/-!
# Compact source and jump energies of the explicit approximants

The physical norm bound gives integrable majorants for the actual source and
edge measures. Dominated convergence therefore applies to the energies themselves.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology CompactlySupported ENNReal NNReal

namespace GaloisForLFunctions.BiScaleUncertainty.SobolevShear
set_option autoImplicit false

theorem smoothedLogarithmicState_tendsto (q : Velocity) (x : ℝ) :
    Tendsto (fun n => smoothedLogarithmicState n q x) atTop (𝓝 (logPrimitive q x)) :=
  (smoothedLogarithmicState_tendstoUniformlyOn q x).tendsto_at (mem_Iic.mpr (le_refl x))

theorem norm_sq_smoothedCompensatedVelocity_le_two (n : ℕ) (q : Velocity) :
    ‖smoothedCompensatedVelocity n q‖ ^ 2 ≤ 2 * ‖q‖ ^ 2 := by
  have he : Real.exp (-producerScale n) ≤ 1 := by
    simpa only [Real.exp_zero] using
      Real.exp_le_exp.mpr (neg_nonpos.mpr (producerScale_pos n).le)
  calc
    _ ≤ (1 + Real.exp (-producerScale n)) * ‖q‖ ^ 2 :=
      norm_sq_smoothedCompensatedVelocity_le n q
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith only [he]) (sq_nonneg _)

end GaloisForLFunctions.BiScaleUncertainty.SobolevShear

namespace GaloisForLFunctions.BiScaleUncertainty.PathCongestion
open SobolevShear
set_option autoImplicit false

/-- Source masses converge for every fixed additive constant in the logarithmic state. -/
theorem sourceMass_smoothedCompensatedVelocity_tendsto
    (ψ : C_c(ℝ, ℝ)) (q : Velocity) (c : ℝ) :
    Tendsto (fun n => sourceMass ψ (smoothedCompensatedVelocity n q) c) atTop
      (𝓝 (sourceMass ψ q c)) := by
  let b : ℝ → ℝ := fun x => ψ x ^ 2 * (2 * c ^ 2 + 4 * Real.exp x * ‖q‖ ^ 2)
  have hb : Integrable b := by
    have hc : Continuous b := by dsimp [b]; fun_prop
    apply hc.integrable_of_hasCompactSupport
    apply HasCompactSupport.of_support_subset_isCompact ψ.hasCompactSupport.isCompact
    intro x hx
    apply subset_closure
    apply Function.mem_support.mpr
    intro hz
    apply (Function.mem_support.mp hx)
    change ψ x ^ 2 * (2 * c ^ 2 + 4 * Real.exp x * ‖q‖ ^ 2) = 0
    rw [hz, sq, zero_mul, zero_mul]
  have hpos (x : ℝ) : 0 ≤ b x := by dsimp [b]; positivity
  apply tendsto_lintegral_of_dominated_convergence (fun x => ENNReal.ofReal (b x))
  · intro n
    exact ((ψ.continuous.pow 2).mul
      ((continuous_const.add (continuous_logPrimitive (smoothedCompensatedVelocity n q))).pow 2)).measurable.ennreal_ofReal
  · intro n
    exact Eventually.of_forall fun x => by
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg (ψ x))
      have ht := logPrimitive_sq_le_exp_mul_norm_sq (smoothedCompensatedVelocity n q) x
      have he := mul_le_mul_of_nonneg_left (norm_sq_smoothedCompensatedVelocity_le_two n q)
        (Real.exp_pos x).le
      nlinarith only [ht, he, sq_nonneg (c - logPrimitive (smoothedCompensatedVelocity n q) x)]
  · rw [← ofReal_integral_eq_lintegral_ofReal hb (Eventually.of_forall hpos)]
    exact ENNReal.ofReal_ne_top
  · exact Eventually.of_forall fun x =>
      ENNReal.tendsto_ofReal (((tendsto_const_nhds.add
        (smoothedLogarithmicState_tendsto q x)).pow 2).const_mul (ψ x ^ 2))

/-- Resistance, rather than the potentially infinite unweighted edge mass, controls each jump. -/
theorem jump_le_resistance_mul_norm_sq (q : Velocity) (e : Edge) :
    jump q e ≤ ENNReal.ofReal (resistance e) * ENNReal.ofReal (‖q‖ ^ 2) := by
  have he : energy q (Real.exp (lower e)) (Real.exp (upper e)) ≤ ‖q‖ ^ 2 := by
    rw [energy, intervalIntegral.integral_of_le (Real.exp_le_exp.mpr (lower_le_upper e)),
      norm_sq_velocity]
    exact setIntegral_le_integral (integrable_velocity_sq q)
      (Eventually.of_forall fun t => sq_nonneg (q t))
  calc
    _ ≤ budget q e := jump_le_budget q e
    _ ≤ _ := by
      rw [budget_eq_physical]
      exact mul_le_mul_right (ENNReal.ofReal_le_ofReal he) _

/-- The actual diffuse-plus-arithmetic jump energies converge. -/
theorem compact_jumpEnergy_smoothedCompensatedVelocity_tendsto
    (ψ : C_c(ℝ, ℝ)) (weights : ℕ → ℝ≥0) (q : Velocity) :
    Tendsto (fun n => jumpEnergy (compactMixture ψ weights) (smoothedCompensatedVelocity n q))
      atTop (𝓝 (jumpEnergy (compactMixture ψ weights) q)) := by
  apply tendsto_lintegral_of_dominated_convergence
    (fun e => ENNReal.ofReal (2 * ‖q‖ ^ 2) * ENNReal.ofReal (resistance e))
  · exact fun n => measurable_jump _
  · intro n
    exact Eventually.of_forall fun e => by
      calc
        _ ≤ ENNReal.ofReal (resistance e) *
            ENNReal.ofReal (‖smoothedCompensatedVelocity n q‖ ^ 2) :=
          jump_le_resistance_mul_norm_sq _ e
        _ ≤ ENNReal.ofReal (resistance e) * ENNReal.ofReal (2 * ‖q‖ ^ 2) :=
          mul_le_mul_right (ENNReal.ofReal_le_ofReal
            (norm_sq_smoothedCompensatedVelocity_le_two n q)) _
        _ = _ := mul_comm _ _
  · rw [lintegral_const_mul _ measurable_resistance.ennreal_ofReal]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (resistanceMass_ne_top ψ weights)
  · exact Eventually.of_forall fun e =>
      ENNReal.tendsto_ofReal (((smoothedLogarithmicState_tendsto q (e.2 + e.1)).sub
        (smoothedLogarithmicState_tendsto q e.2)).pow 2)

/-- Both parts of every constructed compact source form converge along the same sequence. -/
theorem compact_formEnergy_smoothedCompensatedVelocity_tendsto
    (ψ : C_c(ℝ, ℝ)) (weights : ℕ → ℝ≥0) (q : Velocity) (c : ℝ) :
    Tendsto (fun n => sourceMass ψ (smoothedCompensatedVelocity n q) c +
      jumpEnergy (compactMixture ψ weights) (smoothedCompensatedVelocity n q))
      atTop (𝓝 (sourceMass ψ q c + jumpEnergy (compactMixture ψ weights) q)) :=
  (sourceMass_smoothedCompensatedVelocity_tendsto ψ q c).add
    (compact_jumpEnergy_smoothedCompensatedVelocity_tendsto ψ weights q)

end GaloisForLFunctions.BiScaleUncertainty.PathCongestion
