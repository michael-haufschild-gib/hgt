import GaloisForLFunctions.BiScaleUncertainty.CompactSourcePairVariance

/-!
# Variance coercivity and nullspace of the compact-source mixed graph

The diffuse kernel has a positive lower bound on every contributing source
pair. It therefore controls the full weighted variance, even across different
components of source support. Arithmetic edges preserve this coercivity.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal CompactlySupported

namespace GaloisForLFunctions.BiScaleUncertainty.PathCongestion
open SobolevShear
set_option autoImplicit false

def logarithmicState (q : Velocity) (c : ℝ) : C(ℝ, ℝ) :=
  ⟨fun x => c+logPrimitive q x, continuous_const.add (continuous_logPrimitive q)⟩

def coercivityScale (ψ : C_c(ℝ, ℝ)) : ℝ := Real.sinh (2*multiplierSourceRadius ψ)

theorem coercivityScale_pos (ψ : C_c(ℝ, ℝ)) : 0 < coercivityScale ψ :=
  Real.sinh_pos_iff.mpr (mul_pos (by norm_num) (multiplierSourceRadius_pos ψ))

theorem lagGap_logarithmicState (ψ : C_c(ℝ, ℝ)) (q : Velocity) (c : ℝ) (e : Edge) :
    lagGap ψ (logarithmicState q c) e =
      sourcePair ψ e * (logPrimitive q (e.2+e.1)-logPrimitive q e.2)^2 := by
  dsimp [lagGap, pairGap, logarithmicState, sourcePair]
  ring

theorem lintegral_positive_lagGap (ψ : C_c(ℝ, ℝ)) (f : C(ℝ, ℝ)) :
    (∫⁻ e, ENNReal.ofReal (lagGap ψ f e)
      ∂(volume.restrict (Ioi (0 : ℝ))).prod volume) = ENNReal.ofReal (weightedVariance ψ f) := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    ((integrable_lagGap ψ f).mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl))
    (Eventually.of_forall (lagGap_nonneg ψ f)), integral_positive_lagGap]

/-- Uniform comparison on actual source pairs, with zero source pairs handled exactly. -/
theorem lagGap_le_arch_weighted (ψ : C_c(ℝ, ℝ)) (f : C(ℝ, ℝ)) (e : Edge) (he : 0 < e.1) :
    lagGap ψ f e ≤ coercivityScale ψ * (archLevySinhWeight e.1 * lagGap ψ f e) := by
  by_cases hp : sourcePair ψ e = 0
  · have hz : lagGap ψ f e = 0 := by
      change sourcePair ψ e * (f (e.2+e.1)-f e.2)^2 = 0
      rw [hp, zero_mul]
    simp [hz]
  · rcases sourcePair_endpoints ψ e hp with ⟨h₁,h₂⟩
    have hb : e.1 ≤ 2*multiplierSourceRadius ψ := by linarith [h₁.1,h₂.2]
    have hs := (Real.sinh_le_sinh.mpr hb)
    have hx := Real.one_le_exp (show 0 ≤ e.1/2 by linarith)
    have hc := (coercivityScale_pos ψ).le
    have hw : 1 ≤ coercivityScale ψ * archLevySinhWeight e.1 := by
      unfold archLevySinhWeight
      rw [← mul_div_assoc, le_div_iff₀ (Real.sinh_pos_iff.mpr he), one_mul]
      change Real.sinh e.1 ≤ coercivityScale ψ * Real.exp (e.1/2)
      change Real.sinh e.1 ≤ coercivityScale ψ at hs
      nlinarith
    have hn := lagGap_nonneg ψ f e
    nlinarith [mul_nonneg (sub_nonneg.mpr hw) hn]

theorem compactDiffuse_jump_density (ψ : C_c(ℝ, ℝ)) (weights : ℕ → ℝ≥0)
    (q : Velocity) (c : ℝ) (e : Edge) (he : 0 < e.1) :
    ENNReal.ofReal (archLevySinhWeight e.1 * lagGap ψ (logarithmicState q c) e) =
      (compactMixture ψ weights).diffuseWeight e * jump q e := by
  rw [lagGap_logarithmicState]
  change ENNReal.ofReal (_ * (_ * _)) =
    ENNReal.ofReal (archLevySinhWeight e.1 * sourcePair ψ e) *
      ENNReal.ofReal ((logPrimitive q (e.2+e.1)-logPrimitive q e.2)^2)
  rw [← ENNReal.ofReal_mul (mul_nonneg (archLevySinhWeight_nonneg he.le)
    (sourcePair_nonneg ψ e)), mul_assoc]

/-- Exact weighted variance is bounded by the actual diffuse plus arithmetic graph. -/
theorem compact_variance_le_jumpEnergy_extended (ψ : C_c(ℝ, ℝ)) (weights : ℕ → ℝ≥0)
    (q : Velocity) (c : ℝ) :
    ENNReal.ofReal (weightedVariance ψ (logarithmicState q c)) ≤
      ENNReal.ofReal (coercivityScale ψ) * jumpEnergy (compactMixture ψ weights) q := by
  have hae : ∀ᵐ e : Edge ∂(volume.restrict (Ioi (0 : ℝ))).prod volume, 0 < e.1 := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_lt measurable_const measurable_fst)).mpr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
    exact Eventually.of_forall (fun _ => hh)
  calc
    _ = ∫⁻ e, ENNReal.ofReal (lagGap ψ (logarithmicState q c) e)
        ∂(volume.restrict (Ioi (0 : ℝ))).prod volume :=
      (lintegral_positive_lagGap ψ (logarithmicState q c)).symm
    _ ≤ ∫⁻ e, ENNReal.ofReal (coercivityScale ψ) *
        ((compactMixture ψ weights).diffuseWeight e * jump q e)
        ∂(volume.restrict (Ioi (0 : ℝ))).prod volume := by
      apply lintegral_mono_ae
      filter_upwards [hae] with e he
      have h := ENNReal.ofReal_le_ofReal (lagGap_le_arch_weighted ψ (logarithmicState q c) e he)
      rw [ENNReal.ofReal_mul (coercivityScale_pos ψ).le,
        compactDiffuse_jump_density ψ weights q c e he] at h
      exact h
    _ = ENNReal.ofReal (coercivityScale ψ) *
        ∫⁻ e, jump q e ∂diffuseMeasure (compactMixture ψ weights) := by
      have hm : Measurable (fun e : Edge => (compactMixture ψ weights).diffuseWeight e * jump q e) :=
        (measurable_compactDiffuse ψ weights).mul (measurable_jump q)
      rw [lintegral_const_mul _ hm,
        diffuseMeasure, lintegral_withDensity_eq_lintegral_mul _
          (measurable_compactDiffuse ψ weights) (measurable_jump q)]
      rfl
    _ ≤ _ := by
      have hd : (∫⁻ e, jump q e ∂diffuseMeasure (compactMixture ψ weights)) ≤
          jumpEnergy (compactMixture ψ weights) q := by
        rw [jumpEnergy, edgeMeasure, lintegral_add_measure]
        exact le_add_of_nonneg_right zero_le
      simpa only [mul_comm] using mul_le_mul_left hd (ENNReal.ofReal (coercivityScale ψ))

/-- The finite real-valued coercivity law requires no analytic admission premise. -/
theorem compact_variance_le_jumpEnergy (ψ : C_c(ℝ, ℝ)) (weights : ℕ → ℝ≥0)
    (q : Velocity) (c : ℝ) :
    weightedVariance ψ (logarithmicState q c) ≤
      coercivityScale ψ * (jumpEnergy (compactMixture ψ weights) q).toReal := by
  have h := compact_variance_le_jumpEnergy_extended ψ weights q c
  rw [← ENNReal.ofReal_toReal (compact_jumpEnergy_ne_top ψ weights q),
    ← ENNReal.ofReal_mul (coercivityScale_pos ψ).le] at h
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (coercivityScale_pos ψ).le ENNReal.toReal_nonneg)).mp h

/-- Coupling of graph coercivity to the actual local additive Dirichlet energy. -/
theorem compact_variance_le_dirichlet (ψ : C_c(ℝ, ℝ)) (weights : ℕ → ℝ≥0)
    (q : Velocity) (c : ℝ) :
    ENNReal.ofReal (weightedVariance ψ (logarithmicState q c)) ≤
      ENNReal.ofReal (coercivityScale ψ) *
        (resistanceMass ψ weights * sourceDirichletMass ψ q) := by
  apply (compact_variance_le_jumpEnergy_extended ψ weights q c).trans
  have hj : jumpEnergy (compactMixture ψ weights) q ≤
      congestionEnergy (compactMixture ψ weights) q := by
    rw [congestionEnergy_eq_jump_add_slack]
    exact le_add_of_nonneg_right zero_le
  have h := hj.trans (compact_congestionEnergy_le ψ weights q)
  simpa only [mul_comm] using mul_le_mul_left h (ENNReal.ofReal (coercivityScale ψ))

private theorem weighted_jump_eq_zero_of_constant (ψ : C_c(ℝ, ℝ)) (q : Velocity) (c : ℝ)
    (hf : ∀ u v : ℝ, ψ u ≠ 0 → ψ v ≠ 0 → logarithmicState q c u = logarithmicState q c v)
    (e : Edge) (a : ℝ) : ENNReal.ofReal (a*sourcePair ψ e)*jump q e = 0 := by
  by_cases hu : ψ e.2 = 0
  · simp [sourcePair, hu]
  by_cases hv : ψ (e.2+e.1) = 0
  · simp [sourcePair, hv]
  have h := hf e.2 (e.2+e.1) hu hv
  change c+logPrimitive q e.2 = c+logPrimitive q (e.2+e.1) at h
  have hz : logPrimitive q (e.2+e.1)-logPrimitive q e.2 = 0 := by linarith
  simp [jump, hz]

/-- Diffuse jumps join every nonzero source region, including disconnected components. -/
theorem compact_jumpEnergy_eq_zero_iff (ψ : C_c(ℝ, ℝ)) (weights : ℕ → ℝ≥0)
    (q : Velocity) (c : ℝ) :
    jumpEnergy (compactMixture ψ weights) q = 0 ↔
      ∀ u v : ℝ, ψ u ≠ 0 → ψ v ≠ 0 → logarithmicState q c u = logarithmicState q c v := by
  constructor
  · intro hj
    have hv := compact_variance_le_jumpEnergy ψ weights q c
    rw [hj, ENNReal.toReal_zero, mul_zero] at hv
    exact (weightedVariance_eq_zero_iff ψ (logarithmicState q c)).mp
      (le_antisymm hv (weightedVariance_nonneg ψ (logarithmicState q c)))
  · intro hf
    rw [jumpEnergy_eq_diffuse_add_lines]
    have hd : (∫⁻ e, jump q e ∂diffuseMeasure (compactMixture ψ weights)) = 0 := by
      rw [diffuseMeasure, lintegral_withDensity_eq_lintegral_mul _
        (measurable_compactDiffuse ψ weights) (measurable_jump q)]
      have hz (e : Edge) : (compactMixture ψ weights).diffuseWeight e * jump q e = 0 :=
        weighted_jump_eq_zero_of_constant ψ q c hf e (archLevySinhWeight e.1)
      simp only [Pi.mul_apply, hz, lintegral_zero]
    have hl (n : ℕ) : (∫⁻ u, jump q ((compactMixture ψ weights).lag n,u)
        ∂volume.withDensity ((compactMixture ψ weights).lineWeight n)) = 0 := by
      have hm : Measurable (fun u : ℝ => jump q ((compactMixture ψ weights).lag n,u)) :=
        (measurable_jump q).comp (measurable_const.prodMk measurable_id)
      rw [lintegral_withDensity_eq_lintegral_mul _ (measurable_compactLine ψ weights n) hm]
      have hz (u : ℝ) : (compactMixture ψ weights).lineWeight n u *
          jump q ((compactMixture ψ weights).lag n,u) = 0 :=
        weighted_jump_eq_zero_of_constant ψ q c hf _ (weights n)
      simp only [Pi.mul_apply, hz, lintegral_zero]
    simp only [hd, hl, tsum_zero, add_zero]

end GaloisForLFunctions.BiScaleUncertainty.PathCongestion
