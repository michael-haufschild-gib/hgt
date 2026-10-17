import GaloisForLFunctions.BiScaleUncertainty.CompactSourceNodalVariance
import GaloisForLFunctions.BiScaleUncertainty.CompactSourceGraphCoercivity
import GaloisForLFunctions.BiScaleUncertainty.RoughModulusGraphDecomposition

/-!
# Quantitative nodal mass coercivity and strict modulus contraction

The actual compact-source mixed graph loses at least 4PN/sinh(2B) under
modulus. Equality of graph energies holds exactly for sourcewise one-sign
states; disconnected support, arbitrary nonnegative atom weights and the zero
source are covered without extra admission premises.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal CompactlySupported

namespace GaloisForLFunctions.BiScaleUncertainty.PathCongestion
open SobolevShear
set_option autoImplicit false

/-- Exact variance loss for the constructed rough modulus state. -/
theorem compact_modulus_variance_difference (ψ : C_c(ℝ, ℝ)) (q : Velocity) (c : ℝ) :
    weightedVariance ψ (logarithmicState q c) -
      weightedVariance ψ (logarithmicState (modulusVelocity q c) |c|) =
      4 * sourcePositiveMass ψ (logarithmicState q c) *
        sourceNegativeMass ψ (logarithmicState q c) := by
  have he : logarithmicState (modulusVelocity q c) |c| = sourceAbs (logarithmicState q c) := by
    ext x
    exact logPrimitive_modulusVelocity q c x
  rw [he, weightedVariance_modulus_difference]

theorem nodalLagGap_le_arch_weighted (ψ : C_c(ℝ, ℝ)) (f : C(ℝ, ℝ))
    (e : Edge) (he : 0 < e.1) :
    nodalLagGap ψ f e ≤ coercivityScale ψ * (archLevySinhWeight e.1 * nodalLagGap ψ f e) := by
  by_cases hp : sourcePair ψ e = 0
  · simp [nodalLagGap, hp]
  · rcases sourcePair_endpoints ψ e hp with ⟨h₁,h₂⟩
    have hb : e.1 ≤ 2*multiplierSourceRadius ψ := by linarith [h₁.1,h₂.2]
    have hs := Real.sinh_le_sinh.mpr hb
    have hx := Real.one_le_exp (show 0 ≤ e.1/2 by linarith)
    have hc := (coercivityScale_pos ψ).le
    have hw : 1 ≤ coercivityScale ψ * archLevySinhWeight e.1 := by
      unfold archLevySinhWeight
      rw [← mul_div_assoc, le_div_iff₀ (Real.sinh_pos_iff.mpr he), one_mul]
      change Real.sinh e.1 ≤ coercivityScale ψ * Real.exp (e.1/2)
      change Real.sinh e.1 ≤ coercivityScale ψ at hs
      nlinarith
    have hn := nodalLagGap_nonneg ψ f e
    nlinarith [mul_nonneg (sub_nonneg.mpr hw) hn]

theorem compactDiffuse_nodal_density (ψ : C_c(ℝ, ℝ)) (weights : ℕ → ℝ≥0)
    (q : Velocity) (c : ℝ) (e : Edge) (he : 0 < e.1) :
    ENNReal.ofReal (archLevySinhWeight e.1 * nodalLagGap ψ (logarithmicState q c) e) =
      (compactMixture ψ weights).diffuseWeight e * nodalCost q c e := by
  change ENNReal.ofReal (_ * (_ * _)) =
    ENNReal.ofReal (archLevySinhWeight e.1 * sourcePair ψ e) * ENNReal.ofReal _
  rw [← ENNReal.ofReal_mul (mul_nonneg (archLevySinhWeight_nonneg he.le)
    (sourcePair_nonneg ψ e)), mul_assoc]
  rfl

/-- The lower bound retains the full arithmetic part of the actual mixed graph. -/
theorem compact_lobe_product_le_nodalEnergy_extended (ψ : C_c(ℝ, ℝ)) (weights : ℕ → ℝ≥0)
    (q : Velocity) (c : ℝ) :
    ENNReal.ofReal (4 * sourcePositiveMass ψ (logarithmicState q c) *
      sourceNegativeMass ψ (logarithmicState q c)) ≤
      ENNReal.ofReal (coercivityScale ψ) * nodalEnergy (compactMixture ψ weights) q c := by
  have hae : ∀ᵐ e : Edge ∂(volume.restrict (Ioi (0 : ℝ))).prod volume, 0 < e.1 := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_lt measurable_const measurable_fst)).mpr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
    exact Eventually.of_forall (fun _ => hh)
  calc
    _ = ∫⁻ e, ENNReal.ofReal (nodalLagGap ψ (logarithmicState q c) e)
        ∂(volume.restrict (Ioi (0 : ℝ))).prod volume :=
      (lintegral_positive_nodalLagGap ψ (logarithmicState q c)).symm
    _ ≤ ∫⁻ e, ENNReal.ofReal (coercivityScale ψ) *
        ((compactMixture ψ weights).diffuseWeight e * nodalCost q c e)
        ∂(volume.restrict (Ioi (0 : ℝ))).prod volume := by
      apply lintegral_mono_ae
      filter_upwards [hae] with e he
      have h := ENNReal.ofReal_le_ofReal
        (nodalLagGap_le_arch_weighted ψ (logarithmicState q c) e he)
      rw [ENNReal.ofReal_mul (coercivityScale_pos ψ).le,
        compactDiffuse_nodal_density ψ weights q c e he] at h
      exact h
    _ = ENNReal.ofReal (coercivityScale ψ) *
        ∫⁻ e, nodalCost q c e ∂diffuseMeasure (compactMixture ψ weights) := by
      have hm : Measurable (fun e : Edge =>
          (compactMixture ψ weights).diffuseWeight e * nodalCost q c e) :=
        (measurable_compactDiffuse ψ weights).mul (measurable_nodalCost q c)
      rw [lintegral_const_mul _ hm, diffuseMeasure,
        lintegral_withDensity_eq_lintegral_mul _ (measurable_compactDiffuse ψ weights)
          (measurable_nodalCost q c)]
      rfl
    _ ≤ _ := by
      have hd : (∫⁻ e, nodalCost q c e ∂diffuseMeasure (compactMixture ψ weights)) ≤
          nodalEnergy (compactMixture ψ weights) q c := by
        rw [nodalEnergy, edgeMeasure, lintegral_add_measure]
        exact le_add_of_nonneg_right zero_le
      simpa only [mul_comm] using mul_le_mul_left hd (ENNReal.ofReal (coercivityScale ψ))

theorem compact_lobe_product_le_nodalEnergy (ψ : C_c(ℝ, ℝ)) (weights : ℕ → ℝ≥0)
    (q : Velocity) (c : ℝ) :
    4 * sourcePositiveMass ψ (logarithmicState q c) *
      sourceNegativeMass ψ (logarithmicState q c) ≤
      coercivityScale ψ * (nodalEnergy (compactMixture ψ weights) q c).toReal := by
  have h := compact_lobe_product_le_nodalEnergy_extended ψ weights q c
  rw [← ENNReal.ofReal_toReal (compact_nodalEnergy_ne_top ψ weights q c),
    ← ENNReal.ofReal_mul (coercivityScale_pos ψ).le] at h
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (coercivityScale_pos ψ).le ENNReal.toReal_nonneg)).mp h

/-- Actual modulus energy loss controls the positive/negative source-mass product. -/
theorem compact_lobe_product_le_modulus_loss (ψ : C_c(ℝ, ℝ)) (weights : ℕ → ℝ≥0)
    (q : Velocity) (c : ℝ) :
    4 * sourcePositiveMass ψ (logarithmicState q c) *
      sourceNegativeMass ψ (logarithmicState q c) ≤
      coercivityScale ψ * ((jumpEnergy (compactMixture ψ weights) q).toReal -
        (jumpEnergy (compactMixture ψ weights) (modulusVelocity q c)).toReal) := by
  rw [compact_jumpEnergy_modulus_difference]
  exact compact_lobe_product_le_nodalEnergy ψ weights q c

private theorem weighted_nodal_eq_zero_of_one_sign (ψ : C_c(ℝ, ℝ)) (q : Velocity) (c : ℝ)
    (hf : (∀ u, ψ u ≠ 0 → 0 ≤ logarithmicState q c u) ∨
      (∀ u, ψ u ≠ 0 → logarithmicState q c u ≤ 0)) (e : Edge) (a : ℝ) :
    ENNReal.ofReal (a*sourcePair ψ e) * nodalCost q c e = 0 := by
  by_cases hu : ψ e.2 = 0
  · simp [sourcePair, hu]
  by_cases hv : ψ (e.2+e.1) = 0
  · simp [sourcePair, hv]
  have hz : nodalCost q c e = 0 := by
    rcases hf with hf | hf
    · have h₁ := hf e.2 hu
      have h₂ := hf (e.2+e.1) hv
      change 0 ≤ c+logPrimitive q e.2 at h₁
      change 0 ≤ c+logPrimitive q (e.2+e.1) at h₂
      simp only [nodalCost, max_eq_right (neg_nonpos.mpr h₁),
        max_eq_right (neg_nonpos.mpr h₂), mul_zero, zero_mul, add_zero, ENNReal.ofReal_zero]
    · have h₁ := hf e.2 hu
      have h₂ := hf (e.2+e.1) hv
      change c+logPrimitive q e.2 ≤ 0 at h₁
      change c+logPrimitive q (e.2+e.1) ≤ 0 at h₂
      simp [nodalCost, max_eq_right h₁, max_eq_right h₂]
  rw [hz, mul_zero]

/-- A positive diffuse kernel detects opposite signs across all source components. -/
theorem compact_nodalEnergy_eq_zero_iff (ψ : C_c(ℝ, ℝ)) (weights : ℕ → ℝ≥0)
    (q : Velocity) (c : ℝ) :
    nodalEnergy (compactMixture ψ weights) q c = 0 ↔
      (∀ u, ψ u ≠ 0 → 0 ≤ logarithmicState q c u) ∨
      (∀ u, ψ u ≠ 0 → logarithmicState q c u ≤ 0) := by
  constructor
  · intro hn
    have h := compact_lobe_product_le_nodalEnergy ψ weights q c
    rw [hn, ENNReal.toReal_zero, mul_zero] at h
    have hp := sourcePositiveMass_nonneg ψ (logarithmicState q c)
    have hm := sourceNegativeMass_nonneg ψ (logarithmicState q c)
    have hz : sourcePositiveMass ψ (logarithmicState q c) *
        sourceNegativeMass ψ (logarithmicState q c) = 0 := by nlinarith
    rcases mul_eq_zero.mp hz with h₁ | h₂
    · exact Or.inr ((sourcePositiveMass_eq_zero_iff ψ _).mp h₁)
    · exact Or.inl ((sourceNegativeMass_eq_zero_iff ψ _).mp h₂)
  · intro hf
    have hd : (∫⁻ e, nodalCost q c e ∂diffuseMeasure (compactMixture ψ weights)) = 0 := by
      rw [diffuseMeasure, lintegral_withDensity_eq_lintegral_mul _
        (measurable_compactDiffuse ψ weights) (measurable_nodalCost q c)]
      have hz (e : Edge) : (compactMixture ψ weights).diffuseWeight e * nodalCost q c e = 0 :=
        weighted_nodal_eq_zero_of_one_sign ψ q c hf e (archLevySinhWeight e.1)
      simp only [Pi.mul_apply, hz, lintegral_zero]
    have hl (n : ℕ) : (∫⁻ e, nodalCost q c e ∂lineMeasure (compactMixture ψ weights) n) = 0 := by
      rw [lineMeasure, lintegral_map
        (g := fun u : ℝ => ((compactMixture ψ weights).lag n,u))
        (measurable_nodalCost q c) (measurable_const.prodMk measurable_id)]
      have hm : Measurable (fun u : ℝ => nodalCost q c ((compactMixture ψ weights).lag n,u)) :=
        (measurable_nodalCost q c).comp (measurable_const.prodMk measurable_id)
      rw [lintegral_withDensity_eq_lintegral_mul _ (measurable_compactLine ψ weights n) hm]
      have hz (u : ℝ) : (compactMixture ψ weights).lineWeight n u *
          nodalCost q c ((compactMixture ψ weights).lag n,u) = 0 :=
        weighted_nodal_eq_zero_of_one_sign ψ q c hf _ (weights n)
      simp only [Pi.mul_apply, hz, lintegral_zero]
    rw [nodalEnergy, edgeMeasure, lintegral_add_measure, lintegral_sum_measure]
    simp only [hd, hl, tsum_zero, add_zero]

theorem compact_modulus_energy_eq_iff (ψ : C_c(ℝ, ℝ)) (weights : ℕ → ℝ≥0)
    (q : Velocity) (c : ℝ) :
    jumpEnergy (compactMixture ψ weights) (modulusVelocity q c) =
      jumpEnergy (compactMixture ψ weights) q ↔
      (∀ u, ψ u ≠ 0 → 0 ≤ logarithmicState q c u) ∨
      (∀ u, ψ u ≠ 0 → logarithmicState q c u ≤ 0) := by
  rw [← compact_nodalEnergy_eq_zero_iff]
  constructor
  · intro h
    have he : jumpEnergy (compactMixture ψ weights) (modulusVelocity q c) +
        nodalEnergy (compactMixture ψ weights) q c =
        jumpEnergy (compactMixture ψ weights) (modulusVelocity q c) + 0 := by
      rw [add_zero, ← jumpEnergy_modulus_decomposition, ← h]
    exact (ENNReal.add_right_inj (compact_jumpEnergy_ne_top ψ weights (modulusVelocity q c))).mp he
  · intro h
    rw [jumpEnergy_modulus_decomposition _ q c, h, add_zero]

/-- Strict contraction occurs precisely when both signs occur at nonzero source points. -/
theorem compact_modulus_energy_lt_iff (ψ : C_c(ℝ, ℝ)) (weights : ℕ → ℝ≥0)
    (q : Velocity) (c : ℝ) :
    jumpEnergy (compactMixture ψ weights) (modulusVelocity q c) <
      jumpEnergy (compactMixture ψ weights) q ↔
      (∃ u, ψ u ≠ 0 ∧ logarithmicState q c u < 0) ∧
      (∃ v, ψ v ≠ 0 ∧ 0 < logarithmicState q c v) := by
  rw [lt_iff_le_and_ne]
  simp only [jumpEnergy_modulus_le, true_and, ne_eq, compact_modulus_energy_eq_iff]
  push Not
  rfl

end GaloisForLFunctions.BiScaleUncertainty.PathCongestion
