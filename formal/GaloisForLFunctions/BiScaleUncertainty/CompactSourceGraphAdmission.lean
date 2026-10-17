import GaloisForLFunctions.BiScaleUncertainty.CompactSourceResistanceMass

/-!
# Finite mixed graph energies for every physical L2 velocity

Compact source support gives bounded compactly supported path congestion.
The coefficient is the constructed finite resistance mass. Thus the actual
diffuse and arithmetic jump graph admits every logarithmic Sobolev primitive,
without a separate energy-integrability or atom-summability premise.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal CompactlySupported

namespace GaloisForLFunctions.BiScaleUncertainty.PathCongestion
open SobolevShear
set_option autoImplicit false

theorem sourcePair_or_path_zero (ψ : C_c(ℝ, ℝ)) (e : Edge) (y : ℝ)
    (hy : y ∉ Icc (-multiplierSourceRadius ψ) (multiplierSourceRadius ψ)) :
    sourcePair ψ e = 0 ∨ pathKernel e y = 0 := by
  by_cases hp : sourcePair ψ e = 0
  · exact Or.inl hp
  · right
    rcases sourcePair_endpoints ψ e hp with ⟨h₁,h₂⟩
    have hout : y ∉ Ioc (lower e) (upper e) := by
      intro h
      apply hy
      exact ⟨(le_min h₁.1 h₂.1).trans h.1.le, h.2.trans (max_le h₁.2 h₂.2)⟩
    simp [pathKernel, hout]

theorem compact_congestion_eq_zero (ψ : C_c(ℝ, ℝ)) (λ : ℕ → ℝ≥0) (y : ℝ)
    (hy : y ∉ Icc (-multiplierSourceRadius ψ) (multiplierSourceRadius ψ)) :
    congestion (compactMixture ψ λ) y = 0 := by
  rw [congestion_eq_diffuse_add_lines]
  have hd : (∫⁻ e, pathKernel e y ∂diffuseMeasure (compactMixture ψ λ)) = 0 := by
    rw [diffuseMeasure, lintegral_withDensity_eq_lintegral_mul _
      (measurable_compactDiffuse ψ λ) (measurable_pathKernel_left y)]
    have hz : ∀ e, (compactMixture ψ λ).diffuseWeight e * pathKernel e y = 0 := by
      intro e
      rcases sourcePair_or_path_zero ψ e y hy with hp | hp
      · simp [compactMixture, hp]
      · simp [hp]
    simp only [Pi.mul_apply, hz, lintegral_zero]
  have hl (n : ℕ) : (∫⁻ u, pathKernel ((compactMixture ψ λ).lag n,u) y
      ∂volume.withDensity ((compactMixture ψ λ).lineWeight n)) = 0 := by
    rw [lintegral_withDensity_eq_lintegral_mul _ (measurable_compactLine ψ λ n)
      ((measurable_pathKernel_left y).comp (measurable_const.prodMk measurable_id))]
    have hz : ∀ u, (compactMixture ψ λ).lineWeight n u *
        pathKernel ((compactMixture ψ λ).lag n,u) y = 0 := by
      intro u
      rcases sourcePair_or_path_zero ψ ((compactMixture ψ λ).lag n,u) y hy with hp | hp
      · simp [compactMixture] at hp ⊢
        rw [hp]
        simp
      · simp [hp]
    simp only [Pi.mul_apply, hz, lintegral_zero]
  simp only [hd, hl, tsum_zero, add_zero]

theorem compact_congestion_le_mass (ψ : C_c(ℝ, ℝ)) (λ : ℕ → ℝ≥0) (y : ℝ) :
    congestion (compactMixture ψ λ) y ≤ resistanceMass ψ λ := by
  apply lintegral_mono
  intro e
  by_cases hy : y ∈ Ioc (lower e) (upper e)
  · simp [pathKernel, hy]
  · simp [pathKernel, hy]

/-- A bounded compactly supported majorant constructed from the actual source. -/
theorem compact_congestion_le_indicator (ψ : C_c(ℝ, ℝ)) (λ : ℕ → ℝ≥0) (y : ℝ) :
    congestion (compactMixture ψ λ) y ≤
      (Icc (-multiplierSourceRadius ψ) (multiplierSourceRadius ψ)).indicator
        (fun _ => resistanceMass ψ λ) y := by
  by_cases hy : y ∈ Icc (-multiplierSourceRadius ψ) (multiplierSourceRadius ψ)
  · simpa [hy] using compact_congestion_le_mass ψ λ y
  · simp [hy, compact_congestion_eq_zero ψ λ y hy]

def sourceDirichletMass (ψ : C_c(ℝ, ℝ)) (q : Velocity) : ℝ≥0∞ :=
  ∫⁻ y in Icc (-multiplierSourceRadius ψ) (multiplierSourceRadius ψ), density q y

theorem sourceDirichletMass_ne_top (ψ : C_c(ℝ, ℝ)) (q : Velocity) :
    sourceDirichletMass ψ q ≠ ∞ := by
  apply ne_of_lt
  apply (hasFiniteIntegral_iff_ofReal
    (Eventually.of_forall (velocityDensity_nonneg q))).mp
  apply Integrable.hasFiniteIntegral
  apply (integrableOn_Icc_iff_integrableOn_Ioc).mpr
  exact (intervalIntegrable_velocityDensity q _ _).1

/-- Quantitative admission with a finite coefficient and the true local Dirichlet density. -/
theorem compact_congestionEnergy_le (ψ : C_c(ℝ, ℝ)) (λ : ℕ → ℝ≥0) (q : Velocity) :
    congestionEnergy (compactMixture ψ λ) q ≤ resistanceMass ψ λ * sourceDirichletMass ψ q := by
  calc
    _ ≤ ∫⁻ y, (Icc (-multiplierSourceRadius ψ) (multiplierSourceRadius ψ)).indicator
        (fun _ => resistanceMass ψ λ) y * density q y :=
      lintegral_mono (fun y => mul_le_mul_right' (compact_congestion_le_indicator ψ λ y) _)
    _ = ∫⁻ y in Icc (-multiplierSourceRadius ψ) (multiplierSourceRadius ψ),
        resistanceMass ψ λ * density q y := by
      rw [← lintegral_indicator measurableSet_Icc]
      apply lintegral_congr
      intro y
      by_cases hy : y ∈ Icc (-multiplierSourceRadius ψ) (multiplierSourceRadius ψ)
      · simp [hy]
      · simp [hy]
    _ = _ := lintegral_const_mul _ (measurable_density q)

theorem compact_congestionEnergy_ne_top (ψ : C_c(ℝ, ℝ)) (λ : ℕ → ℝ≥0) (q : Velocity) :
    congestionEnergy (compactMixture ψ λ) q ≠ ∞ :=
  ne_top_of_le_ne_top (ENNReal.mul_ne_top (resistanceMass_ne_top ψ λ)
    (sourceDirichletMass_ne_top ψ q)) (compact_congestionEnergy_le ψ λ q)

theorem compact_jumpEnergy_ne_top (ψ : C_c(ℝ, ℝ)) (λ : ℕ → ℝ≥0) (q : Velocity) :
    jumpEnergy (compactMixture ψ λ) q ≠ ∞ := by
  have h := compact_congestionEnergy_ne_top ψ λ q
  rw [congestionEnergy_eq_jump_add_slack, ENNReal.add_ne_top] at h
  exact h.1

theorem compact_slackEnergy_ne_top (ψ : C_c(ℝ, ℝ)) (λ : ℕ → ℝ≥0) (q : Velocity) :
    slackEnergy (compactMixture ψ λ) q ≠ ∞ := by
  have h := compact_congestionEnergy_ne_top ψ λ q
  rw [congestionEnergy_eq_jump_add_slack, ENNReal.add_ne_top] at h
  exact h.2

theorem compact_nodalEnergy_ne_top (ψ : C_c(ℝ, ℝ)) (λ : ℕ → ℝ≥0) (q : Velocity) (c : ℝ) :
    nodalEnergy (compactMixture ψ λ) q c ≠ ∞ :=
  ne_top_of_le_ne_top (compact_jumpEnergy_ne_top ψ λ q)
    (nodalEnergy_le_jumpEnergy _ q c)

/-- The actual derivative-weighted graph energy is finite for every physical L2 velocity. -/
theorem compact_derivativeEnergy_ne_top (ψ : C_c(ℝ, ℝ)) (λ : ℕ → ℝ≥0) (q : Velocity) :
    (∫⁻ y, congestion (compactMixture ψ λ) y *
      ENNReal.ofReal (Real.exp (-y)*(deriv (logPrimitive q) y)^2)) ≠ ∞ := by
  rw [← congestionEnergy_eq_derivative]
  exact compact_congestionEnergy_ne_top ψ λ q

end GaloisForLFunctions.BiScaleUncertainty.PathCongestion
