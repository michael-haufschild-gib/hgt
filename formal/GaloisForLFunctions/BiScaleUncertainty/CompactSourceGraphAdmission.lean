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

theorem compact_congestion_eq_zero (ψ : C_c(ℝ, ℝ)) (weights : ℕ → ℝ≥0) (y : ℝ)
    (hy : y ∉ Icc (-multiplierSourceRadius ψ) (multiplierSourceRadius ψ)) :
    congestion (compactMixture ψ weights) y = 0 := by
  rw [congestion_eq_diffuse_add_lines]
  have hd : (∫⁻ e, pathKernel e y ∂diffuseMeasure (compactMixture ψ weights)) = 0 := by
    rw [diffuseMeasure, lintegral_withDensity_eq_lintegral_mul _
      (measurable_compactDiffuse ψ weights) (measurable_pathKernel_left y)]
    have hz : ∀ e, (compactMixture ψ weights).diffuseWeight e * pathKernel e y = 0 := by
      intro e
      rcases sourcePair_or_path_zero ψ e y hy with hp | hp
      · simp [compactMixture, hp]
      · simp [hp]
    simp only [Pi.mul_apply, hz, lintegral_zero]
  have hl (n : ℕ) : (∫⁻ u, pathKernel ((compactMixture ψ weights).lag n,u) y
      ∂volume.withDensity ((compactMixture ψ weights).lineWeight n)) = 0 := by
    have hm : Measurable (fun u : ℝ => pathKernel ((compactMixture ψ weights).lag n,u) y) :=
      (measurable_pathKernel_left y).comp (measurable_const.prodMk measurable_id)
    rw [lintegral_withDensity_eq_lintegral_mul _ (measurable_compactLine ψ weights n) hm]
    have hz : ∀ u, (compactMixture ψ weights).lineWeight n u *
        pathKernel ((compactMixture ψ weights).lag n,u) y = 0 := by
      intro u
      rcases sourcePair_or_path_zero ψ ((compactMixture ψ weights).lag n,u) y hy with hp | hp
      · simp [compactMixture] at hp ⊢
        rw [hp]
        simp
      · simp [hp]
    simp only [Pi.mul_apply, hz, lintegral_zero]
  simp only [hd, hl, tsum_zero, add_zero]

theorem compact_congestion_le_mass (ψ : C_c(ℝ, ℝ)) (weights : ℕ → ℝ≥0) (y : ℝ) :
    congestion (compactMixture ψ weights) y ≤ resistanceMass ψ weights := by
  apply lintegral_mono
  intro e
  by_cases hy : y ∈ Ioc (lower e) (upper e)
  · simp [pathKernel, hy]
  · simp [pathKernel, hy]

/-- A bounded compactly supported majorant constructed from the actual source. -/
theorem compact_congestion_le_indicator (ψ : C_c(ℝ, ℝ)) (weights : ℕ → ℝ≥0) (y : ℝ) :
    congestion (compactMixture ψ weights) y ≤
      (Icc (-multiplierSourceRadius ψ) (multiplierSourceRadius ψ)).indicator
        (fun _ => resistanceMass ψ weights) y := by
  by_cases hy : y ∈ Icc (-multiplierSourceRadius ψ) (multiplierSourceRadius ψ)
  · simpa [hy] using compact_congestion_le_mass ψ weights y
  · simp [hy, compact_congestion_eq_zero ψ weights y hy]

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
theorem compact_congestionEnergy_le (ψ : C_c(ℝ, ℝ)) (weights : ℕ → ℝ≥0) (q : Velocity) :
    congestionEnergy (compactMixture ψ weights) q ≤ resistanceMass ψ weights * sourceDirichletMass ψ q := by
  calc
    _ ≤ ∫⁻ y, (Icc (-multiplierSourceRadius ψ) (multiplierSourceRadius ψ)).indicator
        (fun _ => resistanceMass ψ weights) y * density q y :=
      lintegral_mono (fun y => by
        gcongr
        exact compact_congestion_le_indicator ψ weights y)
    _ = ∫⁻ y in Icc (-multiplierSourceRadius ψ) (multiplierSourceRadius ψ),
        resistanceMass ψ weights * density q y := by
      rw [← lintegral_indicator measurableSet_Icc]
      apply lintegral_congr
      intro y
      by_cases hy : y ∈ Icc (-multiplierSourceRadius ψ) (multiplierSourceRadius ψ)
      · simp [hy]
      · simp [hy]
    _ = _ := lintegral_const_mul _ (measurable_density q)

theorem compact_congestionEnergy_ne_top (ψ : C_c(ℝ, ℝ)) (weights : ℕ → ℝ≥0) (q : Velocity) :
    congestionEnergy (compactMixture ψ weights) q ≠ ∞ :=
  ne_top_of_le_ne_top (ENNReal.mul_ne_top (resistanceMass_ne_top ψ weights)
    (sourceDirichletMass_ne_top ψ q)) (compact_congestionEnergy_le ψ weights q)

theorem compact_jumpEnergy_ne_top (ψ : C_c(ℝ, ℝ)) (weights : ℕ → ℝ≥0) (q : Velocity) :
    jumpEnergy (compactMixture ψ weights) q ≠ ∞ := by
  have h := compact_congestionEnergy_ne_top ψ weights q
  rw [congestionEnergy_eq_jump_add_slack, ENNReal.add_ne_top] at h
  exact h.1

theorem compact_slackEnergy_ne_top (ψ : C_c(ℝ, ℝ)) (weights : ℕ → ℝ≥0) (q : Velocity) :
    slackEnergy (compactMixture ψ weights) q ≠ ∞ := by
  have h := compact_congestionEnergy_ne_top ψ weights q
  rw [congestionEnergy_eq_jump_add_slack, ENNReal.add_ne_top] at h
  exact h.2

theorem compact_nodalEnergy_ne_top (ψ : C_c(ℝ, ℝ)) (weights : ℕ → ℝ≥0) (q : Velocity) (c : ℝ) :
    nodalEnergy (compactMixture ψ weights) q c ≠ ∞ :=
  ne_top_of_le_ne_top (compact_jumpEnergy_ne_top ψ weights q)
    (nodalEnergy_le_jumpEnergy _ q c)

/-- The actual derivative-weighted graph energy is finite for every physical L2 velocity. -/
theorem compact_derivativeEnergy_ne_top (ψ : C_c(ℝ, ℝ)) (weights : ℕ → ℝ≥0) (q : Velocity) :
    (∫⁻ y, congestion (compactMixture ψ weights) y *
      ENNReal.ofReal (Real.exp (-y)*(deriv (logPrimitive q) y)^2)) ≠ ∞ := by
  rw [← congestionEnergy_eq_derivative]
  exact compact_congestionEnergy_ne_top ψ weights q

/-- Weighted source L2 mass, including the arbitrary constant in a homogeneous primitive. -/
def sourceMass (ψ : C_c(ℝ, ℝ)) (q : Velocity) (c : ℝ) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal (ψ y ^ 2 * (c+logPrimitive q y)^2)

theorem sourceMass_ne_top (ψ : C_c(ℝ, ℝ)) (q : Velocity) (c : ℝ) :
    sourceMass ψ q c ≠ ∞ := by
  have hc : Continuous (fun y => ψ y ^ 2 * (c+logPrimitive q y)^2) :=
    (ψ.continuous.pow 2).mul ((continuous_const.add (continuous_logPrimitive q)).pow 2)
  have hs : HasCompactSupport (fun y => ψ y ^ 2 * (c+logPrimitive q y)^2) := by
    apply HasCompactSupport.of_support_subset_isCompact ψ.hasCompactSupport.isCompact
    intro y hy
    apply subset_closure
    apply Function.mem_support.mpr
    intro hp
    simp [Function.mem_support, hp] at hy
  exact ne_of_lt ((hasFiniteIntegral_iff_ofReal
    (Eventually.of_forall (fun y => mul_nonneg (sq_nonneg (ψ y)) (sq_nonneg _)))).mp
      (hc.integrable_of_hasCompactSupport hs).hasFiniteIntegral)

/-- Admission to the constructed source-mass plus jump-energy domain. -/
theorem compact_formEnergy_ne_top (ψ : C_c(ℝ, ℝ)) (weights : ℕ → ℝ≥0)
    (q : Velocity) (c : ℝ) :
    sourceMass ψ q c + jumpEnergy (compactMixture ψ weights) q ≠ ∞ :=
  ENNReal.add_ne_top.mpr ⟨sourceMass_ne_top ψ q c, compact_jumpEnergy_ne_top ψ weights q⟩

end GaloisForLFunctions.BiScaleUncertainty.PathCongestion
