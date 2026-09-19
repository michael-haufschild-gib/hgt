import GaloisForLFunctions.RHTower.CCMRestrictedWeilGammaSlepianStrictSource
import GaloisForLFunctions.RHTower.CCMRestrictedWeilCanonicalGroundHeadConvergence
import GaloisForLFunctions.RHTower.SuzukiFirstContactBoundaryRoughness

/-!
# Counterexample amplification by the literal restricted-Weil remainder

The exact canonical CCM ground satisfies `E • G u - D u = u`, where `G` is the positive
Gamma--Slepian Gram and `D` is the literal compressed scalar--polar--prime remainder.  A negative
ground energy therefore cannot be a small or contractive remainder effect: it forces strict norm
expansion by `D` on the exact ground.  Convergence of the canonical finite Gamma--Slepian heads
transports that strict expansion cofinally to literal finite heads.

This supplies a source-faithful finite-head counterexample signature.  It does not establish the
RH-bearing nonexpansion condition; rather, it identifies that condition as a concrete operator
target without splitting prime, polar, or Gamma source channels.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct InnerProductSpace BigOperators ComplexConjugate

noncomputable section

namespace RHTower

/-- Negative ground energy strictly expands its exact ground vector under the literal compressed
scalar--polar--prime remainder. -/
theorem ccmRestrictedWeilFormRemainder_strict_norm_expansion_of_groundEnergy_neg
    (a : SuzukiPositiveAperture)
    (hE : ccmRestrictedWeilGroundEnergy a < 0) :
    ‖ccmRestrictedWeilFormRemainder a
        (ccmRestrictedWeilCanonicalGroundFormLift a)‖ >
      ‖ccmRestrictedWeilCanonicalGroundFormLift a‖ := by
  let u := ccmRestrictedWeilCanonicalGroundFormLift a
  let G := ccmArchimedeanGammaSlepianGram a
  let D := ccmRestrictedWeilFormRemainder a
  let E : ℝ := ccmRestrictedWeilGroundEnergy a
  have hfixed := ccmRestrictedWeilCanonicalGroundFormLift_birmanSchwinger_fixed a
  rw [ccmRestrictedWeilFormBirmanSchwinger_eq_gammaSlepian_sub_remainder] at hfixed
  change (E : ℂ) • G u - D u = u at hfixed
  have hD : D u = (E : ℂ) • G u - u := by
    rw [eq_sub_iff_add_eq]
    rw [sub_eq_iff_eq_add] at hfixed
    simpa [add_comm] using hfixed.symm
  have hu : u ≠ 0 := by
    intro hu
    have he := ccmRestrictedWeilCanonicalGroundFormLift_embedding a
    rw [show ccmRestrictedWeilCanonicalGroundFormLift a = 0 by simpa [u] using hu,
      map_zero] at he
    exact ccmRestrictedWeilCanonicalGroundEigenstate_ne_zero a he.symm
  have hphysical : 0 < ‖ccmArchimedeanFormToAperture a u‖ ^ 2 := by
    apply sq_pos_of_pos
    apply norm_pos_iff.mpr
    intro hz
    apply hu
    exact ccmArchimedeanFormToAperture_injective a (by simpa using hz)
  have hinner : 0 < (inner ℂ (G u) u).re := by
    have henergy := ccmArchimedeanGammaSlepianGram_reApplyInnerSelf a u
    rw [ContinuousLinearMap.reApplyInnerSelf_apply] at henergy
    change (inner ℂ (G u) u).re =
      ‖ccmArchimedeanFormToAperture a u‖ ^ 2 at henergy
    rw [henergy]
    exact hphysical
  rw [hD]
  have hsq_gt : ‖u‖ ^ 2 < ‖(E : ℂ) • G u - u‖ ^ 2 := by
    rw [norm_sub_sq (𝕜 := ℂ)]
    have hreal : (inner ℂ ((E : ℂ) • G u) u).re = E * (inner ℂ (G u) u).re := by
      simp [Complex.mul_re]
    change ‖u‖ ^ 2 < ‖(E : ℂ) • G u‖ ^ 2 -
      2 * (inner ℂ ((E : ℂ) • G u) u).re + ‖u‖ ^ 2
    rw [hreal]
    have hsq : 0 ≤ ‖(E : ℂ) • G u‖ ^ 2 := sq_nonneg _
    nlinarith
  have hnorm_gt : ‖u‖ < ‖(E : ℂ) • G u - u‖ := by
    exact (sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq_gt
  simpa [u] using hnorm_gt

/-- A negative exact ground energy forces cofinal strict expansion on the literal finite
Gamma--Slepian heads. -/
theorem eventually_ccmRestrictedWeilCanonicalGroundHead_formRemainder_strict_norm_expansion_of_groundEnergy_neg
    (a : SuzukiPositiveAperture)
    (hE : ccmRestrictedWeilGroundEnergy a < 0) :
    ∀ᶠ n in atTop,
      ‖ccmRestrictedWeilCanonicalGroundHead a n‖ <
        ‖ccmRestrictedWeilFormRemainder a
          (ccmRestrictedWeilCanonicalGroundHead a n)‖ := by
  let u := ccmRestrictedWeilCanonicalGroundFormLift a
  let D := ccmRestrictedWeilFormRemainder a
  have hstrict : ‖u‖ < ‖D u‖ := by
    dsimp only [u, D]
    exact ccmRestrictedWeilFormRemainder_strict_norm_expansion_of_groundEnergy_neg a hE
  have hhead := tendsto_ccmRestrictedWeilCanonicalGroundHead a
  have hnorm : Tendsto (fun n : ℕ => ‖ccmRestrictedWeilCanonicalGroundHead a n‖)
      atTop (nhds ‖u‖) :=
    (continuous_norm.tendsto _).comp hhead
  have hDnorm : Tendsto (fun n : ℕ => ‖D (ccmRestrictedWeilCanonicalGroundHead a n)‖)
      atTop (nhds ‖D u‖) :=
    (continuous_norm.tendsto _).comp ((D.continuous.tendsto _).comp hhead)
  have hdiff := hDnorm.sub hnorm
  filter_upwards [hdiff.eventually (Ioi_mem_nhds (sub_pos.mpr hstrict))] with n hn
  linarith

/-- Cofinal nonexpansion by the same literal compressed remainder on every canonical actual head
implies RH. -/
theorem riemannHypothesis_of_eventually_ccmRestrictedWeilCanonicalGroundHead_formRemainder_nonexpansive
    (h : ∀ a : SuzukiPositiveAperture, ∀ᶠ n in atTop,
      ‖ccmRestrictedWeilFormRemainder a
          (ccmRestrictedWeilCanonicalGroundHead a n)‖ ≤
        ‖ccmRestrictedWeilCanonicalGroundHead a n‖) :
    RiemannHypothesis := by
  by_contra hnot
  obtain ⟨a, hE⟩ := exists_ccmRestrictedWeilGroundEnergy_neg_of_not_riemannHypothesis hnot
  have hexpand :=
    eventually_ccmRestrictedWeilCanonicalGroundHead_formRemainder_strict_norm_expansion_of_groundEnergy_neg
      a hE
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 ((h a).and hexpand)
  have hpair := hN N le_rfl
  linarith [hpair.1, hpair.2]

end RHTower
