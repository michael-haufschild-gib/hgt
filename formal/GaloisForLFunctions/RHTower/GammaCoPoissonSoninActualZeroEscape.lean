import GaloisForLFunctions.RHTower.BurnolCoPoissonReciprocalSeedLanding
import GaloisForLFunctions.RHTower.GammaCoPoissonSoninQuadrantZeta

/-!
# Full-source annihilation and forced escape at actual zeta zeros

General reciprocal-seed landing turns every cosine source generator into a direct source vector.
The existing direct Mellin factorization therefore annihilates both branches at every zeta zero,
then continuity annihilates the full closed source space. This supplies the missing converse from an
actual right-half-strip zeta zero to the co-Poisson ladder annihilator and makes the ladder escape
law unconditional on the actual zero locus.
-/

open Complex Real MeasureTheory Set Topology
open scoped InnerProductSpace

noncomputable section

namespace RHTower

/-- At a zeta zero, the Riesz evaluator annihilates the full source generator set, including every
cosine branch. Reciprocal-seed landing is exactly the missing step for the cosine branch. -/
theorem inner_burnolExtendedSoninEvaluationVector_generator_eq_zero
    {b : ℝ} (hb : 0 < b) {w : ℂ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1)
    (hz : riemannZeta w = 0) {u : evenSubspace}
    (hu : u ∈ burnolCoPoissonGeneratorSet b) :
    ⟪(burnolExtendedSoninEvaluationVector w b hlo hhi hb : evenSubspace), u⟫_ℂ = 0 := by
  obtain ⟨src, rfl | rfl⟩ := hu
  · exact inner_burnolExtendedSoninEvaluationVector_source_eq_zero hb src hlo hhi hz
  · have hrec := inner_burnolExtendedSoninEvaluationVector_source_eq_zero hb
      (src.reciprocal hb) hlo hhi hz
    change ⟪(burnolExtendedSoninEvaluationVector w b hlo hhi hb : evenSubspace),
      ((src.reciprocal hb).vector : evenSubspace)⟫_ℂ = 0 at hrec
    rw [BurnolCoPoissonSource.reciprocal_vector,
      coe_burnolExtendedSoninCosine] at hrec
    exact hrec

/-- A zeta zero annihilates the full closed co-Poisson source space, not only the direct-vector
subspace. -/
theorem inner_burnolExtendedSoninEvaluationVector_eq_zero_of_mem_sourceSpace
    {b : ℝ} (hb : 0 < b) {w : ℂ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1)
    (hz : riemannZeta w = 0) (u : evenSubspace)
    (hu : u ∈ burnolCoPoissonSourceSpace b) :
    ⟪(burnolExtendedSoninEvaluationVector w b hlo hhi hb : evenSubspace), u⟫_ℂ = 0 := by
  set k : evenSubspace :=
    (burnolExtendedSoninEvaluationVector w b hlo hhi hb : evenSubspace) with hk
  set K : Submodule ℂ evenSubspace :=
    LinearMap.ker ((innerSL ℂ k).toLinearMap) with hK
  have hclosed : IsClosed (K : Set evenSubspace) := (innerSL ℂ k).isClosed_ker
  have hgen : burnolCoPoissonGeneratorSet b ⊆ (K : Set evenSubspace) := by
    intro v hv
    rw [SetLike.mem_coe, hK, LinearMap.mem_ker]
    show ⟪k, v⟫_ℂ = 0
    rw [hk]
    exact inner_burnolExtendedSoninEvaluationVector_generator_eq_zero hb hlo hhi hz hv
  have hle : burnolCoPoissonSourceSpace b ≤ K :=
    (burnolCoPoissonAlgebraicSourceSpace b).topologicalClosure_minimal
      (Submodule.span_le.mpr hgen) hclosed
  have hmem := hle hu
  rw [hK, LinearMap.mem_ker] at hmem
  simpa [hk] using hmem

/-- Full-source converse: every right-half-strip zeta zero is a Burnol source-annihilator point. -/
theorem burnolCoPoissonAnnihilatorPoint_of_riemannZeta_eq_zero
    {w : ℂ} {b : ℝ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1) (hb : 0 < b)
    (hz : riemannZeta w = 0) :
    BurnolCoPoissonAnnihilatorPoint w b hlo hhi hb := by
  intro c
  have hinner := inner_burnolExtendedSoninEvaluationVector_eq_zero_of_mem_sourceSpace
    hb hlo hhi hz (c : evenSubspace) c.property
  let u : soninExtendedSpace b :=
    ⟨(c : evenSubspace), burnolCoPoissonSourceSpace_le_soninExtendedSpace hb c.property⟩
  have hinner' :
      ⟪burnolExtendedSoninEvaluationVector w b hlo hhi hb, u⟫_ℂ = 0 := by
    change ⟪(burnolExtendedSoninEvaluationVector w b hlo hhi hb : evenSubspace),
      (c : evenSubspace)⟫_ℂ = 0
    exact hinner
  rw [inner_burnolExtendedSoninEvaluationVector] at hinner'
  exact hinner'

/-- Every right-half-strip zeta zero annihilates every aperture in every positive ladder. -/
theorem coPoissonLadderAnnihilator_of_riemannZeta_eq_zero
    {w : ℂ} {a r : ℝ} {hlo : 1 / 2 < w.re} {hhi : w.re < 1}
    {ha : 0 < a} {hr : 0 < r} (hz : riemannZeta w = 0) :
    CoPoissonLadderAnnihilator w hlo hhi a r ha hr := by
  intro j
  exact burnolCoPoissonAnnihilatorPoint_of_riemannZeta_eq_zero hlo hhi
    (soninAperture_pos ha hr j) hz

/-- Exact actual-zero classification of the full-source ladder annihilator. -/
theorem coPoissonLadderAnnihilator_iff_riemannZeta_eq_zero
    {w : ℂ} {a r : ℝ} {hlo : 1 / 2 < w.re} {hhi : w.re < 1}
    {ha : 0 < a} {hr : 0 < r} (ha1 : a < 1) (hr1 : 1 ≤ r) :
    CoPoissonLadderAnnihilator w hlo hhi a r ha hr ↔ riemannZeta w = 0 := by
  exact ⟨riemannZeta_eq_zero_of_coPoissonLadderAnnihilator ha1 hr1,
    coPoissonLadderAnnihilator_of_riemannZeta_eq_zero⟩

/-- Exact forced escape is now available at every actual right-half-strip zeta zero. -/
theorem norm_coPoissonLadderKernel_max_le_of_riemannZeta_eq_zero
    {w : ℂ} {a r : ℝ} {hlo : 1 / 2 < w.re} {hhi : w.re < 1}
    {ha : 0 < a} {hr : 0 < r} (hr1 : 1 ≤ r) (hz : riemannZeta w = 0) (N : ℕ) :
    max (‖soninLadderCharacter w r‖ ^ N) ((‖soninLadderCharacter w r‖⁻¹) ^ N) *
        ‖coPoissonLadderKernel w hlo hhi a r ha hr 0‖ ≤
      ‖coPoissonLadderKernel w hlo hhi a r ha hr N‖ :=
  norm_coPoissonLadderKernel_max_le hr1
    (coPoissonLadderAnnihilator_of_riemannZeta_eq_zero hz) N

end RHTower
