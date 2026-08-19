import GaloisForLFunctions.RHTower.BurnolCoPoissonCosineClosedZeroAnnihilator
import GaloisForLFunctions.RHTower.BurnolCoPoissonSubWindowIndependence

/-!
# Exact zeroth-jet detection on Burnol's cosine-closed source space

The preceding source theorem proves the forward implication: at a right-strip
zeta zero, the completed Mellin Riesz vector annihilates the closed
cosine-stable co-Poisson source space.  The reverse implication is not a
density assertion.  A single literal symmetric subwindow
`[b, b⁻¹]` belongs to that same closed space and detects every nonzero zeta
value.  Thus the closed cosine system has exactly the zeta zero set as its
zeroth-jet orthogonality locus.

This is a genuine closed-space, cosine-closed zeroth-jet completeness law.  It
does not claim Burnol's higher-jet or aperture-complement completeness
theorems: those require continuous higher jet evaluators and the `L_a/K_a/P_a`
argument.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped InnerProductSpace

noncomputable section

namespace RHTower

/-- On the closed cosine-stable literal co-Poisson source space, the completed
zeroth Mellin jet vanishes exactly at the zeta zeros in the right strip. -/
theorem burnolExtendedSoninEvaluationVector_mem_coPoissonSource_orthogonal_iff
    {b : ℝ} (hb : 0 < b) (hb1 : b < 1)
    {w : ℂ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1) :
    (burnolExtendedSoninEvaluationVector w b hlo hhi hb : evenSubspace) ∈
        (burnolCoPoissonSourceSpace b)ᗮ ↔
      riemannZeta w = 0 := by
  constructor
  · intro horth
    by_contra hzero
    have hbinv : b < b⁻¹ := by
      have h1 : (1 : ℝ) < b⁻¹ := (one_lt_inv₀ hb).mpr hb1
      linarith
    have hap : subWindowAperture b b⁻¹ = b :=
      subWindowAperture_left_eq hb hbinv.le (le_of_eq rfl)
    have hAle : b ≤ subWindowAperture b b⁻¹ := le_of_eq hap.symm
    let u : soninExtendedSpace b := coPoissonSubWindowSoninAt hb hbinv.le hAle
    have hgen : (u : evenSubspace) ∈ burnolCoPoissonGeneratorSet b := by
      refine ⟨coPoissonSubWindowSourceAt hb hb hbinv.le hAle, Or.inl ?_⟩
      rfl
    have hu : (u : evenSubspace) ∈ burnolCoPoissonSourceSpace b :=
      (burnolCoPoissonAlgebraicSourceSpace b).le_topologicalClosure
        (Submodule.subset_span hgen)
    rw [Submodule.mem_orthogonal'] at horth
    have hvan : ⟪(burnolExtendedSoninEvaluationVector w b hlo hhi hb : evenSubspace),
        (u : evenSubspace)⟫_ℂ = 0 :=
      horth u hu
    have hne : ⟪burnolExtendedSoninEvaluationVector w b hlo hhi hb,
        coPoissonSubWindowSoninAt hb hbinv.le hAle⟫_ℂ ≠ 0 :=
      inner_burnolExtendedSoninEvaluationVector_subWindowAt_ne_zero
        hlo hhi hzero hb hb hbinv hAle
    exact hne (by simpa [u] using hvan)
  · intro hzero
    exact burnolExtendedSoninEvaluationVector_mem_coPoissonSource_orthogonal
      hb hlo hhi hzero

end RHTower
