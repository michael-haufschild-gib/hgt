import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmGammaSewnSquarefreeFisherConormalResidue

/-!
# Squarefree Fisher conormal residue splitting

The singular Möbius--Gamma/Xi source correction is the pointed Fisher quotient `F / B`.  At a
strict-right Xi zero, the overlap `B` has order `m` and `F` has order `m - 1`.  This module splits
the quotient into its forced one-dimensional conormal line and an analytic regular germ:

`F(v) / B(v) = 2m / (v - u) + h(v)`.

The regular germ exists and is unique.  This discharges the residue-splitting premise in the MSC
source-order chain; the remaining burden is a source-framed estimate and horizontal annihilation
law for `h`, not removal of the unavoidable residue line.
-/

open Complex Filter Set Topology

namespace RHTower

noncomputable section

/-- A pointed Fisher quotient is its forced simple residue line plus an analytic germ. -/
theorem exists_analyticAt_pointedFisherQuotient_residueSplit
    {f : ℂ → ℂ} {c a : ℂ} {d : ℕ}
    (hf : AnalyticAt ℂ f a)
    (horder : analyticOrderAt f a = (d : ℕ)) :
    ∃ h : ℂ → ℂ, AnalyticAt ℂ h a ∧
      (fun z => pointedFisherNumerator f c z / f z) =ᶠ[𝓝[≠] a]
        fun z => 2 * ((d : ℤ) : ℂ) / (z - a) + h z := by
  have hmeromorphicOrder : meromorphicOrderAt f a = (d : ℤ) := by
    rw [hf.meromorphicOrderAt_eq, horder]
    simp
  obtain ⟨g, hg, hlog⟩ :=
    GaloisForLFunctions.HTGeometry.exists_analyticAt_logDeriv_local_form
      hf.meromorphicAt hmeromorphicOrder
  let h : ℂ → ℂ := fun z => 2 * g z + 2 * c
  have hh : AnalyticAt ℂ h a := by
    dsimp only [h]
    fun_prop
  have hfinite : analyticOrderAt f a ≠ ⊤ := by
    rw [horder]
    exact ENat.coe_ne_top d
  have hfne : ∀ᶠ z in 𝓝[≠] a, f z ≠ 0 := by
    rcases hf.eventually_eq_zero_or_eventually_ne_zero with hzero | hne
    · exact False.elim (hfinite (analyticOrderAt_eq_top.mpr hzero))
    · exact hne
  refine ⟨h, hh, ?_⟩
  filter_upwards [hlog, hfne] with z hzlog hzf
  simp only [pointedFisherNumerator, logDeriv_apply] at hzlog ⊢
  rw [show 2 * (deriv f z + c * f z) / f z =
      2 * (deriv f z / f z + c) by field_simp [hzf]]
  rw [hzlog]
  dsimp only [h]
  ring

/-- The analytic regular part of the residue split is unique as a germ. -/
theorem exists_unique_analyticGerm_pointedFisherQuotient_residueSplit
    {f : ℂ → ℂ} {c a : ℂ} {d : ℕ}
    (hf : AnalyticAt ℂ f a)
    (horder : analyticOrderAt f a = (d : ℕ)) :
    ∃ h : ℂ → ℂ, AnalyticAt ℂ h a ∧
      ((fun z => pointedFisherNumerator f c z / f z) =ᶠ[𝓝[≠] a]
        fun z => 2 * ((d : ℤ) : ℂ) / (z - a) + h z) ∧
      ∀ g : ℂ → ℂ, AnalyticAt ℂ g a →
        ((fun z => pointedFisherNumerator f c z / f z) =ᶠ[𝓝[≠] a]
          fun z => 2 * ((d : ℤ) : ℂ) / (z - a) + g z) →
        h =ᶠ[𝓝 a] g := by
  obtain ⟨h, hh, hsplit⟩ :=
    exists_analyticAt_pointedFisherQuotient_residueSplit hf horder
  refine ⟨h, hh, hsplit, ?_⟩
  intro g hg hgsplit
  have heq : h =ᶠ[𝓝[≠] a] g := by
    filter_upwards [hsplit, hgsplit] with z hz hgz
    linear_combination -hz + hgz
  exact GaloisForLFunctions.HTGeometry.eventuallyEq_nhds_of_nhdsNE_of_continuousAt
    heq hh.continuousAt hg.continuousAt

/-- At every strict-right Xi zero, the singular squarefree Fisher correction splits into the
forced residue `2m/(v-u)` and a unique analytic regular germ. -/
theorem squarefreeFisherConormal_residueSplit_of_strictRightXiZero
    {sigma epsilon u rho : ℂ}
    (hsigma : 1 < sigma.re) (hepsilon : epsilon ≠ 0)
    (hcoord : sigma + u * epsilon = rho)
    (hhalf : 1 / 2 < rho.re) (hone : rho.re < 1)
    (hzero : xi rho = 0) :
    ∃ k : ℕ, analyticOrderAt xi rho = (k + 1 : ℕ) ∧
      ∃ h : ℂ → ℂ, AnalyticAt ℂ h u ∧
        (fun v =>
          GaloisForLFunctions.squarefreeFisherScore sigma epsilon v /
            GaloisForLFunctions.squarefreeBoundaryOverlap sigma epsilon v) =ᶠ[𝓝[≠] u]
          fun v => 2 * ((k + 1 : ℕ) : ℂ) / (v - u) + h v := by
  obtain ⟨k, hkB, _hkF⟩ :=
    analyticOrderAt_squarefreeFisherScore_eq_pred_of_strictRightXiZero
      hsigma hepsilon hcoord hhalf hone hzero
  have hrho1 : rho ≠ 1 := by
    intro h
    rw [h] at hone
    norm_num at hone
  have hBAn : AnalyticAt ℂ
      (GaloisForLFunctions.squarefreeBoundaryOverlap sigma epsilon) u :=
    analyticAt_squarefreeBoundaryOverlap_of_half_lt_re
      (by simpa [hcoord] using hhalf) (by simpa [hcoord] using hrho1)
  have hXiOrder : analyticOrderAt xi rho = (k + 1 : ℕ) := by
    rw [← analyticOrderAt_squarefreeBoundaryOverlap_eq_xi_of_strictRightStrip
      hsigma hepsilon hcoord hhalf hone]
    exact hkB
  obtain ⟨h, hh, hsplit⟩ :=
    exists_analyticAt_pointedFisherQuotient_residueSplit hBAn hkB
      (c := epsilon * GaloisForLFunctions.squarefreeFixedCurrent sigma)
  refine ⟨k, hXiOrder, h, hh, ?_⟩
  change (fun v =>
      pointedFisherNumerator
          (GaloisForLFunctions.squarefreeBoundaryOverlap sigma epsilon)
          (epsilon * GaloisForLFunctions.squarefreeFixedCurrent sigma) v /
        GaloisForLFunctions.squarefreeBoundaryOverlap sigma epsilon v) =ᶠ[𝓝[≠] u]
      fun v => 2 * ((k + 1 : ℕ) : ℂ) / (v - u) + h v
  simpa using hsplit

/-- Closed MSC residue-splitting certificate over every strict-right source line and Xi zero. -/
structure MobiusGammaXiSingularConormalResidueSplitCertificate : Prop where
  split : ∀ {sigma epsilon u rho : ℂ},
    1 < sigma.re → epsilon ≠ 0 → sigma + u * epsilon = rho →
    1 / 2 < rho.re → rho.re < 1 → xi rho = 0 →
    ∃ k : ℕ, analyticOrderAt xi rho = (k + 1 : ℕ) ∧
      ∃ h : ℂ → ℂ, AnalyticAt ℂ h u ∧
        (fun v =>
          GaloisForLFunctions.squarefreeFisherScore sigma epsilon v /
            GaloisForLFunctions.squarefreeBoundaryOverlap sigma epsilon v) =ᶠ[𝓝[≠] u]
          fun v => 2 * ((k + 1 : ℕ) : ℂ) / (v - u) + h v

/-- The MSC singular conormal always admits the exact residue/regular decomposition. -/
theorem mobiusGammaXiSingularConormalResidueSplit_law :
    MobiusGammaXiSingularConormalResidueSplitCertificate where
  split := squarefreeFisherConormal_residueSplit_of_strictRightXiZero

end

end RHTower
