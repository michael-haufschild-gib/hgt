import GaloisForLFunctions.RHTower.HedenmalmSourceHilbertGramClosedGraphNoGo
import GaloisForLFunctions.RHTower.PreQuasiGelfandTwoSidedSingularDefect

/-!
# Hedenmalm theta ordinary-`L²` pre-quasi exclusion

A closed densely defined positive embedding does not repair the ordinary-`L²`
nonclosability of a nonzero momentum-symmetric theta-null Hilbert-Gram form on
the full Schwartz source core.
-/

open Complex Function Filter Set
open scoped Topology SchwartzMap

noncomputable section

namespace RHTower

/-- A full-source pre-quasi realization of the Hedenmalm theta form over
ordinary Lebesgue `L²`. -/
def HedenmalmThetaOrdinaryL2PreQuasiRealization : Prop :=
  ∃ (Q : SchwartzMap.ContinuousSchwartzSesquilinearForm)
      (plus minus : XiThetaL2 →ₗ.[ℂ] XiThetaL2)
      (J : SchwartzMap ℝ ℂ →ₗ[ℂ] XiThetaL2),
    HilbertPreQuasiPair plus minus ∧
      HilbertGramRealizes Q J ∧
      Q.MomentumSymmetric ∧
      J xiThetaSchwartzSource = 0 ∧
      J ≠ 0 ∧
      ∃ hdom : ∀ u : SchwartzMap ℝ ℂ,
          xiThetaSchwartzToL2 u ∈ plus.domain,
        ∀ u : SchwartzMap ℝ ℂ,
          plus ⟨xiThetaSchwartzToL2 u, hdom u⟩ = J u

/-- **Ordinary-`L²` pre-quasi exclusion.** No nonzero momentum-symmetric
theta-null Hilbert-Gram form on the full Schwartz source can be the positive
embedding of even a pre-quasi-Gelfand pair over ordinary `L²(R)`. -/
theorem not_hedenmalmThetaOrdinaryL2PreQuasiRealization :
    ¬ HedenmalmThetaOrdinaryL2PreQuasiRealization := by
  rintro ⟨Q, plus, minus, J, hpair, hgram, hMomentum, hsource, hJ,
    hdom, hrealize⟩
  exact (hilbertGram_l2PartialOperator_not_closable
    Q J hgram hMomentum hsource hJ plus hdom hrealize)
      hpair.plus_closed.isClosable

/-- Closed proposition expressing the strongest positive survivor: every
pre-quasi candidate satisfying the fixed source and Gram clauses must escape
the full-source realization condition. -/
def HedenmalmThetaOrdinaryL2PreQuasiSourceEscape : Prop :=
  ∀ (Q : SchwartzMap.ContinuousSchwartzSesquilinearForm)
      (plus minus : XiThetaL2 →ₗ.[ℂ] XiThetaL2)
      (J : SchwartzMap ℝ ℂ →ₗ[ℂ] XiThetaL2),
    HilbertPreQuasiPair plus minus →
    HilbertGramRealizes Q J →
    Q.MomentumSymmetric →
    J xiThetaSchwartzSource = 0 →
    J ≠ 0 →
      (∃ u : SchwartzMap ℝ ℂ, xiThetaSchwartzToL2 u ∉ plus.domain) ∨
        ∃ (u : SchwartzMap ℝ ℂ)
            (hu : xiThetaSchwartzToL2 u ∈ plus.domain),
          plus ⟨xiThetaSchwartzToL2 u, hu⟩ ≠ J u

/-- **Full-source escape law.** A closed theorem with no declaration premises:
the positive embedding must omit a Schwartz vector or disagree with the
proposed realization on an admitted vector. -/
theorem hedenmalmThetaOrdinaryL2PreQuasi_sourceEscape :
    HedenmalmThetaOrdinaryL2PreQuasiSourceEscape := by
  intro Q plus minus J hpair hgram hMomentum hsource hJ
  by_cases hdom : ∀ u : SchwartzMap ℝ ℂ,
      xiThetaSchwartzToL2 u ∈ plus.domain
  · right
    by_contra hagree
    push Not at hagree
    exact (hilbertGram_l2PartialOperator_not_closable
      Q J hgram hMomentum hsource hJ plus hdom
        (fun u => hagree u (hdom u))) hpair.plus_closed.isClosable
  · left
    push Not at hdom
    exact hdom

end RHTower
