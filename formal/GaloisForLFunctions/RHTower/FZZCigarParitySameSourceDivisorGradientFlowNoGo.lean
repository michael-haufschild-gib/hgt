import GaloisForLFunctions.HTGeometry.EntireZeroSetNull
import GaloisForLFunctions.RHTower.FZZCigarParityReflectedFermiInformationGradientFlow

/-!
# Fixed-source divisor gradient-flow no-go for the FZZ parity route

The literal FZZ parity Mellin source has a strict reflected-Fermi inward velocity off the critical
wall.  That ambient source velocity cannot be a continuous velocity of a zero of the unchanged
source: the open-strip source divisor agrees with the zero set of the nonzero entire completed Xi,
and every continuous family in this discrete divisor is constant.

Consequently a same-source horizontal gradient trajectory through an open-strip FZZ mode exists
exactly on the critical wall.  Universal existence is exactly RH, rather than an independent
dynamical producer of RH.  The strongest positive survivor is source-deformation necessity: every
nonconstant continuous open-strip path must leave the divisor of the unchanged FZZ source.
-/

open Complex MeasureTheory Set InformationTheory
open scoped ENNReal

namespace RHTower

noncomputable section

/-- A horizontal reflected-Fermi gradient curve which remains in the divisor of the unchanged
literal FZZ parity Mellin source. -/
def FZZCigarParitySameSourceReflectedFermiGradientTrajectory (rho : ℂ) : Prop :=
  ∃ gamma : ℝ → ℂ,
    Continuous gamma ∧
      gamma 0 = rho ∧
      (∀ t : ℝ,
        0 < (gamma t).re ∧
          (gamma t).re < 1 ∧
          FZZCigarParityMellinMode (gamma t)) ∧
      ∀ t : ℝ,
        HasDerivAt (fun u : ℝ => (gamma u).re)
          (fzzCigarParityReflectedFermiInformationVelocity (gamma t).re) t

/-- Every continuous family in the open-strip divisor of the unchanged literal FZZ source is
constant. The parameter space may be any preconnected space. -/
theorem continuous_fzzCigarParity_sameSourceModeFamily_constant
    {T : Type*} [TopologicalSpace T] [PreconnectedSpace T]
    (gamma : T → ℂ) (hgamma : Continuous gamma)
    (hstrip : ∀ t : T, 0 < (gamma t).re ∧ (gamma t).re < 1)
    (hmode : ∀ t : T, FZZCigarParityMellinMode (gamma t))
    (s t : T) :
    gamma s = gamma t := by
  letI : DiscreteTopology {z : ℂ // xi z = 0} :=
    HTGeometry.discreteTopology_setOf_eq_zero xi_analyticOnNhd_univ
      ⟨0, by norm_num [xi]⟩
  let gammaXi : T → {z : ℂ // xi z = 0} := fun u =>
    ⟨gamma u,
      (fzzCigarParityMellin_eq_zero_iff_xi_eq_zero
        (hstrip u).1 (hstrip u).2).1 (hmode u)⟩
  have hgammaXi : Continuous gammaXi := hgamma.subtype_mk _
  have hconst : gammaXi s = gammaXi t :=
    PreconnectedSpace.constant (by infer_instance : PreconnectedSpace T) hgammaXi
  exact congrArg Subtype.val hconst

/-- Pointwise classification: same-source reflected-Fermi gradient realizability is exactly the
critical wall. -/
theorem fzzCigarParity_sameSourceReflectedFermiGradientTrajectory_iff
    {rho : ℂ} (h0 : 0 < rho.re) (h1 : rho.re < 1)
    (hmode : FZZCigarParityMellinMode rho) :
    FZZCigarParitySameSourceReflectedFermiGradientTrajectory rho ↔
      rho.re = 1 / 2 := by
  constructor
  · rintro ⟨gamma, hgamma, hgamma0, hfamily, hderiv⟩
    have hconst : ∀ t : ℝ, gamma t = rho := by
      intro t
      exact (continuous_fzzCigarParity_sameSourceModeFamily_constant gamma hgamma
        (fun u => ⟨(hfamily u).1, (hfamily u).2.1⟩)
        (fun u => (hfamily u).2.2) t 0).trans hgamma0
    have hzero : HasDerivAt (fun u : ℝ => (gamma u).re) 0 0 := by
      have hfun : (fun u : ℝ => (gamma u).re) = fun _ : ℝ => rho.re := by
        funext u
        rw [hconst u]
      rw [hfun]
      exact hasDerivAt_const (0 : ℝ) rho.re
    have hvelocity :
        fzzCigarParityReflectedFermiInformationVelocity (gamma 0).re = 0 :=
      (hderiv 0).unique hzero
    have hforce : fzzCigarParityReflectedFermiInformationForce rho.re = 0 := by
      rw [hgamma0, fzzCigarParityReflectedFermiInformationVelocity] at hvelocity
      linarith
    exact (fzzCigarParityReflectedFermiInformationForce_eq_zero_iff h0 h1).1 hforce
  · intro hrho
    refine ⟨fun _ : ℝ => rho, continuous_const, rfl, ?_, ?_⟩
    · intro t
      exact ⟨h0, h1, hmode⟩
    · intro t
      have hvelocity :
          fzzCigarParityReflectedFermiInformationVelocity rho.re = 0 := by
        rw [hrho, fzzCigarParityReflectedFermiInformationVelocity,
          fzzCigarParityReflectedFermiInformationForce_half, neg_zero]
      simpa [hvelocity] using (hasDerivAt_const t rho.re)

/-- Universal same-source gradient realizability for all literal FZZ parity Mellin modes. -/
def FZZCigarParitySameSourceReflectedFermiGradientRealizability : Prop :=
  ∀ rho : ℂ, 0 < rho.re → rho.re < 1 → FZZCigarParityMellinMode rho →
    FZZCigarParitySameSourceReflectedFermiGradientTrajectory rho

/-- Universal same-source gradient realizability is exactly RH. -/
theorem fzzCigarParity_sameSourceReflectedFermiGradientRealizability_iff_riemannHypothesis :
    FZZCigarParitySameSourceReflectedFermiGradientRealizability ↔ RiemannHypothesis := by
  rw [← fzzCigarParityReflectedFermiInformationStationarity_iff_riemannHypothesis]
  constructor
  · intro hrealize rho h0 h1 hmode
    apply (fzzCigarParityReflectedFermiInformationForce_eq_zero_iff h0 h1).2
    exact (fzzCigarParity_sameSourceReflectedFermiGradientTrajectory_iff h0 h1 hmode).1
      (hrealize rho h0 h1 hmode)
  · intro hstationary rho h0 h1 hmode
    apply (fzzCigarParity_sameSourceReflectedFermiGradientTrajectory_iff h0 h1 hmode).2
    exact (fzzCigarParityReflectedFermiInformationForce_eq_zero_iff h0 h1).1
      (hstationary rho h0 h1 hmode)

/-- Positive survivor: a nonconstant continuous open-strip path must leave the divisor of the
unchanged literal FZZ parity Mellin source. -/
theorem exists_not_fzzCigarParityMellinMode_of_continuous_openStrip_path_ne
    (gamma : ℝ → ℂ) (hgamma : Continuous gamma)
    (hstrip : ∀ t : ℝ, 0 < (gamma t).re ∧ (gamma t).re < 1)
    {s t : ℝ} (hne : gamma s ≠ gamma t) :
    ∃ u : ℝ, ¬ FZZCigarParityMellinMode (gamma u) := by
  by_contra hleave
  have hmode : ∀ u : ℝ, FZZCigarParityMellinMode (gamma u) := by
    intro u
    by_contra hnot
    exact hleave ⟨u, hnot⟩
  exact hne
    (continuous_fzzCigarParity_sameSourceModeFamily_constant gamma hgamma hstrip hmode s t)

/-- Closed route classification: fixed-source continuous divisor transport is impossible off the
critical wall, and its universal existence is not a new RH producer but exactly RH. -/
theorem fzzCigarParity_sameSourceDivisorGradientFlow_noGo :
    (∀ {T : Type*} [TopologicalSpace T] [PreconnectedSpace T]
        (gamma : T → ℂ),
        Continuous gamma →
        (∀ t : T, 0 < (gamma t).re ∧ (gamma t).re < 1) →
        (∀ t : T, FZZCigarParityMellinMode (gamma t)) →
        ∀ s t : T, gamma s = gamma t) ∧
      (∀ rho : ℂ, 0 < rho.re → rho.re < 1 →
        FZZCigarParityMellinMode rho →
        (FZZCigarParitySameSourceReflectedFermiGradientTrajectory rho ↔
          rho.re = 1 / 2)) ∧
      (FZZCigarParitySameSourceReflectedFermiGradientRealizability ↔
        RiemannHypothesis) ∧
      (∀ rho : ℂ, 0 < rho.re → rho.re < 1 →
        FZZCigarParityMellinMode rho → rho.re ≠ 1 / 2 →
        ¬ FZZCigarParitySameSourceReflectedFermiGradientTrajectory rho) := by
  refine ⟨?_, ?_,
    fzzCigarParity_sameSourceReflectedFermiGradientRealizability_iff_riemannHypothesis, ?_⟩
  · intro T _ _ gamma hgamma hstrip hmode s t
    exact continuous_fzzCigarParity_sameSourceModeFamily_constant gamma hgamma hstrip hmode s t
  · intro rho h0 h1 hmode
    exact fzzCigarParity_sameSourceReflectedFermiGradientTrajectory_iff h0 h1 hmode
  · intro rho h0 h1 hmode hne htrajectory
    exact hne ((fzzCigarParity_sameSourceReflectedFermiGradientTrajectory_iff h0 h1 hmode).1
      htrajectory)

end

end RHTower
