import GaloisForLFunctions.SignedWindowCriticality.OnReflectionPairsTheCouplingIsTheSmoothedPrimeCount
import GaloisForLFunctions.RHTower.WeilLagFunctionOneSided
import GaloisForLFunctions.RHTower.JointAncestrySquareShellFinitePowerCriterion
import GaloisForLFunctions.RHTower.ChronologicalRiemannEquivalence
import GaloisForLFunctions.RHTower.RegularizedLogZetaAbscissa
import GaloisForLFunctions.RHTower.RobinCriterionRiemann

/-!
# Reflection-pair prime counts feed the classical receivers

The exact band for the self-convolution-smoothed prime count is equivalent to the
Weil-lag lower bound, square-shell Riesz bounds, bounded chronological approximation,
regularized prime-zeta convergence and eventual Robin inequality. The two-site identity
gives the band from Weil positivity; the band itself makes every window test nonnegative.
These equivalences transfer a bound, and do not assert the bound.
-/

noncomputable section

open Filter Topology

namespace GaloisForLFunctions.SignedWindowCriticality

open _root_.RHTower SpacingScaleHarmonicAnalysis CohomologyOfWindowsOfSpecZ

/-- The exact prime-count error band on every left half-window. -/
def ReflectionPrimeCountBand : Prop :=
  ∀ f : ℝ → ℝ, ContDiff ℝ 2 f → HasCompactSupport f →
    (∀ u, 0 < u → f u = 0) →
    |collarHankel 0 f - ∑' n : ℕ, vonMangoldtAtom n * selfConv f (-Real.log n)| ≤
      weilQuad f

/-- The reflection-pair count band is exactly the global window sign. -/
theorem reflectionPrimeCountBand_iff_riemannHypothesis :
    ReflectionPrimeCountBand ↔ RiemannHypothesis := by
  constructor
  · intro h
    apply riemannHypothesis_iff_windowForm_nonneg.mpr
    intro A _ f hf
    have h0 : ∀ u, 0 < u → f u = 0 := fun u hu =>
      hf.vanish u (fun hmem => (not_le.mpr hu) hmem.2)
    exact (abs_nonneg _).trans (h f hf.contDiff hf.hasCompactSupport h0)
  · intro h f hf hfc h0
    have hW := ArithmeticHodgeTheoryOfDegenerations.riemannHypothesis_iff_weilQuad_nonneg.mp h
    have hpair := (abs_coupling_le_weilQuad_iff hf hfc h0).mpr
      ⟨hW _ (hf.add (contDiff_collarReflect hf))
          (hfc.add (hasCompactSupport_collarReflect hfc)),
        hW _ (hf.add (contDiff_collarReflect hf).neg)
          (hfc.add (hasCompactSupport_collarReflect hfc).neg)⟩
    simpa only [mul_zero, zero_sub] using hpair

/-- The band feeds, and is recovered from, the one-sided Weil-lag receiver. -/
theorem reflectionPrimeCountBand_iff_weilLag_bddBelow :
    ReflectionPrimeCountBand ↔ ∃ M : ℝ, ∀ L : ℝ, -M ≤ weilLagFunctionReal L :=
  reflectionPrimeCountBand_iff_riemannHypothesis.trans
    riemannHypothesis_iff_weilLagFunctionReal_bddBelow

/-- The band is equivalent to the finite-power square-shell Riesz receiver. -/
theorem reflectionPrimeCountBand_iff_squareShellRiesz :
    ReflectionPrimeCountBand ↔ ∀ ε : ℝ, 0 < ε → ∃ᶠ m : ℕ in atTop,
      ∀ k : ℕ, m < k →
        (k : ℝ) ≤ (m : ℝ) + (m : ℝ) / Real.log ((m : ℝ) + 1) →
        ‖jasShellRieszSum (m ^ 2) k‖ ≤ (m : ℝ) ^ (ε * k) :=
  reflectionPrimeCountBand_iff_riemannHypothesis.trans
    riemannHypothesis_iff_squareShellRiesz_finitePowerWindow

/-- The band is equivalent to approximation by chronological rows bounded by one. -/
theorem reflectionPrimeCountBand_iff_chronological_unit_rows :
    ReflectionPrimeCountBand ↔ ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∃ a : ℕ → ℝ,
      (∀ k ∈ Finset.Ioc 0 N, |a k| ≤ 1) ∧
        chronologicalL2Norm (chronologicalHeatError a N) < ε :=
  reflectionPrimeCountBand_iff_riemannHypothesis.trans
    riemannHypothesis_iff_chronological_unit_rows

/-- The band is equivalent to convergence of the regularized prime-zeta series. -/
theorem reflectionPrimeCountBand_iff_primeRegCoeff_converges :
    ReflectionPrimeCountBand ↔ ConvergesRightOf primeRegCoeff (1 / 2) :=
  reflectionPrimeCountBand_iff_riemannHypothesis.trans
    riemannHypothesis_iff_primeRegCoeff_converges

/-- The band is equivalent to Robin's inequality at every sufficiently large integer. -/
theorem reflectionPrimeCountBand_iff_eventually_robin :
    ReflectionPrimeCountBand ↔ ∀ᶠ n : ℕ in atTop, (ArithmeticFunction.sigma 1 n : ℝ) <
      Real.exp Real.eulerMascheroniConstant * n * Real.log (Real.log n) :=
  reflectionPrimeCountBand_iff_riemannHypothesis.trans riemannHypothesis_iff_eventually_robin

#print axioms reflectionPrimeCountBand_iff_riemannHypothesis
#print axioms reflectionPrimeCountBand_iff_weilLag_bddBelow
#print axioms reflectionPrimeCountBand_iff_squareShellRiesz
#print axioms reflectionPrimeCountBand_iff_chronological_unit_rows
#print axioms reflectionPrimeCountBand_iff_primeRegCoeff_converges
#print axioms reflectionPrimeCountBand_iff_eventually_robin

end GaloisForLFunctions.SignedWindowCriticality
