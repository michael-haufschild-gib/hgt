import GaloisForLFunctions.RHTower.XiMassCriticalCenteredDirichletCone
import GaloisForLFunctions.RHTower.XiMassCriticalWeilPairingCriterion
import GaloisForLFunctions.RHTower.Deninger.DeningerCriticalFloquetCrossCurrent
import GaloisForLFunctions.RHTower.XiReflectionSelfIntersectionCharge

/-!
# Reflection charge forces critical arithmetic source escape

The mass route has several exact source realizations of the same critical obstruction: the raw
discrete Selberg-remainder current, the finite centered von Mangoldt cone, its literal Dirichlet
polynomial pairing, the fixed half-density Weil measure, and the non-diagonal Deninger cross
current.  Their existing capstones identify uniform vertical boundedness with RH.

This module converts those receiver equivalences into direct, charge-triggered escape laws.  If
one canonical reflection self-intersection charge is nonzero, every proposed uniform bound is
violated at a nonnegative mass time in every realization.  Thus the horizontal divisor charge is
carried specifically by the raw arithmetic source, after the floor, terminal, integer, and
spacelike corrections have been removed.

No RH premise, zero-location estimate, numerical computation, or new axiom is used.
-/

open Complex

namespace RHTower

noncomputable section

private theorem not_riemannHypothesis_of_reflectionCharge_ne_zero
    {T : ℝ} (hcharge : xiReflectionSelfIntersectionCharge T ≠ 0) :
    ¬ RiemannHypothesis := by
  intro hRH
  exact hcharge
    (xiReflectionSelfIntersectionCharge_eq_zero_of_riemannHypothesis hRH T)

private theorem exists_nonnegative_norm_gt_of_not_lineBound
    {f : ℝ → ℂ}
    (hnot : ¬ ∃ C : ℝ, ∀ u : ℝ, 0 ≤ u → ‖f u‖ ≤ C)
    (C : ℝ) :
    ∃ u : ℝ, 0 ≤ u ∧ C < ‖f u‖ := by
  by_contra hescape
  apply hnot
  refine ⟨C, fun u hu => ?_⟩
  by_contra hle
  exact hescape ⟨u, hu, lt_of_not_ge hle⟩

/-- A nonzero reflection charge forces the raw discrete `psi(N) - N` current to escape every
bound on the nonnegative mass half-line. -/
theorem xiMassCriticalDiscreteRemainderFlux_unbounded_of_reflectionCharge_ne_zero
    {a c sigma T : ℝ} (hhalf : 1 / 2 < c) (hca : c < a)
    (hsigma : 0 < sigma)
    (hcharge : xiReflectionSelfIntersectionCharge T ≠ 0)
    (C : ℝ) :
    ∃ u : ℝ, 0 ≤ u ∧ C <
      ‖xiMassCriticalDiscreteRemainderFlux a sigma u‖ := by
  apply exists_nonnegative_norm_gt_of_not_lineBound (C := C)
  intro hbound
  exact (not_riemannHypothesis_of_reflectionCharge_ne_zero hcharge)
    ((riemannHypothesis_iff_xiMassCriticalDiscreteRemainderFluxNonnegativeLineBound
      hhalf hca hsigma).mpr hbound)

/-- The same charge forces escape of the finite centered `Lambda - 1` atom cone. -/
theorem xiMassCriticalCenteredAtomConeSum_unbounded_of_reflectionCharge_ne_zero
    {a c sigma d T : ℝ} (hhalf : 1 / 2 < c) (hca : c < a)
    (hsigma : 0 < sigma) (hdhalf : 1 / 2 < d) (hda : d < a)
    (hcharge : xiReflectionSelfIntersectionCharge T ≠ 0)
    (C : ℝ) :
    ∃ u : ℝ, 0 ≤ u ∧ C <
      ‖xiMassCriticalCenteredAtomConeSum a sigma d u‖ := by
  apply exists_nonnegative_norm_gt_of_not_lineBound (C := C)
  intro hbound
  exact (not_riemannHypothesis_of_reflectionCharge_ne_zero hcharge)
    ((riemannHypothesis_iff_xiMassCriticalCenteredAtomConeLineBound
      hhalf hca hsigma hdhalf hda).mpr hbound)

/-- The exact mass/centered-Dirichlet-polynomial pairing cannot remain uniformly bounded when a
canonical reflection charge survives. -/
theorem xiMassCriticalCenteredDirichletConePairing_unbounded_of_reflectionCharge_ne_zero
    {a c sigma d T : ℝ} (hhalf : 1 / 2 < c) (hca : c < a)
    (hsigma : 0 < sigma) (hdhalf : 1 / 2 < d) (hda : d < a)
    (hcharge : xiReflectionSelfIntersectionCharge T ≠ 0)
    (C : ℝ) :
    ∃ u : ℝ, 0 ≤ u ∧ C <
      ‖∫ x : ℝ, xiMassAnalyticTest a ((sigma : ℂ) + u * I) (x : ℂ) *
        xiMassCriticalCenteredDirichletConePolynomial d u x‖ := by
  apply exists_nonnegative_norm_gt_of_not_lineBound (C := C)
  intro hbound
  exact (not_riemannHypothesis_of_reflectionCharge_ne_zero hcharge)
    ((riemannHypothesis_iff_xiMassCriticalCenteredDirichletConePairingLineBound
      hhalf hca hsigma hdhalf hda).mpr hbound)

/-- After every uniformly bounded moving-cone complement is removed, nonzero reflection charge
forces escape of the fixed critical half-density Weil-source pairing itself. -/
theorem xiMassCriticalHalfDensityWeilPairing_unbounded_of_reflectionCharge_ne_zero
    {a c sigma d T : ℝ} (hhalf : 1 / 2 < c) (hca : c < a)
    (hsigma : 0 < sigma) (hdhalf : 1 / 2 < d) (hda : d < a)
    (hcharge : xiReflectionSelfIntersectionCharge T ≠ 0)
    (C : ℝ) :
    ∃ u : ℝ, 0 ≤ u ∧ C <
      ‖xiMassCriticalHalfDensityWeilPairing a sigma u‖ := by
  apply exists_nonnegative_norm_gt_of_not_lineBound (C := C)
  intro hbound
  exact (not_riemannHypothesis_of_reflectionCharge_ne_zero hcharge)
    ((riemannHypothesis_iff_xiMassCriticalHalfDensityWeilPairingLineBound
      hhalf hca hsigma hdhalf hda).mpr hbound)

/-- The canonical unequal-half Deninger current also carries the charge: its finite critical cone
escapes every proposed bound. -/
theorem xiMassCriticalDeningerCrossCurrentCone_unbounded_of_reflectionCharge_ne_zero
    {a c sigma d T : ℝ} (hhalf : 1 / 2 < c) (hca : c < a)
    (hsigma : 0 < sigma) (hdhalf : 1 / 2 < d) (hda : d < a)
    (hcharge : xiReflectionSelfIntersectionCharge T ≠ 0)
    (C : ℝ) :
    ∃ u : ℝ, 0 ≤ u ∧ C <
      ‖xiMassCriticalDeningerCrossCurrentCone a sigma d u‖ := by
  apply exists_nonnegative_norm_gt_of_not_lineBound (C := C)
  intro hbound
  exact (not_riemannHypothesis_of_reflectionCharge_ne_zero hcharge)
    ((riemannHypothesis_iff_xiMassCriticalDeningerCrossCurrentConeLineBound
      hhalf hca hsigma hdhalf hda).mpr hbound)

end

end RHTower
