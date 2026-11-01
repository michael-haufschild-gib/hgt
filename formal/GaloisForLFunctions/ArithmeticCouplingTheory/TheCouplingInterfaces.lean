import GaloisForLFunctions.ArithmeticCouplingTheory.BoundedCouplingIsTheRiemannHypothesis
import GaloisForLFunctions.ArithmeticCouplingTheory.MixedDifferencesSeeEveryZero
import GaloisForLFunctions.ArithmeticCouplingTheory.TheMertensPolarization
import GaloisForLFunctions.EdgeHodgeTheory.TheEdgeIsAThresholdCurve
import GaloisForLFunctions.EdgeHodgeTheory.TheEdgeOfTheCompleteWeilFamily
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.PrimeCoherenceCalculus

/-!
# Interfaces: edge Hodge theory and critical-scale rigidity

**Edge Hodge theory.** EHT measures where positivity of the complete Weil family fails: the family
`W_{φ,wN,N}` is positive at every horizon iff the atom of width `w` sees no right zero, and RH is
the absence of an edge. The coupling form reads the same data:

* the threshold at width `w` is the threshold of the coupling probe of the atom: positivity at
  every horizon iff the orbit kernel of the mixed difference of the atom has no negative square
  (`forall_positiveAt_width_iff_couplingForm`);
* no edge iff bounded inter-tower coupling (`eventually_hyperplaneEdge_eq_top_iff_bounded_coupling`).

**Critical-scale rigidity.** The incidence packets of ACoT are CSAR's prime-incidence packets, i.e.
normalized conductor packets with coefficients `√(p − 1)/p · b_p`
(`incidencePacket_eq_normalizedConductorPacket`).
-/

open GaloisForLFunctions.HeckeKreinToeplitz
open GaloisForLFunctions.ArithmeticOrientationGeometry (seenRightZeros)
open GaloisForLFunctions.EdgeHodgeTheory (Admissible PositiveAt forall_positiveAt_width_iff
  atomDilate_mem_realTests' hyperplaneEdge riemannHypothesis_iff_eventually_hyperplaneEdge_eq_top)
open GaloisForLFunctions.SpacingScaleHarmonicAnalysis (atomDilate)
open GaloisForLFunctions.SpacingScaleHarmonicAnalysis (tiltedUnitSpline)
open Filter Zeta23

noncomputable section

namespace GaloisForLFunctions.ArithmeticCouplingTheory

/-- **The threshold curve is read by the coupling form.** At width `w`, the complete Weil family is
positive at every horizon iff the coupling probe `(T_α − 1)(T_β − 1)` of the atom has a positive
Weil orbit kernel, for any scales `α, β ≠ 0`. -/
theorem forall_positiveAt_width_iff_couplingForm {φ : ℝ → ℝ} (hφ : Admissible φ) {w : ℝ}
    (hw : 0 < w) {α β : ℝ} (hα : α ≠ 0) (hβ : β ≠ 0) :
    (∀ N : ℕ, 1 ≤ N → PositiveAt φ (w * N) N) ↔
      negIndex (orbitKernel zetaZeroConfig (mixedDiff α β (atomDilate φ w))) = 0 := by
  have hf := atomDilate_mem_realTests' hφ hw
  rw [forall_positiveAt_width_iff hφ hw, negIndex_orbitKernel _
    SquareRootThreshold.temperedConfig_zetaZeroConfig (mixedDiff_mem_realTests hf α β),
    seenRightZeros_mixedDiff _ hf hα hβ, Set.encard_eq_zero]

/-- **No edge is bounded coupling.** The hyperplane edge of the tilted-spline family is eventually
infinite iff the inter-tower coupling of Weil's kernel is bounded on `⟨2, 3⟩ × ⟨5, 7⟩`. -/
theorem eventually_hyperplaneEdge_eq_top_iff_bounded_coupling :
    (∀ᶠ N in atTop, hyperplaneEdge tiltedUnitSpline N = ⊤) ↔
      ∃ M : ℝ, ∀ u ∈ twoPrimeLattice Nat.prime_two Nat.prime_three,
        ∀ v ∈ twoPrimeLattice (by norm_num : Nat.Prime 5) (by norm_num : Nat.Prime 7),
          ‖coupling zetaKernel u v‖ ≤ M := by
  rw [← riemannHypothesis_iff_eventually_hyperplaneEdge_eq_top]
  exact riemannHypothesis_iff_exists_bound_coupling_2357

/-- **ACoT incidence packets are CSAR prime-incidence packets.** -/
theorem incidencePacket_eq_normalizedConductorPacket (Q : ℕ) (b : ℕ → ℝ) (n : ℕ) :
    incidencePacket ((Finset.Icc 1 Q).filter Nat.Prime) b n =
      CriticalScaleArithmeticRigidity.normalizedConductorPacket Q
        (CriticalScaleArithmeticRigidity.primeIncidenceCoefficients b) n := by
  rw [CriticalScaleArithmeticRigidity.primeIncidencePacket_eq, incidencePacket]

end GaloisForLFunctions.ArithmeticCouplingTheory
