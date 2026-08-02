import GaloisForLFunctions.RHTower.CompleteResolutionCofinalConditioningLaw
import GaloisForLFunctions.RHTower.PrimeValuationHellingerReesReflectionFracture
import GaloisForLFunctions.RHTower.XiSourceBoundaryOrientationConservation

/-!
# Nonlocal--singular completion law for the Riemann source

Complete prime-normal observation creates one affine packet radical at the
cofinal Riemann source horizon.  Its leading finite projections are all
surjective.  In the product topology the radical is therefore dense, and
closed relation completion becomes maximally vertical.  An informative
closed completion must instead use a topology strictly finer than every
finite-coordinate observation.

The reflected prime-valuation sectors impose an independent-looking
analytic cost, but the same radical mechanism controls them.  The positive
sector is flat beyond every finite Wold--Rees order, while its reflection is
half-normal.  Every exact linear sewing has norm growth beyond every finite
Rees order.

The capstone below combines the two conclusions.  Any completion which is
both output-informative and reflection-sewing is necessarily nonlocal in
topology and essentially singular in operator order.  This identifies the
minimal architecture of any surviving completion route: neither product
observation nor finite-order graded operators can carry it.
-/

open Complex Filter Topology Asymptotics GaloisForLFunctions

namespace RHTower

noncomputable section

/-- **Nonlocal--singular completion law.** Suppose a closed relation retains
the exact countable prime-normal packets of the complete Riemann source in
a target topology `t` finer than finite-coordinate product observation.
Suppose also that a family of linear sewing maps exactly transports the
positive prime-valuation Hellinger sector to its reflected negative sector.

If the relation still carries output information, then:

1. `t` is strictly finer than the product topology, so the information is
   invisible to every finite set of prime coordinates; and
2. the sewing operator norm dominates every inverse finite power of the
   Wold boundary volume in the little-o sense.

Thus an informative reflected completion must be simultaneously
infinite-prime nonlocal and beyond every finite Rees order. -/
theorem riemannSource_nonlocalSingularCompletion_law
    (t : TopologicalSpace (ℕ → ℂ))
    (ht : t ≤ completeResolutionCountablePrimeProductTopology)
    {c : ℝ} (hc : 0 < c) (hcHalf : c < 1 / 2)
    (S : ℕ → (ℝ →L[ℝ] ℝ))
    (hsew :
      (fun N =>
        S N (primeValuationSquaredHellingerBelow c N)) =
      primeValuationSquaredHellingerBelow (-c)) :
    letI : TopologicalSpace (ℕ → ℂ) := t
    ∀ (R : Submodule ℂ
        (CompleteResolutionSourceSpace × (ℕ → ℂ))),
      IsClosed
          (R : Set (CompleteResolutionSourceSpace × (ℕ → ℂ))) →
      ∀ y : ℕ → ℂ,
      (∀ (K j : ℕ),
        (completeResolutionCountablePrimeInput K j,
          completeResolutionCountablePrimeOutput j - y) ∈ R) →
      (R : Set (CompleteResolutionSourceSpace × (ℕ → ℂ))) ≠
          linearRelationDomain R ×ˢ Set.univ →
      t < completeResolutionCountablePrimeProductTopology ∧
        ∀ K : ℕ,
          (fun N =>
            (primeWoldBoundaryVolumeBelow N)⁻¹ ^ K) =o[atTop]
          (fun N => ‖S N‖) := by
  letI : TopologicalSpace (ℕ → ℂ) := t
  intro R hclosed y hgraph hinfo
  refine
    ⟨completeResolution_countablePrime_informative_forces_strictTopology
      t ht R hclosed y hgraph hinfo, ?_⟩
  intro K
  exact
    reflectedHellingerSewingOperatorNorm_beyondEveryReesOrder
      hc hcHalf S hsew K

/-- **Oriented Xi specialization.** At an actual right-half Xi divisor
copy, the nonlocal--singular cost is carried by the same signed invariant
as the completed logarithmic-current residue.

The reflected source entropy is exactly minus twice the positive
horizontal divisor charge.  If an informative completion sews the two
valuation sectors selected by that charge, its topology is strictly
nonproduct and its operator norm is beyond every finite Rees order, while
the completed Xi current retains the unsquared complex outer charge. -/
theorem xiRight_orientedNonlocalSingularCompletion_law
    (q : XiRightZeroCopy)
    (t : TopologicalSpace (ℕ → ℂ))
    (ht : t ≤ completeResolutionCountablePrimeProductTopology)
    (S : ℕ → (ℝ →L[ℝ] ℝ))
    (hsew :
      (fun N =>
        S N
          (primeValuationSquaredHellingerBelow
            (xiRightSourceModularCharge q) N)) =
      primeValuationSquaredHellingerBelow
        (-xiRightSourceModularCharge q)) :
    letI : TopologicalSpace (ℕ → ℂ) := t
    ∀ (R : Submodule ℂ
        (CompleteResolutionSourceSpace × (ℕ → ℂ))),
      IsClosed
          (R : Set (CompleteResolutionSourceSpace × (ℕ → ℂ))) →
      ∀ y : ℕ → ℂ,
      (∀ (K j : ℕ),
        (completeResolutionCountablePrimeInput K j,
          completeResolutionCountablePrimeOutput j - y) ∈ R) →
      (R : Set (CompleteResolutionSourceSpace × (ℕ → ℂ))) ≠
          linearRelationDomain R ×ˢ Set.univ →
      t < completeResolutionCountablePrimeProductTopology ∧
        (∀ K : ℕ,
          (fun N =>
            (primeWoldBoundaryVolumeBelow N)⁻¹ ^ K) =o[atTop]
          (fun N => ‖S N‖)) ∧
        riemannReflectedSourceEntropy (q.1.1 : ℂ) =
          -2 * xiRightSourceModularCharge q ∧
        Tendsto
          (fun s : ℂ =>
            (s - (q.1.1 : ℂ)) *
              xiExceptionalAffineDivisorCurrent s)
          (𝓝[≠] (q.1.1 : ℂ))
          (𝓝
            (-(((q.1.1 : ℂ) - 1 / 2) *
              ((analyticOrderAt xi (q.1.1 : ℂ)).toNat : ℂ)))) := by
  letI : TopologicalSpace (ℕ → ℂ) := t
  intro R hclosed y hgraph hinfo
  have hcost :=
    riemannSource_nonlocalSingularCompletion_law
      t ht
      (xiRightSourceModularCharge_pos q)
      (xiRightSourceModularCharge_lt_half q)
      S hsew R hclosed y hgraph hinfo
  refine ⟨hcost.1, hcost.2, ?_, ?_⟩
  · exact xiRightReflectedSourceEntropy_eq_neg_two_modularCharge q
  · exact
      (xiDepthNearby_sourceBoundaryOrientationConservation
        (q.1.1 : ℂ)).2.1

end

end RHTower
