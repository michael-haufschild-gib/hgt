import GaloisForLFunctions.RHTower.Deninger.DeningerBigWittCrossPrimeHarmonicSingularGraphSource
import GaloisForLFunctions.RHTower.Deninger.DeningerGammaSixCofinalMeyerTateXiGreenBoundary

/-!
# Coherent Frobenius approximation of the Xi singular boundary

Finite complete Frobenius right-leg fibres have zero one-leg trace.  Their
closure therefore cannot acquire a nonzero vertical graph component.  By
contrast, the source-normalized prime-harmonic rows converge to the vertical
generator with the completed Xi Green provenance as coefficient.

This file proves the resulting separation law.  A vertical graph class is
approximable by complete coherent Frobenius fibres exactly when its coefficient
vanishes.  For the actual reflected-Gaussian Xi class this is exactly the
critical-line condition, pointwise and globally.

The statement is source-facing rather than another Hilbert-space positivity
criterion: ordinary ambient `ell^(2 : ℕ)` observation loses the vertical component,
whereas the singular graph topology retains the arithmetic one-leg trace.  No
RH, zero-location, positivity, or spectral-realization premise is assumed.
-/

open Complex Filter Function Set Topology

namespace RHTower

noncomputable section

/-- Zero is a genuine complete coherent Frobenius right-leg graph packet. -/
theorem deningerBigWittCrossPair_zero_mem_coherentRightLegGraphSet :
    (0 : DeningerBigWittCrossPairSingularOneLegGraph) ∈
      deningerBigWittCrossPairCoherentRightLegGraphSet := by
  refine ⟨fun _ => 0, ∅, ?_⟩
  simp [deningerBigWittCrossPairFiniteRightLegPacket]

/--
Exact vertical radical of complete coherent Frobenius approximation.

The forward implication uses the continuous one-leg trace: it vanishes on
the coherent closure but reads `z` on the vertical generator.  The converse
uses the literal zero coherent packet.
-/
theorem deningerBigWittCrossPair_vertical_mem_coherentClosure_iff
    (z : ℂ) :
    z • deningerBigWittCrossPairOneLegGraphSingularVector ∈
        closure deningerBigWittCrossPairCoherentRightLegGraphSet ↔
      z = 0 := by
  constructor
  · intro hz
    have htrace :=
      deningerBigWittCrossPairCoherentRightLegGraphSet_closure_le_traceKernel hz
    simpa using htrace
  · intro hz
    subst z
    simpa using
      (subset_closure
        deningerBigWittCrossPair_zero_mem_coherentRightLegGraphSet)

/--
At one Xi divisor copy, the actual completed Green vertical boundary is in
the coherent Frobenius closure exactly on the critical line.
-/
theorem
    deningerBigWitt_reflectedGaussianVertical_mem_coherentClosure_iff
    (r : XiZeroCopy) :
    DeningerMeyerGaussianGreen.reflectedGaussianHorizonGreenProvenance r •
        deningerBigWittCrossPairOneLegGraphSingularVector ∈
        closure deningerBigWittCrossPairCoherentRightLegGraphSet ↔
      (r.1 : ℂ).re = 1 / 2 := by
  rw [deningerBigWittCrossPair_vertical_mem_coherentClosure_iff,
    reflectedGaussianHorizonGreenProvenance_apply_eq_zero_iff]

/--
Global coherent-closure classification.  RH is exactly coherent Frobenius
approximability of every source-defined Xi vertical boundary.
-/
theorem
    forall_deningerBigWitt_reflectedGaussianVertical_mem_coherentClosure_iff_rh :
    (∀ r : XiZeroCopy,
      DeningerMeyerGaussianGreen.reflectedGaussianHorizonGreenProvenance r •
          deningerBigWittCrossPairOneLegGraphSingularVector ∈
        closure deningerBigWittCrossPairCoherentRightLegGraphSet) ↔
      RiemannHypothesis := by
  rw [←
    DeningerMeyerGaussianGreen.reflectedGaussianHorizonGreenProvenance_eq_zero_iff_riemannHypothesis]
  constructor
  · intro h
    apply lp.ext
    funext r
    exact
      (deningerBigWittCrossPair_vertical_mem_coherentClosure_iff _).mp
        (h r)
  · intro h r
    apply
      (deningerBigWittCrossPair_vertical_mem_coherentClosure_iff _).mpr
    have hr := congrArg (fun x : XiDivisorL2 => x r) h
    simpa using hr

/-- Sequential approximation by literal complete coherent Frobenius fibres. -/
def DeningerBigWittCrossPairCoherentlyApproximable
    (v : DeningerBigWittCrossPairSingularOneLegGraph) : Prop :=
  ∃ u : ℕ → DeningerBigWittCrossPairSingularOneLegGraph,
    (∀ n, u n ∈ deningerBigWittCrossPairCoherentRightLegGraphSet) ∧
      Tendsto u atTop (nhds v)

/-- In the Hilbert singular graph, sequential coherent approximation is
exactly membership in the coherent closure. -/
theorem deningerBigWittCrossPair_coherentlyApproximable_iff_mem_closure
    (v : DeningerBigWittCrossPairSingularOneLegGraph) :
    DeningerBigWittCrossPairCoherentlyApproximable v ↔
      v ∈ closure deningerBigWittCrossPairCoherentRightLegGraphSet := by
  constructor
  · rintro ⟨u, hu, hlim⟩
    exact isClosed_closure.mem_of_tendsto hlim
      (Filter.Eventually.of_forall fun n => subset_closure (hu n))
  · intro hv
    rw [mem_closure_iff_seq_limit] at hv
    obtain ⟨u, hu, hlim⟩ := hv
    exact ⟨u, hu, hlim⟩

/-- A vertical singular class has a coherent approximating sequence exactly
when its retained one-leg coefficient is zero. -/
theorem deningerBigWittCrossPair_vertical_coherentlyApproximable_iff
    (z : ℂ) :
    DeningerBigWittCrossPairCoherentlyApproximable
        (z • deningerBigWittCrossPairOneLegGraphSingularVector) ↔
      z = 0 := by
  rw [deningerBigWittCrossPair_coherentlyApproximable_iff_mem_closure,
    deningerBigWittCrossPair_vertical_mem_coherentClosure_iff]

/-- Pointwise source law: an actual Xi vertical boundary has a complete
coherent Frobenius approximating sequence exactly on the critical line. -/
theorem deningerBigWitt_reflectedGaussian_coherentlyApproximable_iff
    (r : XiZeroCopy) :
    DeningerBigWittCrossPairCoherentlyApproximable
        (DeningerMeyerGaussianGreen.reflectedGaussianHorizonGreenProvenance r •
          deningerBigWittCrossPairOneLegGraphSingularVector) ↔
      (r.1 : ℂ).re = 1 / 2 := by
  rw [deningerBigWittCrossPair_vertical_coherentlyApproximable_iff,
    reflectedGaussianHorizonGreenProvenance_apply_eq_zero_iff]

/-- **Coherent singular-approximation RH law.**  Every actual completed-Xi
vertical boundary is a singular-graph limit of complete coherent finite
Frobenius fibres exactly under RH. -/
theorem
    forall_deningerBigWitt_reflectedGaussian_coherentlyApproximable_iff_rh :
    (∀ r : XiZeroCopy,
      DeningerBigWittCrossPairCoherentlyApproximable
        (DeningerMeyerGaussianGreen.reflectedGaussianHorizonGreenProvenance r •
          deningerBigWittCrossPairOneLegGraphSingularVector)) ↔
      RiemannHypothesis := by
  constructor
  · intro h
    exact
      forall_deningerBigWitt_reflectedGaussianVertical_mem_coherentClosure_iff_rh.mp
        (fun r =>
          (deningerBigWittCrossPair_coherentlyApproximable_iff_mem_closure _).mp
            (h r))
  · intro h r
    exact
      (deningerBigWittCrossPair_coherentlyApproximable_iff_mem_closure _).mpr
        (forall_deningerBigWitt_reflectedGaussianVertical_mem_coherentClosure_iff_rh.mpr
          h r)

/-- Off-line displacement forbids every coherent finite-source sequence from
converging to the actual completed-Xi graph boundary. -/
theorem deningerBigWitt_offLine_not_tendsto_reflectedGaussian_of_coherent
    (r : XiZeroCopy) (hr : (r.1 : ℂ).re ≠ 1 / 2)
    (u : ℕ → DeningerBigWittCrossPairSingularOneLegGraph)
    (hu : ∀ n, u n ∈ deningerBigWittCrossPairCoherentRightLegGraphSet) :
    ¬ Tendsto u atTop
      (nhds
        (DeningerMeyerGaussianGreen.reflectedGaussianHorizonGreenProvenance r •
          deningerBigWittCrossPairOneLegGraphSingularVector)) := by
  intro hlim
  exact hr
    ((deningerBigWitt_reflectedGaussian_coherentlyApproximable_iff r).mp
      ⟨u, hu, hlim⟩)

end

end RHTower
