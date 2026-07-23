import GaloisForLFunctions.HTGeometry.ConfocalGlobalSupportTransform
import GaloisForLFunctions.RHTower.PositiveFieldBicompletionLaw

/-!
# Positive-field global confocal fixed-point universality

Local Bernstein-field equality recovers equality of exterior confocal envelopes.  Independently,
the global confocal support transform identifies every realized envelope defect as the greatest
nonnegative fixed point of its source-specific null-support operator.  Their closure shows that
two possibly different operators selected by the local field share one greatest fixed-point branch
throughout the exterior domain.
-/

namespace HTGeometry

noncomputable section

/-- A value is the greatest nonnegative fixed point of the confocal null-support operator. -/
def IsGreatestConfocalNullFixedPoint
    (S : Set (ℝ × ℝ)) (R d : ℝ) : Prop :=
  0 ≤ d ∧ d = confocalNullSupportOperator S R d ∧
    ∀ e : ℝ, 0 ≤ e → e = confocalNullSupportOperator S R e → e ≤ d

/-- Equal bounded confocal upper fields have the same greatest fixed-point defect branch, even
though their source-specific null-support operators may differ. -/
theorem eqOn_confocalUpperField_sharedGreatestFixedPoint
    {S T : Set ℂ} (hneS : S.Nonempty) (hneT : T.Nonempty)
    {M N : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hboundS : ∀ z ∈ S, ‖z‖ ≤ M) (hboundT : ∀ z ∈ T, ‖z‖ ≤ N)
    {D : Set ℝ} (hD : ∀ R ∈ D, 0 < R)
    (hfield : Set.EqOn (confocalUpperField S) (confocalUpperField T) D) :
    ∀ R ∈ D,
      IsGreatestConfocalNullFixedPoint (confocalLorentzLift '' S) R
          (confocalGlobalDefect (confocalLorentzLift '' S) R) ∧
        confocalGlobalDefect (confocalLorentzLift '' S) R =
          confocalGlobalDefect (confocalLorentzLift '' T) R ∧
        IsGreatestConfocalNullFixedPoint (confocalLorentzLift '' T) R
          (confocalGlobalDefect (confocalLorentzLift '' T) R) := by
  intro R hRD
  have hconeS : confocalLorentzLift '' S ⊆ confocalLorentzCone := by
    rintro _ ⟨z, _hz, rfl⟩
    exact confocalLorentzLift_mem z
  have hconeT : confocalLorentzLift '' T ⊆ confocalLorentzCone := by
    rintro _ ⟨z, _hz, rfl⟩
    exact confocalLorentzLift_mem z
  have hliftBoundS : ∀ q ∈ confocalLorentzLift '' S, q.2 ≤ M := by
    rintro _ ⟨z, hz, rfl⟩
    simpa [confocalLorentzLift] using hboundS z hz
  have hliftBoundT : ∀ q ∈ confocalLorentzLift '' T, q.2 ≤ N := by
    rintro _ ⟨z, hz, rfl⟩
    simpa [confocalLorentzLift] using hboundT z hz
  have hliftNeS : (confocalLorentzLift '' S).Nonempty := hneS.image _
  have hliftNeT : (confocalLorentzLift '' T).Nonempty := hneT.image _
  have henvelopeS := isConfocalEnvelopeOn_confocalLorentzLift_image hneS hboundS hD
  have henvelopeT := isConfocalEnvelopeOn_confocalLorentzLift_image hneT hboundT hD
  have hglobalS := isLUB_confocalGlobalEnvelope hliftNeS hM (hD R hRD) hconeS hliftBoundS
  have hglobalT := isLUB_confocalGlobalEnvelope hliftNeT hN (hD R hRD) hconeT hliftBoundT
  have henvelopeEqS : confocalGlobalEnvelope (confocalLorentzLift '' S) R =
      confocalUpperField S R := hglobalS.unique (henvelopeS R hRD)
  have henvelopeEqT : confocalGlobalEnvelope (confocalLorentzLift '' T) R =
      confocalUpperField T R := hglobalT.unique (henvelopeT R hRD)
  have hdefectEq : confocalGlobalDefect (confocalLorentzLift '' S) R =
      confocalGlobalDefect (confocalLorentzLift '' T) R := by
    rw [confocalGlobalDefect, confocalGlobalDefect, henvelopeEqS, henvelopeEqT,
      hfield hRD]
  refine ⟨?_, hdefectEq, ?_⟩
  · exact confocalGlobalDefect_isGreatest_fixedPoint
      hliftNeS hM (hD R hRD) hconeS hliftBoundS
  · exact confocalGlobalDefect_isGreatest_fixedPoint
      hliftNeT hN (hD R hRD) hconeT hliftBoundT

end

end HTGeometry

namespace RHTower

open Complex Filter Topology
open scoped BigOperators Real ComplexOrder

noncomputable section

/-- **Positive-field global confocal fixed-point universality.** Agreement on one positive scale
window forces the two atomic presentations' source-specific null-support operators to share their
greatest nonnegative defect branch at every exterior radius. -/
theorem localPositiveScaleField_sharedGlobalConfocalGreatestFixedPoint
    {I J : Type*} (c z : I → ℂ) (d w : J → ℂ) (m m' : ℕ → ℝ)
    (hc : Summable c) (hd : Summable d)
    (htransZ : Tendsto (fun i => HTGeometry.transverseDefect (z i))
      cofinite (nhds 0))
    (htransW : Tendsto (fun j => HTGeometry.transverseDefect (w j))
      cofinite (nhds 0))
    {M N a b : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hboundZ : ∀ i, ‖z i‖ ≤ M) (hboundW : ∀ j, ‖w j‖ ≤ N)
    (hab : a < b)
    (hrealZ : ∀ i, (z i).im = 0 → 0 ≤ (z i).re)
    (hrealW : ∀ j, (w j).im = 0 → 0 ≤ (w j).re)
    (hmomentZ : ∀ n, (m n : ℂ) = atomicPowerMoment c z n)
    (hmomentW : ∀ n, (m' n : ℂ) = atomicPowerMoment d w n)
    (hm0 : 0 < m 0) (hm0' : 0 < m' 0)
    (hobs : LocalPositiveScaleFieldAgrees m m' a b) :
    m = m' ∧
      ∀ R ∈ Set.Ioi (max M N),
        HTGeometry.IsGreatestConfocalNullFixedPoint
            (HTGeometry.confocalLorentzLift ''
              Set.range (atomicAggregateNode c z)) R
            (HTGeometry.confocalGlobalDefect
              (HTGeometry.confocalLorentzLift ''
                Set.range (atomicAggregateNode c z)) R) ∧
          HTGeometry.confocalGlobalDefect
              (HTGeometry.confocalLorentzLift ''
                Set.range (atomicAggregateNode c z)) R =
            HTGeometry.confocalGlobalDefect
              (HTGeometry.confocalLorentzLift ''
                Set.range (atomicAggregateNode d w)) R ∧
          HTGeometry.IsGreatestConfocalNullFixedPoint
            (HTGeometry.confocalLorentzLift ''
              Set.range (atomicAggregateNode d w)) R
            (HTGeometry.confocalGlobalDefect
              (HTGeometry.confocalLorentzLift ''
                Set.range (atomicAggregateNode d w)) R) := by
  letI : Nonempty (AtomicAggregateSupport c z) :=
    nonempty_atomicAggregateSupport_of_positive_real_moment hc hboundZ hmomentZ hm0
  letI : Nonempty (AtomicAggregateSupport d w) :=
    nonempty_atomicAggregateSupport_of_positive_real_moment hd hboundW hmomentW hm0'
  have hsel := localPositiveScaleField_selects_maximalConfocalHull
    c z d w m m' hc hd htransZ htransW hM hN hboundZ hboundW hab
    hrealZ hrealW hmomentZ hmomentW hm0 hm0' hobs
  refine ⟨hsel.1, ?_⟩
  have hbz : ∀ u, ‖atomicAggregateNode c z u‖ ≤ M :=
    norm_atomicAggregateNode_le hboundZ
  have hbw : ∀ v, ‖atomicAggregateNode d w v‖ ≤ N :=
    norm_atomicAggregateNode_le hboundW
  apply HTGeometry.eqOn_confocalUpperField_sharedGreatestFixedPoint
    (Set.range_nonempty (atomicAggregateNode c z))
    (Set.range_nonempty (atomicAggregateNode d w)) hM hN
    (by rintro _ ⟨u, rfl⟩; exact hbz u)
    (by rintro _ ⟨v, rfl⟩; exact hbw v)
    (fun R hR => hM.trans_lt ((le_max_left M N).trans_lt hR))
    hsel.2.2.2.1

end

end RHTower
