import GaloisForLFunctions.RHTower.XiGammaSixWoldJordanContinuousNonlinearDescentNoGo

/-!
# Hausdorff multifibre Wold--Jordan descent no-go

Every genuine fixed-left Big--Witt source row converges to the same singular graph vector.  A
continuous reporter into any Hausdorff space therefore forces all prime-labelled output values to
coincide; scalarity, linearity, boundedness, an algebra law, and a fixed readout are unnecessary.

If the output faithfully encodes literal Wold--Jordan energy, prime constancy pulls back through
injectivity.  The existing Gamma-six classification then forces horizontal weight zero and hence
critical-line placement.  A target carrier may vary with each Xi copy, yet existence for every
copy is still exactly RH.

RH chain killed: actual Big--Witt rows -> continuous Hausdorff multifibre reporter -> faithful
energy encoding -> Gamma-six horizontal vanishing -> critical line -> RH.  Only discontinuous,
non-Hausdorff, or energy-nonfaithful output can escape this obstruction.
-/

open Complex Filter Function Set Topology

namespace RHTower.HedenmalmThetaSource

noncomputable section

universe u

/-- Continuous descent of an arbitrary prime-labelled family into a topological target. -/
def PrimeLabelledActualSourceContinuouslyDescendsTo
    (Y : Type u) [TopologicalSpace Y]
    (c : Nat.Primes → Y) : Prop :=
  ∃ reporter : C(DeningerBigWittCrossPairSingularOneLegGraph, Y),
    ∀ a n : ℕ,
      reporter (deningerBigWittCrossPairFiniteOneLegGraphAdmission
        (deningerBigWittWoldFixedLeftRightEdgeNormalizedPacket a n)) =
      c (nthPrimeSubtype a)

/-- **Hausdorff target classification.**  Continuous actual-source descent into any Hausdorff
target exists exactly when the prime-labelled output is constant. -/
theorem primeLabelledActualSourceContinuouslyDescendsTo_iff
    (Y : Type u) [TopologicalSpace Y] [T2Space Y]
    (c : Nat.Primes → Y) :
    PrimeLabelledActualSourceContinuouslyDescendsTo Y c ↔
      ∃ z : Y, ∀ a : ℕ, c (nthPrimeSubtype a) = z := by
  constructor
  · rintro ⟨reporter, hreporter⟩
    have hlimit (a : ℕ) :
        c (nthPrimeSubtype a) =
          reporter deningerBigWittCrossPairOneLegGraphSingularVector := by
      have hreported : Tendsto
          (fun n => reporter
            (deningerBigWittCrossPairFiniteOneLegGraphAdmission
              (deningerBigWittWoldFixedLeftRightEdgeNormalizedPacket a n)))
          atTop
          (nhds (reporter deningerBigWittCrossPairOneLegGraphSingularVector)) :=
        (reporter.continuous.tendsto
          deningerBigWittCrossPairOneLegGraphSingularVector).comp
            (tendsto_deningerBigWittCrossPairFiniteOneLegGraphAdmission_woldFixedLeftRightEdgeNormalizedPacket a)
      have hreported' : Tendsto
          (fun _n : ℕ => c (nthPrimeSubtype a))
          atTop
          (nhds (reporter deningerBigWittCrossPairOneLegGraphSingularVector)) := by
        refine hreported.congr ?_
        intro n
        exact hreporter a n
      exact tendsto_nhds_unique tendsto_const_nhds hreported'
    refine ⟨c (nthPrimeSubtype 0), ?_⟩
    intro a
    exact (hlimit a).trans (hlimit 0).symm
  · rintro ⟨z, hz⟩
    refine ⟨⟨fun _ => z, continuous_const⟩, ?_⟩
    intro a n
    exact (hz a).symm

/-- **Faithful Hausdorff encoded-energy classification.**  For an arbitrary Hausdorff target and
arbitrary injective encoding, continuous descent of literal Wold--Jordan energy at one Xi copy is
exactly critical-line placement.  No topology on the encoding and no algebra on the target are
required. -/
theorem primeLabelledFaithfulT2EncodedWoldJordanDescent_iff_line
    (Y : Type u) [TopologicalSpace Y] [T2Space Y]
    (q : XiZeroCopy) (encode : ℝ → Y) (hencode : Function.Injective encode) :
    PrimeLabelledActualSourceContinuouslyDescendsTo Y (fun p =>
      encode (thetaGammaSixWoldHorizontalCarrier p q ^ (2 : ℕ))) ↔
      (q.1 : ℂ).re = 1 / 2 := by
  constructor
  · intro hdescent
    obtain ⟨z, hz⟩ :=
      (primeLabelledActualSourceContinuouslyDescendsTo_iff Y
        (fun p => encode (thetaGammaSixWoldHorizontalCarrier p q ^ (2 : ℕ)))).1 hdescent
    have hconstant : ∃ z : ℝ, ∀ a : ℕ,
        thetaGammaSixWoldHorizontalCarrier (nthPrimeSubtype a) q ^ (2 : ℕ) = z := by
      refine ⟨thetaGammaSixWoldHorizontalCarrier (nthPrimeSubtype 0) q ^ (2 : ℕ), ?_⟩
      intro a
      apply hencode
      exact (hz a).trans (hz 0).symm
    let cR : Nat.Primes → ℝ := fun p =>
      thetaGammaSixWoldHorizontalCarrier p q ^ (2 : ℕ)
    have hscalar : PrimeLabelledActualSourceContinuouslyDescends cR :=
      (primeLabelledActualSourceContinuouslyDescends_iff cR).2 hconstant
    rcases hscalar with ⟨reporter, hreporter⟩
    have henergy : DeningerBigWittWoldJordanActualSourceContinuousEnergyDescends q := by
      refine ⟨reporter, ?_⟩
      intro a n
      rw [deningerBigWittCrossPairFiniteWoldJordanEnergyReporter_eq]
      exact hreporter a n
    exact
      (deningerBigWittWoldJordanActualSourceContinuousEnergyDescends_iff_line q).1 henergy
  · intro hline
    have hrate : primeDepthBVWoldXiCenteredRate q.1 = 0 :=
      (primeDepthBVWoldXiCenteredRate_eq_zero_iff q.1).2 hline
    apply (primeLabelledActualSourceContinuouslyDescendsTo_iff Y
      (fun p => encode (thetaGammaSixWoldHorizontalCarrier p q ^ (2 : ℕ)))).2
    refine ⟨encode 0, ?_⟩
    intro a
    have hcarrier : thetaGammaSixWoldHorizontalCarrier (nthPrimeSubtype a) q = 0 :=
      (thetaGammaSixWoldHorizontalCarrier_eq_zero_iff (nthPrimeSubtype a) q).2 hrate
    simp [hcarrier]

/-- One faithful Hausdorff multifibre descent witness.  Carrier, topology, encoding, and reporter
may depend on the Xi copy. -/
structure FaithfulT2EncodedWoldJordanDescent (q : XiZeroCopy) where
  Carrier : Type
  topology : TopologicalSpace Carrier
  t2 : @T2Space Carrier topology
  encode : ℝ → Carrier
  encode_injective : Function.Injective encode
  reporter : DeningerBigWittCrossPairSingularOneLegGraph → Carrier
  reporter_continuous : @Continuous
    DeningerBigWittCrossPairSingularOneLegGraph Carrier
    inferInstance topology reporter
  agrees : ∀ a n : ℕ,
    reporter (deningerBigWittCrossPairFiniteOneLegGraphAdmission
      (deningerBigWittWoldFixedLeftRightEdgeNormalizedPacket a n)) =
    encode (thetaGammaSixWoldHorizontalCarrier (nthPrimeSubtype a) q ^ (2 : ℕ))

/-- Existence of any faithful Hausdorff multifibre descent at one Xi copy is exactly critical-line
placement. -/
theorem nonempty_faithfulT2EncodedWoldJordanDescent_iff_line
    (q : XiZeroCopy) :
    Nonempty (FaithfulT2EncodedWoldJordanDescent q) ↔
      (q.1 : ℂ).re = 1 / 2 := by
  constructor
  · rintro ⟨W⟩
    letI : TopologicalSpace W.Carrier := W.topology
    letI : T2Space W.Carrier := W.t2
    let c : Nat.Primes → W.Carrier := fun p =>
      W.encode (thetaGammaSixWoldHorizontalCarrier p q ^ (2 : ℕ))
    have hdescent : PrimeLabelledActualSourceContinuouslyDescendsTo W.Carrier c := by
      refine ⟨⟨W.reporter, W.reporter_continuous⟩, ?_⟩
      intro a n
      exact W.agrees a n
    exact
      (primeLabelledFaithfulT2EncodedWoldJordanDescent_iff_line
        W.Carrier q W.encode W.encode_injective).1 hdescent
  · intro hline
    have hrate : primeDepthBVWoldXiCenteredRate q.1 = 0 :=
      (primeDepthBVWoldXiCenteredRate_eq_zero_iff q.1).2 hline
    refine ⟨{
      Carrier := ℝ
      topology := inferInstance
      t2 := inferInstance
      encode := id
      encode_injective := fun _ _ h => h
      reporter := fun _ => 0
      reporter_continuous := continuous_const
      agrees := ?_ }⟩
    intro a n
    have hcarrier : thetaGammaSixWoldHorizontalCarrier (nthPrimeSubtype a) q = 0 :=
      (thetaGammaSixWoldHorizontalCarrier_eq_zero_iff (nthPrimeSubtype a) q).2 hrate
    simp [hcarrier]

/-- **[L HAUSDORFF MULTIFIBRE ROUTE-CLASS KILL].**  Allowing a different faithful Hausdorff
operator/multifibre carrier at every Xi copy does not weaken the descent burden: global existence
is exactly RH. -/
theorem everyFaithfulT2EncodedWoldJordanDescent_iff_riemannHypothesis :
    (∀ q : XiZeroCopy, Nonempty (FaithfulT2EncodedWoldJordanDescent q)) ↔
      RiemannHypothesis := by
  constructor
  · intro h
    rw [← everyDeningerBigWittWoldJordanActualSourceContinuousEnergyDescends_iff_riemannHypothesis]
    intro q
    exact
      (deningerBigWittWoldJordanActualSourceContinuousEnergyDescends_iff_line q).2
        ((nonempty_faithfulT2EncodedWoldJordanDescent_iff_line q).1 (h q))
  · intro h q
    have hscalar : DeningerBigWittWoldJordanActualSourceContinuousEnergyDescends q :=
      (everyDeningerBigWittWoldJordanActualSourceContinuousEnergyDescends_iff_riemannHypothesis).2 h q
    exact
      (nonempty_faithfulT2EncodedWoldJordanDescent_iff_line q).2
        ((deningerBigWittWoldJordanActualSourceContinuousEnergyDescends_iff_line q).1 hscalar)

end

end RHTower.HedenmalmThetaSource
