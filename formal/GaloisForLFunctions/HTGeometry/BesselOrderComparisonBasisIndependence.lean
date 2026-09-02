import GaloisForLFunctions.HTGeometry.BesselOrderPPVNoNewConstantsReduced
import GaloisForLFunctions.HTGeometry.SigmaDeltaNoNewConstantsTotalFraction
import GaloisForLFunctions.HTGeometry.SigmaConstantsComponentTensorIndependence

/-!
# Unconditional comparison-basis independence for the Bessel PPV ring

Every constant-field basis of the Bessel comparison-jet algebra is linearly independent over the
entire reduced parameterized Picard--Vessiot ring.  The proof establishes independence on every
minimal prime component using the total-fraction no-new-constants theorem, then descends through
the zero intersection of those components.
-/

namespace GaloisForLFunctions.HTGeometry.BesselDifferentialClosure

open GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped Differential TensorProduct

noncomputable section

local instance besselOrderComparisonBasisBaseDifferential :
    Differential (RatFunc Constants) := coordinateTotalDifferential

local instance besselOrderComparisonBasisConstantsRatDifferentialAlgebra :
    DifferentialAlgebra Constants (RatFunc Constants) :=
  coordinateTotalDifferentialAlgebra

local instance besselOrderComparisonBasisPPVDifferential {s : ℝ}
    (data : BesselOrderParameterizedPVData s) : Differential data.PPVRing :=
  quotientDifferential data.M data.isSigmaDeltaIdeal.2

local instance besselOrderComparisonBasisPPVDifferentialAlgebra {s : ℝ}
    (data : BesselOrderParameterizedPVData s) :
    DifferentialAlgebra (RatFunc Constants) data.PPVRing :=
  ppvQuotientDifferentialAlgebra data.M data.isSigmaDeltaIdeal.2

local instance besselOrderComparisonBasisConstantsPPVDifferentialAlgebra {s : ℝ}
    (data : BesselOrderParameterizedPVData s) :
    DifferentialAlgebra Constants data.PPVRing :=
  differentialAlgebra_trans (C := Constants) (K := RatFunc Constants) (E := data.PPVRing)

local instance besselOrderComparisonBasisPPVReduced {s : ℝ}
    (data : BesselOrderParameterizedPVData s) : IsReduced data.PPVRing := data.isReduced

local instance besselOrderComparisonBasisRatCharZero : CharZero (RatFunc Constants) :=
  charZero_of_injective_ringHom (algebraMap ℚ (RatFunc Constants)).injective

private theorem fixed_pow {R : Type*} [CommRing R] (σ : R ≃+* R)
    {x : R} (hx : σ x = x) (n : ℕ) : (σ ^ n) x = x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ']; change σ ((σ ^ n) x) = x; rw [ih, hx]

/-- A comparison-jet basis is independent over the full Bessel PPV ring. -/
theorem BesselOrderParameterizedPVData.comparisonBasis_linearIndependent
    {s : ℝ} (data : BesselOrderParameterizedPVData s)
    (comparison : data.ComparisonJetData) {ι : Type}
    (basis : Module.Basis ι Constants
      (comparisonJetAlgebra (C := Constants) comparison.Z comparison.w)) :
    LinearIndependent data.PPVRing
      (fun i => ((basis i : comparisonJetAlgebra
        (C := Constants) comparison.Z comparison.w) : data.TensorSquare)) := by
  classical
  letI : Nontrivial data.PPVRing := by
    rw [← not_subsingleton_iff_nontrivial, Ideal.Quotient.subsingleton_iff]
    exact data.ne_top
  obtain ⟨S, hSne, hSmin, hSbot⟩ :=
    exists_finite_minimalPrimeDifferential_inf_eq_bot_of_diffFG
      data.diffGenerators data.diffGenerators_surjective
  have htrans : ∀ P ∈ S, ∀ Q ∈ S, ∃ n : ℕ,
      Ideal.map ((((data.sigmaEquiv ^ n) : data.PPVRing ≃+* data.PPVRing)) :
        data.PPVRing →+* data.PPVRing) P = Q := by
    intro P hPS Q hQS
    obtain ⟨n, hn⟩ := exists_iterate_map_eq_of_isSigmaDeltaSimple
      data.sigmaEquiv data.commutesDeriv data.isSigmaDeltaSimple
      S hSmin hSbot hPS hQS
    refine ⟨n, ?_⟩
    rw [ideal_map_pow_eq_iterate]
    exact hn
  have hcomponent : ∀ P ∈ S,
      let D := data.PPVRing ⧸ P
      LinearIndependent D (fun i => leftComponentTensorMap
        (K := RatFunc Constants) P
        ((basis i : comparisonJetAlgebra
          (C := Constants) comparison.Z comparison.w) : data.TensorSquare)) := by
    intro P hPS
    letI : P.IsPrime := (hSmin P hPS).1
    let D := data.PPVRing ⧸ P
    obtain ⟨period, hperiodPos, hPσ, hPσsymm, hPsimple⟩ :=
      exists_period_componentQuotient_isSigmaDeltaSimple
        data.sigmaEquiv data.commutesDeriv data.isSigmaDeltaSimple
        S hSmin hSbot P hPS
    letI : Differential D := quotientDifferential P (hSmin P hPS).2.1
    letI : IsDomain D := Ideal.Quotient.isDomain P
    letI : DifferentialAlgebra (RatFunc Constants) D := by
      constructor
      intro a
      change Differential.deriv
          (Ideal.Quotient.mk P (algebraMap (RatFunc Constants) data.PPVRing a)) =
        Ideal.Quotient.mk P
          (algebraMap (RatFunc Constants) data.PPVRing (Differential.deriv a))
      rw [quotientDifferential_deriv_mk]
      exact congrArg (Ideal.Quotient.mk P)
        (DifferentialAlgebra.deriv_algebraMap a)
    letI : DifferentialAlgebra Constants D :=
      differentialAlgebra_trans
        (C := Constants) (K := RatFunc Constants) (E := D)
    let τK : RatFunc Constants ≃+* RatFunc Constants :=
      FieldShift.ratShiftEquiv ^ period
    let τR : data.PPVRing ≃+* data.PPVRing := data.sigmaEquiv ^ period
    let τD : D ≃+* D := sigmaQuotientEquiv τR P hPσ hPσsymm
    have hτcomm : CommutesDeriv τD :=
      quotientDifferential_commutesDeriv
        (commutesDeriv_pow data.sigmaEquiv data.commutesDeriv period) P
        ⟨hPσ, (hSmin P hPS).2.1⟩ hPσsymm
    have hτRbase (a : RatFunc Constants) :
        τR (algebraMap (RatFunc Constants) data.PPVRing a) =
          algebraMap (RatFunc Constants) data.PPVRing (τK a) :=
      data.baseCompatible_pow period a
    have hτDbase (a : RatFunc Constants) :
        τD (algebraMap (RatFunc Constants) D a) =
          algebraMap (RatFunc Constants) D (τK a) := by
      change τD (Ideal.Quotient.mk P
          (algebraMap (RatFunc Constants) data.PPVRing a)) = _
      rw [sigmaQuotientEquiv_mk, hτRbase]
      rfl
    have hbaseConst (c : Constants) :
        τK (algebraMap Constants (RatFunc Constants) c) =
          algebraMap Constants (RatFunc Constants) c := by
      apply fixed_pow FieldShift.ratShiftEquiv
      rw [FieldShift.ratShiftEquiv_apply, FieldShift.ratShift_const]
    have hbaseFix (a : RatFunc Constants) (ha : τK a = a) :
        ∃ c : Constants, algebraMap Constants (RatFunc Constants) c = a := by
      obtain ⟨c, hc⟩ :=
        FieldShift.ratShiftEquiv_pow_fixed_eq_const hperiodPos ha
      exact ⟨c, hc.symm⟩
    have hyP := data.component_diffGenerators_surjective P (hSmin P hPS).2.1
    have hfrac : ∀ x : FractionRing D, fractionRingEquiv τD x = x →
        ∃ c : Constants, x = algebraMap Constants (FractionRing D) c := by
      intro x hx
      exact exists_eq_algebraMap_fractionRing_of_isSigmaDeltaSimple_of_diffFG
        (C := Constants) (K := RatFunc Constants) (R := D)
        τK τD hτcomm hτDbase hbaseConst hbaseFix hPsimple
        (fun i => Ideal.Quotient.mk P (data.diffGenerators i)) hyP hx
    let E := comparisonJetAlgebra (C := Constants) comparison.Z comparison.w
    have hCindep : LinearIndependent Constants
        (fun i => ((basis i : E) : data.TensorSquare)) := by
      exact linearIndependent_subalgebraBasis_coe_tensorProduct E basis
    exact linearIndependent_leftComponentTensorMap_of_fraction_fixed
      FieldShift.ratShiftEquiv data.sigmaEquiv data.baseCompatible
      (fun c => by
        rw [IsScalarTower.algebraMap_apply Constants (RatFunc Constants) data.PPVRing]
        calc
          data.sigmaEquiv (algebraMap (RatFunc Constants) data.PPVRing
              (algebraMap Constants (RatFunc Constants) c)) =
              algebraMap (RatFunc Constants) data.PPVRing
                (FieldShift.ratShiftEquiv
                  (algebraMap Constants (RatFunc Constants) c)) := by
            simpa using data.baseCompatible_pow 1
              (algebraMap Constants (RatFunc Constants) c)
          _ = algebraMap (RatFunc Constants) data.PPVRing
              (algebraMap Constants (RatFunc Constants) c) := by
            congr 1
            rw [FieldShift.ratShiftEquiv_apply, FieldShift.ratShift_const])
      S (fun Q hQS => (hSmin Q hQS).1) hSbot htrans P hPS period
      hPσ hPσsymm hfrac
      (fun i => ((basis i : E) : data.TensorSquare))
      (fun i => comparison.fixed (basis i) (basis i).2) hCindep
  exact linearIndependent_of_leftComponentTensorMap S hSbot
    (fun i => ((basis i : comparisonJetAlgebra
      (C := Constants) comparison.Z comparison.w) : data.TensorSquare)) hcomponent

end

end GaloisForLFunctions.HTGeometry.BesselDifferentialClosure
