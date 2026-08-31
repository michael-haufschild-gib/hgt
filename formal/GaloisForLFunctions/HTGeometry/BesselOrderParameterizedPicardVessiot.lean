import GaloisForLFunctions.HTGeometry.BesselOrderDifferentialClosureObstruction
import GaloisForLFunctions.HTGeometry.ParameterizedPicardVessiotSystem
import GaloisForLFunctions.HTGeometry.ParameterizedPicardVessiotGeneration
import GaloisForLFunctions.HTGeometry.RatFuncShiftDerivationCommute

/-!
# Parameterized Picard--Vessiot existence for the concrete Bessel order system

The coefficient field, its differential closure, the physical Bessel slope, the coordinate
derivation, the shift automorphism, the inverse companion matrix, and their compatibility are all
constructed in the corpus.  Consequently the parameterized Picard--Vessiot quotient for the actual
Bessel order companion exists without retaining any of those objects as hypotheses.
-/

namespace GaloisForLFunctions.HTGeometry.BesselDifferentialClosure

noncomputable section

open GaloisForLFunctions.HTGeometry

local instance besselOrderParameterizedPicardVessiotLocalInst1 : Differential (RatFunc Constants) := coordinateTotalDifferential

/-- Explicit inverse of the concrete Bessel order companion. -/
def besselOrderCompanionInverse (s : ℝ) : Matrix (Fin 2) (Fin 2) (RatFunc Constants) :=
  !![-FieldShift.orderShiftCoeff (slope s), 1; 1, 0]

theorem besselOrderCompanion_mul_inverse (s : ℝ) :
    FieldShift.besselOrderCompanion (slope s) * besselOrderCompanionInverse s = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [FieldShift.besselOrderCompanion, besselOrderCompanionInverse,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem besselOrderCompanion_inverse_mul (s : ℝ) :
    besselOrderCompanionInverse s * FieldShift.besselOrderCompanion (slope s) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [FieldShift.besselOrderCompanion, besselOrderCompanionInverse,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- The concrete rational-coordinate shift commutes with the concrete total derivation. -/
theorem besselRatShift_commutes (a : RatFunc Constants) :
    FieldShift.ratShiftEquiv (Differential.deriv a) =
      Differential.deriv (FieldShift.ratShiftEquiv a) := by
  exact ratShift_coordinateTotalDerivation a

/-- The difference automorphism on the differential coordinate ring of the concrete Bessel
system.  All compatibility and invertibility proofs are fixed by the preceding declarations. -/
def besselOrderPPVSigma (s : ℝ) :
    ppvLocalization (RatFunc Constants) 2 ≃+* ppvLocalization (RatFunc Constants) 2 :=
  ppvSigma FieldShift.ratShiftEquiv besselRatShift_commutes
    (FieldShift.besselOrderCompanion (slope s)) (besselOrderCompanionInverse s)
    (besselOrderCompanion_mul_inverse s) (besselOrderCompanion_inverse_mul s)

/-- The concrete parameterized difference action restricts to rational-coordinate shift. -/
theorem besselOrderPPVSigma_base (s : ℝ) (x : RatFunc Constants) :
    besselOrderPPVSigma s (ppvBaseMap (RatFunc Constants) 2 x) =
      ppvBaseMap (RatFunc Constants) 2 (FieldShift.ratShiftEquiv x) := by
  unfold besselOrderPPVSigma
  exact ppvSigma_ppvBaseMap (K := RatFunc Constants) (n := 2)
    FieldShift.ratShiftEquiv besselRatShift_commutes
    (FieldShift.besselOrderCompanion (slope s)) (besselOrderCompanionInverse s)
    (besselOrderCompanion_mul_inverse s) (besselOrderCompanion_inverse_mul s) x

/-- A complete parameterized Picard--Vessiot quotient for the concrete Bessel order companion. -/
structure BesselOrderParameterizedPVData (s : ℝ) where
  M : Ideal (ppvLocalization (RatFunc Constants) 2)
  isSigmaDeltaIdeal : IsSigmaDeltaIdeal (besselOrderPPVSigma s) M
  ne_top : M ≠ ⊤
  isSigmaIdeal_symm : IsSigmaIdeal (besselOrderPPVSigma s).symm M
  isSigmaDeltaSimple :
    @IsSigmaDeltaSimple ((ppvLocalization (RatFunc Constants) 2) ⧸ M) _
      (quotientDifferential M isSigmaDeltaIdeal.2)
      (sigmaQuotientEquiv (besselOrderPPVSigma s) M
        isSigmaDeltaIdeal.1 isSigmaIdeal_symm)
  commutesDeriv :
    @CommutesDeriv ((ppvLocalization (RatFunc Constants) 2) ⧸ M) _
      (quotientDifferential M isSigmaDeltaIdeal.2)
      (sigmaQuotientEquiv (besselOrderPPVSigma s) M
        isSigmaDeltaIdeal.1 isSigmaIdeal_symm)
  baseCompatible : ∀ x : RatFunc Constants,
    sigmaQuotientEquiv (besselOrderPPVSigma s) M
        isSigmaDeltaIdeal.1 isSigmaIdeal_symm
        (Ideal.Quotient.mk M (ppvBaseMap (RatFunc Constants) 2 x)) =
      Ideal.Quotient.mk M
        (ppvBaseMap (RatFunc Constants) 2 (FieldShift.ratShiftEquiv x))
  baseDerivCompatible : ∀ x : RatFunc Constants,
    letI : Differential ((ppvLocalization (RatFunc Constants) 2) ⧸ M) :=
      quotientDifferential M isSigmaDeltaIdeal.2
    Differential.deriv
        (Ideal.Quotient.mk M (ppvBaseMap (RatFunc Constants) 2 x)) =
      Ideal.Quotient.mk M
        (ppvBaseMap (RatFunc Constants) 2 (Differential.deriv x))
  fundamental : ∀ i j,
    sigmaQuotientEquiv (besselOrderPPVSigma s) M
        isSigmaDeltaIdeal.1 isSigmaIdeal_symm
        (Ideal.Quotient.mk M (ppvFundamental (RatFunc Constants) 2 i j)) =
      ((((FieldShift.besselOrderCompanion (slope s)).map
          (ppvBaseMap (RatFunc Constants) 2)).map (Ideal.Quotient.mk M)) *
        ((ppvFundamental (RatFunc Constants) 2).map (Ideal.Quotient.mk M))) i j
  fundamental_det_isUnit :
    IsUnit ((ppvFundamental (RatFunc Constants) 2).map (Ideal.Quotient.mk M)).det
  detInverse : (ppvLocalization (RatFunc Constants) 2) ⧸ M
  fundamental_det_mul_inverse :
    ((ppvFundamental (RatFunc Constants) 2).map (Ideal.Quotient.mk M)).det * detInverse = 1
  generatedJets : Algebra.adjoin (RatFunc Constants)
    (Set.range (fun q : (Fin 2 × Fin 2) × ℕ =>
      Ideal.Quotient.mk M
        (algebraMap (DifferentialPolynomial (Fin 2 × Fin 2) (RatFunc Constants))
          (ppvLocalization (RatFunc Constants) 2) (MvPolynomial.X q))) ∪
      {detInverse}) = ⊤
  jets_are_iteratedDeriv : ∀ i j k,
    letI : Differential ((ppvLocalization (RatFunc Constants) 2) ⧸ M) :=
      quotientDifferential M isSigmaDeltaIdeal.2
    (Differential.deriv^[k])
        (Ideal.Quotient.mk M (ppvFundamental (RatFunc Constants) 2 i j)) =
      Ideal.Quotient.mk M
        (algebraMap (DifferentialPolynomial (Fin 2 × Fin 2) (RatFunc Constants))
          (ppvLocalization (RatFunc Constants) 2) (MvPolynomial.X ((i, j), k)))

/-- Parameterized Picard--Vessiot existence for every concrete Bessel slope.  No base field,
differential closure, commutation, invertibility, simplicity, or fundamental-solution premise is
retained. -/
theorem besselOrder_parameterizedPicardVessiot_exists :
    ∀ s : ℝ, Nonempty (BesselOrderParameterizedPVData s) := by
  intro s
  obtain ⟨M, hM, hMne, hM', hsimple, hcomm, hfund, hdet⟩ :=
    exists_parameterizedPicardVessiot_system
      FieldShift.ratShiftEquiv besselRatShift_commutes
      (FieldShift.besselOrderCompanion (slope s)) (besselOrderCompanionInverse s)
      (besselOrderCompanion_mul_inverse s) (besselOrderCompanion_inverse_mul s)
  have hbase : ∀ x : RatFunc Constants,
      sigmaQuotientEquiv (besselOrderPPVSigma s) M hM.1 hM'
          (Ideal.Quotient.mk M (ppvBaseMap (RatFunc Constants) 2 x)) =
        Ideal.Quotient.mk M
          (ppvBaseMap (RatFunc Constants) 2 (FieldShift.ratShiftEquiv x)) := by
    intro x
    rw [sigmaQuotientEquiv_mk, besselOrderPPVSigma_base]
  have hbaseDeriv : ∀ x : RatFunc Constants,
      letI : Differential ((ppvLocalization (RatFunc Constants) 2) ⧸ M) :=
        quotientDifferential M hM.2
      Differential.deriv
          (Ideal.Quotient.mk M (ppvBaseMap (RatFunc Constants) 2 x)) =
        Ideal.Quotient.mk M
          (ppvBaseMap (RatFunc Constants) 2 (Differential.deriv x)) := by
    intro x
    exact quotientDifferential_ppvBaseMap_deriv M hM.2 x
  exact ⟨{
    M := M
    isSigmaDeltaIdeal := hM
    ne_top := hMne
    isSigmaIdeal_symm := hM'
    isSigmaDeltaSimple := hsimple
    commutesDeriv := hcomm
    baseCompatible := hbase
    baseDerivCompatible := hbaseDeriv
    fundamental := hfund
    fundamental_det_isUnit := hdet
    detInverse := Ideal.Quotient.mk M
      (IsLocalization.Away.invSelf
        ((jetFundamentalMatrix (RatFunc Constants) 2).det))
    fundamental_det_mul_inverse := ppvQuotient_det_mul_inverse M
    generatedJets := ppvQuotient_adjoin_jetVariables M
    jets_are_iteratedDeriv := iterate_deriv_ppvQuotientFundamental M hM.2
  }⟩

end

end GaloisForLFunctions.HTGeometry.BesselDifferentialClosure
