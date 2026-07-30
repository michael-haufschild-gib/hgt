import GaloisForLFunctions.RHTower.PrimeCoherenceRelationIdealCircuitUniversalityLaw
import GaloisForLFunctions.HTGeometry.FiniteShadowCapacity
import GaloisForLFunctions.RHTower.ContinuumPrimeFiniteTailExtensionRelationCircuitUniversalityLaw
import GaloisForLFunctions.HTGeometry.ContinuumAnalyticEulerTailExactFaithfulnessUniversalityLaw

/-!
# Continuum-prime finite-observation master universality

One sparse coherent continuum-prime embedding can be observed through three exact interfaces:
arbitrary finite constant linear frames, arbitrary finite tail-linear extensions, and every
analytic Euler all-jet realization.  The same witness has exact row-rank relation ideals, exact
displayed affine pivot relations with no enlarged differential field, and injective linearly
independent analytic images.
-/

open scoped Differential

namespace RHTower

noncomputable section

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry
open Matrix

/-- Complete finite and analytic observation certificate for one sparse continuum-prime
embedding. -/
structure ContinuumPrimeFiniteObservationMasterCertificate
    (e : PrefixFunctionCoordinate ↪ Nat.Primes) : Prop where
  finiteLinearFrameRank :
    ∀ {m n : Type*} [Fintype m] [Fintype n]
      [DecidableEq m] [DecidableEq n]
      (coord : n → (ℕ → Bool) × ℕ)
      (M : Matrix m n finitePrimeRationalCoefficientField),
      Function.Injective coord →
      (∀ i j,
        (algebraMap finitePrimeRationalCoefficientField
          arithmeticFunctionRationalCoordinateField (M i j))′ = 0) →
      (differentialRelationIdeal
          (C := finitePrimeRationalCoefficientField)
          (matrixLinearForms M
            (fun i =>
              signedPrimeNaturalShiftPalette
                (continuumSparsePrimeOrientation (fun _ => false) e (coord i).1)
                (coord i).2)) = ⊥ ↔
        LinearIndependent finitePrimeRationalCoefficientField M.row)
  finiteTailExtensionSourceRigidity :
    differentialRelationIdeal
        (C := finitePrimeRationalCoefficientField)
        (fun xa : (ℕ → Bool) × ℕ =>
          signedPrimeNaturalShiftPalette
            (continuumSparsePrimeOrientation (fun _ => false) e xa.1) xa.2) = ⊥ ∧
    (∀ {B R A : Type*} [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype A] [DecidableEq A] [Nonempty A]
      (code : B → ℕ → Bool) (hcode : Function.Injective code)
      (dependent : R → Nat.Primes → ℂ) (coefficient : R → B → ℂ)
      (hresidual : ∀ r,
        {p | dependent r p -
          ∑ b, coefficient r b *
            primeDirichletSign
              (continuumSparsePrimeOrientation (fun _ => false) e (code b) p) ≠ 0}.Finite)
      (alpha : A → ℂ)
      (_hdistinct : Function.Injective (fun a => (alpha a).re)),
      let P := coherentPrimeTailPivotPresentation (fun _ => false) e code hcode
        dependent coefficient hresidual
      (∀ ba, P.pivotPalette alpha ba =
        signedPrimeShiftCarrier
          (continuumSparsePrimeOrientation (fun _ => false) e (code ba.1)) (alpha ba.2)) ∧
      differentialRelationIdeal
          (C := finitePrimeRationalCoefficientField)
          (Sum.elim (P.pivotPalette alpha) (P.dependentPalette alpha)) =
        differentialPivotRelationIdeal P.paletteMatrix (P.baseCorrection alpha) ∧
      DifferentialIndependent finitePrimeRationalCoefficientField
        (P.pivotPalette alpha) ∧
      differentialAdjoin finitePrimeRationalCoefficientField
          (Set.range (Sum.elim (P.pivotPalette alpha) (P.dependentPalette alpha))) =
        differentialAdjoin finitePrimeRationalCoefficientField
          (Set.range (P.pivotPalette alpha)) ∧
      Fintype.card (B × A) = Fintype.card A * Fintype.card B) ∧
    (∀ z (Atom : arithmeticFunctionRationalCoordinateField → Prop),
      FiniteDifferentialCircuit Atom
        (signedPrimeNaturalShiftPalette
          (continuumSparsePrimeOrientation (fun _ => false) e z) 0) →
      ∃ a : arithmeticFunctionRationalCoordinateField,
        Atom a ∧ HypertranscendentalOver ℂ a) ∧
    ∀ z (h : arithmeticFunctionRationalCoordinateField)
      (P : Polynomial (differentialAdjoin ℂ
        ({h} : Set arithmeticFunctionRationalCoordinateField))),
      (signedPrimeNaturalShiftPalette
          (continuumSparsePrimeOrientation (fun _ => false) e z) 0)′ =
        Polynomial.eval₂
          (algebraMap
            (differentialAdjoin ℂ
              ({h} : Set arithmeticFunctionRationalCoordinateField))
            arithmeticFunctionRationalCoordinateField)
          (signedPrimeNaturalShiftPalette
            (continuumSparsePrimeOrientation (fun _ => false) e z) 0) P →
      HypertranscendentalOver ℂ h
  analyticEulerTailExactFaithfulness :
    LinearIndependent ℂ
        (fun z : ℕ → Bool =>
          boundedPrimeOrientationTailClass
            (continuumSparsePrimeOrientation (fun _ => false) e z)) ∧
      Cardinal.continuum ≤ Module.rank ℂ BoundedPrimeTailSpace ∧
      ∀ a : ℂ,
        Function.Injective (analyticEulerTailAllJetRealization a) ∧
        LinearIndependent ℂ
          (fun z : ℕ → Bool =>
            analyticEulerTailAllJetRealization a
              (boundedPrimeOrientationTailClass
                (continuumSparsePrimeOrientation (fun _ => false) e z)))

/-- **Continuum-prime finite-observation master universality law.** Every positive coherence
neighborhood contains one continuum palette simultaneously complete for all finite constant
linear frames, all finite tail-linear extensions, and all analytic Euler all-jet observations. -/
theorem exists_orderPointedContinuumPrime_finiteObservationMasterUniversality
    (sigma eta x : ℝ) (hsigma : 0 < sigma) (heta : 0 < eta) (hx : 1 < x) :
    ∃ e : PrefixFunctionCoordinate ↪ Nat.Primes,
      ContinuumPrimeFiniteObservationMasterCertificate e := by
  obtain ⟨e, _, hdiff, _⟩ :=
    exists_orderPointedContinuumPrimeRelationIdealCircuitUniversality
      sigma eta x hsigma heta hx
  refine ⟨e, {
    finiteLinearFrameRank := ?_
    finiteTailExtensionSourceRigidity :=
      continuumPrime_completeFiniteTailExtension_sourceRigidity
        (fun _ => false) e
    analyticEulerTailExactFaithfulness :=
      continuumPrime_analyticEulerTailExactFaithfulnessUniversality
        (fun _ => false) e }⟩
  intro m n _ _ _ _ coord M hcoord hMconst
  let family :
      ((ℕ → Bool) × ℕ) → arithmeticFunctionRationalCoordinateField :=
    fun xa =>
      signedPrimeNaturalShiftPalette
        (continuumSparsePrimeOrientation (fun _ => false) e xa.1) xa.2
  have hselected :
      DifferentialIndependent finitePrimeRationalCoefficientField
        (fun i => family (coord i)) := by
    simpa only [Function.comp_apply] using! hdiff.comp coord hcoord
  calc
    differentialRelationIdeal
          (C := finitePrimeRationalCoefficientField)
          (matrixLinearForms M
            (fun i =>
              signedPrimeNaturalShiftPalette
                (continuumSparsePrimeOrientation (fun _ => false) e (coord i).1)
                (coord i).2)) = ⊥ ↔
        DifferentialIndependent finitePrimeRationalCoefficientField
          (matrixLinearForms M (fun i => family (coord i))) := by
            simpa only [family] using
              (differentialIndependent_iff_relationIdeal_eq_bot
                (C := finitePrimeRationalCoefficientField)
                (matrixLinearForms M (fun i => family (coord i)))).symm
    _ ↔ LinearIndependent finitePrimeRationalCoefficientField M.row :=
      differentialIndependent_matrixLinearForms_iff_rowIndependent
        M hMconst (fun i => family (coord i)) hselected

end

end RHTower
