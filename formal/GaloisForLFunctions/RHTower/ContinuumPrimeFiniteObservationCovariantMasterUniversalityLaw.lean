import GaloisForLFunctions.RHTower.ContinuumPrimeFiniteObservationMasterUniversalityLaw
import GaloisForLFunctions.RHTower.ClosedConstraintPrimeTailPivotLinearCovarianceUniversalityLaw

/-!
# Continuum-prime finite-observation covariant master universality

The continuum-prime master palette remains complete after every invertible
entrywise-differential-constant change of all coordinates in each finite
tail-pivot chart.
-/

open scoped Differential

namespace RHTower

noncomputable section

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry
open Matrix MvPolynomial

/-- Every finite tail-pivot chart drawn from a coherent continuum palette has
its complete relation ideal transported contravariantly by an invertible
entrywise-differential-constant linear coordinate change. -/
theorem coherentPrimeTailPivot_linearCovariantCompleteRelation
    {B R A : Type*}
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype R] [DecidableEq R]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (base : Nat.Primes → Bool)
    (e : PrefixFunctionCoordinate ↪ Nat.Primes)
    (code : B → ℕ → Bool) (hcode : Function.Injective code)
    (dependent : R → Nat.Primes → ℂ) (coefficient : R → B → ℂ)
    (hresidual : ∀ r,
      {p | dependent r p -
        ∑ b, coefficient r b *
          primeDirichletSign
            (continuumSparsePrimeOrientation base e (code b) p) ≠ 0}.Finite)
    (alpha : A → ℂ)
    (hdistinct : Function.Injective (fun a => (alpha a).re))
    (M N : Matrix ((B × A) ⊕ (R × A)) ((B × A) ⊕ (R × A))
      finitePrimeRationalCoefficientField)
    (hMconst : ∀ i j,
      (algebraMap finitePrimeRationalCoefficientField
        arithmeticFunctionRationalCoordinateField (M i j))′ = 0)
    (hMN : M * N = 1) (hNM : N * M = 1)
    (Q : DifferentialPolynomial ((B × A) ⊕ (R × A))
      finitePrimeRationalCoefficientField) :
    let P := coherentPrimeTailPivotPresentation base e code hcode
      dependent coefficient hresidual
    Q ∈ differentialRelationIdeal
        (matrixLinearForms M
          (Sum.elim (P.pivotPalette alpha) (P.dependentPalette alpha))) ↔
      differentialJetLinearChangeAlgEquiv M N hMN hNM Q ∈
        differentialPivotRelationIdeal P.paletteMatrix
          (P.baseCorrection alpha) := by
  classical
  let P := coherentPrimeTailPivotPresentation base e code hcode
    dependent coefficient hresidual
  dsimp only
  rw [mem_differentialRelationIdeal_linearChange_of_coefficients_constant_iff
    M N hMconst hMN hNM
    (Sum.elim (P.pivotPalette alpha) (P.dependentPalette alpha)) Q]
  rw [(coherentPrimeTailPivot_completeFiniteExtension base e code hcode
    dependent coefficient hresidual alpha hdistinct).2.1]

/-- Finite/analytic observation master certificate augmented by exact
coordinate covariance for every finite tail-pivot chart. -/
structure ContinuumPrimeFiniteObservationCovariantMasterCertificate
    (e : PrefixFunctionCoordinate ↪ Nat.Primes) : Prop
    extends ContinuumPrimeFiniteObservationMasterCertificate e where
  finiteTailExtensionLinearCovariance :
    ∀ {B R A : Type*}
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype R] [DecidableEq R]
      [Fintype A] [DecidableEq A] [Nonempty A]
      (code : B → ℕ → Bool) (hcode : Function.Injective code)
      (dependent : R → Nat.Primes → ℂ) (coefficient : R → B → ℂ)
      (hresidual : ∀ r,
        {p | dependent r p -
          ∑ b, coefficient r b *
            primeDirichletSign
              (continuumSparsePrimeOrientation (fun _ => false) e (code b) p) ≠ 0}.Finite)
      (alpha : A → ℂ)
      (_hdistinct : Function.Injective (fun a => (alpha a).re))
      (M N : Matrix ((B × A) ⊕ (R × A)) ((B × A) ⊕ (R × A))
        finitePrimeRationalCoefficientField)
      (_hMconst : ∀ i j,
        (algebraMap finitePrimeRationalCoefficientField
          arithmeticFunctionRationalCoordinateField (M i j))′ = 0)
      (hMN : M * N = 1) (hNM : N * M = 1)
      (Q : DifferentialPolynomial ((B × A) ⊕ (R × A))
        finitePrimeRationalCoefficientField),
      let P := coherentPrimeTailPivotPresentation (fun _ => false) e code hcode
        dependent coefficient hresidual
      Q ∈ differentialRelationIdeal
          (matrixLinearForms M
            (Sum.elim (P.pivotPalette alpha) (P.dependentPalette alpha))) ↔
        differentialJetLinearChangeAlgEquiv M N hMN hNM Q ∈
          differentialPivotRelationIdeal P.paletteMatrix
            (P.baseCorrection alpha)

/-- **Covariant continuum-prime finite-observation master law.** Every
positive coherence neighborhood contains one continuum palette simultaneously
complete under finite frames, finite tail extensions, their invertible
constant coordinate changes, and analytic Euler all-jet observation. -/
theorem exists_orderPointedContinuumPrime_finiteObservationCovariantMasterUniversality
    (sigma eta x : ℝ) (hsigma : 0 < sigma) (heta : 0 < eta) (hx : 1 < x) :
    ∃ e : PrefixFunctionCoordinate ↪ Nat.Primes,
      ContinuumPrimeFiniteObservationCovariantMasterCertificate e := by
  obtain ⟨e, hmaster⟩ :=
    exists_orderPointedContinuumPrime_finiteObservationMasterUniversality
      sigma eta x hsigma heta hx
  refine ⟨e, {
    toContinuumPrimeFiniteObservationMasterCertificate := hmaster
    finiteTailExtensionLinearCovariance := ?_ }⟩
  intro B R A _ _ _ _ _ _ _ _ code hcode dependent coefficient hresidual
    alpha hdistinct M N hMconst hMN hNM Q
  exact coherentPrimeTailPivot_linearCovariantCompleteRelation
    (fun _ => false) e code hcode dependent coefficient hresidual
      alpha hdistinct M N hMconst hMN hNM Q

end

end RHTower
