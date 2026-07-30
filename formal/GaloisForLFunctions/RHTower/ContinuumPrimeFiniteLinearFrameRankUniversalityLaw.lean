import GaloisForLFunctions.RHTower.PrimeCoherenceRelationIdealCircuitUniversalityLaw
import GaloisForLFunctions.HTGeometry.FiniteShadowCapacity

/-!
# Continuum prime finite linear-frame rank universality

The relation-free continuum sparse-prime palette remains completely classifiable after every
injectively selected finite coordinate frame and every finite rectangular observation matrix
whose displayed entries are differential constants.  The transformed complete differential
relation ideal is trivial exactly at full row rank.
-/

open scoped Differential

namespace RHTower

noncomputable section

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry
open Matrix

/-- **Continuum-prime finite linear-frame rank universality.**  Every positive coherence
neighborhood supplies one continuum prime palette such that all injectively selected finite
subfamilies obey the exact rectangular observation law: their linearly transformed complete
differential relation ideal is bottom if and only if the observation rows are linearly
independent. -/
theorem
    exists_orderPointedContinuumPrime_finiteLinearFrameRelationRankUniversality
    (sigma eta x : ℝ) (hsigma : 0 < sigma) (heta : 0 < eta) (hx : 1 < x) :
    ∃ e : PrefixFunctionCoordinate ↪ Nat.Primes,
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
          LinearIndependent finitePrimeRationalCoefficientField M.row) := by
  obtain ⟨e, _, hdiff, _⟩ :=
    exists_orderPointedContinuumPrimeRelationIdealCircuitUniversality
      sigma eta x hsigma heta hx
  refine ⟨e, ?_⟩
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
