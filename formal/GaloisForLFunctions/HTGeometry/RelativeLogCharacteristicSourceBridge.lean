import GaloisForLFunctions.HTGeometry.MultipleGammaAnnihilatorExact
import GaloisForLFunctions.HTGeometry.RelativeLogCharacteristicArrangement

/-!
# The logarithmic characteristic arrangement of the genuine source

The differential-algebraic translation annihilator of the genuine multiple elliptic gamma
logarithmic derivative is the squarefree Veronese ideal.  Its characteristic boundary is therefore
computed by the coface point equations, and pulling those back through the coordinatewise
exponential clock gives the periodic codimension-two pair arrangement.

Everything here is unconditional: the annihilator identification is a theorem about the actual
meromorphic kernels, not an assumed special-function input.
-/

open Filter Set Topology Function Complex
open scoped Differential BigOperators

namespace GaloisForLFunctions

open Bottcher HTGeometry VeroneseIdeal

noncomputable section

attribute [local instance] facePacketMeroDecidableEq

attribute [local instance] ellipticGammaRationalBaseDomain
  ellipticGammaRationalBaseComplexAlgebraMero ellipticGammaRationalBaseComplexDifferential
  ellipticGammaRationalBaseMeroDifferential ellipticGammaRationalBaseMeroCharZero
  ellipticGammaRationalBaseComplexDifferentialAlgebra
  ellipticGammaRationalBaseCoordinateDifferential
  ellipticGammaRationalBaseCoordinateDifferentialAlgebra

attribute [local instance] relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential
  relativeGaugeDifferentialAlgebra relativeGaugeCharZeroBase

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The differential-algebraic translation annihilator -/

/-- Difference operators sending the source into the differentially algebraic locus. -/
def daTranslationAnnihilator (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) :
    Set (MvPolynomial ι ℂ) :=
  {P | DifferentialAlgebraicOver (RatFunc ℂ)
    (xApply τ P (multipleEllipticGammaLogDerivMero τ hτ))}

/-- **`Ann_DA(Ψ_r) = I_r` as sets of operators.** -/
theorem daTranslationAnnihilator_eq_veroneseIdeal
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (hQ : PeriodsIntegrallyIndependent τ) (r : ℕ) (hcard : Fintype.card ι = r + 1) :
    daTranslationAnnihilator τ hτ = (veroneseIdeal ℂ ι r : Set (MvPolynomial ι ℂ)) := by
  ext P
  exact differentialAlgebraicOver_xApply_iff_mem_veroneseIdeal τ hτ hQ r hcard P

/-! ## Its characteristic boundary -/

/-- Evaluating the whole squarefree ideal at a point is the same as evaluating its coface
generators. -/
theorem forall_eval_veroneseIdeal_iff_cofaceProductsVanish
    (r : ℕ) (x : Fin (r + 1) → ℂ) :
    (∀ P ∈ veroneseIdeal ℂ (Fin (r + 1)) r, MvPolynomial.eval x P = 0) ↔
      CofaceProductsVanish r x := by
  classical
  constructor
  · intro h i
    have hgen : (∏ j ∈ Finset.univ.erase i, MvPolynomial.X (R := ℂ) j) ∈
        veroneseIdeal ℂ (Fin (r + 1)) r := by
      refine Ideal.subset_span ⟨Finset.univ.erase i, ?_, rfl⟩
      rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
      omega
    have := h _ hgen
    simpa using this
  · intro hx P hP
    have hker : veroneseIdeal ℂ (Fin (r + 1)) r ≤
        RingHom.ker (MvPolynomial.eval x : MvPolynomial (Fin (r + 1)) ℂ →+* ℂ) := by
      rw [veroneseIdeal, Ideal.span_le]
      rintro Q ⟨J, hJcard, rfl⟩
      have hJ : ∃ i : Fin (r + 1), J = Finset.univ.erase i := by
        have hcompl : (Jᶜ).card = 1 := by
          have htotal := Finset.card_add_card_compl J
          rw [Fintype.card_fin] at htotal
          omega
        obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hcompl
        refine ⟨i, ?_⟩
        have : J = (Jᶜ)ᶜ := by simp
        rw [this, hi]
        ext a
        simp [Finset.mem_erase, eq_comm]
      obtain ⟨i, rfl⟩ := hJ
      have hzero := hx i
      show MvPolynomial.eval x (∏ j ∈ Finset.univ.erase i, MvPolynomial.X j) = 0
      rw [map_prod]
      simpa using hzero
    have := hker hP
    simpa [RingHom.mem_ker] using this

/-- **Logarithmic characteristic arrangement of the genuine source.**  A clock lies on the
characteristic boundary of the genuine differential-algebraic translation annihilator exactly when
two distinct clock coordinates exponentiate to the unit translation character. -/
theorem daTranslationAnnihilator_logCharacteristicBoundary_iff
    (r : ℕ) (τ : Fin (r + 1) → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (hQ : PeriodsIntegrallyIndependent τ) (lambda : Fin (r + 1) → ℂ) :
    (∀ P ∈ daTranslationAnnihilator τ hτ,
        MvPolynomial.eval (fun j => Complex.exp (lambda j) - 1) P = 0) ↔
      ∃ a b : Fin (r + 1), a ≠ b ∧
        Complex.exp (lambda a) = 1 ∧ Complex.exp (lambda b) = 1 := by
  rw [daTranslationAnnihilator_eq_veroneseIdeal τ hτ hQ r (by simp)]
  rw [show (∀ P ∈ (veroneseIdeal ℂ (Fin (r + 1)) r : Set (MvPolynomial (Fin (r + 1)) ℂ)),
      MvPolynomial.eval (fun j => Complex.exp (lambda j) - 1) P = 0) ↔
      (∀ P ∈ veroneseIdeal ℂ (Fin (r + 1)) r,
        MvPolynomial.eval (fun j => Complex.exp (lambda j) - 1) P = 0) from Iff.rfl]
  rw [forall_eval_veroneseIdeal_iff_cofaceProductsVanish]
  exact multipleGammaLogCharacteristicBoundary_iff_exists_resonantPair r lambda

/-- The same boundary in its integral deck-charge form. -/
theorem daTranslationAnnihilator_logCharacteristicBoundary_iff_integer_chargedPair
    (r : ℕ) (τ : Fin (r + 1) → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (hQ : PeriodsIntegrallyIndependent τ) (lambda : Fin (r + 1) → ℂ) :
    (∀ P ∈ daTranslationAnnihilator τ hτ,
        MvPolynomial.eval (fun j => Complex.exp (lambda j) - 1) P = 0) ↔
      ∃ a b : Fin (r + 1), a ≠ b ∧
        ∃ k l : ℤ,
          lambda a = k * (2 * Real.pi * Complex.I) ∧
          lambda b = l * (2 * Real.pi * Complex.I) := by
  rw [daTranslationAnnihilator_logCharacteristicBoundary_iff r τ hτ hQ lambda,
    ← multipleGammaLogCharacteristicBoundary_iff_exists_resonantPair,
    multipleGammaLogCharacteristicBoundary_iff_exists_integer_chargedPair]

end

end GaloisForLFunctions
