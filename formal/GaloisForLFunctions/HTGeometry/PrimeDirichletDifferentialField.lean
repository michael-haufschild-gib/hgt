import GaloisForLFunctions.HTGeometry.PrimeDirichletAnalyticTransfer
import GaloisForLFunctions.HTGeometry.DifferentialAdjoinPairClassification
import GaloisForLFunctions.HTGeometry.DifferenceDifferential
import Mathlib.RingTheory.Derivation.MapCoeffs

/-!
# The differential field of shifted signed prime Dirichlet carriers

This file equips the arithmetic-function fraction field with the rotated logarithmic Dirichlet
derivation and extends it across the formal rational coordinate, with coordinate derivative one.
Every shifted signed-prime carrier then has exactly the previously constructed shifted rotated
jets as its algebraic differential jets.  Passing from all finite jet rectangles to the full
natural-order family proves the exact differential tail-matroid theorem over `E_fin(s)`.
-/

namespace GaloisForLFunctions.HTGeometry

open ArithmeticFunction
open scoped Differential

noncomputable section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

local instance arithmeticFunctionIntAlgebra : Algebra ℤ (ArithmeticFunction ℂ) :=
  Ring.toIntAlgebra (ArithmeticFunction ℂ)

local instance arithmeticFunctionFractionIntAlgebra :
    Algebra ℤ arithmeticFunctionFractionField :=
  Ring.toIntAlgebra arithmeticFunctionFractionField

local instance arithmeticFunctionPolynomialIntAlgebra :
    Algebra ℤ (Polynomial arithmeticFunctionFractionField) :=
  Ring.toIntAlgebra (Polynomial arithmeticFunctionFractionField)

local instance arithmeticFunctionPolynomialFractionIntAlgebra :
    Algebra ℤ (FractionRing (Polynomial arithmeticFunctionFractionField)) :=
  Ring.toIntAlgebra (FractionRing (Polynomial arithmeticFunctionFractionField))

local instance arithmeticFunctionRatFuncIntAlgebra :
    Algebra ℤ arithmeticFunctionRationalCoordinateField :=
  Ring.toIntAlgebra arithmeticFunctionRationalCoordinateField

/-- The rotated logarithmic coefficient derivation before passing to fractions. -/
def rotatedLogArithmeticDerivationComplex :
    Derivation ℂ (ArithmeticFunction ℂ) (ArithmeticFunction ℂ) :=
  Derivation.mk'
    { toFun := fun f => Complex.I • logWeight f
      map_add' := by
        intro f g
        rw [logWeight_add, smul_add]
      map_smul' := by
        intro c f
        rw [logWeight_smul]
        simp only [smul_smul]
        congr 1
        exact mul_comm _ _ }
    (by
      intro f g
      change Complex.I • logWeight (f * g) =
        f * (Complex.I • logWeight g) + g * (Complex.I • logWeight f)
      calc
        Complex.I • logWeight (f * g) =
            (Complex.I • logWeight f) * g +
              f * (Complex.I • logWeight g) := by
          rw [logWeight_leibniz, smul_add, Algebra.smul_mul_assoc,
            Algebra.mul_smul_comm]
        _ = f * (Complex.I • logWeight g) +
            g * (Complex.I • logWeight f) := by
          rw [add_comm, mul_comm g])

/-- The same derivation over the canonical integer base required by Mathlib's `Differential`
class. -/
def rotatedLogArithmeticDerivation :
    Derivation ℤ (ArithmeticFunction ℂ) (ArithmeticFunction ℂ) :=
  rotatedLogArithmeticDerivationComplex.restrictScalars ℤ

@[simp]
theorem rotatedLogArithmeticDerivation_apply (f : ArithmeticFunction ℂ) :
    rotatedLogArithmeticDerivation f = Complex.I • logWeight f :=
  rfl

/-- Quotient-rule extension of the rotated logarithmic derivation to arithmetic fractions. -/
def rotatedLogFractionDerivation :
    Derivation ℤ arithmeticFunctionFractionField arithmeticFunctionFractionField :=
  fractionRingDerivation
    ((Algebra.linearMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField).compDer
      rotatedLogArithmeticDerivation)

@[simp]
theorem rotatedLogFractionDerivation_algebraMap (f : ArithmeticFunction ℂ) :
    rotatedLogFractionDerivation
        (algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField f) =
      algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
        (Complex.I • logWeight f) := by
  exact fractionRingDerivation_algebraMap
    ((Algebra.linearMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField).compDer
      rotatedLogArithmeticDerivation) f

noncomputable instance arithmeticFunctionFractionFieldDifferential :
    Differential arithmeticFunctionFractionField where
  deriv := rotatedLogFractionDerivation

@[simp]
theorem arithmeticFunctionFractionField_deriv_apply
    (x : arithmeticFunctionFractionField) :
    x′ = rotatedLogFractionDerivation x :=
  rfl

/-- A literal polynomial fraction carrier used to construct the quotient-rule derivation before
transporting it to `RatFunc`. -/
abbrev arithmeticFunctionPolynomialFractionField :=
  FractionRing (Polynomial arithmeticFunctionFractionField)

/-- Differentiate coefficients by the rotated logarithmic derivation and the coordinate by one. -/
def arithmeticFunctionPolynomialDerivation :
    Derivation ℤ (Polynomial arithmeticFunctionFractionField)
      (Polynomial arithmeticFunctionFractionField) :=
  Differential.implicitDeriv (1 : Polynomial arithmeticFunctionFractionField)

/-- Quotient-rule extension of the polynomial derivation. -/
def arithmeticFunctionPolynomialFractionDerivation :
    Derivation ℤ arithmeticFunctionPolynomialFractionField
      arithmeticFunctionPolynomialFractionField :=
  fractionRingDerivation
    ((Algebra.linearMap (Polynomial arithmeticFunctionFractionField)
      arithmeticFunctionPolynomialFractionField).compDer
        arithmeticFunctionPolynomialDerivation)

/-- The canonical algebra equivalence between `RatFunc` and the literal polynomial fraction
ring. -/
def arithmeticFunctionRatFuncToPolynomialFraction :
    arithmeticFunctionRationalCoordinateField ≃ₐ[arithmeticFunctionFractionField]
      arithmeticFunctionPolynomialFractionField :=
  RatFunc.toFractionRingAlgEquiv arithmeticFunctionFractionField
    arithmeticFunctionFractionField

/-- The rational-coordinate derivation transported back from the literal fraction ring. -/
def arithmeticFunctionRationalCoordinateDerivation :
    Derivation ℤ arithmeticFunctionRationalCoordinateField
      arithmeticFunctionRationalCoordinateField :=
  let e := arithmeticFunctionRatFuncToPolynomialFraction
  Derivation.mk'
    { toFun := fun x => e.symm (arithmeticFunctionPolynomialFractionDerivation (e x))
      map_add' := by
        intro x y
        rw [map_add, map_add, map_add]
      map_smul' := by
        intro z x
        change e.symm (arithmeticFunctionPolynomialFractionDerivation (e (z • x))) =
          z • e.symm (arithmeticFunctionPolynomialFractionDerivation (e x))
        simp }
    (by
      intro x y
      change e.symm (arithmeticFunctionPolynomialFractionDerivation (e (x * y))) = _
      rw [map_mul, Derivation.leibniz, map_add]
      simp only [smul_eq_mul, map_mul]
      rfl)

noncomputable instance arithmeticFunctionRationalCoordinateFieldDifferential :
    Differential arithmeticFunctionRationalCoordinateField where
  deriv := arithmeticFunctionRationalCoordinateDerivation

/-- The rational-coordinate derivation extends the rotated logarithmic derivation on constant
arithmetic fractions. -/
@[simp]
theorem arithmeticFunctionRationalCoordinateField_deriv_algebraMap
    (x : arithmeticFunctionFractionField) :
    (algebraMap arithmeticFunctionFractionField
      arithmeticFunctionRationalCoordinateField x)′ =
      algebraMap arithmeticFunctionFractionField
        arithmeticFunctionRationalCoordinateField x′ := by
  change arithmeticFunctionRationalCoordinateDerivation
      (algebraMap arithmeticFunctionFractionField
        arithmeticFunctionRationalCoordinateField x) = _
  change arithmeticFunctionRatFuncToPolynomialFraction.symm
      (arithmeticFunctionPolynomialFractionDerivation
        (arithmeticFunctionRatFuncToPolynomialFraction
          (algebraMap arithmeticFunctionFractionField
            arithmeticFunctionRationalCoordinateField x))) = _
  apply arithmeticFunctionRatFuncToPolynomialFraction.injective
  rw [arithmeticFunctionRatFuncToPolynomialFraction.apply_symm_apply]
  rw [show arithmeticFunctionRatFuncToPolynomialFraction
      (algebraMap arithmeticFunctionFractionField
        arithmeticFunctionRationalCoordinateField x) =
      algebraMap arithmeticFunctionFractionField
        arithmeticFunctionPolynomialFractionField x from
    arithmeticFunctionRatFuncToPolynomialFraction.commutes x]
  rw [show arithmeticFunctionRatFuncToPolynomialFraction
      (algebraMap arithmeticFunctionFractionField
        arithmeticFunctionRationalCoordinateField x′) =
      algebraMap arithmeticFunctionFractionField
        arithmeticFunctionPolynomialFractionField x′ from
    arithmeticFunctionRatFuncToPolynomialFraction.commutes x′]
  change arithmeticFunctionPolynomialFractionDerivation
      (algebraMap (Polynomial arithmeticFunctionFractionField)
        arithmeticFunctionPolynomialFractionField (Polynomial.C x)) =
    algebraMap (Polynomial arithmeticFunctionFractionField)
      arithmeticFunctionPolynomialFractionField (Polynomial.C x′)
  rw [arithmeticFunctionPolynomialFractionDerivation,
    fractionRingDerivation_algebraMap]
  change algebraMap (Polynomial arithmeticFunctionFractionField)
      arithmeticFunctionPolynomialFractionField
        (arithmeticFunctionPolynomialDerivation (Polynomial.C x)) = _
  change algebraMap (Polynomial arithmeticFunctionFractionField)
      arithmeticFunctionPolynomialFractionField
        ((Differential.implicitDeriv 1) (Polynomial.C x)) = _
  exact congrArg
    (algebraMap (Polynomial arithmeticFunctionFractionField)
      arithmeticFunctionPolynomialFractionField)
    (Differential.implicitDeriv_C
      (1 : Polynomial arithmeticFunctionFractionField) x)

/-- Applying the ambient derivation to a shifted order-`k` carrier gives exactly the order
`k+1` carrier. -/
@[simp]
theorem rotatedLogFractionDerivation_signedPrimeShiftedRotatedJet
    (ε : Nat.Primes → Bool) (a : ℂ) (k : ℕ) :
    rotatedLogFractionDerivation
        (algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
          (signedPrimeShiftedRotatedJet ε a k).1) =
      algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
        (signedPrimeShiftedRotatedJet ε a (k + 1)).1 := by
  rw [rotatedLogFractionDerivation_algebraMap]
  congr 1
  ext n
  simp only [ArithmeticFunction.smul_map, smul_eq_mul, logWeight_apply,
    signedPrimeShiftedRotatedJet_apply]
  ring

/-- One shifted signed-prime Dirichlet carrier in the formal differential field. -/
def signedPrimeShiftCarrier (ε : Nat.Primes → Bool) (a : ℂ) :
    arithmeticFunctionRationalCoordinateField :=
  algebraMap arithmeticFunctionFractionField arithmeticFunctionRationalCoordinateField
    (algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
      (signedPrimeShiftedRotatedJet ε a 0).1)

/-- Every algebraic differential jet of a shifted carrier is exactly its shifted rotated analytic
jet. -/
@[simp]
theorem differentialJet_signedPrimeShiftCarrier
    (ε : Nat.Primes → Bool) (a : ℂ) (k : ℕ) :
    GaloisForLFunctions.differentialJet k (signedPrimeShiftCarrier ε a) =
      algebraMap arithmeticFunctionFractionField arithmeticFunctionRationalCoordinateField
        (algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
          (signedPrimeShiftedRotatedJet ε a k).1) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [GaloisForLFunctions.differentialJet_succ, ih,
        arithmeticFunctionRationalCoordinateField_deriv_algebraMap,
        arithmeticFunctionFractionField_deriv_apply,
        rotatedLogFractionDerivation_signedPrimeShiftedRotatedJet]

/-- Algebraic independence of all finite initial jet rectangles implies algebraic independence of
the full family indexed by natural derivative order. -/
theorem algebraicIndependent_prod_nat_of_fin
    {R K I : Type*} [CommRing R] [CommRing K] [Algebra R K]
    [Nonempty I] (x : I → ℕ → K)
    (hfin : ∀ m, AlgebraicIndependent R
      (fun ik : I × Fin (m + 1) => x ik.1 ik.2)) :
    AlgebraicIndependent R (fun ik : I × ℕ => x ik.1 ik.2) := by
  apply algebraicIndependent_of_finite_type
  intro t ht
  obtain ⟨q, hq⟩ := Set.exists_upper_bound_image t Prod.snd ht
  let f : t → I × Fin (q.2 + 1) := fun z =>
    (z.1.1, ⟨z.1.2, Nat.lt_succ_of_le (hq z.1 z.2)⟩)
  have hf : Function.Injective f := by
    intro z w hzw
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun u => u.1) hzw
    · exact congrArg (fun u => (u.2 : ℕ)) hzw
  have hsub := (hfin q.2).comp f hf
  simpa only [Function.comp_apply, f] using! hsub

/-- **Complete shifted differential tail matroid.** The family containing every shift in a finite
palette is differentially algebraically independent over `E_fin(s)` exactly when the Boolean
orientation family is linearly independent modulo finite prime support. -/
theorem signedPrimeShiftPalette_differentialIndependent_iff
    {J A : Type*} [Fintype J] [DecidableEq J] [Nonempty J]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (ε : J → Nat.Primes → Bool) (alpha : A → ℂ)
    (hdistinct : Function.Injective (fun a => (alpha a).re)) :
    GaloisForLFunctions.DifferentialIndependent finitePrimeRationalCoefficientField
        (fun ja : J × A => signedPrimeShiftCarrier (ε ja.1) (alpha ja.2)) ↔
      PrimeOrientationTailIndependent ε := by
  constructor
  · intro hdiff
    unfold GaloisForLFunctions.DifferentialIndependent at hdiff
    let f : J × (A × Fin 1) → (J × A) × ℕ := fun jak =>
      ((jak.1, jak.2.1), jak.2.2)
    have hf : Function.Injective f := by
      rintro ⟨j, a, k⟩ ⟨j', a', k'⟩ h
      simp only [f, Prod.mk.injEq] at h ⊢
      exact ⟨h.1.1, h.1.2, Fin.ext h.2⟩
    have hzero := hdiff.comp f hf
    have hjets : AlgebraicIndependent finitePrimeRationalCoefficientField
        (fun jak : J × (A × Fin 1) =>
          algebraMap arithmeticFunctionFractionField
            arithmeticFunctionRationalCoordinateField
            (algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
              (signedPrimeShiftedRotatedJet
                (ε jak.1) (alpha jak.2.1) jak.2.2).1)) := by
      simpa only [Function.comp_apply, f,
        differentialJet_signedPrimeShiftCarrier] using! hzero
    exact
      (signedPrimeShiftedRotatedJets_algebraicIndependent_over_finitePrimeRationalCoefficientField_iff
        ε alpha hdistinct 0).mp hjets
  · intro htail
    unfold GaloisForLFunctions.DifferentialIndependent
    simp_rw [differentialJet_signedPrimeShiftCarrier]
    let x : (J × A) → ℕ → arithmeticFunctionRationalCoordinateField := fun ja k =>
      algebraMap arithmeticFunctionFractionField arithmeticFunctionRationalCoordinateField
        (algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
          (signedPrimeShiftedRotatedJet (ε ja.1) (alpha ja.2) k).1)
    apply algebraicIndependent_prod_nat_of_fin x
    intro m
    let f : (J × A) × Fin (m + 1) → J × (A × Fin (m + 1)) := fun jak =>
      (jak.1.1, (jak.1.2, jak.2))
    have hf : Function.Injective f := by
      rintro ⟨⟨j, a⟩, k⟩ ⟨⟨j', a'⟩, k'⟩ h
      simp only [f, Prod.mk.injEq] at h ⊢
      exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩
    have hrect :=
      (signedPrimeShiftedRotatedJets_algebraicIndependent_over_finitePrimeRationalCoefficientField_iff
        ε alpha hdistinct m).mpr htail
    have hsub := hrect.comp f hf
    simpa only [Function.comp_apply, f, x] using! hsub

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open ArithmeticFunction
open scoped Differential

noncomputable section

/-- The canonical complete nonnegative-integer shift palette of one orientation. -/
def signedPrimeNaturalShiftPalette
    (ε : Nat.Primes → Bool) (a : ℕ) :
    arithmeticFunctionRationalCoordinateField :=
  signedPrimeShiftCarrier ε (a : ℂ)

/-- Distinct natural shifts have distinct real parts. -/
theorem natCastComplex_re_injective :
    Function.Injective (fun n : ℕ => ((n : ℂ)).re) := by
  intro m n h
  norm_num at h
  exact_mod_cast h

/-- **Canonical complete-palette differential matroid.** Differential independence of the entire
nonnegative-integer shift palette is exactly orientation-tail independence. The proof bounds both
shift and derivative order on each finite polynomial support and invokes the already formalized
finite rectangle theorem. -/
theorem signedPrimeNaturalShiftPalette_differentialIndependent_iff
    {J : Type*} [Fintype J] [DecidableEq J] [Nonempty J]
    (ε : J → Nat.Primes → Bool) :
    GaloisForLFunctions.DifferentialIndependent finitePrimeRationalCoefficientField
        (fun ja : J × ℕ => signedPrimeNaturalShiftPalette (ε ja.1) ja.2) ↔
      PrimeOrientationTailIndependent ε := by
  constructor
  · intro hdiff
    unfold GaloisForLFunctions.DifferentialIndependent at hdiff
    let f : J × (Fin 1 × Fin 1) → (J × ℕ) × ℕ := fun jak =>
      ((jak.1, jak.2.1), jak.2.2)
    have hf : Function.Injective f := by
      rintro ⟨j, a, k⟩ ⟨j', a', k'⟩ h
      simp only [f, Prod.mk.injEq] at h ⊢
      exact ⟨h.1.1, Fin.ext h.1.2, Fin.ext h.2⟩
    have hzero := hdiff.comp f hf
    have hjets : AlgebraicIndependent finitePrimeRationalCoefficientField
        (fun jak : J × (Fin 1 × Fin 1) =>
          algebraMap arithmeticFunctionFractionField
            arithmeticFunctionRationalCoordinateField
            (algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
              (signedPrimeShiftedRotatedJet
                (ε jak.1) ((jak.2.1 : ℕ) : ℂ) jak.2.2).1)) := by
      simpa only [Function.comp_apply, f, signedPrimeNaturalShiftPalette,
        differentialJet_signedPrimeShiftCarrier] using! hzero
    exact
      (signedPrimeShiftedRotatedJets_algebraicIndependent_over_finitePrimeRationalCoefficientField_iff
        ε (fun a : Fin 1 => ((a : ℕ) : ℂ)) (by
          intro a b h
          apply Fin.ext
          exact natCastComplex_re_injective h) 0).mp hjets
  · intro htail
    unfold GaloisForLFunctions.DifferentialIndependent
    simp_rw [signedPrimeNaturalShiftPalette, differentialJet_signedPrimeShiftCarrier]
    apply algebraicIndependent_of_finite_type
    intro t ht
    obtain ⟨qa, hqa⟩ := Set.exists_upper_bound_image t (fun z => z.1.2) ht
    obtain ⟨qk, hqk⟩ := Set.exists_upper_bound_image t Prod.snd ht
    let f : t → J × (Fin (qa.1.2 + 1) × Fin (qk.2 + 1)) := fun z =>
      (z.1.1.1,
        (⟨z.1.1.2, Nat.lt_succ_of_le (hqa z.1 z.2)⟩,
          ⟨z.1.2, Nat.lt_succ_of_le (hqk z.1 z.2)⟩))
    have hf : Function.Injective f := by
      intro z w hzw
      apply Subtype.ext
      apply Prod.ext
      · apply Prod.ext
        · exact congrArg (fun u => u.1) hzw
        · exact congrArg (fun u => ((u.2.1 : Fin (qa.1.2 + 1)) : ℕ)) hzw
      · exact congrArg (fun u => ((u.2.2 : Fin (qk.2 + 1)) : ℕ)) hzw
    have hrect :=
      (signedPrimeShiftedRotatedJets_algebraicIndependent_over_finitePrimeRationalCoefficientField_iff
        ε (fun a : Fin (qa.1.2 + 1) => ((a : ℕ) : ℂ)) (by
          intro a b h
          apply Fin.ext
          exact natCastComplex_re_injective h) qk.2).mpr htail
    have hsub := hrect.comp f hf
    simpa only [Function.comp_apply, f] using! hsub

end

end GaloisForLFunctions.HTGeometry
namespace GaloisForLFunctions.HTGeometry

open ArithmeticFunction
open scoped Differential

noncomputable section

def signedPrimeJetSubCoefficient
    (ε δ : Nat.Primes → Bool) (a : ℂ) (k : ℕ) (p : Nat.Primes) : ℂ :=
  (primeDirichletSign (ε p) - primeDirichletSign (δ p)) *
    primeShiftFactor a p * rotatedPrimeLogClock p ^ k

theorem signedPrimeShiftedRotatedJet_sub_eq_arithmeticOfPrimeColumn
    (ε δ : Nat.Primes → Bool) (a : ℂ) (k : ℕ) :
    (signedPrimeShiftedRotatedJet ε a k).1 -
        (signedPrimeShiftedRotatedJet δ a k).1 =
      arithmeticOfPrimeColumn (signedPrimeJetSubCoefficient ε δ a k) := by
  rw [signedPrimeShiftedRotatedJet_eq_arithmeticOfPrimeColumn,
    signedPrimeShiftedRotatedJet_eq_arithmeticOfPrimeColumn]
  ext n
  change arithmeticOfPrimeColumn
      (fun p => primeDirichletSign (ε p) * primeShiftFactor a p *
        rotatedPrimeLogClock p ^ k) n -
      arithmeticOfPrimeColumn
        (fun p => primeDirichletSign (δ p) * primeShiftFactor a p *
          rotatedPrimeLogClock p ^ k) n =
    arithmeticOfPrimeColumn (signedPrimeJetSubCoefficient ε δ a k) n
  by_cases hn : n.Prime
  · rw [arithmeticOfPrimeColumn_apply_prime _ ⟨n, hn⟩,
      arithmeticOfPrimeColumn_apply_prime _ ⟨n, hn⟩,
      arithmeticOfPrimeColumn_apply_prime _ ⟨n, hn⟩]
    simp only [signedPrimeJetSubCoefficient]
    ring
  · simp [arithmeticOfPrimeColumn, hn]

theorem signedPrimeJetSubCoefficient_support_finite
    {ε δ : Nat.Primes → Bool} (h : PrimeOrientationsEventuallyEqual ε δ)
    (a : ℂ) (k : ℕ) :
    {p | signedPrimeJetSubCoefficient ε δ a k p ≠ 0}.Finite := by
  apply h.subset
  intro p hp
  simp only [Set.mem_setOf_eq] at hp ⊢
  intro heq
  apply hp
  simp [signedPrimeJetSubCoefficient, heq]

theorem signedPrimeNaturalShiftPalette_sub_jetsInBase
    {ε δ : Nat.Primes → Bool} (h : PrimeOrientationsEventuallyEqual ε δ) :
    ∀ a n, ∃ b : finitePrimeRationalCoefficientField,
      GaloisForLFunctions.differentialJet n
          (signedPrimeNaturalShiftPalette ε a - signedPrimeNaturalShiftPalette δ a) =
        algebraMap finitePrimeRationalCoefficientField
          arithmeticFunctionRationalCoordinateField b := by
  intro a n
  let coeff := signedPrimeJetSubCoefficient ε δ (a : ℂ) n
  have hcoeff : {p | coeff p ≠ 0}.Finite :=
    signedPrimeJetSubCoefficient_support_finite h (a : ℂ) n
  let kF : finitePrimeCoefficientField :=
    ⟨algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
      (arithmeticOfPrimeColumn coeff),
      (arithmeticOfPrimeColumn_mem_finitePrimeCoefficientField_iff coeff).2 hcoeff⟩
  let b : finitePrimeRationalCoefficientField :=
    algebraMap finitePrimeCoefficientField finitePrimeRationalCoefficientField kF
  refine ⟨b, ?_⟩
  rw [GaloisForLFunctions.differentialJet_sub]
  simp only [signedPrimeNaturalShiftPalette]
  rw [differentialJet_signedPrimeShiftCarrier,
    differentialJet_signedPrimeShiftCarrier, ← map_sub, ← map_sub,
    signedPrimeShiftedRotatedJet_sub_eq_arithmeticOfPrimeColumn]
  change algebraMap arithmeticFunctionFractionField
      arithmeticFunctionRationalCoordinateField kF.1 =
    algebraMap finitePrimeRationalCoefficientField
      arithmeticFunctionRationalCoordinateField b
  exact (finitePrimeRationalCoefficientFieldToFormalRatFunc_algebraMap kF).symm

def signedPrimeJetAddCoefficient
    (ε δ : Nat.Primes → Bool) (a : ℂ) (k : ℕ) (p : Nat.Primes) : ℂ :=
  (primeDirichletSign (ε p) + primeDirichletSign (δ p)) *
    primeShiftFactor a p * rotatedPrimeLogClock p ^ k

theorem signedPrimeShiftedRotatedJet_add_eq_arithmeticOfPrimeColumn
    (ε δ : Nat.Primes → Bool) (a : ℂ) (k : ℕ) :
    (signedPrimeShiftedRotatedJet ε a k).1 +
        (signedPrimeShiftedRotatedJet δ a k).1 =
      arithmeticOfPrimeColumn (signedPrimeJetAddCoefficient ε δ a k) := by
  rw [signedPrimeShiftedRotatedJet_eq_arithmeticOfPrimeColumn,
    signedPrimeShiftedRotatedJet_eq_arithmeticOfPrimeColumn]
  ext n
  change arithmeticOfPrimeColumn
      (fun p => primeDirichletSign (ε p) * primeShiftFactor a p *
        rotatedPrimeLogClock p ^ k) n +
      arithmeticOfPrimeColumn
        (fun p => primeDirichletSign (δ p) * primeShiftFactor a p *
          rotatedPrimeLogClock p ^ k) n =
    arithmeticOfPrimeColumn (signedPrimeJetAddCoefficient ε δ a k) n
  by_cases hn : n.Prime
  · rw [arithmeticOfPrimeColumn_apply_prime _ ⟨n, hn⟩,
      arithmeticOfPrimeColumn_apply_prime _ ⟨n, hn⟩,
      arithmeticOfPrimeColumn_apply_prime _ ⟨n, hn⟩]
    simp only [signedPrimeJetAddCoefficient]
    ring
  · simp [arithmeticOfPrimeColumn, hn]

theorem signedPrimeJetAddCoefficient_support_finite
    {ε δ : Nat.Primes → Bool} (h : PrimeOrientationsEventuallyOpposite ε δ)
    (a : ℂ) (k : ℕ) :
    {p | signedPrimeJetAddCoefficient ε δ a k p ≠ 0}.Finite := by
  apply h.subset
  intro p hp
  simp only [Set.mem_setOf_eq] at hp ⊢
  by_contra hne
  apply hp
  simp only [signedPrimeJetAddCoefficient]
  rw [primeDirichletSign_eq_neg_of_ne hne]
  ring

theorem signedPrimeNaturalShiftPalette_add_jetsInBase
    {ε δ : Nat.Primes → Bool} (h : PrimeOrientationsEventuallyOpposite ε δ) :
    ∀ a n, ∃ b : finitePrimeRationalCoefficientField,
      GaloisForLFunctions.differentialJet n
          (signedPrimeNaturalShiftPalette ε a + signedPrimeNaturalShiftPalette δ a) =
        algebraMap finitePrimeRationalCoefficientField
          arithmeticFunctionRationalCoordinateField b := by
  intro a n
  let coeff := signedPrimeJetAddCoefficient ε δ (a : ℂ) n
  have hcoeff : {p | coeff p ≠ 0}.Finite :=
    signedPrimeJetAddCoefficient_support_finite h (a : ℂ) n
  let kF : finitePrimeCoefficientField :=
    ⟨algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
      (arithmeticOfPrimeColumn coeff),
      (arithmeticOfPrimeColumn_mem_finitePrimeCoefficientField_iff coeff).2 hcoeff⟩
  let b : finitePrimeRationalCoefficientField :=
    algebraMap finitePrimeCoefficientField finitePrimeRationalCoefficientField kF
  refine ⟨b, ?_⟩
  rw [GaloisForLFunctions.differentialJet_add_apply]
  simp only [signedPrimeNaturalShiftPalette]
  rw [differentialJet_signedPrimeShiftCarrier,
    differentialJet_signedPrimeShiftCarrier, ← map_add, ← map_add,
    signedPrimeShiftedRotatedJet_add_eq_arithmeticOfPrimeColumn]
  change algebraMap arithmeticFunctionFractionField
      arithmeticFunctionRationalCoordinateField kF.1 =
    algebraMap finitePrimeRationalCoefficientField
      arithmeticFunctionRationalCoordinateField b
  exact (finitePrimeRationalCoefficientFieldToFormalRatFunc_algebraMap kF).symm

theorem signedPrimeNaturalShiftPalette_differentialAdjoin_eq_of_eventuallyEqual
    {ε δ : Nat.Primes → Bool} (h : PrimeOrientationsEventuallyEqual ε δ) :
    GaloisForLFunctions.differentialAdjoin finitePrimeRationalCoefficientField
        (Set.range (signedPrimeNaturalShiftPalette ε)) =
      GaloisForLFunctions.differentialAdjoin finitePrimeRationalCoefficientField
        (Set.range (signedPrimeNaturalShiftPalette δ)) := by
  exact GaloisForLFunctions.differentialAdjoin_range_eq_of_sub_jetsInBase
    (signedPrimeNaturalShiftPalette ε) (signedPrimeNaturalShiftPalette δ)
      (signedPrimeNaturalShiftPalette_sub_jetsInBase h)

theorem signedPrimeNaturalShiftPalette_differentialAdjoin_eq_of_eventuallyOpposite
    {ε δ : Nat.Primes → Bool} (h : PrimeOrientationsEventuallyOpposite ε δ) :
    GaloisForLFunctions.differentialAdjoin finitePrimeRationalCoefficientField
        (Set.range (signedPrimeNaturalShiftPalette ε)) =
      GaloisForLFunctions.differentialAdjoin finitePrimeRationalCoefficientField
        (Set.range (signedPrimeNaturalShiftPalette δ)) := by
  exact GaloisForLFunctions.differentialAdjoin_range_eq_of_add_jetsInBase
    (signedPrimeNaturalShiftPalette ε) (signedPrimeNaturalShiftPalette δ)
      (signedPrimeNaturalShiftPalette_add_jetsInBase h)

def primeOrientationPair (ε δ : Nat.Primes → Bool) : Bool → Nat.Primes → Bool :=
  fun b => if b then δ else ε

theorem primeOrientationPair_tailIndependent_iff_not_pairDependent
    (ε δ : Nat.Primes → Bool) :
    PrimeOrientationTailIndependent (primeOrientationPair ε δ) ↔
      ¬ PrimeOrientationTailPairDependent ε δ := by
  constructor
  · intro htail hdep
    obtain ⟨a, b, hab, hsupp⟩ := hdep
    let c : Bool → ℂ := fun q => if q then b else a
    have hc : c = 0 := htail c (by
      simpa [primeOrientationPair, c, Fintype.sum_bool, add_comm] using hsupp)
    have ha : a = 0 := by
      have := congrFun hc false
      simpa [c] using this
    have hb : b = 0 := by
      have := congrFun hc true
      simpa [c] using this
    exact hab.elim (fun h => h ha) (fun h => h hb)
  · intro hnot c hsupp
    by_contra hc
    apply hnot
    refine ⟨c false, c true, ?_, ?_⟩
    · have hexists : ∃ q, c q ≠ 0 := by
        simpa only [Pi.zero_apply] using (Function.ne_iff.mp hc)
      obtain ⟨q, hq⟩ := hexists
      cases q
      · exact Or.inl hq
      · exact Or.inr hq
    · simpa only [primeOrientationPair, Bool.if_false_right,
        Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte, Bool.true_eq_false,
        not_false_eq_true, add_comm] using hsupp

theorem signedPrimeNaturalShiftPalette_differentialAdjoin_eq_iff
    (ε δ : Nat.Primes → Bool) :
    GaloisForLFunctions.differentialAdjoin finitePrimeRationalCoefficientField
        (Set.range (signedPrimeNaturalShiftPalette ε)) =
      GaloisForLFunctions.differentialAdjoin finitePrimeRationalCoefficientField
        (Set.range (signedPrimeNaturalShiftPalette δ)) ↔
      PrimeOrientationsEventuallyEqual ε δ ∨
        PrimeOrientationsEventuallyOpposite ε δ := by
  constructor
  · intro heq
    by_contra hrel
    have hnotdep : ¬ PrimeOrientationTailPairDependent ε δ := by
      intro hdep
      exact hrel ((primeOrientationTailPairDependent_iff ε δ).mp hdep)
    have htail : PrimeOrientationTailIndependent (primeOrientationPair ε δ) :=
      (primeOrientationPair_tailIndependent_iff_not_pairDependent ε δ).mpr hnotdep
    have hpair :=
      (signedPrimeNaturalShiftPalette_differentialIndependent_iff
        (primeOrientationPair ε δ)).mpr htail
    let x : ℕ → arithmeticFunctionRationalCoordinateField :=
      signedPrimeNaturalShiftPalette ε
    let y : ℕ → arithmeticFunctionRationalCoordinateField :=
      signedPrimeNaturalShiftPalette δ
    let f : ℕ ⊕ ℕ → Bool × ℕ := fun z =>
      Sum.elim (fun n => (false, n)) (fun n => (true, n)) z
    have hf : Function.Injective f := by
      intro u v huv
      rcases u with n | n <;> rcases v with m | m
      · exact congrArg Sum.inl (congrArg Prod.snd huv)
      · simp [f] at huv
      · simp [f] at huv
      · exact congrArg Sum.inr (congrArg Prod.snd huv)
    have hjoint := hpair.comp f hf
    have hfun :
        ((fun p : Bool × ℕ =>
          signedPrimeNaturalShiftPalette (primeOrientationPair ε δ p.1) p.2) ∘ f) =
        Sum.elim x y := by
      funext z
      rcases z with n | n <;> rfl
    rw [hfun] at hjoint
    exact (GaloisForLFunctions.differentialIndependent_sum_unequal_differentialAdjoin
      (F := finitePrimeRationalCoefficientField) x y hjoint) heq
  · rintro (heq | hopp)
    · exact signedPrimeNaturalShiftPalette_differentialAdjoin_eq_of_eventuallyEqual heq
    · exact signedPrimeNaturalShiftPalette_differentialAdjoin_eq_of_eventuallyOpposite hopp

end
end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open scoped Differential

noncomputable section

/-- Two orientations outside the eventual equal/opposite tail orbit carry jointly differentially
independent complete natural-shift palettes. This is the differential transcendence-rank-two
content of the tail matroid classification. -/
theorem signedPrimeNaturalShiftPalettes_differentialIndependent_of_not_tailEquivalent
    (ε δ : Nat.Primes → Bool)
    (hrel : ¬ (PrimeOrientationsEventuallyEqual ε δ ∨
      PrimeOrientationsEventuallyOpposite ε δ)) :
    GaloisForLFunctions.DifferentialIndependent finitePrimeRationalCoefficientField
      (Sum.elim (signedPrimeNaturalShiftPalette ε)
        (signedPrimeNaturalShiftPalette δ)) := by
  have hnotdep : ¬ PrimeOrientationTailPairDependent ε δ := by
    intro hdep
    exact hrel ((primeOrientationTailPairDependent_iff ε δ).mp hdep)
  have htail : PrimeOrientationTailIndependent (primeOrientationPair ε δ) :=
    (primeOrientationPair_tailIndependent_iff_not_pairDependent ε δ).mpr hnotdep
  have hpair :=
    (signedPrimeNaturalShiftPalette_differentialIndependent_iff
      (primeOrientationPair ε δ)).mpr htail
  let f : ℕ ⊕ ℕ → Bool × ℕ := fun z =>
    Sum.elim (fun n => (false, n)) (fun n => (true, n)) z
  have hf : Function.Injective f := by
    intro u v huv
    rcases u with n | n <;> rcases v with m | m
    · exact congrArg Sum.inl (congrArg Prod.snd huv)
    · simp [f] at huv
    · simp [f] at huv
    · exact congrArg Sum.inr (congrArg Prod.snd huv)
  have hjoint := hpair.comp f hf
  have hfun :
      ((fun p : Bool × ℕ =>
        signedPrimeNaturalShiftPalette (primeOrientationPair ε δ p.1) p.2) ∘ f) =
        Sum.elim (signedPrimeNaturalShiftPalette ε)
          (signedPrimeNaturalShiftPalette δ) := by
    funext z
    rcases z with n | n <;> rfl
  rw [hfun] at hjoint
  exact hjoint

/-- The two unshifted signed-prime sources themselves are jointly differentially independent
whenever their orientation tails are neither eventually equal nor eventually opposite. -/
theorem signedPrimeUnshiftedPair_differentialIndependent_of_not_tailEquivalent
    (ε δ : Nat.Primes → Bool)
    (hrel : ¬ (PrimeOrientationsEventuallyEqual ε δ ∨
      PrimeOrientationsEventuallyOpposite ε δ)) :
    GaloisForLFunctions.DifferentialIndependent finitePrimeRationalCoefficientField
      (Sum.elim (fun _ : Unit => signedPrimeNaturalShiftPalette ε 0)
        (fun _ : Unit => signedPrimeNaturalShiftPalette δ 0)) := by
  have hfull :=
    signedPrimeNaturalShiftPalettes_differentialIndependent_of_not_tailEquivalent ε δ hrel
  let f : Unit ⊕ Unit → ℕ ⊕ ℕ := fun z =>
    Sum.elim (fun _ => Sum.inl 0) (fun _ => Sum.inr 0) z
  have hf : Function.Injective f := by
    intro u v huv
    rcases u with u | u <;> rcases v with v | v
    · rfl
    · simp [f] at huv
    · simp [f] at huv
    · rfl
  have hfun :
      (Sum.elim (signedPrimeNaturalShiftPalette ε)
        (signedPrimeNaturalShiftPalette δ) ∘ f) =
      Sum.elim (fun _ : Unit => signedPrimeNaturalShiftPalette ε 0)
        (fun _ : Unit => signedPrimeNaturalShiftPalette δ 0) := by
    funext z
    rcases z with u | u <;> cases u <;> rfl
  have hzero := hfull.comp f hf
  rw [hfun] at hzero
  exact hzero

/-- The singleton all-positive orientation is tail-independent because the prime index type is
infinite: a nonzero constant coefficient cannot have finite support. -/
theorem primeOrientationAllPositive_singleton_tailIndependent :
    PrimeOrientationTailIndependent
      (fun _ : Unit => fun _ : Nat.Primes => false) := by
  intro c hfin
  funext u
  have hu : u = () := Subsingleton.elim _ _
  subst u
  change c () = (0 : ℂ)
  by_contra hc
  have hset :
      {p : Nat.Primes |
        ∑ i : Unit, c i * primeDirichletSign ((fun _ : Nat.Primes => false) p) ≠ 0} =
        Set.univ := by
    ext p
    simp [hc]
  rw [hset] at hfin
  exact Set.infinite_univ hfin

/-- The canonical all-positive signed-prime source is hypertranscendental over the finite-prime
rational coefficient field in the ambient rational-coordinate differential field. -/
theorem allPositiveSignedPrimeSource_hypertranscendental :
    GaloisForLFunctions.HypertranscendentalOver finitePrimeRationalCoefficientField
      (signedPrimeNaturalShiftPalette (fun _ : Nat.Primes => false) 0) := by
  rw [GaloisForLFunctions.hypertranscendentalOver_iff_differentialIndependent_singleton]
  have hpalette :=
    (signedPrimeNaturalShiftPalette_differentialIndependent_iff
      (fun _ : Unit => fun _ : Nat.Primes => false)).mpr
        primeOrientationAllPositive_singleton_tailIndependent
  have hsource := hpalette.comp (fun _ : Unit => ((), 0)) (by
    intro _ _ _
    exact Subsingleton.elim _ _)
  simpa only [Function.comp_apply] using! hsource

end
end GaloisForLFunctions.HTGeometry
