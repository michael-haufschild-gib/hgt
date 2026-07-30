import GaloisForLFunctions.HTGeometry.GammaPoleScaleHarmonicRelativeFreeness
import GaloisForLFunctions.HTGeometry.MvPolynomialDiagonalScaleDomain
import GaloisForLFunctions.HTGeometry.GammaInversePoleBranchCoefficientFreeness

/-!
# Joint freeness of the Gamma pole scale and inverse-branch coefficients

The normalized inverse branch at the Gamma pole `-n` has nonlinear coefficients indexed by the
pole label.  Existing modules prove freeness of the reciprocal signed-factorial scale together
with the harmonic boundary, and freeness of the inverse-branch coefficients without that scale.
This module proves the missing joint statement.

For every finite prefix, an injective polynomial map fixes the scale and sends each harmonic
coordinate to its factorially weighted affine logarithmic coordinate.  A head-preserving lift then
transports injectivity through the Bell map, multiplicative unit inversion, and tangent
compositional inversion.  A finite-prefix argument yields countable algebraic independence of the
scale and all nonlinear inverse-branch coefficients.  The proof is purely algebraic and uses no
asymptotic or numerical input.
-/

open MvPolynomial Polynomial

namespace GaloisForLFunctions

noncomputable section

local instance jointLogComplexNatGermAlgebra : Algebra ℂ NatGerm :=
  complexNatGerm.toAlgebra

local instance jointLogRationalNatGermAlgebra :
    Algebra GammaPoleRationalBase NatGerm :=
  ratNatEval.toAlgebra

def optionTailAffineMap {K : Type*} [Field K]
    (m : ℕ) (alpha beta : Fin m → K) :
    MvPolynomial (Option (Fin m)) K →ₐ[K] MvPolynomial (Option (Fin m)) K :=
  MvPolynomial.aeval fun o => match o with
    | none => MvPolynomial.X none
    | some j => MvPolynomial.C (alpha j) * MvPolynomial.X (some j) +
        MvPolynomial.C (beta j)

def optionTailAffineMapInv {K : Type*} [Field K]
    (m : ℕ) (alpha beta : Fin m → K) :
    MvPolynomial (Option (Fin m)) K →ₐ[K] MvPolynomial (Option (Fin m)) K :=
  MvPolynomial.aeval fun o => match o with
    | none => MvPolynomial.X none
    | some j => MvPolynomial.C (alpha j)⁻¹ *
        (MvPolynomial.X (some j) - MvPolynomial.C (beta j))

theorem optionTailAffineMap_injective {K : Type*} [Field K]
    (m : ℕ) {alpha beta : Fin m → K}
    (halpha : ∀ j, alpha j ≠ 0) :
    Function.Injective (optionTailAffineMap m alpha beta) := by
  have hcomp :
      (optionTailAffineMapInv m alpha beta).comp (optionTailAffineMap m alpha beta) =
        AlgHom.id K _ := by
    apply MvPolynomial.algHom_ext
    intro o
    rcases o with (_ | j)
    · simp [optionTailAffineMap, optionTailAffineMapInv]
    · simp [optionTailAffineMap, optionTailAffineMapInv]
      rw [← mul_assoc, ← MvPolynomial.C_mul]
      simp [halpha j]
  apply Function.LeftInverse.injective
  intro P
  change optionTailAffineMapInv m alpha beta
      (optionTailAffineMap m alpha beta P) = P
  exact AlgHom.congr_fun hcomp P

def optionTailScaleMap {K : Type*} [Field K] (m : ℕ) :
    MvPolynomial (Option (Fin m)) K →ₐ[K] MvPolynomial (Option (Fin m)) K :=
  (MvPolynomial.optionEquivRight K (Fin m)).symm.toAlgHom.comp
    ((mvPolynomialDiagonalScaleRing
      (fun j : Fin m => (Polynomial.X : Polynomial K) ^ ((j : ℕ) + 1))).restrictScalars K |>.comp
        (MvPolynomial.optionEquivRight K (Fin m)).toAlgHom)

theorem optionTailScaleMap_none {K : Type*} [Field K] (m : ℕ) :
    optionTailScaleMap (K := K) m (MvPolynomial.X none) = MvPolynomial.X none := by
  simp [optionTailScaleMap, mvPolynomialDiagonalScaleRing]

theorem optionTailScaleMap_some {K : Type*} [Field K]
    (m : ℕ) (j : Fin m) :
    optionTailScaleMap (K := K) m (MvPolynomial.X (some j)) =
      MvPolynomial.X none ^ ((j : ℕ) + 1) * MvPolynomial.X (some j) := by
  simp [optionTailScaleMap, mvPolynomialDiagonalScaleRing]

theorem optionTailScaleMap_injective {K : Type*} [Field K] (m : ℕ) :
    Function.Injective (optionTailScaleMap (K := K) m) := by
  let E := MvPolynomial.optionEquivRight K (Fin m)
  let c : Fin m → Polynomial K :=
    fun j => Polynomial.X ^ ((j : ℕ) + 1)
  intro P Q hPQ
  apply sub_eq_zero.mp
  by_contra hne
  have hE : E (P - Q) ≠ 0 := by
    intro hzero
    apply hne
    apply E.injective
    simpa using hzero
  have hc : ∀ j, c j ≠ 0 := by
    intro j
    simp [c]
  have hscale : mvPolynomialDiagonalScaleRing c (E (P - Q)) ≠ 0 :=
    mvPolynomialDiagonalScaleRing_ne_zero c hc hE
  apply hscale
  apply E.symm.injective
  have hmap : optionTailScaleMap (K := K) m (P - Q) = 0 := by
    rw [map_sub, hPQ, sub_self]
  simpa [optionTailScaleMap, E, c] using hmap

def weightedScaleAffineMap {K : Type*} [Field K]
    (m : ℕ) (alpha beta : Fin m → K) :
    MvPolynomial (Option (Fin m)) K →ₐ[K] MvPolynomial (Option (Fin m)) K :=
  (optionTailAffineMap m alpha beta).comp (optionTailScaleMap m)

theorem weightedScaleAffineMap_injective {K : Type*} [Field K]
    (m : ℕ) {alpha beta : Fin m → K}
    (halpha : ∀ j, alpha j ≠ 0) :
    Function.Injective (weightedScaleAffineMap m alpha beta) := by
  intro P Q hPQ
  apply optionTailScaleMap_injective m
  apply optionTailAffineMap_injective m halpha
  simpa [weightedScaleAffineMap] using hPQ

theorem weightedScaleAffineMap_none {K : Type*} [Field K]
    (m : ℕ) (alpha beta : Fin m → K) :
    weightedScaleAffineMap m alpha beta (MvPolynomial.X none) =
      MvPolynomial.X none := by
  simp [weightedScaleAffineMap, optionTailScaleMap_none, optionTailAffineMap]

theorem weightedScaleAffineMap_some {K : Type*} [Field K]
    (m : ℕ) (alpha beta : Fin m → K)
    (j : Fin m) :
    weightedScaleAffineMap m alpha beta (MvPolynomial.X (some j)) =
      MvPolynomial.X none ^ ((j : ℕ) + 1) *
        (MvPolynomial.C (alpha j) * MvPolynomial.X (some j) +
          MvPolynomial.C (beta j)) := by
  rw [weightedScaleAffineMap, AlgHom.comp_apply, optionTailScaleMap_some]
  simp [optionTailAffineMap]

def gammaPoleScaleAndHarmonicComplexEval (m : ℕ) :
    MvPolynomial (Option (Fin m)) ℂ →+* NatGerm :=
  (gammaPoleScaleAndHarmonicEval m).comp
    (MvPolynomial.map (algebraMap ℂ GammaPoleRationalBase))

theorem gammaPoleScaleAndHarmonicComplexEval_injective (m : ℕ) :
    Function.Injective (gammaPoleScaleAndHarmonicComplexEval m) := by
  exact (gammaPoleScaleAndHarmonicEval_injective m).comp
    (MvPolynomial.map_injective (algebraMap ℂ GammaPoleRationalBase)
      (FaithfulSMul.algebraMap_injective ℂ GammaPoleRationalBase))

def gammaPoleScaleAndLogCoefficientFamily (m : ℕ) : Option (Fin m) → NatGerm
  | none => reciprocalSignedFactorialGerm
  | some j => gammaPoleLogCoefficientGerm (j : ℕ)

def gammaPoleScaleAndLogCoefficientEval (m : ℕ) :
    MvPolynomial (Option (Fin m)) ℂ →+* NatGerm :=
  MvPolynomial.eval₂Hom complexNatGerm (gammaPoleScaleAndLogCoefficientFamily m)

theorem gammaPoleScaleAndLogCoefficientEval_eq_comp (m : ℕ) :
    gammaPoleScaleAndLogCoefficientEval m =
      (gammaPoleScaleAndHarmonicComplexEval m).comp
        (weightedScaleAffineMap m
          (fun j => gammaPoleLogSlope (j : ℕ))
          (fun j => gammaPoleLogConstant (j : ℕ))).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [gammaPoleScaleAndLogCoefficientEval,
      gammaPoleScaleAndHarmonicComplexEval,
      gammaPoleScaleAndHarmonicEval, complexNatGerm]
  · intro o
    rcases o with (_ | j)
    · simp [gammaPoleScaleAndLogCoefficientEval,
        gammaPoleScaleAndLogCoefficientFamily,
        gammaPoleScaleAndHarmonicComplexEval,
        gammaPoleScaleAndHarmonicEval,
        gammaPoleScaleAndHarmonicFamily,
        weightedScaleAffineMap_none]
    · change (gammaPoleScaleAndLogCoefficientEval m) (MvPolynomial.X (some j)) =
        (gammaPoleScaleAndHarmonicComplexEval m)
          (weightedScaleAffineMap m
            (fun j => gammaPoleLogSlope (j : ℕ))
            (fun j => gammaPoleLogConstant (j : ℕ)) (MvPolynomial.X (some j)))
      have hbase (c : ℂ) :
          algebraMap ℂ NatGerm c = ratNatEval (RatFunc.C c) := rfl
      rw [weightedScaleAffineMap_some]
      simp [gammaPoleScaleAndLogCoefficientEval,
        gammaPoleScaleAndLogCoefficientFamily,
        gammaPoleScaleAndHarmonicComplexEval,
        gammaPoleScaleAndHarmonicEval,
        gammaPoleScaleAndHarmonicFamily,
        gammaPoleLogCoefficientGerm, hbase]

theorem gammaPoleScaleAndLogCoefficientEval_injective (m : ℕ) :
    Function.Injective (gammaPoleScaleAndLogCoefficientEval m) := by
  rw [gammaPoleScaleAndLogCoefficientEval_eq_comp]
  exact (gammaPoleScaleAndHarmonicComplexEval_injective m).comp
    (weightedScaleAffineMap_injective m
      (fun j => gammaPoleLogSlope_ne_zero (j : ℕ)))

theorem algebraicIndependent_gammaPoleScaleAndLogCoefficientFamily (m : ℕ) :
    AlgebraicIndependent ℂ (gammaPoleScaleAndLogCoefficientFamily m) := by
  rw [algebraicIndependent_iff_injective_aeval]
  simpa [gammaPoleScaleAndLogCoefficientEval, MvPolynomial.aeval_def] using!
    gammaPoleScaleAndLogCoefficientEval_injective m

/-- Extend a tail coordinate map by fixing one distinguished head variable. -/
def optionHeadLiftAlgHom {K iota : Type*} [CommSemiring K]
    (f : MvPolynomial iota K →ₐ[K] MvPolynomial iota K) :
    MvPolynomial (Option iota) K →ₐ[K] MvPolynomial (Option iota) K :=
  (MvPolynomial.optionEquivLeft K iota).symm.toAlgHom.comp
    ((Polynomial.mapAlgHom f).comp
      (MvPolynomial.optionEquivLeft K iota).toAlgHom)

theorem optionHeadLiftAlgHom_injective {K iota : Type*} [CommSemiring K]
    {f : MvPolynomial iota K →ₐ[K] MvPolynomial iota K}
    (hf : Function.Injective f) :
    Function.Injective (optionHeadLiftAlgHom f) := by
  exact (MvPolynomial.optionEquivLeft K iota).symm.injective.comp
    ((Polynomial.map_injective f.toRingHom hf).comp
      (MvPolynomial.optionEquivLeft K iota).injective)

theorem optionHeadLiftAlgHom_none {K iota : Type*} [CommSemiring K]
    (f : MvPolynomial iota K →ₐ[K] MvPolynomial iota K) :
    optionHeadLiftAlgHom f (MvPolynomial.X none) = MvPolynomial.X none := by
  simp [optionHeadLiftAlgHom]

theorem optionHeadLiftAlgHom_C {K iota : Type*} [CommSemiring K]
    (f : MvPolynomial iota K →ₐ[K] MvPolynomial iota K) (c : K) :
    optionHeadLiftAlgHom f (MvPolynomial.C c) = MvPolynomial.C c := by
  simp [optionHeadLiftAlgHom]

theorem optionHeadLiftAlgHom_some {K iota : Type*} [CommSemiring K]
    (f : MvPolynomial iota K →ₐ[K] MvPolynomial iota K) (i : iota) :
    optionHeadLiftAlgHom f (MvPolynomial.X (some i)) =
      MvPolynomial.rename some (f (MvPolynomial.X i)) := by
  simp [optionHeadLiftAlgHom]
  change Polynomial.aevalTower (MvPolynomial.rename some) (MvPolynomial.X none)
      (Polynomial.C (f (MvPolynomial.X i))) = _
  simp

def gammaPoleScaleAndLogDerivativeFamily (m : ℕ) : Option (Fin m) → NatGerm
  | none => reciprocalSignedFactorialGerm
  | some j => gammaPoleLogDerivativeGerm (j : ℕ)

def gammaPoleScaleAndLogDerivativeEval (m : ℕ) :
    MvPolynomial (Option (Fin m)) ℂ →+* NatGerm :=
  MvPolynomial.eval₂Hom complexNatGerm (gammaPoleScaleAndLogDerivativeFamily m)

theorem gammaPoleScaleAndLogDerivativeEval_eq_comp (m : ℕ) :
    gammaPoleScaleAndLogDerivativeEval m =
      (gammaPoleScaleAndLogCoefficientEval m).comp
        (optionTailAffineMap m
          (fun j => (((j : ℕ) + 1).factorial : ℂ)) 0).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [gammaPoleScaleAndLogDerivativeEval,
      gammaPoleScaleAndLogCoefficientEval, complexNatGerm]
  · intro o
    rcases o with (_ | j)
    · simp [gammaPoleScaleAndLogDerivativeEval,
        gammaPoleScaleAndLogDerivativeFamily,
        gammaPoleScaleAndLogCoefficientEval,
        gammaPoleScaleAndLogCoefficientFamily,
        optionTailAffineMap]
    · rw [RingHom.comp_apply]
      simp only [gammaPoleScaleAndLogDerivativeEval, MvPolynomial.eval₂Hom_X',
        gammaPoleScaleAndLogDerivativeFamily]
      change gammaPoleLogDerivativeGerm (j : ℕ) =
        (gammaPoleScaleAndLogCoefficientEval m)
          (optionTailAffineMap m
            (fun j => (((j : ℕ) + 1).factorial : ℂ)) 0
            (MvPolynomial.X (some j)))
      rw [gammaPoleLogDerivativeGerm_eq_factorial_mul]
      simp [gammaPoleScaleAndLogCoefficientEval,
        gammaPoleScaleAndLogCoefficientFamily, optionTailAffineMap]

theorem gammaPoleScaleAndLogDerivativeEval_injective (m : ℕ) :
    Function.Injective (gammaPoleScaleAndLogDerivativeEval m) := by
  rw [gammaPoleScaleAndLogDerivativeEval_eq_comp]
  exact (gammaPoleScaleAndLogCoefficientEval_injective m).comp
    (optionTailAffineMap_injective m (fun j =>
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero ((j : ℕ) + 1))))

theorem algebraicIndependent_gammaPoleScaleAndLogDerivativeFamily (m : ℕ) :
    AlgebraicIndependent ℂ (gammaPoleScaleAndLogDerivativeFamily m) := by
  rw [algebraicIndependent_iff_injective_aeval]
  simpa [gammaPoleScaleAndLogDerivativeEval, MvPolynomial.aeval_def] using!
    gammaPoleScaleAndLogDerivativeEval_injective m

def gammaPoleRegularBellScale (n : ℕ) (j : Fin (n + 1)) : ℂ :=
  -((((j : ℕ) + 1).factorial : ℂ)⁻¹)

theorem gammaPoleRegularBellScale_ne_zero (n : ℕ) (j : Fin (n + 1)) :
    gammaPoleRegularBellScale n j ≠ 0 := by
  exact neg_ne_zero.mpr (inv_ne_zero
    (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero ((j : ℕ) + 1))))

def scaledBellCoefficientAlgHom (n : ℕ) (c : Fin (n + 1) → ℂ) :
    MvPolynomial (Fin (n + 1)) ℂ →ₐ[ℂ] MvPolynomial (Fin (n + 1)) ℂ :=
  MvPolynomial.aeval fun j =>
    MvPolynomial.C (c j) * bellAt n ((j : ℕ) + 1) j.isLt

theorem scaledBellCoefficientAlgHom_toRingHom (n : ℕ) (c : Fin (n + 1) → ℂ) :
    (scaledBellCoefficientAlgHom n c).toRingHom = scaledBellCoefficientMap n c := by
  exact (scaledBellCoefficientMap_eq_aeval n c).symm

theorem scaledBellCoefficientAlgHom_injective (n : ℕ)
    {c : Fin (n + 1) → ℂ} (hc : ∀ j, c j ≠ 0) :
    Function.Injective (scaledBellCoefficientAlgHom n c) := by
  intro P Q hPQ
  apply scaledBellCoefficientMap_injective n hc
  have h := hPQ
  change (scaledBellCoefficientAlgHom n c).toRingHom P =
    (scaledBellCoefficientAlgHom n c).toRingHom Q at h
  rwa [scaledBellCoefficientAlgHom_toRingHom] at h

def gammaPoleScaleAndRegularCoefficientFamily (n : ℕ) :
    Option (Fin (n + 1)) → NatGerm
  | none => reciprocalSignedFactorialGerm
  | some j => gammaPoleRegularCoefficientGerm (j : ℕ)

def gammaPoleScaleAndRegularCoefficientEval (n : ℕ) :
    MvPolynomial (Option (Fin (n + 1))) ℂ →+* NatGerm :=
  MvPolynomial.eval₂Hom complexNatGerm (gammaPoleScaleAndRegularCoefficientFamily n)

theorem gammaPoleScaleAndRegularCoefficientEval_eq_comp (n : ℕ) :
    gammaPoleScaleAndRegularCoefficientEval n =
      (gammaPoleScaleAndLogDerivativeEval (n + 1)).comp
        (optionHeadLiftAlgHom
          (scaledBellCoefficientAlgHom n (gammaPoleRegularBellScale n))).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [gammaPoleScaleAndRegularCoefficientEval,
      gammaPoleScaleAndLogDerivativeEval, complexNatGerm]
  · intro o
    rcases o with (_ | j)
    · simp [gammaPoleScaleAndRegularCoefficientEval,
        gammaPoleScaleAndRegularCoefficientFamily,
        gammaPoleScaleAndLogDerivativeEval,
        gammaPoleScaleAndLogDerivativeFamily,
        optionHeadLiftAlgHom_none]
    · rw [RingHom.comp_apply]
      simp only [gammaPoleScaleAndRegularCoefficientEval, MvPolynomial.eval₂Hom_X',
        gammaPoleScaleAndRegularCoefficientFamily]
      change gammaPoleRegularCoefficientGerm (j : ℕ) =
        (gammaPoleScaleAndLogDerivativeEval (n + 1))
          (optionHeadLiftAlgHom
            (scaledBellCoefficientAlgHom n (gammaPoleRegularBellScale n))
            (MvPolynomial.X (some j)))
      rw [optionHeadLiftAlgHom_some]
      simp [gammaPoleScaleAndLogDerivativeEval,
        gammaPoleRegularCoefficientGerm,
        gammaPoleRegularBellScale,
        scaledBellCoefficientAlgHom,
        bellAt, Function.comp_def]
      rw [MvPolynomial.eval₂_rename]
      simp [gammaPoleScaleAndLogDerivativeFamily,
        MvPolynomial.aeval_def, Function.comp_def]
      change complexNatGerm _ *
        MvPolynomial.eval₂ complexNatGerm
          (fun i : Fin ((j : ℕ) + 1) => gammaPoleLogDerivativeGerm (i : ℕ))
          (bellCore ((j : ℕ) + 1)) = _
      rfl

theorem gammaPoleScaleAndRegularCoefficientEval_injective (n : ℕ) :
    Function.Injective (gammaPoleScaleAndRegularCoefficientEval n) := by
  rw [gammaPoleScaleAndRegularCoefficientEval_eq_comp]
  exact (gammaPoleScaleAndLogDerivativeEval_injective (n + 1)).comp
    (optionHeadLiftAlgHom_injective
      (scaledBellCoefficientAlgHom_injective n (gammaPoleRegularBellScale_ne_zero n)))

theorem algebraicIndependent_gammaPoleScaleAndRegularCoefficientFamily (n : ℕ) :
    AlgebraicIndependent ℂ (gammaPoleScaleAndRegularCoefficientFamily n) := by
  rw [algebraicIndependent_iff_injective_aeval]
  simpa [gammaPoleScaleAndRegularCoefficientEval, MvPolynomial.aeval_def] using!
    gammaPoleScaleAndRegularCoefficientEval_injective n

def gammaPoleScaleAndUnitPositiveCoefficientFamilyFin (n : ℕ) :
    Option (Fin (n + 1)) → NatGerm
  | none => reciprocalSignedFactorialGerm
  | some j => gammaPoleUnitPositiveCoefficientGerm (j : ℕ)

def gammaPoleScaleAndUnitPositiveCoefficientEvalFin (n : ℕ) :
    MvPolynomial (Option (Fin (n + 1))) ℂ →+* NatGerm :=
  MvPolynomial.eval₂Hom complexNatGerm
    (gammaPoleScaleAndUnitPositiveCoefficientFamilyFin n)

theorem gammaPoleScaleAndUnitPositiveCoefficientEvalFin_eq_comp (n : ℕ) :
    gammaPoleScaleAndUnitPositiveCoefficientEvalFin n =
      (gammaPoleScaleAndRegularCoefficientEval n).comp
        (optionTailAffineMap (n + 1) (fun _ => -1) 0).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [gammaPoleScaleAndUnitPositiveCoefficientEvalFin,
      gammaPoleScaleAndRegularCoefficientEval, complexNatGerm]
  · intro o
    rcases o with (_ | j)
    · simp [gammaPoleScaleAndUnitPositiveCoefficientEvalFin,
        gammaPoleScaleAndUnitPositiveCoefficientFamilyFin,
        gammaPoleScaleAndRegularCoefficientEval,
        gammaPoleScaleAndRegularCoefficientFamily,
        optionTailAffineMap]
    · rw [RingHom.comp_apply]
      simp only [gammaPoleScaleAndUnitPositiveCoefficientEvalFin,
        MvPolynomial.eval₂Hom_X', gammaPoleScaleAndUnitPositiveCoefficientFamilyFin]
      change gammaPoleUnitPositiveCoefficientGerm (j : ℕ) =
        (gammaPoleScaleAndRegularCoefficientEval n)
          (optionTailAffineMap (n + 1) (fun _ => -1) 0
            (MvPolynomial.X (some j)))
      rw [gammaPoleUnitPositiveCoefficientGerm,
        actualGammaPoleRegularCoefficientGerm_eq]
      simp [gammaPoleScaleAndRegularCoefficientEval,
        gammaPoleScaleAndRegularCoefficientFamily,
        optionTailAffineMap]

theorem gammaPoleScaleAndUnitPositiveCoefficientEvalFin_injective (n : ℕ) :
    Function.Injective (gammaPoleScaleAndUnitPositiveCoefficientEvalFin n) := by
  rw [gammaPoleScaleAndUnitPositiveCoefficientEvalFin_eq_comp]
  exact (gammaPoleScaleAndRegularCoefficientEval_injective n).comp
    (optionTailAffineMap_injective (n + 1) (fun _ => neg_ne_zero.mpr one_ne_zero))

theorem algebraicIndependent_gammaPoleScaleAndUnitPositiveCoefficientFamilyFin (n : ℕ) :
    AlgebraicIndependent ℂ (gammaPoleScaleAndUnitPositiveCoefficientFamilyFin n) := by
  rw [algebraicIndependent_iff_injective_aeval]
  simpa [gammaPoleScaleAndUnitPositiveCoefficientEvalFin, MvPolynomial.aeval_def] using!
    gammaPoleScaleAndUnitPositiveCoefficientEvalFin_injective n

def optionNatValue : Option ℕ → ℕ
  | none => 0
  | some n => n

def optionFinInclude (n : ℕ) : Option (Fin (n + 1)) → Option ℕ :=
  Option.map fun j => (j : ℕ)

theorem algebraicIndependent_optionNat_of_prefix
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (x : Option ℕ → A)
    (hprefix : ∀ n, AlgebraicIndependent R (x ∘ optionFinInclude n)) :
    AlgebraicIndependent R x := by
  apply algebraicIndependent_of_finite_type
  intro t ht
  have hfinite : (optionNatValue '' (t : Set (Option ℕ))).Finite :=
    ht.image optionNatValue
  obtain ⟨m, hm⟩ := hfinite.bddAbove
  have hbound (q : t) : optionNatValue q.1 ≤ m :=
    hm ⟨q.1, q.2, rfl⟩
  let embed : t → Option (Fin (m + 1)) := fun q =>
    match hq : q.1 with
    | none => none
    | some k => some ⟨k, Nat.lt_succ_of_le (by
        have hb := hbound q
        simpa [optionNatValue, hq] using hb)⟩
  have hinclude (q : t) : optionFinInclude m (embed q) = q.1 := by
    simp only [optionFinInclude]
    dsimp only [embed]
    split <;> simp_all
  have hembed : Function.Injective embed := by
    intro q r hqr
    apply Subtype.ext
    rw [← hinclude q, ← hinclude r, hqr]
  have hsub := (hprefix m).comp embed hembed
  have hfamily : (x ∘ optionFinInclude m) ∘ embed = fun q : t => x q.1 := by
    funext q
    simp [Function.comp_def, hinclude]
  rw [hfamily] at hsub
  exact hsub

def gammaPoleScaleAndUnitPositiveCoefficientFamily : Option ℕ → NatGerm
  | none => reciprocalSignedFactorialGerm
  | some j => gammaPoleUnitPositiveCoefficientGerm j

theorem algebraicIndependent_gammaPoleScaleAndUnitPositiveCoefficientFamily :
    AlgebraicIndependent ℂ gammaPoleScaleAndUnitPositiveCoefficientFamily := by
  apply algebraicIndependent_optionNat_of_prefix
  intro n
  have h := algebraicIndependent_gammaPoleScaleAndUnitPositiveCoefficientFamilyFin n
  have hfamily : gammaPoleScaleAndUnitPositiveCoefficientFamily ∘ optionFinInclude n =
      gammaPoleScaleAndUnitPositiveCoefficientFamilyFin n := by
    funext o
    rcases o with (_ | j) <;> rfl
  rw [hfamily]
  exact h

def gammaPoleScaleAndUnitPositiveCoefficientEval :
    MvPolynomial (Option ℕ) ℂ →+* NatGerm :=
  MvPolynomial.eval₂Hom complexNatGerm
    gammaPoleScaleAndUnitPositiveCoefficientFamily

theorem gammaPoleScaleAndUnitPositiveCoefficientEval_injective :
    Function.Injective gammaPoleScaleAndUnitPositiveCoefficientEval := by
  have h := algebraicIndependent_iff_injective_aeval.mp
    algebraicIndependent_gammaPoleScaleAndUnitPositiveCoefficientFamily
  simpa [gammaPoleScaleAndUnitPositiveCoefficientEval,
    MvPolynomial.aeval_def] using! h

def gammaPoleScaleAndReciprocalUnitCoefficientFamily : Option ℕ → NatGerm
  | none => reciprocalSignedFactorialGerm
  | some j => gammaPoleReciprocalUnitCoefficientGerm j

def gammaPoleScaleAndReciprocalUnitCoefficientEval :
    MvPolynomial (Option ℕ) ℂ →+* NatGerm :=
  MvPolynomial.eval₂Hom complexNatGerm
    gammaPoleScaleAndReciprocalUnitCoefficientFamily

theorem gammaPoleScaleAndReciprocalUnitCoefficientEval_eq_comp :
    gammaPoleScaleAndReciprocalUnitCoefficientEval =
      gammaPoleScaleAndUnitPositiveCoefficientEval.comp
        (optionHeadLiftAlgHom universalUnitInverseCoefficientMap).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [gammaPoleScaleAndReciprocalUnitCoefficientEval,
      gammaPoleScaleAndUnitPositiveCoefficientEval, complexNatGerm]
  · intro o
    rcases o with (_ | j)
    · simp [gammaPoleScaleAndReciprocalUnitCoefficientEval,
        gammaPoleScaleAndReciprocalUnitCoefficientFamily,
        gammaPoleScaleAndUnitPositiveCoefficientEval,
        gammaPoleScaleAndUnitPositiveCoefficientFamily,
        optionHeadLiftAlgHom_none]
    · rw [RingHom.comp_apply]
      simp only [gammaPoleScaleAndReciprocalUnitCoefficientEval,
        MvPolynomial.eval₂Hom_X', gammaPoleScaleAndReciprocalUnitCoefficientFamily]
      change gammaPoleReciprocalUnitCoefficientGerm j =
        gammaPoleScaleAndUnitPositiveCoefficientEval
          (optionHeadLiftAlgHom universalUnitInverseCoefficientMap
            (MvPolynomial.X (some j)))
      rw [optionHeadLiftAlgHom_some]
      simp [gammaPoleReciprocalUnitCoefficientGerm,
        gammaPoleScaleAndUnitPositiveCoefficientEval,
        universalUnitInverseCoefficientMap,
        unitInverseCoefficientOfCoefficients_eq_aeval]
      rw [MvPolynomial.eval₂_rename]
      simp [gammaPoleScaleAndUnitPositiveCoefficientFamily,
        MvPolynomial.aeval_def, Function.comp_def]
      change MvPolynomial.eval₂ complexNatGerm
        gammaPoleUnitPositiveCoefficientGerm (universalUnitInverseCoefficient j) = _
      rfl

theorem gammaPoleScaleAndReciprocalUnitCoefficientEval_injective :
    Function.Injective gammaPoleScaleAndReciprocalUnitCoefficientEval := by
  rw [gammaPoleScaleAndReciprocalUnitCoefficientEval_eq_comp]
  exact gammaPoleScaleAndUnitPositiveCoefficientEval_injective.comp
    (optionHeadLiftAlgHom_injective universalUnitInverseCoefficientMap_injective)

theorem algebraicIndependent_gammaPoleScaleAndReciprocalUnitCoefficientFamily :
    AlgebraicIndependent ℂ gammaPoleScaleAndReciprocalUnitCoefficientFamily := by
  rw [algebraicIndependent_iff_injective_aeval]
  simpa [gammaPoleScaleAndReciprocalUnitCoefficientEval,
    MvPolynomial.aeval_def] using!
      gammaPoleScaleAndReciprocalUnitCoefficientEval_injective

/-- The reciprocal factorial scale together with every nonlinear inverse-Gamma branch
coefficient. -/
def gammaPoleScaleAndInverseBranchCoefficientFamily : Option ℕ → NatGerm
  | none => reciprocalSignedFactorialGerm
  | some j => gammaInversePoleBranchCoefficientGerm j

def gammaPoleScaleAndInverseBranchCoefficientEval :
    MvPolynomial (Option ℕ) ℂ →+* NatGerm :=
  MvPolynomial.eval₂Hom complexNatGerm
    gammaPoleScaleAndInverseBranchCoefficientFamily

theorem gammaPoleScaleAndInverseBranchCoefficientEval_eq_comp :
    gammaPoleScaleAndInverseBranchCoefficientEval =
      gammaPoleScaleAndReciprocalUnitCoefficientEval.comp
        (optionHeadLiftAlgHom universalTangentInverseCoefficientMap).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [gammaPoleScaleAndInverseBranchCoefficientEval,
      gammaPoleScaleAndReciprocalUnitCoefficientEval, complexNatGerm]
  · intro o
    rcases o with (_ | j)
    · simp [gammaPoleScaleAndInverseBranchCoefficientEval,
        gammaPoleScaleAndInverseBranchCoefficientFamily,
        gammaPoleScaleAndReciprocalUnitCoefficientEval,
        gammaPoleScaleAndReciprocalUnitCoefficientFamily,
        optionHeadLiftAlgHom_none]
    · rw [RingHom.comp_apply]
      simp only [gammaPoleScaleAndInverseBranchCoefficientEval,
        MvPolynomial.eval₂Hom_X', gammaPoleScaleAndInverseBranchCoefficientFamily]
      change gammaInversePoleBranchCoefficientGerm j =
        gammaPoleScaleAndReciprocalUnitCoefficientEval
          (optionHeadLiftAlgHom universalTangentInverseCoefficientMap
            (MvPolynomial.X (some j)))
      rw [optionHeadLiftAlgHom_some]
      simp [gammaInversePoleBranchCoefficientGerm,
        gammaPoleScaleAndReciprocalUnitCoefficientEval,
        universalTangentInverseCoefficientMap,
        tangentInverseCoefficientOfCoefficients_eq_aeval]
      rw [MvPolynomial.eval₂_rename]
      simp [gammaPoleScaleAndReciprocalUnitCoefficientFamily,
        MvPolynomial.aeval_def, Function.comp_def]
      change MvPolynomial.eval₂ complexNatGerm
        gammaPoleReciprocalUnitCoefficientGerm
          (universalTangentInverseCoefficient j) = _
      rfl

theorem gammaPoleScaleAndInverseBranchCoefficientEval_injective :
    Function.Injective gammaPoleScaleAndInverseBranchCoefficientEval := by
  rw [gammaPoleScaleAndInverseBranchCoefficientEval_eq_comp]
  exact gammaPoleScaleAndReciprocalUnitCoefficientEval_injective.comp
    (optionHeadLiftAlgHom_injective universalTangentInverseCoefficientMap_injective)

/-- Joint countable freeness of the factorial scale and all nonlinear normalized inverse-Gamma
pole-branch coefficients. -/
theorem algebraicIndependent_gammaPoleScaleAndInverseBranchCoefficientFamily :
    AlgebraicIndependent ℂ gammaPoleScaleAndInverseBranchCoefficientFamily := by
  rw [algebraicIndependent_iff_injective_aeval]
  simpa [gammaPoleScaleAndInverseBranchCoefficientEval,
    MvPolynomial.aeval_def] using!
      gammaPoleScaleAndInverseBranchCoefficientEval_injective

end

end GaloisForLFunctions
