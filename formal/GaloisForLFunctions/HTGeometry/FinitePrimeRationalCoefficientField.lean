import GaloisForLFunctions.HTGeometry.FinitePrimeCoefficientField
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental

/-!
# Adjoining the independent Dirichlet coordinate to the finite-prime field

The intrinsic finite-prime coefficient field lives in the fraction field of arithmetic
functions.  This module adjoins one independent rational coordinate, producing the formal
coefficient field `E_fin(s)`.  Algebraic independence over the finite-prime field survives this
extension: the new coordinate is transcendental over every family of constant arithmetic
fractions, and passage from polynomials to rational functions is algebraic.

The ambient `RatFunc arithmeticFunctionFractionField` is a formal algebraic carrier.  A separate
analytic realization may later send its coordinate to the upper-end variable and its constant
coefficients to meromorphic L-series germs.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

noncomputable section

/-- Adding one formal rational coordinate to any algebraically independent family of constants
preserves independence over the polynomial coordinate algebra. -/
theorem algebraicIndependent_ratFuncConstants_over_coordinateAdjoin
    {K F I : Type*} [Field K] [Field F] [Algebra K F]
    (x : I → F) (hx : AlgebraicIndependent K x) :
    AlgebraicIndependent
      (Algebra.adjoin K
        (Set.range (fun _ : Unit => (RatFunc.X : RatFunc F))))
      (fun i => algebraMap F (RatFunc F) (x i)) := by
  let A := RatFunc F
  let xR : I → A := fun i => algebraMap F A (x i)
  have hxR : AlgebraicIndependent K xR :=
    hx.map' (f := IsScalarTower.toAlgHom K F A) (algebraMap F A).injective
  let B : Subalgebra K A := (IsScalarTower.toAlgHom K F A).range
  have hle : Algebra.adjoin K (Set.range xR) ≤ B := by
    rw [Algebra.adjoin_le_iff]
    rintro y ⟨i, rfl⟩
    exact ⟨x i, rfl⟩
  let e := AlgEquiv.ofInjective (IsScalarTower.toAlgHom K F A)
    (algebraMap F A).injective
  let _ : Algebra (Algebra.adjoin K (Set.range xR)) F :=
    (e.symm.toAlgHom.comp (Subalgebra.inclusion hle)).toAlgebra
  haveI : IsScalarTower (Algebra.adjoin K (Set.range xR)) F A :=
    .of_algebraMap_eq fun y => show _ = (e (e.symm _)).1 by simp
  have htrans : Transcendental (Algebra.adjoin K (Set.range xR))
      (RatFunc.X : A) :=
    (RatFunc.transcendental_X (K := F)).restrictScalars
      (e.symm.injective.comp (Subalgebra.inclusion_injective hle))
  have hopt : AlgebraicIndependent K
      (fun o : Option I => o.elim (RatFunc.X : A) xR) :=
    (hxR.option_iff_transcendental (RatFunc.X : A)).mpr htrans
  have hjoint : AlgebraicIndependent K
      (Sum.elim xR (fun _ : Unit => (RatFunc.X : A))) := by
    let eqv : I ⊕ Unit ≃ Option I :=
      { toFun := fun z => Sum.elim some (fun _ => none) z
        invFun := fun o => o.elim (Sum.inr ()) Sum.inl
        left_inv := by
          intro z
          rcases z with i | u
          · rfl
          · rcases u
            rfl
        right_inv := by
          intro o
          rcases o with _ | i <;> rfl }
    have heq : (Sum.elim xR (fun _ : Unit => (RatFunc.X : A))) =
        (fun z => (fun o : Option I => o.elim (RatFunc.X : A) xR) (eqv z)) := by
      funext z
      rcases z with i | u
      · rfl
      · rcases u
        rfl
    rw [heq]
    exact hopt.comp eqv eqv.injective
  simpa only [xR, A] using (AlgebraicIndependent.sumElim_iff.mp hjoint).2

/-- Finite-prime arithmetic fractions with one independent
rational coordinate adjoined. -/
abbrev finitePrimeRationalCoefficientField :=
  RatFunc finitePrimeCoefficientField

/-- Formal rational functions whose constants are arbitrary arithmetic-function fractions. -/
abbrev arithmeticFunctionRationalCoordinateField :=
  RatFunc arithmeticFunctionFractionField

/-- Coefficientwise inclusion of finite-prime polynomials into arbitrary arithmetic-fraction
polynomials. -/
noncomputable def finitePrimeCoefficientPolynomialMap :
    Polynomial finitePrimeCoefficientField →ₐ[finitePrimeCoefficientField]
      Polynomial arithmeticFunctionFractionField :=
  Polynomial.mapAlgHom
    (IsScalarTower.toAlgHom finitePrimeCoefficientField
      finitePrimeCoefficientField arithmeticFunctionFractionField)

theorem finitePrimeCoefficientPolynomialMap_injective :
    Function.Injective finitePrimeCoefficientPolynomialMap := by
  exact Polynomial.map_injective _
    (FaithfulSMul.algebraMap_injective finitePrimeCoefficientField
      arithmeticFunctionFractionField)

/-- Coefficientwise faithful inclusion of `E_fin(s)` into the formal rational-coordinate field
over all arithmetic fractions. -/
noncomputable def finitePrimeRationalCoefficientFieldToFormalRatFunc :
    finitePrimeRationalCoefficientField →ₐ[finitePrimeCoefficientField]
      arithmeticFunctionRationalCoordinateField :=
  RatFunc.mapAlgHom finitePrimeCoefficientPolynomialMap
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      finitePrimeCoefficientPolynomialMap_injective)

theorem finitePrimeRationalCoefficientFieldToFormalRatFunc_injective :
    Function.Injective finitePrimeRationalCoefficientFieldToFormalRatFunc := by
  exact RatFunc.map_injective finitePrimeCoefficientPolynomialMap
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      finitePrimeCoefficientPolynomialMap_injective)
    finitePrimeCoefficientPolynomialMap_injective

/-- The formal rational-coordinate field over all arithmetic fractions is an algebra over the
finite-prime rational coefficient field. -/
noncomputable instance finitePrimeRationalCoefficientFieldAlgebra :
    Algebra finitePrimeRationalCoefficientField
      arithmeticFunctionRationalCoordinateField :=
  finitePrimeRationalCoefficientFieldToFormalRatFunc.toAlgebra

/-- **Purely transcendental base extension.**  A constant family algebraically independent over
the finite-prime coefficient field remains algebraically independent after adjoining the formal
Dirichlet coordinate and passing to its rational function field. -/
theorem algebraicIndependent_constants_over_finitePrimeRationalCoefficientField
    {I : Type*} (x : I → arithmeticFunctionFractionField)
    (hx : AlgebraicIndependent finitePrimeCoefficientField x) :
    AlgebraicIndependent finitePrimeRationalCoefficientField
      (fun i => algebraMap arithmeticFunctionFractionField
        arithmeticFunctionRationalCoordinateField (x i)) := by
  let K := finitePrimeCoefficientField
  let F := arithmeticFunctionFractionField
  let A := arithmeticFunctionRationalCoordinateField
  let xR : I → A := fun i => algebraMap F A (x i)
  let R : Subalgebra K A := Algebra.adjoin K ({RatFunc.X} : Set A)
  have hR : AlgebraicIndependent R xR := by
    have h := algebraicIndependent_ratFuncConstants_over_coordinateAdjoin x hx
    have hrange : Set.range (fun _ : Unit => (RatFunc.X : A)) =
        ({RatFunc.X} : Set A) := by
      ext z
      constructor
      · rintro ⟨u, rfl⟩
        rfl
      · intro hz
        rw [Set.mem_singleton_iff] at hz
        exact ⟨(), hz.symm⟩
    rw [hrange] at h
    exact h
  have hX : Transcendental K (RatFunc.X : A) :=
    (RatFunc.transcendental_X (K := F)).restrictScalars
      (FaithfulSMul.algebraMap_injective K F)
  let eCoord : Polynomial K ≃ₐ[K] R :=
    Polynomial.algEquivOfTranscendental K (RatFunc.X : A) hX
  let _ : Algebra (Polynomial K) A :=
    ((Subalgebra.val R).comp eCoord.toAlgHom).toAlgebra
  have hPoly : AlgebraicIndependent (Polynomial K) xR := by
    apply hR.ringHom_of_comp_eq eCoord.symm.toRingHom (RingHom.id A)
    · exact eCoord.symm.surjective
    · exact Function.injective_id
    · ext r
      change ((eCoord (eCoord.symm r) : R) : A) = (r : A)
      rw [eCoord.apply_symm_apply]
  have hmapPoly : ∀ p : Polynomial K,
      algebraMap (Polynomial K) A p =
        algebraMap finitePrimeRationalCoefficientField A
          (algebraMap (Polynomial K) finitePrimeRationalCoefficientField p) := by
    have hmaps : (algebraMap (Polynomial K) A) =
        (finitePrimeRationalCoefficientFieldToFormalRatFunc.toRingHom.comp
          (algebraMap (Polynomial K) finitePrimeRationalCoefficientField)) := by
      apply Polynomial.ringHom_ext
      · intro c
        change ((eCoord (Polynomial.C c) : R) : A) =
          finitePrimeRationalCoefficientFieldToFormalRatFunc
            (algebraMap (Polynomial K) finitePrimeRationalCoefficientField
              (Polynomial.C c))
        have hleft : ((eCoord (Polynomial.C c) : R) : A) =
            algebraMap K A c := by
          rw [Polynomial.algEquivOfTranscendental_apply, Polynomial.aeval_C]
          rfl
        rw [hleft]
        rw [show Polynomial.C c = algebraMap K (Polynomial K) c by rfl,
          ← IsScalarTower.algebraMap_apply K (Polynomial K)
            finitePrimeRationalCoefficientField]
        exact (finitePrimeRationalCoefficientFieldToFormalRatFunc.commutes c).symm
      · change ((eCoord Polynomial.X : R) : A) =
          finitePrimeRationalCoefficientFieldToFormalRatFunc
            (algebraMap (Polynomial K) finitePrimeRationalCoefficientField Polynomial.X)
        rw [Polynomial.algEquivOfTranscendental_apply_X]
        change (RatFunc.X : A) =
          RatFunc.map finitePrimeCoefficientPolynomialMap
            (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
              finitePrimeCoefficientPolynomialMap_injective)
            (algebraMap (Polynomial K) finitePrimeRationalCoefficientField Polynomial.X)
        rw [show algebraMap (Polynomial K) finitePrimeRationalCoefficientField Polynomial.X =
          algebraMap (Polynomial K) finitePrimeRationalCoefficientField Polynomial.X /
            algebraMap (Polynomial K) finitePrimeRationalCoefficientField 1 by
            rw [map_one, div_one],
          RatFunc.map_apply_div]
        simp only [finitePrimeCoefficientPolynomialMap, Polynomial.coe_mapAlgHom, Polynomial.map_X,
          map_one, div_one, RatFunc.algebraMap_X]
    exact fun p => RingHom.congr_fun hmaps p
  haveI : IsScalarTower (Polynomial K) finitePrimeRationalCoefficientField A :=
    .of_algebraMap_eq hmapPoly
  letI : Algebra.IsAlgebraic (Polynomial K) finitePrimeRationalCoefficientField := by
    constructor
    intro z
    apply (IsFractionRing.isAlgebraic_iff (Polynomial K)
      finitePrimeRationalCoefficientField finitePrimeRationalCoefficientField).mpr
    exact isAlgebraic_algebraMap (R := finitePrimeRationalCoefficientField) z
  -- the fraction-field embedding of `K[X]` is faithful
  haveI : FaithfulSMul (Polynomial K) finitePrimeRationalCoefficientField :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (IsFractionRing.injective (Polynomial K) finitePrimeRationalCoefficientField)
  exact (Algebra.IsAlgebraic.algebraicIndependent_iff
    (Polynomial K) finitePrimeRationalCoefficientField).mp hPoly

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The faithful rational-coordinate embedding preserves every constant from the finite-prime
coefficient field. -/
theorem finitePrimeRationalCoefficientFieldToFormalRatFunc_algebraMap
    (k : finitePrimeCoefficientField) :
    finitePrimeRationalCoefficientFieldToFormalRatFunc
        (algebraMap finitePrimeCoefficientField finitePrimeRationalCoefficientField k) =
      algebraMap arithmeticFunctionFractionField arithmeticFunctionRationalCoordinateField
        (algebraMap finitePrimeCoefficientField arithmeticFunctionFractionField k) := by
  change RatFunc.map finitePrimeCoefficientPolynomialMap
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
        finitePrimeCoefficientPolynomialMap_injective)
      (algebraMap finitePrimeCoefficientField (RatFunc finitePrimeCoefficientField) k) = _
  rw [RatFunc.algebraMap_apply, RatFunc.map_apply_div]
  simp [finitePrimeCoefficientPolynomialMap]

/-- **Exact rational-coordinate base change.** A family of constant arithmetic fractions is
algebraically independent over `E_fin(s)` exactly when it is algebraically independent over the
intrinsic finite-prime coefficient field. The forward direction maps any relation over the smaller
field coefficientwise into the rational-coordinate field; the reverse direction is the purely
transcendental base-extension theorem above. -/
theorem algebraicIndependent_constants_over_finitePrimeRationalCoefficientField_iff
    {I : Type*} (x : I → arithmeticFunctionFractionField) :
    AlgebraicIndependent finitePrimeRationalCoefficientField
        (fun i => algebraMap arithmeticFunctionFractionField
          arithmeticFunctionRationalCoordinateField (x i)) ↔
      AlgebraicIndependent finitePrimeCoefficientField x := by
  let xR : I → arithmeticFunctionRationalCoordinateField := fun i =>
    algebraMap arithmeticFunctionFractionField arithmeticFunctionRationalCoordinateField (x i)
  constructor
  · intro hAI
    rw [algebraicIndependent_iff]
    intro P hPeval
    let Q : MvPolynomial I finitePrimeRationalCoefficientField :=
      MvPolynomial.map
        (algebraMap finitePrimeCoefficientField finitePrimeRationalCoefficientField) P
    have hcoeffHom :
        (algebraMap finitePrimeRationalCoefficientField
          arithmeticFunctionRationalCoordinateField).comp
            (algebraMap finitePrimeCoefficientField finitePrimeRationalCoefficientField) =
          (algebraMap arithmeticFunctionFractionField
            arithmeticFunctionRationalCoordinateField).comp
              (algebraMap finitePrimeCoefficientField arithmeticFunctionFractionField) := by
      ext k
      exact finitePrimeRationalCoefficientFieldToFormalRatFunc_algebraMap k
    have hQeval : MvPolynomial.aeval xR Q = 0 := by
      have heval : MvPolynomial.aeval xR Q =
          algebraMap arithmeticFunctionFractionField
            arithmeticFunctionRationalCoordinateField
              (MvPolynomial.aeval x P) := by
        rw [MvPolynomial.aeval_def]
        change MvPolynomial.eval₂
            (algebraMap finitePrimeRationalCoefficientField
              arithmeticFunctionRationalCoordinateField) xR
              (MvPolynomial.map
                (algebraMap finitePrimeCoefficientField
                  finitePrimeRationalCoefficientField) P) = _
        rw [MvPolynomial.eval₂_map]
        rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_comp_left]
        rw [hcoeffHom]
        rfl
      rw [heval, hPeval, map_zero]
    have hQzero := hAI.eq_zero_of_aeval_eq_zero Q hQeval
    apply (MvPolynomial.map_injective
      (algebraMap finitePrimeCoefficientField finitePrimeRationalCoefficientField)
      (FaithfulSMul.algebraMap_injective finitePrimeCoefficientField
        finitePrimeRationalCoefficientField))
    simpa only [Q, map_zero] using hQzero
  · exact algebraicIndependent_constants_over_finitePrimeRationalCoefficientField x

end

end GaloisForLFunctions.HTGeometry
