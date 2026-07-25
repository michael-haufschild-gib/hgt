import GaloisForLFunctions.HTGeometry.DirichletPolyLead
import GaloisForLFunctions.HTGeometry.UpperEndDirichletCoordinate
import Mathlib

/-!
# Analytic realization of finite-abscissa Dirichlet polynomials

Polynomials in the Dirichlet variable with finite-abscissa Dirichlet coefficients realize to the
upper-end meromorphic field by `dirRealize P = sum_k L(P_k) s^k`.  This map is an injective ring
homomorphism, and it intertwines the coefficient-first unit shift `f_n ↦ f_n / n`, `s ↦ s + 1` with
upper-end translation by `I`.

Because the leading-term interface already lives on all coefficient-first Dirichlet series, every
identity produced by the analytic side is transported along the coefficient inclusion and settled
there.
-/

open Polynomial ArithmeticFunction

namespace GaloisForLFunctions.HTGeometry

noncomputable section

local instance dirRealizeDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance dirRealizeDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

local instance dirRealizeComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

/-- Polynomials in the Dirichlet variable with finite-abscissa Dirichlet coefficients. -/
abbrev FAPoly := Polynomial finiteAbscissaArithmeticSubalgebra

instance faPolyCommRing : CommRing FAPoly := by
  exact @Polynomial.commRing (finiteAbscissaArithmeticSubalgebra) _

/-! ## The coefficient-side unit shift -/

theorem dirichletShift_one_apply (f : ArithmeticFunction ℂ) (n : ℕ) :
    dirichletShift 1 f n = f n / (n : ℂ) := by
  rw [dirichletShift_apply, cpowWeight, Complex.cpow_neg, Complex.cpow_one, div_eq_inv_mul]

theorem finiteAbscissaDirichletShift_one_mul
    (f g : finiteAbscissaArithmeticSubalgebra) :
    finiteAbscissaDirichletShift 1 (f * g)
      = finiteAbscissaDirichletShift 1 f * finiteAbscissaDirichletShift 1 g := by
  apply Subtype.ext
  exact dirichletShift_mul 1 f.1 g.1

theorem finiteAbscissaDirichletShift_one_add
    (f g : finiteAbscissaArithmeticSubalgebra) :
    finiteAbscissaDirichletShift 1 (f + g)
      = finiteAbscissaDirichletShift 1 f + finiteAbscissaDirichletShift 1 g := by
  apply Subtype.ext
  exact dirichletShift_add 1 f.1 g.1

theorem finiteAbscissaDirichletShift_one_one :
    finiteAbscissaDirichletShift 1 (1 : finiteAbscissaArithmeticSubalgebra) = 1 := by
  apply Subtype.ext
  ext n
  show cpowWeight 1 n * (1 : ArithmeticFunction ℂ) n = (1 : ArithmeticFunction ℂ) n
  by_cases h : n = 1
  · subst h
    simp [cpowWeight]
  · simp [h]

theorem finiteAbscissaDirichletShift_one_zero :
    finiteAbscissaDirichletShift 1 (0 : finiteAbscissaArithmeticSubalgebra) = 0 := by
  apply Subtype.ext
  ext n
  show cpowWeight 1 n * (0 : ArithmeticFunction ℂ) n = (0 : ArithmeticFunction ℂ) n
  simp

theorem dirichletShift_comp (a b : ℂ) (f : ArithmeticFunction ℂ) :
    dirichletShift a (dirichletShift b f) = dirichletShift (a + b) f := by
  ext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  show cpowWeight a n * (cpowWeight b n * f n) = cpowWeight (a + b) n * f n
  rw [cpowWeight, cpowWeight, cpowWeight, ← mul_assoc, ← Complex.cpow_add _ _ hn0]
  ring_nf

theorem finiteAbscissaDirichletShift_comp (a b : ℂ)
    (f : finiteAbscissaArithmeticSubalgebra) :
    finiteAbscissaDirichletShift a (finiteAbscissaDirichletShift b f)
      = finiteAbscissaDirichletShift (a + b) f := by
  apply Subtype.ext
  exact dirichletShift_comp a b f.1

theorem finiteAbscissaDirichletShift_zero (f : finiteAbscissaArithmeticSubalgebra) :
    finiteAbscissaDirichletShift 0 f = f := by
  apply Subtype.ext
  ext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  show cpowWeight 0 n * f.1 n = f.1 n
  rw [cpowWeight, neg_zero, Complex.cpow_zero, one_mul]

/-- The coefficient-side unit shift as a ring homomorphism. -/
def faShiftHom :
    finiteAbscissaArithmeticSubalgebra →+* finiteAbscissaArithmeticSubalgebra where
  toFun := finiteAbscissaDirichletShift 1
  map_one' := finiteAbscissaDirichletShift_one_one
  map_zero' := finiteAbscissaDirichletShift_one_zero
  map_add' := finiteAbscissaDirichletShift_one_add
  map_mul' := finiteAbscissaDirichletShift_one_mul

@[simp] theorem faShiftHom_apply (f : finiteAbscissaArithmeticSubalgebra) :
    faShiftHom f = finiteAbscissaDirichletShift 1 f := rfl

/-- The coefficient-side unit shift divides the `n`-th coefficient by `n`. -/
theorem val_faShiftHom (f : finiteAbscissaArithmeticSubalgebra) :
    (faShiftHom f).1 = _root_.HTGeometry.DirPoly.dshift f.1 := by
  ext n
  show dirichletShift 1 f.1 n = f.1 n / (n : ℂ)
  exact dirichletShift_one_apply f.1 n

/-! ## The shift on Dirichlet polynomials -/

/-- The unit shift on polynomials in the Dirichlet variable. -/
def faSigmaPoly : FAPoly →+* FAPoly :=
  (Polynomial.eval₂RingHom Polynomial.C ((X : FAPoly) + 1)).comp
    (Polynomial.mapRingHom faShiftHom)

theorem faSigmaPoly_apply (P : FAPoly) :
    faSigmaPoly P = (P.map faShiftHom).comp ((X : FAPoly) + 1) := rfl

/-- The index-one embedding of complex polynomials. -/
def faEmb : ℂ[X] →+* FAPoly :=
  Polynomial.mapRingHom (algebraMap ℂ finiteAbscissaArithmeticSubalgebra)

/-- The coefficient inclusion into all coefficient-first Dirichlet series. -/
def faToDirPoly : FAPoly →+* _root_.HTGeometry.DirPoly :=
  Polynomial.mapRingHom
    (finiteAbscissaArithmeticSubalgebra.val : finiteAbscissaArithmeticSubalgebra →+*
      ArithmeticFunction ℂ)

theorem faToDirPoly_injective : Function.Injective faToDirPoly := by
  have hval : Function.Injective
      (finiteAbscissaArithmeticSubalgebra.val : finiteAbscissaArithmeticSubalgebra →+*
        ArithmeticFunction ℂ) := fun a b hab => Subtype.ext hab
  exact Polynomial.map_injective _ hval

theorem faToDirPoly_sigma (P : FAPoly) :
    faToDirPoly (faSigmaPoly P)
      = _root_.HTGeometry.DirPoly.sigmaDirPoly (faToDirPoly P) := by
  show ((P.map faShiftHom).comp ((X : FAPoly) + 1)).map
      (finiteAbscissaArithmeticSubalgebra.val : finiteAbscissaArithmeticSubalgebra →+*
        ArithmeticFunction ℂ)
    = ((P.map (finiteAbscissaArithmeticSubalgebra.val : finiteAbscissaArithmeticSubalgebra →+*
        ArithmeticFunction ℂ)).map
        (_root_.HTGeometry.DirPoly.dshift :
          ArithmeticFunction ℂ →+* ArithmeticFunction ℂ)).comp (X + 1)
  have hcomp :
      ((finiteAbscissaArithmeticSubalgebra.val : finiteAbscissaArithmeticSubalgebra →+*
          ArithmeticFunction ℂ).comp faShiftHom)
        = ((_root_.HTGeometry.DirPoly.dshift : ArithmeticFunction ℂ →+* ArithmeticFunction ℂ).comp
            (finiteAbscissaArithmeticSubalgebra.val : finiteAbscissaArithmeticSubalgebra →+*
              ArithmeticFunction ℂ)) :=
    RingHom.ext fun f => val_faShiftHom f
  rw [Polynomial.map_comp, Polynomial.map_map, Polynomial.map_map, hcomp]
  simp only [Polynomial.map_add, Polynomial.map_X, Polynomial.map_one]

theorem faToDirPoly_emb (p : ℂ[X]) :
    faToDirPoly (faEmb p) = _root_.HTGeometry.DirPoly.embDirPoly p := by
  show ((p.map (algebraMap ℂ finiteAbscissaArithmeticSubalgebra)).map
      (finiteAbscissaArithmeticSubalgebra.val : finiteAbscissaArithmeticSubalgebra →+*
        ArithmeticFunction ℂ))
    = p.map (algebraMap ℂ (ArithmeticFunction ℂ))
  rw [Polynomial.map_map]
  congr 1

theorem dirichletLeadPoly_sigma :
    (_root_.HTGeometry.DirPoly.dirichletLeadPoly).sigma
      = _root_.HTGeometry.DirPoly.sigmaDirPoly := rfl

theorem dirichletLeadPoly_emb :
    (_root_.HTGeometry.DirPoly.dirichletLeadPoly).emb
      = _root_.HTGeometry.DirPoly.embDirPoly := rfl

/-! ## Analytic realization -/

/-- The analytic realization of a Dirichlet polynomial at the Dirichlet variable. -/
def dirRealize : FAPoly →+* upperEndMeroField :=
  Polynomial.eval₂RingHom
    (finiteAbscissaLSeriesToUpperEndMero :
      finiteAbscissaArithmeticSubalgebra →+* upperEndMeroField) dirCoordMero

@[simp] theorem dirRealize_C (f : finiteAbscissaArithmeticSubalgebra) :
    dirRealize (Polynomial.C f) = finiteAbscissaLSeriesToUpperEndMero f := by
  simp [dirRealize]

@[simp] theorem dirRealize_X : dirRealize X = dirCoordMero := by
  simp [dirRealize]

/-- The scaling constant turning the Dirichlet variable into the upper-end coordinate. -/
def faRot : finiteAbscissaArithmeticSubalgebra :=
  algebraMap ℂ finiteAbscissaArithmeticSubalgebra (-Complex.I)

theorem lseries_faRot :
    (finiteAbscissaLSeriesToUpperEndMero :
      finiteAbscissaArithmeticSubalgebra →+* upperEndMeroField) faRot
      = algebraMap ℂ upperEndMeroField (-Complex.I) :=
  finiteAbscissaLSeriesToUpperEndMero.commutes _

theorem coordMero_eq_upperEndCoordinateMero : coordMero = upperEndCoordinateMero :=
  coordMero_eq_polyX

theorem dirRealize_eq_coordRealize (P : FAPoly) :
    dirRealize P = Polynomial.eval₂
      (finiteAbscissaLSeriesToUpperEndMero :
        finiteAbscissaArithmeticSubalgebra →+* upperEndMeroField)
      upperEndCoordinateMero (P.comp (Polynomial.C faRot * X)) := by
  rw [Polynomial.eval₂_comp]
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X]
  rw [lseries_faRot, ← coordMero_eq_upperEndCoordinateMero, ← dirCoordMero_eq]
  rfl

theorem faRot_isUnit : IsUnit faRot := by
  refine ⟨⟨faRot, algebraMap ℂ finiteAbscissaArithmeticSubalgebra (-Complex.I)⁻¹, ?_, ?_⟩, rfl⟩
  · rw [faRot, ← map_mul, mul_inv_cancel₀ (by simp), map_one]
  · rw [faRot, ← map_mul, inv_mul_cancel₀ (by simp), map_one]

theorem dirRealize_eq_zero (P : FAPoly) (hP : dirRealize P = 0) : P = 0 := by
  obtain ⟨u, hu⟩ := faRot_isUnit
  have hcomp : (P.comp (Polynomial.C faRot * X)) = 0 := by
    apply upperEndCoordinate_polynomial_relation_eq_zero
    rw [← dirRealize_eq_coordRealize]
    exact hP
  have hunit : (Polynomial.C faRot * X).comp
      (Polynomial.C (↑u⁻¹ : finiteAbscissaArithmeticSubalgebra) * X) = X := by
    simp only [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp,
      ← mul_assoc, ← Polynomial.C_mul]
    rw [← hu, ← Units.val_mul, mul_inv_cancel, Units.val_one, Polynomial.C_1, one_mul]
  have hback : (P.comp (Polynomial.C faRot * X)).comp
      (Polynomial.C (↑u⁻¹ : finiteAbscissaArithmeticSubalgebra) * X) = P := by
    rw [Polynomial.comp_assoc, hunit, Polynomial.comp_X]
  rw [← hback, hcomp, Polynomial.zero_comp]

theorem dirRealize_injective : Function.Injective dirRealize := by
  intro P Q hPQ
  have hzero : dirRealize (P - Q) = 0 := by rw [map_sub, hPQ, sub_self]
  exact sub_eq_zero.mp (dirRealize_eq_zero _ hzero)

/-- Translation acts on a realized polynomial by shifting the coefficients and the variable. -/
theorem translate_dirEval (P : FAPoly) :
    upperEndTranslationMeroEquiv Complex.I
        (Polynomial.eval₂ (finiteAbscissaLSeriesToUpperEndMero :
          finiteAbscissaArithmeticSubalgebra →+* upperEndMeroField) dirCoordMero P)
      = Polynomial.eval₂
          ((finiteAbscissaLSeriesToUpperEndMero :
            finiteAbscissaArithmeticSubalgebra →+* upperEndMeroField).comp faShiftHom)
          (upperEndTranslationMeroEquiv Complex.I dirCoordMero) P := by
  have hL : ∀ f : finiteAbscissaArithmeticSubalgebra,
      upperEndTranslationMeroEquiv Complex.I
          ((finiteAbscissaLSeriesToUpperEndMero :
            finiteAbscissaArithmeticSubalgebra →+* upperEndMeroField) f)
        = ((finiteAbscissaLSeriesToUpperEndMero :
            finiteAbscissaArithmeticSubalgebra →+* upperEndMeroField).comp faShiftHom) f := by
    intro f
    have h := finiteAbscissaLSeriesToUpperEndMero_dirichletShift 1 f
    rw [mul_one] at h
    show upperEndTranslationMeroEquiv Complex.I (finiteAbscissaLSeriesToUpperEndMero f)
      = finiteAbscissaLSeriesToUpperEndMero (finiteAbscissaDirichletShift 1 f)
    rw [h]
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [Polynomial.eval₂_add, (upperEndTranslationMeroEquiv Complex.I).map_add, hp, hq,
        Polynomial.eval₂_add]
  | monomial j f =>
      rw [Polynomial.eval₂_monomial, Polynomial.eval₂_monomial,
        (upperEndTranslationMeroEquiv Complex.I).map_mul, map_pow, hL f]

/-- **The realization intertwines the two unit shifts.** -/
theorem dirRealize_sigma (P : FAPoly) :
    upperEndTranslationMeroEquiv Complex.I (dirRealize P) = dirRealize (faSigmaPoly P) := by
  have hstep : dirRealize (faSigmaPoly P)
      = Polynomial.eval₂
          ((finiteAbscissaLSeriesToUpperEndMero :
            finiteAbscissaArithmeticSubalgebra →+* upperEndMeroField).comp faShiftHom)
          (dirCoordMero + 1) P := by
    show Polynomial.eval₂ _ dirCoordMero ((P.map faShiftHom).comp ((X : FAPoly) + 1)) = _
    rw [Polynomial.eval₂_comp, Polynomial.eval₂_map]
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_X, Polynomial.eval₂_one]
  rw [hstep, ← upperEndTranslate_dirCoordMero]
  exact translate_dirEval P

/-- Realizing an index-one embedding is evaluation at the Dirichlet variable. -/
theorem dirRealize_faEmb (p : ℂ[X]) :
    dirRealize (faEmb p) = Polynomial.aeval dirCoordMero p := by
  have hext : (dirRealize.comp faEmb)
      = ((Polynomial.aeval dirCoordMero : ℂ[X] →ₐ[ℂ] upperEndMeroField).toRingHom) := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · show dirRealize (faEmb (Polynomial.C a)) = Polynomial.aeval dirCoordMero (Polynomial.C a)
      rw [Polynomial.aeval_C]
      show dirRealize ((Polynomial.C a).map
        (algebraMap ℂ finiteAbscissaArithmeticSubalgebra)) = _
      rw [Polynomial.map_C, dirRealize_C]
      exact finiteAbscissaLSeriesToUpperEndMero.commutes a
    · show dirRealize (faEmb X) = Polynomial.aeval dirCoordMero X
      rw [Polynomial.aeval_X]
      show dirRealize (X.map (algebraMap ℂ finiteAbscissaArithmeticSubalgebra)) = _
      rw [Polynomial.map_X, dirRealize_X]
  exact congrArg (fun f : ℂ[X] →+* upperEndMeroField => f p) hext

end

end GaloisForLFunctions.HTGeometry
