import GaloisForLFunctions.RHTower.FieldOneRationalPrimaryReciprocity
import GaloisForLFunctions.HTGeometry.FieldOneArchimedeanWeylMultiplier
import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# Semilocal Bruhat--Schwartz Weyl tensor

The rational semilocal test carrier has an archimedean Schwartz factor and a
finite-adele compactly supported locally constant factor.  This file forms
their algebraic tensor product and combines the already-constructed Weyl
multipliers on both factors.

The archimedean parameter is normalized by `2π`, so its phase
`exp (-2π i h x)` matches the standard finite-adele character.  The resulting
tensor endomorphisms satisfy the exact additive, identity, and inverse laws,
and therefore are algebraic automorphisms.  The diagonal rational
specialization uses the canonical finite diagonal embedding.

No LF topology on the finite Bruhat factor, completed tensor product, Haar
measure, Hilbert completion, spectral assertion, positivity premise, or
Riemann-hypothesis premise occurs here.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open scoped TensorProduct

abbrev FieldOneArchimedeanSchwartz := SchwartzMap ℝ ℂ

abbrev FieldOneFiniteBruhatSchwartz :=
  compactlySupportedLocallyConstant FieldOneFiniteAdele

/-- Algebraic semilocal test carrier
`𝒮(ℝ) ⊗ C_c^lc(𝔸_f)`. -/
abbrev FieldOneSemilocalBruhatSchwartz :=
  FieldOneArchimedeanSchwartz ⊗[ℂ] FieldOneFiniteBruhatSchwartz

/-- Archimedean component with standard additive-character normalization
`exp (-2π i h x)`. -/
def fieldOneSemilocalArchimedeanWeylMultiplier (h : ℝ) :
    FieldOneArchimedeanSchwartz →ₗ[ℂ]
      FieldOneArchimedeanSchwartz :=
  (HTGeometry.FieldOneCore.fieldOneArchimedeanWeylMultiplier
    (2 * Real.pi * h)).toLinearMap

/-- Tensor product of the normalized archimedean and standard finite-adele
Weyl multipliers. -/
def fieldOneSemilocalBruhatWeylMultiplier
    (a : ℝ × FieldOneFiniteAdele) :
    FieldOneSemilocalBruhatSchwartz →ₗ[ℂ]
      FieldOneSemilocalBruhatSchwartz :=
  TensorProduct.map
    (fieldOneSemilocalArchimedeanWeylMultiplier a.1)
    (fieldOneFiniteAdeleStandardWeylMultiplier a.2)

@[simp]
theorem fieldOneSemilocalBruhatWeylMultiplier_tmul
    (a : ℝ × FieldOneFiniteAdele)
    (f : FieldOneArchimedeanSchwartz)
    (g : FieldOneFiniteBruhatSchwartz) :
    fieldOneSemilocalBruhatWeylMultiplier a (f ⊗ₜ[ℂ] g) =
      fieldOneSemilocalArchimedeanWeylMultiplier a.1 f ⊗ₜ[ℂ]
        fieldOneFiniteAdeleStandardWeylMultiplier a.2 g :=
  TensorProduct.map_tmul _ _ _ _

theorem fieldOneSemilocalArchimedeanWeylMultiplier_add
    (h k : ℝ) :
    (fieldOneSemilocalArchimedeanWeylMultiplier h).comp
        (fieldOneSemilocalArchimedeanWeylMultiplier k) =
      fieldOneSemilocalArchimedeanWeylMultiplier (h + k) := by
  have hscaled :
      2 * Real.pi * (h + k) =
        2 * Real.pi * h + 2 * Real.pi * k := by
    ring
  simpa only [fieldOneSemilocalArchimedeanWeylMultiplier,
    hscaled] using congrArg ContinuousLinearMap.toLinearMap
      (HTGeometry.FieldOneCore.fieldOneArchimedeanWeylMultiplier_add
        (2 * Real.pi * h) (2 * Real.pi * k))

@[simp]
theorem fieldOneSemilocalArchimedeanWeylMultiplier_zero :
    fieldOneSemilocalArchimedeanWeylMultiplier 0 =
      LinearMap.id := by
  simpa only [fieldOneSemilocalArchimedeanWeylMultiplier,
    mul_zero] using congrArg ContinuousLinearMap.toLinearMap
      HTGeometry.FieldOneCore.fieldOneArchimedeanWeylMultiplier_zero

/-- Addition in the semilocal parameter group becomes composition on the
algebraic Schwartz--Bruhat tensor. -/
theorem fieldOneSemilocalBruhatWeylMultiplier_add
    (a b : ℝ × FieldOneFiniteAdele) :
    (fieldOneSemilocalBruhatWeylMultiplier a).comp
        (fieldOneSemilocalBruhatWeylMultiplier b) =
      fieldOneSemilocalBruhatWeylMultiplier (a + b) := by
  apply TensorProduct.ext'
  intro f g
  simp only [LinearMap.comp_apply,
    fieldOneSemilocalBruhatWeylMultiplier_tmul]
  have harch :=
    DFunLike.congr_fun
      (fieldOneSemilocalArchimedeanWeylMultiplier_add a.1 b.1) f
  have hfinite :=
    DFunLike.congr_fun
      (fieldOneFiniteAdeleStandardWeylMultiplier_add a.2 b.2) g
  simpa only [Prod.fst_add, Prod.snd_add] using
    congrArg₂ (fun u v => u ⊗ₜ[ℂ] v) harch hfinite

@[simp]
theorem fieldOneSemilocalBruhatWeylMultiplier_zero :
    fieldOneSemilocalBruhatWeylMultiplier
        (0 : ℝ × FieldOneFiniteAdele) =
      LinearMap.id := by
  rw [fieldOneSemilocalBruhatWeylMultiplier]
  simp only [Prod.fst_zero, Prod.snd_zero,
    fieldOneSemilocalArchimedeanWeylMultiplier_zero,
    fieldOneFiniteAdeleStandardWeylMultiplier,
    locallyConstantWeylMultiplier_zero,
    TensorProduct.map_id]

theorem fieldOneSemilocalBruhatWeylMultiplier_neg_left
    (a : ℝ × FieldOneFiniteAdele) :
    (fieldOneSemilocalBruhatWeylMultiplier (-a)).comp
        (fieldOneSemilocalBruhatWeylMultiplier a) =
      LinearMap.id := by
  rw [fieldOneSemilocalBruhatWeylMultiplier_add, neg_add_cancel,
    fieldOneSemilocalBruhatWeylMultiplier_zero]

theorem fieldOneSemilocalBruhatWeylMultiplier_neg_right
    (a : ℝ × FieldOneFiniteAdele) :
    (fieldOneSemilocalBruhatWeylMultiplier a).comp
        (fieldOneSemilocalBruhatWeylMultiplier (-a)) =
      LinearMap.id := by
  rw [fieldOneSemilocalBruhatWeylMultiplier_add, add_neg_cancel,
    fieldOneSemilocalBruhatWeylMultiplier_zero]

/-- Every semilocal Weyl multiplier is an algebraic automorphism, with
inverse indexed by the negative parameter. -/
def fieldOneSemilocalBruhatWeylLinearEquiv
    (a : ℝ × FieldOneFiniteAdele) :
    FieldOneSemilocalBruhatSchwartz ≃ₗ[ℂ]
      FieldOneSemilocalBruhatSchwartz where
  toLinearMap := fieldOneSemilocalBruhatWeylMultiplier a
  invFun := fieldOneSemilocalBruhatWeylMultiplier (-a)
  left_inv x := by
    exact DFunLike.congr_fun
      (fieldOneSemilocalBruhatWeylMultiplier_neg_left a) x
  right_inv x := by
    exact DFunLike.congr_fun
      (fieldOneSemilocalBruhatWeylMultiplier_neg_right a) x

/-- Canonical diagonal embedding of a rational parameter into the
archimedean--finite semilocal ring. -/
def fieldOneRationalDiagonalSemilocalParameter :
    ℚ →+ ℝ × FieldOneFiniteAdele where
  toFun q := ((q : ℝ), algebraMap ℚ FieldOneFiniteAdele q)
  map_zero' := by simp
  map_add' q r := by
    ext <;> simp

theorem fieldOneRationalDiagonalSemilocalParameter_injective :
    Function.Injective fieldOneRationalDiagonalSemilocalParameter := by
  intro q r h
  have hreal :
      (q : ℝ) = (r : ℝ) :=
    congrArg Prod.fst h
  exact_mod_cast hreal

/-- Rational diagonal specialization of the semilocal Weyl action. -/
def fieldOneRationalDiagonalBruhatWeylMultiplier (q : ℚ) :
    FieldOneSemilocalBruhatSchwartz →ₗ[ℂ]
      FieldOneSemilocalBruhatSchwartz :=
  fieldOneSemilocalBruhatWeylMultiplier
    (fieldOneRationalDiagonalSemilocalParameter q)

theorem fieldOneRationalDiagonalBruhatWeylMultiplier_add
    (q r : ℚ) :
    (fieldOneRationalDiagonalBruhatWeylMultiplier q).comp
        (fieldOneRationalDiagonalBruhatWeylMultiplier r) =
      fieldOneRationalDiagonalBruhatWeylMultiplier (q + r) := by
  rw [fieldOneRationalDiagonalBruhatWeylMultiplier,
    fieldOneRationalDiagonalBruhatWeylMultiplier,
    fieldOneRationalDiagonalBruhatWeylMultiplier,
    fieldOneSemilocalBruhatWeylMultiplier_add,
    map_add]

end

end GaloisForLFunctions.RHTower
