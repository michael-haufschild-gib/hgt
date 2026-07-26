import GaloisForLFunctions.RHTower.KRealCompactlySupportedLocallyConstant
import Mathlib.Topology.LocallyConstant.Algebra

/-!
# Field-one Weyl multipliers on finite-place Bruhat functions

For a topological commutative ring, a locally constant additive character
remains locally constant after every multiplicative shift `x ↦ r * x`.
Multiplication by that shift preserves compactly supported locally constant
functions, because it does not enlarge support.

This file constructs the resulting linear Weyl action, proves its additive,
root, inverse, and scaling-covariance laws, and thereby supplies the generic
finite-place component of the spherical-to-Bruhat multiplier bridge.

Construction of the canonical global additive character on the rational
finite adeles and LF-topological continuity remain separate tasks.
-/

open Function

namespace GaloisForLFunctions.RHTower

noncomputable section

variable {R : Type*} [TopologicalSpace R] [CommRing R]
  [IsTopologicalRing R]

/-- An additive character which is locally constant in the source topology. -/
def LocallyConstantAddChar :=
  {ψ : AddChar R ℂ // IsLocallyConstant ψ}

/-- Multiplicative shift `x ↦ ψ (r * x)` as a locally constant function. -/
def locallyConstantAddCharShift
    (ψ : LocallyConstantAddChar (R := R)) (r : R) :
    LocallyConstant R ℂ where
  toFun x := ψ.1 (r * x)
  isLocallyConstant :=
    ψ.2.comp_continuous (continuous_const.mul continuous_id)

@[simp]
theorem locallyConstantAddCharShift_apply
    (ψ : LocallyConstantAddChar (R := R)) (r x : R) :
    locallyConstantAddCharShift ψ r x = ψ.1 (r * x) :=
  rfl

theorem locallyConstantAddCharShift_add
    (ψ : LocallyConstantAddChar (R := R)) (r s : R) :
    locallyConstantAddCharShift ψ (r + s) =
      locallyConstantAddCharShift ψ r *
        locallyConstantAddCharShift ψ s := by
  ext x
  simp [locallyConstantAddCharShift_apply, add_mul,
    AddChar.map_add_eq_mul]

@[simp]
theorem locallyConstantAddCharShift_zero
    (ψ : LocallyConstantAddChar (R := R)) :
    locallyConstantAddCharShift ψ 0 = 1 := by
  ext x
  simp [locallyConstantAddCharShift_apply]

/-- Natural multiples of an exponent become pointwise character powers. -/
theorem locallyConstantAddCharShift_nsmul
    (ψ : LocallyConstantAddChar (R := R)) (n : ℕ) (r : R) :
    locallyConstantAddCharShift ψ (n • r) =
      locallyConstantAddCharShift ψ r ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [succ_nsmul, locallyConstantAddCharShift_add, ih, pow_succ]

/-- Multiplication by a shifted locally constant character preserves the
finite-place Bruhat carrier. -/
def locallyConstantWeylMultiplier
    (ψ : LocallyConstantAddChar (R := R)) (r : R) :
    compactlySupportedLocallyConstant R →ₗ[ℂ]
      compactlySupportedLocallyConstant R where
  toFun f :=
    ⟨locallyConstantAddCharShift ψ r * f.1, f.2.mul_left⟩
  map_add' f g := by
    apply Subtype.ext
    ext x
    simp [mul_add]
  map_smul' c f := by
    apply Subtype.ext
    ext x
    simp

@[simp]
theorem locallyConstantWeylMultiplier_apply
    (ψ : LocallyConstantAddChar (R := R)) (r : R)
    (f : compactlySupportedLocallyConstant R) (x : R) :
    (locallyConstantWeylMultiplier ψ r f).1 x =
      ψ.1 (r * x) * f.1 x :=
  rfl

/-- Addition of exponents becomes composition of finite-place multipliers. -/
theorem locallyConstantWeylMultiplier_add
    (ψ : LocallyConstantAddChar (R := R)) (r s : R) :
    (locallyConstantWeylMultiplier ψ r).comp
        (locallyConstantWeylMultiplier ψ s) =
      locallyConstantWeylMultiplier ψ (r + s) := by
  ext f x
  simp [locallyConstantWeylMultiplier_apply, add_mul,
    AddChar.map_add_eq_mul, mul_assoc]

@[simp]
theorem locallyConstantWeylMultiplier_zero
    (ψ : LocallyConstantAddChar (R := R)) :
    locallyConstantWeylMultiplier ψ 0 = LinearMap.id := by
  ext f x
  simp [locallyConstantWeylMultiplier_apply]

theorem locallyConstantWeylMultiplier_neg_left
    (ψ : LocallyConstantAddChar (R := R)) (r : R) :
    (locallyConstantWeylMultiplier ψ (-r)).comp
        (locallyConstantWeylMultiplier ψ r) =
      LinearMap.id := by
  rw [locallyConstantWeylMultiplier_add, neg_add_cancel,
    locallyConstantWeylMultiplier_zero]

theorem locallyConstantWeylMultiplier_neg_right
    (ψ : LocallyConstantAddChar (R := R)) (r : R) :
    (locallyConstantWeylMultiplier ψ r).comp
        (locallyConstantWeylMultiplier ψ (-r)) =
      LinearMap.id := by
  rw [locallyConstantWeylMultiplier_add, add_neg_cancel,
    locallyConstantWeylMultiplier_zero]

/-- Pullback by right multiplication with a unit preserves compact support. -/
def compactlySupportedLocallyConstantMulRight
    (u : Rˣ) :
    compactlySupportedLocallyConstant R →ₗ[ℂ]
      compactlySupportedLocallyConstant R where
  toFun f :=
    ⟨LocallyConstant.comap
        ⟨fun x => x * (u : R), continuous_mul_const _⟩ f.1,
      f.2.comp_homeomorph
        (ContinuousAddEquiv.mulRight u).toHomeomorph⟩
  map_add' f g := by
    apply Subtype.ext
    ext x
    simp
  map_smul' c f := by
    apply Subtype.ext
    ext x
    simp

@[simp]
theorem compactlySupportedLocallyConstantMulRight_apply
    (u : Rˣ) (f : compactlySupportedLocallyConstant R) (x : R) :
    (compactlySupportedLocallyConstantMulRight u f).1 x =
      f.1 (x * u) :=
  rfl

/-- Exact Weyl covariance under finite-place multiplicative scaling. -/
theorem locallyConstantWeylMultiplier_scale_covariance
    (ψ : LocallyConstantAddChar (R := R)) (r : R) (u : Rˣ) :
    (compactlySupportedLocallyConstantMulRight u).comp
        ((locallyConstantWeylMultiplier ψ r).comp
          (compactlySupportedLocallyConstantMulRight u⁻¹)) =
      locallyConstantWeylMultiplier ψ (r * (u : R)) := by
  ext f x
  simp [locallyConstantWeylMultiplier_apply,
    compactlySupportedLocallyConstantMulRight_apply,
    mul_assoc, mul_comm, mul_left_comm]

end

end GaloisForLFunctions.RHTower
