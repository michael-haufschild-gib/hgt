import Mathlib.LinearAlgebra.Prod

/-!
# Resolved defect conservation

The sum of two transported internal defects is their observed composite defect.  Before this
codiagonal is taken, the two defects live in a resolved product.  The kernel of the codiagonal is
exactly the antidiagonal, so a covariant composite can hide a nonzero resolved defect there.

An observation detects vanishing of a defect family exactly when it is conservative on the range
of that family.  This packages the distinction between total covariance and factor covariance in
an observation-independent form.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {R X Z W : Type*}
variable [CommRing R]
variable [AddCommGroup X] [Module R X]
variable [AddCommGroup Z] [Module R Z]
variable [AddCommGroup W] [Module R W]

/-- Codiagonal observation of a two-channel resolved defect. -/
def resolvedDefectCodiagonal : (Z × Z) →ₗ[R] Z :=
  LinearMap.fst R Z Z + LinearMap.snd R Z Z

@[simp]
theorem resolvedDefectCodiagonal_apply (z : Z × Z) :
    resolvedDefectCodiagonal (R := R) z = z.1 + z.2 :=
  rfl

/-- Universal hidden channel of the codiagonal: equal and opposite internal defects. -/
def resolvedDefectAntidiagonal : Z →ₗ[R] (Z × Z) where
  toFun z := (z, -z)
  map_add' x y := by
    apply Prod.ext <;> simp [add_comm]
  map_smul' c x := by
    apply Prod.ext <;> simp

@[simp]
theorem resolvedDefectAntidiagonal_apply (z : Z) :
    resolvedDefectAntidiagonal (R := R) z = (z, -z) :=
  rfl

/-- The universal antidiagonal is invisible after the codiagonal observation. -/
theorem resolvedDefectCodiagonal_comp_antidiagonal :
    (resolvedDefectCodiagonal (R := R) (Z := Z)).comp
        (resolvedDefectAntidiagonal (R := R) (Z := Z)) = 0 := by
  ext z
  simp [resolvedDefectCodiagonal, resolvedDefectAntidiagonal]

/-- **Universal two-factor cancellation sequence.**  The entire codiagonal kernel is the
antidiagonal range; there is no other hidden two-channel defect. -/
theorem ker_resolvedDefectCodiagonal_eq_range_antidiagonal :
    LinearMap.ker (resolvedDefectCodiagonal (R := R) (Z := Z)) =
      LinearMap.range (resolvedDefectAntidiagonal (R := R) (Z := Z)) := by
  ext z
  constructor
  · intro hz
    change z.1 + z.2 = 0 at hz
    refine ⟨z.1, ?_⟩
    apply Prod.ext
    · rfl
    · exact (eq_neg_of_add_eq_zero_right hz).symm
  · rintro ⟨x, rfl⟩
    change x + -x = 0
    exact add_neg_cancel x

/-- A linear observation is conservative on a specified defect sector when its kernel meets that
sector only at zero. -/
def IsConservativeOn
    (observe : Z →ₗ[R] W) (sector : Submodule R Z) : Prop :=
  Disjoint sector (LinearMap.ker observe)

/-- Conservativity on the range of a defect family makes observed vanishing equivalent to actual
vanishing. -/
theorem observedDefect_eq_zero_iff_of_conservativeOn
    (defect : X →ₗ[R] Z) (observe : Z →ₗ[R] W)
    (sector : Submodule R Z)
    (hrange : LinearMap.range defect ≤ sector)
    (hconservative : IsConservativeOn observe sector) :
    observe.comp defect = 0 ↔ defect = 0 := by
  constructor
  · intro hobserved
    apply LinearMap.ext
    intro x
    have hsector : defect x ∈ sector :=
      hrange ⟨x, rfl⟩
    have hkernel : defect x ∈ LinearMap.ker observe := by
      change observe (defect x) = 0
      simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using
        LinearMap.congr_fun hobserved x
    exact
      (Submodule.disjoint_def.mp hconservative)
        (defect x) hsector hkernel
  · rintro rfl
    simp

/-- Any observer applied only after the codiagonal remains blind to every antidiagonal defect. -/
theorem codiagonalObservation_antidiagonal
    (observe : Z →ₗ[R] W) (z : Z) :
    (observe.comp (resolvedDefectCodiagonal (R := R) (Z := Z)))
        (resolvedDefectAntidiagonal (R := R) z) = 0 := by
  simp [resolvedDefectCodiagonal, resolvedDefectAntidiagonal]

/-- A resolved two-channel defect vanishes exactly when both coordinate detectors vanish. -/
theorem resolvedDefect_eq_zero_iff_coordinates
    (defect : X →ₗ[R] (Z × Z)) :
    defect = 0 ↔
      (LinearMap.fst R Z Z).comp defect = 0 ∧
        (LinearMap.snd R Z Z).comp defect = 0 := by
  constructor
  · rintro rfl
    simp
  · rintro ⟨hfst, hsnd⟩
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · have hx := LinearMap.congr_fun hfst x
      change (defect x).1 = 0 at hx
      exact hx
    · have hx := LinearMap.congr_fun hsnd x
      change (defect x).2 = 0 at hx
      exact hx

end

end GaloisForLFunctions.HTGeometry
