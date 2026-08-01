import GaloisForLFunctions.RHTower.DeningerRealKummerArakelovBoundary
import Mathlib.Algebra.TrivSqZeroExt.Basic

/-!
# The square-zero Kummer boundary

An augmentation `s` of a real algebra kills its augmentation ideal `I`.  A linear functional
that vanishes on the unit and on every product of two elements of `I` is therefore forced to
obey the Leibniz rule relative to `s`, and the pair `(s, δ)` is an algebra map into the
square-zero extension `ℝ ⊕ ℝε`.

For the real Milnor algebra of `ℚ` the augmentation is the rank map, `I` is the positive-degree
part, and a functional supported in Milnor degree one vanishes on `I·I ⊆ ⨁_{n≥2}`.  So the
archimedean Kummer boundary is not an ad hoc additive functional: it is the weight-one
square-zero boundary of the augmented algebra.

* `deningerAugmentation_leibniz` is the Leibniz rule.
* `deningerSquareZeroHom` is the resulting algebra map into `TrivSqZeroExt ℝ ℝ`.
* `deningerSquareZeroHom_of_algHom` is the converse: the second component of any algebra map
  into the square-zero extension is such a functional.
-/

namespace RHTower

noncomputable section

variable {A : Type*} [CommRing A] [Algebra ℝ A]

/-- A functional vanishing on the unit vanishes on all of `ℝ`. -/
theorem deningerDelta_algebraMap (δ : A →ₗ[ℝ] ℝ) (hone : δ 1 = 0) (r : ℝ) :
    δ (algebraMap ℝ A r) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, hone, smul_zero]

/-- **Square-zero Leibniz rule.**  A linear functional killing the unit and every product of two
elements of the augmentation ideal is an `s`-derivation. -/
theorem deningerAugmentation_leibniz (s : A →ₐ[ℝ] ℝ) (δ : A →ₗ[ℝ] ℝ)
    (hone : δ 1 = 0) (hsq : ∀ x y : A, s x = 0 → s y = 0 → δ (x * y) = 0) (x y : A) :
    δ (x * y) = s x * δ y + δ x * s y := by
  have hconst := deningerDelta_algebraMap δ hone
  set x₀ : A := x - algebraMap ℝ A (s x) with hx₀
  set y₀ : A := y - algebraMap ℝ A (s y) with hy₀
  have hsx₀ : s x₀ = 0 := by simp [hx₀]
  have hsy₀ : s y₀ = 0 := by simp [hy₀]
  have hδx₀ : δ x₀ = δ x := by simp [hx₀, hconst]
  have hδy₀ : δ y₀ = δ y := by simp [hy₀, hconst]
  have hxy : x * y = algebraMap ℝ A (s x * s y)
      + (algebraMap ℝ A (s x) * y₀ + algebraMap ℝ A (s y) * x₀) + x₀ * y₀ := by
    simp only [hx₀, hy₀, map_mul]
    ring
  have hscal : ∀ (r : ℝ) (z : A), δ (algebraMap ℝ A r * z) = r * δ z := by
    intro r z
    rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  rw [hxy, map_add, map_add, hconst, hsq x₀ y₀ hsx₀ hsy₀, map_add, hscal, hscal,
    hδx₀, hδy₀]
  ring

/-- **The square-zero extension map.**  The pair of an augmentation and such a functional is an
algebra map into `ℝ ⊕ ℝε`. -/
def deningerSquareZeroHom (s : A →ₐ[ℝ] ℝ) (δ : A →ₗ[ℝ] ℝ)
    (hone : δ 1 = 0) (hsq : ∀ x y : A, s x = 0 → s y = 0 → δ (x * y) = 0) :
    A →ₐ[ℝ] TrivSqZeroExt ℝ ℝ where
  toFun a := (s a, δ a)
  map_one' := by
    apply TrivSqZeroExt.ext
    · simp
    · simpa using hone
  map_mul' a b := by
    apply TrivSqZeroExt.ext
    · simp
    · simpa [smul_eq_mul, mul_comm] using deningerAugmentation_leibniz s δ hone hsq a b
  map_zero' := by
    apply TrivSqZeroExt.ext <;> simp
  map_add' a b := by
    apply TrivSqZeroExt.ext <;> simp
  commutes' r := by
    rw [TrivSqZeroExt.algebraMap_eq_inl']
    apply TrivSqZeroExt.ext
    · simp
    · simpa using deningerDelta_algebraMap δ hone r

@[simp] theorem deningerSquareZeroHom_fst (s : A →ₐ[ℝ] ℝ) (δ : A →ₗ[ℝ] ℝ)
    (hone : δ 1 = 0) (hsq : ∀ x y : A, s x = 0 → s y = 0 → δ (x * y) = 0) (a : A) :
    (deningerSquareZeroHom s δ hone hsq a).fst = s a := rfl

@[simp] theorem deningerSquareZeroHom_snd (s : A →ₐ[ℝ] ℝ) (δ : A →ₗ[ℝ] ℝ)
    (hone : δ 1 = 0) (hsq : ∀ x y : A, s x = 0 → s y = 0 → δ (x * y) = 0) (a : A) :
    (deningerSquareZeroHom s δ hone hsq a).snd = δ a := rfl

/-- **Converse.**  The second component of an algebra map into the square-zero extension obeys
the Leibniz rule relative to the first. -/
theorem deningerSquareZeroHom_of_algHom (F : A →ₐ[ℝ] TrivSqZeroExt ℝ ℝ) (x y : A) :
    (F (x * y)).snd = (F x).fst * (F y).snd + (F x).snd * (F y).fst := by
  rw [map_mul, TrivSqZeroExt.snd_mul]
  simp [smul_eq_mul, mul_comm]

/-- The second component of an algebra map into the square-zero extension kills the unit. -/
theorem deningerSquareZeroHom_of_algHom_one (F : A →ₐ[ℝ] TrivSqZeroExt ℝ ℝ) :
    (F 1).snd = 0 := by
  rw [map_one]
  simp

section KummerModel

/-- The square-zero model of the real Milnor algebra in Kummer degrees: `ℝ ⊕ V` with `V` the
real Kummer line of prime coordinates. -/
abbrev DeningerKummerSquareZero := TrivSqZeroExt ℝ (ℕ →₀ ℝ)

/-- The rank augmentation of the square-zero Kummer algebra. -/
def deningerKummerRank : DeningerKummerSquareZero →ₐ[ℝ] ℝ :=
  TrivSqZeroExt.fstHom ℝ ℝ (ℕ →₀ ℝ)

/-- The archimedean Kummer boundary as a functional on the square-zero Kummer algebra:
`∂_∞` in degree one, zero in degree zero. -/
def deningerKummerArchDelta : DeningerKummerSquareZero →ₗ[ℝ] ℝ :=
  deningerArchBoundary.comp (TrivSqZeroExt.sndHom ℝ (ℕ →₀ ℝ))

@[simp] theorem deningerKummerRank_apply (x : DeningerKummerSquareZero) :
    deningerKummerRank x = x.fst := rfl

@[simp] theorem deningerKummerArchDelta_apply (x : DeningerKummerSquareZero) :
    deningerKummerArchDelta x = deningerArchBoundary x.snd := rfl

theorem deningerKummerArchDelta_one : deningerKummerArchDelta 1 = 0 := by
  simp

theorem deningerKummerArchDelta_sq (x y : DeningerKummerSquareZero)
    (hx : deningerKummerRank x = 0) (hy : deningerKummerRank y = 0) :
    deningerKummerArchDelta (x * y) = 0 := by
  have hxf : x.fst = 0 := hx
  have hyf : y.fst = 0 := hy
  simp [TrivSqZeroExt.snd_mul, hxf, hyf]

/-- **The weight-one square-zero boundary.**  The rank augmentation together with the
archimedean Kummer boundary is an algebra map from the square-zero Kummer algebra to the
square-zero extension `ℝ ⊕ ℝε`. -/
def deningerKummerSquareZeroHom : DeningerKummerSquareZero →ₐ[ℝ] TrivSqZeroExt ℝ ℝ :=
  deningerSquareZeroHom deningerKummerRank deningerKummerArchDelta
    deningerKummerArchDelta_one deningerKummerArchDelta_sq

@[simp] theorem deningerKummerSquareZeroHom_fst (x : DeningerKummerSquareZero) :
    (deningerKummerSquareZeroHom x).fst = x.fst := rfl

@[simp] theorem deningerKummerSquareZeroHom_snd (x : DeningerKummerSquareZero) :
    (deningerKummerSquareZeroHom x).snd = deningerArchBoundary x.snd := rfl

/-- On the Kummer line the square-zero boundary is minus the logarithm of a positive
rational. -/
theorem deningerKummerSquareZeroHom_ratExpReal {q : ℚ} (hq : 0 < q) :
    (deningerKummerSquareZeroHom (TrivSqZeroExt.inr (deningerRatExpReal q))).snd
      = -Real.log q := by
  rw [deningerKummerSquareZeroHom_snd, TrivSqZeroExt.snd_inr,
    deningerArchBoundary_ratExpReal hq]

end KummerModel

end

end RHTower
