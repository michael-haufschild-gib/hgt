import GaloisForLFunctions.HTGeometry.BorsukUlam.Theorem
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.Tactic

/-!
# Induced antipode and conformal reciprocity

This module formalizes the topological, conformal-factor, and centring claims in Okten--Turan,
arXiv:2608.19244v1, equations `(38)`--`(50)`.  The selected balanced uniformization is represented
by a homeomorphism with the round sphere.  No existence or branch-independence assertion is made:
the paper also treats that uniformization as selected geometric input.
-/

open Metric MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Equation `(38)`: pull the round antipode back through a selected spherical homeomorphism. -/
def inducedAntipode {X : Type*} [TopologicalSpace X] {n : ℕ}
    (h : X ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) (x : X) : X :=
  h.symm (-h x)

/-- The induced antipode is an involution. -/
@[simp] theorem inducedAntipode_involutive {X : Type*} [TopologicalSpace X] {n : ℕ}
    (h : X ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) (x : X) :
    inducedAntipode h (inducedAntipode h x) = x := by
  simp [inducedAntipode]

/-- Equations `(39)`--`(41)`: Borsuk--Ulam transported to the induced antipode.  For the paper's
pair `(kappa / kappaRef, kappaDot / kappaRef²)`, take `n = 2`. -/
theorem exists_eq_inducedAntipode {X : Type*} [TopologicalSpace X] {n : ℕ}
    (h : X ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
    (v : X → EuclideanSpace ℝ (Fin n)) (hv : Continuous v) :
    ∃ x : X, v x = v (inducedAntipode h x) := by
  obtain ⟨y, hy⟩ := GaloisForLFunctions.BorsukUlam.borsuk_ulam_sphere
    (v ∘ h.symm) (hv.comp h.symm.continuous)
  refine ⟨h.symm y, ?_⟩
  simpa [inducedAntipode, Function.comp_def] using hy

/-- Equation `(42)`: exponent of the conformal factor induced by conjugating the round antipode,
after the geometric pullback calculation has supplied the uniformizing exponent `rho`. -/
def inducedConformalExponent {X : Type*} (rho : X → ℝ) (A : X → X) (x : X) : ℝ :=
  rho x - rho (A x)

/-- Equations `(43)`--`(44)`: positive area Jacobian in two dimensions. -/
def inducedJacobian {X : Type*} (rho : X → ℝ) (A : X → X) (x : X) : ℝ :=
  Real.exp (2 * inducedConformalExponent rho A x)

/-- The conformal exponent changes sign at antipodes. -/
theorem inducedConformalExponent_apply {X : Type*} (rho : X → ℝ) (A : X → X)
    (hA : Function.Involutive A) (x : X) :
    inducedConformalExponent rho A (A x) = -inducedConformalExponent rho A x := by
  simp [inducedConformalExponent, hA x]

/-- The induced Jacobian is strictly positive. -/
theorem inducedJacobian_pos {X : Type*} (rho : X → ℝ) (A : X → X) (x : X) :
    0 < inducedJacobian rho A x := Real.exp_pos _

/-- Equation `(46)`: involutivity forces pointwise Jacobian reciprocity. -/
theorem inducedJacobian_reciprocal {X : Type*} (rho : X → ℝ) (A : X → X)
    (hA : Function.Involutive A) (x : X) :
    inducedJacobian rho A (A x) * inducedJacobian rho A x = 1 := by
  rw [inducedJacobian, inducedConformalExponent_apply rho A hA x, inducedJacobian]
  rw [← Real.exp_add]
  simp

/-- Equations `(45)`--`(47)`: attained positive extrema of a reciprocal Jacobian are reciprocal.
The extrema hypotheses are exactly the unpacked meaning of `min` and `max` on the compact slice. -/
theorem extrema_reciprocal_of_involutive {X : Type*} [Nonempty X]
    (A : X → X) (J : X → ℝ) (Jmin Jmax : ℝ)
    (hmin : ∀ x, Jmin ≤ J x) (hmax : ∀ x, J x ≤ Jmax)
    (hminpos : 0 < Jmin)
    (hminAttained : ∃ x, J x = Jmin) (hmaxAttained : ∃ x, J x = Jmax)
    (hrecip : ∀ x, J (A x) * J x = 1) :
    Jmax = Jmin⁻¹ := by
  obtain ⟨xmin, hxmin⟩ := hminAttained
  obtain ⟨xmax, hxmax⟩ := hmaxAttained
  have hupper := hmax (A xmin)
  have hlower := hmin (A xmax)
  have hrecMin := hrecip xmin
  have hrecMax := hrecip xmax
  rw [hxmin] at hrecMin
  rw [hxmax] at hrecMax
  have hminxmax := hmin xmax
  rw [hxmax] at hminxmax
  have hJmaxpos : 0 < Jmax := lt_of_lt_of_le hminpos hminxmax
  have hprodLe : Jmin * Jmax ≤ 1 := by
    have := mul_le_mul_of_nonneg_right hlower hJmaxpos.le
    nlinarith
  have hprodGe : 1 ≤ Jmin * Jmax := by
    have := mul_le_mul_of_nonneg_right hupper hminpos.le
    nlinarith
  have hprod : Jmin * Jmax = 1 := le_antisymm hprodLe hprodGe
  calc
    Jmax = 1 / Jmin := (eq_div_iff hminpos.ne').2 (by nlinarith [hprod])
    _ = Jmin⁻¹ := one_div _

/-- Equation `(49)`: centred antipodal mismatch, using mathlib's measure average. -/
def centeredAntipodalMismatch {X : Type*} [MeasurableSpace X]
    (mu : Measure X) (A : X → X) (f : X → ℝ) (x : X) : ℝ :=
  (f x - ⨍ y, f y ∂mu) - (f (A x) - ⨍ y, f (A y) ∂mu)

/-- The centred mismatch is integrable whenever both fields entering it are integrable. -/
theorem integrable_centeredAntipodalMismatch {X : Type*} [MeasurableSpace X]
    (mu : Measure X) [IsFiniteMeasure mu] (A : X → X) (f : X → ℝ)
    (hf : Integrable f mu) (hfA : Integrable (f ∘ A) mu) :
    Integrable (centeredAntipodalMismatch mu A f) mu := by
  change Integrable (fun x => (f x - ⨍ y, f y ∂mu) -
    ((f ∘ A) x - ⨍ y, (f ∘ A) y ∂mu)) mu
  exact (hf.sub (integrable_const _)).sub (hfA.sub (integrable_const _))

/-- The field in equation `(49)` has zero spatial mean, the prerequisite used in equation `(52)`. -/
theorem integral_centeredAntipodalMismatch_eq_zero {X : Type*} [MeasurableSpace X]
    (mu : Measure X) [IsFiniteMeasure mu] (A : X → X) (f : X → ℝ)
    (hf : Integrable f mu) (hfA : Integrable (f ∘ A) mu) :
    ∫ x, centeredAntipodalMismatch mu A f x ∂mu = 0 := by
  change ∫ x, (f x - ⨍ y, f y ∂mu) -
    ((f ∘ A) x - ⨍ y, (f ∘ A) y ∂mu) ∂mu = 0
  calc
    _ = (∫ x, f x - ⨍ y, f y ∂mu ∂mu) -
        ∫ x, (f ∘ A) x - ⨍ y, (f ∘ A) y ∂mu ∂mu :=
      integral_sub' (hf.sub (integrable_const _)) (hfA.sub (integrable_const _))
    _ = 0 := by rw [integral_sub_average, integral_sub_average, sub_zero]

end

end GaloisForLFunctions.HTGeometry
