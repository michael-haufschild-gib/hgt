import GaloisForLFunctions.RHTower.Deninger.DeningerStageCurrent
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Algebra.Colimit.Module

/-!
# The archimedean current on the pro-Ind model

The archimedean currents of the finite character stages are compatible with the transitions when the
place averages are, so they glue to a single functional on the filtered colimit of the stage
cohomologies.  Composing with the universal property of the exterior algebra lifts that functional to
a square-zero algebra map on the pro-Ind model.

Its continuity is the elementary bound on integration over a part of a measure space: the modulus of
the integral of a function over a subset is at most the integral of its modulus over the whole space.

* `RHTower.deningerProIndCurrent` : the archimedean current on the colimit of the stage cohomologies.
* `RHTower.deningerProIndLift` : its square-zero algebra lift.
* `RHTower.deningerArchimedean_norm_le` : the `L¹` bound.
-/

set_option maxSynthPendingDepth 3

namespace RHTower

open Complex Finset Module

section ProInd

variable {ι : Type*} [Preorder ι] [DecidableEq ι]

/-- The directed system of first cohomologies of the character stages. -/
noncomputable def deningerStageCohomologySystem (r : ι → ℕ)
    (m : ∀ i j, i ≤ j → Fin (r i) → Fin (r j) → ℤ) (i j : ι) (h : i ≤ j) :
    deningerCohomology (r i) 0 →ₗ[ℂ] deningerCohomology (r j) 0 :=
  deningerCohomologyMap (m i j h) 0

/-- **The archimedean current on the pro-Ind model.**  The stage currents agree along every
transition when the place averages are related by the exponent matrix, so they descend to the
filtered colimit. -/
noncomputable def deningerProIndCurrent (r : ι → ℕ)
    (m : ∀ i j, i ≤ j → Fin (r i) → Fin (r j) → ℤ) (ell : ∀ i, Fin (r i) → ℂ)
    (hcompat : ∀ (i j : ι) (h : i ≤ j) (a : Fin (r i)),
      ell i a = ∑ b, (m i j h a b : ℂ) * ell j b) :
    Module.DirectLimit (fun i => deningerCohomology (r i) 0)
        (deningerStageCohomologySystem r m) →ₗ[ℂ] ℂ :=
  Module.DirectLimit.lift ℂ ι (fun i => deningerCohomology (r i) 0)
    (deningerStageCohomologySystem r m) (fun i => deningerStageCurrent (r i) (ell i)) (by
    intro i j h x
    have hnat := deningerStageCurrent_natural (m i j h) (ell j)
    have hell : (fun a => ∑ b, (m i j h a b : ℂ) * ell j b) = ell i := by
      funext a
      exact (hcompat i j h a).symm
    rw [hell] at hnat
    exact congrArg (fun L : deningerCohomology (r i) 0 →ₗ[ℂ] ℂ => L x) hnat)

/-- The pro-Ind current restricts on each stage to the stage current. -/
theorem deningerProIndCurrent_of (r : ι → ℕ)
    (m : ∀ i j, i ≤ j → Fin (r i) → Fin (r j) → ℤ) (ell : ∀ i, Fin (r i) → ℂ)
    (hcompat : ∀ (i j : ι) (h : i ≤ j) (a : Fin (r i)),
      ell i a = ∑ b, (m i j h a b : ℂ) * ell j b) (i : ι) (x : deningerCohomology (r i) 0) :
    deningerProIndCurrent r m ell hcompat
        (Module.DirectLimit.of ℂ ι (fun i => deningerCohomology (r i) 0)
          (deningerStageCohomologySystem r m) i x)
      = deningerStageCurrent (r i) (ell i) x :=
  Module.DirectLimit.lift_of (R := ℂ) (ι := ι) (G := fun i => deningerCohomology (r i) 0)
    (f := deningerStageCohomologySystem r m) (fun i => deningerStageCurrent (r i) (ell i)) _ x

/-- The value of the pro-Ind current on a Kummer class of a stage is the archimedean place average
of that stage. -/
theorem deningerProIndCurrent_kummer (r : ι → ℕ)
    (m : ∀ i j, i ≤ j → Fin (r i) → Fin (r j) → ℤ) (ell : ∀ i, Fin (r i) → ℂ)
    (hcompat : ∀ (i j : ι) (h : i ≤ j) (a : Fin (r i)),
      ell i a = ∑ b, (m i j h a b : ℂ) * ell j b) (i : ι) (a : Fin (r i) → ℂ) :
    deningerProIndCurrent r m ell hcompat
        (Module.DirectLimit.of ℂ ι (fun i => deningerCohomology (r i) 0)
          (deningerStageCohomologySystem r m) i (deningerKummerClass (r i) a))
      = ∑ c, a c * ell i c := by
  rw [deningerProIndCurrent_of, deningerStageCurrent_kummer]

/-- **The square-zero derived algebra map on the pro-Ind model.**  The universal property of the
exterior algebra lifts the pro-Ind current to a unital algebra map into `ℂ[ε]/(ε²)`. -/
noncomputable def deningerProIndLift (r : ι → ℕ)
    (m : ∀ i j, i ≤ j → Fin (r i) → Fin (r j) → ℤ) (ell : ∀ i, Fin (r i) → ℂ)
    (hcompat : ∀ (i j : ι) (h : i ≤ j) (a : Fin (r i)),
      ell i a = ∑ b, (m i j h a b : ℂ) * ell j b) :
    ExteriorAlgebra ℂ (Module.DirectLimit (fun i => deningerCohomology (r i) 0)
        (deningerStageCohomologySystem r m)) →ₐ[ℂ] TrivSqZeroExt ℂ ℂ :=
  deningerArchimedeanLift (deningerProIndCurrent r m ell hcompat)

/-- Products of two positive-degree generators are killed by the pro-Ind lift. -/
theorem deningerProIndLift_mul_eq_zero (r : ι → ℕ)
    (m : ∀ i j, i ≤ j → Fin (r i) → Fin (r j) → ℤ) (ell : ∀ i, Fin (r i) → ℂ)
    (hcompat : ∀ (i j : ι) (h : i ≤ j) (a : Fin (r i)),
      ell i a = ∑ b, (m i j h a b : ℂ) * ell j b)
    (x y : Module.DirectLimit (fun i => deningerCohomology (r i) 0)
      (deningerStageCohomologySystem r m)) :
    deningerProIndLift r m ell hcompat (ExteriorAlgebra.ι ℂ x * ExteriorAlgebra.ι ℂ y) = 0 :=
  deningerArchimedeanLift_mul_eq_zero _ x y

end ProInd

section Bound

open MeasureTheory

/-- **The archimedean functional is bounded by the `L¹` norm.**  It is integration of a function
over the archimedean part of the place space, so its modulus is at most the integral of the modulus
there, which is at most the integral of the modulus over the whole place space. -/
theorem deningerArchimedean_norm_le {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) (S : Set Y)
    (f : Y → ℂ) (hf : Integrable f μ) : ‖∫ y in S, f y ∂μ‖ ≤ ∫ y, ‖f y‖ ∂μ :=
  le_trans (norm_integral_le_integral_norm _)
    (setIntegral_le_integral hf.norm (Filter.Eventually.of_forall fun _ => norm_nonneg _))

end Bound

end RHTower
