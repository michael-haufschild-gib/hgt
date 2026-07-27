import GaloisForLFunctions.RHTower.FieldOneFiniteAdeleL2WeylMultiplier
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Semilocal `L²` Weyl multiplier

On the product of the real additive group and the rational finite adeles,
combine the normalized archimedean phase
`exp (-2π i a∞ x∞)` with the standard finite-adele phase.  Their product has
norm one and therefore acts unitarily on complex `L²` for the product of
Lebesgue and finite-adele Haar measure.

This is the analytic product-space realization of the same phase used by the
algebraic Schwartz--Bruhat tensor action.  It does not identify the algebraic
tensor with a completed Hilbert tensor and makes no trace, spectral, or
positivity assertion.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open MeasureTheory

/-- Product Haar measure on the additive semilocal ring `ℝ × 𝔸_f`.

The finite-adele factor is placed first when forming `Measure.prod`, so the
sigma-finite real factor is on the right; the measure is then transported by
coordinate swap.  This orientation gives the usual open-positive product
measure without assuming a not-yet-formalized sigma-finiteness theorem for
finite-adele Haar measure. -/
noncomputable abbrev fieldOneSemilocalAddHaar :
    Measure (ℝ × FieldOneFiniteAdele) :=
  Measure.map Prod.swap
    (fieldOneFiniteAdeleAddHaar.prod (volume : Measure ℝ))

noncomputable instance fieldOneSemilocalAddHaarIsOpenPosMeasure :
    fieldOneSemilocalAddHaar.IsOpenPosMeasure :=
  continuous_swap.isOpenPosMeasure_map Prod.swap_surjective

/-- Product of the standard normalized real and finite-adele Weyl phases. -/
def fieldOneSemilocalL2WeylPhase
    (a x : ℝ × FieldOneFiniteAdele) : ℂ :=
  HTGeometry.FieldOneCore.fieldOneArchimedeanPhase
      (2 * Real.pi * a.1) x.1 *
    fieldOneFiniteAdeleL2WeylPhase a.2 x.2

theorem fieldOneSemilocalL2WeylPhase_continuous
    (a : ℝ × FieldOneFiniteAdele) :
    Continuous (fieldOneSemilocalL2WeylPhase a) := by
  apply Continuous.mul
  · dsimp only [fieldOneSemilocalL2WeylPhase,
      HTGeometry.FieldOneCore.fieldOneArchimedeanPhase,
      HTGeometry.scalarWeylCharacter]
    fun_prop
  · exact
      (fieldOneFiniteAdeleL2WeylPhase_continuous a.2).comp
        continuous_snd

@[simp]
theorem norm_fieldOneSemilocalL2WeylPhase
    (a x : ℝ × FieldOneFiniteAdele) :
    ‖fieldOneSemilocalL2WeylPhase a x‖ = 1 := by
  simp [fieldOneSemilocalL2WeylPhase]

/-- Semilocal phase packaged for the general `L²` unitary construction. -/
def fieldOneSemilocalUnitModulusL2Phase
    (a : ℝ × FieldOneFiniteAdele) :
    UnitModulusL2Phase
      (ℝ × FieldOneFiniteAdele) fieldOneSemilocalAddHaar where
  toFun := fieldOneSemilocalL2WeylPhase a
  aestronglyMeasurable :=
    (fieldOneSemilocalL2WeylPhase_continuous a).aestronglyMeasurable
  norm_eq_one :=
    Filter.Eventually.of_forall
      (norm_fieldOneSemilocalL2WeylPhase a)

/-- Unitary semilocal Weyl multiplier on product Haar `L²`. -/
def fieldOneSemilocalL2WeylUnitary
    (a : ℝ × FieldOneFiniteAdele) :
    Lp ℂ 2 fieldOneSemilocalAddHaar ≃ₗᵢ[ℂ]
      Lp ℂ 2 fieldOneSemilocalAddHaar :=
  (fieldOneSemilocalUnitModulusL2Phase a).mulUnitary

theorem fieldOneSemilocalL2WeylUnitary_ae
    (a : ℝ × FieldOneFiniteAdele)
    (f : Lp ℂ 2 fieldOneSemilocalAddHaar) :
    fieldOneSemilocalL2WeylUnitary a f
      =ᵐ[fieldOneSemilocalAddHaar]
        fun x => fieldOneSemilocalL2WeylPhase a x * f x :=
  (fieldOneSemilocalUnitModulusL2Phase a).mulUnitary_ae f

theorem fieldOneSemilocalL2WeylPhase_add
    (a b x : ℝ × FieldOneFiniteAdele) :
    fieldOneSemilocalL2WeylPhase (a + b) x =
      fieldOneSemilocalL2WeylPhase a x *
        fieldOneSemilocalL2WeylPhase b x := by
  have hscale :
      2 * Real.pi * (a + b).1 =
        2 * Real.pi * a.1 + 2 * Real.pi * b.1 := by
    simp only [Prod.fst_add]
    ring
  rw [fieldOneSemilocalL2WeylPhase,
    fieldOneSemilocalL2WeylPhase,
    fieldOneSemilocalL2WeylPhase,
    hscale,
    HTGeometry.FieldOneCore.fieldOneArchimedeanPhase_add]
  simp only [Prod.snd_add, fieldOneFiniteAdeleL2WeylPhase, add_mul]
  rw [AddChar.map_add_eq_mul]
  simp only [Pi.mul_apply]
  ring

theorem fieldOneSemilocalL2WeylUnitary_add_apply
    (a b : ℝ × FieldOneFiniteAdele)
    (f : Lp ℂ 2 fieldOneSemilocalAddHaar) :
    fieldOneSemilocalL2WeylUnitary a
        (fieldOneSemilocalL2WeylUnitary b f) =
      fieldOneSemilocalL2WeylUnitary (a + b) f := by
  apply Lp.ext
  filter_upwards [
    fieldOneSemilocalL2WeylUnitary_ae b f,
    fieldOneSemilocalL2WeylUnitary_ae a
      (fieldOneSemilocalL2WeylUnitary b f),
    fieldOneSemilocalL2WeylUnitary_ae (a + b) f]
    with x hb ha hab
  rw [ha, hb, hab, fieldOneSemilocalL2WeylPhase_add]
  ring

/-- Rational diagonal specialization of the semilocal Haar-`L²` Weyl
action. -/
def fieldOneRationalDiagonalL2WeylUnitary (q : ℚ) :
    Lp ℂ 2 fieldOneSemilocalAddHaar ≃ₗᵢ[ℂ]
      Lp ℂ 2 fieldOneSemilocalAddHaar :=
  fieldOneSemilocalL2WeylUnitary
    (fieldOneRationalDiagonalSemilocalParameter q)

theorem fieldOneRationalDiagonalL2WeylUnitary_add_apply
    (q r : ℚ)
    (f : Lp ℂ 2 fieldOneSemilocalAddHaar) :
    fieldOneRationalDiagonalL2WeylUnitary q
        (fieldOneRationalDiagonalL2WeylUnitary r f) =
      fieldOneRationalDiagonalL2WeylUnitary (q + r) f := by
  rw [fieldOneRationalDiagonalL2WeylUnitary,
    fieldOneRationalDiagonalL2WeylUnitary,
    fieldOneRationalDiagonalL2WeylUnitary,
    fieldOneSemilocalL2WeylUnitary_add_apply,
    map_add]

end

end GaloisForLFunctions.RHTower
