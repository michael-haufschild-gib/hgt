/-
# Semilocal prolate finite part from compression alone

The central physical and Fourier Sonin cutoffs determine a one-way boundary transition
`L_a = (1 - P_F) P_X P_F`.  This file defines its positive energy `L_a† L_a` as the
prolate finite-part carrier.  No prime, Euler, Gamma, Weil, Xi, or completed-source object
appears in the construction.

The resulting carrier is genuinely trace class, not merely an `opTrace` expression.  Its trace
is the nonnegative finite part and agrees exactly with the real trace of the prolate impurity
`T_a - T_a²`.  Packaging `0 < a` in the aperture type leaves every exported theorem free of
analytic or arithmetic premises.
-/
import GaloisForLFunctions.RHTower.SoninProlateCommutatorEnergy
import Mathlib.Analysis.InnerProductSpace.Positive

noncomputable section

namespace RHTower

open ContinuousLinearMap

/-- A strictly positive central Sonin aperture, with positivity internalized in the data rather
than left as a theorem premise. -/
def SemilocalSoninAperture := {a : ℝ // 0 < a}

/-- The one-way physical/Fourier boundary transition determined by the semilocal compression at
aperture `a`. -/
def semilocalSoninProlateTransition (a : SemilocalSoninAperture) :
    SoninL2 →L[ℂ] SoninL2 :=
  crossBoundary (centralFourierForbidden a.1).starProjection
    (centralPhysicalForbidden a.1).starProjection

/-- Positive trace-class carrier of the compression-derived prolate finite part. -/
def semilocalSoninProlateFinitePartCarrier (a : SemilocalSoninAperture) :
    SoninL2 →L[ℂ] SoninL2 :=
  ContinuousLinearMap.adjoint (semilocalSoninProlateTransition a) ∘L
    semilocalSoninProlateTransition a

/-- The scalar prolate finite part: squared Hilbert--Schmidt boundary leakage of the semilocal
compression. -/
def semilocalSoninProlateFinitePart (a : SemilocalSoninAperture) : ℝ :=
  hsNormSq (semilocalSoninProlateTransition a)

/-- The compression-determined boundary transition is Hilbert--Schmidt. -/
theorem semilocalSoninProlateTransition_isHilbertSchmidt
    (a : SemilocalSoninAperture) :
    IsHilbertSchmidt (semilocalSoninProlateTransition a) := by
  exact centralProlateTransition_isHilbertSchmidt a.1 a.2

/-- The prolate finite-part carrier is trace class without a source-side regularization. -/
theorem semilocalSoninProlateFinitePartCarrier_isTraceClass
    (a : SemilocalSoninAperture) :
    IsTraceClass (semilocalSoninProlateFinitePartCarrier a) := by
  exact (semilocalSoninProlateTransition_isHilbertSchmidt a).adjoint_comp_self_isTraceClass

/-- The finite-part carrier is positive. -/
theorem semilocalSoninProlateFinitePartCarrier_isPositive
    (a : SemilocalSoninAperture) :
    (semilocalSoninProlateFinitePartCarrier a).IsPositive := by
  exact ContinuousLinearMap.isPositive_adjoint_comp_self
    (semilocalSoninProlateTransition a)

/-- The actual trace of the positive carrier is the real finite part, including the vanishing
imaginary coordinate. -/
theorem opTrace_semilocalSoninProlateFinitePartCarrier
    (a : SemilocalSoninAperture) :
    opTrace (semilocalSoninProlateFinitePartCarrier a) =
      (semilocalSoninProlateFinitePart a : ℂ) := by
  rw [semilocalSoninProlateFinitePartCarrier,
    ContinuousLinearMap.opTrace_adjoint_comp_self]
  apply Complex.ext
  · exact hsInner_self_re (semilocalSoninProlateTransition_isHilbertSchmidt a)
  · rw [Complex.ofReal_im]
    change (∑' i, inner ℂ
      (semilocalSoninProlateTransition a (hsBasis ℂ SoninL2 i))
      (semilocalSoninProlateTransition a (hsBasis ℂ SoninL2 i))).im = 0
    rw [Complex.im_tsum
      ((semilocalSoninProlateTransition_isHilbertSchmidt a).summable_inner
        (semilocalSoninProlateTransition_isHilbertSchmidt a) (hsBasis ℂ SoninL2))]
    have hzero :
        (fun i => (inner ℂ
          (semilocalSoninProlateTransition a (hsBasis ℂ SoninL2 i))
          (semilocalSoninProlateTransition a (hsBasis ℂ SoninL2 i))).im) =
          fun _ => 0 := by
      funext i
      simpa using inner_self_im (𝕜 := ℂ)
        (semilocalSoninProlateTransition a (hsBasis ℂ SoninL2 i))
    rw [hzero, tsum_zero]

/-- The independently constructed finite part is nonnegative. -/
theorem semilocalSoninProlateFinitePart_nonneg
    (a : SemilocalSoninAperture) :
    0 ≤ semilocalSoninProlateFinitePart a := by
  exact hsNormSq_nonneg _

/-- The trace finite part of the positive boundary carrier is exactly the real trace of the
prolate compression impurity. -/
theorem semilocalSoninProlateFinitePart_eq_prolateImpurityTrace
    (a : SemilocalSoninAperture) :
    semilocalSoninProlateFinitePart a =
      Complex.re
        (opTrace
          (soninAlternatingBlock (centralPhysicalForbidden a.1)
            (centralFourierForbidden a.1) -
            soninAlternatingBlock (centralPhysicalForbidden a.1)
              (centralFourierForbidden a.1) *
              soninAlternatingBlock (centralPhysicalForbidden a.1)
                (centralFourierForbidden a.1))) := by
  exact (re_opTrace_centralProlateImpurity_eq_transition_hsNormSq a.1 a.2).symm

/-- Exact finite-aperture splitting: retained prolate energy plus the independently constructed
finite part is the Shannon area. -/
theorem hsNormSq_centralProlateBlock_add_semilocalSoninProlateFinitePart_eq_four_mul_sq
    (a : SemilocalSoninAperture) :
    hsNormSq
        (soninAlternatingBlock (centralPhysicalForbidden a.1)
          (centralFourierForbidden a.1)) +
      semilocalSoninProlateFinitePart a = 4 * a.1 ^ 2 := by
  exact hsNormSq_centralProlateBlock_add_transition_eq_four_mul_sq a.1 a.2

/-- Aperture-area upper bound for the source-free finite part. -/
theorem semilocalSoninProlateFinitePart_le_apertureArea
    (a : SemilocalSoninAperture) :
    semilocalSoninProlateFinitePart a ≤ 4 * a.1 ^ 2 := by
  have hbudget :=
    hsNormSq_centralProlateBlock_add_semilocalSoninProlateFinitePart_eq_four_mul_sq a
  have hblock : 0 ≤ hsNormSq
      (soninAlternatingBlock (centralPhysicalForbidden a.1)
        (centralFourierForbidden a.1)) :=
    hsNormSq_nonneg _
  linarith

/-- The source-free prolate finite part lies in its exact aperture interval. -/
theorem semilocalSoninProlateFinitePart_mem_apertureArea
    (a : SemilocalSoninAperture) :
    0 ≤ semilocalSoninProlateFinitePart a ∧
      semilocalSoninProlateFinitePart a ≤ 4 * a.1 ^ 2 :=
  ⟨semilocalSoninProlateFinitePart_nonneg a,
    semilocalSoninProlateFinitePart_le_apertureArea a⟩

end RHTower
