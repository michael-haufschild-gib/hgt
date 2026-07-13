import GaloisForLFunctions.HTGeometry.RieszBrothersReduction
import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Riesz--Fischer reduction of the Riesz-brothers input

This module formalizes the Riesz--Fischer step in the cofinal Cholesky manuscript.  A
square-summable analytic half-line is extended by zero to an `ℓ²(ℤ)` sequence, reconstructed as
an `L²` function by the Fourier Hilbert basis on the additive circle, and transported to the
multiplicative circle.  Consequently the square-summable Riesz-brothers conclusion reduces
exactly to the classical vanishing-half-line F. and M. Riesz theorem.

No F. and M. Riesz theorem is assumed silently: its remaining conclusion is exposed by
`HasFAndMRieszVanishingConclusion`.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory
open scoped ENNReal NNReal lp

noncomputable section

/-- The measurable equivalence from the unit additive circle to the multiplicative circle. -/
noncomputable def addCircleCircleEquiv : AddCircle (1 : ℝ) ≃ᵐ Circle :=
  (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).toMeasurableEquiv

/-- The additive-to-multiplicative circle equivalence preserves normalized Haar probability. -/
noncomputable def addCircleCircleMeasurePreserving :
    MeasurePreserving addCircleCircleEquiv
      (@AddCircle.haarAddCircle (1 : ℝ) inferInstance) circleLebesgue :=
  ⟨addCircleCircleEquiv.measurable, rfl⟩

/-- Pull an `L²` function on the multiplicative circle back to the additive circle. -/
noncomputable def circleLpToAddCircleLinearIsometry :
    Lp ℂ 2 circleLebesgue →ₗᵢ[ℂ]
      Lp ℂ 2 (@AddCircle.haarAddCircle (1 : ℝ) inferInstance) :=
  Lp.compMeasurePreservingₗᵢ ℂ addCircleCircleEquiv addCircleCircleMeasurePreserving

private theorem circleLpToAddCircleLinearIsometry_surjective :
    Function.Surjective (circleLpToAddCircleLinearIsometry :
      Lp ℂ 2 circleLebesgue →
        Lp ℂ 2 (@AddCircle.haarAddCircle (1 : ℝ) inferInstance)) := by
  intro g
  let hmpInv := addCircleCircleMeasurePreserving.symm addCircleCircleEquiv
  let h : Lp ℂ 2 circleLebesgue :=
    Lp.compMeasurePreserving addCircleCircleEquiv.symm hmpInv g
  refine ⟨h, ?_⟩
  change Lp.compMeasurePreserving addCircleCircleEquiv
      addCircleCircleMeasurePreserving
      (Lp.compMeasurePreserving addCircleCircleEquiv.symm hmpInv g) = g
  rw [← Lp.compMeasurePreserving_comp_apply g hmpInv
    addCircleCircleMeasurePreserving]
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving g
    (hmpInv.comp addCircleCircleMeasurePreserving)] with x hx
  convert hx using 1
  all_goals simp [Function.comp_apply]

/-- The unit additive and multiplicative circle `L²` spaces are linearly isometric. -/
noncomputable def circleLpAddCircleLinearIsometryEquiv :
    Lp ℂ 2 circleLebesgue ≃ₗᵢ[ℂ]
      Lp ℂ 2 (@AddCircle.haarAddCircle (1 : ℝ) inferInstance) :=
  LinearIsometryEquiv.ofSurjective circleLpToAddCircleLinearIsometry
    circleLpToAddCircleLinearIsometry_surjective

private theorem coe_toCircle_nsmul (x : AddCircle (1 : ℝ)) (n : ℕ) :
    ((((n • x).toCircle : Circle)) : ℂ) = (((x.toCircle : Circle)) : ℂ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [succ_nsmul, AddCircle.toCircle_add, Circle.coe_mul, pow_succ, ih]

/-- Pullback sends the `n`th multiplicative monomial to the `n`th additive Fourier vector. -/
theorem circleLpToAddCircleLinearIsometry_circleMonomial (n : ℕ) :
    circleLpToAddCircleLinearIsometry (circleMonomialLp circleLebesgue n) =
      (fourierLp 2 (n : ℤ) :
        Lp ℂ 2 (@AddCircle.haarAddCircle (1 : ℝ) inferInstance)) := by
  change Lp.compMeasurePreserving addCircleCircleEquiv
      addCircleCircleMeasurePreserving
      ((circleMonomial_memLp circleLebesgue n).toLp
        (fun z : Circle => (z : ℂ) ^ n)) = _
  rw [Lp.toLp_compMeasurePreserving]
  apply Lp.ext
  filter_upwards
    [((circleMonomial_memLp circleLebesgue n).comp_measurePreserving
      addCircleCircleMeasurePreserving).coeFn_toLp,
      coeFn_fourierLp 2 (n : ℤ)] with x hx hfourier
  rw [hx, hfourier]
  simp only [Function.comp_apply, addCircleCircleEquiv, fourier_apply]
  change (((AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero x : Circle) : ℂ) ^ n) =
    (((((n : ℤ) • x).toCircle : Circle)) : ℂ)
  rw [AddCircle.homeomorphCircle_apply]
  exact (coe_toCircle_nsmul x n).symm

/-- Extend a one-sided coefficient sequence by zero on the strictly negative integers. -/
def nonnegativeIntExtension (c : ℕ → ℂ) (k : ℤ) : ℂ :=
  if 0 ≤ k then c k.toNat else 0

@[simp] theorem nonnegativeIntExtension_ofNat (c : ℕ → ℂ) (n : ℕ) :
    nonnegativeIntExtension c (n : ℤ) = c n := by
  simp [nonnegativeIntExtension]

@[simp] theorem nonnegativeIntExtension_negSucc (c : ℕ → ℂ) (n : ℕ) :
    nonnegativeIntExtension c (Int.negSucc n) = 0 := by
  simp [nonnegativeIntExtension]

/-- Zero-extension from the analytic half-line preserves square summability. -/
theorem nonnegativeIntExtension_memℓp_two (c : ℕ → ℂ) (hc : Memℓp c 2) :
    Memℓp (nonnegativeIntExtension c) 2 := by
  apply memℓp_gen
  have hsum : Summable (fun n : ℕ => ‖c n‖ ^ (2 : ℝ)) := by
    simpa using hc.summable (by norm_num)
  rw [summable_int_iff_summable_nat_and_neg]
  constructor
  · simpa using hsum
  · apply summable_of_ne_finset_zero (s := {0})
    intro n hn
    have hn0 : n ≠ 0 := by simpa using hn
    simp [nonnegativeIntExtension, hn0]

/-- The `L²` circle function reconstructed from a square-summable analytic half-line. -/
noncomputable def circleRieszFischerOfNat
    (c : ℕ → ℂ) (hc : Memℓp c 2) : Lp ℂ 2 circleLebesgue :=
  circleLpAddCircleLinearIsometryEquiv.symm
    (fourierBasis.repr.symm
      (⟨nonnegativeIntExtension c, nonnegativeIntExtension_memℓp_two c hc⟩ :
        lp (fun _ : ℤ => ℂ) 2))

/-- Riesz--Fischer reconstruction has exactly the prescribed analytic monomial coefficients. -/
theorem circleMonomialLp_inner_circleRieszFischerOfNat
    (c : ℕ → ℂ) (hc : Memℓp c 2) (n : ℕ) :
    inner ℂ (circleMonomialLp circleLebesgue n)
      (circleRieszFischerOfNat c hc) = c n := by
  let a : lp (fun _ : ℤ => ℂ) 2 :=
    ⟨nonnegativeIntExtension c, nonnegativeIntExtension_memℓp_two c hc⟩
  let g : Lp ℂ 2 (@AddCircle.haarAddCircle (1 : ℝ) inferInstance) :=
    fourierBasis.repr.symm a
  let U := circleLpAddCircleLinearIsometryEquiv
  calc
    inner ℂ (circleMonomialLp circleLebesgue n)
        (circleRieszFischerOfNat c hc) =
      inner ℂ (U (circleMonomialLp circleLebesgue n))
        (U (circleRieszFischerOfNat c hc)) :=
          (U.inner_map_map _ _).symm
    _ = inner ℂ (fourierLp 2 (n : ℤ)) g := by
      rw [show U (circleMonomialLp circleLebesgue n) = fourierLp 2 (n : ℤ) by
        simpa [U, circleLpAddCircleLinearIsometryEquiv] using
          circleLpToAddCircleLinearIsometry_circleMonomial n]
      congr 1
      simp [U, g, a, circleRieszFischerOfNat,
        circleLpAddCircleLinearIsometryEquiv]
    _ = a (n : ℤ) := by
      rw [← show fourierBasis (n : ℤ) = fourierLp 2 (n : ℤ) by
        exact congrFun coe_fourierBasis (n : ℤ)]
      rw [← HilbertBasis.repr_apply_apply]
      simp [g]
    _ = c n := by simp [a]

/-- The F. and M. Riesz vanishing-half-line conclusion in the exact two-density form obtained
after Riesz--Fischer reconstruction of the square-summable half-line. -/
def HasFAndMRieszVanishingConclusion
    (mu : Measure Circle) [IsFiniteMeasure mu] : Prop :=
  ∀ (y : Lp ℂ 2 mu) (h : Lp ℂ 2 circleLebesgue),
    (∀ n : ℕ,
      inner ℂ (circleMonomialLp mu n) y =
        inner ℂ (circleMonomialLp circleLebesgue n) h) →
      mu.withDensityᵥ (⇑y) - circleLebesgue.withDensityᵥ (⇑h) ≪ᵥ
        circleLebesgue.toENNRealVectorMeasure

/-- Riesz--Fischer reconstruction reduces the square-summable Riesz-brothers input to the
classical vanishing-half-line F. and M. Riesz theorem. -/
theorem hasRieszBrothersDensityConclusion_of_fAndMRieszVanishing
    (mu : Measure Circle) [IsFiniteMeasure mu]
    (hfm : HasFAndMRieszVanishingConclusion mu) :
    HasRieszBrothersDensityConclusion mu circleLebesgue := by
  intro y hy
  let c : ℕ → ℂ := fun n => inner ℂ (circleMonomialLp mu n) y
  let h : Lp ℂ 2 circleLebesgue := circleRieszFischerOfNat c hy
  have hcoeff : ∀ n : ℕ,
      inner ℂ (circleMonomialLp mu n) y =
        inner ℂ (circleMonomialLp circleLebesgue n) h := by
    intro n
    symm
    exact circleMonomialLp_inner_circleRieszFischerOfNat c hy n
  have hres := hfm y h hcoeff
  have hhInt : Integrable (⇑h) circleLebesgue :=
    (Lp.memLp h).integrable (by norm_num)
  have hhac : circleLebesgue.withDensityᵥ (⇑h) ≪ᵥ
      circleLebesgue.toENNRealVectorMeasure :=
    withDensityV_absolutelyContinuous_toENNReal circleLebesgue (⇑h) hhInt
  rw [← sub_add_cancel (mu.withDensityᵥ (⇑y))
    (circleLebesgue.withDensityᵥ (⇑h))]
  exact hres.add hhac

end

end GaloisForLFunctions.HTGeometry
