import GaloisForLFunctions.HTGeometry.SzegoBoundaryH2

/-!
# Two-sided circle Fourier vectors for one-sided Riesz--Fischer reconstructions

The existing Riesz--Fischer reconstruction prescribes the analytic coefficients indexed by
natural numbers.  This module exposes the full integer Fourier basis on the multiplicative
circle and proves that the reconstructed function has zero coefficients on the negative
half-line.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Complex Filter Topology Set
open scoped ENNReal NNReal lp

noncomputable section

/-- Every integer circle monomial belongs to `L²` of a finite circle measure. -/
theorem circleZMonomial_memLp (mu : Measure Circle) [IsFiniteMeasure mu] (k : ℤ) :
    MemLp (fun z : Circle => (z : ℂ) ^ k) 2 mu := by
  have hcont : Continuous (fun z : Circle => (z : ℂ) ^ k) :=
    (continuousOn_zpow₀ k).comp_continuous continuous_subtype_val (fun z => by simp)
  apply MemLp.of_bound hcont.aestronglyMeasurable 1
  filter_upwards with z
  rw [norm_zpow]
  simp

/-- The integer monomial `z ↦ zᵏ` as an `L²` vector. -/
noncomputable def circleZMonomialLp
    (mu : Measure Circle) [IsFiniteMeasure mu] (k : ℤ) : Lp ℂ 2 mu :=
  MemLp.toLp (fun z : Circle => (z : ℂ) ^ k) (circleZMonomial_memLp mu k)

theorem circleZMonomialLp_coeFn_ae
    (mu : Measure Circle) [IsFiniteMeasure mu] (k : ℤ) :
    ⇑(circleZMonomialLp mu k) =ᵐ[mu] fun z : Circle => (z : ℂ) ^ k :=
  (circleZMonomial_memLp mu k).coeFn_toLp

/-- The integer monomial inner product is its corresponding weighted Fourier integral. -/
theorem circleZMonomialLp_inner (mu : Measure Circle) [IsFiniteMeasure mu]
    (k : ℤ) (y : Lp ℂ 2 mu) :
    inner ℂ (circleZMonomialLp mu k) y =
      ∫ z : Circle, ⇑y z * (starRingEnd ℂ) ((z : ℂ) ^ k) ∂mu := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [circleZMonomialLp_coeFn_ae mu k] with z hz
  rw [hz, RCLike.inner_apply]

/-- Pullback sends every integer multiplicative monomial to the corresponding additive Fourier
vector. -/
theorem circleLpToAddCircleLinearIsometry_circleZMonomial (k : ℤ) :
    circleLpToAddCircleLinearIsometry (circleZMonomialLp circleLebesgue k) =
      (fourierLp 2 k : Lp ℂ 2 (@AddCircle.haarAddCircle (1 : ℝ) inferInstance)) := by
  change Lp.compMeasurePreserving addCircleCircleEquiv
      addCircleCircleMeasurePreserving
      ((circleZMonomial_memLp circleLebesgue k).toLp
        (fun z : Circle => (z : ℂ) ^ k)) = _
  rw [Lp.toLp_compMeasurePreserving]
  apply Lp.ext
  filter_upwards
    [((circleZMonomial_memLp circleLebesgue k).comp_measurePreserving
      addCircleCircleMeasurePreserving).coeFn_toLp,
      coeFn_fourierLp 2 k] with x hx hfourier
  rw [hx, hfourier]
  simp only [Function.comp_apply, addCircleCircleEquiv, fourier_apply]
  change (((AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero x : Circle) : ℂ) ^ k) =
    (((((k : ℤ) • x).toCircle : Circle)) : ℂ)
  rw [AddCircle.homeomorphCircle_apply, AddCircle.toCircle_zsmul]
  exact (Circle.coe_zpow x.toCircle k).symm

/-- The full integer Fourier coefficient sequence of a one-sided Riesz--Fischer reconstruction
is precisely the zero extension of its input. -/
theorem circleZMonomialLp_inner_circleRieszFischerOfNat
    (c : ℕ → ℂ) (hc : Memℓp c 2) (k : ℤ) :
    inner ℂ (circleZMonomialLp circleLebesgue k)
      (circleRieszFischerOfNat c hc) = nonnegativeIntExtension c k := by
  let a : lp (fun _ : ℤ => ℂ) 2 :=
    ⟨nonnegativeIntExtension c, nonnegativeIntExtension_memℓp_two c hc⟩
  let g : Lp ℂ 2 (@AddCircle.haarAddCircle (1 : ℝ) inferInstance) :=
    fourierBasis.repr.symm a
  let U := circleLpAddCircleLinearIsometryEquiv
  calc
    inner ℂ (circleZMonomialLp circleLebesgue k)
        (circleRieszFischerOfNat c hc) =
      inner ℂ (U (circleZMonomialLp circleLebesgue k))
        (U (circleRieszFischerOfNat c hc)) := (U.inner_map_map _ _).symm
    _ = inner ℂ (fourierLp 2 k) g := by
      rw [show U (circleZMonomialLp circleLebesgue k) = fourierLp 2 k by
        simpa [U, circleLpAddCircleLinearIsometryEquiv] using
          circleLpToAddCircleLinearIsometry_circleZMonomial k]
      congr 1
      simp [U, g, a, circleRieszFischerOfNat,
        circleLpAddCircleLinearIsometryEquiv]
    _ = a k := by
      rw [← show fourierBasis k = fourierLp 2 k by exact congrFun coe_fourierBasis k]
      rw [← HilbertBasis.repr_apply_apply]
      simp [g]
    _ = nonnegativeIntExtension c k := by simp [a]

end

end GaloisForLFunctions.HTGeometry
