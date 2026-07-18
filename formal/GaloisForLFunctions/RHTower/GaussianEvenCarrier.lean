import GaloisForLFunctions.RHTower.ConstrainedProlateOperator
import GaloisForLFunctions.HTGeometry.GaussianSchwartz
import GaloisForLFunctions.HTGeometry.TruncatedFixedVector

/-!
# The Gaussian inside the even prolate carrier

The prolate trial functions live in the project's even `L²` carrier, cut down to the aperture.
This module places the Gaussian there: its `L²` class is even, hence a member of
`evenSubspace`, and the even Fourier transform fixes it, because that transform is the
restriction of the `L²` Fourier transform which fixes the Gaussian.

The Gaussian is even pointwise since it depends on `x` only through `x²`, and evenness of an
`L²` class is evenness of any representative almost everywhere; the Schwartz representative is
continuous, so its own evenness transports.
-/

open MeasureTheory
open scoped Real

noncomputable section

namespace RHTower

/-- The `L²` class of the Gaussian. -/
def gaussL2 : SoninL2 := GaloisForLFunctions.gaussianSchwartz.toLp 2

theorem gaussL2_coeFn :
    (gaussL2 : ℝ → ℂ) =ᵐ[volume] fun x => (GaloisForLFunctions.gaussReal x : ℂ) := by
  have h := SchwartzMap.coeFn_toLp GaloisForLFunctions.gaussianSchwartz 2 (μ := volume)
  refine h.trans ?_
  filter_upwards with x
  exact GaloisForLFunctions.gaussianSchwartz_apply x

/-- The Gaussian is even. -/
theorem gaussReal_neg (x : ℝ) : GaloisForLFunctions.gaussReal (-x)
    = GaloisForLFunctions.gaussReal x := by
  unfold GaloisForLFunctions.gaussReal
  congr 1
  ring

/-- **The Gaussian lies in the even carrier.** -/
theorem gaussL2_mem_evenSubspace : gaussL2 ∈ evenSubspace := by
  rw [mem_evenSubspace_iff]
  apply Lp.ext
  have hneg := gaussL2_coeFn.comp_tendsto
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.tendsto_ae
  filter_upwards [l2Reflection_ae gaussL2, hneg, gaussL2_coeFn] with x href hleft hright
  have hleft' : (gaussL2 : ℝ → ℂ) (-x) = (GaloisForLFunctions.gaussReal (-x) : ℂ) := by
    simpa [Function.comp_apply] using hleft
  rw [href, hleft', hright, gaussReal_neg]

/-- The Gaussian as an element of the even carrier. -/
def gaussEven : evenSubspace := ⟨gaussL2, gaussL2_mem_evenSubspace⟩

@[simp] theorem coe_gaussEven : (gaussEven : SoninL2) = gaussL2 := rfl

/-- **The even Fourier transform fixes the Gaussian.**  The even transform is the restriction of
the `L²` Fourier transform, which fixes the Gaussian's class. -/
theorem evenFourierTransform_gaussEven : evenFourierTransform gaussEven = gaussEven := by
  apply Subtype.ext
  rw [coe_evenFourierTransform_apply, coe_gaussEven]
  exact GaloisForLFunctions.fourier_gaussianSchwartz_toLp

/-- The Gaussian is nonzero in `L²`: its value at the origin is one, and it is continuous. -/
theorem gaussEven_ne_zero : gaussEven ≠ 0 := by
  intro hzero
  have hcoe : gaussL2 = 0 := by
    have := congrArg (fun v : evenSubspace => (v : SoninL2)) hzero
    simpa using this
  have hae : (fun x : ℝ => (GaloisForLFunctions.gaussReal x : ℂ)) =ᵐ[volume] 0 := by
    refine gaussL2_coeFn.symm.trans ?_
    rw [hcoe]
    exact Lp.coeFn_zero _ _ _
  have hpos : ∀ x : ℝ, (GaloisForLFunctions.gaussReal x : ℂ) ≠ 0 := by
    intro x
    simpa using (GaloisForLFunctions.gaussReal_pos x).ne'
  have hvol : (volume : Measure ℝ) = 0 := by
    simpa using hae.mono fun x hx => hpos x hx
  have hIcc : (volume : Measure ℝ) (Set.Icc (0 : ℝ) 1) = 0 := by rw [hvol]; rfl
  rw [Real.volume_Icc] at hIcc
  norm_num at hIcc

/-! ## The aperture cutoff as a star projection on the even carrier -/

/-- The even aperture cutoff is symmetric: it inherits symmetry from the underlying
multiplication by an indicator. -/
theorem evenIndicatorCutoff_symmetric (a : ℝ) (f g : evenSubspace) :
    inner ℂ (evenIndicatorCutoff a f) g = inner ℂ f (evenIndicatorCutoff a g) := by
  have h := indicatorCutoff_symmetric (centralInterval a) (measurableSet_centralInterval a)
    (f : SoninL2) (g : SoninL2)
  rw [Submodule.coe_inner, Submodule.coe_inner, coe_evenIndicatorCutoff_apply,
    coe_evenIndicatorCutoff_apply]
  exact h

theorem evenIndicatorCutoff_apply_apply (a : ℝ) (f : evenSubspace) :
    evenIndicatorCutoff a (evenIndicatorCutoff a f) = evenIndicatorCutoff a f := by
  have h := evenIndicatorCutoff_idempotent a
  rw [IsIdempotentElem] at h
  calc evenIndicatorCutoff a (evenIndicatorCutoff a f)
      = (evenIndicatorCutoff a * evenIndicatorCutoff a) f := rfl
    _ = evenIndicatorCutoff a f := by rw [h]

/-- **The Gaussian trial estimate at the aperture.**  The truncated Gaussian retains at least
`1 − 4θ²` of its squared norm under the compressed Fourier block, where `θ` bounds the relative
truncation error.  This is `evenProlateLeakageValue_le_of_form_trial`'s hypothesis for the
one-dimensional trial space spanned by the truncated Gaussian. -/
theorem gaussEven_concentration (a : ℝ) {θ : ℝ}
    (hθ : ‖gaussEven - evenIndicatorCutoff a gaussEven‖
      ≤ θ * ‖evenIndicatorCutoff a gaussEven‖) :
    (1 - 4 * θ ^ 2) * ‖evenIndicatorCutoff a gaussEven‖ ^ 2
      ≤ ‖evenIndicatorCutoff a (evenFourierTransform (evenIndicatorCutoff a gaussEven))‖ ^ 2 :=
  ContinuousLinearMap.norm_sq_proj_unitary_proj_ge_of_rel
    (fun x => evenFourierTransform_isometry x)
    (evenIndicatorCutoff_apply_apply a)
    (evenIndicatorCutoff_symmetric a)
    evenFourierTransform_gaussEven hθ

/-- The compressed Fourier block applied to the truncated Gaussian is the doubly-cut
transform, by idempotency of the cutoff. -/
theorem evenTimeBandFourier_gaussEven_cut (a : ℝ) :
    evenTimeBandFourier a (evenIndicatorCutoff a gaussEven)
      = evenIndicatorCutoff a (evenFourierTransform (evenIndicatorCutoff a gaussEven)) := by
  rw [evenTimeBandFourier_eq_mul]
  change evenIndicatorCutoff a (evenFourierTransform
    (evenIndicatorCutoff a (evenIndicatorCutoff a gaussEven))) = _
  rw [evenIndicatorCutoff_apply_apply]

/-- **The truncated Gaussian is a concentrated trial vector for the compressed Fourier block.**
Relative truncation error `θ` gives concentration deficit `4θ²` — the exact hypothesis shape of
`evenProlateLeakageValue_le_of_form_trial`. -/
theorem gaussEven_timeBand_concentration (a : ℝ) {θ : ℝ}
    (hθ : ‖gaussEven - evenIndicatorCutoff a gaussEven‖
      ≤ θ * ‖evenIndicatorCutoff a gaussEven‖) :
    (1 - 4 * θ ^ 2) * ‖evenIndicatorCutoff a gaussEven‖ ^ 2
      ≤ ‖evenTimeBandFourier a (evenIndicatorCutoff a gaussEven)‖ ^ 2 := by
  rw [evenTimeBandFourier_gaussEven_cut]
  exact gaussEven_concentration a hθ

/-- The concentration estimate is homogeneous, so it holds on the whole line spanned by the
truncated Gaussian — the one-dimensional trial space. -/
theorem gaussEven_span_concentration (a : ℝ) {θ : ℝ}
    (hθ : ‖gaussEven - evenIndicatorCutoff a gaussEven‖
      ≤ θ * ‖evenIndicatorCutoff a gaussEven‖)
    (f : evenSubspace)
    (hf : f ∈ Submodule.span ℂ {evenIndicatorCutoff a gaussEven}) :
    (1 - 4 * θ ^ 2) * ‖f‖ ^ 2 ≤ ‖evenTimeBandFourier a f‖ ^ 2 := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hf
  have hbase := gaussEven_timeBand_concentration a hθ
  rw [← hc, map_smul, norm_smul, norm_smul]
  have hcn : (0 : ℝ) ≤ ‖c‖ ^ 2 := sq_nonneg _
  calc (1 - 4 * θ ^ 2) * (‖c‖ * ‖evenIndicatorCutoff a gaussEven‖) ^ 2
      = ‖c‖ ^ 2 * ((1 - 4 * θ ^ 2) * ‖evenIndicatorCutoff a gaussEven‖ ^ 2) := by ring
    _ ≤ ‖c‖ ^ 2 * ‖evenTimeBandFourier a (evenIndicatorCutoff a gaussEven)‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hbase hcn
    _ = (‖c‖ * ‖evenTimeBandFourier a (evenIndicatorCutoff a gaussEven)‖) ^ 2 := by ring

end RHTower
