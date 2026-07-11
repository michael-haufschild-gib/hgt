import Mathlib.MeasureTheory.Integral.Prod
import GaloisForLFunctions.RHTower.SlepianBandCommutation

/-!
# L² symmetry of the band transform

The entire sinc kernel is symmetric, `K̃_c(x,y) = K̃_c(y,x)` (the profile is even), so the band
transform is a symmetric bilinear kernel operator on the band:

`∫_{−1}^{1} (T̃f)(x)·g(x) dx = ∫_{−1}^{1} f(y)·(T̃g)(y) dy`  (`bandTransform_symmetric`),

by Fubini on the rectangle `[−1,1]²` — the jointly continuous integrand is integrable on the
compact square.  Together with the commuting theorem this completes the formal Slepian package
for the band transform: a symmetric kernel operator commuting with a symmetric Sturm–Liouville
operator, whose eigenlines it preserves with a scalar concentration eigenvalue.
-/

open Filter MeasureTheory

namespace RHTower

/-- The entire sinc profile is even. -/
theorem sincSmooth_even (c u : ℝ) : sincSmooth c (-u) = sincSmooth c u := by
  by_cases h : u = 0
  · subst h; norm_num
  · rw [sincSmooth_eq_off (neg_ne_zero.mpr h), sincSmooth_eq_off h]
    unfold sincScalar
    rw [show c * -u = -(c * u) by ring, Real.sin_neg,
      show Real.pi * -u = -(Real.pi * u) by ring, neg_div_neg_eq]

/-- The entire time–band kernel is symmetric. -/
theorem sincKernelSmooth_symm (c x y : ℝ) :
    sincKernelSmooth c x y = sincKernelSmooth c y x := by
  unfold sincKernelSmooth
  rw [show x - y = -(y - x) by ring, sincSmooth_even]

/-- **L² symmetry of the band transform**: the symmetric kernel makes the transform a
symmetric bilinear operator over the band. -/
theorem bandTransform_symmetric (c : ℝ) {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    ∫ x in (-1 : ℝ)..1, bandTransform c f x * g x
      = ∫ y in (-1 : ℝ)..1, f y * bandTransform c g y := by
  have hK : Continuous (fun p : ℝ × ℝ => sincSmooth c (p.1 - p.2)) :=
    (contDiff_sincSmooth c).continuous.comp (continuous_fst.sub continuous_snd)
  have hFcont : Continuous (Function.uncurry
      (fun x y => sincKernelSmooth c x y * f y * g x)) :=
    (hK.mul (hf.comp continuous_snd)).mul (hg.comp continuous_fst)
  have h_int : Integrable (Function.uncurry (fun x y => sincKernelSmooth c x y * f y * g x))
      ((volume.restrict (Set.uIoc (-1 : ℝ) 1)).prod
        (volume.restrict (Set.Ioc (-1 : ℝ) 1))) := by
    rw [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1), MeasureTheory.Measure.prod_restrict]
    refine MeasureTheory.IntegrableOn.mono_set
      (t := Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1) ?_
      (Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self)
    exact hFcont.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hswap := MeasureTheory.intervalIntegral_integral_swap
    (μ := volume.restrict (Set.Ioc (-1 : ℝ) 1))
    (f := fun x y => sincKernelSmooth c x y * f y * g x) h_int
  calc ∫ x in (-1 : ℝ)..1, bandTransform c f x * g x
      = ∫ x in (-1 : ℝ)..1, ∫ y in (-1 : ℝ)..1, sincKernelSmooth c x y * f y * g x := by
        refine intervalIntegral.integral_congr fun x _ => ?_
        rw [intervalIntegral.integral_mul_const]
        simp only [bandTransform]
    _ = ∫ x in (-1 : ℝ)..1, ∫ y, sincKernelSmooth c x y * f y * g x
          ∂(volume.restrict (Set.Ioc (-1 : ℝ) 1)) :=
        intervalIntegral.integral_congr fun x _ =>
          intervalIntegral.integral_of_le (by norm_num)
    _ = ∫ y, (∫ x in (-1 : ℝ)..1, sincKernelSmooth c x y * f y * g x)
          ∂(volume.restrict (Set.Ioc (-1 : ℝ) 1)) := hswap
    _ = ∫ y in (-1 : ℝ)..1, ∫ x in (-1 : ℝ)..1, sincKernelSmooth c x y * f y * g x :=
        (intervalIntegral.integral_of_le (by norm_num)).symm
    _ = ∫ y in (-1 : ℝ)..1, f y * bandTransform c g y := by
        refine intervalIntegral.integral_congr fun y _ => ?_
        rw [intervalIntegral.integral_congr (g := fun x => f y * (sincKernelSmooth c y x * g x))
          fun x _ => by rw [sincKernelSmooth_symm c x y]; ring,
          intervalIntegral.integral_const_mul]
        simp only [bandTransform]

end RHTower
