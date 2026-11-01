import GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.MollifiedCorridorAndThetaReading
import GaloisForLFunctions.RHTower.CosDilationKernelBlindnessLink
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# One-Sided Half-Plane Mollified Green-Jensen Source Reading (`Re z ≥ 1/2`)

This module formulates and proves the one-sided (`Re z ≥ 1/2`) Poincaré–Lelong / Green-Jensen
source reading for mollified completed and finite-theta amplitudes, bypassing the vertical Euler
zeros on `Re z = 0` (`eulerFactor_verticalZeros_depthKernel_ge`) via `lineReflect` symmetry and
eliminating discrete zero-counting shells:

1. **Superharmonic critical-line-only no-go**
   (`superharmonic_rect_verticalMean_le_linear`, `no_superharmonic_weight_dominates_depthKernel`):
   Any `C²` superharmonic weight `Φ` (`ΔΦ ≤ 0`) on `[1/2, σ_R] × [T₁, T₂]` vanishing on the critical
   line `Re z = 1/2` with vanishing vertical normal derivative on `{y = T₁, T₂}` obeys the linear
   vertical-mean ceiling `∫_{T₁}^{T₂} Φ(x + iy) dy ≤ (x - 1/2) ∫_{T₁}^{T₂} ∂_x Φ(1/2 + iy) dy`,
   and therefore cannot dominate `depthKernel L (x - 1/2)` (`L > 0`).

2. **Exact Taylor–Green kernel representation and continuous hyperbolic layer-cake**
   (`depthKernel_eq_abscissa_integral`, `depthKernel_eq_unitStrip_hinge_integral`,
    `sum_depthKernel_eq_sinh_tail_integral`, `sum_depthKernel_band_le_sinh_tail_integral`):
   For all `x ≥ 1/2`,
   `depthKernel L (x - 1/2) = ∫ σ in (1/2)..x, 8 * L^2 * cosh(2L(σ - 1/2)) * (x - σ)`,
   with nonnegative right-half mollifier credit `mollifierRightCredit L x` vanishing identically on
   all left/vertical zeros `x ≤ 1/2`, and continuous hyperbolic layer-cake representation
   `∑_{w ∈ S} m(w) depthKernel L (Re w - 1/2) = ∫_0^{1/2} 4L sinh(2Lu) (∑_{Re w ≥ 1/2 + u} m(w)) du`.

3. **Second-order critical-line jet-vanishing Green identity, mollified finite-theta positive
   curvature, and Archimedean harmonic annihilation**
   (`halfPlane_green_identity_of_vanishing_jet`, `halfPlane_green_identity_halfPlaneDepthWeight`,
    `laplacian_mollifiedFiniteThetaPotential`, `halfPlane_archXi_log_norm_annihilated`):
   Because `depthKernel L (x - 1/2)` vanishes to second order at `x = 1/2`, the half-plane weight
   `ψ(z) = χ(z) depthKernel L (Re z - 1/2)` has vanishing value and normal derivative on `Re z = 1/2`
   without requiring `χ` to vanish on `Re z = 1/2`. Regularized mollified potentials of both `ξ` and
   `finiteThetaAmplitude K` have pointwise nonnegative curvature, while `log ‖archXi z‖` is harmonic
   and identically annihilated by `Δψ` on `Re z ≥ 1/2, Im z > 0`.

4. **Continuous abscissa-integrated mollified source ceiling and shell-free collapse (`0 < c < 1/4`)**
   (`exists_wide_zetaOffLine_hinge_add_mollifierCredit_le`,
    `exists_shellDepthSum_add_mollifierCredit_le_abscissa_source_integral`,
    `exists_twoLength_mollified_meanSquare_arbitrary_exponents`,
    `exists_pure_abscissa_mollified_shellDepthSum_le_log_quarter`):
   Integrating the wide mollifier-credited Littlewood hinge inequality over `σ ∈ [1/2, 1]` against
   `8L^2 cosh(2L(σ - 1/2)) dσ` bounds `π · shellDepthSum T₁ T₂ L` plus nonnegative right-half
   mollifier zero credit purely by an abscissa integral of continuous mollified line mean squares.
   For all `0 < c < 1/4`, a single two-length Barban–Vehov mollifier bounds this continuous source
   integral directly by `O_c(V log V)` across `[1/2, 1]` without discrete shells or zero-density inputs.
-/

set_option autoImplicit false

open Complex Filter Topology Set MeasureTheory intervalIntegral Laplacian InnerProductSpace
open scoped BigOperators Real ComplexConjugate ContDiff ENNReal Laplacian Interval
open _root_.RHTower _root_.RHTower.ExactNullDivisorTransfer _root_.Zeta23

noncomputable section

namespace GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect

open GaloisForLFunctions.ConjugateDiagonalGeometry

/-! ## §1. Directional calculus on half-plane rectangles and superharmonic linear ceiling -/

private theorem cont_horiz_pt (y : ℝ) : Continuous (fun s : ℝ => (s : ℂ) + (y : ℂ) * I) := by
  fun_prop

private theorem cont_vert_pt (x : ℝ) : Continuous (fun y : ℝ => (x : ℂ) + (y : ℂ) * I) := by
  fun_prop

private theorem intervalIntegral_swap_of_continuousOn {F : ℝ → ℝ → ℝ} {a b c d : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d)
    (hF : ContinuousOn (Function.uncurry F) (Icc a b ×ˢ Icc c d)) :
    (∫ x in a..b, ∫ y in c..d, F x y) = ∫ y in c..d, ∫ x in a..b, F x y := by
  simp only [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hcd]
  refine MeasureTheory.integral_integral_swap ?_
  rw [Measure.prod_restrict]
  exact (hF.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
    (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)

private theorem continuousOn_parametric_intervalIntegral_of_continuousOn {F : ℝ → ℝ → ℝ}
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hF : ContinuousOn (Function.uncurry F) (Icc a b ×ˢ Icc c d)) :
    ContinuousOn (fun x => ∫ y in c..d, F x y) (Icc a b) := by
  let G : ℝ → ℝ → ℝ := fun x y => F (max a (min b x)) (max c (min d y))
  have hG_cont : Continuous (Function.uncurry G) := by
    have hclamp : Continuous (fun p : ℝ × ℝ => (max a (min b p.1), max c (min d p.2))) := by
      fun_prop
    exact hF.comp_continuous hclamp fun p =>
      ⟨⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩,
       ⟨le_max_left _ _, max_le hcd (min_le_left _ _)⟩⟩
  refine (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume)
    hG_cont c d).continuousOn.congr fun x hx => ?_
  refine intervalIntegral.integral_congr fun y hy => ?_
  rw [uIcc_of_le hcd] at hy
  dsimp only [G]
  rw [min_eq_right hx.2, max_eq_right hx.1, min_eq_right hy.2, max_eq_right hy.1]

private theorem hasDerivAt_horiz_pt (y x : ℝ) :
    HasDerivAt (fun s : ℝ => (s : ℂ) + (y : ℂ) * I) 1 x := by
  simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).add_const ((y : ℂ) * I)

private theorem hasDerivAt_vert_pt (x y : ℝ) :
    HasDerivAt (fun t : ℝ => (x : ℂ) + (t : ℂ) * I) I y := by
  have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * I) ((1 : ℂ) * I) y :=
    (Complex.ofRealCLM.hasDerivAt (x := y)).mul_const I
  rw [one_mul] at h1
  simpa using h1.const_add (x : ℂ)

private theorem hasDerivAt_horiz_real {f : ℂ → ℝ} {x y : ℝ}
    (hf : DifferentiableAt ℝ f ((x : ℂ) + (y : ℂ) * I)) :
    HasDerivAt (fun s : ℝ => f ((s : ℂ) + (y : ℂ) * I))
      (fderiv ℝ f ((x : ℂ) + (y : ℂ) * I) 1) x :=
  hf.hasFDerivAt.comp_hasDerivAt x (hasDerivAt_horiz_pt y x)

private theorem hasDerivAt_vert_real {f : ℂ → ℝ} {x y : ℝ}
    (hf : DifferentiableAt ℝ f ((x : ℂ) + (y : ℂ) * I)) :
    HasDerivAt (fun t : ℝ => f ((x : ℂ) + (t : ℂ) * I))
      (fderiv ℝ f ((x : ℂ) + (y : ℂ) * I) I) y :=
  hf.hasFDerivAt.comp_hasDerivAt y (hasDerivAt_vert_pt x y)

private theorem contDiffAt_fderiv_apply {f : ℂ → ℝ} {z : ℂ} (hf : ContDiffAt ℝ 2 f z) (v : ℂ) :
    ContDiffAt ℝ 1 (fun w => fderiv ℝ f w v) z :=
  ((ContinuousLinearMap.apply ℝ ℝ v).contDiff.contDiffAt).comp z
    (hf.fderiv_right (m := 1) (by norm_num))

private theorem continuousAt_dderiv_of_contDiffAt {f : ℂ → ℝ} {z : ℂ}
    (hf : ContDiffAt ℝ 2 f z) (v : ℂ) :
    ContinuousAt (Bottcher.dderiv f v) z := by
  have h1 : ContDiffAt ℝ 1 (fun w => fderiv ℝ f w v) z := contDiffAt_fderiv_apply hf v
  have h0 : ContDiffAt ℝ 0 (fderiv ℝ (fun w => fderiv ℝ f w v)) z :=
    h1.fderiv_right (m := 0) (by norm_num)
  exact ((ContinuousLinearMap.apply ℝ ℝ v).continuous.continuousAt).comp h0.continuousAt

private theorem laplacian_eq_dderiv_at {f : ℂ → ℝ} {z : ℂ} (hf : ContDiffAt ℝ 2 f z) :
    Δ f z = Bottcher.dderiv f 1 z + Bottcher.dderiv f I z := by
  have key : ∀ u : ℂ, iteratedFDeriv ℝ 2 f z ![u, u] = Bottcher.dderiv f u z := by
    intro u
    rw [iteratedFDeriv_two_apply]
    show (fderiv ℝ (fderiv ℝ f) z u) u = fderiv ℝ (fun y => fderiv ℝ f y u) z u
    have hdiff : DifferentiableAt ℝ (fderiv ℝ f) z :=
      (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    have hcomp : fderiv ℝ (fun y => (fderiv ℝ f y) u) z =
        (ContinuousLinearMap.apply ℝ ℝ u).comp (fderiv ℝ (fderiv ℝ f) z) := by
      rw [show (fun y => (fderiv ℝ f y) u) = (ContinuousLinearMap.apply ℝ ℝ u) ∘ (fderiv ℝ f) from rfl]
      rw [fderiv_comp z (ContinuousLinearMap.apply ℝ ℝ u).differentiableAt hdiff,
        ContinuousLinearMap.fderiv]
    rw [hcomp]; rfl
  have hb := congrFun (laplacian_eq_iteratedFDeriv_orthonormalBasis f Complex.orthonormalBasisOneI) z
  have h0 : Complex.orthonormalBasisOneI 0 = (1 : ℂ) := by simp [Complex.coe_orthonormalBasisOneI]
  have h1 : Complex.orthonormalBasisOneI 1 = I := by simp [Complex.coe_orthonormalBasisOneI]
  rw [hb, Fin.sum_univ_two, h0, h1, key 1, key I]

/-- **Superharmonic critical-line-only linear ceiling:** any `C²` function `Φ : ℂ → ℝ` on
`[1/2, σ_R] × [T₁, T₂]` with `Φ(1/2 + iy) = 0`, vanishing vertical normal derivatives at `T₁, T₂`,
and `ΔΦ ≤ 0` obeys `∫_{T₁}^{T₂} Φ(x + iy) dy ≤ (x - 1/2) ∫_{T₁}^{T₂} ∂_x Φ(1/2 + iy) dy`. -/
theorem superharmonic_rect_verticalMean_le_linear {Φ : ℂ → ℝ} {σ_R T₁ T₂ : ℝ}
    (hΦ : ContDiff ℝ 2 Φ) (_hσ : 1 / 2 ≤ σ_R) (hT : T₁ ≤ T₂)
    (hcrit : ∀ y ∈ Icc T₁ T₂, Φ (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I) = 0)
    (hbot : ∀ x ∈ Icc (1 / 2) σ_R, fderiv ℝ Φ ((x : ℂ) + (T₁ : ℂ) * I) I = 0)
    (htop : ∀ x ∈ Icc (1 / 2) σ_R, fderiv ℝ Φ ((x : ℂ) + (T₂ : ℂ) * I) I = 0)
    (hsuper : ∀ x ∈ Icc (1 / 2) σ_R, ∀ y ∈ Icc T₁ T₂, Δ Φ ((x : ℂ) + (y : ℂ) * I) ≤ 0)
    {x : ℝ} (hx : x ∈ Icc (1 / 2) σ_R) :
    (∫ y in T₁..T₂, Φ ((x : ℂ) + (y : ℂ) * I)) ≤
      (x - 1 / 2) * ∫ y in T₁..T₂, fderiv ℝ Φ (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I) 1 := by
  have hpair_cont : Continuous (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * I) := by fun_prop
  have hD1_cont : Continuous (fun z : ℂ => fderiv ℝ Φ z 1) :=
    ((hΦ.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).continuous
  have hdd1_cont : Continuous (Bottcher.dderiv Φ 1) := by
    rw [continuous_iff_continuousAt]
    exact fun z => continuousAt_dderiv_of_contDiffAt hΦ.contDiffAt 1
  have hddI_cont : Continuous (Bottcher.dderiv Φ I) := by
    rw [continuous_iff_continuousAt]
    exact fun z => continuousAt_dderiv_of_contDiffAt hΦ.contDiffAt I
  set B₀ : ℝ := ∫ y in T₁..T₂, fderiv ℝ Φ (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I) 1
  have hslope_le : ∀ t ∈ Icc (1 / 2) x,
      (∫ y in T₁..T₂, fderiv ℝ Φ ((t : ℂ) + (y : ℂ) * I) 1) ≤ B₀ := by
    intro t ht
    have hftc_s : ∀ y ∈ Icc T₁ T₂,
        fderiv ℝ Φ ((t : ℂ) + (y : ℂ) * I) 1 -
          fderiv ℝ Φ (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I) 1 =
          ∫ s in (1 / 2)..t, Bottcher.dderiv Φ 1 ((s : ℂ) + (y : ℂ) * I) := by
      intro y _
      exact (integral_eq_sub_of_hasDerivAt
        (f := fun s : ℝ => fderiv ℝ Φ ((s : ℂ) + (y : ℂ) * I) 1)
        (f' := fun s : ℝ => Bottcher.dderiv Φ 1 ((s : ℂ) + (y : ℂ) * I))
        (fun s _ => hasDerivAt_horiz_real
          ((contDiffAt_fderiv_apply hΦ.contDiffAt 1).differentiableAt one_ne_zero))
        ((show Continuous fun s : ℝ => Bottcher.dderiv Φ 1 ((s : ℂ) + (y : ℂ) * I) from
          hdd1_cont.comp (cont_horiz_pt y)).intervalIntegrable _ _)).symm
    have hint_diff : (∫ y in T₁..T₂, (fderiv ℝ Φ ((t : ℂ) + (y : ℂ) * I) 1 -
        fderiv ℝ Φ (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I) 1)) =
        ∫ s in (1 / 2)..t, ∫ y in T₁..T₂, Bottcher.dderiv Φ 1 ((s : ℂ) + (y : ℂ) * I) := by
      have hcongr : (∫ y in T₁..T₂, (fderiv ℝ Φ ((t : ℂ) + (y : ℂ) * I) 1 -
          fderiv ℝ Φ (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I) 1)) =
          ∫ y in T₁..T₂, ∫ s in (1 / 2)..t, Bottcher.dderiv Φ 1 ((s : ℂ) + (y : ℂ) * I) := by
        refine integral_congr fun y hy => ?_
        rw [uIcc_of_le hT] at hy
        exact hftc_s y hy
      rw [hcongr]
      exact intervalIntegral_swap_of_continuousOn
        (F := fun y s => Bottcher.dderiv Φ 1 ((s : ℂ) + (y : ℂ) * I)) hT ht.1
        ((hdd1_cont.comp (hpair_cont.comp continuous_swap)).continuousOn)
    have hs_nonpos : ∀ s ∈ Icc (1 / 2) t,
        (∫ y in T₁..T₂, Bottcher.dderiv Φ 1 ((s : ℂ) + (y : ℂ) * I)) ≤ 0 := by
      intro s hs
      have hs_mem : s ∈ Icc (1 / 2) σ_R := ⟨hs.1, hs.2.trans (ht.2.trans hx.2)⟩
      have hddI_zero : (∫ y in T₁..T₂, Bottcher.dderiv Φ I ((s : ℂ) + (y : ℂ) * I)) = 0 := by
        have hftc_y := integral_eq_sub_of_hasDerivAt (a := T₁) (b := T₂)
          (f := fun y : ℝ => fderiv ℝ Φ ((s : ℂ) + (y : ℂ) * I) I)
          (f' := fun y : ℝ => Bottcher.dderiv Φ I ((s : ℂ) + (y : ℂ) * I))
          (fun y _ => hasDerivAt_vert_real
            ((contDiffAt_fderiv_apply hΦ.contDiffAt I).differentiableAt one_ne_zero))
          ((show Continuous fun y : ℝ => Bottcher.dderiv Φ I ((s : ℂ) + (y : ℂ) * I) from
            hddI_cont.comp (cont_vert_pt s)).intervalIntegrable T₁ T₂)
        rw [hftc_y, htop s hs_mem, hbot s hs_mem, sub_zero]
      have hlap_eq : (∫ y in T₁..T₂, Δ Φ ((s : ℂ) + (y : ℂ) * I)) =
          ∫ y in T₁..T₂, Bottcher.dderiv Φ 1 ((s : ℂ) + (y : ℂ) * I) := by
        have hpt : ∀ y : ℝ, Δ Φ ((s : ℂ) + (y : ℂ) * I) =
            Bottcher.dderiv Φ 1 ((s : ℂ) + (y : ℂ) * I) +
              Bottcher.dderiv Φ I ((s : ℂ) + (y : ℂ) * I) :=
          fun y => laplacian_eq_dderiv_at hΦ.contDiffAt
        have hc1 : Continuous (fun y : ℝ => Bottcher.dderiv Φ 1 ((s : ℂ) + (y : ℂ) * I)) :=
          hdd1_cont.comp (cont_vert_pt s)
        have hcI : Continuous (fun y : ℝ => Bottcher.dderiv Φ I ((s : ℂ) + (y : ℂ) * I)) :=
          hddI_cont.comp (cont_vert_pt s)
        simp_rw [hpt]
        rw [intervalIntegral.integral_add (hc1.intervalIntegrable _ _)
          (hcI.intervalIntegrable _ _), hddI_zero, add_zero]
      rw [← hlap_eq]
      have hlap_cont : Continuous (fun y : ℝ => Δ Φ ((s : ℂ) + (y : ℂ) * I)) := by
        have hpt : (fun y : ℝ => Δ Φ ((s : ℂ) + (y : ℂ) * I)) =
            fun y : ℝ => Bottcher.dderiv Φ 1 ((s : ℂ) + (y : ℂ) * I) +
              Bottcher.dderiv Φ I ((s : ℂ) + (y : ℂ) * I) :=
          funext fun y => laplacian_eq_dderiv_at hΦ.contDiffAt
        rw [hpt]
        exact (hdd1_cont.comp (cont_vert_pt s)).add (hddI_cont.comp (cont_vert_pt s))
      simpa using integral_mono_on (μ := volume) hT (hlap_cont.intervalIntegrable _ _)
        intervalIntegrable_const (fun y hy => hsuper s hs_mem y hy)
    have hrhs_nonpos :
        (∫ s in (1 / 2)..t, ∫ y in T₁..T₂, Bottcher.dderiv Φ 1 ((s : ℂ) + (y : ℂ) * I)) ≤ 0 := by
      have hcont_inner : Continuous (fun s : ℝ =>
          ∫ y in T₁..T₂, Bottcher.dderiv Φ 1 ((s : ℂ) + (y : ℂ) * I)) :=
        intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume)
          (f := fun (s : ℝ) (y : ℝ) => Bottcher.dderiv Φ 1 ((s : ℂ) + (y : ℂ) * I))
          (show Continuous (Function.uncurry fun s y : ℝ =>
            Bottcher.dderiv Φ 1 ((s : ℂ) + (y : ℂ) * I)) from hdd1_cont.comp hpair_cont) T₁ T₂
      simpa using integral_mono_on (μ := volume) ht.1 (hcont_inner.intervalIntegrable _ _)
        intervalIntegrable_const hs_nonpos
    have hcD_t : Continuous (fun y : ℝ => fderiv ℝ Φ ((t : ℂ) + (y : ℂ) * I) 1) :=
      hD1_cont.comp (cont_vert_pt t)
    have hcD_h : Continuous (fun y : ℝ => fderiv ℝ Φ (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I) 1) :=
      hD1_cont.comp (cont_vert_pt (1 / 2))
    have hsub_int := intervalIntegral.integral_sub
      (hcD_t.intervalIntegrable (μ := volume) T₁ T₂)
      (hcD_h.intervalIntegrable (μ := volume) T₁ T₂)
    linarith [hsub_int, hint_diff, hrhs_nonpos]
  have hftc_x : ∀ y ∈ Icc T₁ T₂,
      Φ ((x : ℂ) + (y : ℂ) * I) =
        ∫ t in (1 / 2)..x, fderiv ℝ Φ ((t : ℂ) + (y : ℂ) * I) 1 := by
    intro y hy
    have h := integral_eq_sub_of_hasDerivAt
      (f := fun t : ℝ => Φ ((t : ℂ) + (y : ℂ) * I))
      (f' := fun t : ℝ => fderiv ℝ Φ ((t : ℂ) + (y : ℂ) * I) 1)
      (fun t _ => hasDerivAt_horiz_real (hΦ.differentiable (by norm_num) _))
      ((show Continuous fun t : ℝ => fderiv ℝ Φ ((t : ℂ) + (y : ℂ) * I) 1 from
        hD1_cont.comp (cont_horiz_pt y)).intervalIntegrable (1 / 2) x)
    rw [hcrit y hy, sub_zero] at h
    exact h.symm
  have hswap : (∫ y in T₁..T₂, Φ ((x : ℂ) + (y : ℂ) * I)) =
      ∫ t in (1 / 2)..x, ∫ y in T₁..T₂, fderiv ℝ Φ ((t : ℂ) + (y : ℂ) * I) 1 := by
    have hcongr : (∫ y in T₁..T₂, Φ ((x : ℂ) + (y : ℂ) * I)) =
        ∫ y in T₁..T₂, ∫ t in (1 / 2)..x, fderiv ℝ Φ ((t : ℂ) + (y : ℂ) * I) 1 := by
      refine integral_congr fun y hy => ?_
      rw [uIcc_of_le hT] at hy
      exact hftc_x y hy
    rw [hcongr]
    exact intervalIntegral_swap_of_continuousOn
      (F := fun y t => fderiv ℝ Φ ((t : ℂ) + (y : ℂ) * I) 1) hT hx.1
      ((hD1_cont.comp (hpair_cont.comp continuous_swap)).continuousOn)
  rw [hswap]
  have hcont_t : Continuous (fun t : ℝ =>
      ∫ y in T₁..T₂, fderiv ℝ Φ ((t : ℂ) + (y : ℂ) * I) 1) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume)
      (f := fun (t : ℝ) (y : ℝ) => fderiv ℝ Φ ((t : ℂ) + (y : ℂ) * I) 1)
      (show Continuous (Function.uncurry fun t y : ℝ =>
        fderiv ℝ Φ ((t : ℂ) + (y : ℂ) * I) 1) from hD1_cont.comp hpair_cont) T₁ T₂
  calc (∫ t in (1 / 2)..x, ∫ y in T₁..T₂, fderiv ℝ Φ ((t : ℂ) + (y : ℂ) * I) 1)
      ≤ ∫ _t in (1 / 2)..x, B₀ :=
        integral_mono_on (μ := volume) hx.1 (hcont_t.intervalIntegrable _ _)
          intervalIntegrable_const hslope_le
    _ = (x - 1 / 2) * B₀ := by rw [intervalIntegral.integral_const, smul_eq_mul]

/-- **No-go for critical-line-only superharmonic weights:** for `L > 0` and `T₁ < T₂`, no `C²`
superharmonic (`ΔΦ ≤ 0`) weight on `Re z ≥ 1/2, Im z ∈ [T₁, T₂]` with `Φ(1/2 + iy) = 0` and
`∂_y Φ(x + iT₁) = ∂_y Φ(x + iT₂) = 0` can majorize `depthKernel L (Re z - 1/2)` across `Re z ≥ 1/2`. -/
theorem no_superharmonic_weight_dominates_depthKernel {Φ : ℂ → ℝ} {L T₁ T₂ : ℝ}
    (hL : 0 < L) (hT : T₁ < T₂) (hΦ : ContDiff ℝ 2 Φ)
    (hcrit : ∀ y ∈ Icc T₁ T₂, Φ (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I) = 0)
    (hbot : ∀ x : ℝ, 1 / 2 ≤ x → fderiv ℝ Φ ((x : ℂ) + (T₁ : ℂ) * I) I = 0)
    (htop : ∀ x : ℝ, 1 / 2 ≤ x → fderiv ℝ Φ ((x : ℂ) + (T₂ : ℂ) * I) I = 0)
    (hsuper : ∀ x : ℝ, 1 / 2 ≤ x → ∀ y ∈ Icc T₁ T₂, Δ Φ ((x : ℂ) + (y : ℂ) * I) ≤ 0) :
    ¬ (∀ x : ℝ, 1 / 2 ≤ x → ∀ y ∈ Icc T₁ T₂,
        depthKernel L (x - 1 / 2) ≤ Φ ((x : ℂ) + (y : ℂ) * I)) := by
  intro hdom
  set B₀ : ℝ := ∫ y in T₁..T₂, fderiv ℝ Φ (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I) 1
  have hT_pos : 0 < T₂ - T₁ := sub_pos.mpr hT
  set u : ℝ := max 1 ((|B₀| / (T₂ - T₁) + 4) / (2 * L ^ 2))
  have hu1 : 1 ≤ u := le_max_left _ _
  have hu_pos : 0 < u := lt_of_lt_of_le zero_lt_one hu1
  have hu_hi : (|B₀| / (T₂ - T₁) + 4) / (2 * L ^ 2) ≤ u := le_max_right _ _
  set x : ℝ := 1 / 2 + u
  have hx_ge : 1 / 2 ≤ x := by dsimp [x]; linarith
  have hlin := superharmonic_rect_verticalMean_le_linear hΦ hx_ge hT.le hcrit
    (fun s hs => hbot s hs.1) (fun s hs => htop s hs.1) (fun s hs y hy => hsuper s hs.1 y hy)
    ⟨hx_ge, le_rfl⟩
  have hlo_int : (T₂ - T₁) * depthKernel L u ≤ ∫ y in T₁..T₂, Φ ((x : ℂ) + (y : ℂ) * I) := by
    have hpt : ∀ y ∈ Icc T₁ T₂, depthKernel L u ≤ Φ ((x : ℂ) + (y : ℂ) * I) := by
      intro y hy
      simpa [x] using hdom x hx_ge y hy
    have hcont : Continuous (fun y : ℝ => Φ ((x : ℂ) + (y : ℂ) * I)) :=
      hΦ.continuous.comp (cont_vert_pt x)
    have hmono := integral_mono_on (μ := volume) hT.le intervalIntegrable_const
      (hcont.intervalIntegrable T₁ T₂) hpt
    simpa [intervalIntegral.integral_const, smul_eq_mul] using hmono
  have hquad : 2 * L ^ 2 * u ^ 2 - 2 < depthKernel L u := by
    have h1 := Real.pow_div_factorial_le_exp (x := 2 * u * L) (by positivity) 2
    have hfac : (Nat.factorial 2 : ℝ) = 2 := by norm_num
    rw [hfac] at h1
    have hring : (2 * u * L) ^ 2 / 2 = 2 * L ^ 2 * u ^ 2 := by ring
    rw [hring] at h1
    have hexp_neg : 0 < Real.exp (-(2 * u * L)) := Real.exp_pos _
    unfold depthKernel
    rw [Real.cosh_eq]
    linarith
  have hB_le : B₀ ≤ |B₀| := le_abs_self B₀
  have h2L2_pos : 0 < 2 * L ^ 2 := by positivity
  have hu_mul : |B₀| / (T₂ - T₁) + 4 ≤ u * (2 * L ^ 2) := (div_le_iff₀ h2L2_pos).mp hu_hi
  have hstep1 : (|B₀| / (T₂ - T₁) + 4) * u ≤ 2 * L ^ 2 * u ^ 2 := by
    nlinarith [hu_mul, hu_pos]
  have hstep2 : (|B₀| / (T₂ - T₁)) * u + 2 < depthKernel L u := by
    nlinarith [hquad, hstep1, hu1]
  have hstep3 : |B₀| * u + 2 * (T₂ - T₁) < (T₂ - T₁) * depthKernel L u := by
    have hm := mul_lt_mul_of_pos_left hstep2 hT_pos
    have hdiv : (T₂ - T₁) * (|B₀| / (T₂ - T₁) * u + 2) = |B₀| * u + 2 * (T₂ - T₁) := by
      field_simp [hT_pos.ne']
    rwa [hdiv] at hm
  have hx_sub : x - 1 / 2 = u := by dsimp [x]; ring
  rw [hx_sub] at hlin
  nlinarith [hlo_int, hlin, hstep3, hB_le, hu_pos, hT_pos]

/-! ## §2. Exact Taylor–Green abscissa representation and continuous hyperbolic layer-cake -/

private theorem depthKernel_eq_two_cosh_sub_two (L d : ℝ) :
    depthKernel L d = 2 * Real.cosh (2 * L * d) - 2 := by
  unfold depthKernel
  rw [show 2 * d * L = 2 * L * d by ring]

/-- **Exact second-order Taylor–Green representation of `depthKernel`:**
`depthKernel L (x - 1/2) = ∫ σ in (1/2)..x, 8 * L^2 * cosh(2L(σ - 1/2)) * (x - σ)` for all `x ≥ 1/2`. -/
theorem depthKernel_eq_abscissa_integral {L x : ℝ} (_hx : 1 / 2 ≤ x) :
    depthKernel L (x - 1 / 2) =
      ∫ σ in (1 / 2)..x, 8 * L ^ 2 * Real.cosh (2 * L * (σ - 1 / 2)) * (x - σ) := by
  set F : ℝ → ℝ := fun σ =>
    4 * L * Real.sinh (2 * L * (σ - 1 / 2)) * (x - σ) + 2 * Real.cosh (2 * L * (σ - 1 / 2))
  have hderiv : ∀ σ : ℝ,
      HasDerivAt F (8 * L ^ 2 * Real.cosh (2 * L * (σ - 1 / 2)) * (x - σ)) σ := by
    intro σ
    have hlin : HasDerivAt (fun t : ℝ => 2 * L * (t - 1 / 2)) (2 * L * 1) σ :=
      ((hasDerivAt_id σ).sub_const (1 / 2)).const_mul (2 * L)
    have hsh := (Real.hasDerivAt_sinh _).comp σ hlin
    have hch := (Real.hasDerivAt_cosh _).comp σ hlin
    have hsub : HasDerivAt (fun t : ℝ => x - t) (0 - 1) σ :=
      (hasDerivAt_const σ x).sub (hasDerivAt_id σ)
    exact (((hsh.const_mul (4 * L)).mul hsub).add (hch.const_mul 2)).congr_deriv
      (by simp only [Function.comp_apply]; ring)
  have hint : IntervalIntegrable
      (fun σ : ℝ => 8 * L ^ 2 * Real.cosh (2 * L * (σ - 1 / 2)) * (x - σ)) volume (1 / 2) x :=
    (by fun_prop : Continuous fun σ : ℝ =>
      8 * L ^ 2 * Real.cosh (2 * L * (σ - 1 / 2)) * (x - σ)).intervalIntegrable _ _
  rw [integral_eq_sub_of_hasDerivAt (fun σ _ => hderiv σ) hint]
  dsimp [F]
  rw [depthKernel_eq_two_cosh_sub_two]
  simp

/-- **Unit-strip hinge representation of `depthKernel`:** for `x ∈ [1/2, 1]`,
`depthKernel L (x - 1/2) = ∫ σ in (1/2)..1, 8 * L^2 * cosh(2L(σ - 1/2)) * max (x - σ) 0`. -/
theorem depthKernel_eq_unitStrip_hinge_integral {L x : ℝ} (hlo : 1 / 2 ≤ x) (hhi : x ≤ 1) :
    depthKernel L (x - 1 / 2) =
      ∫ σ in (1 / 2)..1, 8 * L ^ 2 * Real.cosh (2 * L * (σ - 1 / 2)) * max (x - σ) 0 := by
  set g : ℝ → ℝ := fun σ => 8 * L ^ 2 * Real.cosh (2 * L * (σ - 1 / 2)) * max (x - σ) 0
  have hg_cont : Continuous g := by fun_prop
  rw [← integral_add_adjacent_intervals (hg_cont.intervalIntegrable (1 / 2) x)
    (hg_cont.intervalIntegrable x 1)]
  have hleft : (∫ σ in (1 / 2)..x, g σ) =
      ∫ σ in (1 / 2)..x, 8 * L ^ 2 * Real.cosh (2 * L * (σ - 1 / 2)) * (x - σ) := by
    refine integral_congr fun σ hσ => ?_
    rw [uIcc_of_le hlo] at hσ
    dsimp [g]
    rw [max_eq_left (sub_nonneg.mpr hσ.2)]
  have hright : (∫ σ in x..1, g σ) = 0 := by
    have hcongr : (∫ σ in x..1, g σ) = ∫ _σ in x..1, (0 : ℝ) := by
      refine integral_congr fun σ hσ => ?_
      rw [uIcc_of_le hhi] at hσ
      dsimp [g]
      rw [max_eq_right (sub_nonpos.mpr hσ.1), mul_zero]
    rw [hcongr, intervalIntegral.integral_zero]
  rw [hleft, hright, add_zero, ← depthKernel_eq_abscissa_integral hlo]

/-- Nonnegative right-half mollifier zero credit obtained by integrating `max (x - σ) 0` against
`8 L² cosh(2L(σ - 1/2))` across `σ ∈ [1/2, 1]`. Vanishes identically on all left/vertical zeros
`x ≤ 1/2` (including all Euler-factor vertical zeros on `Re s = 0`). -/
def mollifierRightCredit (L x : ℝ) : ℝ :=
  ∫ σ in (1 / 2)..1, 8 * L ^ 2 * Real.cosh (2 * L * (σ - 1 / 2)) * max (x - σ) 0

theorem mollifierRightCredit_nonneg (L x : ℝ) : 0 ≤ mollifierRightCredit L x := by
  unfold mollifierRightCredit
  refine integral_nonneg (by norm_num) fun σ _ => ?_
  exact mul_nonneg (mul_nonneg (by positivity) (Real.cosh_pos _).le) (le_max_right _ _)

theorem mollifierRightCredit_eq_zero_of_le_half {L x : ℝ} (hx : x ≤ 1 / 2) :
    mollifierRightCredit L x = 0 := by
  unfold mollifierRightCredit
  have hcongr : (∫ σ in (1 / 2)..1,
      8 * L ^ 2 * Real.cosh (2 * L * (σ - 1 / 2)) * max (x - σ) 0) = ∫ _σ in (1 / 2)..1, (0 : ℝ) := by
    refine integral_congr fun σ hσ => ?_
    rw [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)] at hσ
    rw [max_eq_right (by linarith [hσ.1]), mul_zero]
  rw [hcongr, intervalIntegral.integral_zero]

theorem mollifierRightCredit_eq_depthKernel_of_mem_Icc {L x : ℝ} (hlo : 1 / 2 ≤ x) (hhi : x ≤ 1) :
    mollifierRightCredit L x = depthKernel L (x - 1 / 2) :=
  (depthKernel_eq_unitStrip_hinge_integral hlo hhi).symm

/-- First-order hyperbolic antiderivative: `depthKernel L b - depthKernel L a = ∫_a^b 4L sinh(2Lu) du`. -/
theorem depthKernel_sub_eq_sinh_integral (L a b : ℝ) :
    depthKernel L b - depthKernel L a = ∫ u in a..b, 4 * L * Real.sinh (2 * L * u) := by
  have hderiv : ∀ u : ℝ,
      HasDerivAt (fun t : ℝ => 2 * Real.cosh (2 * L * t) - 2) (4 * L * Real.sinh (2 * L * u)) u := by
    intro u
    have hlin : HasDerivAt (fun t : ℝ => 2 * L * t) (2 * L * 1) u :=
      (hasDerivAt_id u).const_mul (2 * L)
    exact ((((Real.hasDerivAt_cosh _).comp u hlin).const_mul 2).sub_const 2).congr_deriv (by ring)
  rw [integral_eq_sub_of_hasDerivAt (fun u _ => hderiv u)
    ((by fun_prop : Continuous fun u : ℝ => 4 * L * Real.sinh (2 * L * u)).intervalIntegrable a b),
    ← depthKernel_eq_two_cosh_sub_two, ← depthKernel_eq_two_cosh_sub_two]

private theorem depthKernel_sub_eq_step_integral {L a₀ b₀ d : ℝ}
    (had : a₀ ≤ d) (hdb : d ≤ b₀) :
    depthKernel L d - depthKernel L a₀ =
      ∫ u in a₀..b₀, (if u ≤ d then 4 * L * Real.sinh (2 * L * u) else 0) := by
  set g : ℝ → ℝ := fun u => 4 * L * Real.sinh (2 * L * u)
  have hg_cont : Continuous g := by fun_prop
  have heq1 : Set.EqOn (fun u => if u ≤ d then g u else 0) g (uIoc a₀ d) := by
    intro u hu
    rw [uIoc_of_le had] at hu
    exact if_pos hu.2
  have heq2 : Set.EqOn (fun u => if u ≤ d then g u else 0) (fun _ => 0) (uIoc d b₀) := by
    intro u hu
    rw [uIoc_of_le hdb] at hu
    exact if_neg (not_le.mpr hu.1)
  have hint1 : IntervalIntegrable (fun u => if u ≤ d then g u else 0) volume a₀ d :=
    (hg_cont.intervalIntegrable a₀ d).congr heq1.symm
  have hint2 : IntervalIntegrable (fun u => if u ≤ d then g u else 0) volume d b₀ :=
    intervalIntegrable_const.congr heq2.symm
  rw [← integral_add_adjacent_intervals hint1 hint2,
    intervalIntegral.integral_congr_ae (ae_of_all _ heq1),
    intervalIntegral.integral_congr_ae (ae_of_all _ heq2),
    intervalIntegral.integral_zero, add_zero, ← depthKernel_sub_eq_sinh_integral]

/-- **Continuous hyperbolic layer-cake identity:** for any finite set `S` in the right half of the
critical strip (`1/2 ≤ Re w ≤ 1`),
`∑_{w ∈ S} m(w) depthKernel L (Re w - 1/2) = ∫_0^{1/2} 4L sinh(2Lu) (∑_{w ∈ S, 1/2 + u ≤ Re w} m(w)) du`. -/
theorem sum_depthKernel_eq_sinh_tail_integral (S : Finset ℂ) (m : ℂ → ℝ) (L : ℝ)
    (hS : ∀ w ∈ S, 1 / 2 ≤ w.re ∧ w.re ≤ 1) :
    (∑ w ∈ S, m w * depthKernel L (w.re - 1 / 2)) =
      ∫ u in (0 : ℝ)..(1 / 2),
        4 * L * Real.sinh (2 * L * u) *
          ∑ w ∈ S.filter (fun w => 1 / 2 + u ≤ w.re), m w := by
  classical
  set g : ℝ → ℝ := fun u => 4 * L * Real.sinh (2 * L * u)
  have hg_cont : Continuous g := by fun_prop
  have hterm : ∀ w ∈ S,
      m w * depthKernel L (w.re - 1 / 2) =
        ∫ u in (0 : ℝ)..(1 / 2), (if 1 / 2 + u ≤ w.re then m w * g u else 0) := by
    intro w hw
    obtain ⟨hlo, hhi⟩ := hS w hw
    have hd0 : 0 ≤ w.re - 1 / 2 := sub_nonneg.mpr hlo
    have hd1 : w.re - 1 / 2 ≤ 1 / 2 := by linarith
    have hstep := depthKernel_sub_eq_step_integral (L := L) hd0 hd1
    rw [depthKernel_zero_depth, sub_zero] at hstep
    rw [hstep, ← intervalIntegral.integral_const_mul]
    refine integral_congr fun u _ => ?_
    have hiff : (u ≤ w.re - 1 / 2) ↔ (1 / 2 + u ≤ w.re) := ⟨fun h => by linarith, fun h => by linarith⟩
    by_cases h : u ≤ w.re - 1 / 2
    · rw [if_pos h, if_pos (hiff.mp h)]
    · rw [if_neg h, if_neg (fun hc => h (hiff.mpr hc)), mul_zero]
  have hint : ∀ w ∈ S,
      IntervalIntegrable (fun u => if 1 / 2 + u ≤ w.re then m w * g u else 0)
        volume (0 : ℝ) (1 / 2) := by
    intro w hw
    obtain ⟨hlo, hhi⟩ := hS w hw
    have hd0 : 0 ≤ w.re - 1 / 2 := sub_nonneg.mpr hlo
    have hd1 : w.re - 1 / 2 ≤ 1 / 2 := by linarith
    have h1 : IntervalIntegrable (fun u => if 1 / 2 + u ≤ w.re then m w * g u else 0)
        volume 0 (w.re - 1 / 2) :=
      ((hg_cont.const_mul (m w)).intervalIntegrable 0 (w.re - 1 / 2)).congr fun u hu => by
        rw [uIoc_of_le hd0] at hu
        exact (if_pos (by linarith [hu.2])).symm
    have h2 : IntervalIntegrable (fun u => if 1 / 2 + u ≤ w.re then m w * g u else 0)
        volume (w.re - 1 / 2) (1 / 2) :=
      intervalIntegrable_const.congr fun u hu => by
        rw [uIoc_of_le hd1] at hu
        exact (if_neg (by linarith [hu.1])).symm
    exact h1.trans h2
  rw [Finset.sum_congr rfl hterm, ← intervalIntegral.integral_finsetSum hint]
  refine integral_congr fun u _ => ?_
  rw [Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  split_ifs <;> ring

/-- **Truncated continuous hyperbolic layer-cake bound** on any abscissa band
`1/2 + a₀ ≤ Re w < 1/2 + b₀` (`0 ≤ a₀ ≤ b₀`, `0 ≤ L`, `m ≥ 0`). -/
theorem sum_depthKernel_band_le_sinh_tail_integral (S : Finset ℂ) (m : ℂ → ℝ) {L a₀ b₀ : ℝ}
    (hL : 0 ≤ L) (ha₀ : 0 ≤ a₀) (hab : a₀ ≤ b₀) (hm : ∀ w ∈ S, 0 ≤ m w) :
    (∑ w ∈ S.filter (fun w => 1 / 2 + a₀ ≤ w.re ∧ w.re < 1 / 2 + b₀),
        m w * depthKernel L (w.re - 1 / 2)) ≤
      depthKernel L a₀ * (∑ w ∈ S.filter (fun w => 1 / 2 + a₀ ≤ w.re), m w) +
        ∫ u in a₀..b₀,
          4 * L * Real.sinh (2 * L * u) *
            ∑ w ∈ S.filter (fun w => 1 / 2 + u ≤ w.re), m w := by
  classical
  let B := S.filter (fun w => 1 / 2 + a₀ ≤ w.re ∧ w.re < 1 / 2 + b₀)
  set g : ℝ → ℝ := fun u => 4 * L * Real.sinh (2 * L * u)
  have hg_cont : Continuous g := by fun_prop
  have hterm : ∀ w ∈ B,
      m w * depthKernel L (w.re - 1 / 2) =
        m w * depthKernel L a₀ +
          ∫ u in a₀..b₀, (if 1 / 2 + u ≤ w.re then m w * g u else 0) := by
    intro w hw
    obtain ⟨_, hlo, hhi⟩ := Finset.mem_filter.mp hw
    have hd_lo : a₀ ≤ w.re - 1 / 2 := by linarith
    have hd_hi : w.re - 1 / 2 ≤ b₀ := by linarith
    have hstep := depthKernel_sub_eq_step_integral (L := L) hd_lo hd_hi
    have hdk_eq : depthKernel L (w.re - 1 / 2) = depthKernel L a₀ +
        ∫ u in a₀..b₀, (if u ≤ w.re - 1 / 2 then g u else 0) := by linarith
    rw [hdk_eq, mul_add, ← intervalIntegral.integral_const_mul]
    congr 1
    refine integral_congr fun u _ => ?_
    have hiff : (u ≤ w.re - 1 / 2) ↔ (1 / 2 + u ≤ w.re) := ⟨fun h => by linarith, fun h => by linarith⟩
    by_cases h : u ≤ w.re - 1 / 2
    · rw [if_pos h, if_pos (hiff.mp h)]
    · rw [if_neg h, if_neg (fun hc => h (hiff.mpr hc)), mul_zero]
  have hint_B : ∀ w ∈ B,
      IntervalIntegrable (fun u => if 1 / 2 + u ≤ w.re then m w * g u else 0) volume a₀ b₀ := by
    intro w hw
    obtain ⟨_, hlo, hhi⟩ := Finset.mem_filter.mp hw
    have hd_lo : a₀ ≤ w.re - 1 / 2 := by linarith
    have hd_hi : w.re - 1 / 2 ≤ b₀ := by linarith
    have h1 : IntervalIntegrable (fun u => if 1 / 2 + u ≤ w.re then m w * g u else 0)
        volume a₀ (w.re - 1 / 2) :=
      ((hg_cont.const_mul (m w)).intervalIntegrable a₀ (w.re - 1 / 2)).congr fun u hu => by
        rw [uIoc_of_le hd_lo] at hu
        exact (if_pos (by linarith [hu.2])).symm
    have h2 : IntervalIntegrable (fun u => if 1 / 2 + u ≤ w.re then m w * g u else 0)
        volume (w.re - 1 / 2) b₀ :=
      intervalIntegrable_const.congr fun u hu => by
        rw [uIoc_of_le hd_hi] at hu
        exact (if_neg (by linarith [hu.1])).symm
    exact h1.trans h2
  have hint_S : ∀ w ∈ S,
      IntervalIntegrable (fun u => if 1 / 2 + u ≤ w.re then m w * g u else 0) volume a₀ b₀ := by
    intro w _
    rcases le_total (w.re - 1 / 2) a₀ with hle | hge
    · exact intervalIntegrable_const.congr fun u hu => by
        rw [uIoc_of_le hab] at hu
        exact (if_neg (by linarith [hu.1])).symm
    · rcases le_total b₀ (w.re - 1 / 2) with hge_b | hle_b
      · exact ((hg_cont.const_mul (m w)).intervalIntegrable a₀ b₀).congr fun u hu => by
          rw [uIoc_of_le hab] at hu
          exact (if_pos (by linarith [hu.2])).symm
      · have h1 : IntervalIntegrable (fun u => if 1 / 2 + u ≤ w.re then m w * g u else 0)
            volume a₀ (w.re - 1 / 2) :=
          ((hg_cont.const_mul (m w)).intervalIntegrable a₀ (w.re - 1 / 2)).congr fun u hu => by
            rw [uIoc_of_le hge] at hu
            exact (if_pos (by linarith [hu.2])).symm
        have h2 : IntervalIntegrable (fun u => if 1 / 2 + u ≤ w.re then m w * g u else 0)
            volume (w.re - 1 / 2) b₀ :=
          intervalIntegrable_const.congr fun u hu => by
            rw [uIoc_of_le hle_b] at hu
            exact (if_neg (by linarith [hu.1])).symm
        exact h1.trans h2
  have hlhs : (∑ w ∈ B, m w * depthKernel L (w.re - 1 / 2)) =
      depthKernel L a₀ * (∑ w ∈ B, m w) +
        ∫ u in a₀..b₀, ∑ w ∈ B, (if 1 / 2 + u ≤ w.re then m w * g u else 0) := by
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.sum_mul,
      mul_comm (∑ w ∈ B, m w), ← intervalIntegral.integral_finsetSum hint_B]
  have hrhs_int : (∫ u in a₀..b₀, g u * ∑ w ∈ S.filter (fun w => 1 / 2 + u ≤ w.re), m w) =
      ∫ u in a₀..b₀, ∑ w ∈ S, (if 1 / 2 + u ≤ w.re then m w * g u else 0) := by
    refine integral_congr fun u _ => ?_
    rw [Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    split_ifs <;> ring
  rw [hlhs, hrhs_int]
  refine add_le_add ?_ ?_
  · refine mul_le_mul_of_nonneg_left ?_ (depthKernel_nonneg L a₀)
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (fun w hw => Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hw).1, (Finset.mem_filter.mp hw).2.1⟩)
      (fun w hw _ => hm w (Finset.mem_filter.mp hw).1)
  · have hint_B_sum : IntervalIntegrable
        (fun u => ∑ w ∈ B, if 1 / 2 + u ≤ w.re then m w * g u else 0) volume a₀ b₀ :=
      (IntervalIntegrable.sum B hint_B).congr fun u _ => Finset.sum_apply u B _
    have hint_S_sum : IntervalIntegrable
        (fun u => ∑ w ∈ S, if 1 / 2 + u ≤ w.re then m w * g u else 0) volume a₀ b₀ :=
      (IntervalIntegrable.sum S hint_S).congr fun u _ => Finset.sum_apply u S _
    refine integral_mono_on (μ := volume) hab hint_B_sum hint_S_sum fun u hu => ?_
    have hg_nn : 0 ≤ g u := by
      dsimp [g]
      have hsh : 0 ≤ Real.sinh (2 * L * u) := by
        rw [Real.sinh_eq]
        have hu0 : 0 ≤ 2 * L * u := mul_nonneg (by linarith) (ha₀.trans hu.1)
        linarith [Real.exp_le_one_iff.mpr (by linarith : -(2 * L * u) ≤ 0), Real.one_le_exp hu0]
      exact mul_nonneg (by linarith) hsh
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun w hw => (Finset.mem_filter.mp hw).1)
      fun w hw _ => ?_
    split_ifs
    · exact mul_nonneg (hm w hw) hg_nn
    · exact le_rfl

/-! ## §3. One-sided (`Re z ≥ 1/2`) Green identity, mollified finite-theta curvature, and `archXi` annihilation -/

private theorem interval_ibp_zero_boundary {f g f' g' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hf' : ContinuousOn f' (Icc a b)) (hg' : ContinuousOn g' (Icc a b))
    (hdf : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (hdg : ∀ t ∈ Icc a b, HasDerivAt g (g' t) t)
    (hfa : f a = 0) (hfb : f b = 0) :
    (∫ t in a..b, f t * g' t) = - ∫ t in a..b, f' t * g t := by
  have hi1 : IntervalIntegrable (fun t => f' t * g t) volume a b :=
    (hf'.mul hg).intervalIntegrable_of_Icc hab
  have hi2 : IntervalIntegrable (fun t => f t * g' t) volume a b :=
    (hf.mul hg').intervalIntegrable_of_Icc hab
  have hftc := integral_eq_sub_of_hasDerivAt
    (f := fun t => f t * g t) (f' := fun t => f' t * g t + f t * g' t)
    (fun t ht => by
      rw [uIcc_of_le hab] at ht
      exact (hdf t ht).mul (hdg t ht))
    (hi1.add hi2)
  rw [integral_add hi1 hi2, hfb, hfa, zero_mul, zero_mul, sub_zero] at hftc
  linarith

private theorem interval_second_ibp_zero_jet {ψ u ψ' u' ψ'' u'' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hψ : ContinuousOn ψ (Icc a b)) (hu : ContinuousOn u (Icc a b))
    (hψ' : ContinuousOn ψ' (Icc a b)) (hu' : ContinuousOn u' (Icc a b))
    (hψ'' : ContinuousOn ψ'' (Icc a b)) (hu'' : ContinuousOn u'' (Icc a b))
    (hdψ : ∀ t ∈ Icc a b, HasDerivAt ψ (ψ' t) t)
    (hdu : ∀ t ∈ Icc a b, HasDerivAt u (u' t) t)
    (hdψ' : ∀ t ∈ Icc a b, HasDerivAt ψ' (ψ'' t) t)
    (hdu' : ∀ t ∈ Icc a b, HasDerivAt u' (u'' t) t)
    (hψa : ψ a = 0) (hψb : ψ b = 0) (hψ'a : ψ' a = 0) (hψ'b : ψ' b = 0) :
    (∫ t in a..b, ψ t * u'' t) = ∫ t in a..b, ψ'' t * u t := by
  rw [interval_ibp_zero_boundary hab hψ hu' hψ' hu'' hdψ hdu' hψa hψb,
    interval_ibp_zero_boundary hab hψ' hu hψ'' hu' hdψ' hdu hψ'a hψ'b, neg_neg]

/-- **One-sided (`Re z ≥ 1/2`) Green identity on `[1/2, σ_R] × [T₁, T₂]`:**
for any `C²` test `ψ` whose value and normal derivative vanish on `∂([1/2, σ_R] × [T₁, T₂])` and
any `u` that is `C²` at every point of `[1/2, σ_R] × [T₁, T₂]`,
`∫_{T₁}^{T₂} ∫_{1/2}^{σ_R} ψ Δu dx dy = ∫_{T₁}^{T₂} ∫_{1/2}^{σ_R} (Δψ) u dx dy` with zero boundary terms. -/
theorem halfPlane_green_identity_of_vanishing_jet {ψ u : ℂ → ℝ} {σ_R T₁ T₂ : ℝ}
    (hσ : 1 / 2 ≤ σ_R) (hT : T₁ ≤ T₂) (hψ : ContDiff ℝ 2 ψ)
    (hu : ∀ z ∈ Icc (1 / 2) σ_R ×ℂ Icc T₁ T₂, ContDiffAt ℝ 2 u z)
    (hleft : ∀ y ∈ Icc T₁ T₂,
      ψ (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I) = 0 ∧
        fderiv ℝ ψ (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I) 1 = 0)
    (hright : ∀ y ∈ Icc T₁ T₂,
      ψ ((σ_R : ℂ) + (y : ℂ) * I) = 0 ∧ fderiv ℝ ψ ((σ_R : ℂ) + (y : ℂ) * I) 1 = 0)
    (hbot : ∀ x ∈ Icc (1 / 2) σ_R,
      ψ ((x : ℂ) + (T₁ : ℂ) * I) = 0 ∧ fderiv ℝ ψ ((x : ℂ) + (T₁ : ℂ) * I) I = 0)
    (htop : ∀ x ∈ Icc (1 / 2) σ_R,
      ψ ((x : ℂ) + (T₂ : ℂ) * I) = 0 ∧ fderiv ℝ ψ ((x : ℂ) + (T₂ : ℂ) * I) I = 0) :
    (∫ y in T₁..T₂, ∫ x in (1 / 2)..σ_R, ψ ((x : ℂ) + (y : ℂ) * I) * Δ u ((x : ℂ) + (y : ℂ) * I)) =
      ∫ y in T₁..T₂, ∫ x in (1 / 2)..σ_R, Δ ψ ((x : ℂ) + (y : ℂ) * I) * u ((x : ℂ) + (y : ℂ) * I) := by
  set R : Set ℂ := Icc (1 / 2) σ_R ×ℂ Icc T₁ T₂
  have hmemR : ∀ x ∈ Icc (1 / 2) σ_R, ∀ y ∈ Icc T₁ T₂, ((x : ℂ) + (y : ℂ) * I) ∈ R := by
    intro x hx y hy
    exact Complex.mem_reProdIm.mpr ⟨by simpa using hx, by simpa using hy⟩
  have hpair_maps : MapsTo (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * I)
      (Icc (1 / 2) σ_R ×ˢ Icc T₁ T₂) R := fun p hp => hmemR p.1 hp.1 p.2 hp.2
  have hswap_maps : MapsTo (fun p : ℝ × ℝ => (p.2 : ℂ) + (p.1 : ℂ) * I)
      (Icc T₁ T₂ ×ˢ Icc (1 / 2) σ_R) R := fun p hp => hmemR p.2 hp.2 p.1 hp.1
  have hpair_cont : Continuous (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * I) := by fun_prop
  have hswap_cont : Continuous (fun p : ℝ × ℝ => (p.2 : ℂ) + (p.1 : ℂ) * I) := by fun_prop
  have hu_cont : ContinuousOn u R := fun z hz => (hu z hz).continuousAt.continuousWithinAt
  have hDu_cont : ∀ v : ℂ, ContinuousOn (fun z => fderiv ℝ u z v) R :=
    fun v z hz => (contDiffAt_fderiv_apply (hu z hz) v).continuousAt.continuousWithinAt
  have hddu_cont : ∀ v : ℂ, ContinuousOn (Bottcher.dderiv u v) R :=
    fun v z hz => (continuousAt_dderiv_of_contDiffAt (hu z hz) v).continuousWithinAt
  have hDψ_cont : ∀ v : ℂ, Continuous (fun z => fderiv ℝ ψ z v) :=
    fun v => ((hψ.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).continuous
  have hddψ_cont : ∀ v : ℂ, Continuous (Bottcher.dderiv ψ v) := fun v => by
    rw [continuous_iff_continuousAt]
    exact fun z => continuousAt_dderiv_of_contDiffAt hψ.contDiffAt v
  have hpart1 : (∫ y in T₁..T₂, ∫ x in (1 / 2)..σ_R,
        ψ ((x : ℂ) + (y : ℂ) * I) * Bottcher.dderiv u 1 ((x : ℂ) + (y : ℂ) * I)) =
      ∫ y in T₁..T₂, ∫ x in (1 / 2)..σ_R,
        Bottcher.dderiv ψ 1 ((x : ℂ) + (y : ℂ) * I) * u ((x : ℂ) + (y : ℂ) * I) := by
    refine integral_congr fun y hy => ?_
    rw [uIcc_of_le hT] at hy
    have hmap_x : MapsTo (fun x : ℝ => (x : ℂ) + (y : ℂ) * I) (Icc (1 / 2) σ_R) R :=
      fun x hx => hmemR x hx y hy
    have hcx : Continuous (fun x : ℝ => (x : ℂ) + (y : ℂ) * I) := cont_horiz_pt y
    exact interval_second_ibp_zero_jet hσ
      ((hψ.continuous.comp hcx).continuousOn)
      (hu_cont.comp hcx.continuousOn hmap_x)
      (((hDψ_cont 1).comp hcx).continuousOn)
      ((hDu_cont 1).comp hcx.continuousOn hmap_x)
      (((hddψ_cont 1).comp hcx).continuousOn)
      ((hddu_cont 1).comp hcx.continuousOn hmap_x)
      (fun x _ => hasDerivAt_horiz_real (hψ.differentiable (by norm_num) _))
      (fun x hx => hasDerivAt_horiz_real ((hu _ (hmemR x hx y hy)).differentiableAt (by norm_num)))
      (fun x _ => hasDerivAt_horiz_real
        ((contDiffAt_fderiv_apply hψ.contDiffAt 1).differentiableAt one_ne_zero))
      (fun x hx => hasDerivAt_horiz_real
        ((contDiffAt_fderiv_apply (hu _ (hmemR x hx y hy)) 1).differentiableAt one_ne_zero))
      (hleft y hy).1 (hright y hy).1 (hleft y hy).2 (hright y hy).2
  have hpartI : (∫ y in T₁..T₂, ∫ x in (1 / 2)..σ_R,
        ψ ((x : ℂ) + (y : ℂ) * I) * Bottcher.dderiv u I ((x : ℂ) + (y : ℂ) * I)) =
      ∫ y in T₁..T₂, ∫ x in (1 / 2)..σ_R,
        Bottcher.dderiv ψ I ((x : ℂ) + (y : ℂ) * I) * u ((x : ℂ) + (y : ℂ) * I) := by
    have hswapL := intervalIntegral_swap_of_continuousOn
      (F := fun y x => ψ ((x : ℂ) + (y : ℂ) * I) * Bottcher.dderiv u I ((x : ℂ) + (y : ℂ) * I))
      hT hσ
      (((hψ.continuous.comp hswap_cont).continuousOn).mul
        ((hddu_cont I).comp hswap_cont.continuousOn hswap_maps))
    have hswapR := intervalIntegral_swap_of_continuousOn
      (F := fun y x => Bottcher.dderiv ψ I ((x : ℂ) + (y : ℂ) * I) * u ((x : ℂ) + (y : ℂ) * I))
      hT hσ
      ((((hddψ_cont I).comp hswap_cont).continuousOn).mul
        (hu_cont.comp hswap_cont.continuousOn hswap_maps))
    rw [hswapL, hswapR]
    refine integral_congr fun x hx => ?_
    rw [uIcc_of_le hσ] at hx
    have hmap_y : MapsTo (fun y : ℝ => (x : ℂ) + (y : ℂ) * I) (Icc T₁ T₂) R :=
      fun y hy => hmemR x hx y hy
    have hcy : Continuous (fun y : ℝ => (x : ℂ) + (y : ℂ) * I) := cont_vert_pt x
    exact interval_second_ibp_zero_jet hT
      ((hψ.continuous.comp hcy).continuousOn)
      (hu_cont.comp hcy.continuousOn hmap_y)
      (((hDψ_cont I).comp hcy).continuousOn)
      ((hDu_cont I).comp hcy.continuousOn hmap_y)
      (((hddψ_cont I).comp hcy).continuousOn)
      ((hddu_cont I).comp hcy.continuousOn hmap_y)
      (fun y _ => hasDerivAt_vert_real (hψ.differentiable (by norm_num) _))
      (fun y hy => hasDerivAt_vert_real ((hu _ (hmemR x hx y hy)).differentiableAt (by norm_num)))
      (fun y _ => hasDerivAt_vert_real
        ((contDiffAt_fderiv_apply hψ.contDiffAt I).differentiableAt one_ne_zero))
      (fun y hy => hasDerivAt_vert_real
        ((contDiffAt_fderiv_apply (hu _ (hmemR x hx y hy)) I).differentiableAt one_ne_zero))
      (hbot x hx).1 (htop x hx).1 (hbot x hx).2 (htop x hx).2
  have hlhs_split : (∫ y in T₁..T₂, ∫ x in (1 / 2)..σ_R,
        ψ ((x : ℂ) + (y : ℂ) * I) * Δ u ((x : ℂ) + (y : ℂ) * I)) =
      (∫ y in T₁..T₂, ∫ x in (1 / 2)..σ_R,
        ψ ((x : ℂ) + (y : ℂ) * I) * Bottcher.dderiv u 1 ((x : ℂ) + (y : ℂ) * I)) +
      (∫ y in T₁..T₂, ∫ x in (1 / 2)..σ_R,
        ψ ((x : ℂ) + (y : ℂ) * I) * Bottcher.dderiv u I ((x : ℂ) + (y : ℂ) * I)) := by
    have hinner : ∀ y ∈ uIcc T₁ T₂,
        (∫ x in (1 / 2)..σ_R, ψ ((x : ℂ) + (y : ℂ) * I) * Δ u ((x : ℂ) + (y : ℂ) * I)) =
          (∫ x in (1 / 2)..σ_R,
            ψ ((x : ℂ) + (y : ℂ) * I) * Bottcher.dderiv u 1 ((x : ℂ) + (y : ℂ) * I)) +
          (∫ x in (1 / 2)..σ_R,
            ψ ((x : ℂ) + (y : ℂ) * I) * Bottcher.dderiv u I ((x : ℂ) + (y : ℂ) * I)) := by
      intro y hy
      rw [uIcc_of_le hT] at hy
      have hcx : Continuous (fun x : ℝ => (x : ℂ) + (y : ℂ) * I) := cont_horiz_pt y
      have hmap_x : MapsTo (fun x : ℝ => (x : ℂ) + (y : ℂ) * I) (Icc (1 / 2) σ_R) R :=
        fun x hx => hmemR x hx y hy
      have hi1 : IntervalIntegrable
          (fun x : ℝ => ψ ((x : ℂ) + (y : ℂ) * I) * Bottcher.dderiv u 1 ((x : ℂ) + (y : ℂ) * I))
          volume (1 / 2) σ_R :=
        (((hψ.continuous.comp hcx).continuousOn).mul
          ((hddu_cont 1).comp hcx.continuousOn hmap_x)).intervalIntegrable_of_Icc hσ
      have hiI : IntervalIntegrable
          (fun x : ℝ => ψ ((x : ℂ) + (y : ℂ) * I) * Bottcher.dderiv u I ((x : ℂ) + (y : ℂ) * I))
          volume (1 / 2) σ_R :=
        (((hψ.continuous.comp hcx).continuousOn).mul
          ((hddu_cont I).comp hcx.continuousOn hmap_x)).intervalIntegrable_of_Icc hσ
      have hcongr : (∫ x in (1 / 2)..σ_R, ψ ((x : ℂ) + (y : ℂ) * I) * Δ u ((x : ℂ) + (y : ℂ) * I)) =
          ∫ x in (1 / 2)..σ_R,
            (ψ ((x : ℂ) + (y : ℂ) * I) * Bottcher.dderiv u 1 ((x : ℂ) + (y : ℂ) * I) +
              ψ ((x : ℂ) + (y : ℂ) * I) * Bottcher.dderiv u I ((x : ℂ) + (y : ℂ) * I)) := by
        refine integral_congr fun x hx => ?_
        rw [uIcc_of_le hσ] at hx
        rw [laplacian_eq_dderiv_at (hu _ (hmemR x hx y hy)), mul_add]
      rw [hcongr, intervalIntegral.integral_add hi1 hiI]
    rw [integral_congr hinner, intervalIntegral.integral_add]
    · exact (continuousOn_parametric_intervalIntegral_of_continuousOn
        (F := fun y x => ψ ((x : ℂ) + (y : ℂ) * I) * Bottcher.dderiv u 1 ((x : ℂ) + (y : ℂ) * I))
        hT hσ
        (((hψ.continuous.comp hswap_cont).continuousOn).mul
          ((hddu_cont 1).comp hswap_cont.continuousOn hswap_maps))).intervalIntegrable_of_Icc hT
    · exact (continuousOn_parametric_intervalIntegral_of_continuousOn
        (F := fun y x => ψ ((x : ℂ) + (y : ℂ) * I) * Bottcher.dderiv u I ((x : ℂ) + (y : ℂ) * I))
        hT hσ
        (((hψ.continuous.comp hswap_cont).continuousOn).mul
          ((hddu_cont I).comp hswap_cont.continuousOn hswap_maps))).intervalIntegrable_of_Icc hT
  have hrhs_split : (∫ y in T₁..T₂, ∫ x in (1 / 2)..σ_R,
        Δ ψ ((x : ℂ) + (y : ℂ) * I) * u ((x : ℂ) + (y : ℂ) * I)) =
      (∫ y in T₁..T₂, ∫ x in (1 / 2)..σ_R,
        Bottcher.dderiv ψ 1 ((x : ℂ) + (y : ℂ) * I) * u ((x : ℂ) + (y : ℂ) * I)) +
      (∫ y in T₁..T₂, ∫ x in (1 / 2)..σ_R,
        Bottcher.dderiv ψ I ((x : ℂ) + (y : ℂ) * I) * u ((x : ℂ) + (y : ℂ) * I)) := by
    have hinner : ∀ y ∈ uIcc T₁ T₂,
        (∫ x in (1 / 2)..σ_R, Δ ψ ((x : ℂ) + (y : ℂ) * I) * u ((x : ℂ) + (y : ℂ) * I)) =
          (∫ x in (1 / 2)..σ_R,
            Bottcher.dderiv ψ 1 ((x : ℂ) + (y : ℂ) * I) * u ((x : ℂ) + (y : ℂ) * I)) +
          (∫ x in (1 / 2)..σ_R,
            Bottcher.dderiv ψ I ((x : ℂ) + (y : ℂ) * I) * u ((x : ℂ) + (y : ℂ) * I)) := by
      intro y hy
      rw [uIcc_of_le hT] at hy
      have hcx : Continuous (fun x : ℝ => (x : ℂ) + (y : ℂ) * I) := cont_horiz_pt y
      have hmap_x : MapsTo (fun x : ℝ => (x : ℂ) + (y : ℂ) * I) (Icc (1 / 2) σ_R) R :=
        fun x hx => hmemR x hx y hy
      have hi1 : IntervalIntegrable
          (fun x : ℝ => Bottcher.dderiv ψ 1 ((x : ℂ) + (y : ℂ) * I) * u ((x : ℂ) + (y : ℂ) * I))
          volume (1 / 2) σ_R :=
        ((((hddψ_cont 1).comp hcx).continuousOn).mul
          (hu_cont.comp hcx.continuousOn hmap_x)).intervalIntegrable_of_Icc hσ
      have hiI : IntervalIntegrable
          (fun x : ℝ => Bottcher.dderiv ψ I ((x : ℂ) + (y : ℂ) * I) * u ((x : ℂ) + (y : ℂ) * I))
          volume (1 / 2) σ_R :=
        ((((hddψ_cont I).comp hcx).continuousOn).mul
          (hu_cont.comp hcx.continuousOn hmap_x)).intervalIntegrable_of_Icc hσ
      have hcongr : (∫ x in (1 / 2)..σ_R, Δ ψ ((x : ℂ) + (y : ℂ) * I) * u ((x : ℂ) + (y : ℂ) * I)) =
          ∫ x in (1 / 2)..σ_R,
            (Bottcher.dderiv ψ 1 ((x : ℂ) + (y : ℂ) * I) * u ((x : ℂ) + (y : ℂ) * I) +
              Bottcher.dderiv ψ I ((x : ℂ) + (y : ℂ) * I) * u ((x : ℂ) + (y : ℂ) * I)) := by
        refine integral_congr fun x _ => ?_
        rw [laplacian_eq_dderiv_at hψ.contDiffAt, add_mul]
      rw [hcongr, intervalIntegral.integral_add hi1 hiI]
    rw [integral_congr hinner, intervalIntegral.integral_add]
    · exact (continuousOn_parametric_intervalIntegral_of_continuousOn
        (F := fun y x => Bottcher.dderiv ψ 1 ((x : ℂ) + (y : ℂ) * I) * u ((x : ℂ) + (y : ℂ) * I))
        hT hσ
        ((((hddψ_cont 1).comp hswap_cont).continuousOn).mul
          (hu_cont.comp hswap_cont.continuousOn hswap_maps))).intervalIntegrable_of_Icc hT
    · exact (continuousOn_parametric_intervalIntegral_of_continuousOn
        (F := fun y x => Bottcher.dderiv ψ I ((x : ℂ) + (y : ℂ) * I) * u ((x : ℂ) + (y : ℂ) * I))
        hT hσ
        ((((hddψ_cont I).comp hswap_cont).continuousOn).mul
          (hu_cont.comp hswap_cont.continuousOn hswap_maps))).intervalIntegrable_of_Icc hT
  rw [hlhs_split, hrhs_split, hpart1, hpartI]

/-- Half-plane depth-weighted test `ψ(z) = χ(z) · depthKernel L (Re z - 1/2)`. Because `depthKernel`
vanishes to second order at `0`, both `ψ` and `∂_x ψ` vanish automatically along `Re z = 1/2`
without requiring `χ` to vanish on `Re z = 1/2`. -/
def halfPlaneDepthWeight (χ : ℂ → ℝ) (L : ℝ) (z : ℂ) : ℝ :=
  χ z * depthKernel L (z.re - 1 / 2)

theorem contDiff_halfPlaneDepthWeight {χ : ℂ → ℝ} (hχ : ContDiff ℝ 2 χ) (L : ℝ) :
    ContDiff ℝ 2 (halfPlaneDepthWeight χ L) := by
  have hre : ContDiff ℝ 2 (fun z : ℂ => z.re) := Complex.reCLM.contDiff
  have hdk : ContDiff ℝ 2 (fun z : ℂ => depthKernel L (z.re - 1 / 2)) := by
    unfold depthKernel
    exact (contDiff_const.mul (Real.contDiff_cosh.comp
      ((contDiff_const.mul (hre.sub contDiff_const)).mul contDiff_const))).sub contDiff_const
  exact hχ.mul hdk

theorem halfPlaneDepthWeight_crit_jet_zero {χ : ℂ → ℝ} (hχ : Differentiable ℝ χ) (L y : ℝ) :
    halfPlaneDepthWeight χ L (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I) = 0 ∧
      fderiv ℝ (halfPlaneDepthWeight χ L) (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I) 1 = 0 := by
  set z₀ : ℂ := ((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I
  have hz₀_re : z₀.re = 1 / 2 := by simp [z₀]
  refine ⟨?_, ?_⟩
  · unfold halfPlaneDepthWeight
    rw [hz₀_re, sub_self, depthKernel_zero_depth, mul_zero]
  · have hdk_eq : (fun z : ℂ => depthKernel L (z.re - 1 / 2)) =
        fun z : ℂ => 2 * Real.cosh (2 * L * (z.re - 1 / 2)) - 2 :=
      funext fun z => depthKernel_eq_two_cosh_sub_two L (z.re - 1 / 2)
    have harg : HasFDerivAt (fun z : ℂ => 2 * L * (z.re - 1 / 2))
        ((2 * L) • Complex.reCLM) z₀ :=
      ((Complex.reCLM.hasFDerivAt (x := z₀)).sub_const (1 / 2)).const_mul (2 * L)
    have hdk_fd : HasFDerivAt (fun z : ℂ => depthKernel L (z.re - 1 / 2))
        ((2 * Real.sinh (2 * L * (z₀.re - 1 / 2))) • ((2 * L) • Complex.reCLM)) z₀ := by
      rw [hdk_eq]
      have h1 := ((Real.hasDerivAt_cosh _).comp_hasFDerivAt z₀ harg).const_mul 2 |>.sub_const 2
      simpa [smul_smul, mul_assoc] using h1
    have hprod := (hχ z₀).hasFDerivAt.mul hdk_fd
    change HasFDerivAt (halfPlaneDepthWeight χ L) _ z₀ at hprod
    rw [hprod.fderiv]
    simp [hz₀_re]

/-- **Automatic critical-line jet cancellation for `halfPlaneDepthWeight`:**
the cutoff `χ` needs vanishing 1-jet only on `{Re z = σ_R} ∪ {Im z = T₁, T₂}`, with no boundary
condition on the critical line `Re z = 1/2`. -/
theorem halfPlane_green_identity_halfPlaneDepthWeight {χ u : ℂ → ℝ} {L σ_R T₁ T₂ : ℝ}
    (hσ : 1 / 2 ≤ σ_R) (hT : T₁ ≤ T₂) (hχ : ContDiff ℝ 2 χ)
    (hu : ∀ z ∈ Icc (1 / 2) σ_R ×ℂ Icc T₁ T₂, ContDiffAt ℝ 2 u z)
    (hright : ∀ y ∈ Icc T₁ T₂,
      χ ((σ_R : ℂ) + (y : ℂ) * I) = 0 ∧ fderiv ℝ χ ((σ_R : ℂ) + (y : ℂ) * I) 1 = 0)
    (hbot : ∀ x ∈ Icc (1 / 2) σ_R,
      χ ((x : ℂ) + (T₁ : ℂ) * I) = 0 ∧ fderiv ℝ χ ((x : ℂ) + (T₁ : ℂ) * I) I = 0)
    (htop : ∀ x ∈ Icc (1 / 2) σ_R,
      χ ((x : ℂ) + (T₂ : ℂ) * I) = 0 ∧ fderiv ℝ χ ((x : ℂ) + (T₂ : ℂ) * I) I = 0) :
    (∫ y in T₁..T₂, ∫ x in (1 / 2)..σ_R,
        halfPlaneDepthWeight χ L ((x : ℂ) + (y : ℂ) * I) * Δ u ((x : ℂ) + (y : ℂ) * I)) =
      ∫ y in T₁..T₂, ∫ x in (1 / 2)..σ_R,
        Δ (halfPlaneDepthWeight χ L) ((x : ℂ) + (y : ℂ) * I) *
          u ((x : ℂ) + (y : ℂ) * I) := by
  have hdk_diff : Differentiable ℝ (fun z : ℂ => depthKernel L (z.re - 1 / 2)) := by
    have hdk_cd : ContDiff ℝ 2 (fun z : ℂ => depthKernel L (z.re - 1 / 2)) := by
      unfold depthKernel
      exact (contDiff_const.mul (Real.contDiff_cosh.comp
        ((contDiff_const.mul (Complex.reCLM.contDiff.sub contDiff_const)).mul
          contDiff_const))).sub contDiff_const
    exact hdk_cd.differentiable (by norm_num)
  have hχ_diff : Differentiable ℝ χ := hχ.differentiable (by norm_num)
  have hfderiv_mul_zero : ∀ z v : ℂ, χ z = 0 → fderiv ℝ χ z v = 0 →
      (v.re = 0 ∨ fderiv ℝ (fun w : ℂ => depthKernel L (w.re - 1 / 2)) z v = 0 ∨ χ z = 0) →
      fderiv ℝ (halfPlaneDepthWeight χ L) z v = 0 := by
    intro z v hχz hDχ _
    have hp := (hχ_diff z).hasFDerivAt.mul (hdk_diff z).hasFDerivAt
    change HasFDerivAt (halfPlaneDepthWeight χ L) _ z at hp
    rw [hp.fderiv]
    simp [hχz, hDχ]
  refine halfPlane_green_identity_of_vanishing_jet hσ hT (contDiff_halfPlaneDepthWeight hχ L) hu
    (fun y _ => halfPlaneDepthWeight_crit_jet_zero hχ_diff L y)
    (fun y hy => ⟨by simp [halfPlaneDepthWeight, (hright y hy).1],
      hfderiv_mul_zero _ 1 (hright y hy).1 (hright y hy).2 (Or.inr (Or.inr (hright y hy).1))⟩)
    (fun x hx => ⟨by simp [halfPlaneDepthWeight, (hbot x hx).1],
      hfderiv_mul_zero _ I (hbot x hx).1 (hbot x hx).2 (Or.inr (Or.inr (hbot x hx).1))⟩)
    (fun x hx => ⟨by simp [halfPlaneDepthWeight, (htop x hx).1],
      hfderiv_mul_zero _ I (htop x hx).1 (htop x hx).2 (Or.inr (Or.inr (htop x hx).1))⟩)

/-- Regularized logarithmic potential of a mollified finite-theta amplitude
`finiteThetaAmplitude K z * edPoly b (Finset.Icc 1 N) z`. -/
def mollifiedFiniteThetaPotential (η : ℝ) (K : ℕ) (b : ℕ → ℂ) (N : ℕ) (z : ℂ) : ℝ :=
  radialLogPotential η (finiteThetaAmplitude K z * edPoly b (Finset.Icc 1 N) z)

/-- Regularized logarithmic potential of the mollified completed zeta function
`xi z * edPoly b (Finset.Icc 1 N) z`. -/
def mollifiedXiPotential (η : ℝ) (b : ℕ → ℂ) (N : ℕ) (z : ℂ) : ℝ :=
  radialLogPotential η (xi z * edPoly b (Finset.Icc 1 N) z)

theorem contDiff_mollifiedFiniteThetaPotential {η : ℝ} (hη : 0 < η) (K : ℕ) (b : ℕ → ℂ) (N : ℕ) :
    ContDiff ℝ 2 (mollifiedFiniteThetaPotential η K b N) := by
  have hd : Differentiable ℂ (fun z => finiteThetaAmplitude K z * edPoly b (Finset.Icc 1 N) z) :=
    (differentiable_finiteThetaAmplitude K).mul
      (differentiable_edPoly b fun n hn => (Finset.mem_Icc.mp hn).1)
  exact (contDiff_radialLogPotential hη).comp (hd.contDiff.restrict_scalars ℝ)

theorem contDiff_mollifiedXiPotential {η : ℝ} (hη : 0 < η) (b : ℕ → ℂ) (N : ℕ) :
    ContDiff ℝ 2 (mollifiedXiPotential η b N) := by
  have hd : Differentiable ℂ (fun z => xi z * edPoly b (Finset.Icc 1 N) z) :=
    xi_differentiable.mul (differentiable_edPoly b fun n hn => (Finset.mem_Icc.mp hn).1)
  exact (contDiff_radialLogPotential hη).comp (hd.contDiff.restrict_scalars ℝ)

/-- Exact positive-curvature formula for `mollifiedFiniteThetaPotential`: both `finiteThetaAmplitude`
zeros and Dirichlet mollifier zeros contribute nonnegative subharmonic curvature. -/
theorem laplacian_mollifiedFiniteThetaPotential {η : ℝ} (hη : 0 < η) (K : ℕ) (b : ℕ → ℂ)
    (N : ℕ) (z : ℂ) :
    Δ (mollifiedFiniteThetaPotential η K b N) z =
      2 * η *
        Complex.normSq (deriv (fun w => finiteThetaAmplitude K w * edPoly b (Finset.Icc 1 N) w) z) /
          (Complex.normSq (finiteThetaAmplitude K z * edPoly b (Finset.Icc 1 N) z) + η) ^ 2 := by
  have hd : Differentiable ℂ (fun w => finiteThetaAmplitude K w * edPoly b (Finset.Icc 1 N) w) :=
    (differentiable_finiteThetaAmplitude K).mul
      (differentiable_edPoly b fun n hn => (Finset.mem_Icc.mp hn).1)
  rw [show mollifiedFiniteThetaPotential η K b N =
        radialLogPotential η ∘ (fun w => finiteThetaAmplitude K w * edPoly b (Finset.Icc 1 N) w) from rfl,
    laplacian_real_holomorphic_comp _ _ (contDiff_radialLogPotential hη) hd,
    laplacian_radialLogPotential hη]
  ring

theorem laplacian_mollifiedFiniteThetaPotential_nonneg {η : ℝ} (hη : 0 < η) (K : ℕ) (b : ℕ → ℂ)
    (N : ℕ) (z : ℂ) :
    0 ≤ Δ (mollifiedFiniteThetaPotential η K b N) z := by
  rw [laplacian_mollifiedFiniteThetaPotential hη]
  exact div_nonneg (mul_nonneg (by positivity) (Complex.normSq_nonneg _)) (sq_nonneg _)

/-- Exact positive-curvature formula for `mollifiedXiPotential`. -/
theorem laplacian_mollifiedXiPotential {η : ℝ} (hη : 0 < η) (b : ℕ → ℂ) (N : ℕ) (z : ℂ) :
    Δ (mollifiedXiPotential η b N) z =
      2 * η * Complex.normSq (deriv (fun w => xi w * edPoly b (Finset.Icc 1 N) w) z) /
        (Complex.normSq (xi z * edPoly b (Finset.Icc 1 N) z) + η) ^ 2 := by
  have hd : Differentiable ℂ (fun w => xi w * edPoly b (Finset.Icc 1 N) w) :=
    xi_differentiable.mul (differentiable_edPoly b fun n hn => (Finset.mem_Icc.mp hn).1)
  rw [show mollifiedXiPotential η b N =
        radialLogPotential η ∘ (fun w => xi w * edPoly b (Finset.Icc 1 N) w) from rfl,
    laplacian_real_holomorphic_comp _ _ (contDiff_radialLogPotential hη) hd,
    laplacian_radialLogPotential hη]
  ring

theorem laplacian_mollifiedXiPotential_nonneg {η : ℝ} (hη : 0 < η) (b : ℕ → ℂ) (N : ℕ) (z : ℂ) :
    0 ≤ Δ (mollifiedXiPotential η b N) z := by
  rw [laplacian_mollifiedXiPotential hη]
  exact div_nonneg (mul_nonneg (by positivity) (Complex.normSq_nonneg _)) (sq_nonneg _)

private theorem radialZero_contDiffAt {w : ℂ} (hw : w ≠ 0) :
    ContDiffAt ℝ 2 (radialLogPotential 0) w := by
  have hpos : 0 < w.re ^ 2 + w.im ^ 2 + 0 := by
    have hns : 0 < Complex.normSq w := Complex.normSq_pos.mpr hw
    rw [Complex.normSq_apply] at hns
    nlinarith
  unfold radialLogPotential
  exact contDiffAt_const.mul
    ((((Complex.reCLM.contDiff.pow 2).add (Complex.imCLM.contDiff.pow 2)).add
      contDiff_const).contDiffAt.log hpos.ne')

private theorem radialZero_laplacian_eq_zero {w : ℂ} (hw : w ≠ 0) :
    Δ (radialLogPotential 0) w = 0 := by
  have hpos_at : ∀ z : ℂ, z ≠ 0 → 0 < z.re ^ 2 + z.im ^ 2 + 0 := by
    intro z hz
    have hns : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz
    rw [Complex.normSq_apply] at hns
    nlinarith
  have hfirst_ev : ∀ v : ℂ,
      (fun z => fderiv ℝ (radialLogPotential 0) z v) =ᶠ[𝓝 w]
        fun z : ℂ => (z.re * v.re + z.im * v.im) / (z.re ^ 2 + z.im ^ 2 + 0) := by
    intro v
    filter_upwards [isOpen_ne.mem_nhds hw] with z hz
    have hq := ((Complex.reCLM.hasFDerivAt (x := z)).pow 2).add
      ((Complex.imCLM.hasFDerivAt (x := z)).pow 2) |>.add_const 0
    have hd := (hq.log (hpos_at z hz).ne').const_mul (1 / 2)
    change HasFDerivAt (radialLogPotential 0) _ z at hd
    rw [hd.fderiv]
    simp only [FunLike.coe_smul, FunLike.coe_add, Pi.smul_apply, Pi.add_apply,
      Complex.reCLM_apply, Complex.imCLM_apply, smul_eq_mul, nsmul_eq_mul]
    norm_num
    ring
  have hsecond : ∀ v : ℂ,
      Bottcher.dderiv (radialLogPotential 0) v w =
        ((v.re ^ 2 + v.im ^ 2) * (w.re ^ 2 + w.im ^ 2) -
          2 * (w.re * v.re + w.im * v.im) ^ 2) / (w.re ^ 2 + w.im ^ 2) ^ 2 := by
    intro v
    rw [Bottcher.dderiv, (hfirst_ev v).fderiv_eq]
    simp_rw [add_zero, div_eq_mul_inv]
    have hden_ne : w.re ^ 2 + w.im ^ 2 ≠ 0 := by linarith [hpos_at w hw]
    have hn := ((Complex.reCLM.hasFDerivAt (x := w)).mul_const v.re).add
      ((Complex.imCLM.hasFDerivAt (x := w)).mul_const v.im)
    have hq := ((Complex.reCLM.hasFDerivAt (x := w)).pow 2).add
      ((Complex.imCLM.hasFDerivAt (x := w)).pow 2)
    have hi := (hasDerivAt_inv hden_ne).comp_hasFDerivAt w hq
    have hd := hn.mul hi
    change HasFDerivAt (fun z : ℂ => (z.re * v.re + z.im * v.im) *
      (z.re ^ 2 + z.im ^ 2)⁻¹) _ w at hd
    rw [hd.fderiv]
    simp only [FunLike.coe_smul, FunLike.coe_add, Pi.smul_apply, Pi.add_apply,
      Complex.reCLM_apply, Complex.imCLM_apply, smul_eq_mul, nsmul_eq_mul]
    norm_num
    field_simp [hden_ne]
    ring
  rw [laplacian_eq_dderiv_at (radialZero_contDiffAt hw), hsecond 1, hsecond I]
  simp only [Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im,
    one_pow, zero_pow (by norm_num : 2 ≠ 0), mul_one, mul_zero, add_zero, zero_add]
  ring

/-- Every nonvanishing analytic germ `G` has `C²` harmonic logarithmic norm `Δ(log ‖G‖) = 0`. -/
theorem contDiffAt_and_laplacian_log_norm_eq_zero {G : ℂ → ℂ} {z : ℂ}
    (hG : AnalyticAt ℂ G z) (hne : G z ≠ 0) :
    ContDiffAt ℝ 2 (fun w => Real.log ‖G w‖) z ∧ Δ (fun w => Real.log ‖G w‖) z = 0 := by
  have hGc : ContDiffAt ℂ 2 G z := hG.contDiffAt
  have hGr : ContDiffAt ℝ 2 G z := hGc.restrict_scalars ℝ
  have hrad_eq : (fun w => Real.log ‖G w‖) =ᶠ[𝓝 z] (radialLogPotential 0 ∘ G) := by
    filter_upwards [hG.continuousAt.eventually_ne hne] with w hw
    have hsq : (G w).re ^ 2 + (G w).im ^ 2 + 0 = ‖G w‖ ^ 2 := by
      rw [add_zero, Complex.sq_norm, Complex.normSq_apply]; ring
    simp only [Function.comp_apply, radialLogPotential, hsq, Real.log_pow]
    ring
  have hcomp_cd : ContDiffAt ℝ 2 (radialLogPotential 0 ∘ G) z :=
    (radialZero_contDiffAt hne).comp z hGr
  refine ⟨hcomp_cd.congr_of_eventuallyEq hrad_eq, ?_⟩
  rw [(laplacian_congr_nhds hrad_eq).eq_of_nhds]
  have huc : ContDiffAt ℝ 2 (Complex.ofRealCLM ∘ radialLogPotential 0) (G z) :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp (G z) (radialZero_contDiffAt hne)
  have hc := HTGeometry.ComplexC2Laplacian.laplacian_holomorphic_comp
    (f := Complex.ofRealCLM ∘ radialLogPotential 0) (g := G) (z := z) huc hGc
  have hcomplex_eq : ∀ (f : ℂ → ℂ) (w : ℂ), ContDiffAt ℝ 2 f w →
      HTGeometry.ComplexC2Laplacian.laplacian f w = Δ f w := by
    intro f w hf
    have hb := congrFun (laplacian_eq_iteratedFDeriv_orthonormalBasis f Complex.orthonormalBasisOneI) w
    have h0 : Complex.orthonormalBasisOneI 0 = (1 : ℂ) := by simp [Complex.coe_orthonormalBasisOneI]
    have h1 : Complex.orthonormalBasisOneI 1 = I := by simp [Complex.coe_orthonormalBasisOneI]
    rw [hb, Fin.sum_univ_two, h0, h1]
    have key : ∀ v : ℂ, fderiv ℝ (fun y => fderiv ℝ f y v) w v = iteratedFDeriv ℝ 2 f w ![v, v] := by
      intro v
      rw [iteratedFDeriv_two_apply]
      have hd := ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
      simpa using congrArg (fun L => L v) (hd.clm_apply (hasFDerivAt_const v w)).fderiv
    exact congrArg₂ (· + ·) (key 1) (key I)
  rw [hcomplex_eq _ z (huc.comp z hGr), hcomplex_eq _ (G z) huc] at hc
  have hleft := hcomp_cd.laplacian_CLM_comp_left (l := Complex.ofRealCLM) (x := z)
  have hright := (radialZero_contDiffAt hne).laplacian_CLM_comp_left
    (l := Complex.ofRealCLM) (x := G z)
  change Δ (Complex.ofRealCLM ∘ (radialLogPotential 0 ∘ G)) z = _ at hc
  rw [hleft, hright] at hc
  simp only [Function.comp_apply, radialZero_laplacian_eq_zero hne, map_zero, mul_zero] at hc
  have hc' : ((Δ (radialLogPotential 0 ∘ G) z : ℝ) : ℂ) = 0 := by simpa using hc
  exact_mod_cast hc'

/-- `archXi` is analytic and nonvanishing on `{z : ℂ | 0 < z.re ∧ z ≠ 1}`, hence `log ‖archXi‖`
is `C²` and harmonic everywhere on `[1/2, σ_R] × [T₁, T₂]` for any `0 < T₁ ≤ T₂`. -/
theorem archXi_analyticAt_and_ne_zero {z : ℂ} (hre : 0 < z.re) (hne1 : z ≠ 1) :
    AnalyticAt ℂ archXi z ∧ archXi z ≠ 0 := by
  have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hdiff : DifferentiableOn ℂ archXi {w : ℂ | 0 < w.re} :=
    fun w hw => (differentiableAt_archXi hw).differentiableWithinAt
  have hana : AnalyticAt ℂ archXi z := hdiff.analyticOnNhd hopen z hre
  have hne0 : z ≠ 0 := by rintro rfl; simp at hre
  have hne : archXi z ≠ 0 := by
    unfold archXi
    exact mul_ne_zero (div_ne_zero (mul_ne_zero hne0 (sub_ne_zero.mpr hne1)) two_ne_zero)
      (Complex.Gammaℝ_ne_zero_of_re_pos hre)
  exact ⟨hana, hne⟩

/-- **Archimedean harmonic annihilation:** on any half-plane rectangle `[1/2, σ_R] × [T₁, T₂]`
(`0 < T₁ ≤ T₂`), testing `log ‖archXi‖` against `Δψ` for any `ψ` with vanishing 1-jet on the
boundary identically gives `0`, isolating `log ‖riemannZeta z * M z‖` from `log ‖xi z * M z‖`. -/
theorem halfPlane_archXi_log_norm_annihilated {ψ : ℂ → ℝ} {σ_R T₁ T₂ : ℝ}
    (hσ : 1 / 2 ≤ σ_R) (hT₁ : 0 < T₁) (hT : T₁ ≤ T₂) (hψ : ContDiff ℝ 2 ψ)
    (hleft : ∀ y ∈ Icc T₁ T₂,
      ψ (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I) = 0 ∧
        fderiv ℝ ψ (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I) 1 = 0)
    (hright : ∀ y ∈ Icc T₁ T₂,
      ψ ((σ_R : ℂ) + (y : ℂ) * I) = 0 ∧ fderiv ℝ ψ ((σ_R : ℂ) + (y : ℂ) * I) 1 = 0)
    (hbot : ∀ x ∈ Icc (1 / 2) σ_R,
      ψ ((x : ℂ) + (T₁ : ℂ) * I) = 0 ∧ fderiv ℝ ψ ((x : ℂ) + (T₁ : ℂ) * I) I = 0)
    (htop : ∀ x ∈ Icc (1 / 2) σ_R,
      ψ ((x : ℂ) + (T₂ : ℂ) * I) = 0 ∧ fderiv ℝ ψ ((x : ℂ) + (T₂ : ℂ) * I) I = 0) :
    (∫ y in T₁..T₂, ∫ x in (1 / 2)..σ_R,
        Δ ψ ((x : ℂ) + (y : ℂ) * I) * Real.log ‖archXi ((x : ℂ) + (y : ℂ) * I)‖) = 0 := by
  have hu : ∀ z ∈ Icc (1 / 2) σ_R ×ℂ Icc T₁ T₂,
      ContDiffAt ℝ 2 (fun w => Real.log ‖archXi w‖) z ∧
        Δ (fun w => Real.log ‖archXi w‖) z = 0 := by
    intro z hz
    obtain ⟨hzx, hzy⟩ := Complex.mem_reProdIm.mp hz
    have hre : 0 < z.re := by linarith [hzx.1]
    have hne1 : z ≠ 1 := by
      rintro rfl
      simp only [Complex.one_im] at hzy
      linarith [hzy.1]
    obtain ⟨hana, hne⟩ := archXi_analyticAt_and_ne_zero hre hne1
    exact contDiffAt_and_laplacian_log_norm_eq_zero hana hne
  rw [← halfPlane_green_identity_of_vanishing_jet hσ hT hψ (fun z hz => (hu z hz).1)
    hleft hright hbot htop]
  have hinner : ∀ y ∈ uIcc T₁ T₂,
      (∫ x in (1 / 2)..σ_R,
        ψ ((x : ℂ) + (y : ℂ) * I) * Δ (fun w => Real.log ‖archXi w‖) ((x : ℂ) + (y : ℂ) * I)) = 0 := by
    intro y hy
    rw [uIcc_of_le hT] at hy
    have hcongr : (∫ x in (1 / 2)..σ_R,
        ψ ((x : ℂ) + (y : ℂ) * I) * Δ (fun w => Real.log ‖archXi w‖) ((x : ℂ) + (y : ℂ) * I)) =
        ∫ _x in (1 / 2)..σ_R, (0 : ℝ) := by
      refine integral_congr fun x hx => ?_
      rw [uIcc_of_le hσ] at hx
      have hmem : ((x : ℂ) + (y : ℂ) * I) ∈ Icc (1 / 2) σ_R ×ℂ Icc T₁ T₂ :=
        Complex.mem_reProdIm.mpr ⟨by simpa using hx, by simpa using hy⟩
      rw [(hu _ hmem).2, mul_zero]
    rw [hcongr, intervalIntegral.integral_zero]
  rw [integral_congr hinner, intervalIntegral.integral_zero]

/-- Exact conversion between `‖riemannZeta s * M s‖²` and `‖xi s * M s‖² / ‖archXi s‖²` for
`0 < Re s`, `s ≠ 1`. -/
theorem norm_zeta_mul_sq_eq_norm_xi_mul_sq_div_archXi {s : ℂ} (hs : 0 < s.re) (h1 : s ≠ 1)
    (M : ℂ) :
    ‖riemannZeta s * M‖ ^ 2 = ‖xi s * M‖ ^ 2 / ‖archXi s‖ ^ 2 := by
  obtain ⟨_, hne⟩ := archXi_analyticAt_and_ne_zero hs h1
  have hxi : xi s * M = archXi s * (riemannZeta s * M) := by
    rw [xi_eq_archXi_mul_riemannZeta hs h1, mul_assoc]
  symm
  rw [hxi, norm_mul, mul_pow, mul_div_cancel_left₀ _ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hne))]

/-! ## §4. Wide mollifier-credited hinge bound and continuous abscissa-integrated source ceiling -/

/-- **Wide mollifier-credited Littlewood hinge ceiling (`1/2 ≤ σ₀ < 2`):**
retains both the full `ζ` zero hinge `∑_{w ∈ Z} m_w(ζ) max(Re w - σ₀, 0)` and the nonnegative
right-half mollifier zero credit `∑_{w ∈ Z_Ψ} m_w(Ψ) max(Re w - σ₀, 0)`, while all left/vertical
zeros `Re w ≤ 1/2` of `Ψ` contribute `0`. -/
theorem exists_wide_zetaOffLine_hinge_add_mollifierCredit_le :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ (b : ℕ → ℂ) (N : ℕ), 1 ≤ N → b 1 = 1 →
        (∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1) →
        (∀ n ∈ Finset.Icc 1 N, (starRingEnd ℂ) (b n) = b n) →
      ∀ Mb : ℝ, 1 ≤ Mb →
        (∑ n ∈ Finset.Icc 1 N, ‖b n‖ * ((n : ℝ) ^ (4 : ℝ))) ≤ Mb →
      ∀ σ₀ T₁ T₂ Msq : ℝ, 1 / 2 ≤ σ₀ → σ₀ < 2 → 20 ≤ T₁ → T₁ < T₂ →
        (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ), riemannZeta ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) →
        (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ), riemannZeta ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) →
        (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ),
          edPoly b (Finset.Icc 1 N) ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) →
        (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ),
          edPoly b (Finset.Icc 1 N) ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) →
        (∫ t in T₁..T₂,
          ‖riemannZeta ((σ₀ : ℂ) + (t : ℂ) * I) *
            edPoly b (Finset.Icc 1 N) ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤ Msq →
      ∀ Z ZΨ : Finset ℂ,
        (∀ z : ℂ, z ∈ Z ↔
          z ∈ (uIcc (1 / 2 : ℝ) (15 / 2) ×ℂ uIcc T₁ T₂) ∧ riemannZeta z = 0) →
        (∀ z : ℂ, z ∈ ZΨ ↔
          z ∈ (uIcc (1 / 2 : ℝ) (15 / 2) ×ℂ uIcc T₁ T₂) ∧
            edPoly b (Finset.Icc 1 N) z = 0) →
        0 < (∫ t in T₁..T₂,
          ‖riemannZeta ((σ₀ : ℂ) + (t : ℂ) * I) *
            edPoly b (Finset.Icc 1 N) ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2) ∧
        2 * Real.pi *
            ((∑ w ∈ Z, ((analyticOrderAt riemannZeta w).toNat : ℝ) * max (w.re - σ₀) 0) +
              ∑ w ∈ ZΨ,
                ((analyticOrderAt (edPoly b (Finset.Icc 1 N)) w).toNat : ℝ) * max (w.re - σ₀) 0)
          ≤ (T₂ - T₁) / 2 * Real.log (Msq / (T₂ - T₁)) +
              C + K * (Real.log T₂ + Real.log Mb) := by
  classical
  obtain ⟨C, K, hC, hK, hbudget⟩ := exists_levinson_mollified_budget_le_wide
  refine ⟨C, K, hC, hK, ?_⟩
  intro b N hN hb1 hbn hbreal Mb hMb1 hmass σ₀ T₁ T₂ Msq hσ₀_half hσ₀' h20 hT
    hG1 hG2 hP1 hP2 hMsq Z ZΨ hZ hZΨ
  have hσ₀ : 1 / 4 ≤ σ₀ := by linarith
  set s : Finset ℕ := Finset.Icc 1 N
  have hs : ∀ m ∈ s, 1 ≤ m := fun m hm => (Finset.mem_Icc.mp hm).1
  have h1mem : 1 ∈ s := Finset.mem_Icc.mpr ⟨le_rfl, hN⟩
  have hσ₀15 : σ₀ < 15 / 2 := by linarith
  have huIccx : uIcc σ₀ (15 / 2 : ℝ) = Set.Icc σ₀ (15 / 2 : ℝ) := uIcc_of_le hσ₀15.le
  have huIcct : uIcc T₁ T₂ = Set.Icc T₁ T₂ := uIcc_of_le hT.le
  have hne1 : ∀ (x T : ℝ), 20 ≤ T → ((x : ℂ) + (T : ℂ) * I) ≠ 1 := by
    intro x T hT' hEq
    have him := congrArg Complex.im hEq
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, Complex.one_im] at him
    linarith
  have hlamN : ‖((0 : ℝ) : ℂ)‖ ≤ 1 := by simp
  have hG0 : ∀ z : ℂ, levinsonG ((0 : ℝ) : ℂ) z = riemannZeta z := fun z => by simp [levinsonG]
  set Ψ : ℂ → ℂ := edPoly b s with hΨdef
  set g : ℂ → ℂ := levinsonMollifiedDetector ((0 : ℝ) : ℂ) b s with hgdef
  set F : ℂ → ℂ := fun z => levinsonGEntire ((0 : ℝ) : ℂ) z * Ψ z with hFdef
  have hΨana : AnalyticOnNhd ℂ Ψ Set.univ := analyticOnNhd_edPoly b hs
  have hΨright : ∀ t : ℝ, Ψ (((15 / 2 : ℝ) : ℂ) + (t : ℂ) * I) ≠ 0 := by
    intro t h0
    rw [hΨdef] at h0
    have hre : (2 : ℝ) ≤ ((((15 / 2 : ℝ) : ℂ) + (t : ℂ) * I)).re := by simp; norm_num
    have hd := norm_edPoly_sub_one_le_exp b hs h1mem hb1 hbn hre
    have hEsmall : Real.exp (-(Real.log 2) * ((((15 / 2 : ℝ) : ℂ) + (t : ℂ) * I)).re) ≤ 1 / 16 := by
      rw [exp_neg_log_two_eq]
      have hle : ((2 : ℝ) ^ (4 : ℝ)) ≤ ((2 : ℝ) ^ ((((15 / 2 : ℝ) : ℂ) + (t : ℂ) * I)).re) := by
        refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
        simp; norm_num
      have h16 : ((2 : ℝ) ^ (4 : ℝ)) = 16 := by
        rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
      rw [h16] at hle
      have hpos : (0 : ℝ) < (2 : ℝ) ^ ((((15 / 2 : ℝ) : ℂ) + (t : ℂ) * I)).re :=
        Real.rpow_pos_of_pos (by norm_num) _
      rw [inv_le_iff_one_le_mul₀ hpos]; linarith
    rw [h0] at hd
    have hone : ‖(0 : ℂ) - 1‖ = 1 := by simp
    rw [hone] at hd; linarith
  have hΨne : ∃ z : ℂ, Ψ z ≠ 0 := ⟨((15 / 2 : ℝ) : ℂ) + ((T₁ : ℝ) : ℂ) * I, hΨright T₁⟩
  have hGeright : ∀ t : ℝ,
      levinsonGEntire ((0 : ℝ) : ℂ) (((15 / 2 : ℝ) : ℂ) + (t : ℂ) * I) ≠ 0 :=
    fun t => levinsonGEntire_ne_zero_of_four_le hlamN (by simp; norm_num)
  have hGright : ∀ t : ℝ,
      levinsonG ((0 : ℝ) : ℂ) (((15 / 2 : ℝ) : ℂ) + (t : ℂ) * I) ≠ 0 :=
    fun t => levinsonG_ne_zero_of_four_le hlamN (by simp; norm_num)
  have hG1' : ∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ),
      levinsonG ((0 : ℝ) : ℂ) ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0 := fun x hx => by rw [hG0]; exact hG1 x hx
  have hG2' : ∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ),
      levinsonG ((0 : ℝ) : ℂ) ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0 := fun x hx => by rw [hG0]; exact hG2 x hx
  have hFbot : ∀ x ∈ uIcc σ₀ (15 / 2 : ℝ),
      levinsonGEntire ((0 : ℝ) : ℂ) ((x : ℂ) + (T₁ : ℂ) * I) * Ψ ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0 := by
    intro x hx; rw [huIccx] at hx
    refine mul_ne_zero ?_ (hP1 x hx)
    rw [Ne, levinsonGEntire_eq_zero_iff _ (hne1 x T₁ h20)]
    exact hG1' x hx
  have hFtop : ∀ x ∈ uIcc σ₀ (15 / 2 : ℝ),
      levinsonGEntire ((0 : ℝ) : ℂ) ((x : ℂ) + (T₂ : ℂ) * I) * Ψ ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0 := by
    intro x hx; rw [huIccx] at hx
    refine mul_ne_zero ?_ (hP2 x hx)
    rw [Ne, levinsonGEntire_eq_zero_iff _ (hne1 x T₂ (by linarith))]
    exact hG2' x hx
  have hFright : ∀ t ∈ uIcc T₁ T₂,
      levinsonGEntire ((0 : ℝ) : ℂ) (((15 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
        Ψ (((15 / 2 : ℝ) : ℂ) + (t : ℂ) * I) ≠ 0 :=
    fun t _ => mul_ne_zero (hGeright t) (hΨright t)
  have hGan : AnalyticOnNhd ℂ (levinsonGEntire ((0 : ℝ) : ℂ)) Set.univ :=
    analyticOnNhd_levinsonGEntire _
  have hFan : AnalyticOnNhd ℂ F Set.univ := fun z hz => (hGan z hz).mul (hΨana z hz)
  have hFne : ∃ z : ℂ, F z ≠ 0 :=
    ⟨((15 / 2 : ℝ) : ℂ) + ((T₁ : ℝ) : ℂ) * I, mul_ne_zero (hGeright T₁) (hΨright T₁)⟩
  have hGne : ∃ z : ℂ, levinsonGEntire ((0 : ℝ) : ℂ) z ≠ 0 :=
    ⟨((15 / 2 : ℝ) : ℂ) + ((T₁ : ℝ) : ℂ) * I, hGeright T₁⟩
  have hGorder : ∀ w : ℂ, analyticOrderAt (levinsonGEntire ((0 : ℝ) : ℂ)) w ≠ ⊤ := fun w =>
    analyticOrderAt_ne_top_of_entire_exists_ne_zero hGan hGne w
  have hPorder : ∀ w : ℂ, analyticOrderAt Ψ w ≠ ⊤ := fun w =>
    analyticOrderAt_ne_top_of_entire_exists_ne_zero hΨana hΨne w
  have hrectfin : {z ∈ (uIcc σ₀ (15 / 2 : ℝ) ×ℂ uIcc T₁ T₂) | F z = 0}.Finite := by
    have h := entire_zeros_closedRectangle_finite hFan hFne
      ((σ₀ : ℂ) + (T₁ : ℂ) * I) (((15 / 2 : ℝ) : ℂ) + (T₂ : ℂ) * I)
    simpa using h
  have hmemleft : ∀ t : ℝ, t ∈ uIcc T₁ T₂ →
      ((σ₀ : ℂ) + (t : ℂ) * I) ∈ (uIcc σ₀ (15 / 2 : ℝ) ×ℂ uIcc T₁ T₂) := by
    intro t ht
    refine Complex.mem_reProdIm.mpr ⟨?_, ?_⟩ <;> simp [left_mem_uIcc, ht]
  have hgFzero : ∀ t : ℝ, t ∈ uIcc T₁ T₂ →
      (g ((σ₀ : ℂ) + (t : ℂ) * I) = 0 ↔ F ((σ₀ : ℂ) + (t : ℂ) * I) = 0) := by
    intro t ht; rw [huIcct] at ht
    have hzne : ((σ₀ : ℂ) + (t : ℂ) * I) ≠ 1 := hne1 σ₀ t (by linarith [ht.1])
    constructor
    · intro h0
      have : F ((σ₀ : ℂ) + (t : ℂ) * I) =
          (((σ₀ : ℂ) + (t : ℂ) * I) - 1) ^ 2 * g ((σ₀ : ℂ) + (t : ℂ) * I) := by
        simp only [hFdef, hgdef, levinsonMollifiedDetector, levinsonGEntire_eq _ hzne]; ring
      rw [this, h0, mul_zero]
    · intro h0
      have hgauge : (((σ₀ : ℂ) + (t : ℂ) * I) - 1) ≠ 0 := sub_ne_zero.mpr hzne
      have heq : (((σ₀ : ℂ) + (t : ℂ) * I) - 1) ^ 2 * g ((σ₀ : ℂ) + (t : ℂ) * I) = 0 := by
        rw [← h0]; simp only [hFdef, hgdef, levinsonMollifiedDetector, levinsonGEntire_eq _ hzne]; ring
      rcases mul_eq_zero.mp heq with h | h
      · exact absurd (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h) hgauge
      · exact h
  have hgfin : {t : ℝ | t ∈ uIcc T₁ T₂ ∧ g ((σ₀ : ℂ) + (t : ℂ) * I) = 0}.Finite := by
    have hinj : Set.InjOn (fun t : ℝ => (σ₀ : ℂ) + (t : ℂ) * I)
        {t : ℝ | t ∈ uIcc T₁ T₂ ∧ g ((σ₀ : ℂ) + (t : ℂ) * I) = 0} := by
      intro x _ y _ hxy; simpa using congrArg Complex.im hxy
    refine Set.Finite.of_finite_image (Set.Finite.subset hrectfin ?_) hinj
    rintro z ⟨t, ⟨ht, hz⟩, rfl⟩
    exact ⟨hmemleft t ht, (hgFzero t ht).mp hz⟩
  have hgex : ∃ t ∈ Set.Ioo T₁ T₂, g ((σ₀ : ℂ) + (t : ℂ) * I) ≠ 0 := by
    by_contra hall
    push Not at hall
    have hsubset : Set.Ioo T₁ T₂ ⊆
        {t : ℝ | t ∈ uIcc T₁ T₂ ∧ g ((σ₀ : ℂ) + (t : ℂ) * I) = 0} :=
      fun t ht => ⟨by rw [huIcct]; exact Set.Ioo_subset_Icc_self ht, hall t ht⟩
    exact (Set.Ioo_infinite hT) (hgfin.subset hsubset)
  have hMsq_pos : 0 < ∫ t in T₁..T₂,
      ‖riemannZeta ((σ₀ : ℂ) + (t : ℂ) * I) * Ψ ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
    obtain ⟨t₀, ht₀, hne_t₀⟩ := hgex
    have hcont_normSq : ContinuousOn
        (fun t : ℝ => ‖riemannZeta ((σ₀ : ℂ) + (t : ℂ) * I) * Ψ ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2)
        (Icc T₁ T₂) := by
      intro t ht
      have hne : ((σ₀ : ℂ) + (t : ℂ) * I) ≠ 1 := hne1 σ₀ t (by linarith [ht.1])
      exact (((ContinuousAt.comp (g := riemannZeta) (f := fun t : ℝ => (σ₀ : ℂ) + (t : ℂ) * I)
        (differentiableAt_riemannZeta hne).continuousAt (cont_vert_pt σ₀).continuousAt).mul
        (ContinuousAt.comp (g := Ψ) (f := fun t : ℝ => (σ₀ : ℂ) + (t : ℂ) * I)
          (differentiable_edPoly b hs _).continuousAt (cont_vert_pt σ₀).continuousAt)).norm.pow
            2).continuousWithinAt
    refine intervalIntegral.integral_pos hT hcont_normSq (fun t _ => sq_nonneg _) ⟨t₀, ?_, ?_⟩
    · exact Ioo_subset_Icc_self ht₀
    · have hne' : riemannZeta ((σ₀ : ℂ) + (t₀ : ℂ) * I) * Ψ ((σ₀ : ℂ) + (t₀ : ℂ) * I) ≠ 0 := by
        simpa [hgdef, levinsonMollifiedDetector, levinsonG, hΨdef] using hne_t₀
      exact sq_pos_of_pos (norm_pos_iff.mpr hne')
  have hMsq' : (∫ t in T₁..T₂,
      ‖levinsonMollifiedDetector ((0 : ℝ) : ℂ) b s ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤ Msq := by
    refine le_trans (le_of_eq ?_) hMsq
    apply intervalIntegral.integral_congr
    intro t _; simp only [levinsonMollifiedDetector, hG0]; rfl
  have hbud := hbudget 0 (by simp) b N hN hb1 hbn hbreal Mb hMb1 hmass σ₀ T₁ T₂ Msq
    hσ₀ hσ₀' h20 hT hG1' hG2' hP1 hP2 hgfin hgex hMsq'
  have hUsub : (uIcc σ₀ (15 / 2 : ℝ) ×ℂ uIcc T₁ T₂) ⊆ {z : ℂ | z ≠ 1} := by
    intro z hz hEq
    have him := (Complex.mem_reProdIm.mp hz).2
    rw [huIcct, hEq, Complex.one_im] at him
    linarith [him.1]
  have hcongrF : weightedLittlewoodBoundary F σ₀ (15 / 2) T₁ T₂ =
      weightedLittlewoodBoundary (fun z => (z - 1) ^ 2 * g z) σ₀ (15 / 2) T₁ T₂ := by
    refine weightedLittlewoodBoundary_congr isOpen_ne hUsub fun z hz => ?_
    simp only [hFdef, hgdef, levinsonMollifiedDetector, levinsonGEntire_eq _ hz]; ring
  have hgaugefree : weightedLittlewoodBoundary (fun z => (z - 1) ^ 2 * g z) σ₀ (15 / 2) T₁ T₂ =
      weightedLittlewoodBoundary g σ₀ (15 / 2) T₁ T₂ := by
    refine weightedLittlewoodBoundary_poleGauge_mul hσ₀15 hT ?_ ?_ ?_ ?_ ?_ hgfin
    · intro hmem
      have him := (Complex.mem_reProdIm.mp hmem).2
      rw [huIcct, Complex.one_im] at him; linarith [him.1]
    · exact fun z hz => analyticAt_levinsonMollifiedDetector _ b hs (hUsub hz)
    · intro x hx; rw [huIccx] at hx; exact mul_ne_zero (hG1' x hx) (hP1 x hx)
    · intro x hx; rw [huIccx] at hx; exact mul_ne_zero (hG2' x hx) (hP2 x hx)
    · exact fun t _ => mul_ne_zero (hGright t) (hΨright t)
  obtain ⟨Z', hZ', hident⟩ :=
    exists_entire_weighted_littlewood_rectangle_allow_left_zeros hFan hFne hσ₀15 hT
      hFbot hFtop hFright
  have horder_split : ∀ w ∈ Z',
      ((analyticOrderAt F w).toNat : ℝ) =
        ((analyticOrderAt riemannZeta w).toNat : ℝ) + ((analyticOrderAt Ψ w).toNat : ℝ) := by
    intro w hw
    have hwmem := ((hZ' w).mp hw).1
    have hw1 : w ≠ 1 := hUsub hwmem
    have hev : levinsonGEntire ((0 : ℝ) : ℂ) =ᶠ[nhds w]
        (fun z : ℂ => (z - 1) ^ 2) * riemannZeta := by
      filter_upwards [isOpen_ne.mem_nhds hw1] with z hz
      rw [Pi.mul_apply, levinsonGEntire_eq _ hz, hG0]
    have hpow_an : AnalyticAt ℂ (fun z : ℂ => (z - 1) ^ 2) w :=
      (analyticAt_id.sub analyticAt_const).pow 2
    have hordG : analyticOrderAt (levinsonGEntire ((0 : ℝ) : ℂ)) w =
        analyticOrderAt riemannZeta w := by
      rw [analyticOrderAt_congr hev,
        analyticOrderAt_mul hpow_an (analyticAt_riemannZeta_of_ne_one hw1),
        (hpow_an.analyticOrderAt_eq_zero).mpr (pow_ne_zero 2 (sub_ne_zero.mpr hw1)), zero_add]
    have hmul := analyticOrderAt_mul (hGan w (Set.mem_univ _)) (hΨana w (Set.mem_univ _))
    change ((analyticOrderAt (levinsonGEntire ((0 : ℝ) : ℂ) * Ψ) w).toNat : ℝ) = _
    rw [hmul, ENat.toNat_add (hGorder w) (hPorder w), hordG]
    push_cast; rfl
  have hZ_le : (∑ w ∈ Z, ((analyticOrderAt riemannZeta w).toNat : ℝ) * max (w.re - σ₀) 0) ≤
      ∑ w ∈ Z', ((analyticOrderAt riemannZeta w).toNat : ℝ) * (w.re - σ₀) := by
    have hfilt : (∑ w ∈ Z, ((analyticOrderAt riemannZeta w).toNat : ℝ) * max (w.re - σ₀) 0) =
        ∑ w ∈ Z.filter (fun w => σ₀ ≤ w.re),
          ((analyticOrderAt riemannZeta w).toNat : ℝ) * (w.re - σ₀) := by
      rw [← Finset.sum_filter_add_sum_filter_not Z (fun w => σ₀ ≤ w.re)]
      have h0 : ∑ w ∈ Z.filter (fun w => ¬ σ₀ ≤ w.re),
          ((analyticOrderAt riemannZeta w).toNat : ℝ) * max (w.re - σ₀) 0 = 0 := by
        refine Finset.sum_eq_zero fun w hw => ?_
        have hlt := not_le.mp (Finset.mem_filter.mp hw).2
        rw [max_eq_right (by linarith), mul_zero]
      rw [h0, add_zero]
      refine Finset.sum_congr rfl fun w hw => ?_
      rw [max_eq_left (sub_nonneg.mpr (Finset.mem_filter.mp hw).2)]
    rw [hfilt]
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun w hw => ?_) (fun w hw _ => ?_)
    · obtain ⟨hwZ, hwre⟩ := Finset.mem_filter.mp hw
      obtain ⟨hwmem, hwzero⟩ := (hZ w).mp hwZ
      obtain ⟨hre, him⟩ := Complex.mem_reProdIm.mp hwmem
      rw [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 15 / 2)] at hre
      refine (hZ' w).mpr ⟨Complex.mem_reProdIm.mpr ⟨by rw [huIccx]; exact ⟨hwre, hre.2⟩, him⟩, ?_⟩
      have hw1 : w ≠ 1 := by rintro rfl; exact riemannZeta_one_ne_zero hwzero
      simp only [hFdef, levinsonGEntire_eq _ hw1, hG0, hwzero]; ring
    · have hre := (Complex.mem_reProdIm.mp ((hZ' w).mp hw).1).1
      rw [huIccx] at hre
      exact mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hre.1)
  have hZΨ_le : (∑ w ∈ ZΨ, ((analyticOrderAt Ψ w).toNat : ℝ) * max (w.re - σ₀) 0) ≤
      ∑ w ∈ Z', ((analyticOrderAt Ψ w).toNat : ℝ) * (w.re - σ₀) := by
    have hfilt : (∑ w ∈ ZΨ, ((analyticOrderAt Ψ w).toNat : ℝ) * max (w.re - σ₀) 0) =
        ∑ w ∈ ZΨ.filter (fun w => σ₀ ≤ w.re),
          ((analyticOrderAt Ψ w).toNat : ℝ) * (w.re - σ₀) := by
      rw [← Finset.sum_filter_add_sum_filter_not ZΨ (fun w => σ₀ ≤ w.re)]
      have h0 : ∑ w ∈ ZΨ.filter (fun w => ¬ σ₀ ≤ w.re),
          ((analyticOrderAt Ψ w).toNat : ℝ) * max (w.re - σ₀) 0 = 0 := by
        refine Finset.sum_eq_zero fun w hw => ?_
        have hlt := not_le.mp (Finset.mem_filter.mp hw).2
        rw [max_eq_right (by linarith), mul_zero]
      rw [h0, add_zero]
      refine Finset.sum_congr rfl fun w hw => ?_
      rw [max_eq_left (sub_nonneg.mpr (Finset.mem_filter.mp hw).2)]
    rw [hfilt]
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun w hw => ?_) (fun w hw _ => ?_)
    · obtain ⟨hwZ, hwre⟩ := Finset.mem_filter.mp hw
      obtain ⟨hwmem, hwzero⟩ := (hZΨ w).mp hwZ
      obtain ⟨hre, him⟩ := Complex.mem_reProdIm.mp hwmem
      rw [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 15 / 2)] at hre
      refine (hZ' w).mpr ⟨Complex.mem_reProdIm.mpr ⟨by rw [huIccx]; exact ⟨hwre, hre.2⟩, him⟩, ?_⟩
      simp only [hFdef, hwzero, mul_zero]
    · have hre := (Complex.mem_reProdIm.mp ((hZ' w).mp hw).1).1
      rw [huIccx] at hre
      exact mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hre.1)
  have hsum_F : (∑ w ∈ Z', ((analyticOrderAt riemannZeta w).toNat : ℝ) * (w.re - σ₀)) +
      (∑ w ∈ Z', ((analyticOrderAt Ψ w).toNat : ℝ) * (w.re - σ₀)) =
      ∑ w ∈ Z', ((analyticOrderAt F w).toNat : ℝ) * (w.re - σ₀) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [horder_split w hw, add_mul]
  refine ⟨hMsq_pos, ?_⟩
  calc 2 * Real.pi *
        ((∑ w ∈ Z, ((analyticOrderAt riemannZeta w).toNat : ℝ) * max (w.re - σ₀) 0) +
          ∑ w ∈ ZΨ, ((analyticOrderAt Ψ w).toNat : ℝ) * max (w.re - σ₀) 0)
      ≤ 2 * Real.pi * (∑ w ∈ Z', ((analyticOrderAt F w).toNat : ℝ) * (w.re - σ₀)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        linarith [hZ_le, hZΨ_le, hsum_F]
    _ = weightedLittlewoodBoundary F σ₀ (15 / 2) T₁ T₂ := hident
    _ = weightedLittlewoodBoundary g σ₀ (15 / 2) T₁ T₂ := by rw [hcongrF, hgaugefree]
    _ ≤ _ := hbud

/-- **Continuous abscissa-integrated mollified source ceiling on `shellDepthSum` (`Re z ≥ 1/2`):**
folding left-half `ξ`-zeros onto `Re z > 1/2` via `lineReflect` and integrating the wide
mollifier-credited hinge bound over `σ ∈ [1/2, 1]` bounds `π · shellDepthSum T₁ T₂ L` plus
nonnegative right-half mollifier zero credit purely by the continuous abscissa source integral of
`‖riemannZeta (σ + it) * Ψ (σ + it)‖²`, without routing through discrete zero-counting shells. -/
theorem exists_shellDepthSum_add_mollifierCredit_le_abscissa_source_integral :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ (b : ℕ → ℂ) (N : ℕ), 1 ≤ N → b 1 = 1 →
        (∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1) →
        (∀ n ∈ Finset.Icc 1 N, (starRingEnd ℂ) (b n) = b n) →
      ∀ Mb : ℝ, 1 ≤ Mb →
        (∑ n ∈ Finset.Icc 1 N, ‖b n‖ * ((n : ℝ) ^ (4 : ℝ))) ≤ Mb →
      ∀ T₁ T₂ L : ℝ, 20 ≤ T₁ → T₁ < T₂ →
        (∀ x ∈ Set.Icc (1 / 2 : ℝ) (15 / 2), riemannZeta ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) →
        (∀ x ∈ Set.Icc (1 / 2 : ℝ) (15 / 2), riemannZeta ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) →
        (∀ x ∈ Set.Icc (1 / 2 : ℝ) (15 / 2),
          edPoly b (Finset.Icc 1 N) ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) →
        (∀ x ∈ Set.Icc (1 / 2 : ℝ) (15 / 2),
          edPoly b (Finset.Icc 1 N) ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) →
      ∀ ZΨ : Finset ℂ,
        (∀ z : ℂ, z ∈ ZΨ ↔
          z ∈ (uIcc (1 / 2 : ℝ) (15 / 2) ×ℂ uIcc T₁ T₂) ∧
            edPoly b (Finset.Icc 1 N) z = 0) →
        Real.pi * shellDepthSum T₁ T₂ L +
          2 * Real.pi *
            ∑ w ∈ ZΨ,
              ((analyticOrderAt (edPoly b (Finset.Icc 1 N)) w).toNat : ℝ) *
                mollifierRightCredit L w.re ≤
          ∫ σ in (1 / 2)..1,
            8 * L ^ 2 * Real.cosh (2 * L * (σ - 1 / 2)) *
              ((T₂ - T₁) / 2 *
                Real.log ((∫ t in T₁..T₂,
                  ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I) *
                    edPoly b (Finset.Icc 1 N) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) / (T₂ - T₁)) +
                C + K * (Real.log T₂ + Real.log Mb)) := by
  classical
  obtain ⟨C, K, hC, hK, hwide⟩ := exists_wide_zetaOffLine_hinge_add_mollifierCredit_le
  refine ⟨C, K, hC, hK, ?_⟩
  intro b N hN hb1 hbn hbreal Mb hMb1 hmass T₁ T₂ L h20 hT hG1 hG2 hP1 hP2 ZΨ hZΨ
  set Ψ : ℂ → ℂ := edPoly b (Finset.Icc 1 N)
  set Z : Finset ℂ := windowZeros T₁ T₂
  have hT₁_pos : 0 < T₁ := by linarith
  have hZ_iff : ∀ z : ℂ, z ∈ Z ↔
      z ∈ (uIcc (1 / 2 : ℝ) (15 / 2) ×ℂ uIcc T₁ T₂) ∧ riemannZeta z = 0 :=
    fun z => mem_windowZeros_iff hT₁_pos hT.le z
  set Msq : ℝ → ℝ := fun σ =>
    ∫ t in T₁..T₂, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I) * Ψ ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2
  have hptw : ∀ σ ∈ Icc (1 / 2 : ℝ) 1,
      0 < Msq σ ∧
        2 * Real.pi *
            ((∑ w ∈ Z, ((analyticOrderAt riemannZeta w).toNat : ℝ) * max (w.re - σ) 0) +
              ∑ w ∈ ZΨ, ((analyticOrderAt Ψ w).toNat : ℝ) * max (w.re - σ) 0) ≤
          (T₂ - T₁) / 2 * Real.log (Msq σ / (T₂ - T₁)) +
            C + K * (Real.log T₂ + Real.log Mb) := by
    intro σ hσ
    exact hwide b N hN hb1 hbn hbreal Mb hMb1 hmass σ T₁ T₂ (Msq σ)
      hσ.1 (by linarith [hσ.2]) h20 hT
      (fun x hx => hG1 x ⟨hσ.1.trans hx.1, hx.2⟩)
      (fun x hx => hG2 x ⟨hσ.1.trans hx.1, hx.2⟩)
      (fun x hx => hP1 x ⟨hσ.1.trans hx.1, hx.2⟩)
      (fun x hx => hP2 x ⟨hσ.1.trans hx.1, hx.2⟩)
      le_rfl Z ZΨ hZ_iff hZΨ
  have hMsq_cont : ContinuousOn Msq (Icc (1 / 2 : ℝ) 1) := by
    have hp_cont : Continuous (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * I) := by fun_prop
    have hjoint : ContinuousOn
        (fun p : ℝ × ℝ => ‖riemannZeta ((p.1 : ℂ) + (p.2 : ℂ) * I) *
          Ψ ((p.1 : ℂ) + (p.2 : ℂ) * I)‖ ^ 2)
        (Icc (1 / 2 : ℝ) 1 ×ˢ Icc T₁ T₂) := by
      intro p hp
      have hne : ((p.1 : ℂ) + (p.2 : ℂ) * I) ≠ 1 := by
        intro hEq
        have him := congrArg Complex.im hEq
        simp at him
        linarith [hp.2.1]
      exact (((ContinuousAt.comp (g := riemannZeta)
        (f := fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * I)
        (differentiableAt_riemannZeta hne).continuousAt hp_cont.continuousAt).mul
        (ContinuousAt.comp (g := Ψ) (f := fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * I)
          (differentiable_edPoly b (fun n hn => (Finset.mem_Icc.mp hn).1) _).continuousAt
          hp_cont.continuousAt)).norm.pow 2).continuousWithinAt
    exact continuousOn_parametric_intervalIntegral_of_continuousOn
      (F := fun σ t => ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I) * Ψ ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
      (by norm_num) hT.le hjoint
  have hrhs_cont : ContinuousOn
      (fun σ : ℝ => 8 * L ^ 2 * Real.cosh (2 * L * (σ - 1 / 2)) *
        ((T₂ - T₁) / 2 * Real.log (Msq σ / (T₂ - T₁)) + C + K * (Real.log T₂ + Real.log Mb)))
      (Icc (1 / 2 : ℝ) 1) := by
    have hlog : ContinuousOn (fun σ : ℝ => Real.log (Msq σ / (T₂ - T₁))) (Icc (1 / 2 : ℝ) 1) := by
      refine ContinuousOn.log (hMsq_cont.div_const (T₂ - T₁)) ?_
      intro σ hσ
      exact (div_pos (hptw σ hσ).1 (sub_pos.mpr hT)).ne'
    exact ((by fun_prop : Continuous fun σ : ℝ =>
      8 * L ^ 2 * Real.cosh (2 * L * (σ - 1 / 2))).continuousOn).mul
      (((continuousOn_const.mul hlog).add continuousOn_const).add continuousOn_const)
  set K_w : ℝ → ℝ := fun σ => 8 * L ^ 2 * Real.cosh (2 * L * (σ - 1 / 2))
  have hKw_cont : Continuous K_w := by dsimp [K_w]; fun_prop
  have hlhs_cont : Continuous (fun σ : ℝ => K_w σ *
      (2 * Real.pi *
        ((∑ w ∈ Z, ((analyticOrderAt riemannZeta w).toNat : ℝ) * max (w.re - σ) 0) +
          ∑ w ∈ ZΨ, ((analyticOrderAt Ψ w).toNat : ℝ) * max (w.re - σ) 0))) := by
    have hsum1 : Continuous (fun σ : ℝ =>
        ∑ w ∈ Z, ((analyticOrderAt riemannZeta w).toNat : ℝ) * max (w.re - σ) 0) :=
      continuous_finsetSum _ fun w _ => by fun_prop
    have hsum2 : Continuous (fun σ : ℝ =>
        ∑ w ∈ ZΨ, ((analyticOrderAt Ψ w).toNat : ℝ) * max (w.re - σ) 0) :=
      continuous_finsetSum _ fun w _ => by fun_prop
    exact hKw_cont.mul (continuous_const.mul (hsum1.add hsum2))
  have hint_ineq := integral_mono_on (μ := volume) (by norm_num : (1 / 2 : ℝ) ≤ 1)
    (hlhs_cont.intervalIntegrable _ _) (hrhs_cont.intervalIntegrable_of_Icc (by norm_num))
    fun σ hσ => mul_le_mul_of_nonneg_left (hptw σ hσ).2
      (mul_nonneg (by positivity) (Real.cosh_pos _).le)
  have hint_Z : (∫ σ in (1 / 2)..1, K_w σ *
        ∑ w ∈ Z, ((analyticOrderAt riemannZeta w).toNat : ℝ) * max (w.re - σ) 0) =
      ∑ w ∈ Z, ((analyticOrderAt riemannZeta w).toNat : ℝ) * mollifierRightCredit L w.re := by
    have hrew : (fun σ : ℝ => K_w σ *
          ∑ w ∈ Z, ((analyticOrderAt riemannZeta w).toNat : ℝ) * max (w.re - σ) 0) =
        fun σ : ℝ => ∑ w ∈ Z,
          ((analyticOrderAt riemannZeta w).toNat : ℝ) * (K_w σ * max (w.re - σ) 0) := by
      funext σ; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun w _ => by ring
    rw [hrew, intervalIntegral.integral_finsetSum
      (fun w _ => (by dsimp [K_w]; fun_prop : Continuous _).intervalIntegrable _ _)]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [intervalIntegral.integral_const_mul]; rfl
  have hint_ZΨ : (∫ σ in (1 / 2)..1, K_w σ *
        ∑ w ∈ ZΨ, ((analyticOrderAt Ψ w).toNat : ℝ) * max (w.re - σ) 0) =
      ∑ w ∈ ZΨ, ((analyticOrderAt Ψ w).toNat : ℝ) * mollifierRightCredit L w.re := by
    have hrew : (fun σ : ℝ => K_w σ *
          ∑ w ∈ ZΨ, ((analyticOrderAt Ψ w).toNat : ℝ) * max (w.re - σ) 0) =
        fun σ : ℝ => ∑ w ∈ ZΨ,
          ((analyticOrderAt Ψ w).toNat : ℝ) * (K_w σ * max (w.re - σ) 0) := by
      funext σ; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun w _ => by ring
    rw [hrew, intervalIntegral.integral_finsetSum
      (fun w _ => (by dsimp [K_w]; fun_prop : Continuous _).intervalIntegrable _ _)]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [intervalIntegral.integral_const_mul]; rfl
  have hlhs_eval : (∫ σ in (1 / 2)..1, K_w σ *
        (2 * Real.pi *
          ((∑ w ∈ Z, ((analyticOrderAt riemannZeta w).toNat : ℝ) * max (w.re - σ) 0) +
            ∑ w ∈ ZΨ, ((analyticOrderAt Ψ w).toNat : ℝ) * max (w.re - σ) 0))) =
      2 * Real.pi *
        ((∑ w ∈ Z, ((analyticOrderAt riemannZeta w).toNat : ℝ) * mollifierRightCredit L w.re) +
          ∑ w ∈ ZΨ, ((analyticOrderAt Ψ w).toNat : ℝ) * mollifierRightCredit L w.re) := by
    have h1 : IntervalIntegrable (fun σ => K_w σ *
        ∑ w ∈ Z, ((analyticOrderAt riemannZeta w).toNat : ℝ) * max (w.re - σ) 0) volume (1 / 2) 1 :=
      (hKw_cont.mul (continuous_finsetSum _ fun _ _ => by fun_prop)).intervalIntegrable _ _
    have h2 : IntervalIntegrable (fun σ => K_w σ *
        ∑ w ∈ ZΨ, ((analyticOrderAt Ψ w).toNat : ℝ) * max (w.re - σ) 0) volume (1 / 2) 1 :=
      (hKw_cont.mul (continuous_finsetSum _ fun _ _ => by fun_prop)).intervalIntegrable _ _
    have hrew : (fun σ => K_w σ *
          (2 * Real.pi *
            ((∑ w ∈ Z, ((analyticOrderAt riemannZeta w).toNat : ℝ) * max (w.re - σ) 0) +
              ∑ w ∈ ZΨ, ((analyticOrderAt Ψ w).toNat : ℝ) * max (w.re - σ) 0))) =
        fun σ => 2 * Real.pi *
          (K_w σ * (∑ w ∈ Z, ((analyticOrderAt riemannZeta w).toNat : ℝ) * max (w.re - σ) 0) +
            K_w σ * (∑ w ∈ ZΨ, ((analyticOrderAt Ψ w).toNat : ℝ) * max (w.re - σ) 0)) := by
      funext σ; ring
    rw [hrew, intervalIntegral.integral_const_mul, intervalIntegral.integral_add h1 h2,
      hint_Z, hint_ZΨ]
  rw [hlhs_eval] at hint_ineq
  have hshell_le : Real.pi * shellDepthSum T₁ T₂ L ≤
      2 * Real.pi * ∑ w ∈ Z,
        ((analyticOrderAt riemannZeta w).toNat : ℝ) * mollifierRightCredit L w.re := by
    rw [shellDepthSum_eq_two_mul_right,
      show Real.pi * (2 * ∑ z ∈ (shellZeros T₁ T₂).filter (fun z => 1 / 2 < z.re),
        ((analyticOrderAt xi z).toNat : ℝ) * depthKernel L (z.re - 1 / 2)) =
        2 * Real.pi * ∑ z ∈ (shellZeros T₁ T₂).filter (fun z => 1 / 2 < z.re),
          ((analyticOrderAt xi z).toNat : ℝ) * depthKernel L (z.re - 1 / 2) by ring]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hsub : (shellZeros T₁ T₂).filter (fun z => 1 / 2 < z.re) ⊆ Z := by
      intro z hz
      obtain ⟨hz_sh, hre_gt⟩ := Finset.mem_filter.mp hz
      obtain ⟨hz_pos, him1⟩ := Finset.mem_filter.mp hz_sh
      obtain ⟨h0, h1, _, him2, hxi⟩ := mem_stripFinsetPos.mp hz_pos
      rw [hZ_iff]
      refine ⟨Complex.mem_reProdIm.mpr ⟨?_, ?_⟩, (xi_zero_iff_zeta_zero_of_mem_strip h0 h1).mp hxi⟩
      · rw [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 15 / 2)]; exact ⟨hre_gt.le, by linarith⟩
      · rw [uIcc_of_le hT.le]; exact ⟨him1.le, him2⟩
    have hcongr_sum : (∑ z ∈ (shellZeros T₁ T₂).filter (fun z => 1 / 2 < z.re),
          ((analyticOrderAt xi z).toNat : ℝ) * depthKernel L (z.re - 1 / 2)) =
        ∑ z ∈ (shellZeros T₁ T₂).filter (fun z => 1 / 2 < z.re),
          ((analyticOrderAt riemannZeta z).toNat : ℝ) * mollifierRightCredit L z.re := by
      refine Finset.sum_congr rfl fun z hz => ?_
      obtain ⟨hz_sh, hre_gt⟩ := Finset.mem_filter.mp hz
      obtain ⟨h0, h1, _, _, _⟩ := mem_stripFinsetPos.mp (Finset.mem_filter.mp hz_sh).1
      rw [xi_analyticOrderAt_eq_riemannZeta_of_mem_strip ⟨h0, h1⟩,
        mollifierRightCredit_eq_depthKernel_of_mem_Icc hre_gt.le h1.le]
    rw [hcongr_sum]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun w _ _ =>
      mul_nonneg (Nat.cast_nonneg _) (mollifierRightCredit_nonneg L w.re)
  linarith [hint_ineq, hshell_le]

/-! ## §5. Arbitrary-exponent Barban–Vehov line mean square across `[1/2, 1]` and pure shell-free `c < 1/4` collapse -/

/-- **Simultaneous two-length Barban–Vehov line mean square for arbitrary `0 < θ_Y < θ_X < 1/2`
and arbitrary exponential rate `0 < r < 2 * θ_Y` across ALL `σ₀ ∈ [1/2, 1]`:**
by pushing the right three-lines abscissa `σ_R` past `3 * θ_X / (2 * θ_Y - r) + 2`, the mollified
mean square on every vertical line `Re s = σ₀` (`1/2 ≤ σ₀ ≤ 1`) simultaneously obeys
`∫_{T₁}^{T₂} ‖ζ(σ₀ + it) Ψ_{X, Y}(σ₀ + it)‖² dt ≤ (T₂ - T₁)(1 + A₀ e^{-r(σ₀ - 1/2) log S}) + 120 S^{θ_X + 1/2}`. -/
private theorem rpow_neg_interp_arbitrary_le {Z S θ θ_Y θ_X r σR u : ℝ}
    (hS : 1 < S) (hθY_le : θ_Y ≤ θ) (hθ_le : θ ≤ θ_X) (hr_lt : r < 2 * θ_Y)
    (hσR_40 : 40 ≤ σR) (hσR_rate : 3 * θ_X / (2 * θ_Y - r) + 2 ≤ σR)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2) (hZ : S ^ θ / 2 ≤ Z) (hZ1 : 1 ≤ S ^ θ / 2) :
    Z ^ ((4 - 2 * σR) * (u / (σR - 1 / 2))) ≤ 2 * Real.exp (-(r * u * Real.log S)) := by
  have hL : 0 < Real.log S := Real.log_pos hS
  have hS0 : 0 < S := by linarith
  have hden : 0 < σR - 1 / 2 := by linarith
  set lam : ℝ := u / (σR - 1 / 2)
  have hlam0 : 0 ≤ lam := div_nonneg hu0 hden.le
  set q : ℝ := (2 * σR - 4) * lam
  have hq0 : 0 ≤ q := mul_nonneg (by linarith) hlam0
  have hq1 : q ≤ 1 := by
    dsimp [q, lam]
    rw [mul_div_assoc', div_le_one hden]
    nlinarith
  have hZ0 : 0 < S ^ θ / 2 := by linarith
  have hexp_eq : (4 - 2 * σR) * lam = -q := by dsimp [q]; ring
  rw [hexp_eq]
  refine (Real.rpow_le_rpow_of_nonpos hZ0 hZ (by linarith)).trans ?_
  rw [Real.div_rpow (Real.rpow_nonneg hS0.le _) (by norm_num), ← Real.rpow_mul hS0.le,
    div_eq_mul_inv]
  have h2 : ((2 : ℝ) ^ (-q))⁻¹ ≤ 2 := by
    rw [← Real.rpow_neg (by norm_num), neg_neg]
    calc (2 : ℝ) ^ q ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hq1
      _ = 2 := Real.rpow_one 2
  have hgap_pos : 0 < 2 * θ_Y - r := by linarith
  have h3θ : 3 * θ ≤ (2 * θ_Y - r) * (σR - 1 / 2) := by
    have h1 : 3 * θ_X ≤ (2 * θ_Y - r) * (σR - 2) := by
      have hm := (div_le_iff₀ hgap_pos).mp (by linarith [hσR_rate] : 3 * θ_X / (2 * θ_Y - r) ≤ σR - 2)
      linarith
    nlinarith
  have hrate_ineq : r * (σR - 1 / 2) ≤ θ * (2 * σR - 4) := by
    have hid : θ * (2 * σR - 4) = 2 * θ * (σR - 1 / 2) - 3 * θ := by ring
    nlinarith
  have hSexp : S ^ (θ * -q) ≤ Real.exp (-(r * u * Real.log S)) := by
    rw [Real.rpow_def_of_pos hS0]
    refine Real.exp_le_exp.mpr ?_
    have hmul_u : r * u ≤ θ * q := by
      dsimp [q, lam]
      rw [show θ * ((2 * σR - 4) * (u / (σR - 1 / 2))) =
        (θ * (2 * σR - 4) * u) / (σR - 1 / 2) by ring, le_div_iff₀ hden]
      nlinarith only [hrate_ineq, hu0]
    nlinarith only [hmul_u, hL]
  have he : 0 ≤ S ^ (θ * -q) := Real.rpow_nonneg hS0.le _
  nlinarith [mul_le_mul hSexp h2 (inv_nonneg.mpr (Real.rpow_nonneg (by norm_num) _))
    (Real.exp_pos _).le]

private theorem hbMollifiedTail_block_arbitrary_rate_le
    {N : ℕ} {S θ θ_Y θ_X r σR H CW CL T₁ T₂ σ₀ : ℝ}
    (hS1 : 1 < S) (hN2 : 2 ≤ N) (hθlo : θ_Y ≤ θ) (hθhi : θ ≤ θ_X) (hr : r < 2 * θ_Y)
    (hσR_40 : 40 ≤ σR) (hσR_rate : 3 * θ_X / (2 * θ_Y - r) + 2 ≤ σR)
    (hH_σR : σR ≤ H) (hCW : 0 ≤ CW) (hCL : 0 < CL)
    (hNlo : S ^ θ / 2 ≤ (N : ℝ)) (hN1 : 1 ≤ S ^ θ / 2)
    (hT₁_1 : 1 ≤ T₁) (hT12 : T₁ ≤ T₂) (h2H_le : 2 * H ≤ T₂ - T₁)
    (hσ₀ : σ₀ ∈ Set.Icc (1 / 2 : ℝ) 1)
    (hWN : ∀ z : ℂ, 1 / 4 ≤ z.re → z.re ≤ 3 → ‖nearLineField N z‖ ≤ CW * N * (1 + |z.im|))
    (hleftN : ∀ τ : ℝ, T₁ + H ≤ τ → τ < T₂ + H → ∀ y : ℝ, ∫ t in (τ - H)..(τ + H),
      ‖nearLineWindowField N H τ (((1 / 2 : ℝ) : ℂ) + ((y + t : ℝ) : ℂ) * I)‖ ^ 2 ≤ CL * H) :
    (∫ t in T₁..T₂, ‖hbMollifiedTail N ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤
      (T₂ - T₁) * (4 * Real.exp 2 * (CL + 8 * Real.exp 2) *
        Real.exp (-(r * (σ₀ - 1 / 2) * Real.log S))) := by
  have hT₁_pos : 0 < T₁ := by linarith only [hT₁_1]
  have hH0 : 0 < H := by linarith only [hσR_40, hH_σR]
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hu0 : 0 ≤ σ₀ - 1 / 2 := sub_nonneg.mpr hσ₀.1
  have hu1 : σ₀ - 1 / 2 ≤ 1 / 2 := by linarith only [hσ₀.2]
  set W_win : ℝ := 4 * Real.exp 2 * (CL + 8 * Real.exp 2) * H *
    Real.exp (-(r * (σ₀ - 1 / 2) * Real.log S))
  have hW0 : 0 ≤ W_win := by dsimp [W_win]; positivity
  have hblock := integral_hbMollifiedTail_block_criticalGate_le (N := N) (σ₀ := σ₀)
    hH0 hT₁_pos hT12 hW0 fun τ h1 h2 => by
      have h3 := integral_hbMollifiedTail_window_le_farRight hN2 (σR := σR) (σL := 1 / 2)
        (σ₀ := σ₀) (SL := CL * H) (by linarith only [hσR_40]) hH_σR hCW hWN (by norm_num)
        hσ₀.1 hσ₀.1 hσ₀.2 (by linarith only [hT₁_1, h1]) (by positivity) (hleftN τ h1 h2)
      refine h3.trans ?_
      set lam : ℝ := (σ₀ - 1 / 2) / (σR - 1 / 2)
      have hlam0 : 0 ≤ lam := div_nonneg hu0 (by linarith only [hσR_40])
      have hlam1 : lam ≤ 1 :=
        (div_le_one (by linarith only [hσR_40])).mpr (by linarith only [hσ₀.2, hσR_40])
      have hy : 0 < (N : ℝ) ^ (4 - 2 * σR) := Real.rpow_pos_of_pos hN0 _
      have hinterp := rpow_mul_window_interp_le (A := CL) (B := 8 * Real.exp 2) (x := H)
        (y := (N : ℝ) ^ (4 - 2 * σR)) hCL (by positivity) hH0 hy hlam0 hlam1
      have hrw : ((N : ℝ) ^ (4 - 2 * σR)) ^ lam = (N : ℝ) ^ ((4 - 2 * σR) * lam) :=
        (Real.rpow_mul hN0.le _ _).symm
      have hdec := rpow_neg_interp_arbitrary_le hS1 hθlo hθhi hr hσR_40 hσR_rate hu0 hu1 hNlo hN1
      calc 2 * Real.exp 2 * ((CL * H) ^ (1 - lam) *
            (8 * Real.exp 2 * H * (N : ℝ) ^ (4 - 2 * σR)) ^ lam)
          ≤ 2 * Real.exp 2 * ((CL + 8 * Real.exp 2) * H * ((N : ℝ) ^ (4 - 2 * σR)) ^ lam) :=
            mul_le_mul_of_nonneg_left hinterp (by positivity)
        _ = 2 * Real.exp 2 * ((CL + 8 * Real.exp 2) * H * (N : ℝ) ^ ((4 - 2 * σR) * lam)) := by
            rw [hrw]
        _ ≤ 2 * Real.exp 2 * ((CL + 8 * Real.exp 2) * H *
              (2 * Real.exp (-(r * (σ₀ - 1 / 2) * Real.log S)))) := by gcongr
        _ = W_win := by dsimp [W_win]; ring
  have hratio : (T₂ - T₁) / (2 * H) + 1 ≤ (T₂ - T₁) / H := by
    rw [div_add_one (by positivity), div_le_div_iff₀ (by positivity) hH0]
    nlinarith only [h2H_le, hH0]
  calc (∫ t in T₁..T₂, ‖hbMollifiedTail N ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2)
      ≤ ((T₂ - T₁) / (2 * H) + 1) * W_win := hblock
    _ ≤ (T₂ - T₁) / H * W_win := mul_le_mul_of_nonneg_right hratio hW0
    _ = (T₂ - T₁) * (4 * Real.exp 2 * (CL + 8 * Real.exp 2) *
          Real.exp (-(r * (σ₀ - 1 / 2) * Real.log S))) := by dsimp [W_win]; field_simp

theorem exists_twoLength_mollified_meanSquare_arbitrary_exponents
    {θ_Y θ_X r : ℝ} (hθY : 0 < θ_Y) (hYX_exp : θ_Y < θ_X) (hθX : θ_X < 1 / 2)
    (_hr0 : 0 < r) (hr : r < 2 * θ_Y) :
    ∃ A₀ : ℝ, 0 < A₀ ∧ ∀ᶠ S : ℝ in atTop,
      ∃ T₁ ∈ Ioo (2 * S / 3) (2 * S / 3 + 1), ∃ T₂ ∈ Ioo (4 * S / 3 - 1) (4 * S / 3),
        3 ≤ VerticalAP.molLen θ_Y S ∧
        VerticalAP.molLen θ_Y S < VerticalAP.molLen θ_X S ∧
        (VerticalAP.molLen θ_X S : ℝ) ≤ S ^ θ_X ∧
        (∀ x ∈ Set.Icc (1 / 4 : ℝ) (15 / 2),
          riemannZeta ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0 ∧
            edPoly (twoLengthCoeff (VerticalAP.molLen θ_X S) (VerticalAP.molLen θ_Y S))
              (Finset.Icc 1 (VerticalAP.molLen θ_X S)) ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) ∧
        (∀ x ∈ Set.Icc (1 / 4 : ℝ) (15 / 2),
          riemannZeta ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0 ∧
            edPoly (twoLengthCoeff (VerticalAP.molLen θ_X S) (VerticalAP.molLen θ_Y S))
              (Finset.Icc 1 (VerticalAP.molLen θ_X S)) ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) ∧
        ∀ σ₀ ∈ Set.Icc (1 / 2 : ℝ) 1,
          (∫ t in T₁..T₂,
            ‖riemannZeta ((σ₀ : ℂ) + (t : ℂ) * I) *
              edPoly (twoLengthCoeff (VerticalAP.molLen θ_X S) (VerticalAP.molLen θ_Y S))
                (Finset.Icc 1 (VerticalAP.molLen θ_X S)) ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤
            (T₂ - T₁) * (1 + A₀ * Real.exp (-(r * (σ₀ - 1 / 2) * Real.log S))) +
              120 * S ^ (θ_X + 1 / 2) := by
  have hθX_pos : 0 < θ_X := hθY.trans hYX_exp
  set η : ℝ := min ((1 / 2 - θ_X) / 2) (1 / 50)
  have hη_pos : 0 < η := lt_min (by linarith) (by norm_num)
  have hη_le50 : η ≤ 1 / 50 := min_le_right _ _
  have hθX_η : θ_X + η < 1 / 2 := by
    have : η ≤ (1 / 2 - θ_X) / 2 := min_le_left _ _
    linarith
  have hθY_η : θ_Y + η < 1 / 2 := by linarith
  set σR : ℝ := max 40 (3 * θ_X / (2 * θ_Y - r) + 2)
  have hσR_40 : 40 ≤ σR := le_max_left _ _
  have hσR_rate : 3 * θ_X / (2 * θ_Y - r) + 2 ≤ σR := le_max_right _ _
  set g₀ : ℝ := (θ_X - θ_Y) / 2
  have hg₀_pos : 0 < g₀ := by dsimp [g₀]; linarith
  set K_gap : ℝ := 1 / (2 * g₀)
  have hK_gap_pos : 0 < K_gap := by dsimp [K_gap]; positivity
  obtain ⟨CgX, hCgX, hgX⟩ := exists_eventually_criticalGate hθX_pos hη_pos hθX_η
  obtain ⟨CgY, hCgY, hgY⟩ := exists_eventually_criticalGate hθY hη_pos hθY_η
  obtain ⟨CW, hCW, hW⟩ := exists_norm_nearLineField_le
  obtain ⟨CM, hCM⟩ := exists_sum_vonMangoldt_sq_div_le
  set CLX : ℝ := criticalGateLeftConst CgX CM
  set CLY : ℝ := criticalGateLeftConst CgY CM
  have hCLX : 0 < CLX := criticalGateLeftConst_pos hCgX
  have hCLY : 0 < CLY := criticalGateLeftConst_pos hCgY
  set A₀ : ℝ := 8 / g₀ ^ 2 +
    4 * K_gap ^ 2 * (4 * Real.exp 2 * (CLX + 8 * Real.exp 2) +
      4 * Real.exp 2 * (CLY + 8 * Real.exp 2)) + 1
  have hA₀_pos : 0 < A₀ := by dsimp [A₀]; positivity
  refine ⟨A₀, hA₀_pos, ?_⟩
  have hev_lenY := eventually_const_mul_rpow_le_rpow (C := 6) (α := 0) (β := θ_Y) hθY
  have hev_lenYX := eventually_const_mul_rpow_le_rpow (C := 3) (α := θ_Y) (β := θ_X) hYX_exp
  have hev_H_σR := eventually_const_mul_rpow_le_rpow (C := 2 * σR) (α := 0) (β := 1 - η)
    (by linarith)
  have hev_H_S16 := eventually_const_mul_rpow_le_rpow (C := 8) (α := 1 - η) (β := 1) (by linarith)
  have hev_H_95 := eventually_const_mul_rpow_le_rpow (C := 8) (α := 95 / 100) (β := 1 - η)
    (by linarith)
  have hev_MVT := eventually_const_mul_one_add_log_le_rpow (C := 16) (ε := 1 - η - θ_X)
    (by linarith)
  have hev_key := eventually_mul_rpow_mul_exp_neg_rpow_le_one (C := 36 * CW ^ 2)
    (k := 2 * θ_X + 2 + 2 * (1 - η)) (c := 1 / 64) (ε := 2 * η) (by norm_num) (by positivity)
  have hev_log := Real.tendsto_log_atTop.eventually
    (eventually_ge_atTop (max (|CM| + 2) (Real.log 2 / g₀ + 1)))
  filter_upwards [hgX, hgY, hev_lenY, hev_lenYX, hev_H_σR, hev_H_S16, hev_H_95, hev_MVT,
    hev_key, hev_log, eventually_ge_atTop (60 : ℝ)]
    with S hgXS hgYS h6Y h3YX hHσR hHS16 hH95 hMVT_S hkey_S hlogS hS60
  clear hgX hgY hev_lenY hev_lenYX hev_H_σR hev_H_S16 hev_H_95 hev_MVT hev_key hev_log
  have hS1 : 1 < S := by linarith only [hS60]
  have hS0 : 0 < S := by linarith only [hS60]
  have hLS_pos : 0 < Real.log S := Real.log_pos hS1
  rw [Real.rpow_zero, mul_one] at h6Y hHσR
  rw [Real.rpow_one] at hHS16
  set X : ℕ := VerticalAP.molLen θ_X S
  set Y : ℕ := VerticalAP.molLen θ_Y S
  set H : ℝ := S ^ (1 - η) / 2
  have hY0 : 0 < S ^ θ_Y := Real.rpow_pos_of_pos hS0 _
  have hX6 : 6 ≤ S ^ θ_X := by nlinarith only [h6Y, h3YX]
  have hXlo : S ^ θ_X / 2 ≤ (X : ℝ) := half_rpow_le_molLen (by linarith only [hX6])
  have hYlo : S ^ θ_Y / 2 ≤ (Y : ℝ) := half_rpow_le_molLen (by linarith only [h6Y])
  have hXhi : (X : ℝ) ≤ S ^ θ_X := VerticalAP.molLen_le hS0.le
  have hYhi : (Y : ℝ) ≤ S ^ θ_Y := VerticalAP.molLen_le hS0.le
  have hY1_pow : 1 ≤ S ^ θ_Y / 2 := by linarith only [h6Y]
  have hX1_pow : 1 ≤ S ^ θ_X / 2 := by linarith only [hX6]
  have hY3_r : (3 : ℝ) ≤ (Y : ℝ) := by linarith only [h6Y, hYlo]
  have hY3 : 3 ≤ Y := by exact_mod_cast hY3_r
  have hYX_r : (Y : ℝ) < (X : ℝ) := by nlinarith only [hY0, h3YX, hYhi, hXlo]
  have hYX : Y < X := by exact_mod_cast hYX_r
  have hX3 : 3 ≤ X := by omega
  have hXpos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
  have hYpos : (0 : ℝ) < (Y : ℝ) := by exact_mod_cast (by omega : 0 < Y)
  have hlogX_hi : Real.log (X : ℝ) ≤ θ_X * Real.log S := by
    rw [← Real.log_rpow hS0]
    exact Real.log_le_log hXpos hXhi
  have hlogX_lo : θ_X * Real.log S - Real.log 2 ≤ Real.log (X : ℝ) := by
    rw [← Real.log_rpow hS0, ← Real.log_div (by positivity) (by norm_num)]
    exact Real.log_le_log (by positivity) hXlo
  have hlogY_hi : Real.log (Y : ℝ) ≤ θ_Y * Real.log S := by
    rw [← Real.log_rpow hS0]
    exact Real.log_le_log hYpos hYhi
  have hlogY_1 : 1 ≤ Real.log (Y : ℝ) := by
    have he : Real.exp 1 ≤ 3 := by linarith only [Real.exp_one_lt_d9]
    rw [Real.le_log_iff_exp_le hYpos]; linarith only [he, hY3_r]
  have hlogX_1 : 1 ≤ Real.log (X : ℝ) := hlogY_1.trans (Real.log_le_log hYpos hYX_r.le)
  have hCM_le : |CM| + 2 ≤ Real.log S := (le_max_left _ _).trans hlogS
  have hCMabs : |CM| ≤ Real.log S := by linarith only [hCM_le]
  have hgap_log : Real.log 2 / g₀ + 1 ≤ Real.log S := (le_max_right _ _).trans hlogS
  have hlog2_le : Real.log 2 ≤ g₀ * Real.log S := by
    have hm := (div_le_iff₀ hg₀_pos).mp (by linarith only [hgap_log] : Real.log 2 / g₀ ≤ Real.log S)
    linarith only [hm]
  have hgap : g₀ * Real.log S ≤ Real.log (X : ℝ) - Real.log (Y : ℝ) := by
    have hdiff : θ_X * Real.log S - θ_Y * Real.log S = 2 * (g₀ * Real.log S) := by dsimp [g₀]; ring
    linarith only [hlogX_lo, hlogY_hi, hlog2_le, hdiff]
  have hH_σR : σR ≤ H := by dsimp [H]; linarith only [hHσR]
  have hH_40 : 40 ≤ H := hσR_40.trans hH_σR
  have hHS : H ≤ S / 16 := by dsimp [H]; linarith only [hHS16]
  have hα95 : 2 * (2 * S) ^ ((95 : ℝ) / 100) ≤ H := by
    rw [Real.mul_rpow (by norm_num) hS0.le]
    have h2 : (2 : ℝ) ^ ((95 : ℝ) / 100) ≤ 2 := by
      calc (2 : ℝ) ^ ((95 : ℝ) / 100) ≤ 2 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := Real.rpow_one 2
    have hp : 0 ≤ S ^ ((95 : ℝ) / 100) := Real.rpow_nonneg hS0.le _
    dsimp [H]; nlinarith only [h2, hp, hH95]
  have hMVT_fn : ∀ N : ℝ, 0 < N → N ≤ S ^ θ_X → 8 * N * (1 + Real.log N) ≤ H := by
    intro N hN hNS
    have hNS' : N ≤ S := hNS.trans (Real.rpow_le_self_of_one_le hS1.le (by linarith only [hθX]))
    have hlogN : Real.log N ≤ Real.log S := Real.log_le_log hN hNS'
    have hsplit : S ^ (1 - η) = S ^ θ_X * S ^ (1 - η - θ_X) := by
      rw [← Real.rpow_add hS0]; ring_nf
    have h1 : 8 * N * (1 + Real.log N) ≤ 8 * S ^ θ_X * (1 + Real.log S) :=
      (mul_le_mul_of_nonneg_left (by linarith only [hlogN]) (by linarith only [hN])).trans
        (mul_le_mul_of_nonneg_right (by linarith only [hNS])
          (by linarith only [Real.log_nonneg hS1.le]))
    dsimp [H]; rw [hsplit]
    have hp : 0 ≤ S ^ θ_X := Real.rpow_nonneg hS0.le _
    nlinarith only [h1, hp, hMVT_S]
  have hkey_fn : ∀ N : ℝ, 0 ≤ N → N ≤ S ^ θ_X →
      16 * CW ^ 2 * N ^ 2 * (1 + 2 * S) ^ 2 * H ^ 2 *
        Real.exp (-((S / 16) ^ 2 / H ^ 2)) ≤ 1 := by
    intro N hN hNS
    have hH2 : H ^ 2 = S ^ (2 * (1 - η)) / 4 := by
      dsimp [H]; rw [div_pow, ← Real.rpow_natCast, ← Real.rpow_mul hS0.le, mul_comm]; norm_num
    have hratio : (S / 16) ^ 2 / H ^ 2 = 1 / 64 * S ^ (2 * η) := by
      rw [hH2, div_pow, show (S : ℝ) ^ 2 = S ^ (2 : ℝ) by rw [← Real.rpow_natCast]; norm_num]
      have h2 : S ^ (2 : ℝ) = S ^ (2 * (1 - η)) * S ^ (2 * η) := by
        rw [← Real.rpow_add hS0]; ring_nf
      have hp : 0 < S ^ (2 * (1 - η)) := Real.rpow_pos_of_pos hS0 _
      rw [h2]; field_simp; ring
    rw [hratio]
    have hN2 : N ^ 2 ≤ S ^ (2 * θ_X) := by
      calc N ^ 2 = N ^ (2 : ℝ) := by rw [← Real.rpow_natCast]; norm_num
        _ ≤ (S ^ θ_X) ^ (2 : ℝ) := Real.rpow_le_rpow hN hNS (by norm_num)
        _ = S ^ (2 * θ_X) := by rw [← Real.rpow_mul hS0.le, mul_comm]
    have h1 : (1 + 2 * S) ^ 2 ≤ 9 * S ^ (2 : ℝ) := by
      rw [show S ^ (2 : ℝ) = S ^ (2 : ℕ) by rw [← Real.rpow_natCast]; norm_num]
      nlinarith only [hS1]
    have hprod : S ^ (2 * θ_X) * S ^ (2 : ℝ) * S ^ (2 * (1 - η)) =
        S ^ (2 * θ_X + 2 + 2 * (1 - η)) := by
      rw [← Real.rpow_add hS0, ← Real.rpow_add hS0]
    have hpoly : 16 * CW ^ 2 * N ^ 2 * (1 + 2 * S) ^ 2 * H ^ 2 ≤
        36 * CW ^ 2 * S ^ (2 * θ_X + 2 + 2 * (1 - η)) := by
      rw [hH2]
      calc 16 * CW ^ 2 * N ^ 2 * (1 + 2 * S) ^ 2 * (S ^ (2 * (1 - η)) / 4)
          ≤ 16 * CW ^ 2 * S ^ (2 * θ_X) * (9 * S ^ (2 : ℝ)) * (S ^ (2 * (1 - η)) / 4) := by
            gcongr
        _ = 36 * CW ^ 2 * (S ^ (2 * θ_X) * S ^ (2 : ℝ) * S ^ (2 * (1 - η))) := by ring
        _ = 36 * CW ^ 2 * S ^ (2 * θ_X + 2 + 2 * (1 - η)) := by rw [hprod]
    exact (mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le).trans hkey_S
  have h2H : 2 * H = S ^ (1 - η) := by dsimp [H]; ring
  have hgateX : ∀ α : ℝ, S / 2 ≤ α → α ≤ 2 * S →
      ∫ u in α..(α + 2 * H), ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I) *
        edPoly (hbCoeff X) (Finset.Icc 1 X) (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I)‖ ^ 2 ≤
          CgX * (2 * H) := fun α h1 h2 => by rw [h2H]; exact hgXS α h1 h2
  have hgateY : ∀ α : ℝ, S / 2 ≤ α → α ≤ 2 * S →
      ∫ u in α..(α + 2 * H), ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I) *
        edPoly (hbCoeff Y) (Finset.Icc 1 Y) (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I)‖ ^ 2 ≤
          CgY * (2 * H) := fun α h1 h2 => by rw [h2H]; exact hgYS α h1 h2
  obtain ⟨T₁, hT₁, T₂, hT₂, hadm1, hadm2⟩ := exists_admissible_heights_of_mollifier
    (b := twoLengthCoeff X Y) (N := X) (by omega) (twoLengthCoeff_one (by omega) hYX)
    (fun n hn => norm_twoLengthCoeff_le (by omega) hYX hn) (A₁ := 2 * S / 3)
    (B₁ := 2 * S / 3 + 1) (A₂ := 4 * S / 3 - 1) (B₂ := 4 * S / 3) (by linarith only [hS60])
    (by linarith only [hS60]) (by linarith only [hS60]) (by linarith only [hS60])
  refine ⟨T₁, hT₁, T₂, hT₂, hY3, hYX, hXhi, hadm1, hadm2, fun σ₀ hσ₀ => ?_⟩
  have hT12 : T₁ ≤ T₂ := by linarith only [hT₁.2, hT₂.1, hS60]
  have h2H_le : 2 * H ≤ T₂ - T₁ := by linarith only [hT₁.2, hT₂.1, hHS, hS60]
  have hlX := criticalGate_leftWindows (N := X) hX3 hH_40 hHS hCgX hCW.le (hW X (by omega))
    hgateX hα95 (hMVT_fn X hXpos hXhi) hlogX_1 (hCM X (by omega)) (hkey_fn X hXpos.le hXhi)
    hT₁.1 hT₂.2
  have hlY := criticalGate_leftWindows (N := Y) hY3 hH_40 hHS hCgY hCW.le (hW Y (by omega))
    hgateY hα95 (hMVT_fn Y hYpos (hYX_r.le.trans hXhi)) hlogY_1 (hCM Y (by omega))
    (hkey_fn Y hYpos.le (hYX_r.le.trans hXhi)) hT₁.1 hT₂.2
  set u : ℝ := σ₀ - 1 / 2
  have hu0 : 0 ≤ u := sub_nonneg.mpr hσ₀.1
  have hu1 : u ≤ 1 / 2 := by dsimp [u]; linarith only [hσ₀.2]
  have hT₁_1 : 1 ≤ T₁ := by linarith only [hT₁.1, hS60]
  have hT₁_pos : 0 < T₁ := by linarith only [hT₁_1]
  have hfX := hbMollifiedTail_block_arbitrary_rate_le hS1 (by omega : 2 ≤ X) hYX_exp.le le_rfl
    hr hσR_40 hσR_rate hH_σR hCW.le hCLX hXlo hX1_pow hT₁_1 hT12 h2H_le hσ₀
    (hW X (by omega)) hlX
  have hfY := hbMollifiedTail_block_arbitrary_rate_le hS1 (by omega : 2 ≤ Y) le_rfl hYX_exp.le
    hr hσR_40 hσR_rate hH_σR hCW.le hCLY hYlo hY1_pow hT₁_1 hT12 h2H_le hσ₀
    (hW Y (by omega)) hlY
  have hhead : (∫ τ in T₁..T₂, ‖edPoly (twoLengthHeadCoeff X Y) (Finset.Icc 1 X)
        ((σ₀ : ℂ) + (τ : ℂ) * I)‖ ^ 2) ≤
      (T₂ - T₁) * ((4 / g₀ ^ 2) * Real.exp (-(r * u * Real.log S))) := by
    have hh := integral_normSq_twoLengthHead_le (by omega : 1 ≤ Y) hYX (δ := u) hu0
      (hCM X (by omega)) hT12
    have hpt : ∀ τ : ℝ, displacedLinePt (-u) τ = ((σ₀ : ℂ) + (τ : ℂ) * I) := by
      intro τ; unfold displacedLinePt; dsimp [u]; congr 2; ring
    simp only [hpt] at hh
    refine hh.trans ?_
    have hYpow : (Y : ℝ) ^ (-(2 * u)) ≤ 2 * Real.exp (-(r * u * Real.log S)) := by
      have hZ0 : 0 < S ^ θ_Y / 2 := by linarith only [hY0]
      refine (Real.rpow_le_rpow_of_nonpos hZ0 hYlo (by linarith only [hu0])).trans ?_
      rw [Real.div_rpow (Real.rpow_nonneg hS0.le _) (by norm_num), ← Real.rpow_mul hS0.le,
        div_eq_mul_inv]
      have h2 : ((2 : ℝ) ^ (-(2 * u)))⁻¹ ≤ 2 := by
        rw [← Real.rpow_neg (by norm_num), neg_neg]
        calc (2 : ℝ) ^ (2 * u) ≤ 2 ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hu1])
          _ = 2 := Real.rpow_one 2
      have hSexp : S ^ (θ_Y * -(2 * u)) ≤ Real.exp (-(r * u * Real.log S)) := by
        rw [Real.rpow_def_of_pos hS0]
        have hru : r * u ≤ 2 * θ_Y * u := mul_le_mul_of_nonneg_right hr.le hu0
        exact Real.exp_le_exp.mpr (by nlinarith only [hru, hLS_pos])
      have he : 0 ≤ S ^ (θ_Y * -(2 * u)) := Real.rpow_nonneg hS0.le _
      have hm := mul_le_mul hSexp h2 (inv_nonneg.mpr (Real.rpow_nonneg (by norm_num) _))
        (Real.exp_pos _).le
      linarith only [hm]
    have hratio : Real.log (X : ℝ) * (Real.log (X : ℝ) + CM) /
        (Real.log (X : ℝ) - Real.log (Y : ℝ)) ^ 2 ≤ 1 / g₀ ^ 2 := by
      have hgap0 : 0 < Real.log (X : ℝ) - Real.log (Y : ℝ) := by
        nlinarith only [hgap, hg₀_pos, hLS_pos]
      rw [div_le_iff₀ (by positivity)]
      have hnum : Real.log (X : ℝ) * (Real.log (X : ℝ) + CM) ≤
          (1 / 2 * Real.log S) * (2 * Real.log S) := by
        have hlX_half : Real.log (X : ℝ) ≤ 1 / 2 * Real.log S := by
          nlinarith only [hlogX_hi, hθX, hLS_pos]
        have hlX_CM : Real.log (X : ℝ) + CM ≤ 2 * Real.log S := by
          linarith only [le_abs_self CM, hCMabs, hlX_half, hLS_pos]
        rcases le_or_gt 0 (Real.log (X : ℝ) + CM) with hc | hc
        · exact mul_le_mul hlX_half hlX_CM hc (by positivity)
        · have hlX0 : 0 ≤ Real.log (X : ℝ) := by linarith only [hlogX_1]
          nlinarith only [hc, hlX0, hLS_pos]
      have hden2 : (g₀ * Real.log S) ^ 2 ≤ (Real.log (X : ℝ) - Real.log (Y : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hgap 2
      have hid : 1 / g₀ ^ 2 * (g₀ * Real.log S) ^ 2 = (1 / 2 * Real.log S) * (2 * Real.log S) := by
        field_simp [hg₀_pos.ne']
      have hmul := mul_le_mul_of_nonneg_left hden2 (by positivity : 0 ≤ 1 / g₀ ^ 2)
      linarith only [hnum, hid, hmul]
    have hMVT_X : 8 * (X : ℝ) * (1 + Real.log (X : ℝ)) ≤ T₂ - T₁ := by
      have hmvt := hMVT_fn X hXpos hXhi
      have hH0 : 0 < H := by linarith only [hH_40]
      linarith only [hmvt, h2H_le, hH0]
    set q : ℝ := Real.log (X : ℝ) * (Real.log (X : ℝ) + CM) /
      (Real.log (X : ℝ) - Real.log (Y : ℝ)) ^ 2
    have hrw : (T₂ - T₁ + 8 * (X : ℝ) * (1 + Real.log (X : ℝ))) *
        ((Y : ℝ) ^ (-(2 * u)) * (Real.log (X : ℝ) * (Real.log (X : ℝ) + CM)) /
          (Real.log (X : ℝ) - Real.log (Y : ℝ)) ^ 2) =
        (T₂ - T₁ + 8 * (X : ℝ) * (1 + Real.log (X : ℝ))) * ((Y : ℝ) ^ (-(2 * u)) * q) := by
      dsimp [q]; ring
    rw [hrw]
    have hYp0 : 0 ≤ (Y : ℝ) ^ (-(2 * u)) := Real.rpow_nonneg hYpos.le _
    rcases le_or_gt 0 q with hq0 | hq0
    · calc (T₂ - T₁ + 8 * (X : ℝ) * (1 + Real.log (X : ℝ))) * ((Y : ℝ) ^ (-(2 * u)) * q)
          ≤ (2 * (T₂ - T₁)) * ((2 * Real.exp (-(r * u * Real.log S))) * (1 / g₀ ^ 2)) :=
            mul_le_mul (by linarith only [hMVT_X]) (mul_le_mul hYpow hratio hq0 (by positivity))
              (mul_nonneg hYp0 hq0) (by linarith only [hT12])
        _ = (T₂ - T₁) * ((4 / g₀ ^ 2) * Real.exp (-(r * u * Real.log S))) := by ring
    · have hnonpos : (T₂ - T₁ + 8 * (X : ℝ) * (1 + Real.log (X : ℝ))) *
          ((Y : ℝ) ^ (-(2 * u)) * q) ≤ 0 := by
        have hterm0 : 0 ≤ 8 * (X : ℝ) * (1 + Real.log (X : ℝ)) := by positivity
        exact mul_nonpos_of_nonneg_of_nonpos (by linarith only [hT12, hterm0])
          (mul_nonpos_of_nonneg_of_nonpos hYp0 hq0.le)
      have hnn : 0 ≤ (T₂ - T₁) * ((4 / g₀ ^ 2) * Real.exp (-(r * u * Real.log S))) := by
        positivity
      linarith only [hnonpos, hnn]
  have hfirst := norm_integral_zeta_mul_edPoly_sub_one_block_le (c := twoLengthCoeff X Y)
    (by omega : 1 ≤ X) (twoLengthCoeff_one (by omega) hYX)
    (fun n hn => norm_twoLengthCoeff_le (by omega) hYX hn) (σ := σ₀) (T := 2 * S / 3)
    hσ₀.1 (by linarith only [hσ₀.2]) (by linarith only [hS60]) hT₁.1.le
    (by linarith only [hT₁.2, hS60]) (by linarith only [hT₂.1, hS60])
    (by linarith only [hT₂.2, hS60]) hT12
  have hcross : 2 * ‖∫ t in T₁..T₂, (riemannZeta ((σ₀ : ℂ) + (t : ℂ) * I) *
      edPoly (twoLengthCoeff X Y) (Finset.Icc 1 X) ((σ₀ : ℂ) + (t : ℂ) * I) - 1)‖ ≤
      120 * S ^ (θ_X + 1 / 2) := by
    have hsq : Real.sqrt (2 * S / 3) ≤ S ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow]; exact Real.sqrt_le_sqrt (by linarith only [hS0])
    have hadd : S ^ θ_X * S ^ (1 / 2 : ℝ) = S ^ (θ_X + 1 / 2) := (Real.rpow_add hS0 _ _).symm
    have hX_le : (X : ℝ) ≤ S ^ (θ_X + 1 / 2) :=
      hXhi.trans (Real.rpow_le_rpow_of_exponent_le hS1.le (by linarith only))
    have h1_le : 1 ≤ S ^ (θ_X + 1 / 2) := Real.one_le_rpow hS1.le (by linarith only [hθX_pos])
    have hmul : (X : ℝ) * Real.sqrt (2 * S / 3) ≤ S ^ (θ_X + 1 / 2) := by
      rw [← hadd]
      exact mul_le_mul hXhi hsq (Real.sqrt_nonneg _) (Real.rpow_nonneg hS0.le _)
    linarith only [hfirst, hmul, hX_le, h1_le]
  have hs_mem : ∀ n ∈ Finset.Icc 1 X, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp hn).1
  have hwc : ContinuousOn (fun t : ℝ => riemannZeta ((σ₀ : ℂ) + (t : ℂ) * I) *
      edPoly (twoLengthCoeff X Y) (Finset.Icc 1 X) ((σ₀ : ℂ) + (t : ℂ) * I) - 1) (Icc T₁ T₂) := by
    intro t ht
    have hne : ((σ₀ : ℂ) + (t : ℂ) * I) ≠ 1 := by
      intro h; have := congrArg Complex.im h; simp at this; linarith only [this, ht.1, hT₁_pos]
    exact (((ContinuousAt.comp (g := riemannZeta) (f := fun t : ℝ => (σ₀ : ℂ) + (t : ℂ) * I)
      (differentiableAt_riemannZeta hne).continuousAt (cont_vert_pt σ₀).continuousAt).mul
      (ContinuousAt.comp (g := edPoly (twoLengthCoeff X Y) (Finset.Icc 1 X))
        (f := fun t : ℝ => (σ₀ : ℂ) + (t : ℂ) * I)
        (differentiable_edPoly _ hs_mem _).continuousAt (cont_vert_pt σ₀).continuousAt)).sub
          continuousAt_const).continuousWithinAt
  have hM1 := integral_normSq_one_add_le hT12 hwc
  simp only [add_sub_cancel] at hM1
  have hptw_sub : ∀ z : ℂ,
      ‖riemannZeta z * edPoly (twoLengthCoeff X Y) (Finset.Icc 1 X) z - 1‖ ^ 2 ≤
        2 * ‖edPoly (twoLengthHeadCoeff X Y) (Finset.Icc 1 X) z‖ ^ 2 +
          4 * K_gap ^ 2 * (‖hbMollifiedTail X z‖ ^ 2 + ‖hbMollifiedTail Y z‖ ^ 2) := by
    intro z
    have hgap0 : 0 < Real.log (X : ℝ) - Real.log (Y : ℝ) := by
      nlinarith only [hgap, hg₀_pos, hLS_pos]
    have hK : Real.log (X : ℝ) ≤ K_gap * (Real.log (X : ℝ) - Real.log (Y : ℝ)) := by
      have h1 : K_gap * (g₀ * Real.log S) = 1 / 2 * Real.log S := by
        dsimp [K_gap]; field_simp [hg₀_pos.ne']
      have h2 := mul_le_mul_of_nonneg_left hgap hK_gap_pos.le
      have hlX_half : Real.log (X : ℝ) ≤ 1 / 2 * Real.log S := by
        nlinarith only [hlogX_hi, hθX, hLS_pos]
      linarith only [h1, h2, hlX_half]
    have hK' : Real.log (Y : ℝ) ≤ K_gap * (Real.log (X : ℝ) - Real.log (Y : ℝ)) :=
      (Real.log_le_log hYpos hYX_r.le).trans hK
    rw [zeta_mul_twoLength_eq (by omega) hYX, add_sub_cancel_left]
    exact normSq_add_twoLength_le (by linarith only [hlogX_1]) (by linarith only [hlogY_1])
      hgap0 hK hK' _ _ _
  have hiP : IntervalIntegrable (fun t : ℝ => ‖edPoly (twoLengthHeadCoeff X Y) (Finset.Icc 1 X)
      ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2) volume T₁ T₂ :=
    ((((differentiable_edPoly _ hs_mem).continuous.comp (cont_vert_pt σ₀)).continuousOn).norm.pow
      2).intervalIntegrable_of_Icc hT12
  have hiX : IntervalIntegrable (fun t : ℝ => ‖hbMollifiedTail X ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2)
      volume T₁ T₂ :=
    ((continuousOn_hbMollifiedTail_line X σ₀ (T₂ := T₂) hT₁_pos).norm.pow
      2).intervalIntegrable_of_Icc hT12
  have hiY : IntervalIntegrable (fun t : ℝ => ‖hbMollifiedTail Y ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2)
      volume T₁ T₂ :=
    ((continuousOn_hbMollifiedTail_line Y σ₀ (T₂ := T₂) hT₁_pos).norm.pow
      2).intervalIntegrable_of_Icc hT12
  have hiw : IntervalIntegrable (fun t : ℝ => ‖riemannZeta ((σ₀ : ℂ) + (t : ℂ) * I) *
      edPoly (twoLengthCoeff X Y) (Finset.Icc 1 X) ((σ₀ : ℂ) + (t : ℂ) * I) - 1‖ ^ 2)
      volume T₁ T₂ := (hwc.norm.pow 2).intervalIntegrable_of_Icc hT12
  have hmono := intervalIntegral.integral_mono_on hT12 hiw
    ((hiP.const_mul 2).add ((hiX.add hiY).const_mul (4 * K_gap ^ 2)))
    fun t _ => hptw_sub _
  rw [intervalIntegral.integral_add (hiP.const_mul 2) ((hiX.add hiY).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add hiX hiY] at hmono
  have hcomb : 2 * (∫ t in T₁..T₂, ‖edPoly (twoLengthHeadCoeff X Y) (Finset.Icc 1 X)
        ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2) +
      4 * K_gap ^ 2 *
        ((∫ t in T₁..T₂, ‖hbMollifiedTail X ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2) +
          ∫ t in T₁..T₂, ‖hbMollifiedTail Y ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤
      (T₂ - T₁) * (A₀ * Real.exp (-(r * u * Real.log S))) := by
    dsimp [u] at hhead ⊢
    have hsum_le := add_le_add (mul_le_mul_of_nonneg_left hhead zero_le_two)
      (mul_le_mul_of_nonneg_left (add_le_add hfX hfY) (by positivity : 0 ≤ 4 * K_gap ^ 2))
    refine hsum_le.trans ?_
    have hnn : 0 ≤ (T₂ - T₁) * Real.exp (-(r * (σ₀ - 1 / 2) * Real.log S)) :=
      mul_nonneg (sub_nonneg.mpr hT12) (Real.exp_pos _).le
    have hid : (T₂ - T₁) * (A₀ * Real.exp (-(r * (σ₀ - 1 / 2) * Real.log S))) =
        2 * ((T₂ - T₁) * (4 / g₀ ^ 2 * Real.exp (-(r * (σ₀ - 1 / 2) * Real.log S)))) +
          4 * K_gap ^ 2 *
            ((T₂ - T₁) * (4 * Real.exp 2 * (CLX + 8 * Real.exp 2) *
                Real.exp (-(r * (σ₀ - 1 / 2) * Real.log S))) +
              (T₂ - T₁) * (4 * Real.exp 2 * (CLY + 8 * Real.exp 2) *
                Real.exp (-(r * (σ₀ - 1 / 2) * Real.log S)))) +
          (T₂ - T₁) * Real.exp (-(r * (σ₀ - 1 / 2) * Real.log S)) := by
      dsimp [A₀]; ring
    linarith only [hid, hnn]
  dsimp [u] at hcomb
  linarith only [hM1, hcross, hmono, hcomb]

private theorem abscissa_main_exp_integral_le
    {A₀ c δ_c V S L T₁ T₂ : ℝ}
    (hA₀ : 0 < A₀) (hc0 : 0 < c) (hδ_pos : 0 < δ_c) (hV_pos : 0 < V)
    (hLV_pos : 0 < Real.log V) (hLS_pos : 0 < Real.log S)
    (hLV_le_LS : Real.log V ≤ Real.log S) (hlen_pos : 0 < T₂ - T₁) (hlen_hi : T₂ - T₁ ≤ V)
    (hL_eq : L = c * Real.log V) :
    (∫ σ in (1 / 2)..1,
      4 * A₀ * L ^ 2 * (T₂ - T₁) * Real.exp (-(δ_c * Real.log S * (σ - 1 / 2)))) ≤
      (12 * A₀ * c ^ 2 / δ_c) * V * Real.log V := by
  have hderiv_exp : ∀ σ : ℝ,
      HasDerivAt (fun t : ℝ => -(1 / (δ_c * Real.log S)) *
        Real.exp (-(δ_c * Real.log S * (t - 1 / 2))))
        (Real.exp (-(δ_c * Real.log S * (σ - 1 / 2)))) σ := by
    intro σ
    have hlin : HasDerivAt (fun t : ℝ => -(δ_c * Real.log S * (t - 1 / 2)))
        (-(δ_c * Real.log S)) σ :=
      (((hasDerivAt_id σ).sub_const (1 / 2)).const_mul (δ_c * Real.log S)).neg.congr_deriv (by ring)
    have hexp := ((Real.hasDerivAt_exp _).comp σ hlin).const_mul (-(1 / (δ_c * Real.log S)))
    exact hexp.congr_deriv (by field_simp [hδ_pos.ne', hLS_pos.ne'])
  rw [intervalIntegral.integral_const_mul,
    integral_eq_sub_of_hasDerivAt (fun σ _ => hderiv_exp σ)
      ((by fun_prop : Continuous _).intervalIntegrable _ _)]
  simp only [sub_self, mul_zero, neg_zero, Real.exp_zero, mul_one]
  have hsub_le : -(1 / (δ_c * Real.log S)) * Real.exp (-(δ_c * Real.log S * (1 - 1 / 2))) -
      (-(1 / (δ_c * Real.log S))) ≤ 1 / (δ_c * Real.log S) := by
    have hpos_e : 0 ≤ (1 / (δ_c * Real.log S)) * Real.exp (-(δ_c * Real.log S * (1 - 1 / 2))) := by
      positivity
    linarith only [hpos_e]
  calc 4 * A₀ * L ^ 2 * (T₂ - T₁) *
        (-(1 / (δ_c * Real.log S)) * Real.exp (-(δ_c * Real.log S * (1 - 1 / 2))) -
          -(1 / (δ_c * Real.log S)))
      ≤ 4 * A₀ * L ^ 2 * (T₂ - T₁) * (1 / (δ_c * Real.log S)) :=
        mul_le_mul_of_nonneg_left hsub_le (by positivity)
    _ ≤ 4 * A₀ * (c * Real.log V) ^ 2 * V * (1 / (δ_c * Real.log V)) := by
        rw [hL_eq]
        refine mul_le_mul (mul_le_mul_of_nonneg_left hlen_hi (by positivity))
          (one_div_le_one_div_of_le (by positivity)
            (mul_le_mul_of_nonneg_left hLV_le_LS hδ_pos.le))
          (by positivity) (by positivity)
    _ = 4 * (A₀ * c ^ 2 * V * Real.log V / δ_c) := by
        field_simp [hδ_pos.ne', hLV_pos.ne']
    _ ≤ 12 * (A₀ * c ^ 2 * V * Real.log V / δ_c) := by
        have hpos_main : 0 ≤ A₀ * c ^ 2 * V * Real.log V / δ_c := by positivity
        linarith only [hpos_main]
    _ = (12 * A₀ * c ^ 2 / δ_c) * V * Real.log V := by ring

private theorem abscissa_cross_cosh_integral_le
    {c δ_c θ_X C K V S L : ℝ}
    (hc0 : 0 < c) (hδ_pos : 0 < δ_c) (hθX_pos : 0 < θ_X) (hC : 0 < C) (hK : 0 < K)
    (hV_pos : 0 < V) (hS1 : 1 < S) (hLV_ge1 : 1 ≤ Real.log V)
    (hL_nn : 0 ≤ L) (hL_le_cS : L ≤ c * Real.log S)
    (hS_eq : S = (3 / 2 : ℝ) * V)
    (hexp_id : c + (θ_X + 1 / 2 + δ_c / 4) + δ_c / 4 = 1 - δ_c / 2)
    (hlog_S : 1 * (1 + Real.log S) ≤ S ^ (δ_c / 4))
    (hcross_S : 8 * c * (120 + C + 5 * K) * S ^ (1 - δ_c / 2) ≤ S ^ (1 : ℝ)) :
    (∫ σ in (1 / 2)..1,
      8 * L ^ 2 * Real.cosh (2 * L * (σ - 1 / 2)) *
        (60 * S ^ (θ_X + 1 / 2) + C + 5 * K * Real.log S)) ≤
      4 * V * Real.log V := by
  have hS_pos : 0 < S := zero_lt_one.trans hS1
  have hLS_pos : 0 < Real.log S := Real.log_pos hS1
  have hderiv_ch : ∀ σ : ℝ,
      HasDerivAt (fun t : ℝ => 4 * L * Real.sinh (2 * L * (t - 1 / 2)))
        (8 * L ^ 2 * Real.cosh (2 * L * (σ - 1 / 2))) σ := by
    intro σ
    have hlin : HasDerivAt (fun t : ℝ => 2 * L * (t - 1 / 2)) (2 * L) σ :=
      (((hasDerivAt_id σ).sub_const (1 / 2)).const_mul (2 * L)).congr_deriv (by ring)
    have hsh := ((Real.hasDerivAt_sinh _).comp σ hlin).const_mul (4 * L)
    exact hsh.congr_deriv (by ring)
  rw [intervalIntegral.integral_mul_const,
    integral_eq_sub_of_hasDerivAt (fun σ _ => hderiv_ch σ)
      ((by fun_prop : Continuous _).intervalIntegrable _ _)]
  simp only [sub_self, mul_zero, Real.sinh_zero, sub_zero,
    show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, show 2 * L * (1 / 2) = L by ring]
  have hsh_nn : 0 ≤ Real.sinh L := by
    rw [Real.sinh_eq]
    have h1 : Real.exp (-L) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith only [hL_nn])
    have h2 : 1 ≤ Real.exp L := Real.one_le_exp hL_nn
    linarith only [h1, h2]
  have h4sinh : 4 * L * Real.sinh L ≤ 2 * c * Real.log S * S ^ c := by
    have hsh : Real.sinh L ≤ Real.exp L / 2 := by
      rw [Real.sinh_eq]
      have hpos : 0 < Real.exp (-L) := Real.exp_pos _
      linarith only [hpos]
    have hexpL : Real.exp L ≤ S ^ c := by
      rw [Real.rpow_def_of_pos hS_pos, mul_comm]
      exact Real.exp_le_exp.mpr hL_le_cS
    calc 4 * L * Real.sinh L ≤ 4 * (c * Real.log S) * (S ^ c / 2) := by
          refine mul_le_mul (by linarith only [hL_le_cS])
            (hsh.trans (by linarith only [hexpL])) hsh_nn (by positivity)
      _ = 2 * c * Real.log S * S ^ c := by ring
  have herr_sum : 60 * S ^ (θ_X + 1 / 2) + C + 5 * K * Real.log S ≤
      (120 + C + 5 * K) * S ^ (θ_X + 1 / 2 + δ_c / 4) := by
    have h1_pow : 1 ≤ S ^ (θ_X + 1 / 2) :=
      Real.one_le_rpow hS1.le (by linarith only [hθX_pos])
    have h1_d : 1 ≤ S ^ (δ_c / 4) := Real.one_le_rpow hS1.le (by positivity)
    have hadd_p : S ^ (θ_X + 1 / 2) * S ^ (δ_c / 4) = S ^ (θ_X + 1 / 2 + δ_c / 4) :=
      (Real.rpow_add hS_pos _ _).symm
    have hp1 : S ^ (θ_X + 1 / 2) ≤ S ^ (θ_X + 1 / 2 + δ_c / 4) := by
      rw [← hadd_p]; exact le_mul_of_one_le_right (Real.rpow_nonneg hS_pos.le _) h1_d
    have hp2 : 1 ≤ S ^ (θ_X + 1 / 2 + δ_c / 4) := h1_pow.trans hp1
    have hlogS_pow : Real.log S ≤ S ^ (δ_c / 4) := by linarith only [hlog_S]
    have hp3 : Real.log S ≤ S ^ (θ_X + 1 / 2 + δ_c / 4) := by
      calc Real.log S ≤ 1 * S ^ (δ_c / 4) := by linarith only [hlogS_pow]
        _ ≤ S ^ (θ_X + 1 / 2) * S ^ (δ_c / 4) :=
            mul_le_mul_of_nonneg_right h1_pow (Real.rpow_nonneg hS_pos.le _)
        _ = S ^ (θ_X + 1 / 2 + δ_c / 4) := hadd_p
    nlinarith only [hC, hK, hp1, hp2, hp3]
  have hlogS_pow : Real.log S ≤ S ^ (δ_c / 4) := by linarith only [hlog_S]
  have hprod_S : (2 * c * Real.log S * S ^ c) *
      ((120 + C + 5 * K) * S ^ (θ_X + 1 / 2 + δ_c / 4)) ≤
      8 * c * (120 + C + 5 * K) * S ^ (1 - δ_c / 2) := by
    have hm1 : Real.log S * S ^ c * S ^ (θ_X + 1 / 2 + δ_c / 4) ≤
        S ^ (δ_c / 4) * S ^ c * S ^ (θ_X + 1 / 2 + δ_c / 4) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hlogS_pow (Real.rpow_nonneg hS_pos.le _))
        (Real.rpow_nonneg hS_pos.le _)
    have hm2 : S ^ (δ_c / 4) * S ^ c * S ^ (θ_X + 1 / 2 + δ_c / 4) = S ^ (1 - δ_c / 2) := by
      rw [← Real.rpow_add hS_pos, ← Real.rpow_add hS_pos]
      congr 1; linarith only [hexp_id]
    rw [hm2] at hm1
    have hpos_const : 0 ≤ 2 * c * (120 + C + 5 * K) := by positivity
    have hm3 := mul_le_mul_of_nonneg_left hm1 hpos_const
    have hnn_pow : 0 ≤ c * (120 + C + 5 * K) * S ^ (1 - δ_c / 2) := by positivity
    linarith only [hm3, hnn_pow]
  have hstep := mul_le_mul h4sinh herr_sum
    (by positivity) (by positivity)
  have hS_le : 8 * c * (120 + C + 5 * K) * S ^ (1 - δ_c / 2) ≤ 4 * V * Real.log V := by
    have h1 : S ^ (1 : ℝ) = (3 / 2) * V := by rw [Real.rpow_one, hS_eq]
    rw [h1] at hcross_S
    nlinarith only [hcross_S, hLV_ge1, hV_pos]
  exact (hstep.trans hprod_S).trans hS_le

/-- **Pure continuous abscissa-integrated shell collapse (`0 < c < 1/4`):**
for every `0 < c < 1/4`, integrating `exists_shellDepthSum_add_mollifierCredit_le_abscissa_source_integral`
with a single two-length Barban–Vehov mollifier (`c < θ_Y < θ_X < 1/2 - c`) across `σ ∈ [1/2, 1]`
bounds `shellDepthSum V (2 * V) (c * Real.log V) ≤ K_c * V * Real.log V` directly from the
one-sided mollified source integral with **zero** discrete zero-counting shells and **zero**
external zero-density inputs. -/
theorem exists_pure_abscissa_mollified_shellDepthSum_le_log_quarter
    {c : ℝ} (hc0 : 0 < c) (hc : c < 1 / 4) :
    ∃ K_c : ℝ, 0 < K_c ∧ ∀ᶠ V : ℝ in atTop,
      shellDepthSum V (2 * V) (c * Real.log V) ≤ K_c * V * Real.log V := by
  classical
  set δ_c : ℝ := (1 / 2 - 2 * c) / 3
  have hδ_pos : 0 < δ_c := by dsimp [δ_c]; linarith
  set θ_Y : ℝ := c + δ_c
  set θ_X : ℝ := c + 2 * δ_c
  set r : ℝ := 2 * c + δ_c
  have hθY : 0 < θ_Y := by dsimp [θ_Y]; linarith
  have hYX_exp : θ_Y < θ_X := by dsimp [θ_Y, θ_X]; linarith
  have hθX : θ_X < 1 / 2 := by dsimp [θ_X, δ_c]; linarith
  have hr0 : 0 < r := by dsimp [r]; linarith
  have hr : r < 2 * θ_Y := by dsimp [r, θ_Y]; linarith
  obtain ⟨A₀, hA₀, hev_msq⟩ :=
    exists_twoLength_mollified_meanSquare_arbitrary_exponents hθY hYX_exp hθX hr0 hr
  obtain ⟨C, K, hC, hK, habs_ceil⟩ :=
    exists_shellDepthSum_add_mollifierCredit_le_abscissa_source_integral
  have htend_S : Tendsto (fun V : ℝ => (3 / 2 : ℝ) * V) atTop atTop :=
    Tendsto.const_mul_atTop (by norm_num) tendsto_id
  have hev_cross := eventually_const_mul_rpow_le_rpow
    (C := 8 * c * (120 + C + 5 * K)) (α := 1 - δ_c / 2) (β := 1) (by linarith)
  have hev_logsq := eventually_const_mul_one_add_log_le_rpow (C := 1) (ε := δ_c / 4) (by positivity)
  have hev_end := eventually_const_mul_rpow_le_rpow
    (C := 64 * (|xiLineTwoLogDerivConstant| + 4)) (α := c + δ_c / 4) (β := 1)
    (by dsimp [δ_c]; linarith)
  set K_c : ℝ := (12 * A₀ * c ^ 2 / δ_c + 4) / Real.pi + 2
  have hKc_pos : 0 < K_c := by dsimp [K_c]; positivity
  refine ⟨K_c, hKc_pos, ?_⟩
  filter_upwards [htend_S.eventually hev_msq, htend_S.eventually hev_cross,
    htend_S.eventually hev_logsq, hev_end, eventually_ge_atTop (60 : ℝ)]
    with V hmsq hcross_S hlog_S hend_V hV60
  clear hev_msq hev_cross hev_logsq hev_end htend_S
  set S : ℝ := (3 / 2 : ℝ) * V
  have hV_pos : 0 < V := by linarith
  have hS_pos : 0 < S := by dsimp [S]; positivity
  have hS1 : 1 < S := by dsimp [S]; linarith
  have hLV_pos : 0 < Real.log V := Real.log_pos (by linarith)
  have hLV_ge1 : 1 ≤ Real.log V := by
    have : Real.exp 1 ≤ V := by linarith [Real.exp_one_lt_d9]
    exact (Real.le_log_iff_exp_le hV_pos).mpr this
  have hLS_pos : 0 < Real.log S := Real.log_pos hS1
  have hLV_le_LS : Real.log V ≤ Real.log S :=
    Real.log_le_log hV_pos (by dsimp [S]; linarith)
  have hLS_le_2LV : Real.log S ≤ 2 * Real.log V := by
    have h1 : Real.log S ≤ Real.log (2 * V) := Real.log_le_log hS_pos (by dsimp [S]; linarith)
    rw [Real.log_mul two_ne_zero hV_pos.ne'] at h1
    linarith [Real.log_two_lt_d9, hLV_ge1]
  obtain ⟨T₁, hT₁, T₂, hT₂, hY3, hYX, hXhi, hadm1, hadm2, hMsq_all⟩ := hmsq
  set X : ℕ := VerticalAP.molLen θ_X S
  set Y : ℕ := VerticalAP.molLen θ_Y S
  have hT₁_lo : V < T₁ := by have := hT₁.1; dsimp [S] at this; linarith
  have hT₁_hi : T₁ < V + 1 := by have := hT₁.2; dsimp [S] at this; linarith
  have hT₂_lo : 2 * V - 1 < T₂ := by have := hT₂.1; dsimp [S] at this; linarith
  have hT₂_hi : T₂ < 2 * V := by have := hT₂.2; dsimp [S] at this; linarith
  have hT12 : T₁ < T₂ := by linarith
  have hlen_lo : V / 2 ≤ T₂ - T₁ := by linarith
  have hlen_hi : T₂ - T₁ ≤ V := by linarith
  have hlen_pos : 0 < T₂ - T₁ := by linarith
  set Ψ : ℂ → ℂ := edPoly (twoLengthCoeff X Y) (Finset.Icc 1 X)
  have hΨana : AnalyticOnNhd ℂ Ψ Set.univ :=
    analyticOnNhd_edPoly _ fun m hm => (Finset.mem_Icc.mp hm).1
  have hΨne : ∃ z : ℂ, Ψ z ≠ 0 :=
    ⟨((1 / 2 : ℝ) : ℂ) + (T₁ : ℂ) * I, (hadm1 (1 / 2) ⟨by norm_num, by norm_num⟩).2⟩
  have hZΨ_fin : {z ∈ (uIcc (1 / 2 : ℝ) (15 / 2) ×ℂ uIcc T₁ T₂) | Ψ z = 0}.Finite := by
    have h := entire_zeros_closedRectangle_finite hΨana hΨne
      (((1 / 2 : ℝ) : ℂ) + (T₁ : ℂ) * I) (((15 / 2 : ℝ) : ℂ) + (T₂ : ℂ) * I)
    simpa using h
  set ZΨ : Finset ℂ := hZΨ_fin.toFinset
  set L : ℝ := c * Real.log V
  have hL_nn : 0 ≤ L := by dsimp [L]; positivity
  have hL_le_cS : L ≤ c * Real.log S := mul_le_mul_of_nonneg_left hLV_le_LS hc0.le
  have hlogT₂ : Real.log T₂ ≤ 2 * Real.log S := by
    have h1 : Real.log T₂ ≤ Real.log (2 * S) := Real.log_le_log (by linarith) (by dsimp [S]; linarith)
    rw [Real.log_mul two_ne_zero hS_pos.ne'] at h1
    linarith [Real.log_two_lt_d9, hLV_ge1, hLV_le_LS]
  have hX_ge1 : 1 ≤ X := by omega
  have hlogMb : Real.log ((X : ℝ) ^ (5 : ℕ)) ≤ 3 * Real.log S := by
    rw [Real.log_pow]; push_cast
    have hXpos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX_ge1
    have hlogX : Real.log (X : ℝ) ≤ θ_X * Real.log S := by
      rw [← Real.log_rpow hS_pos]; exact Real.log_le_log hXpos hXhi
    nlinarith [hθX, hLS_pos]
  have hceil := habs_ceil (twoLengthCoeff X Y) X hX_ge1
    (twoLengthCoeff_one (by omega) hYX)
    (fun n hn => norm_twoLengthCoeff_le (by omega) hYX hn)
    (fun n _ => conj_twoLengthCoeff X Y n)
    ((X : ℝ) ^ (5 : ℕ)) (one_le_pow₀ (by exact_mod_cast hX_ge1))
    (sum_norm_twoLengthCoeff_mul_rpow_le (by omega) hYX)
    T₁ T₂ L (by linarith) hT12
    (fun x hx => (hadm1 x ⟨by linarith [hx.1], hx.2⟩).1)
    (fun x hx => (hadm2 x ⟨by linarith [hx.1], hx.2⟩).1)
    (fun x hx => (hadm1 x ⟨by linarith [hx.1], hx.2⟩).2)
    (fun x hx => (hadm2 x ⟨by linarith [hx.1], hx.2⟩).2)
    ZΨ (fun z => Set.Finite.mem_toFinset hZΨ_fin)
  have hcred_nn : 0 ≤ 2 * Real.pi *
      ∑ w ∈ ZΨ, ((analyticOrderAt Ψ w).toNat : ℝ) * mollifierRightCredit L w.re :=
    mul_nonneg (by positivity) (Finset.sum_nonneg fun w _ =>
      mul_nonneg (Nat.cast_nonneg _) (mollifierRightCredit_nonneg L w.re))
  set Msq : ℝ → ℝ := fun σ =>
    ∫ t in T₁..T₂, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I) * Ψ ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2
  have hMsq_cont : ContinuousOn Msq (Icc (1 / 2 : ℝ) 1) := by
    have hp_cont : Continuous (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * I) := by fun_prop
    have hjoint : ContinuousOn
        (fun p : ℝ × ℝ => ‖riemannZeta ((p.1 : ℂ) + (p.2 : ℂ) * I) *
          Ψ ((p.1 : ℂ) + (p.2 : ℂ) * I)‖ ^ 2)
        (Icc (1 / 2 : ℝ) 1 ×ˢ Icc T₁ T₂) := by
      intro p hp
      have hne : ((p.1 : ℂ) + (p.2 : ℂ) * I) ≠ 1 := by
        intro hEq; have him := congrArg Complex.im hEq; simp at him; linarith only [him, hp.2.1, hT₁_lo, hV60]
      exact (((ContinuousAt.comp (g := riemannZeta)
        (f := fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * I)
        (differentiableAt_riemannZeta hne).continuousAt hp_cont.continuousAt).mul
        (ContinuousAt.comp (g := Ψ) (f := fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * I)
          (differentiable_edPoly _ (fun n hn => (Finset.mem_Icc.mp hn).1) _).continuousAt
          hp_cont.continuousAt)).norm.pow 2).continuousWithinAt
    exact continuousOn_parametric_intervalIntegral_of_continuousOn
      (F := fun σ t => ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I) * Ψ ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
      (by norm_num) hT12.le hjoint
  obtain ⟨C', K', _, _, hwide_pos⟩ := exists_wide_zetaOffLine_hinge_add_mollifierCredit_le
  have hMsq_pos : ∀ σ ∈ Icc (1 / 2 : ℝ) 1, 0 < Msq σ := fun σ hσ =>
    (hwide_pos (twoLengthCoeff X Y) X hX_ge1 (twoLengthCoeff_one (by omega) hYX)
      (fun n hn => norm_twoLengthCoeff_le (by omega) hYX hn)
      (fun n _ => conj_twoLengthCoeff X Y n) ((X : ℝ) ^ (5 : ℕ))
      (one_le_pow₀ (by exact_mod_cast hX_ge1))
      (sum_norm_twoLengthCoeff_mul_rpow_le (by omega) hYX) σ T₁ T₂ (Msq σ)
      hσ.1 (by linarith only [hσ.2]) (by linarith only [hT₁_lo, hV60]) hT12
      (fun x hx => (hadm1 x ⟨by linarith only [hx.1, hσ.1], hx.2⟩).1)
      (fun x hx => (hadm2 x ⟨by linarith only [hx.1, hσ.1], hx.2⟩).1)
      (fun x hx => (hadm1 x ⟨by linarith only [hx.1, hσ.1], hx.2⟩).2)
      (fun x hx => (hadm2 x ⟨by linarith only [hx.1, hσ.1], hx.2⟩).2) le_rfl
      (windowZeros T₁ T₂) ZΨ (fun z => mem_windowZeros_iff (by linarith only [hT₁_lo, hV60]) hT12.le z)
      (fun z => Set.Finite.mem_toFinset hZΨ_fin)).1
  clear hwide_pos habs_ceil hadm1 hadm2
  have hint_ptw : ∀ σ ∈ Icc (1 / 2 : ℝ) 1,
      8 * L ^ 2 * Real.cosh (2 * L * (σ - 1 / 2)) *
        ((T₂ - T₁) / 2 * Real.log (Msq σ / (T₂ - T₁)) + C + K * (Real.log T₂ + Real.log ((X : ℝ) ^ (5 : ℕ)))) ≤
      4 * A₀ * L ^ 2 * (T₂ - T₁) * Real.exp (-(δ_c * Real.log S * (σ - 1 / 2))) +
        8 * L ^ 2 * Real.cosh (2 * L * (σ - 1 / 2)) *
          (60 * S ^ (θ_X + 1 / 2) + C + 5 * K * Real.log S) := by
    intro σ hσ
    have hlog_le : Real.log (Msq σ / (T₂ - T₁)) ≤
        A₀ * Real.exp (-(r * (σ - 1 / 2) * Real.log S)) + 120 * S ^ (θ_X + 1 / 2) / (T₂ - T₁) := by
      have hm := hMsq_all σ hσ
      have hdiv : Msq σ / (T₂ - T₁) ≤
          1 + A₀ * Real.exp (-(r * (σ - 1 / 2) * Real.log S)) +
            120 * S ^ (θ_X + 1 / 2) / (T₂ - T₁) := by
        rw [div_le_iff₀ hlen_pos]
        have hrhs : (1 + A₀ * Real.exp (-(r * (σ - 1 / 2) * Real.log S)) +
            120 * S ^ (θ_X + 1 / 2) / (T₂ - T₁)) * (T₂ - T₁) =
            (T₂ - T₁) * (1 + A₀ * Real.exp (-(r * (σ - 1 / 2) * Real.log S))) +
              120 * S ^ (θ_X + 1 / 2) := by
          field_simp [hlen_pos.ne']
        rwa [hrhs]
      have hsub1 := Real.log_le_sub_one_of_pos (by positivity :
        0 < 1 + A₀ * Real.exp (-(r * (σ - 1 / 2) * Real.log S)) +
          120 * S ^ (θ_X + 1 / 2) / (T₂ - T₁))
      exact (Real.log_le_log (div_pos (hMsq_pos σ hσ) hlen_pos) hdiv).trans (by linarith only [hsub1])
    have hm_half : (T₂ - T₁) / 2 * Real.log (Msq σ / (T₂ - T₁)) ≤
        (T₂ - T₁) / 2 * A₀ * Real.exp (-(r * (σ - 1 / 2) * Real.log S)) +
          60 * S ^ (θ_X + 1 / 2) := by
      have h1 := mul_le_mul_of_nonneg_left hlog_le (by positivity : 0 ≤ (T₂ - T₁) / 2)
      have h2 : (T₂ - T₁) / 2 * (120 * S ^ (θ_X + 1 / 2) / (T₂ - T₁)) =
          60 * S ^ (θ_X + 1 / 2) := by field_simp [hlen_pos.ne']; ring
      linarith only [h1, h2]
    have hch_exp : Real.cosh (2 * L * (σ - 1 / 2)) ≤ Real.exp (2 * c * Real.log S * (σ - 1 / 2)) := by
      rw [Real.cosh_eq]
      have hu_nn : 0 ≤ σ - 1 / 2 := sub_nonneg.mpr hσ.1
      have h1 : Real.exp (-(2 * L * (σ - 1 / 2))) ≤ Real.exp (2 * L * (σ - 1 / 2)) :=
        Real.exp_le_exp.mpr (by nlinarith only [hL_nn, hu_nn])
      have h2 : Real.exp (2 * L * (σ - 1 / 2)) ≤ Real.exp (2 * c * Real.log S * (σ - 1 / 2)) :=
        Real.exp_le_exp.mpr (by nlinarith only [hL_le_cS, hu_nn])
      linarith only [h1, h2]
    have hexp_prod : Real.cosh (2 * L * (σ - 1 / 2)) *
        Real.exp (-(r * (σ - 1 / 2) * Real.log S)) ≤
        Real.exp (-(δ_c * Real.log S * (σ - 1 / 2))) := by
      calc Real.cosh (2 * L * (σ - 1 / 2)) * Real.exp (-(r * (σ - 1 / 2) * Real.log S))
          ≤ Real.exp (2 * c * Real.log S * (σ - 1 / 2)) *
              Real.exp (-(r * (σ - 1 / 2) * Real.log S)) :=
            mul_le_mul_of_nonneg_right hch_exp (Real.exp_pos _).le
        _ = Real.exp (-(δ_c * Real.log S * (σ - 1 / 2))) := by
            rw [← Real.exp_add]; congr 1; dsimp [r]; ring
    have hK_err : K * (Real.log T₂ + Real.log ((X : ℝ) ^ (5 : ℕ))) ≤ 5 * K * Real.log S := by
      nlinarith only [hK, hlogT₂, hlogMb]
    have h8_nn : 0 ≤ 8 * L ^ 2 * Real.cosh (2 * L * (σ - 1 / 2)) :=
      mul_nonneg (by positivity) (Real.cosh_pos _).le
    have hstep := mul_le_mul_of_nonneg_left
      (add_le_add (add_le_add hm_half (le_rfl : C ≤ C)) hK_err) h8_nn
    have hmain_step : 8 * L ^ 2 * Real.cosh (2 * L * (σ - 1 / 2)) *
        ((T₂ - T₁) / 2 * A₀ * Real.exp (-(r * (σ - 1 / 2) * Real.log S))) ≤
        4 * A₀ * L ^ 2 * (T₂ - T₁) * Real.exp (-(δ_c * Real.log S * (σ - 1 / 2))) := by
      have hm := mul_le_mul_of_nonneg_left hexp_prod (by positivity : 0 ≤ 4 * A₀ * L ^ 2 * (T₂ - T₁))
      linarith only [hm]
    linarith only [hstep, hmain_step]
  have hlhs_int_cont : ContinuousOn
      (fun σ : ℝ => 8 * L ^ 2 * Real.cosh (2 * L * (σ - 1 / 2)) *
        ((T₂ - T₁) / 2 * Real.log (Msq σ / (T₂ - T₁)) + C +
          K * (Real.log T₂ + Real.log ((X : ℝ) ^ (5 : ℕ)))))
      (Icc (1 / 2 : ℝ) 1) := by
    have hlog : ContinuousOn (fun σ : ℝ => Real.log (Msq σ / (T₂ - T₁))) (Icc (1 / 2 : ℝ) 1) :=
      ContinuousOn.log (hMsq_cont.div_const _) fun σ hσ => (div_pos (hMsq_pos σ hσ) hlen_pos).ne'
    exact ((by fun_prop : Continuous fun σ : ℝ =>
      8 * L ^ 2 * Real.cosh (2 * L * (σ - 1 / 2))).continuousOn).mul
      (((continuousOn_const.mul hlog).add continuousOn_const).add continuousOn_const)
  have hrhs1_int := abscissa_main_exp_integral_le hA₀ hc0 hδ_pos hV_pos hLV_pos hLS_pos
    hLV_le_LS hlen_pos hlen_hi (rfl : L = c * Real.log V)
  have hrhs2_int := abscissa_cross_cosh_integral_le hc0 hδ_pos (hθY.trans hYX_exp) hC hK
    hV_pos hS1 hLV_ge1 hL_nn hL_le_cS (rfl : S = (3 / 2 : ℝ) * V)
    (by dsimp [θ_X, δ_c]; ring) hlog_S hcross_S
  have hint_total : (∫ σ in (1 / 2)..1,
      8 * L ^ 2 * Real.cosh (2 * L * (σ - 1 / 2)) *
        ((T₂ - T₁) / 2 * Real.log (Msq σ / (T₂ - T₁)) + C +
          K * (Real.log T₂ + Real.log ((X : ℝ) ^ (5 : ℕ))))) ≤
      (12 * A₀ * c ^ 2 / δ_c + 4) * V * Real.log V := by
    have h1 : IntervalIntegrable (fun σ : ℝ =>
        4 * A₀ * L ^ 2 * (T₂ - T₁) * Real.exp (-(δ_c * Real.log S * (σ - 1 / 2))))
        volume (1 / 2) 1 := (by fun_prop : Continuous _).intervalIntegrable _ _
    have h2 : IntervalIntegrable (fun σ : ℝ =>
        8 * L ^ 2 * Real.cosh (2 * L * (σ - 1 / 2)) *
          (60 * S ^ (θ_X + 1 / 2) + C + 5 * K * Real.log S))
        volume (1 / 2) 1 := (by fun_prop : Continuous _).intervalIntegrable _ _
    have hmono := integral_mono_on (μ := volume) (by norm_num : (1 / 2 : ℝ) ≤ 1)
      (hlhs_int_cont.intervalIntegrable_of_Icc (by norm_num)) (h1.add h2) hint_ptw
    rw [intervalIntegral.integral_add h1 h2] at hmono
    linarith only [hmono, hrhs1_int, hrhs2_int]
  have hmid_shell : shellDepthSum T₁ T₂ L ≤
      ((12 * A₀ * c ^ 2 / δ_c + 4) / Real.pi) * V * Real.log V := by
    have hpi_pos : 0 < Real.pi := Real.pi_pos
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hpi_pos]
    linarith only [hceil, hcred_nn, hint_total]
  clear hMsq_all hMsq_cont hMsq_pos hint_ptw hlhs_int_cont hrhs1_int hrhs2_int
    hint_total hceil hcred_nn ZΨ hZΨ_fin hΨne hΨana Msq Ψ
  have hend_bound : shellDepthSum V T₁ L + shellDepthSum T₂ (2 * V) L ≤ 2 * V * Real.log V := by
    have hdk_end : ∀ z : ℂ, |z.re - 1 / 2| ≤ 1 / 2 → depthKernel L (z.re - 1 / 2) ≤ V ^ c := by
      intro z hz
      rw [← depthKernel_abs_depth, depthKernel_eq_four_sinh_sq]
      have harg : |z.re - 1 / 2| * L ≤ L / 2 := by nlinarith only [hz, hL_nn]
      have hsh : Real.sinh (|z.re - 1 / 2| * L) ≤ Real.exp (L / 2) / 2 := by
        rw [Real.sinh_eq]
        have h1 : Real.exp (|z.re - 1 / 2| * L) ≤ Real.exp (L / 2) := Real.exp_le_exp.mpr harg
        have h2 : 0 < Real.exp (-(|z.re - 1 / 2| * L)) := Real.exp_pos _
        linarith only [h1, h2]
      have hsh_nn : 0 ≤ Real.sinh (|z.re - 1 / 2| * L) :=
        sinh_nonneg_of_nonneg_aux (mul_nonneg (abs_nonneg _) hL_nn)
      have hsq := pow_le_pow_left₀ hsh_nn hsh 2
      calc 4 * Real.sinh (|z.re - 1 / 2| * L) ^ 2
          ≤ 4 * (Real.exp (L / 2) / 2) ^ 2 := mul_le_mul_of_nonneg_left hsq (by norm_num)
        _ = Real.exp L := by
            rw [div_pow, sq, ← Real.exp_add]
            have : L / 2 + L / 2 = L := by ring
            rw [this]; ring
        _ = V ^ c := by dsimp [L]; rw [Real.rpow_def_of_pos hV_pos, mul_comm]
    have hcap : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 2 * V → b - a ≤ 2 →
        shellDepthSum a b L ≤ V * Real.log V := by
      intro a b ha0 hab hb2V hba
      have hpt : ∀ z ∈ shellZeros a b,
          ((analyticOrderAt xi z).toNat : ℝ) * depthKernel L (z.re - 1 / 2) ≤
            ((analyticOrderAt xi z).toNat : ℝ) * V ^ c := by
        intro z hz
        obtain ⟨h0, h1, _, _, _⟩ := mem_stripFinsetPos.mp (Finset.mem_filter.mp hz).1
        exact mul_le_mul_of_nonneg_left
          (hdk_end z (abs_le.mpr ⟨by linarith only [h0], by linarith only [h1]⟩)) (Nat.cast_nonneg _)
      have hsum_ord := shortShell_orderSum_le_log ha0 hab hba
      have hlog_b : Real.log (b + 4) ≤ 2 * Real.log V := by
        have h1 : Real.log (b + 4) ≤ Real.log (V ^ (2 : ℕ)) :=
          Real.log_le_log (by linarith only [ha0, hab]) (by nlinarith only [hb2V, hV60])
        rw [Real.log_pow] at h1; push_cast at h1; exact h1
      calc shellDepthSum a b L
          ≤ ∑ z ∈ shellZeros a b, ((analyticOrderAt xi z).toNat : ℝ) * V ^ c :=
            Finset.sum_le_sum hpt
        _ = (∑ z ∈ shellZeros a b, ((analyticOrderAt xi z).toNat : ℝ)) * V ^ c :=
            (Finset.sum_mul _ _ _).symm
        _ ≤ 16 * (|xiLineTwoLogDerivConstant| + Real.log (b + 4)) * V ^ c :=
            mul_le_mul_of_nonneg_right hsum_ord (Real.rpow_nonneg hV_pos.le _)
        _ ≤ (64 * (|xiLineTwoLogDerivConstant| + 4) * V ^ (c + δ_c / 4)) * Real.log V := by
            have hvc : V ^ c ≤ V ^ (c + δ_c / 4) :=
              Real.rpow_le_rpow_of_exponent_le (by linarith only [hV60]) (by linarith only [hδ_pos])
            have hc_abs : 0 ≤ |xiLineTwoLogDerivConstant| := abs_nonneg _
            have hbr : |xiLineTwoLogDerivConstant| + Real.log (b + 4) ≤
                (|xiLineTwoLogDerivConstant| + 4) * Real.log V := by
              nlinarith only [hlog_b, hLV_ge1, hc_abs]
            have hm := mul_le_mul (mul_le_mul_of_nonneg_left hbr (by norm_num : (0 : ℝ) ≤ 16))
              hvc (Real.rpow_nonneg hV_pos.le _) (by positivity)
            have hv_nn : 0 ≤ V ^ (c + δ_c / 4) := Real.rpow_nonneg hV_pos.le (c + δ_c / 4)
            have hid : 16 * ((|xiLineTwoLogDerivConstant| + 4) * Real.log V) * V ^ (c + δ_c / 4) =
                16 * ((|xiLineTwoLogDerivConstant| + 4) * V ^ (c + δ_c / 4) * Real.log V) := by ring
            have hid2 : (64 * (|xiLineTwoLogDerivConstant| + 4) * V ^ (c + δ_c / 4)) * Real.log V =
                64 * ((|xiLineTwoLogDerivConstant| + 4) * V ^ (c + δ_c / 4) * Real.log V) := by ring
            have hnn : 0 ≤ (|xiLineTwoLogDerivConstant| + 4) * V ^ (c + δ_c / 4) * Real.log V :=
              mul_nonneg (mul_nonneg (by positivity) hv_nn) hLV_pos.le
            linarith only [hm, hid, hid2, hnn]
        _ ≤ V * Real.log V := by
            have hv1 : V ^ (1 : ℝ) = V := Real.rpow_one V
            rw [hv1] at hend_V
            exact mul_le_mul_of_nonneg_right hend_V hLV_pos.le
    exact (add_le_add
      (hcap V T₁ hV_pos.le hT₁_lo.le (by linarith only [hT₁_hi, hV60]) (by linarith only [hT₁_lo, hT₁_hi]))
      (hcap T₂ (2 * V) (by linarith only [hT₂_lo, hV60]) hT₂_hi.le le_rfl (by linarith only [hT₂_lo, hT₂_hi]))).trans_eq
      (by ring)
  rw [shellDepthSum_split hT₁_lo.le (hT12.le.trans hT₂_hi.le),
    shellDepthSum_split hT12.le hT₂_hi.le]
  have hsum_kc : ((12 * A₀ * c ^ 2 / δ_c + 4) / Real.pi) * V * Real.log V + 2 * V * Real.log V =
      K_c * V * Real.log V := by dsimp [K_c]; ring
  linarith only [hmid_shell, hend_bound, hsum_kc]
where
  sinh_nonneg_of_nonneg_aux {x : ℝ} (hx : 0 ≤ x) : 0 ≤ Real.sinh x := by
    rw [Real.sinh_eq]
    linarith [Real.exp_le_one_iff.mpr (by linarith : -x ≤ 0), Real.one_le_exp hx]

end GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect

#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.superharmonic_rect_verticalMean_le_linear
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.no_superharmonic_weight_dominates_depthKernel
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.depthKernel_eq_abscissa_integral
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.sum_depthKernel_eq_sinh_tail_integral
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.halfPlane_green_identity_halfPlaneDepthWeight
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.halfPlane_archXi_log_norm_annihilated
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.exists_shellDepthSum_add_mollifierCredit_le_abscissa_source_integral
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.exists_pure_abscissa_mollified_shellDepthSum_le_log_quarter


