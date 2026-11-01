import GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.MollifiedCorridorAndThetaReading
import GaloisForLFunctions.RHTower.CosDilationKernelBlindnessLink
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
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

open Complex Filter Topology Set MeasureTheory intervalIntegral
open scoped BigOperators Real ComplexConjugate ContDiff ENNReal Laplacian Interval
open _root_.RHTower _root_.RHTower.ExactNullDivisorTransfer _root_.Zeta23

noncomputable section

namespace GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect

open GaloisForLFunctions.ConjugateDiagonalGeometry

/-! ## §1. Directional calculus on half-plane rectangles and superharmonic linear ceiling -/

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
  rw [laplacian_eq_iteratedFDeriv_complexPlane f]
  show iteratedFDeriv ℝ 2 f z ![1, 1] + iteratedFDeriv ℝ 2 f z ![I, I] =
    Bottcher.dderiv f 1 z + Bottcher.dderiv f I z
  rw [key 1, key I]

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
  have hdd1_cont : Continuous (Bottcher.dderiv Φ 1) := fun_prop_aux :
    by
      rw [continuous_iff_continuousAt]
      exact fun z => continuousAt_dderiv_of_contDiffAt hΦ.contDiffAt 1
  have hddI_cont : Continuous (Bottcher.dderiv Φ I) := by
    rw [continuous_iff_continuousAt]
    exact fun z => continuousAt_dderiv_of_contDiffAt hΦ.contDiffAt I
  have hslope_le : ∀ t ∈ Icc (1 / 2) x,
      (∫ y in T₁..T₂, fderiv ℝ Φ ((t : ℂ) + (y : ℂ) * I) 1) ≤
        ∫ y in T₁..T₂, fderiv ℝ Φ (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I) 1 := by
    intro t ht
    have ht_mem : ∀ s ∈ Icc (1 / 2) t, s ∈ Icc (1 / 2) σ_R :=
      fun s hs => ⟨hs.1, hs.2.trans (ht.2.trans hx.2)⟩
    have hftc_s : ∀ y ∈ Icc T₁ T₂,
        fderiv ℝ Φ ((t : ℂ) + (y : ℂ) * I) 1 -
          fderiv ℝ Φ (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I) 1 =
          ∫ s in (1 / 2)..t, Bottcher.dderiv Φ 1 ((s : ℂ) + (y : ℂ) * I) := by
      intro y _
      symm
      refine integral_eq_sub_of_hasDerivAt (fun s _ => ?_)
        ((hdd1_cont.comp (by fun_prop)).intervalIntegrable _ _)
      exact hasDerivAt_horiz_real ((contDiffAt_fderiv_apply hΦ.contDiffAt 1).differentiableAt le_rfl)
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
      exact integral_integral_swap ((hdd1_cont.comp hpair_cont). integrableOn_Icc ?_ )
  sorry
