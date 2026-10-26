import GaloisForLFunctions.ConjugateDiagonalGeometry.ZetaDepthDistribution
import GaloisForLFunctions.RHTower.EulerShiftPairIncidenceCurrent
import GaloisForLFunctions.RHTower.CompletedPrimeFluxFittingAttachment
import GaloisForLFunctions.RHTower.EvenSectorFullPositivity
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# The xi current evaluated on conjugate-diagonal kernels

The distributional Laplacian of `log ‖xi‖` evaluates compact nonholomorphic
test squares. A canonical smooth exhaustion recovers the full collided form
and every fixed-scale depth-kernel moment. Multiplicities and convergence
are proved for the actual zeta divisor.

These source integrals contain no zero-indexed definition. Their evaluation
does not by itself estimate them by prime data or force the Hecke defect to
vanish.
-/

open Complex MeasureTheory Filter Set Metric
open scoped Laplacian Topology

noncomputable section

namespace GaloisForLFunctions.ConjugateDiagonalGeometry

open Zeta23 ArithmeticPolarization HTGeometry _root_.RHTower

/-- Canonical smooth exhaustion of the spectral plane. -/
def sourceCutoff (n : ℕ) : ContDiffBump (0 : ℂ) where
  rIn := (n : ℝ) + 1
  rOut := (n : ℝ) + 2
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

theorem sourceCutoff_eventually_one (z : ℂ) :
    ∀ᶠ n : ℕ in atTop, sourceCutoff n z = 1 := by
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop ‖z‖]
    with n hn
  apply (sourceCutoff n).one_of_mem_closedBall
  rw [Metric.mem_closedBall, dist_zero_right]
  change ‖z‖ ≤ (n : ℝ) + 1
  linarith only [hn]

/-- The entire source transform is smooth also in the two real spectral coordinates. -/
theorem contDiff_tr (f : CompactTest) : ContDiff ℝ 2 (tr f.1) := by
  have htr : Differentiable ℂ (tr f.1) :=
    (RHTower.EvenSector.differentiable_paperFT_of_compact f.2.1.continuous f.2.2).comp
      (by unfold gammaOf; fun_prop)
  exact htr.contDiff.restrict_scalars ℝ

/-- Nonholomorphic spectral kernel for the `j`-th depth moment. -/
def sourceDepthKernel (f : CompactTest) (L : ℝ) (j : ℕ) (z : ℂ) : ℝ :=
  Complex.normSq (tr f.1 z) * depthKernel L (z.re - 1 / 2) ^ j

theorem contDiff_sourceDepthKernel (f : CompactTest) (L : ℝ) (j : ℕ) :
    ContDiff ℝ 2 (sourceDepthKernel f L j) := by
  have htr := contDiff_tr f
  have hn : ContDiff ℝ 2 (fun z => Complex.normSq (tr f.1 z)) := by
    simp only [Complex.normSq_apply]
    simpa only [pow_two] using ((Complex.reCLM.contDiff.comp htr).pow 2).add
      ((Complex.imCLM.contDiff.comp htr).pow 2)
  have hk : ContDiff ℝ 2 (fun z : ℂ => depthKernel L (z.re - 1 / 2)) := by
    unfold depthKernel
    have hRe : ContDiff ℝ 2 (fun z : ℂ => z.re) := Complex.reCLM.contDiff
    fun_prop
  exact hn.mul (hk.pow j)

/-- A source-defined reading of the xi current against a cutoff diagonal kernel. -/
def sourceCurrentReading (f : CompactTest) (L : ℝ) (j n : ℕ) : ℝ :=
  ∫ z : ℂ, Real.log ‖xi z‖ *
    Laplacian.laplacian (fun w => sourceCutoff n w * sourceDepthKernel f L j w) z

/-- Compact support makes the xi divisor pairing a finite carrier sum, with zeta multiplicity. -/
theorem xi_realDivisorPairing_eq_carrier (φ : ℂ → ℝ) (hc : HasCompactSupport φ) :
    realDivisorPairing xi φ =
      ∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℝ) * φ ρ := by
  classical
  let g : ℂ → ℝ := fun z => (HTGeometry.zeroMult xi z : ℝ) * φ z
  have hzero (z : ℂ) (hz : z ∈ Function.support g) : xi z = 0 := by
    apply HTGeometry.eq_zero_of_zeroMult_ne_zero
    intro hm
    exact hz (by simp only [g, hm, Nat.cast_zero, zero_mul])
  have hφ (z : ℂ) (hz : z ∈ Function.support g) : φ z ≠ 0 := by
    intro h
    exact hz (by simp only [g, h, mul_zero])
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall (0 : ℂ)
  have hfinite : Function.HasFiniteSupport g :=
    (xi_zeros_closedBall_finite 0 R).subset fun z hz =>
      ⟨hR (subset_tsupport φ (hφ z hz)), hzero z hz⟩
  have hsupport : Function.support g ⊆ zetaZeroConfig.carrier := by
    intro z hz
    have hxi := hzero z hz
    have hstrip := xi_zero_re_mem_open_unit hxi
    change IsNontrivialZero z
    exact ⟨(xi_zero_iff_zeta_zero_of_mem_strip hstrip.1 hstrip.2).mp hxi, hstrip⟩
  change (∑ᶠ z, g z) = _
  rw [← tsum_eq_finsum (L := SummationFilter.unconditional ℂ) hfinite,
    ← tsum_subtype_eq_of_support_subset hsupport]
  apply tsum_congr
  intro ρ
  have hm : HTGeometry.zeroMult xi (ρ : ℂ) = zetaZeroConfig.mult ρ := by
    change (analyticOrderAt xi (ρ : ℂ)).toNat =
      (analyticOrderAt riemannZeta (ρ : ℂ)).toNat
    rw [xi_analyticOrderAt_eq_riemannZeta_of_mem_strip ⟨ρ.2.2.1, ρ.2.2.2⟩]
  exact congrArg (fun m : ℕ => (m : ℝ) * φ ρ) hm

/-- Exact cutoff identity: the analytic current computes the diagonal kernel trace. -/
theorem sourceCurrentReading_eq_trace (f : CompactTest) (L : ℝ) (j n : ℕ) :
    sourceCurrentReading f L j n = 2 * Real.pi *
      ∑' ρ : zetaZeroConfig.carrier,
        sourceCutoff n ρ * (zetaWeight f ρ * depthKernel L (zetaDepth ρ) ^ j) := by
  have hc : HasCompactSupport (fun z => sourceCutoff n z * sourceDepthKernel f L j z) :=
    (sourceCutoff n).hasCompactSupport.mul_right
  rw [sourceCurrentReading,
    RHTower.EulerShiftPairIncidenceCurrent.xi_isPoincareLelongOfSmooth _
      ((sourceCutoff n).contDiff.mul (contDiff_sourceDepthKernel f L j)) hc,
    xi_realDivisorPairing_eq_carrier _ hc]
  congr 1
  apply tsum_congr
  intro ρ
  dsimp [zetaWeight, sourceDepthKernel, zetaDepth]
  ring

/-- Cutoff exhaustion evaluates every depth-kernel moment without a convergence premise. -/
theorem tendsto_sourceCurrentReading (f : CompactTest) (L : ℝ) (j : ℕ) :
    Tendsto (fun n => sourceCurrentReading f L j n) atTop
      (𝓝 (2 * Real.pi * ∑' ρ : zetaZeroConfig.carrier,
        zetaWeight f ρ * depthKernel L (zetaDepth ρ) ^ j)) := by
  have hnonneg (ρ : zetaZeroConfig.carrier) :
      0 ≤ zetaWeight f ρ * depthKernel L (zetaDepth ρ) ^ j :=
    mul_nonneg (zetaWeight_nonneg f ρ) (pow_nonneg (depthKernel_nonneg _ _) _)
  have hlim := tendsto_tsum_of_dominated_convergence
    (f := fun n (ρ : zetaZeroConfig.carrier) =>
      sourceCutoff n ρ * (zetaWeight f ρ * depthKernel L (zetaDepth ρ) ^ j))
    (g := fun ρ => zetaWeight f ρ * depthKernel L (zetaDepth ρ) ^ j)
    (bound := fun ρ => zetaWeight f ρ * depthKernel L (zetaDepth ρ) ^ j)
    (summable_zeta_kernel_pow f L j)
    (fun ρ => tendsto_const_nhds.congr' ((sourceCutoff_eventually_one ρ).mono
      fun n hn => by dsimp only; rw [hn, one_mul]))
    (Eventually.of_forall fun n ρ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sourceCutoff n).nonneg (hnonneg ρ))]
      calc sourceCutoff n ρ * (zetaWeight f ρ * depthKernel L (zetaDepth ρ) ^ j)
          ≤ 1 * (zetaWeight f ρ * depthKernel L (zetaDepth ρ) ^ j) :=
            mul_le_mul_of_nonneg_right (sourceCutoff n).le_one (hnonneg ρ)
        _ = _ := one_mul _)
  simpa only [sourceCurrentReading_eq_trace] using hlim.const_mul (2 * Real.pi)

/-- The full collided form is a limit of integrals defined only by xi and the source test. -/
theorem tendsto_sourceCurrentReading_collided (f : CompactTest) :
    Tendsto (fun n => sourceCurrentReading f 0 0 n) atTop
      (𝓝 (2 * Real.pi * collidedForm zetaZeroConfig f.1)) := by
  simpa only [pow_zero, mul_one, zetaWeight, collidedForm] using
    tendsto_sourceCurrentReading f 0 0

/-- The same arithmetic analytic source reads the symmetric Hecke defect. -/
theorem tendsto_sourceCurrentReading_heckeDefect (f : CompactTest) (L : ℝ) :
    Tendsto (fun n => sourceCurrentReading f L 1 n) atTop
      (𝓝 (2 * Real.pi * heckeDefect f L)) := by
  simpa only [pow_one, heckeDefect] using tendsto_sourceCurrentReading f L 1

end GaloisForLFunctions.ConjugateDiagonalGeometry
