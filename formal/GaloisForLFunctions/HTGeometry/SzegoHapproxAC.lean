import GaloisForLFunctions.HTGeometry.SzegoUpperBoundAC
import GaloisForLFunctions.HTGeometry.SzegoUpperBound
import GaloisForLFunctions.HTGeometry.SzegoLowerBoundGeneral
import GaloisForLFunctions.HTGeometry.SzegoH2

/-!
# The absolutely continuous Szegő approximation

For a positive continuous weight `W` bounded between `0 < c ≤ W ≤ C` on the unit circle, the
reversed Taylor polynomials of the reciprocal outer function `D(0)/D` realize the Szegő infimum:
`∫|q*|² dμ → GM`, where `dμ = W · dm` and `GM = |D(0)|²`.  This is the outer-function approximation
that discharges the `happrox` hypothesis of `hasSzegoFirstLimitConclusion_of_approx` for the
absolutely continuous bounded case.

The algebraic core here is that the reversed polynomial `revPoly c (N+1)` with the reflected,
conjugated Taylor coefficients of `1/D` equals `D(0)` times the `(N+2)`-nd Taylor partial sum of
`1/D`; its circle modulus is therefore `|D(0)|·|Sₙ|`, and the interior bound of `SzegoUpperBoundAC`
drives `(2π)⁻¹∫|Sₙ|² W → 1`.
-/

open MeasureTheory Complex Filter Topology
open scoped Real ComplexConjugate ENNReal NNReal

namespace GaloisForLFunctions.HTGeometry

/-- **The reversed polynomial is `D(0)` times the Taylor partial sum of `1/D`.**  With the reflected
conjugated coefficients `cᵢ = -conj(D(0)·b_{N+1-i})`, the value-`1`-at-origin reversed polynomial
`revPoly c (N+1)` equals `D(0)·S_{N+2}` where `S_{N+2}` is the `(N+2)`-nd Taylor partial sum of the
reciprocal outer function `1/D`. -/
theorem revPoly_eq_szegoOuter_mul_partialSum (w : ℝ → ℝ) {R₀ : NNReal} (N : ℕ)
    (hb0 : szegoOuter w 0 * (cauchyPowerSeries (fun z => (szegoOuter w z)⁻¹) 0 R₀).coeff 0 = 1)
    (z : ℂ) :
    revPoly (fun i => -(starRingEnd ℂ) (szegoOuter w 0 *
        (cauchyPowerSeries (fun z => (szegoOuter w z)⁻¹) 0 R₀).coeff (N + 1 - i))) (N + 1) z
      = szegoOuter w 0
        * (cauchyPowerSeries (fun z => (szegoOuter w z)⁻¹) 0 R₀).partialSum (N + 2) z := by
  set p := cauchyPowerSeries (fun z => (szegoOuter w z)⁻¹) 0 R₀ with hp
  set D0 := szegoOuter w 0 with hD0
  set g : ℕ → ℂ := fun k => D0 * (z ^ k * p.coeff k) with hg
  -- RHS as `∑_{k<N+2} g k`
  have hRHS : D0 * p.partialSum (N + 2) z = ∑ k ∈ Finset.range (N + 2), g k := by
    rw [FormalMultilinearSeries.partialSum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [p.apply_eq_pow_smul_coeff, smul_eq_mul, hg]
  -- LHS: expand the reversed polynomial and simplify the conjugate of each coefficient
  have hLHS : revPoly (fun i => -(starRingEnd ℂ) (D0 * p.coeff (N + 1 - i))) (N + 1) z
      = 1 + ∑ i ∈ Finset.range (N + 1), g (N + 1 - i) := by
    rw [revPoly]
    have hcoeff : ∀ i, (starRingEnd ℂ) (-(starRingEnd ℂ) (D0 * p.coeff (N + 1 - i)))
        * z ^ (N + 1 - i) = -(g (N + 1 - i)) := by
      intro i
      rw [map_neg, Complex.conj_conj, hg]
      ring
    rw [Finset.sum_congr rfl (fun i _ => hcoeff i)]
    rw [Finset.sum_neg_distrib, sub_neg_eq_add]
  rw [hLHS, hRHS]
  -- `g 0 = 1`
  have hg0 : g 0 = 1 := by rw [hg]; simp only [pow_zero, one_mul]; rw [← hb0]
  -- reindex: `∑_{i<N+1} g(N+1-i) = ∑_{i<N+1} g(i+1)`, then peel off `g 0`
  have hreflect : ∑ i ∈ Finset.range (N + 1), g (N + 1 - i)
      = ∑ i ∈ Finset.range (N + 1), g (i + 1) := by
    rw [← Finset.sum_range_reflect (fun i => g (i + 1)) (N + 1)]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hilt : i < N + 1 := Finset.mem_range.mp hi
    congr 1
    omega
  rw [hreflect, Finset.sum_range_succ' g (N + 1), hg0, add_comm]

/-- **Measure-plumbing for a continuous circle density.**  Integrating a continuous `F` against the
absolutely continuous measure `dμ = W · dm` (`m = circleLebesgue`) equals the angular integral
`(2π)⁻¹∫₀²π W(e^{iθ})·F(e^{iθ}) dθ`. -/
theorem integral_withDensity_circleLebesgue_eq {W : ℂ → ℝ} (hWcont : Continuous W)
    (hWc0 : ∀ z : Circle, 0 ≤ W (z : ℂ))
    {F : ℂ → ℝ} (hF : Continuous F) :
    ∫ z : Circle, F (z : ℂ) ∂(circleLebesgue.withDensity (fun z => ENNReal.ofReal (W (z : ℂ))))
      = (2 * π)⁻¹ * ∫ θ in (0:ℝ)..(2 * π), W (circleMap 0 1 θ) * F (circleMap 0 1 θ) := by
  have hcoe : Continuous (fun z : Circle => (z : ℂ)) := by fun_prop
  have hWcirc : Continuous (fun z : Circle => W (z : ℂ)) := hWcont.comp hcoe
  set dens : Circle → ℝ≥0∞ := fun z => ENNReal.ofReal (W (z : ℂ)) with hdens
  have hmeas : AEMeasurable dens circleLebesgue :=
    (ENNReal.continuous_ofReal.comp hWcirc).measurable.aemeasurable
  have hlt : ∀ᵐ z ∂circleLebesgue, dens z < ∞ :=
    Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
  rw [integral_withDensity_eq_integral_toReal_smul₀ hmeas hlt (fun z => F (z : ℂ))]
  have hcongr : (fun z : Circle => (dens z).toReal • F (z : ℂ))
      = fun z : Circle => (fun u => W u * F u) (z : ℂ) := by
    funext z; simp only [hdens]; rw [smul_eq_mul, ENNReal.toReal_ofReal (hWc0 z)]
  rw [hcongr]
  have hWF : AEStronglyMeasurable (fun z : Circle => (fun u => W u * F u) (z : ℂ)) circleLebesgue :=
    ((hWcont.mul hF).comp hcoe).aestronglyMeasurable
  rw [integral_circleLebesgue_eq_circleAverage (fun u => W u * F u) hWF, Real.circleAverage,
    smul_eq_mul]

/-- **The Szegő geometric mean of a continuous circle density is `|D(0)|²`.**  For `dμ = W · dm`
with `W` continuous and `c ≤ W` on the circle, the Radon–Nikodym density has Szegő geometric mean
`exp((2π)⁻¹∫ log W) = ‖D(0)‖²`, the squared value of the outer function at the origin. -/
theorem szegoGeometricMean_withDensity_eq {W : ℂ → ℝ} {c : ℝ} (hc : 0 < c)
    (hWcont : Continuous W) (hWc : ∀ z : Circle, c ≤ W (z : ℂ)) :
    szegoGeometricMean circleLebesgue
        ((circleLebesgue.withDensity (fun z => ENNReal.ofReal (W (z : ℂ)))).rnDeriv circleLebesgue)
      = ‖szegoOuter (fun θ => W (circleMap 0 1 θ)) 0‖ ^ 2 := by
  have hcoe : Continuous (fun z : Circle => (z : ℂ)) := by fun_prop
  have hWcirc : Continuous (fun z : Circle => W (z : ℂ)) := hWcont.comp hcoe
  have hWpos : ∀ z : Circle, 0 < W (z : ℂ) := fun z => lt_of_lt_of_le hc (hWc z)
  set dens : Circle → ℝ≥0∞ := fun z => ENNReal.ofReal (W (z : ℂ)) with hdens
  -- rnDeriv of the withDensity measure equals the density a.e.
  have hrn : (circleLebesgue.withDensity dens).rnDeriv circleLebesgue =ᵐ[circleLebesgue] dens :=
    Measure.rnDeriv_withDensity circleLebesgue (ENNReal.continuous_ofReal.comp hWcirc).measurable
  rw [szegoGeometricMean_congr_ae circleLebesgue _ dens hrn]
  -- positivity and log-integrability, so the finite-log branch applies
  have hpos : ∀ᵐ z ∂circleLebesgue, 0 < dens z ∧ dens z < ∞ :=
    Filter.Eventually.of_forall (fun z => ⟨ENNReal.ofReal_pos.mpr (hWpos z), ENNReal.ofReal_lt_top⟩)
  have hlogWcirc : Continuous (fun z : Circle => Real.log (W (z : ℂ))) :=
    hWcirc.log (fun z => (hWpos z).ne')
  have htoReal : (fun z : Circle => Real.log ((dens z).toReal))
      = fun z : Circle => Real.log (W (z : ℂ)) := by
    funext z; simp only [hdens]; rw [ENNReal.toReal_ofReal (hWpos z).le]
  have hint : Integrable (fun z : Circle => Real.log ((dens z).toReal)) circleLebesgue := by
    rw [htoReal]
    exact hlogWcirc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [szegoGeometricMean_eq_exp_integral circleLebesgue dens hpos hint, normSq_szegoOuter_zero]
  -- identify the integral with the angular log-integral, matching `normSq_szegoOuter_zero`
  congr 1
  rw [htoReal, integral_circleLebesgue_eq_circleAverage (fun u => Real.log (W u))
      hlogWcirc.aestronglyMeasurable, Real.circleAverage, smul_eq_mul, one_div]

/-- **The first Szegő limit theorem for a continuous positive circle weight.**  For a continuous
`W` with `0 < c ≤ W ≤ C` on the unit circle and infinite-support absolutely continuous measure
`dμ = W · dm`, the consecutive Toeplitz determinant ratios converge to the geometric mean
`GM = |D(0)|²`.  The reversed Taylor polynomials of `D(0)/D` realize the Szegő infimum. -/
theorem hasSzegoFirstLimitConclusion_withDensity_continuous {W : ℂ → ℝ} {c C : ℝ}
    (hc : 0 < c) (hWcont : Continuous W)
    (hwc : ∀ u : ℂ, ‖u‖ = 1 → c ≤ W u) (hwC : ∀ u : ℂ, ‖u‖ = 1 → W u ≤ C)
    (hsupp : (circleLebesgue.withDensity (fun z => ENNReal.ofReal (W (z : ℂ)))).support.Infinite) :
    HasSzegoFirstLimitConclusion
      (circleMeasureGramTower (circleLebesgue.withDensity (fun z => ENNReal.ofReal (W (z : ℂ)))))
      (circleLebesgue.withDensity (fun z => ENNReal.ofReal (W (z : ℂ))))
      circleLebesgue := by
  classical
  set w : ℝ → ℝ := fun θ => W (circleMap 0 1 θ) with hw
  -- boundary/circle norm facts
  have hnorm1 : ∀ θ : ℝ, ‖circleMap 0 1 θ‖ = 1 := fun θ => by rw [norm_circleMap_zero]; norm_num
  have hcnorm : ∀ z : Circle, ‖(z : ℂ)‖ = 1 := fun z => Circle.norm_coe z
  -- angular weight bounds
  have hwcθ : ∀ θ, c ≤ w θ := fun θ => hwc _ (hnorm1 θ)
  have hwCθ : ∀ θ, w θ ≤ C := fun θ => hwC _ (hnorm1 θ)
  have hwpos : ∀ θ, 0 < w θ := fun θ => lt_of_lt_of_le hc (hwcθ θ)
  have hCpos : 0 < C := lt_of_lt_of_le hc (le_trans (hwcθ 0) (hwCθ 0))
  have hWc0 : ∀ z : Circle, 0 ≤ W (z : ℂ) := fun z => le_trans hc.le (hwc _ (hcnorm z))
  -- continuity + integrability of `log w`
  have hwcont : Continuous w := hWcont.comp (continuous_circleMap 0 1)
  have hlogcont : Continuous (fun θ => Real.log (w θ)) := hwcont.log (fun θ => (hwpos θ).ne')
  have hlog : IntervalIntegrable (fun θ => Real.log (w θ)) volume 0 (2 * π) :=
    hlogcont.intervalIntegrable 0 (2 * π)
  have hlogLI : LocallyIntegrable (fun θ => Real.log (w θ)) volume := hlogcont.locallyIntegrable
  have hwper : Function.Periodic w (2 * π) := fun θ => by
    simp only [hw]; rw [periodic_circleMap 0 1 θ]
  have hper : Function.Periodic (fun θ => Real.log (w θ)) (2 * π) := fun θ => by
    show Real.log (w (θ + 2 * π)) = Real.log (w θ); rw [hwper θ]
  have hlogφ : ∀ φ, IntervalIntegrable (fun t => Real.log (w (φ + t))) volume (-π) π := fun φ =>
    (hlogcont.comp (continuous_const.add continuous_id)).intervalIntegrable (-π) π
  -- fixed radius and reciprocal-outer power series
  set R₀ : NNReal := 1 / 2 with hR₀
  have hR₀0 : 0 < R₀ := by rw [hR₀]; norm_num
  have hR₀1 : (R₀ : ℝ) < 1 := by rw [hR₀]; norm_num
  set p := cauchyPowerSeries (fun z => (szegoOuter w z)⁻¹) 0 R₀ with hp
  have hsum : Summable (fun k => ‖p.coeff k‖ ^ 2) :=
    summable_of_sum_range_le (fun k => by positivity)
      (fun N => gutzmer_tsum_le hc hlog hper hlogφ hwcθ hR₀0 hR₀1 N)
  have hb0 : szegoOuter w 0 * p.coeff 0 = 1 := by
    have hc0 : p.coeff 0 = (szegoOuter w 0)⁻¹ :=
      (hasFPowerSeriesOnBall_inv_szegoOuter hlog hR₀0 hR₀1).coeff_zero 1
    rw [hc0, mul_inv_cancel₀ (szegoOuter_ne_zero w 0)]
  -- geometric mean is `|D(0)|²`
  have hGMid : szegoGeometricMean circleLebesgue
      ((circleLebesgue.withDensity (fun z => ENNReal.ofReal (W (z : ℂ)))).rnDeriv circleLebesgue)
      = ‖szegoOuter w 0‖ ^ 2 := by
    rw [hw]; exact szegoGeometricMean_withDensity_eq hc hWcont (fun z => hwc _ (hcnorm z))
  have hGMpos : 0 < ‖szegoOuter w 0‖ ^ 2 := pow_pos (norm_pos_iff.mpr (szegoOuter_ne_zero w 0)) 2
  -- the weighted measure is finite (bounded density on a probability space)
  haveI hfin : IsFiniteMeasure (circleLebesgue.withDensity (fun z => ENNReal.ofReal (W (z : ℂ)))) := by
    have hle : ∫⁻ z, ENNReal.ofReal (W (z : ℂ)) ∂circleLebesgue ≤ ENNReal.ofReal C := by
      calc ∫⁻ z, ENNReal.ofReal (W (z : ℂ)) ∂circleLebesgue
          ≤ ∫⁻ _, ENNReal.ofReal C ∂circleLebesgue :=
            lintegral_mono (fun z => ENNReal.ofReal_le_ofReal (hwC _ (hcnorm z)))
        _ = ENNReal.ofReal C * circleLebesgue Set.univ := lintegral_const _
        _ = ENNReal.ofReal C := by rw [measure_univ, mul_one]
    exact isFiniteMeasure_withDensity (ne_of_lt (lt_of_le_of_lt hle ENNReal.ofReal_lt_top))
  -- reduce to the approximation
  refine hasSzegoFirstLimitConclusion_of_approx _ hsupp (fun ε hε => ?_)
  set δ : ℝ := ε / ‖szegoOuter w 0‖ ^ 2 with hδdef
  have hδ : 0 < δ := div_pos hε hGMpos
  obtain ⟨n, hn2, hnbound⟩ := exists_boundary_integral_partialSum_le hc hCpos hlogLI hlog hper hlogφ
    hwcθ hwCθ hR₀0 hR₀1 hsum hδ
  rw [← hp] at hnbound
  set N := n - 2 with hN
  have hNn : N + 2 = n := by omega
  refine ⟨N, fun i => -(starRingEnd ℂ) (szegoOuter w 0 * p.coeff (N + 1 - i)), ?_⟩
  set cc : ℕ → ℂ := fun i => -(starRingEnd ℂ) (szegoOuter w 0 * p.coeff (N + 1 - i)) with hcc
  -- pointwise square-modulus identity `‖revPoly‖² = |D(0)|²·‖Sₙ‖²`
  have hidentity : ∀ u : ℂ, ‖revPoly cc (N + 1) u‖ ^ 2
      = ‖szegoOuter w 0‖ ^ 2 * ‖p.partialSum (N + 2) u‖ ^ 2 := by
    intro u
    rw [hcc, revPoly_eq_szegoOuter_mul_partialSum (R₀ := R₀) w N hb0, norm_mul, mul_pow, ← hp]
  have hFcont : Continuous (fun u => ‖revPoly cc (N + 1) u‖ ^ 2) := by
    have hd : Differentiable ℂ (revPoly cc (N + 1)) := by unfold revPoly; fun_prop
    exact hd.continuous.norm.pow 2
  rw [integral_withDensity_circleLebesgue_eq hWcont hWc0 hFcont, hGMid]
  have hintegrand : ∀ θ, W (circleMap 0 1 θ) * ‖revPoly cc (N + 1) (circleMap 0 1 θ)‖ ^ 2
      = ‖szegoOuter w 0‖ ^ 2 * (‖p.partialSum n (circleMap 0 1 θ)‖ ^ 2 * w θ) := by
    intro θ
    rw [hidentity, hNn]
    have hwθ : w θ = W (circleMap 0 1 θ) := rfl
    rw [hwθ]; ring
  rw [intervalIntegral.integral_congr (fun θ _ => hintegrand θ),
    intervalIntegral.integral_const_mul]
  rw [show (2 * π)⁻¹ * (‖szegoOuter w 0‖ ^ 2 *
        ∫ θ in (0:ℝ)..(2 * π), ‖p.partialSum n (circleMap 0 1 θ)‖ ^ 2 * w θ)
      = ‖szegoOuter w 0‖ ^ 2 * ((2 * π)⁻¹ *
        ∫ θ in (0:ℝ)..(2 * π), ‖p.partialSum n (circleMap 0 1 θ)‖ ^ 2 * w θ) from by ring]
  calc ‖szegoOuter w 0‖ ^ 2 * ((2 * π)⁻¹ *
        ∫ θ in (0:ℝ)..(2 * π), ‖p.partialSum n (circleMap 0 1 θ)‖ ^ 2 * w θ)
      ≤ ‖szegoOuter w 0‖ ^ 2 * (1 + δ) := mul_le_mul_of_nonneg_left hnbound hGMpos.le
    _ = ‖szegoOuter w 0‖ ^ 2 + ε := by
        rw [mul_add, mul_one, hδdef, mul_div_cancel₀ ε (ne_of_gt hGMpos)]

end GaloisForLFunctions.HTGeometry
