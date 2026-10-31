import GaloisForLFunctions.RenormalizedIntersectionTheory.TheKunnethInertiaLaw
import GaloisForLFunctions.ArithmeticOrientationGeometry.TheSplineOrbitDecidesTheCriticalLine
import GaloisForLFunctions.ArithmeticOrientationGeometry.TheOrientationOfACycle
import GaloisForLFunctions.SquareRootThreshold.LagRateBoundsTheDeBruijnNewmanHeatTime

/-!
# The Künneth square of Weil's kernel is RH

Weil's kernel `K_ζ(u) = W(B, B(· − log u))` on `ℚ_{>0}` (cubic spline `B`) is the value at
`t = −log u` of the exponential sum `F(t) = Σ_ρ e^{t(ρ−1/2)} w_ρ` over the zeros
(`zetaKernel_eq_splineSeries`), whose real part is the orbit correlation of the spline cycle
(`orbitCorr_splineCycle_eq`).

* **Continuity** (`continuous_splineSeries`): the zeros lie in the strip, so on `|t| ≤ R` every term
  is at most `e^{R/2} |w_ρ|`, a summable majorant.
* **Weil's kernel has a positive square** (`riemannHypothesis_of_posIndex_zetaKernel_eq_zero`): if
  `K_ζ` had none, `−K_ζ` would be positive definite, hence bounded by `−K_ζ(1)`; the scales `log q`,
  `q ∈ ℚ_{>0}`, are dense, so `F` and the spline orbit would be bounded, which is zero width `0`.
* **The Künneth square is RH** (`riemannHypothesis_iff_negIndex_kunnethZeta_eq_zero`):
  `K_ζ ⊠ K_ζ` on `ℚ_{>0} × ℚ_{>0}` is positive definite iff RH holds.

With the inertia law (`TheKunnethInertiaLaw`) the sign of the Künneth square is the sign of `K_ζ`:
a tensor square of the scaling surface does not soften the problem, and any finite index for it
already forces the zeros seen by the square.
-/

open Complex Filter Topology
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HeckeKreinToeplitz
  GaloisForLFunctions.ArithmeticOrientationGeometry GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Zeta23
open GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge (cubicSpline contDiff_cubicSpline
  hasCompactSupport_cubicSpline)

noncomputable section

namespace GaloisForLFunctions.RenormalizedIntersectionTheory

/-- The zero-side exponential sum `F(t) = Σ_ρ e^{t(ρ−1/2)} w_ρ` of the cubic spline. -/
def splineSeries (t : ℝ) : ℂ :=
  ∑' τ : zetaZeroConfig.carrier, cexp ((t : ℂ) * ((τ : ℂ) - 1 / 2)) *
    zetaZeroConfig.Wsummand (cx cubicSpline) (cx cubicSpline) τ

theorem zetaKernel_eq_splineSeries (u : HeckeLattice) :
    zetaKernel u = splineSeries (-Real.log ((u : ℚ) : ℝ)) := by
  rw [zetaKernel, orbitKernel_eq, W_shiftTest_shiftTest, scale_heckeLogScale, splineSeries]
  refine tsum_congr fun τ => ?_
  congr 2
  push_cast
  ring

theorem orbitCorr_splineCycle_eq (t : ℝ) :
    zetaScalingDatum.orbitCorr splineCycle t = (splineSeries t).re := by
  rw [← configScalingDatum_zeta_orbitCorr, configScalingDatum_orbitCorr_eq]
  rfl

/-- **The spline series is continuous.** -/
theorem continuous_splineSeries : Continuous splineSeries := by
  have hsum := summable_norm_Wsummand zetaZeroConfig SquareRootThreshold.temperedConfig_zetaZeroConfig
    (cx_contDiff contDiff_cubicSpline) (cx_hasCompactSupport hasCompactSupport_cubicSpline)
    (cx_contDiff contDiff_cubicSpline) (cx_hasCompactSupport hasCompactSupport_cubicSpline)
  rw [continuous_iff_continuousAt]
  intro t₀
  set R := |t₀| + 1
  have hon : ContinuousOn splineSeries (Metric.ball t₀ 1) := by
    refine continuousOn_tsum (u := fun τ => Real.exp (R / 2) *
        ‖zetaZeroConfig.Wsummand (cx cubicSpline) (cx cubicSpline) τ‖)
      (fun τ => by fun_prop) (hsum.mul_left _) fun τ t ht => ?_
    have hstrip := zetaZeroConfig.strip τ.1 τ.2
    have ht' : |t| ≤ R := by
      have := Metric.mem_ball.mp ht
      rw [Real.dist_eq] at this
      have := abs_sub_abs_le_abs_sub t t₀
      simp only [R]; linarith
    rw [norm_mul, Complex.norm_exp]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    refine Real.exp_le_exp.mpr ?_
    have hre : ((t : ℂ) * ((τ : ℂ) - 1 / 2)).re = t * ((τ : ℂ).re - 1 / 2) := by simp
    rw [hre]
    have h1 : |(τ : ℂ).re - 1 / 2| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [hstrip.1], by linarith [hstrip.2]⟩
    calc t * ((τ : ℂ).re - 1 / 2) ≤ |t * ((τ : ℂ).re - 1 / 2)| := le_abs_self _
      _ = |t| * |(τ : ℂ).re - 1 / 2| := abs_mul _ _
      _ ≤ R * (1 / 2) := mul_le_mul ht' h1 (abs_nonneg _) (by positivity)
      _ = R / 2 := by ring
  exact hon.continuousAt (Metric.ball_mem_nhds t₀ one_pos)

/-- **Weil's kernel has a positive square**, unless RH holds. -/
theorem riemannHypothesis_of_posIndex_zetaKernel_eq_zero (h : posIndex zetaKernel = 0) :
    RiemannHypothesis := by
  -- `−K_ζ` is positive definite, hence bounded
  have hherm : IsHermKernel fun u => -zetaKernel u := fun u => by
    simp only [isHermKernel_zetaKernel u, map_neg]
  have hpd : IsPosDefKernel fun u => -zetaKernel u := (isPosDefKernel_iff hherm).mpr h
  set C := (-zetaKernel 1).re
  have hbd : ∀ u : HeckeLattice, ‖splineSeries (-Real.log ((u : ℚ) : ℝ))‖ ≤ C := fun u => by
    rw [← zetaKernel_eq_splineSeries, ← norm_neg]
    exact hpd.norm_le u
  -- density of the rational scales extends the bound to every real scale
  have hall : ∀ t : ℝ, ‖splineSeries t‖ ≤ C := by
    intro t
    by_contra hgt
    push Not at hgt
    have hev : ∀ᶠ s in 𝓝 t, C < ‖splineSeries s‖ :=
      (continuous_splineSeries.norm.continuousAt).eventually (lt_mem_nhds hgt)
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show Real.exp (-t) < Real.exp (-t + δ) by
      exact Real.exp_lt_exp.mpr (by linarith))
    have hqpos : (0 : ℝ) < q := lt_trans (Real.exp_pos _) hq1
    have hq0 : (0 : ℚ) < q := by exact_mod_cast hqpos
    have hlog1 : -t < Real.log q := by
      rw [Real.lt_log_iff_exp_lt hqpos]; exact hq1
    have hlog2 : Real.log q < -t + δ := by
      rw [Real.log_lt_iff_lt_exp hqpos]; exact hq2
    have hd : dist (-Real.log ((⟨q, hq0⟩ : HeckeLattice) : ℚ)) t < δ := by
      rw [Real.dist_eq]
      show |-Real.log (q : ℝ) - t| < δ
      rw [abs_lt]; constructor <;> linarith
    exact absurd (hbd ⟨q, hq0⟩) (not_le.mpr (hball hd))
  -- bounded spline orbit = zero width zero
  have hrate : SquareRootThreshold.zetaZeroWidth ≤ 0 := by
    refine (zeta_splineOrbit_rate_iff_zetaZeroWidth_le le_rfl).mp ⟨C, fun t _ => ?_⟩
    rw [zero_mul, Real.exp_zero, mul_one, orbitCorr_splineCycle_eq]
    exact (Complex.abs_re_le_norm _).trans (hall t)
  exact SquareRootThreshold.riemannHypothesis_iff_zetaZeroWidth_eq_zero.mpr
    (le_antisymm hrate SquareRootThreshold.zetaZeroWidth_nonneg)

/-- **The Künneth square of Weil's kernel is positive definite iff RH holds.** -/
theorem riemannHypothesis_iff_negIndex_kunnethZeta_eq_zero :
    RiemannHypothesis ↔ negIndex kunnethZeta = 0 := by
  rw [negIndex_kunnethZeta_eq_zero_iff]
  exact ⟨Or.inl, fun h => h.elim id riemannHypothesis_of_posIndex_zetaKernel_eq_zero⟩

end GaloisForLFunctions.RenormalizedIntersectionTheory
