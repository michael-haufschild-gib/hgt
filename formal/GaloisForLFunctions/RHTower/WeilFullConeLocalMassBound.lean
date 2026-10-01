import GaloisForLFunctions.RHTower.WeilFullConeHorizontalPotential
import GaloisForLFunctions.RHTower.WeilPositiveShortIntervalSupport

/-!
# Local mass of the boundary measure of a Weil-positive system

For a full-cone Weil-positive `lam`, the boundary measure `μ_lam` carries at most logarithmic
mass on every unit window:

`μ_lam([t − 1, t + 1]) ≤ 2 Re Φ_lam(3/2 + it) ≤ C log(|t| + 3)`

(`boundaryMeasure_Icc_le`, `exists_boundaryMeasure_Icc_le_log`).  This is the analogue, for every
producer, of the unit-window zero count `N(t + 1) − N(t − 1) = O(log t)` of `ζ`.  In particular
every atom of `μ_lam` is `O(log |t|)`.

**Proof.**  On the window, `1 ≤ 2/(1 + (r − t)²)`, and
`∫ dμ_lam(r)/(1 + (r − t)²) = Re Φ_lam(3/2 + it)` by the Poisson representation at abscissa `3/2`.
At abscissa `3/2`, `Φ_lam = A + 1/(s−1) − Σ lam(n) n^{−s}` is bounded by the logarithmic growth of
the archimedean datum `A` plus `2 + Σ |lam(n)| n^{−3/2}`.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real NNReal ENNReal

noncomputable section

namespace RHTower.WeilSpectral

open WeilHerglotz

/-- **Unit-window mass bound.**  `μ_lam([t − 1, t + 1]) ≤ 2 Re Φ_lam(3/2 + it)`. -/
theorem boundaryMeasure_Icc_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (t : ℝ) :
    boundaryMeasure hW (Icc (t - 1) (t + 1)) ≤
      ENNReal.ofReal (2 * (weilFunction lam ((3 / 2 : ℂ) + t * I)).re) := by
  set s : ℂ := (3 / 2 : ℂ) + t * I with hsdef
  have hs : 1 < s.re := by rw [hsdef]; simp; norm_num
  have hrep := lintegral_poissonDensity_eq hW hs
  have hw : (s - 1 / 2) = (1 : ℂ) + t * I := by rw [hsdef]; ring
  have hwre : (s - 1 / 2).re = 1 := by rw [hw]; simp
  rw [hwre, div_one] at hrep
  have hpt : ∀ r ∈ Icc (t - 1) (t + 1), (1 : ℝ≥0∞) ≤ 2 * poissonDensity (s - 1 / 2) r := by
    intro r hr
    rw [← ENNReal.ofReal_toReal (poissonDensity_ne_top _ r), poissonDensity_toReal, hwre, hw]
    have him : ((1 : ℂ) + t * I).im = t := by simp
    rw [him]
    have hx : (r - t) ^ 2 ≤ 1 := by
      have h1 : |r - t| ≤ 1 := abs_le.mpr ⟨by linarith [hr.1], by linarith [hr.2]⟩
      have := pow_le_pow_left₀ (abs_nonneg _) h1 2
      rwa [sq_abs, one_pow] at this
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num, ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    rw [one_pow, mul_one_div, le_div_iff₀ (by positivity)]
    linarith
  calc boundaryMeasure hW (Icc (t - 1) (t + 1))
      = ∫⁻ r in Icc (t - 1) (t + 1), 1 ∂boundaryMeasure hW := by
        rw [setLIntegral_const, one_mul]
    _ ≤ ∫⁻ r in Icc (t - 1) (t + 1), 2 * poissonDensity (s - 1 / 2) r ∂boundaryMeasure hW :=
        setLIntegral_mono' measurableSet_Icc hpt
    _ ≤ ∫⁻ r, 2 * poissonDensity (s - 1 / 2) r ∂boundaryMeasure hW := setLIntegral_le_lintegral _ _
    _ = 2 * ENNReal.ofReal (weilFunction lam s).re := by
        rw [lintegral_const_mul _ (measurable_poissonDensity _), hrep]
    _ = ENNReal.ofReal (2 * (weilFunction lam s).re) := by
        rw [ENNReal.ofReal_mul (by norm_num)]
        norm_num

/-- **Logarithmic local mass.**  There is `C` with `μ_lam([t − 1, t + 1]) ≤ C log(|t| + 3)` for
every `t`. -/
theorem exists_boundaryMeasure_Icc_le_log {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      boundaryMeasure hW (Icc (t - 1) (t + 1)) ≤ ENNReal.ofReal (C * Real.log (|t| + 3)) := by
  obtain ⟨K, hK, hAK⟩ := RHTower.exists_log_bound_zetaArchimedeanDatum
  have hsum := WeilMeanSquare.summable_abs_div_rpow_of_weilPositiveFull hW
    (σ := 3 / 2) (by norm_num)
  set L : ℝ := ∑' n : ℕ, |lam n| / (n : ℝ) ^ (3 / 2 : ℝ) with hL
  have hL0 : 0 ≤ L := tsum_nonneg fun n => by positivity
  have hlog1 : ∀ t : ℝ, 1 ≤ Real.log (|t| + 3) := by
    intro t
    rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    linarith [abs_nonneg t]
  refine ⟨2 * (K + 2 + L), by positivity, fun t => (boundaryMeasure_Icc_le hW t).trans ?_⟩
  apply ENNReal.ofReal_le_ofReal
  set s : ℂ := (3 / 2 : ℂ) + t * I with hsdef
  have hsre : s.re = 3 / 2 := by rw [hsdef]; simp
  have hsim : s.im = t := by rw [hsdef]; simp
  -- the three parts of `Φ_lam(s)`
  have hA : ‖RHTower.zetaArchimedeanDatum s‖ ≤ K * Real.log (|t| + 3) := by
    have := hAK s (by rw [hsre]; norm_num) (by rw [hsre]; norm_num)
    rwa [hsim] at this
  have hpole : ‖1 / (s - 1)‖ ≤ 2 := by
    have h := Complex.abs_re_le_norm (s - 1)
    rw [Complex.sub_re, hsre, Complex.one_re] at h
    have h' : (1 : ℝ) / 2 ≤ ‖s - 1‖ := by norm_num at h ⊢; linarith
    rw [norm_div, norm_one]
    have := one_div_le_one_div_of_le (by norm_num) h'
    norm_num at this ⊢
    linarith
  have hD : ‖LSeries (lamC lam) s‖ ≤ L := by
    have hbound : ∀ n : ℕ, ‖LSeries.term (lamC lam) s n‖ ≤ |lam n| / (n : ℝ) ^ (3 / 2 : ℝ) := by
      intro n
      rw [LSeries.norm_term_eq]
      split_ifs with hn
      · positivity
      · rw [hsre]
        unfold lamC
        rw [Complex.norm_real, Real.norm_eq_abs]
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        split_ifs
        · exact le_rfl
        · simp
    have hsn : Summable fun n => ‖LSeries.term (lamC lam) s n‖ :=
      hsum.of_nonneg_of_le (fun _ => norm_nonneg _) hbound
    exact (norm_tsum_le_tsum_norm hsn).trans (hsn.tsum_le_tsum hbound hsum)
  have hsplit : weilFunction lam s = RHTower.zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (lamC lam) s := by
    rw [weilFunction, RHTower.zetaArchimedeanDatum]
  have hre : (weilFunction lam s).re ≤ K * Real.log (|t| + 3) + 2 + L := by
    rw [hsplit]
    have h1 := Complex.re_le_norm (RHTower.zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (lamC lam) s)
    have h2 := norm_sub_le (RHTower.zetaArchimedeanDatum s + 1 / (s - 1)) (LSeries (lamC lam) s)
    have h3 := norm_add_le (RHTower.zetaArchimedeanDatum s) (1 / (s - 1))
    linarith
  have hl := hlog1 t
  nlinarith

end RHTower.WeilSpectral

end
