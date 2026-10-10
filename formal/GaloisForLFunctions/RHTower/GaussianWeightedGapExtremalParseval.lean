import GaloisForLFunctions.RHTower.GaussianWeightedGapExtremalBessel

/-!
# Parseval identity at the extremal line

Let `G(y) = Σ Λ(n) n^{-1/2} e^{-yn²} − ∫₁^∞ u^{-1/2} e^{-yu²} du`, `Θ = sup Re ρ`,
`g(u) = e^{-(Θ−½)u/2} G(e^{-u})`, and `c_ρ = ½ Γ((ρ−½)/2)` for zero copies on `Re ρ = Θ`.

* **Abstract Parseval** (`tendsto_gaussianWindowAverage_mul_conj_tsum_cexp`).  For an absolutely
  convergent exponential series `S(u) = Σ_q c_q e^{iμ_q u}`, the window means of `|S|²` converge to
  the pair sum `Σ_{μ_q = μ_{q'}} c_q c̄_{q'}`.
* **Extremal Parseval** (`tendsto_extremalGap_meanSquare`).  Unconditionally,
  `T⁻¹ ∫₀^T g(u)² du → [Θ = ½]·|A(½)|² + Re Σ_{Re ρ = Re ρ' = Θ, Im ρ = Im ρ'} c_ρ c̄_{ρ'}`.
  This is a trace identity: the prime-side mean square equals the extremal zero Gram trace plus the
  archimedean bias, with no residual.
* **Gaussian Cramér identity under RH** (`tendsto_centralGap_meanSquare_of_riemannHypothesis`).
  `T⁻¹ ∫₀^T G(e^{-u})² du → |A(½)|² + Re Σ_{Im ρ = Im ρ'} ½Γ((ρ−½)/2)·conj ½Γ((ρ'−½)/2)`.
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower

noncomputable section

open XiAtlasFinitePart

theorem conj_tsum_cexp {ι : Type*} (c : ι → ℂ) (μ : ι → ℝ) (u : ℝ) :
    (starRingEnd ℂ) (∑' q, c q * Complex.exp ((μ q : ℂ) * I * (u : ℂ))) =
      ∑' q, (starRingEnd ℂ) (c q) * Complex.exp (((-(μ q) : ℝ) : ℂ) * I * (u : ℂ)) := by
  rw [Complex.conj_tsum]
  refine tsum_congr fun q => ?_
  rw [map_mul, ← Complex.exp_conj]
  congr 2
  rw [map_mul, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

theorem mul_conj_tsum_cexp_eq {ι : Type*} (c : ι → ℂ) (hc : Summable fun q => ‖c q‖) (μ : ι → ℝ)
    (u : ℝ) :
    (∑' q, c q * Complex.exp ((μ q : ℂ) * I * (u : ℂ))) *
      (starRingEnd ℂ) (∑' q, c q * Complex.exp ((μ q : ℂ) * I * (u : ℂ))) =
      (∑' p : ι × ι, (c p.1 * (starRingEnd ℂ) (c p.2)) *
        Complex.exp (((μ p.1 - μ p.2 : ℝ) : ℂ) * I * (u : ℂ))) *
        Complex.exp (((-(0 : ℝ) : ℝ) : ℂ) * I * (u : ℂ)) := by
  have hexpc : Summable fun q => ‖c q * Complex.exp ((μ q : ℂ) * I * (u : ℂ))‖ := by
    simpa only [norm_mul, norm_cexp_ofReal_mul_I_mul, mul_one] using hc
  have hcexp : Summable fun q =>
      ‖(starRingEnd ℂ) (c q) * Complex.exp (((-(μ q) : ℝ) : ℂ) * I * (u : ℂ))‖ := by
    simpa only [norm_mul, norm_cexp_ofReal_mul_I_mul, mul_one, Complex.norm_conj] using hc
  rw [conj_tsum_cexp, tsum_mul_tsum_of_summable_norm hexpc hcexp]
  rw [neg_zero, Complex.ofReal_zero, zero_mul, zero_mul, Complex.exp_zero, mul_one]
  refine tsum_congr fun p => ?_
  rw [mul_mul_mul_comm, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- **Abstract Parseval.**  For `Σ ‖c_q‖ < ∞`, the window means of `S(u) conj S(u)` converge to the
pair sum `Σ_{μ_q = μ_{q'}} c_q conj c_{q'}`. -/
theorem tendsto_gaussianWindowAverage_mul_conj_tsum_cexp {ι : Type*} [Countable ι] (c : ι → ℂ)
    (hc : Summable fun q => ‖c q‖) (μ : ι → ℝ) :
    Tendsto (gaussianWindowAverage fun u =>
        (∑' q, c q * Complex.exp ((μ q : ℂ) * I * (u : ℂ))) *
          (starRingEnd ℂ) (∑' q, c q * Complex.exp ((μ q : ℂ) * I * (u : ℂ)))) atTop
      (𝓝 (∑' p : ι × ι, if μ p.1 - μ p.2 = 0 then c p.1 * (starRingEnd ℂ) (c p.2) else 0)) := by
  have hcc : Summable fun q => ‖(starRingEnd ℂ) (c q)‖ := by
    simpa only [Complex.norm_conj] using hc
  have hdsum : Summable fun p : ι × ι => ‖c p.1 * (starRingEnd ℂ) (c p.2)‖ :=
    Summable.mul_norm (f := c) (g := fun q => (starRingEnd ℂ) (c q)) hc hcc
  have h := tendsto_gaussianWindowAverage_tsum_cexp (fun p : ι × ι => c p.1 * (starRingEnd ℂ) (c p.2))
    hdsum (fun p : ι × ι => μ p.1 - μ p.2) 0
  beta_reduce at h
  refine h.congr fun T => ?_
  unfold gaussianWindowAverage
  rw [intervalIntegral.integral_congr fun u _ => (mul_conj_tsum_cexp_eq c hc μ u).symm]

/-- **Mean square of an almost-periodic function plus a constant.**  Let `g` be real continuous
with `g + S − K₀ → 0`, where `S(u) = Σ_q c_q e^{iμ_q u}` is absolutely convergent with vanishing
`0`-coefficient.  Then `T⁻¹ ∫₀^T g² → ‖K₀‖² + Re Σ_{μ_q = μ_{q'}} c_q conj c_{q'}`. -/
theorem tendsto_meanSquare_of_tendsto_add_tsum {ι : Type*} [Countable ι] {g : ℝ → ℝ}
    (hg : Continuous g) (c : ι → ℂ) (hc : Summable fun q => ‖c q‖) (μ : ι → ℝ) (K₀ : ℂ)
    (hlim : Tendsto (fun u : ℝ => (g u : ℂ) +
      (∑' q, c q * Complex.exp ((μ q : ℂ) * I * (u : ℂ))) - K₀) atTop (𝓝 0))
    (h0 : (∑' q, if μ q = 0 then c q else 0) = 0) :
    Tendsto (fun T : ℝ => T⁻¹ * ∫ u in (0 : ℝ)..T, g u ^ 2) atTop
      (𝓝 (‖K₀‖ ^ 2 + (∑' p : ι × ι,
        if μ p.1 - μ p.2 = 0 then c p.1 * (starRingEnd ℂ) (c p.2) else 0).re)) := by
  set S : ℝ → ℂ := fun u => ∑' q, c q * Complex.exp ((μ q : ℂ) * I * (u : ℂ)) with hSdef
  have hScont : Continuous S := by
    refine continuous_tsum (fun q => by fun_prop) hc (fun q u => ?_)
    rw [norm_mul, norm_cexp_ofReal_mul_I_mul, mul_one]
  have hSb : ∀ u, ‖S u‖ ≤ ∑' q, ‖c q‖ := fun u => by
    refine (norm_tsum_le_tsum_norm (hc.congr fun q => ?_)).trans (le_of_eq (tsum_congr fun q => ?_))
    · rw [norm_mul, norm_cexp_ofReal_mul_I_mul, mul_one]
    · rw [norm_mul, norm_cexp_ofReal_mul_I_mul, mul_one]
  set B : ℝ → ℂ := fun u => K₀ - S u with hBdef
  have hBcont : Continuous B := continuous_const.sub hScont
  set r : ℝ → ℂ := fun u => (g u : ℂ) + S u - K₀ with hrdef
  have hrcont : Continuous r := ((Complex.continuous_ofReal.comp hg).add hScont).sub continuous_const
  -- the cross terms vanish
  set X : ℝ → ℂ := fun u => r u * (starRingEnd ℂ) (B u) + B u * (starRingEnd ℂ) (r u) +
    r u * (starRingEnd ℂ) (r u) with hXdef
  have hXcont : Continuous X := by
    have hcB : Continuous fun u => (starRingEnd ℂ) (B u) := Complex.continuous_conj.comp hBcont
    have hcr : Continuous fun u => (starRingEnd ℂ) (r u) := Complex.continuous_conj.comp hrcont
    exact ((hrcont.mul hcB).add (hBcont.mul hcr)).add (hrcont.mul hcr)
  have hX0 : Tendsto X atTop (𝓝 0) := by
    set K : ℝ := ‖K₀‖ + ∑' q, ‖c q‖ with hK
    have hBb : ∀ u, ‖B u‖ ≤ K := fun u => (norm_sub_le _ _).trans (by linarith [hSb u])
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hr0 := tendsto_zero_iff_norm_tendsto_zero.1 hlim
    have hbound : Tendsto (fun u => ‖r u‖ * K + K * ‖r u‖ + ‖r u‖ * ‖r u‖) atTop (𝓝 0) := by
      have := ((hr0.mul_const K).add (hr0.const_mul K)).add (hr0.mul hr0)
      simpa using this
    refine squeeze_zero (fun u => norm_nonneg _) (fun u => ?_) hbound
    have h1 := hBb u
    have hn : 0 ≤ ‖r u‖ := norm_nonneg _
    calc ‖X u‖ ≤ ‖r u * (starRingEnd ℂ) (B u)‖ + ‖B u * (starRingEnd ℂ) (r u)‖ +
          ‖r u * (starRingEnd ℂ) (r u)‖ := norm_add₃_le
      _ = ‖r u‖ * ‖B u‖ + ‖B u‖ * ‖r u‖ + ‖r u‖ * ‖r u‖ := by
          simp only [norm_mul, Complex.norm_conj]
      _ ≤ _ := by gcongr
  have hXavg := tendsto_gaussianWindowAverage_of_tendsto_zero hXcont hX0
  -- the averages of `S` and `conj S`
  have hSavg : Tendsto (gaussianWindowAverage S) atTop (𝓝 0) := by
    have h := tendsto_gaussianWindowAverage_tsum_cexp c hc μ 0
    rw [h0] at h
    refine h.congr fun T => ?_
    unfold gaussianWindowAverage
    congr 1
    refine intervalIntegral.integral_congr fun u _ => ?_
    simp only [hSdef, neg_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one]
  have hcSavg : Tendsto (gaussianWindowAverage fun u => (starRingEnd ℂ) (S u)) atTop (𝓝 0) := by
    have hcc : Summable fun q => ‖(starRingEnd ℂ) (c q)‖ := by
      simpa only [Complex.norm_conj] using hc
    have h := tendsto_gaussianWindowAverage_tsum_cexp (fun q => (starRingEnd ℂ) (c q)) hcc
      (fun q => -(μ q)) 0
    have h0' : (∑' q, if -(μ q) = 0 then (starRingEnd ℂ) (c q) else 0) = 0 := by
      have : (∑' q, if -(μ q) = 0 then (starRingEnd ℂ) (c q) else 0) =
          (starRingEnd ℂ) (∑' q, if μ q = 0 then c q else 0) := by
        rw [Complex.conj_tsum]
        refine tsum_congr fun q => ?_
        by_cases hq : μ q = 0
        · rw [if_pos (by rw [hq, neg_zero]), if_pos hq]
        · rw [if_neg (fun h => hq (neg_eq_zero.1 h)), if_neg hq, map_zero]
      rw [this, h0, map_zero]
    beta_reduce at h
    rw [h0'] at h
    refine h.congr fun T => ?_
    unfold gaussianWindowAverage
    congr 1
    refine intervalIntegral.integral_congr fun u _ => ?_
    simp only [hSdef]
    rw [conj_tsum_cexp]
    simp only [neg_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one]
  have hPars := tendsto_gaussianWindowAverage_mul_conj_tsum_cexp c hc μ
  -- assemble: `g² = K₀ conj K₀ − K₀ conj S − S conj K₀ + S conj S + X`
  have hpt : ∀ u : ℝ, ((g u ^ 2 : ℝ) : ℂ) = K₀ * (starRingEnd ℂ) K₀ -
      K₀ * (starRingEnd ℂ) (S u) - (starRingEnd ℂ) K₀ * S u +
      S u * (starRingEnd ℂ) (S u) + X u := by
    intro u
    have hg : (g u : ℂ) = B u + r u := by simp only [hBdef, hrdef]; ring
    have hsq : ((g u ^ 2 : ℝ) : ℂ) = (g u : ℂ) * (starRingEnd ℂ) (g u : ℂ) := by
      rw [Complex.conj_ofReal]; push_cast; ring
    rw [hsq, hg, map_add]
    simp only [hXdef, hBdef, map_sub]
    ring
  have hcomb := ((((tendsto_const_nhds (x := K₀ * (starRingEnd ℂ) K₀)).sub
    (hcSavg.const_mul K₀)).sub (hSavg.const_mul ((starRingEnd ℂ) K₀))).add hPars).add hXavg
  rw [mul_zero, mul_zero, sub_zero, sub_zero, add_zero] at hcomb
  have hre := (Complex.continuous_re.tendsto _).comp hcomb
  have htarget : (K₀ * (starRingEnd ℂ) K₀ + ∑' p : ι × ι,
      (if μ p.1 - μ p.2 = 0 then c p.1 * (starRingEnd ℂ) (c p.2) else 0)).re =
      ‖K₀‖ ^ 2 + (∑' p : ι × ι,
        if μ p.1 - μ p.2 = 0 then c p.1 * (starRingEnd ℂ) (c p.2) else 0).re := by
    rw [Complex.add_re, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  rw [htarget] at hre
  refine hre.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with T hT
  simp only [Function.comp]
  have hlin : gaussianWindowAverage (fun u => ((g u ^ 2 : ℝ) : ℂ)) T =
      K₀ * (starRingEnd ℂ) K₀ -
        K₀ * gaussianWindowAverage (fun u => (starRingEnd ℂ) (S u)) T -
        (starRingEnd ℂ) K₀ * gaussianWindowAverage S T +
        gaussianWindowAverage (fun u => S u * (starRingEnd ℂ) (S u)) T +
        gaussianWindowAverage X T := by
    have hcS : Continuous fun u => (starRingEnd ℂ) (S u) := Complex.continuous_conj.comp hScont
    unfold gaussianWindowAverage
    rw [intervalIntegral.integral_congr fun u _ => hpt u]
    have i1 : IntervalIntegrable (fun u => K₀ * (starRingEnd ℂ) K₀ -
        K₀ * (starRingEnd ℂ) (S u) - (starRingEnd ℂ) K₀ * S u + S u * (starRingEnd ℂ) (S u))
        MeasureTheory.volume 0 T :=
      (((continuous_const.sub (continuous_const.mul hcS)).sub (continuous_const.mul hScont)).add
        (hScont.mul hcS)).intervalIntegrable _ _
    have i2 : IntervalIntegrable (fun u => K₀ * (starRingEnd ℂ) K₀ -
        K₀ * (starRingEnd ℂ) (S u) - (starRingEnd ℂ) K₀ * S u) MeasureTheory.volume 0 T :=
      ((continuous_const.sub (continuous_const.mul hcS)).sub
        (continuous_const.mul hScont)).intervalIntegrable _ _
    have i3 : IntervalIntegrable (fun u => K₀ * (starRingEnd ℂ) K₀ -
        K₀ * (starRingEnd ℂ) (S u)) MeasureTheory.volume 0 T :=
      (continuous_const.sub (continuous_const.mul hcS)).intervalIntegrable _ _
    have i4 : IntervalIntegrable (fun u => S u * (starRingEnd ℂ) (S u)) MeasureTheory.volume 0 T :=
      (hScont.mul hcS).intervalIntegrable _ _
    have i5 : IntervalIntegrable (fun u => (starRingEnd ℂ) K₀ * S u) MeasureTheory.volume 0 T :=
      (continuous_const.mul hScont).intervalIntegrable _ _
    have i6 : IntervalIntegrable (fun u => K₀ * (starRingEnd ℂ) (S u)) MeasureTheory.volume 0 T :=
      (continuous_const.mul hcS).intervalIntegrable _ _
    have i7 : IntervalIntegrable X MeasureTheory.volume 0 T := hXcont.intervalIntegrable _ _
    rw [intervalIntegral.integral_add i1 i7, intervalIntegral.integral_add i2 i4,
      intervalIntegral.integral_sub i3 i5, intervalIntegral.integral_sub intervalIntegrable_const i6,
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, sub_zero, Complex.real_smul]
    have hT0 : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hT.ne'
    field_simp
  have hreal : T⁻¹ * ∫ u in (0 : ℝ)..T, g u ^ 2 =
      (gaussianWindowAverage (fun u => ((g u ^ 2 : ℝ) : ℂ)) T).re := by
    unfold gaussianWindowAverage
    rw [intervalIntegral.integral_ofReal, ← Complex.ofReal_inv, ← Complex.ofReal_mul,
      Complex.ofReal_re]
  rw [hreal, hlin]

theorem tsum_ite_halfOrdinate_eq_zero (c : XiZeroCopy → ℂ) :
    (∑' q : XiZeroCopy, if xiZeroHalfOrdinate q = 0 then c q else 0) = 0 := by
  have hall : ∀ q : XiZeroCopy, ¬ xiZeroHalfOrdinate q = 0 := by
    intro q hq
    rw [xiZeroHalfOrdinate] at hq
    have him : (xiZero q).im = 0 := by linarith
    exact xi_ne_zero_of_abs_im_le_one (by rw [him, abs_zero]; norm_num) (xi_xiZero q)
  simp [hall]

/-- **Extremal Parseval (unconditional).**  With `c_ρ = ½ Γ((ρ−½)/2)` on `Re ρ = Θ` (and `0`
elsewhere), `T⁻¹ ∫₀^T g² → ‖[Θ = ½] A(½)‖² + Re Σ_{Im ρ = Im ρ'} c_ρ conj c_{ρ'}`. -/
theorem tendsto_extremalGap_meanSquare :
    Tendsto (fun T : ℝ => T⁻¹ * ∫ u in (0 : ℝ)..T,
        (Real.exp (-((xiZeroAbscissa - 1 / 2) * u / 2)) *
          (gaussianWeightedPrimeMass (1 / 2) (Real.exp (-u)) -
            gaussianWeightedContinuumMass (1 / 2) (Real.exp (-u)))) ^ 2) atTop
      (𝓝 (‖(((if xiZeroAbscissa = 1 / 2 then 1 else 0 : ℝ)) : ℂ) *
          gaussianArchimedeanCurrent ((1 / 2 : ℝ) : ℂ)‖ ^ 2 +
        (∑' p : XiZeroCopy × XiZeroCopy,
          if xiZeroHalfOrdinate p.1 - xiZeroHalfOrdinate p.2 = 0 then
            (if (xiZero p.1).re = xiZeroAbscissa then zeroBohrAmplitude p.1 else 0) *
              (starRingEnd ℂ) (if (xiZero p.2).re = xiZeroAbscissa then zeroBohrAmplitude p.2 else 0)
          else 0).re)) := by
  have hGcont : Continuous fun u : ℝ => gaussianWeightedPrimeMass (1 / 2) (Real.exp (-u)) -
      gaussianWeightedContinuumMass (1 / 2) (Real.exp (-u)) := by
    have h := continuous_gaussianBudgetProfile (σ := 1 / 2) (by norm_num) (-1) 0 0
    have heq : (fun u : ℝ => gaussianWeightedPrimeMass (1 / 2) (Real.exp (-u)) -
        gaussianWeightedContinuumMass (1 / 2) (Real.exp (-u))) =
        gaussianBudgetProfile (-1) (1 / 2) 0 0 := by
      funext u; simp [gaussianBudgetProfile]
    rw [heq]; exact h
  have hgcont : Continuous fun u : ℝ => Real.exp (-((xiZeroAbscissa - 1 / 2) * u / 2)) *
      (gaussianWeightedPrimeMass (1 / 2) (Real.exp (-u)) -
        gaussianWeightedContinuumMass (1 / 2) (Real.exp (-u))) :=
    (by fun_prop : Continuous fun u : ℝ =>
      Real.exp (-((xiZeroAbscissa - 1 / 2) * u / 2))).mul hGcont
  have hcsum : Summable fun q : XiZeroCopy =>
      ‖if (xiZero q).re = xiZeroAbscissa then zeroBohrAmplitude q else 0‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun q => by split_ifs <;> simp) summable_norm_zeroBohrAmplitude
  exact tendsto_meanSquare_of_tendsto_add_tsum hgcont _ hcsum xiZeroHalfOrdinate _
    tendsto_extremalGap_add_series (tsum_ite_halfOrdinate_eq_zero _)

/-- **Gaussian Cramér identity under RH.**
`T⁻¹ ∫₀^T G(e^{-u})² du → ‖A(½)‖² + Re Σ_{Im ρ = Im ρ'} ½Γ((ρ−½)/2) conj ½Γ((ρ'−½)/2)`. -/
theorem tendsto_centralGap_meanSquare_of_riemannHypothesis (hRH : RiemannHypothesis) :
    Tendsto (fun T : ℝ => T⁻¹ * ∫ u in (0 : ℝ)..T,
        (gaussianWeightedPrimeMass (1 / 2) (Real.exp (-u)) -
          gaussianWeightedContinuumMass (1 / 2) (Real.exp (-u))) ^ 2) atTop
      (𝓝 (‖gaussianArchimedeanCurrent ((1 / 2 : ℝ) : ℂ)‖ ^ 2 +
        (∑' p : XiZeroCopy × XiZeroCopy,
          if xiZeroHalfOrdinate p.1 - xiZeroHalfOrdinate p.2 = 0 then
            zeroBohrAmplitude p.1 * (starRingEnd ℂ) (zeroBohrAmplitude p.2) else 0).re)) := by
  have hθ : ∀ ρ : ℂ, xi ρ = 0 → ρ.re ≤ 1 / 2 := fun ρ hρ => by
    by_contra h
    push Not at h
    exact (rh_iff_xi_ne_zero_right.mp hRH) ρ (mem_rightHalf.mpr h) hρ
  have hre : ∀ q : XiZeroCopy, (xiZero q).re = 1 / 2 :=
    fun q => xiZeroCopy_re_eq_half_of_riemannHypothesis hRH q
  have hGcont : Continuous fun u : ℝ => gaussianWeightedPrimeMass (1 / 2) (Real.exp (-u)) -
      gaussianWeightedContinuumMass (1 / 2) (Real.exp (-u)) := by
    have h := continuous_gaussianBudgetProfile (σ := 1 / 2) (by norm_num) (-1) 0 0
    have heq : (fun u : ℝ => gaussianWeightedPrimeMass (1 / 2) (Real.exp (-u)) -
        gaussianWeightedContinuumMass (1 / 2) (Real.exp (-u))) =
        gaussianBudgetProfile (-1) (1 / 2) 0 0 := by
      funext u; simp [gaussianBudgetProfile]
    rw [heq]; exact h
  have hlim := tendsto_weightedGap_add_extremalSeries hθ
  have hlim' : Tendsto (fun u : ℝ => ((gaussianWeightedPrimeMass (1 / 2) (Real.exp (-u)) -
      gaussianWeightedContinuumMass (1 / 2) (Real.exp (-u)) : ℝ) : ℂ) +
      (∑' q : XiZeroCopy, zeroBohrAmplitude q *
        Complex.exp ((xiZeroHalfOrdinate q : ℂ) * I * (u : ℂ))) -
      gaussianArchimedeanCurrent ((1 / 2 : ℝ) : ℂ)) atTop (𝓝 0) := by
    refine hlim.congr fun u => ?_
    simp only [sub_self, zero_mul, zero_div, neg_zero, Real.exp_zero, one_mul, if_true,
      Complex.ofReal_one]
    congr 2
    exact tsum_congr fun q => by rw [if_pos (hre q)]
  exact tendsto_meanSquare_of_tendsto_add_tsum hGcont zeroBohrAmplitude
    summable_norm_zeroBohrAmplitude xiZeroHalfOrdinate _ hlim' (tsum_ite_halfOrdinate_eq_zero _)

end

end RHTower
