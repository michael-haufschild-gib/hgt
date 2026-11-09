import GaloisForLFunctions.SurfaceOfSpecZ.TheLowerSideSeesTheSignOfTheTopLayer

/-!
# Almost all primes suffice

A sampling weight stays sampling when a part of relative Abel density zero is removed
(`SamplingWeight.of_le_of_tendsto_ratio`): if `0 ≤ w' ≤ w` and
`Σ (w − w')(n) n^{−σ} / Σ w(n) n^{−σ} → 0` as `σ ↓ 1`, then `w'` is sampling. The removed part may
have a divergent series; only its relative size matters.

Hence (`onLine_of_bddBelow_primes_off_null_of_max`) a lower bound on the spline traces at the primes
outside an exceptional set `E` with `Σ_{p ∈ E} log p · p^{−σ} = o(Σ_p log p · p^{−σ})` decides the line
for every tempered configuration without real zeros and with an attained maximal real part; for `ζ` a
lower bound off such a set leaves no deepest off-line zero
(`exists_re_gt_of_bddBelow_primes_off_null`). The count of the prime planes is needed only for a set
of primes of relative logarithmic density one.
-/

open Complex Filter Topology

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri SquareRootThreshold Zeta23
open ArithmeticFunction

/-- **Removing a part of relative density zero keeps a weight sampling.** -/
theorem SamplingWeight.of_le_of_tendsto_ratio {w w' : ℕ → ℝ} (hw : SamplingWeight w)
    (h0 : ∀ j, 0 ≤ w' j) (hle : ∀ j, w' j ≤ w j)
    (hrat : Tendsto (fun σ => wSum (fun j => w j - w' j) σ / wSum w σ) (𝓝[>] 1) (𝓝 0)) :
    SamplingWeight w' := by
  set h : ℕ → ℝ := fun j => w j - w' j with hhdef
  have hh0 : ∀ j, 0 ≤ h j := fun j => sub_nonneg.mpr (hle j)
  have hhw : ∀ j, h j ≤ w j := fun j => by have := h0 j; simp only [hhdef]; linarith
  have hw's : ∀ σ : ℝ, 1 < σ → Summable fun j : ℕ => w' j * ((j : ℝ) + 1) ^ (-σ) := fun σ hσ =>
    Summable.of_nonneg_of_le (fun j => mul_nonneg (h0 j) (by positivity))
      (fun j => mul_le_mul_of_nonneg_right (hle j) (by positivity)) (hw.summable hσ)
  have hhs : ∀ σ : ℝ, 1 < σ → Summable fun j : ℕ => h j * ((j : ℝ) + 1) ^ (-σ) := fun σ hσ =>
    Summable.of_nonneg_of_le (fun j => mul_nonneg (hh0 j) (by positivity))
      (fun j => mul_le_mul_of_nonneg_right (hhw j) (by positivity)) (hw.summable hσ)
  have hsub : ∀ σ : ℝ, 1 < σ → wSum w' σ = wSum w σ - wSum h σ := by
    intro σ hσ
    rw [wSum, wSum, wSum, ← (hw.summable hσ).tsum_sub (hhs σ hσ)]
    refine tsum_congr fun j => ?_
    simp only [hhdef]; ring
  have hhalf : ∀ᶠ σ in 𝓝[>] (1 : ℝ), wSum h σ ≤ wSum w σ / 2 := by
    filter_upwards [hrat.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
      hw.eventually_pos] with σ hσ hV
    rw [div_lt_iff₀ hV] at hσ
    linarith
  have hw'half : ∀ᶠ σ in 𝓝[>] (1 : ℝ), wSum w σ / 2 ≤ wSum w' σ := by
    filter_upwards [hhalf, self_mem_nhdsWithin] with σ hh hσ
    rw [hsub σ hσ]; linarith
  have hatTop : Tendsto (wSum w') (𝓝[>] 1) atTop :=
    tendsto_atTop_mono' _ hw'half (hw.tendsto_atTop.atTop_div_const (by norm_num))
  refine ⟨h0, hw's, hatTop, fun c hc hre => ?_⟩
  have hsubC : ∀ σ : ℝ, 1 < σ →
      wSeries w' ((σ : ℂ) + c) = wSeries w ((σ : ℂ) + c) - wSeries h ((σ : ℂ) + c) := by
    intro σ hσ
    have hs : 1 < ((σ : ℂ) + c).re := by simp; linarith
    rw [wSeries, wSeries, wSeries, ← (hw.summable_series hs).tsum_sub
      (hw.summable_series_of_le hh0 hhw hs)]
    refine tsum_congr fun j => ?_
    simp only [hhdef]; push_cast; ring
  have hnormh : ∀ σ : ℝ, 1 < σ → ‖wSeries h ((σ : ℂ) + c)‖ ≤ wSum h σ := by
    intro σ hσ
    have hs : 1 < ((σ : ℂ) + c).re := by simp; linarith
    calc ‖wSeries h ((σ : ℂ) + c)‖ ≤ ∑' j : ℕ, ‖(h j : ℂ) * ((j : ℂ) + 1) ^ (-((σ : ℂ) + c))‖ :=
          norm_tsum_le_tsum_norm (hw.summable_series_of_le hh0 hhw hs).norm
      _ = wSum h ((σ : ℂ) + c).re := by
          rw [wSum]
          refine tsum_congr fun j => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hh0 j),
            norm_natCast_add_one_cpow, Complex.neg_re]
      _ ≤ wSum h σ := by
          refine Summable.tsum_le_tsum (fun j => ?_) (hhs _ hs) (hhs σ hσ)
          exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le
            (by linarith [Nat.cast_nonneg (α := ℝ) j]) (by simp; linarith)) (hh0 j)
  have hrel : Tendsto (fun σ : ℝ => ‖wSeries w ((σ : ℂ) + c)‖ / wSum w σ) (𝓝[>] 1) (𝓝 0) := by
    have := (hw.tendsto_off c hc hre).norm
    rw [norm_zero] at this
    refine this.congr' ?_
    filter_upwards [hw.eventually_pos] with σ hV
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hV]
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    (by simpa using (hrel.const_mul 2).add (hrat.const_mul 2))
  filter_upwards [self_mem_nhdsWithin, hw'half, hw.eventually_pos] with σ hσ hw' hV
  have hσ1 : 1 < σ := hσ
  have hw'pos : 0 < wSum w' σ := by linarith
  rw [hsubC σ hσ1, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hw'pos,
    div_le_iff₀ hw'pos]
  have hn := norm_sub_le (wSeries w ((σ : ℂ) + c)) (wSeries h ((σ : ℂ) + c))
  have hnh := hnormh σ hσ1
  have hge : (2 * (‖wSeries w ((σ : ℂ) + c)‖ / wSum w σ) + 2 * (wSum h σ / wSum w σ)) *
      (wSum w σ / 2) = ‖wSeries w ((σ : ℂ) + c)‖ + wSum h σ := by field_simp
  have hnn : 0 ≤ 2 * (‖wSeries w ((σ : ℂ) + c)‖ / wSum w σ) + 2 * (wSum h σ / wSum w σ) := by
    have : 0 ≤ wSum h σ := tsum_nonneg fun j => mul_nonneg (hh0 j) (by positivity)
    positivity
  nlinarith [mul_le_mul_of_nonneg_left hw' hnn]

/-- The primes off an exceptional set `E`: `log p · 1_{p ∉ E}` at `n = j + 1`. -/
def primeOffWeight (E : Set ℕ) [DecidablePred (· ∈ E)] (j : ℕ) : ℝ :=
  if (j + 1).Prime ∧ (j + 1) ∉ E then Λ (j + 1) else 0

/-- The primes, `log p · 1_{p prime}`, are sampling: they differ from `Λ` by the prime powers
`pᵏ`, `k ≥ 2`, whose series converges at `1`. -/
theorem samplingWeight_primeWeight : SamplingWeight primeWeight := by
  refine samplingWeight_vonMangoldt.of_le_of_summable_sub (fun j => ?_) (fun j => ?_) ?_
  · unfold primeWeight; split_ifs
    · exact vonMangoldt_nonneg
    · exact le_rfl
  · unfold primeWeight; split_ifs
    · exact le_rfl
    · exact vonMangoldt_nonneg
  · refine (summable_higherWeight (by norm_num : (1 : ℝ) / 2 < 1)).congr fun j => ?_
    unfold primeWeight higherWeight; split_ifs <;> ring

/-- **The primes off a set of relative density zero are sampling.** -/
theorem samplingWeight_primeOff (E : Set ℕ) [DecidablePred (· ∈ E)]
    (hE : Tendsto (fun σ => wSum (fun j => primeWeight j - primeOffWeight E j) σ /
      wSum primeWeight σ) (𝓝[>] 1) (𝓝 0)) :
    SamplingWeight (primeOffWeight E) := by
  refine samplingWeight_primeWeight.of_le_of_tendsto_ratio (fun j => ?_) (fun j => ?_) hE
  · unfold primeOffWeight; split_ifs
    · exact vonMangoldt_nonneg
    · exact le_rfl
  · unfold primeOffWeight primeWeight; split_ifs with h1 h2
    · exact le_rfl
    · exact absurd h1.1 h2
    · exact vonMangoldt_nonneg
    · exact le_rfl

theorem bound_of_primeOffWeight_ne_zero {E : Set ℕ} [DecidablePred (· ∈ E)] {Z : ZeroConfig}
    {P : ℝ → Prop}
    (hK : ∀ p : ℕ, p.Prime → p ∉ E → P (2 * (lagStructure Z (boxSpline 1 3) (Real.log p)).re)) :
    ∀ j : ℕ, primeOffWeight E j ≠ 0 →
      P (2 * (lagStructure Z (boxSpline 1 3) (Real.log (j + 1))).re) := by
  intro j hj
  unfold primeOffWeight at hj
  split_ifs at hj with h
  · have := hK (j + 1) h.1 h.2
    push_cast at this
    exact this
  · exact absurd rfl hj

/-- **Almost all primes sample every top layer.** -/
theorem onLine_of_bddBelow_primes_off_null_of_max (E : Set ℕ) [DecidablePred (· ∈ E)]
    (hE : Tendsto (fun σ => wSum (fun j => primeWeight j - primeOffWeight E j) σ /
      wSum primeWeight σ) (𝓝[>] 1) (𝓝 0))
    (Z : ZeroConfig) (hZ : TemperedConfig Z) (hnoreal : ∀ ρ ∈ Z.carrier, ρ.im ≠ 0) {ρ₀ : ℂ}
    (hρ₀ : ρ₀ ∈ Z.carrier) (hmax : ∀ ρ ∈ Z.carrier, ρ.re ≤ ρ₀.re) {K : ℝ}
    (hK : ∀ p : ℕ, p.Prime → p ∉ E → -K ≤ 2 * (lagStructure Z (boxSpline 1 3) (Real.log p)).re) :
    ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2 :=
  onLine_of_bddBelow_of_samplingWeight (samplingWeight_primeOff E hE) Z hZ hnoreal hρ₀ hmax
    (bound_of_primeOffWeight_ne_zero (P := fun x => -K ≤ x) hK)

/-- **For `ζ`, a lower bound at almost all primes leaves no deepest off-line zero.** -/
theorem exists_re_gt_of_bddBelow_primes_off_null (E : Set ℕ) [DecidablePred (· ∈ E)]
    (hE : Tendsto (fun σ => wSum (fun j => primeWeight j - primeOffWeight E j) σ /
      wSum primeWeight σ) (𝓝[>] 1) (𝓝 0)) {K : ℝ}
    (hK : ∀ p : ℕ, p.Prime → p ∉ E →
      -K ≤ 2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log p)).re)
    {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ zetaZeroConfig.carrier) (hoff : 1 / 2 < ρ₀.re) :
    ∃ ρ ∈ zetaZeroConfig.carrier, ρ₀.re < ρ.re := by
  by_contra hno
  push Not at hno
  have hmem := re_mem_of_bddBelow_of_samplingWeight (samplingWeight_primeOff E hE)
    zetaZeroConfig temperedConfig_zetaZeroConfig hρ₀ hoff hno
    (bound_of_primeOffWeight_ne_zero (P := fun x => -K ≤ x) hK)
  exact zetaZeroConfig_im_ne_zero' _ hmem (Complex.ofReal_im _)

end GaloisForLFunctions.SurfaceOfSpecZ
