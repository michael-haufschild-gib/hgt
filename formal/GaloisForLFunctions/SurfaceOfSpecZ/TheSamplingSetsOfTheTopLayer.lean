import GaloisForLFunctions.SurfaceOfSpecZ.TheOtherSideSamplesEveryTopLayer

/-!
# The sampling sets of the top layer

`ThePrimesSampleEveryTopLayer` uses two properties of the weights `Λ(n)`: their series
`W(s) = Σ Λ(n) n^{−s}` blows up as `s ↓ 1`, and `W(σ + c) = o(W(σ))` for every `c ≠ 0` with `Re c ≥ 0`.
Any weight `0 ≤ w ≤ Λ` with these two properties (`SamplingWeight`) samples the top layer:

* `onLine_of_bddBelow_of_samplingWeight`: for a tempered configuration without real zeros whose
  maximal real part is attained, `2 Re S_Z(log n) ≥ −K` at the `n` with `w(n) ≠ 0` puts every zero on
  the critical line. The prime powers are sampling (`samplingWeight_vonMangoldt`).

**The primes in a residue class** (`samplingWeight_residueClass`). For `a` a unit mod `q`, the weight
`Λ(n) 1_{n ≡ a}` is sampling: its series is `φ(q)⁻¹/(s − 1)` plus a function continuous on `Re s ≥ 1`
(Mathlib's `LFunctionResidueClassAux`, from `L(1 + it, χ) ≠ 0`). Hence
(`onLine_of_bddBelow_primePowers_mod_of_max`) a lower bound at the prime powers `n ≡ a (mod q)`
decides the line for every configuration without real zeros and with an attained maximum.

**Masking is the only blindness** (`re_mem_of_bddBelow_of_samplingWeight`,
`onLine_or_re_mem_of_bddBelow_of_samplingWeight`). Real zeros are allowed: under a lower bound at a
sampling set, a zero `ρ₀` of maximal real part off the line forces the real point `Re ρ₀` to be a
zero. Only a real exponent in the top layer can carry the mean of `F`; without one the mean of `F²`,
`Σ_{Re z = b}|e_z|² > 0`, is bounded by `o(1)`. For a primitive character, a lower bound at the prime
powers in a residue class gives GRH for `L(s, χ)` or a real zero of maximal real part
(`grh_or_real_zero_of_bddBelow_primePowers_mod`).

The Dirichlet-series bootstrap of `TheZeroFreeStripImprovesItself` does not reach these degrees:
their series brings in the zeros of the `L(s, χ)`. The sampling argument needs only their absence on
`Re s = 1`.
-/

open Complex Filter Topology

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri SquareRootThreshold Zeta23
open ArithmeticFunction

/-! ### Sampling weights -/

/-- `Σ_{n ≥ 1} w(n) n^{−σ}`, with `w` indexed from `n = j + 1`. -/
def wSum (w : ℕ → ℝ) (σ : ℝ) : ℝ := ∑' j : ℕ, w j * ((j : ℝ) + 1) ^ (-σ)

/-- `Σ_{n ≥ 1} w(n) n^{−s}`. -/
def wSeries (w : ℕ → ℝ) (s : ℂ) : ℂ := ∑' j : ℕ, (w j : ℂ) * ((j : ℂ) + 1) ^ (-s)

theorem ofReal_wSum (w : ℕ → ℝ) (σ : ℝ) : ((wSum w σ : ℝ) : ℂ) = wSeries w σ := by
  rw [wSum, wSeries, Complex.ofReal_tsum]
  refine tsum_congr fun j => ?_
  rw [Complex.ofReal_mul, ofReal_add_one_rpow j (-σ)]
  push_cast; ring

/-- A weight below `Λ` has a convergent series on `σ > 1`. -/
theorem summable_of_le_vonMangoldt {w : ℕ → ℝ} (h0 : ∀ j, 0 ≤ w j) (hle : ∀ j, w j ≤ Λ (j + 1)) :
    ∀ σ : ℝ, 1 < σ → Summable fun j : ℕ => w j * ((j : ℝ) + 1) ^ (-σ) := fun σ hσ =>
  Summable.of_nonneg_of_le (fun j => mul_nonneg (h0 j) (by positivity))
    (fun j => mul_le_mul_of_nonneg_right (hle j) (by positivity)) (summable_vonMangoldt_rpow hσ)

/-- A sampling weight: `w ≥ 0` with `Σ w(n) n^{−σ} < ∞` for `σ > 1`, `Σ w(n) n^{−σ} → ∞` as `σ ↓ 1`,
and `Σ w(n) n^{−σ−c} = o(Σ w(n) n^{−σ})` for `c ≠ 0`, `Re c ≥ 0`. -/
structure SamplingWeight (w : ℕ → ℝ) : Prop where
  nonneg : ∀ j, 0 ≤ w j
  summable' : ∀ σ : ℝ, 1 < σ → Summable fun j : ℕ => w j * ((j : ℝ) + 1) ^ (-σ)
  tendsto_atTop : Tendsto (wSum w) (𝓝[>] 1) atTop
  tendsto_off : ∀ c : ℂ, c ≠ 0 → 0 ≤ c.re →
    Tendsto (fun σ : ℝ => wSeries w ((σ : ℂ) + c) / (wSum w σ : ℂ)) (𝓝[>] 1) (𝓝 0)

namespace SamplingWeight

variable {w : ℕ → ℝ} (hw : SamplingWeight w)
include hw

theorem summable {σ : ℝ} (hσ : 1 < σ) : Summable fun j : ℕ => w j * ((j : ℝ) + 1) ^ (-σ) :=
  hw.summable' σ hσ

theorem summable_series {s : ℂ} (hs : 1 < s.re) :
    Summable fun j : ℕ => (w j : ℂ) * ((j : ℂ) + 1) ^ (-s) := by
  refine Summable.of_norm_bounded (hw.summable hs) fun j => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw.nonneg j),
    norm_natCast_add_one_cpow]
  simp

theorem summable_series_of_le {v : ℕ → ℝ} (h0 : ∀ j, 0 ≤ v j) (hle : ∀ j, v j ≤ w j) {s : ℂ}
    (hs : 1 < s.re) : Summable fun j : ℕ => (v j : ℂ) * ((j : ℂ) + 1) ^ (-s) := by
  refine Summable.of_norm_bounded (hw.summable hs) fun j => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (h0 j),
    norm_natCast_add_one_cpow, Complex.neg_re]
  exact mul_le_mul_of_nonneg_right (hle j) (by positivity)

theorem norm_wSeries_le {s : ℂ} (hs : 1 < s.re) : ‖wSeries w s‖ ≤ wSum w s.re := by
  calc ‖wSeries w s‖ ≤ ∑' j : ℕ, ‖(w j : ℂ) * ((j : ℂ) + 1) ^ (-s)‖ :=
        norm_tsum_le_tsum_norm (hw.summable_series hs).norm
    _ = wSum w s.re := by
        rw [wSum]
        refine tsum_congr fun j => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw.nonneg j),
          norm_natCast_add_one_cpow]
        simp

theorem wSum_nonneg (σ : ℝ) : 0 ≤ wSum w σ :=
  tsum_nonneg fun j => mul_nonneg (hw.nonneg j) (by positivity)

theorem antitone {σ σ' : ℝ} (hσ : 1 < σ) (hσσ' : σ ≤ σ') : wSum w σ' ≤ wSum w σ := by
  refine Summable.tsum_le_tsum (fun j => ?_) (hw.summable (by linarith)) (hw.summable hσ)
  have hj1 : (1 : ℝ) ≤ (j : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) j]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hj1 (by linarith))
    (hw.nonneg j)

theorem eventually_pos : ∀ᶠ σ in 𝓝[>] (1 : ℝ), 0 < wSum w σ :=
  hw.tendsto_atTop.eventually (eventually_gt_atTop 0)

end SamplingWeight

/-! ### The weighted means of the normalized trace -/

/-- `Σ w(n) F(log n) n^{−σ}`. -/
def wMean (w : ℕ → ℝ) (Z : ZeroConfig) (b σ : ℝ) : ℝ :=
  ∑' j : ℕ, w j * normTrace Z b (Real.log (j + 1)) * ((j : ℝ) + 1) ^ (-σ)

/-- `Σ w(n) F(log n)² n^{−σ}`. -/
def wSqMean (w : ℕ → ℝ) (Z : ZeroConfig) (b σ : ℝ) : ℝ :=
  ∑' j : ℕ, w j * normTrace Z b (Real.log (j + 1)) ^ 2 * ((j : ℝ) + 1) ^ (-σ)

section Means

variable {w : ℕ → ℝ} (hw : SamplingWeight w) {Z : ZeroConfig} {b : ℝ}
include hw

theorem summable_wMean (hZ : TemperedConfig Z) (h : TopDepth Z b) {σ : ℝ} (hσ : 1 < σ) :
    Summable fun j : ℕ => w j * normTrace Z b (Real.log (j + 1)) * ((j : ℝ) + 1) ^ (-σ) := by
  refine Summable.of_norm_bounded ((hw.summable hσ).mul_left
    (∑' z, ‖evenCoeff Z (boxSpline 1 3) z‖)) fun j => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hw.nonneg j),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((j : ℝ) + 1) ^ (-σ))]
  have := abs_normTrace_le hZ h (log_add_one_nonneg j)
  have hw0 := hw.nonneg j
  have hp : 0 ≤ ((j : ℝ) + 1) ^ (-σ) := by positivity
  nlinarith [mul_nonneg hw0 hp]

theorem summable_wSqMean (hZ : TemperedConfig Z) (h : TopDepth Z b) {σ : ℝ} (hσ : 1 < σ) :
    Summable fun j : ℕ => w j * normTrace Z b (Real.log (j + 1)) ^ 2 * ((j : ℝ) + 1) ^ (-σ) := by
  set E := ∑' z, ‖evenCoeff Z (boxSpline 1 3) z‖
  refine Summable.of_nonneg_of_le (fun j => by have := hw.nonneg j; positivity) (fun j => ?_)
    ((hw.summable hσ).mul_left (E ^ 2))
  have h1 := abs_normTrace_le hZ h (log_add_one_nonneg j)
  have hsq : normTrace Z b (Real.log (j + 1)) ^ 2 ≤ E ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have hw0 := hw.nonneg j
  have hp : 0 ≤ ((j : ℝ) + 1) ^ (-σ) := by positivity
  calc w j * normTrace Z b (Real.log (j + 1)) ^ 2 * ((j : ℝ) + 1) ^ (-σ)
      = normTrace Z b (Real.log (j + 1)) ^ 2 * (w j * ((j : ℝ) + 1) ^ (-σ)) := by ring
    _ ≤ E ^ 2 * (w j * ((j : ℝ) + 1) ^ (-σ)) := mul_le_mul_of_nonneg_right hsq (mul_nonneg hw0 hp)

/-- **The mean of `F` through the exponents.** `Σ w(n) F(log n) n^{−σ} = Σ_z e_z W(σ + b − z)`. -/
theorem ofReal_wMean (hZ : TemperedConfig Z) (h : TopDepth Z b) {σ : ℝ} (hσ : 1 < σ) :
    ((wMean w Z b σ : ℝ) : ℂ) =
      ∑' z, evenCoeff Z (boxSpline 1 3) z * wSeries w ((σ : ℂ) + (b - z)) := by
  set e := evenCoeff Z (boxSpline 1 3) with hedef
  have hE := summable_norm_evenCoeff_spline hZ
  set f : ℕ → ℂ → ℂ := fun j z => (w j : ℂ) * (e z * ((j : ℂ) + 1) ^ (-((σ : ℂ) + (b - z))))
    with hfdef
  have hfn : ∀ j z, ‖f j z‖ ≤ w j * ((j : ℝ) + 1) ^ (-σ) * ‖e z‖ := by
    intro j z
    by_cases hz : e z = 0
    · simp [hfdef, hz]
    have h1 := h z hz
    simp only [hfdef, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hw.nonneg j), norm_natCast_add_one_cpow]
    have hexp : ((j : ℝ) + 1) ^ (-((σ : ℂ) + (b - z))).re ≤ ((j : ℝ) + 1) ^ (-σ) := by
      apply Real.rpow_le_rpow_of_exponent_le (by linarith [Nat.cast_nonneg (α := ℝ) j])
      simp; linarith
    calc w j * (‖e z‖ * ((j : ℝ) + 1) ^ (-((σ : ℂ) + (b - z))).re)
        ≤ w j * (‖e z‖ * ((j : ℝ) + 1) ^ (-σ)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp (norm_nonneg _)) (hw.nonneg j)
      _ = _ := by ring
  have hprod : Summable fun p : ℕ × ℂ => w p.1 * ((p.1 : ℝ) + 1) ^ (-σ) * ‖e p.2‖ :=
    (hw.summable hσ).mul_of_nonneg hE
      (fun j => mul_nonneg (hw.nonneg j) (by positivity)) (fun _ => norm_nonneg _)
  have hFsum2 : Summable (Function.uncurry f) := Summable.of_norm_bounded hprod fun p => hfn p.1 p.2
  have hj : ∀ j : ℕ, ∑' z, f j z =
      ((w j * normTrace Z b (Real.log (j + 1)) * ((j : ℝ) + 1) ^ (-σ) : ℝ) : ℂ) := by
    intro j
    simp only [hfdef]
    rw [tsum_mul_left, Complex.ofReal_mul, Complex.ofReal_mul, ofReal_normTrace hZ,
      ofReal_add_one_rpow j (-σ), mul_assoc, ← tsum_mul_right]
    congr 1
    refine tsum_congr fun z => ?_
    rw [natCast_add_one_cpow_eq, natCast_add_one_cpow_eq, mul_assoc, ← Complex.exp_add]
    push_cast
    congr 2
    ring
  have hz : ∀ z : ℂ, ∑' j, f j z = e z * wSeries w ((σ : ℂ) + (b - z)) := by
    intro z
    rw [wSeries, ← tsum_mul_left]
    refine tsum_congr fun j => ?_
    simp only [hfdef]; ring
  rw [wMean, Complex.ofReal_tsum, ← tsum_congr hj, hFsum2.tsum_comm.symm, tsum_congr hz]

/-- **The relative mean of `F` vanishes** when the top layer has no real exponent. -/
theorem tendsto_wMean (hZ : TemperedConfig Z) (h : TopDepth Z b)
    (hreal : ∀ z, evenCoeff Z (boxSpline 1 3) z ≠ 0 → z.re = b → z.im ≠ 0) :
    Tendsto (fun σ => wMean w Z b σ / wSum w σ) (𝓝[>] 1) (𝓝 0) := by
  set e := evenCoeff Z (boxSpline 1 3) with hedef
  have hE := summable_norm_evenCoeff_spline hZ
  have hc : Tendsto (fun σ : ℝ => ∑' z, e z * wSeries w ((σ : ℂ) + (b - z)) / (wSum w σ : ℂ))
      (𝓝[>] 1) (𝓝 (∑' _z : ℂ, (0 : ℂ))) := by
    refine tendsto_tsum_of_dominated_convergence hE (fun z => ?_) ?_
    · by_cases hz : e z = 0
      · simp [hz]
      have h1 := h z hz
      have hne : (b : ℂ) - z ≠ 0 := by
        intro h0
        have hre := congrArg Complex.re h0
        have him := congrArg Complex.im h0
        simp at hre him
        exact hreal z hz (by linarith) (by linarith)
      have := (hw.tendsto_off ((b : ℂ) - z) hne (by simp; linarith)).const_mul (e z)
      simpa [mul_div_assoc] using this
    · filter_upwards [self_mem_nhdsWithin, hw.eventually_pos] with σ hσ hV
      intro z
      have hσ1 : 1 < σ := hσ
      by_cases hz : e z = 0
      · simp [hz]
      have h1 := h z hz
      have hres : 1 < ((σ : ℂ) + (b - z)).re := by simp; linarith
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hV, norm_mul, div_le_iff₀ hV]
      have hb1 := hw.norm_wSeries_le hres
      have hb2 : wSum w ((σ : ℂ) + (b - z)).re ≤ wSum w σ := hw.antitone hσ1 (by simp; linarith)
      exact mul_le_mul_of_nonneg_left (hb1.trans hb2) (norm_nonneg _)
  rw [tsum_zero] at hc
  have hc' := (Complex.continuous_re.tendsto 0).comp hc
  refine (hc'.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  have hrat : ((wMean w Z b σ / wSum w σ : ℝ) : ℂ) =
      ∑' z, e z * wSeries w ((σ : ℂ) + (b - z)) / (wSum w σ : ℂ) := by
    rw [Complex.ofReal_div, ofReal_wMean hw hZ h hσ, tsum_div_const]
  simp only [Function.comp_def]
  rw [← hrat, Complex.ofReal_re]

/-- **The mean of `F²` through the pairs of exponents.** -/
theorem ofReal_wSqMean (hZ : TemperedConfig Z) (h : TopDepth Z b) {σ : ℝ} (hσ : 1 < σ) :
    ((wSqMean w Z b σ : ℝ) : ℂ) = ∑' q : ℂ × ℂ, evenCoeff Z (boxSpline 1 3) q.1 *
      evenCoeff Z (boxSpline 1 3) q.2 * wSeries w ((σ : ℂ) + (2 * b - q.1 - q.2)) := by
  set e := evenCoeff Z (boxSpline 1 3) with hedef
  have hE := summable_norm_evenCoeff_spline hZ
  have hEE : Summable fun q : ℂ × ℂ => ‖e q.1‖ * ‖e q.2‖ :=
    Summable.mul_of_nonneg (f := fun z => ‖e z‖) (g := fun z => ‖e z‖) hE hE
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  have hFsum : ∀ u : ℝ, 0 ≤ u → Summable fun z => e z * cexp ((z - b) * u) := fun u hu =>
    Summable.of_norm_bounded hE fun z => norm_evenCoeff_mul_cexp_le h z hu
  have hF2 : ∀ u : ℝ, 0 ≤ u → ((normTrace Z b u ^ 2 : ℝ) : ℂ) =
      ∑' q : ℂ × ℂ, e q.1 * e q.2 * cexp ((q.1 + q.2 - 2 * b) * u) := by
    intro u hu
    rw [Complex.ofReal_pow, ofReal_normTrace hZ, sq,
      tsum_mul_tsum_of_summable_norm (hFsum u hu).norm (hFsum u hu).norm]
    refine tsum_congr fun q => ?_
    rw [show e q.1 * cexp ((q.1 - b) * u) * (e q.2 * cexp ((q.2 - b) * u)) =
      e q.1 * e q.2 * (cexp ((q.1 - b) * u) * cexp ((q.2 - b) * u)) by ring, ← Complex.exp_add]
    congr 2; ring
  set f : ℕ → ℂ × ℂ → ℂ := fun j q => (w j : ℂ) *
    (e q.1 * e q.2 * ((j : ℂ) + 1) ^ (-((σ : ℂ) + (2 * b - q.1 - q.2)))) with hfdef
  have hfn : ∀ j q, ‖f j q‖ ≤ w j * ((j : ℝ) + 1) ^ (-σ) * (‖e q.1‖ * ‖e q.2‖) := by
    intro j q
    by_cases hq : e q.1 * e q.2 = 0
    · simp only [hfdef, hq, zero_mul, mul_zero, norm_zero]
      exact mul_nonneg (mul_nonneg (hw.nonneg j) (by positivity)) (by positivity)
    have h1 := h q.1 (left_ne_zero_of_mul hq)
    have h2 := h q.2 (right_ne_zero_of_mul hq)
    simp only [hfdef, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hw.nonneg j), norm_natCast_add_one_cpow]
    have hexp : ((j : ℝ) + 1) ^ (-((σ : ℂ) + (2 * b - q.1 - q.2))).re ≤ ((j : ℝ) + 1) ^ (-σ) := by
      apply Real.rpow_le_rpow_of_exponent_le (by linarith [Nat.cast_nonneg (α := ℝ) j])
      simp; linarith
    calc w j * (‖e q.1‖ * ‖e q.2‖ * ((j : ℝ) + 1) ^ (-((σ : ℂ) + (2 * b - q.1 - q.2))).re)
        ≤ w j * (‖e q.1‖ * ‖e q.2‖ * ((j : ℝ) + 1) ^ (-σ)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp (by positivity)) (hw.nonneg j)
      _ = _ := by ring
  have hprod : Summable fun p : ℕ × (ℂ × ℂ) =>
      w p.1 * ((p.1 : ℝ) + 1) ^ (-σ) * (‖e p.2.1‖ * ‖e p.2.2‖) :=
    (hw.summable hσ).mul_of_nonneg hEE
      (fun j => mul_nonneg (hw.nonneg j) (by positivity)) (fun _ => by positivity)
  have hFsum2 : Summable (Function.uncurry f) :=
    Summable.of_norm_bounded hprod fun p => hfn p.1 p.2
  have hj : ∀ j : ℕ, ∑' q, f j q =
      ((w j * normTrace Z b (Real.log (j + 1)) ^ 2 * ((j : ℝ) + 1) ^ (-σ) : ℝ) : ℂ) := by
    intro j
    simp only [hfdef]
    rw [tsum_mul_left, Complex.ofReal_mul, Complex.ofReal_mul, hF2 _ (log_add_one_nonneg j),
      ofReal_add_one_rpow j (-σ), mul_assoc, ← tsum_mul_right]
    congr 1
    refine tsum_congr fun q => ?_
    rw [natCast_add_one_cpow_eq, natCast_add_one_cpow_eq, mul_assoc (e q.1 * e q.2),
      ← Complex.exp_add]
    push_cast
    congr 2
    ring
  have hz : ∀ q : ℂ × ℂ, ∑' j, f j q =
      e q.1 * e q.2 * wSeries w ((σ : ℂ) + (2 * b - q.1 - q.2)) := by
    intro q
    rw [wSeries, ← tsum_mul_left]
    refine tsum_congr fun j => ?_
    simp only [hfdef]; ring
  rw [wSqMean, Complex.ofReal_tsum, ← tsum_congr hj, hFsum2.tsum_comm.symm, tsum_congr hz]

/-- **The relative mean of `F²` is the diagonal weight.** -/
theorem tendsto_wSqMean (hZ : TemperedConfig Z) (h : TopDepth Z b) :
    Tendsto (fun σ => wSqMean w Z b σ / wSum w σ) (𝓝[>] 1) (𝓝 (∑' q, diagWeight Z b q).re) := by
  set e := evenCoeff Z (boxSpline 1 3) with hedef
  have hE := summable_norm_evenCoeff_spline hZ
  have hEE : Summable fun q : ℂ × ℂ => ‖e q.1‖ * ‖e q.2‖ :=
    Summable.mul_of_nonneg (f := fun z => ‖e z‖) (g := fun z => ‖e z‖) hE hE
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  have hc : Tendsto (fun σ : ℝ => ∑' q : ℂ × ℂ, e q.1 * e q.2 *
      wSeries w ((σ : ℂ) + (2 * b - q.1 - q.2)) / (wSum w σ : ℂ))
      (𝓝[>] 1) (𝓝 (∑' q, diagWeight Z b q)) := by
    refine tendsto_tsum_of_dominated_convergence hEE (fun q => ?_) ?_
    · by_cases hq : e q.1 * e q.2 = 0
      · simp [diagWeight, ← hedef, hq]
      by_cases hq2 : q.1 + q.2 = 2 * (b : ℂ)
      · have hconst : ∀ᶠ σ : ℝ in 𝓝[>] (1 : ℝ), e q.1 * e q.2 *
            wSeries w ((σ : ℂ) + (2 * b - q.1 - q.2)) / (wSum w σ : ℂ) = e q.1 * e q.2 := by
          filter_upwards [hw.eventually_pos] with σ hV
          have h0 : (σ : ℂ) + (2 * b - q.1 - q.2) = σ := by rw [← hq2]; ring
          rw [h0, ← ofReal_wSum, mul_div_assoc,
            div_self (by exact_mod_cast hV.ne'), mul_one]
        simp only [diagWeight, ← hedef, if_pos hq2]
        exact tendsto_const_nhds.congr' (hconst.mono fun σ h => h.symm)
      · have h1 := h q.1 (left_ne_zero_of_mul hq)
        have h2 := h q.2 (right_ne_zero_of_mul hq)
        have hne : (2 * (b : ℂ) - q.1 - q.2) ≠ 0 := fun h0 => hq2 (by linear_combination -h0)
        have hre : 0 ≤ (2 * (b : ℂ) - q.1 - q.2).re := by simp; linarith
        have := (hw.tendsto_off _ hne hre).const_mul (e q.1 * e q.2)
        simp only [diagWeight, ← hedef, if_neg hq2]
        simpa [mul_div_assoc] using this
    · filter_upwards [self_mem_nhdsWithin, hw.eventually_pos] with σ hσ hV
      intro q
      have hσ1 : 1 < σ := hσ
      by_cases hq : e q.1 * e q.2 = 0
      · simp [hq]; positivity
      have h1 := h q.1 (left_ne_zero_of_mul hq)
      have h2 := h q.2 (right_ne_zero_of_mul hq)
      have hres : 1 < ((σ : ℂ) + (2 * b - q.1 - q.2)).re := by simp; linarith
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hV, norm_mul, norm_mul,
        div_le_iff₀ hV]
      have hb1 := hw.norm_wSeries_le hres
      have hb2 : wSum w ((σ : ℂ) + (2 * b - q.1 - q.2)).re ≤ wSum w σ :=
        hw.antitone hσ1 (by simp; linarith)
      exact mul_le_mul_of_nonneg_left (hb1.trans hb2) (by positivity)
  have hc' := (Complex.continuous_re.tendsto _).comp hc
  refine (hc'.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  have hrat : ((wSqMean w Z b σ / wSum w σ : ℝ) : ℂ) = ∑' q : ℂ × ℂ, e q.1 * e q.2 *
      wSeries w ((σ : ℂ) + (2 * b - q.1 - q.2)) / (wSum w σ : ℂ) := by
    rw [Complex.ofReal_div, ofReal_wSqMean hw hZ h hσ, tsum_div_const]
  simp only [Function.comp_def]
  rw [← hrat, Complex.ofReal_re]

/-- **At the sampled degrees, `F² ≤ E(F + 2|K| n^{−b})`.** -/
theorem wSqMean_le (hZ : TemperedConfig Z) (h : TopDepth Z b) {K : ℝ}
    (hK : ∀ j : ℕ, w j ≠ 0 → -K ≤ 2 * (lagStructure Z (boxSpline 1 3) (Real.log (j + 1))).re)
    {σ : ℝ} (hσ : 1 < σ) (hb0 : 0 ≤ b) :
    wSqMean w Z b σ ≤ (∑' z, ‖evenCoeff Z (boxSpline 1 3) z‖) * wMean w Z b σ +
      2 * (∑' z, ‖evenCoeff Z (boxSpline 1 3) z‖) * |K| * wSum w (σ + b) := by
  set E := ∑' z, ‖evenCoeff Z (boxSpline 1 3) z‖ with hEdef
  have hE0 : 0 ≤ E := tsum_nonneg fun _ => norm_nonneg _
  have hεsum := hw.summable (show 1 < σ + b by linarith)
  have hS₁sum := summable_wMean hw hZ h hσ
  have hrhs : Summable fun j : ℕ =>
      E * (w j * normTrace Z b (Real.log (j + 1)) * ((j : ℝ) + 1) ^ (-σ)) +
        2 * E * |K| * (w j * ((j : ℝ) + 1) ^ (-(σ + b))) :=
    (hS₁sum.mul_left E).add (hεsum.mul_left _)
  calc wSqMean w Z b σ
      ≤ ∑' j : ℕ, (E * (w j * normTrace Z b (Real.log (j + 1)) * ((j : ℝ) + 1) ^ (-σ)) +
          2 * E * |K| * (w j * ((j : ℝ) + 1) ^ (-(σ + b)))) := by
        refine Summable.tsum_le_tsum (fun j => ?_) (summable_wSqMean hw hZ h hσ) hrhs
        have hw0 := hw.nonneg j
        have hj0 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
        have hp : 0 < ((j : ℝ) + 1) ^ (-σ) := by positivity
        have hsplit : ((j : ℝ) + 1) ^ (-(σ + b)) = ((j : ℝ) + 1) ^ (-σ) * ((j : ℝ) + 1) ^ (-b) := by
          rw [← Real.rpow_add hj0]; ring_nf
        rw [hsplit]
        by_cases hw00 : w j = 0
        · rw [hw00]; simp
        have h1 := hK j hw00
        have hexp : Real.exp (-(b * Real.log ((j : ℝ) + 1))) = ((j : ℝ) + 1) ^ (-b) := by
          rw [Real.rpow_def_of_pos hj0]; ring_nf
        have hpb : 0 < ((j : ℝ) + 1) ^ (-b) := by positivity
        have hlow : -(|K| * ((j : ℝ) + 1) ^ (-b)) ≤ normTrace Z b (Real.log ((j : ℝ) + 1)) := by
          rw [normTrace, hexp]
          have h3 := mul_le_mul_of_nonneg_right h1 hpb.le
          have h4 : K * ((j : ℝ) + 1) ^ (-b) ≤ |K| * ((j : ℝ) + 1) ^ (-b) :=
            mul_le_mul_of_nonneg_right (le_abs_self K) hpb.le
          linarith
        have hFb := abs_normTrace_le hZ h (log_add_one_nonneg j)
        set f := normTrace Z b (Real.log ((j : ℝ) + 1))
        have habs : |f| ≤ f + 2 * (|K| * ((j : ℝ) + 1) ^ (-b)) := by
          rcases le_total 0 f with h0 | h0
          · rw [abs_of_nonneg h0]; nlinarith [abs_nonneg K]
          · rw [abs_of_nonpos h0]; linarith
        have hsq : f ^ 2 ≤ E * (f + 2 * (|K| * ((j : ℝ) + 1) ^ (-b))) := by
          calc f ^ 2 = |f| * |f| := by rw [← sq_abs, sq]
            _ ≤ E * |f| := mul_le_mul_of_nonneg_right hFb (abs_nonneg _)
            _ ≤ _ := mul_le_mul_of_nonneg_left habs hE0
        have hwp : 0 ≤ w j * ((j : ℝ) + 1) ^ (-σ) := mul_nonneg hw0 hp.le
        have h5 := mul_le_mul_of_nonneg_right hsq hwp
        calc w j * f ^ 2 * ((j : ℝ) + 1) ^ (-σ) = f ^ 2 * (w j * ((j : ℝ) + 1) ^ (-σ)) := by ring
          _ ≤ E * (f + 2 * (|K| * ((j : ℝ) + 1) ^ (-b))) * (w j * ((j : ℝ) + 1) ^ (-σ)) := h5
          _ = _ := by ring
    _ = E * wMean w Z b σ + 2 * E * |K| * wSum w (σ + b) := by
        rw [(hS₁sum.mul_left E).tsum_add (hεsum.mul_left _), tsum_mul_left, tsum_mul_left]
        rfl

end Means

/-! ### The theorem -/

/-- **The lower side sees down to the deepest real zero.** If a sampling weight bounds the spline
traces from below and `ρ₀` is a zero of maximal real part off the line, then `Re ρ₀` is itself a
zero: the top layer contains a real zero. -/
theorem re_mem_of_bddBelow_of_samplingWeight {w : ℕ → ℝ} (hw : SamplingWeight w)
    (Z : ZeroConfig) (hZ : TemperedConfig Z) {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ Z.carrier)
    (hoff : 1 / 2 < ρ₀.re) (hmax : ∀ ρ ∈ Z.carrier, ρ.re ≤ ρ₀.re) {K : ℝ}
    (hK : ∀ j : ℕ, w j ≠ 0 → -K ≤ 2 * (lagStructure Z (boxSpline 1 3) (Real.log (j + 1))).re) :
    (ρ₀.re : ℂ) ∈ Z.carrier := by
  by_contra hnot
  have hb3 := contDiff_boxSpline (r := 1) one_pos 2
  have hbc := hasCompactSupport_of_support_subset_abs (boxSpline_support (r := 1) one_pos 3)
  set b : ℝ := ρ₀.re - 1 / 2 with hbdef
  have hb0 : 0 < b := by rw [hbdef]; linarith
  have htop : TopDepth Z b := by
    intro z hz
    rcases mem_of_evenCoeff_ne_zero hz with h | h
    · have h1 := hmax _ h; simp at h1; rw [hbdef]; linarith
    · have h1 := hmax _ h; simp at h1; rw [hbdef]; linarith
  -- a real exponent at depth `b` would be the real zero `Re ρ₀`
  have hreal : ∀ z, evenCoeff Z (boxSpline 1 3) z ≠ 0 → z.re = b → z.im ≠ 0 := by
    intro z hz hzre hzim
    have hzb : z = (b : ℂ) := Complex.ext (by simpa using hzre) (by simpa using hzim)
    have hpt : (1 / 2 : ℂ) + (b : ℂ) = (ρ₀.re : ℂ) := by rw [hbdef]; push_cast; ring
    rcases mem_of_evenCoeff_ne_zero hz with h | h
    · rw [hzb, hpt] at h; exact hnot h
    · rw [hzb, Complex.conj_ofReal, hpt] at h; exact hnot h
  have hz₀ : evenCoeff Z (boxSpline 1 3) (ρ₀ - 1 / 2) ≠ 0 :=
    evenCoeff_sub_half_ne_zero_of_conj_symm Z hb3.continuous hbc
      (conj_paperFT_boxSpline _ _) (paperFT_boxSpline_neg _ _) hρ₀
      (paperFT_boxSpline_ne_zero one_pos 3 (im_gammaOf_ne_zero (by linarith)))
  have hpos := re_tsum_diagWeight_pos hZ htop hz₀ (by simp [hbdef])
  set E := ∑' z, ‖evenCoeff Z (boxSpline 1 3) z‖ with hEdef
  have hlimε : Tendsto (fun σ => wSum w (σ + b) / wSum w σ) (𝓝[>] 1) (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (tendsto_const_nhds (x := (0 : ℝ)))
      ((tendsto_const_nhds (x := wSum w (1 + b))).div_atTop hw.tendsto_atTop) ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with σ hσ
      exact div_nonneg (hw.wSum_nonneg _) (hw.wSum_nonneg _)
    · filter_upwards [self_mem_nhdsWithin] with σ hσ
      have hσ1 : 1 < σ := hσ
      exact div_le_div_of_nonneg_right (hw.antitone (by linarith) (by linarith))
        (hw.wSum_nonneg _)
  have hrhs : Tendsto (fun σ => E * (wMean w Z b σ / wSum w σ) +
      2 * E * |K| * (wSum w (σ + b) / wSum w σ)) (𝓝[>] 1) (𝓝 0) := by
    simpa using ((tendsto_wMean hw hZ htop hreal).const_mul E).add (hlimε.const_mul (2 * E * |K|))
  have hle : (∑' q, diagWeight Z b q).re ≤ 0 := by
    refine le_of_tendsto_of_tendsto (tendsto_wSqMean hw hZ htop) hrhs ?_
    filter_upwards [self_mem_nhdsWithin, hw.eventually_pos] with σ hσ hV
    have hσ1 : 1 < σ := hσ
    have h := wSqMean_le hw hZ htop hK hσ1 hb0.le
    rw [div_le_iff₀ hV]
    have : (E * (wMean w Z b σ / wSum w σ) + 2 * E * |K| * (wSum w (σ + b) / wSum w σ)) *
        wSum w σ = E * wMean w Z b σ + 2 * E * |K| * wSum w (σ + b) := by field_simp
    rw [this]; exact h
  linarith

/-- An attained maximal real part `Re ρ₀ ≥ ½`, together with `Re ρ₀ = ½`, puts every zero on the
line. -/
theorem onLine_of_max_eq_half {Z : ZeroConfig} {ρ₀ : ℂ} (hmax : ∀ ρ ∈ Z.carrier, ρ.re ≤ ρ₀.re)
    (hb : ρ₀.re = 1 / 2) : ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2 := by
  intro ρ hρ
  have h1 := hmax ρ hρ
  have h2 := hmax _ (Z.reflect_mem ρ hρ)
  have hrefl : (Zeta23.reflect ρ).re = 1 - ρ.re := by simp [Zeta23.reflect]
  rw [hrefl] at h2; linarith

theorem half_le_of_max {Z : ZeroConfig} {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ Z.carrier)
    (hmax : ∀ ρ ∈ Z.carrier, ρ.re ≤ ρ₀.re) : 1 / 2 ≤ ρ₀.re := by
  have h := hmax _ (Z.reflect_mem ρ₀ hρ₀)
  have hrefl : (Zeta23.reflect ρ₀).re = 1 - ρ₀.re := by simp [Zeta23.reflect]
  rw [hrefl] at h; linarith

/-- **Masking is the only blindness.** Under a lower bound at a sampling set, either every zero
lies on the line or the maximal real part is that of a real zero. -/
theorem onLine_or_re_mem_of_bddBelow_of_samplingWeight {w : ℕ → ℝ} (hw : SamplingWeight w)
    (Z : ZeroConfig) (hZ : TemperedConfig Z) {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ Z.carrier)
    (hmax : ∀ ρ ∈ Z.carrier, ρ.re ≤ ρ₀.re) {K : ℝ}
    (hK : ∀ j : ℕ, w j ≠ 0 → -K ≤ 2 * (lagStructure Z (boxSpline 1 3) (Real.log (j + 1))).re) :
    (∀ ρ ∈ Z.carrier, ρ.re = 1 / 2) ∨ (ρ₀.re : ℂ) ∈ Z.carrier := by
  rcases (half_le_of_max hρ₀ hmax).eq_or_lt with h | h
  · exact Or.inl (onLine_of_max_eq_half hmax h.symm)
  · exact Or.inr (re_mem_of_bddBelow_of_samplingWeight hw Z hZ hρ₀ h hmax hK)

/-- **Sampling weights sample every top layer** of a configuration without real zeros. -/
theorem onLine_of_bddBelow_of_samplingWeight {w : ℕ → ℝ} (hw : SamplingWeight w)
    (Z : ZeroConfig) (hZ : TemperedConfig Z) (hnoreal : ∀ ρ ∈ Z.carrier, ρ.im ≠ 0) {ρ₀ : ℂ}
    (hρ₀ : ρ₀ ∈ Z.carrier) (hmax : ∀ ρ ∈ Z.carrier, ρ.re ≤ ρ₀.re) {K : ℝ}
    (hK : ∀ j : ℕ, w j ≠ 0 → -K ≤ 2 * (lagStructure Z (boxSpline 1 3) (Real.log (j + 1))).re) :
    ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2 := by
  rcases onLine_or_re_mem_of_bddBelow_of_samplingWeight hw Z hZ hρ₀ hmax hK with h | h
  · exact h
  · exact absurd (Complex.ofReal_im _) (hnoreal _ h)

/-! ### The prime powers -/

/-- **The prime powers form a sampling set**: `−ζ'/ζ(σ + c)/Σ Λ(n)n^{−σ} → 0` off `c = 0`. -/
theorem samplingWeight_vonMangoldt : SamplingWeight fun j => Λ (j + 1) := by
  refine ⟨fun j => vonMangoldt_nonneg, fun σ hσ => summable_vonMangoldt_rpow hσ, tendsto_vmSum_atTop,
    fun c hc hre => ?_⟩
  have h := (tendsto_logDeriv_div_vmSum hre hc).neg
  rw [neg_zero] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  have hσ1 : 1 < σ := hσ
  have hs : 1 < ((σ : ℂ) + c).re := by simp; linarith
  have hser : wSeries (fun j => Λ (j + 1)) ((σ : ℂ) + c) = -logDeriv riemannZeta ((σ : ℂ) + c) :=
    (summable_tsum_vonMangoldt hs).2
  rw [hser]
  show -(logDeriv riemannZeta ((σ : ℂ) + c) / (vmSum σ : ℂ)) =
    -logDeriv riemannZeta ((σ : ℂ) + c) / (vmSum σ : ℂ)
  ring

/-! ### The primes in a residue class -/

section ResidueClass

variable {q : ℕ} [NeZero q] {a : ZMod q}

/-- The residue-class weight `Λ(n) 1_{n ≡ a}` at `n = j + 1`. -/
def residueWeight (a : ZMod q) (j : ℕ) : ℝ := vonMangoldt.residueClass a (j + 1)

omit [NeZero q] in
theorem residueWeight_nonneg (j : ℕ) : 0 ≤ residueWeight a j :=
  vonMangoldt.residueClass_nonneg a _

omit [NeZero q] in
theorem residueWeight_le (j : ℕ) : residueWeight a j ≤ Λ (j + 1) :=
  vonMangoldt.residueClass_le a _

omit [NeZero q] in
theorem wSeries_residueWeight_eq {s : ℂ} (hs : 1 < s.re) :
    wSeries (residueWeight a) s = LSeries (fun n => (vonMangoldt.residueClass a n : ℂ)) s := by
  have hsum : Summable fun j : ℕ => ((residueWeight a j : ℝ) : ℂ) * ((j : ℂ) + 1) ^ (-s) := by
    refine Summable.of_norm_bounded ((summable_vonMangoldt_rpow hs)) fun j => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (residueWeight_nonneg j), norm_natCast_add_one_cpow]
    exact mul_le_mul_of_nonneg_right (residueWeight_le j) (by positivity)
  have hterm : ∀ j : ℕ, LSeries.term (fun n => (vonMangoldt.residueClass a n : ℂ)) s (j + 1) =
      ((residueWeight a j : ℝ) : ℂ) * ((j : ℂ) + 1) ^ (-s) := by
    intro j
    rw [LSeries.term_def, if_neg (Nat.succ_ne_zero j), residueWeight]
    push_cast
    rw [Complex.cpow_neg, div_eq_mul_inv]
  have hL : Summable (LSeries.term (fun n => (vonMangoldt.residueClass a n : ℂ)) s) :=
    (summable_nat_add_iff 1).mp (hsum.congr fun j => (hterm j).symm)
  rw [wSeries, LSeries, hL.tsum_eq_zero_add, LSeries.term_zero, zero_add]
  exact tsum_congr fun j => (hterm j).symm

omit [NeZero q] in
theorem wSum_residueWeight_eq {σ : ℝ} (hσ : 1 < σ) :
    wSum (residueWeight a) σ = ∑' n, vonMangoldt.residueClass a n / (n : ℝ) ^ σ := by
  have hs : Summable fun j : ℕ => residueWeight a j * ((j : ℝ) + 1) ^ (-σ) :=
    Summable.of_nonneg_of_le (fun j => mul_nonneg (residueWeight_nonneg j) (by positivity))
      (fun j => mul_le_mul_of_nonneg_right (residueWeight_le j) (by positivity))
      (summable_vonMangoldt_rpow hσ)
  have hs' : Summable fun n : ℕ => vonMangoldt.residueClass a n / (n : ℝ) ^ σ := by
    refine (summable_nat_add_iff 1).mp (hs.congr fun j => ?_)
    rw [residueWeight, Real.rpow_neg (by positivity), div_eq_mul_inv]; push_cast; ring
  rw [hs'.tsum_eq_zero_add, vonMangoldt.residueClass_apply_zero, zero_div, zero_add, wSum]
  refine tsum_congr fun j => ?_
  rw [residueWeight, Real.rpow_neg (by positivity), div_eq_mul_inv]; push_cast; ring

/-- `Σ Λ(n) 1_{n ≡ a} n^{−σ} ≥ φ(q)⁻¹/(σ − 1) − C` blows up as `σ ↓ 1`. -/
theorem tendsto_wSum_residueWeight (ha : IsUnit a) :
    Tendsto (wSum (residueWeight a)) (𝓝[>] 1) atTop := by
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  obtain ⟨C, hC⟩ := vonMangoldt.LSeries_residueClass_lower_bound (a := a) ha
  have hlow : ∀ᶠ σ in 𝓝[>] (1 : ℝ),
      (q.totient : ℝ)⁻¹ / (σ - 1) - C ≤ wSum (residueWeight a) σ := by
    filter_upwards [Ioo_mem_nhdsGT (show (1 : ℝ) < 2 by norm_num)] with σ hσ
    rw [wSum_residueWeight_eq hσ.1]
    exact hC ⟨hσ.1, hσ.2.le⟩
  have hpole : Tendsto (fun σ : ℝ => (q.totient : ℝ)⁻¹ / (σ - 1) - C) (𝓝[>] 1) atTop := by
    have h1 : Tendsto (fun σ : ℝ => σ - 1) (𝓝[>] 1) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have := (continuous_id.sub continuous_const).tendsto (1 : ℝ) (f := fun σ : ℝ => σ - 1)
        simpa using this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with σ hσ
        exact sub_pos.mpr (show (1 : ℝ) < σ from hσ)
    have h2 := (tendsto_inv_nhdsGT_zero.comp h1).const_mul_atTop (inv_pos.mpr hφ)
    refine (tendsto_atTop_add_const_right _ (-C) h2).congr fun σ => ?_
    simp [div_eq_mul_inv, sub_eq_add_neg]
  exact tendsto_atTop_mono' _ hlow hpole

/-- **The primes in a residue class form a sampling set.** Off `c = 0` the series
`Σ Λ(n) 1_{n ≡ a} n^{−σ−c}` has the finite limit `Aux(1 + c) + φ(q)⁻¹/c`. -/
theorem samplingWeight_residueClass (ha : IsUnit a) : SamplingWeight (residueWeight a) := by
  refine ⟨residueWeight_nonneg, summable_of_le_vonMangoldt residueWeight_nonneg residueWeight_le,
    tendsto_wSum_residueWeight ha, fun c hc hre => ?_⟩
  have hlim : Tendsto (fun σ : ℝ => wSeries (residueWeight a) ((σ : ℂ) + c)) (𝓝[>] 1)
      (𝓝 (vonMangoldt.LFunctionResidueClassAux a (1 + c) + (q.totient : ℂ)⁻¹ / c)) := by
    have hpath : Tendsto (fun σ : ℝ => (σ : ℂ) + c) (𝓝[>] 1) (𝓝[{s | 1 ≤ s.re}] (1 + c)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have := (Complex.continuous_ofReal.add continuous_const).tendsto (1 : ℝ)
          (f := fun σ : ℝ => (σ : ℂ) + c)
        simpa using this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with σ hσ
        have hσ1 : 1 < σ := hσ
        show 1 ≤ ((σ : ℂ) + c).re
        simp; linarith
    have hcont := (vonMangoldt.continuousOn_LFunctionResidueClassAux a) (1 + c)
      (show 1 ≤ (1 + c).re by simp; linarith)
    have h1 := hcont.tendsto.comp hpath
    have h2 : Tendsto (fun σ : ℝ => (q.totient : ℂ)⁻¹ / ((σ : ℂ) + c - 1)) (𝓝[>] 1)
        (𝓝 ((q.totient : ℂ)⁻¹ / c)) := by
      have h3 : Tendsto (fun σ : ℝ => (σ : ℂ) + c - 1) (𝓝[>] 1) (𝓝 c) := by
        have := ((Complex.continuous_ofReal.add continuous_const).sub continuous_const).tendsto
          (1 : ℝ) (f := fun σ : ℝ => (σ : ℂ) + c - 1)
        simpa using this.mono_left nhdsWithin_le_nhds
      exact tendsto_const_nhds.div h3 hc
    refine (h1.add h2).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    have hσ1 : 1 < σ := hσ
    have hs : 1 < ((σ : ℂ) + c).re := by simp; linarith
    have heq := vonMangoldt.eqOn_LFunctionResidueClassAux (q := q) (a := a) ha hs
    simp only [Function.comp_def]
    rw [heq, wSeries_residueWeight_eq hs]
    ring
  have hden := tendsto_wSum_residueWeight ha
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hnorm : ∀ᶠ σ : ℝ in 𝓝[>] (1 : ℝ), ‖wSeries (residueWeight a) ((σ : ℂ) + c) /
      (wSum (residueWeight a) σ : ℂ)‖ =
        ‖wSeries (residueWeight a) ((σ : ℂ) + c)‖ / wSum (residueWeight a) σ := by
    filter_upwards [hden.eventually (eventually_gt_atTop 0)] with σ hV
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hV]
  exact ((hlim.norm).div_atTop hden).congr' (hnorm.mono fun σ h => h.symm)

omit [NeZero q] in
/-- A bound at the prime powers `n ≡ a (mod q)` is a bound where the residue weight is nonzero. -/
theorem bound_of_residueWeight_ne_zero {Z : ZeroConfig} {K : ℝ}
    (hK : ∀ n : ℕ, IsPrimePow n → (n : ZMod q) = a →
      -K ≤ 2 * (lagStructure Z (boxSpline 1 3) (Real.log n)).re) :
    ∀ j : ℕ, residueWeight a j ≠ 0 →
      -K ≤ 2 * (lagStructure Z (boxSpline 1 3) (Real.log (j + 1))).re := by
  intro j hj
  have hj' : vonMangoldt.residueClass a (j + 1) ≠ 0 := hj
  simp only [vonMangoldt.residueClass, Set.indicator_apply, Set.mem_setOf_eq] at hj'
  split_ifs at hj' with hmod
  · have := hK (j + 1) (vonMangoldt_ne_zero_iff.mp hj') hmod
    push_cast at this
    exact this
  · exact absurd rfl hj'

/-- **The primes in a residue class sample every top layer.** For a unit `a` mod `q`, a lower bound
at the prime powers `n ≡ a (mod q)` puts every zero of a tempered configuration without real zeros
and with an attained maximal real part on the critical line. -/
theorem onLine_of_bddBelow_primePowers_mod_of_max (ha : IsUnit a) (Z : ZeroConfig)
    (hZ : TemperedConfig Z) (hnoreal : ∀ ρ ∈ Z.carrier, ρ.im ≠ 0) {ρ₀ : ℂ}
    (hρ₀ : ρ₀ ∈ Z.carrier) (hmax : ∀ ρ ∈ Z.carrier, ρ.re ≤ ρ₀.re) {K : ℝ}
    (hK : ∀ n : ℕ, IsPrimePow n → (n : ZMod q) = a →
      -K ≤ 2 * (lagStructure Z (boxSpline 1 3) (Real.log n)).re) :
    ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2 :=
  onLine_of_bddBelow_of_samplingWeight (samplingWeight_residueClass ha) Z hZ hnoreal hρ₀ hmax
    (bound_of_residueWeight_ne_zero hK)

/-- **Masking is the only blindness at the primes in a residue class.** -/
theorem onLine_or_re_mem_of_bddBelow_primePowers_mod (ha : IsUnit a) (Z : ZeroConfig)
    (hZ : TemperedConfig Z) {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ Z.carrier) (hmax : ∀ ρ ∈ Z.carrier, ρ.re ≤ ρ₀.re)
    {K : ℝ} (hK : ∀ n : ℕ, IsPrimePow n → (n : ZMod q) = a →
      -K ≤ 2 * (lagStructure Z (boxSpline 1 3) (Real.log n)).re) :
    (∀ ρ ∈ Z.carrier, ρ.re = 1 / 2) ∨ (ρ₀.re : ℂ) ∈ Z.carrier :=
  onLine_or_re_mem_of_bddBelow_of_samplingWeight (samplingWeight_residueClass ha) Z hZ hρ₀ hmax
    (bound_of_residueWeight_ne_zero hK)

/-- **Real zeros are the only lower-side obstruction for `L(s, χ)`.** For a primitive character `χ`
mod `N` whose nontrivial zeros have an attained maximal real part `Re ρ₀`, a lower bound on the
spline traces of these zeros at the prime powers `n ≡ a (mod q)` gives GRH for `L(s, χ)` or makes
`Re ρ₀` a real zero of `L(s, χ)`. -/
theorem grh_or_real_zero_of_bddBelow_primePowers_mod {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hN : 1 < N) (hprim : χ.IsPrimitive) (ha : IsUnit a) {ρ₀ : ℂ}
    (hρ₀ : ρ₀ ∈ (ThmE.LZeros (ThmE.LSeam_of hN hprim)).carrier)
    (hmax : ∀ ρ ∈ (ThmE.LZeros (ThmE.LSeam_of hN hprim)).carrier, ρ.re ≤ ρ₀.re) {K : ℝ}
    (hK : ∀ n : ℕ, IsPrimePow n → (n : ZMod q) = a →
      -K ≤ 2 * (lagStructure (ThmE.LZeros (ThmE.LSeam_of hN hprim)) (boxSpline 1 3)
        (Real.log n)).re) :
    (∀ ρ ∈ (ThmE.LZeros (ThmE.LSeam_of hN hprim)).carrier, ρ.re = 1 / 2) ∨
      (ρ₀.re : ℂ) ∈ (ThmE.LZeros (ThmE.LSeam_of hN hprim)).carrier :=
  onLine_or_re_mem_of_bddBelow_primePowers_mod ha _ (temperedConfig_LZeros hN hprim) hρ₀ hmax hK

end ResidueClass

end GaloisForLFunctions.SurfaceOfSpecZ
