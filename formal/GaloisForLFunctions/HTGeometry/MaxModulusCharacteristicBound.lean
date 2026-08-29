import GaloisForLFunctions.HTGeometry.NevanlinnaTranslationBoundary
import GaloisForLFunctions.HTGeometry.LogDerivPoissonJensen
import GaloisForLFunctions.HTGeometry.PolynomialAntiderivative
import GaloisForLFunctions.HTGeometry.BorelGoodRadii

/-!
# The maximum modulus is controlled by the characteristic

For an entire function the Poisson–Jensen formula has no pole term, so the interior value at a point
of modulus at most `r` is bounded by the Poisson-weighted boundary mean, hence by the characteristic
at the larger radius `R`:

```text
log⁺‖f w‖ ≤ (R+r)/(R−r) · (2·T(R,f) + K),   ‖w‖ ≤ r < R.
```

Consequently a characteristic that is logarithmically small along *some* sequence of radii forces
polynomial Cauchy estimates along that sequence, hence a polynomial; equivalently, an entire
function that is not a polynomial has `T(r,f)/log r → ∞`.

* `posLog_norm_le_characteristic` — the maximum modulus bound;
* `iteratedDeriv_eq_zero_of_frequently_growth` — the Cauchy estimate along a sequence of radii;
* `exists_polynomial_of_frequently_characteristic_le_log` — the recognition principle;
* `tendsto_characteristic_div_log_atTop` — transcendence forces superlogarithmic characteristic;
* `charMajorant_growth_of_not_polynomial` — the two Nevanlinna growth conditions from transcendence.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Metric Real Set Filter ValueDistribution MeromorphicOn
open scoped Topology

/-- **The interior maximum modulus is bounded by the characteristic at a larger radius.**  For an
entire function the Poisson–Jensen pole term vanishes. -/
theorem posLog_norm_le_characteristic {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (horder : ∀ u, meromorphicOrderAt f u ≠ ⊤) {R r : ℝ} (hR : 1 ≤ R) (hr0 : 0 ≤ r) (hrR : r < R)
    {w : ℂ} (hw : ‖w‖ ≤ r) :
    Real.posLog ‖f w‖ ≤ (R + r) / (R - r) *
      (2 * ValueDistribution.characteristic f ⊤ R
        + max |Real.log ‖f 0‖| |Real.log ‖meromorphicTrailingCoeffAt f 0‖|) := by
  have hR0 : (0 : ℝ) < R := by linarith
  have hfm : Meromorphic f := fun z => (hf.analyticAt z).meromorphicAt
  have hfan : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) |R|) :=
    fun z _ => hf.analyticAt z
  have hfactor : (0 : ℝ) ≤ (R + r) / (R - r) := by
    apply div_nonneg <;> linarith
  have habs := PoissonJensen.circleAverage_abs_log_norm_le_characteristic (r := R) hR hfm
  by_cases hfw : f w = 0
  · have hzero : Real.posLog ‖f w‖ = 0 := by
      rw [hfw]
      simp [Real.posLog]
    rw [hzero]
    refine mul_nonneg hfactor ?_
    have h1 : 0 ≤ ValueDistribution.characteristic f ⊤ R :=
      ValueDistribution.characteristic_nonneg (by linarith)
    have h2 : (0 : ℝ) ≤ max |Real.log ‖f 0‖| |Real.log ‖meromorphicTrailingCoeffAt f 0‖| :=
      le_trans (abs_nonneg _) (le_max_left _ _)
    linarith
  · have hwball : w ∈ ball (0 : ℂ) R := by
      rw [mem_ball_zero_iff]
      linarith [hw]
    have hpoisson := posLog_norm_le_poissonBoundary_add_poleGreen hR0 hfm horder hwball
      (hf.analyticAt w) hfw hw hrR
    have hdiv : 0 ≤ MeromorphicOn.divisor f (closedBall (0 : ℂ) |R|) :=
      (hfan.meromorphicNFOn.divisor_nonneg_iff_analyticOnNhd).mpr hfan
    have hpole : (∑ᶠ u : ℂ, (MeromorphicOn.divisor f (closedBall (0 : ℂ) |R|) u : ℝ)⁻ *
        (Real.log ‖PoissonJensen.innerLogKernel 0 u R w‖ - Real.log ‖w - u‖)) = 0 := by
      refine finsum_eq_zero_of_forall_eq_zero fun u => ?_
      have hu : (0 : ℤ) ≤ MeromorphicOn.divisor f (closedBall (0 : ℂ) |R|) u := hdiv u
      have huR : (0 : ℝ) ≤ (MeromorphicOn.divisor f (closedBall (0 : ℂ) |R|) u : ℝ) := by
        exact_mod_cast hu
      rw [negPart_eq_zero.mpr huR, zero_mul]
    rw [hpole, add_zero] at hpoisson
    refine le_trans hpoisson ?_
    exact mul_le_mul_of_nonneg_left habs hfactor

/-- **A Cauchy estimate along a sequence of radii.**  A growth bound holding on arbitrarily large
discs already kills every derivative of order above the exponent. -/
theorem iteratedDeriv_eq_zero_of_frequently_growth {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    {C a : ℝ} {n : ℕ} (ha0 : 0 ≤ a) (han : a < n) (hC : 0 < C)
    (hbound : ∃ᶠ R in atTop, ∀ z : ℂ, ‖z‖ ≤ R / 2 → ‖g z‖ ≤ C * R ^ a) (c : ℂ) :
    iteratedDeriv n g c = 0 := by
  have hkey : ∀ R : ℝ, 0 < R → 4 * ‖c‖ ≤ R → (∀ z : ℂ, ‖z‖ ≤ R / 2 → ‖g z‖ ≤ C * R ^ a) →
      ‖iteratedDeriv n g c‖ ≤ (n.factorial : ℝ) * (C * R ^ a) / (R / 4) ^ n := by
    intro R hR hRc hb
    refine norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n (by linarith)
      hg.diffContOnCl fun z hz => ?_
    have hz' : ‖z - c‖ = R / 4 := by simpa [Complex.dist_eq] using mem_sphere_iff_norm.1 hz
    have hzc : ‖z‖ ≤ R / 2 := by
      have hsub : ‖z‖ ≤ ‖z - c‖ + ‖c‖ := by simpa using norm_add_le (z - c) c
      rw [hz'] at hsub
      linarith
    exact hb z hzc
  have hlim : Tendsto (fun R : ℝ => (n.factorial : ℝ) * (C * R ^ a) / (R / 4) ^ n) atTop (𝓝 0) := by
    have hrw : ∀ R : ℝ, 0 < R →
        (n.factorial : ℝ) * (C * R ^ a) / (R / 4) ^ n
          = ((n.factorial : ℝ) * C * 4 ^ n) * R ^ (a - (n : ℝ)) := by
      intro R hR
      rw [div_pow, Real.rpow_sub hR, ← Real.rpow_natCast R n]
      field_simp
    have hpow : Tendsto (fun R : ℝ => R ^ (a - (n : ℝ))) atTop (𝓝 0) := by
      have hy : 0 < (n : ℝ) - a := by linarith
      have := tendsto_rpow_neg_atTop hy
      refine this.congr fun R => ?_
      congr 1
      ring
    have := hpow.const_mul ((n.factorial : ℝ) * C * 4 ^ n)
    rw [mul_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    exact (hrw R hR).symm
  by_contra hne
  have hpos : 0 < ‖iteratedDeriv n g c‖ := norm_pos_iff.mpr hne
  have hev : ∀ᶠ R : ℝ in atTop,
      (n.factorial : ℝ) * (C * R ^ a) / (R / 4) ^ n < ‖iteratedDeriv n g c‖ := by
    have := hlim.eventually (eventually_lt_nhds hpos)
    exact this
  have hcomb : ∃ᶠ R : ℝ in atTop, (∀ z : ℂ, ‖z‖ ≤ R / 2 → ‖g z‖ ≤ C * R ^ a) ∧
      ((n.factorial : ℝ) * (C * R ^ a) / (R / 4) ^ n < ‖iteratedDeriv n g c‖ ∧
        (0 < R ∧ 4 * ‖c‖ ≤ R)) := by
    refine hbound.and_eventually ?_
    filter_upwards [hev, eventually_gt_atTop (0 : ℝ), eventually_ge_atTop (4 * ‖c‖)]
      with R h1 h2 h3
    exact ⟨h1, h2, h3⟩
  obtain ⟨R, hb, hRlt, hRpos, hRc⟩ := hcomb.exists
  exact absurd (hkey R hRpos hRc hb) (not_le.mpr hRlt)

/-- An entire function whose meromorphic order is infinite at one point vanishes identically. -/
private theorem eq_zero_of_order_top {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {z : ℂ} (h : meromorphicOrderAt f z = ⊤) (w : ℂ) : f w = 0 := by
  have hfan : AnalyticOnNhd ℂ f Set.univ := hf.differentiableOn.analyticOnNhd isOpen_univ
  rw [meromorphicOrderAt_eq_top_iff] at h
  exact hfan.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
    (Set.mem_univ z) h.frequently (Set.mem_univ w)

/-- **Recognition of polynomials by the characteristic.**  An entire function whose characteristic
is logarithmically bounded along some sequence of radii is a polynomial. -/
theorem exists_polynomial_of_frequently_characteristic_le_log {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∃ᶠ R in atTop, ValueDistribution.characteristic f ⊤ R ≤ K * Real.log R) :
    ∃ p : Polynomial ℂ, ∀ z : ℂ, f z = p.eval z := by
  by_cases hzero : ∀ z : ℂ, f z = 0
  · exact ⟨0, by simpa using hzero⟩
  push_neg at hzero
  obtain ⟨z₀, hz₀⟩ := hzero
  have horder : ∀ u, meromorphicOrderAt f u ≠ ⊤ := fun u hu => hz₀ (eq_zero_of_order_top hf hu z₀)
  set C₀ : ℝ := max |Real.log ‖f 0‖| |Real.log ‖meromorphicTrailingCoeffAt f 0‖| with hC₀
  have hC₀0 : 0 ≤ C₀ := le_trans (abs_nonneg _) (le_max_left _ _)
  set a : ℝ := 6 * K with ha
  set C : ℝ := Real.exp (3 * C₀) with hCdef
  have hC0 : 0 < C := Real.exp_pos _
  -- the growth bound at the good radii
  have hgrowth : ∃ᶠ R in atTop, ∀ z : ℂ, ‖z‖ ≤ R / 2 → ‖f z‖ ≤ C * R ^ a := by
    refine (hbound.and_eventually (eventually_ge_atTop (2 : ℝ))).mono ?_
    rintro R ⟨hTR, hR2⟩ z hz
    have hR1 : (1 : ℝ) ≤ R := by linarith
    have hlogR : 0 ≤ Real.log R := Real.log_nonneg hR1
    have hpl := posLog_norm_le_characteristic hf horder (r := R / 2) hR1 (by linarith)
      (by linarith) hz
    have hratio : (R + R / 2) / (R - R / 2) = 3 := by
      field_simp
      ring
    rw [hratio] at hpl
    have hbnd : Real.posLog ‖f z‖ ≤ 6 * K * Real.log R + 3 * C₀ := by
      have hTle : ValueDistribution.characteristic f ⊤ R ≤ K * Real.log R := hTR
      nlinarith [hpl, hTle, hC₀0]
    have hexp : ‖f z‖ ≤ Real.exp (Real.posLog ‖f z‖) := by
      rcases le_or_gt ‖f z‖ 1 with h | h
      · have h0 : (0 : ℝ) ≤ Real.posLog ‖f z‖ := le_max_left _ _
        have h1 : (1 : ℝ) ≤ Real.exp (Real.posLog ‖f z‖) := Real.one_le_exp h0
        linarith
      · rw [Real.posLog, max_eq_right (Real.log_nonneg h.le), Real.exp_log (by linarith)]
    calc ‖f z‖ ≤ Real.exp (Real.posLog ‖f z‖) := hexp
      _ ≤ Real.exp (6 * K * Real.log R + 3 * C₀) := Real.exp_le_exp.mpr hbnd
      _ = C * R ^ a := by
          rw [hCdef, ha, Real.exp_add, Real.rpow_def_of_pos (by linarith : (0:ℝ) < R)]
          ring_nf
  -- kill the high derivatives
  set n : ℕ := ⌊a⌋₊ + 1 with hn
  have han : a < (n : ℝ) := by
    rw [hn]
    push_cast
    exact Nat.lt_floor_add_one a
  have ha0 : 0 ≤ a := by rw [ha]; linarith
  have hderiv : ∀ z : ℂ, iteratedDeriv n f z = 0 :=
    fun z => iteratedDeriv_eq_zero_of_frequently_growth hf ha0 han hC0 hgrowth z
  obtain ⟨m, hm⟩ : ∃ m : ℕ, n = m + 1 := ⟨n - 1, by omega⟩
  rw [hm] at hderiv
  exact exists_polynomial_of_iteratedDeriv_eq_zero hf hderiv

/-- **Transcendence forces a superlogarithmic characteristic.** -/
theorem tendsto_characteristic_div_log_atTop {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hnp : ¬ ∃ p : Polynomial ℂ, ∀ z : ℂ, f z = p.eval z) :
    Tendsto (fun r => ValueDistribution.characteristic f ⊤ r / Real.log r) atTop atTop := by
  rw [Filter.tendsto_atTop]
  intro b
  by_contra hcon
  rw [not_eventually] at hcon
  set K : ℝ := max b 0 with hK
  have hK0 : 0 ≤ K := le_max_right _ _
  refine hnp (exists_polynomial_of_frequently_characteristic_le_log hf hK0 ?_)
  refine (hcon.and_eventually (eventually_gt_atTop (1 : ℝ))).mono ?_
  rintro r ⟨hlt, hr1⟩
  rw [not_le] at hlt
  have hlog : 0 < Real.log r := Real.log_pos hr1
  rw [div_lt_iff₀ hlog] at hlt
  have : b ≤ K := le_max_left _ _
  nlinarith [hlt, hlog]

/-- **The two Nevanlinna growth conditions from transcendence alone.** -/
theorem charMajorant_growth_of_not_polynomial {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hnp : ¬ ∃ p : Polynomial ℂ, ∀ z : ℂ, f z = p.eval z) :
    Tendsto (charMajorant f) atTop atTop ∧
      Tendsto (fun r => Real.log r / charMajorant f r) atTop (𝓝 0) := by
  have hdiv := tendsto_characteristic_div_log_atTop hf hnp
  constructor
  · refine tendsto_atTop_mono' atTop ?_ hdiv
    filter_upwards [eventually_ge_atTop (Real.exp 1)] with r hr
    have hr1 : (1 : ℝ) ≤ r := le_trans (le_trans (by norm_num) (Real.add_one_le_exp 1)) hr
    have hlog : (1 : ℝ) ≤ Real.log r := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      exact hr
    have hchar := characteristic_le_charMajorant (f := f) hr1
    have hT0 : 0 ≤ ValueDistribution.characteristic f ⊤ r :=
      ValueDistribution.characteristic_nonneg (by linarith)
    calc ValueDistribution.characteristic f ⊤ r / Real.log r
        ≤ ValueDistribution.characteristic f ⊤ r := by
          rw [div_le_iff₀ (by linarith)]
          nlinarith
      _ ≤ charMajorant f r := hchar
  · have hinv : Tendsto
        (fun r => (ValueDistribution.characteristic f ⊤ r / Real.log r)⁻¹) atTop (𝓝 0) :=
      hdiv.inv_tendsto_atTop
    refine squeeze_zero' ?_ ?_ hinv
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
      exact div_nonneg (Real.log_nonneg hr) (by linarith [one_le_charMajorant f r])
    · filter_upwards [eventually_ge_atTop (Real.exp 1),
        hdiv.eventually_gt_atTop (0 : ℝ)] with r hr hpos
      have hr1 : (1 : ℝ) ≤ r := le_trans (le_trans (by norm_num) (Real.add_one_le_exp 1)) hr
      have hlog : (1 : ℝ) ≤ Real.log r := by
        rw [Real.le_log_iff_exp_le (by linarith)]
        exact hr
      have hT0 : 0 < ValueDistribution.characteristic f ⊤ r := by
        by_contra hcon
        push_neg at hcon
        have : ValueDistribution.characteristic f ⊤ r / Real.log r ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg hcon (by linarith)
        linarith
      have hchar := characteristic_le_charMajorant (f := f) hr1
      rw [inv_div]
      exact div_le_div_of_nonneg_left (by linarith) (by linarith) hchar

end GaloisForLFunctions.HTGeometry
