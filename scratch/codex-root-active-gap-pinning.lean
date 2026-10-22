import GaloisForLFunctions.RHTower.CCM.CCMActualHeadMatchedQuantileActiveGapResonance

noncomputable section
namespace RHTower

/-- A literal resonant consecutive-prime gap is pinned to log p to second order. -/
theorem ccmActualHeadMatchedQuantileResonantPrimeGap_abs_log_le
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (hpexp : Real.exp 2 ≤ (p : ℝ))
    (hfree : ∀ k : ℕ, p < k → k < q → criticalMellinAtomWeight k = 0)
    (heq : ccmActualHeadMatchedQuantilePolarDisplacement q =
      ccmActualHeadMatchedQuantilePolarDisplacement p) :
    |((q : ℝ) - p) - Real.log p| ≤ Real.log p ^ (2 : ℕ) / (2 * p) := by
  let l : ℝ := Real.log (p : ℝ)
  let g : ℝ := (q : ℝ) - p
  let P : ℝ := (p : ℝ)
  have hpR : 0 < P := by
    dsimp only [P]
    exact_mod_cast hp.pos
  have hl0 : 0 ≤ l := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  have hle : l ≤ P := Real.log_le_self hpR.le
  have hu := ccmActualHeadMatchedQuantileResonantPrimeGap_upper hp hq hpq hpexp hfree heq
  have hd := ccmActualHeadMatchedQuantileResonantPrimeGap_lower hp hq hpq hfree heq
  change g ≤ l + l ^ (2 : ℕ) / (2 * P) at hu
  change l - g ≤ l * g / (4 * P) at hd
  have hsq : l ^ (2 : ℕ) / (2 * P) ≤ l := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * P)).mpr
    nlinarith only [mul_nonneg hl0 (sub_nonneg.mpr hle), hl0]
  have hg2 : g ≤ 2 * l := by linarith only [hu, hsq]
  have hmul : l * g ≤ 2 * l ^ (2 : ℕ) := by
    nlinarith only [mul_le_mul_of_nonneg_left hg2 hl0]
  have hlow : l - g ≤ l ^ (2 : ℕ) / (2 * P) := by
    calc
      l - g ≤ l * g / (4 * P) := hd
      _ ≤ (2 * l ^ (2 : ℕ)) / (4 * P) :=
        div_le_div_of_nonneg_right hmul (by positivity)
      _ = l ^ (2 : ℕ) / (2 * P) := by ring
  change |g - l| ≤ l ^ (2 : ℕ) / (2 * P)
  exact abs_le.mpr ⟨by linarith only [hlow], by linarith only [hu]⟩

/-- Odd-centered logarithmic windows contain no resonant adjacent odd-prime edge. -/
theorem ccmActualHeadMatchedQuantile_no_resonant_prime_edge_on_odd_log_band
    {p q t : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (hp2 : p ≠ 2)
    (hpexp : Real.exp 2 ≤ (p : ℝ))
    (hloglo : ((2 * t + 1 : ℕ) : ℝ) ≤ Real.log p)
    (hloghi : Real.log p ≤ ((2 * t + 1 : ℕ) : ℝ) + 1 / 4)
    (herror : Real.log p ^ (2 : ℕ) / (2 * p) < 1 / 4)
    (hfree : ∀ k : ℕ, p < k → k < q → criticalMellinAtomWeight k = 0) :
    ccmActualHeadMatchedQuantilePolarDisplacement q ≠
      ccmActualHeadMatchedQuantilePolarDisplacement p := by
  intro heq
  have hpin := ccmActualHeadMatchedQuantileResonantPrimeGap_abs_log_le
    hp hq hpq hpexp hfree heq
  have hpin' := abs_le.mp hpin
  have hglow : ((2 * t + 1 : ℕ) : ℝ) - 1 / 4 <
      (q : ℝ) - p := by
    linarith only [hpin'.1, hloglo, herror]
  have hghigh : (q : ℝ) - p <
      ((2 * t + 1 : ℕ) : ℝ) + 1 / 2 := by
    linarith only [hpin'.2, hloghi, herror]
  have hgaplo : 2 * t + 1 ≤ q - p := by
    by_contra hc
    have hnat : q - p ≤ 2 * t := by omega
    have hcast : ((q - p : ℕ) : ℝ) ≤ ((2 * t : ℕ) : ℝ) := by
      exact_mod_cast hnat
    rw [Nat.cast_sub hpq.le] at hcast
    push_cast at hcast hglow
    linarith only [hcast, hglow]
  have hgaphigh : q - p < 2 * t + 2 := by
    have hcast : ((q - p : ℕ) : ℝ) < ((2 * t + 2 : ℕ) : ℝ) := by
      rw [Nat.cast_sub hpq.le]
      push_cast
      push_cast at hghigh
      linarith only [hghigh]
    exact_mod_cast hcast
  have hpodd := hp.odd_of_ne_two hp2
  have hq2 : q ≠ 2 := by
    have hpge := hp.two_le
    omega
  have hqodd := hq.odd_of_ne_two hq2
  obtain ⟨a, ha⟩ := hpodd
  obtain ⟨b, hb⟩ := hqodd
  omega

/-- The logarithmic correction is eventually smaller than one quarter. -/
theorem eventually_ccmActualHead_prime_gap_resonance_error_lt_quarter :
    ∀ᶠ x : ℝ in Filter.atTop,
      Real.log x ^ (2 : ℕ) / (2 * x) < 1 / 4 := by
  have hzero : Filter.Tendsto
      (fun x : ℝ => Real.log x ^ (2 : ℕ) / x)
      Filter.atTop (nhds 0) := by
    simpa using (Real.isLittleO_pow_log_id_atTop (n := 2)).tendsto_div_nhds_zero
  have hsmall := hzero.eventually
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [hsmall] with x hx
  have hid : Real.log x ^ (2 : ℕ) / (2 * x) =
      (Real.log x ^ (2 : ℕ) / x) / 2 := by ring
  rw [hid]
  linarith

/-- Odd-centered exponential windows forbid literal equal-displacement
adjacent odd-prime edges once the asymptotic correction is small. -/
theorem ccmActualHeadMatchedQuantile_no_resonant_prime_edge_on_odd_exp_window
    {p q t : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (hp2 : p ≠ 2)
    (hpexp : Real.exp 2 ≤ (p : ℝ))
    (hlo : Real.exp ((2 * t + 1 : ℕ) : ℝ) ≤ (p : ℝ))
    (hhi : (p : ℝ) ≤ Real.exp (((2 * t + 1 : ℕ) : ℝ) + 1 / 4))
    (herror : Real.log p ^ (2 : ℕ) / (2 * p) < 1 / 4)
    (hfree : ∀ k : ℕ, p < k → k < q → criticalMellinAtomWeight k = 0) :
    ccmActualHeadMatchedQuantilePolarDisplacement q ≠
      ccmActualHeadMatchedQuantilePolarDisplacement p := by
  have hloglo : ((2 * t + 1 : ℕ) : ℝ) ≤ Real.log p := by
    have h := Real.log_le_log (Real.exp_pos _) hlo
    simpa only [Real.log_exp] using h
  have hloghi : Real.log p ≤ ((2 * t + 1 : ℕ) : ℝ) + 1 / 4 := by
    have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have h := Real.log_le_log hpR hhi
    simpa only [Real.log_exp] using h
  exact ccmActualHeadMatchedQuantile_no_resonant_prime_edge_on_odd_log_band
    hp hq hpq hp2 hpexp hloglo hloghi herror hfree

end RHTower

#print axioms RHTower.ccmActualHeadMatchedQuantileResonantPrimeGap_upper
#print axioms RHTower.ccmActualHeadMatchedQuantileResonantPrimeGap_lower
#print axioms RHTower.ccmActualHeadMatchedQuantileResonantPrimeGap_abs_log_le
#print axioms RHTower.ccmActualHeadMatchedQuantile_no_resonant_prime_edge_on_odd_log_band
#print axioms RHTower.eventually_ccmActualHead_prime_gap_resonance_error_lt_quarter
#print axioms RHTower.ccmActualHeadMatchedQuantile_no_resonant_prime_edge_on_odd_exp_window
