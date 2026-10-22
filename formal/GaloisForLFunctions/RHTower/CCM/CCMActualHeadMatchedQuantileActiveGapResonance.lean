import GaloisForLFunctions.RHTower.CCM.CCMActualHeadMatchedQuantilePolarParabolicVarianceBalance

noncomputable section

namespace RHTower

/-- On an interval with no intervening prime-power atom, the equal-mass quantile
centroid gap is carried solely by the two endpoint atoms. -/
theorem ccmActualHeadQuantilePolarCentroid_gap_of_no_intermediate_atom
    {m n : ℕ} (hmn : m < n)
    (hfree : ∀ k : ℕ, m < k → k < n → criticalMellinAtomWeight k = 0) :
    ccmActualHeadQuantilePolarCentroid n -
        ccmActualHeadQuantilePolarCentroid m =
      (criticalMellinAtomWeight m + criticalMellinAtomWeight n) / 2 := by
  let y := ccmActualHeadQuantilePolarCoordinate
  have hflat : ∀ k : ℕ, m + 1 ≤ k → k ≤ n → y k = y (m + 1) := by
    intro k hmk
    induction k, hmk using Nat.le_induction with
    | base => intro _; rfl
    | succ k hmk ih =>
      intro hkn
      have hklt : k < n := by omega
      have hkm : m < k := by omega
      have hstep := ccmActualHeadQuantilePolarCoordinate_succ_sub_eq_atomWeight k
      change y (k + 1) - y k = criticalMellinAtomWeight k at hstep
      rw [hfree k hkm hklt] at hstep
      linarith [ih (by omega)]
  have hy : y n = y (m + 1) := hflat n (by omega) le_rfl
  have hm := ccmActualHeadQuantilePolarCoordinate_succ_sub_eq_atomWeight m
  have hn := ccmActualHeadQuantilePolarCoordinate_succ_sub_eq_atomWeight n
  change y (m + 1) - y m = criticalMellinAtomWeight m at hm
  change y (n + 1) - y n = criticalMellinAtomWeight n at hn
  change (y n + y (n + 1)) / 2 - (y m + y (m + 1)) / 2 = _
  linarith only [hy, hm, hn]

/-- A pair of adjacent active atoms can have identical matched--quantile
translation only at one exact geometric/arithmetical gap resonance. -/
theorem ccmActualHeadMatchedQuantilePolarDisplacement_eq_iff_gap_resonance
    {m n : ℕ} (hmn : m < n)
    (hfree : ∀ k : ℕ, m < k → k < n → criticalMellinAtomWeight k = 0) :
    ccmActualHeadMatchedQuantilePolarDisplacement n =
        ccmActualHeadMatchedQuantilePolarDisplacement m ↔
      ccmActualHeadMatchedPolarCentroid n -
          ccmActualHeadMatchedPolarCentroid m =
        (criticalMellinAtomWeight m + criticalMellinAtomWeight n) / 2 := by
  have hq := ccmActualHeadQuantilePolarCentroid_gap_of_no_intermediate_atom hmn hfree
  rw [ccmActualHeadQuantilePolarCentroid_eq_matched_add_displacement,
    ccmActualHeadQuantilePolarCentroid_eq_matched_add_displacement] at hq
  constructor <;> intro h <;> linarith only [hq, h]

/-- Equal displacement across a literal atom-free interval forces an exact
integer-gap/endpoint-weight resonance.  Its coefficient is the physical
matched-cell junction, not a free clock. -/
theorem ccmActualHeadMatchedQuantilePolarDisplacement_eq_imp_gap_mass_law
    {m n : ℕ} (hm : 0 < m) (hmn : m < n)
    (hfree : ∀ k : ℕ, m < k → k < n → criticalMellinAtomWeight k = 0)
    (heq : ccmActualHeadMatchedQuantilePolarDisplacement n =
      ccmActualHeadMatchedQuantilePolarDisplacement m) :
    4 * ((n : ℝ) - m) =
      (ccmActualHeadMatchedPolarCentroid m + criticalMellinAtomWeight m / 2) *
        (criticalMellinAtomWeight m + criticalMellinAtomWeight n) := by
  let cm := ccmActualHeadMatchedPolarCentroid m
  let cn := ccmActualHeadMatchedPolarCentroid n
  let wm := criticalMellinAtomWeight m
  let wn := criticalMellinAtomWeight n
  have hgap :=
    (ccmActualHeadMatchedQuantilePolarDisplacement_eq_iff_gap_resonance hmn hfree).mp heq
  change cn - cm = (wm + wn) / 2 at hgap
  have hsm := ccmActualHeadMatchedPolarCentroid_sq m hm
  have hsn := ccmActualHeadMatchedPolarCentroid_sq n (hm.trans hmn)
  change cm ^ (2 : ℕ) = 4 * (m : ℝ) + wm ^ (2 : ℕ) / 4 at hsm
  change cn ^ (2 : ℕ) = 4 * (n : ℝ) + wn ^ (2 : ℕ) / 4 at hsn
  have hcn : cn = cm + (wm + wn) / 2 := by linarith only [hgap]
  rw [hcn] at hsn
  change 4 * ((n : ℝ) - m) = (cm + wm / 2) * (wm + wn)
  nlinarith only [hsm, hsn]

/-- At a resonant pair of consecutive active primes, the integer gap cannot
exceed `log p` by more than the explicit quadratic correction.  This uses the
actual prime atom weights and monotonicity of `log x / sqrt x`; a matching
lower estimate is still required for resonance rarity. -/
theorem ccmActualHeadMatchedQuantileResonantPrimeGap_upper
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (hpexp : Real.exp 2 ≤ (p : ℝ))
    (hfree : ∀ k : ℕ, p < k → k < q → criticalMellinAtomWeight k = 0)
    (heq : ccmActualHeadMatchedQuantilePolarDisplacement q =
      ccmActualHeadMatchedQuantilePolarDisplacement p) :
    (q : ℝ) - p ≤ Real.log p + Real.log p ^ (2 : ℕ) / (2 * p) := by
  let a : ℝ := criticalMellinAtomWeight p
  let b : ℝ := criticalMellinAtomWeight q
  let c : ℝ := ccmActualHeadMatchedPolarCentroid p
  let s : ℝ := Real.sqrt (p : ℝ)
  let l : ℝ := Real.log (p : ℝ)
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hqR : (p : ℝ) ≤ q := by exact_mod_cast hpq.le
  have hs : 0 < s := Real.sqrt_pos.mpr hpR
  have hl : 0 ≤ l := Real.log_nonneg (by
    exact_mod_cast hp.one_lt.le)
  have ha : a = l / s := by
    dsimp only [a, l, s]
    rw [criticalMellinAtomWeight_eq_div_sqrt,
      ArithmeticFunction.vonMangoldt_apply_prime hp]
  have hb : b = Real.log (q : ℝ) / Real.sqrt q := by
    dsimp only [b]
    rw [criticalMellinAtomWeight_eq_div_sqrt,
      ArithmeticFunction.vonMangoldt_apply_prime hq]
  have hb_le : b ≤ a := by
    rw [ha, hb]
    exact Real.log_div_sqrt_antitoneOn
      (Set.mem_Ici.mpr hpexp)
      (Set.mem_Ici.mpr (hpexp.trans hqR)) hqR
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have hb0 : 0 ≤ b := by
    rw [hb]
    have hlog : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by
      exact_mod_cast hq.one_lt.le)
    positivity
  have hcsq := ccmActualHeadMatchedPolarCentroid_sq p hp.pos
  change c ^ (2 : ℕ) = 4 * (p : ℝ) + a ^ (2 : ℕ) / 4 at hcsq
  have hc0 : 0 < c := ccmActualHeadMatchedPolarCentroid_pos p
  have hssq : s ^ (2 : ℕ) = (p : ℝ) := Real.sq_sqrt hpR.le
  have hc_le : c ≤ 2 * s + a / 2 := by
    nlinarith only [hcsq, hssq, hc0, hs, ha0,
      mul_nonneg (show 0 ≤ s by positivity) ha0]
  have hgap := ccmActualHeadMatchedQuantilePolarDisplacement_eq_imp_gap_mass_law
    hp.pos hpq hfree heq
  change 4 * ((q : ℝ) - p) = (c + a / 2) * (a + b) at hgap
  have hcore : 4 * ((q : ℝ) - p) ≤ (2 * s + a) * (2 * a) := by
    calc
      4 * ((q : ℝ) - p) = (c + a / 2) * (a + b) := hgap
      _ ≤ (2 * s + a) * (a + b) := by
        exact mul_le_mul_of_nonneg_right (by linarith only [hc_le])
          (add_nonneg ha0 hb0)
      _ ≤ (2 * s + a) * (2 * a) := by
        exact mul_le_mul_of_nonneg_left (by linarith only [hb_le])
          (by positivity)
  rw [ha] at hcore
  have hiden : (2 * s + l / s) * (2 * (l / s)) =
      4 * l + 2 * l ^ (2 : ℕ) / (p : ℝ) := by
    rw [← hssq]
    field_simp [hs.ne']
    ring
  rw [hiden] at hcore
  dsimp only [l] at *
  calc
    (q : ℝ) - p ≤
        (4 * Real.log p + 2 * Real.log p ^ (2 : ℕ) / (p : ℝ)) / 4 := by
          linarith only [hcore]
    _ = Real.log p + Real.log p ^ (2 : ℕ) / (2 * p) := by ring

private theorem sqrt_inverse_tangent_lower
    {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    (1 - (y - x) / (2 * x)) * Real.sqrt y ≤ Real.sqrt x := by
  let s := Real.sqrt x
  let t := Real.sqrt y
  have hs : 0 < s := Real.sqrt_pos.mpr hx
  have ht : 0 < t := Real.sqrt_pos.mpr (hx.trans_le hxy)
  have hssq : s ^ (2 : ℕ) = x := Real.sq_sqrt hx.le
  have htsq : t ^ (2 : ℕ) = y := Real.sq_sqrt (hx.trans_le hxy).le
  have hpos : 0 ≤ (t - s) ^ (2 : ℕ) * (t + 2 * s) := by positivity
  have hident :
      s - (1 - (y - x) / (2 * x)) * t =
        (t - s) ^ (2 : ℕ) * (t + 2 * s) / (2 * x) := by
    rw [← hssq, ← htsq]
    field_simp [hs.ne']
    ring
  change (1 - (y - x) / (2 * x)) * t ≤ s
  have hquot : 0 ≤ (t - s) ^ (2 : ℕ) * (t + 2 * s) / (2 * x) := by
    positivity
  linarith only [hident, hquot]

/-- The opposite side of the prime-gap resonance: convexity of inverse square
root keeps the later atom's weight close to the earlier one, forcing the
integer gap to stay near `log p` from below.  This retains the actual prime
weights and needs no lower cutoff beyond primality. -/
theorem ccmActualHeadMatchedQuantileResonantPrimeGap_lower
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (hfree : ∀ k : ℕ, p < k → k < q → criticalMellinAtomWeight k = 0)
    (heq : ccmActualHeadMatchedQuantilePolarDisplacement q =
      ccmActualHeadMatchedQuantilePolarDisplacement p) :
    Real.log p - ((q : ℝ) - p) ≤
      Real.log p * ((q : ℝ) - p) / (4 * p) := by
  let a : ℝ := criticalMellinAtomWeight p
  let b : ℝ := criticalMellinAtomWeight q
  let c : ℝ := ccmActualHeadMatchedPolarCentroid p
  let s : ℝ := Real.sqrt (p : ℝ)
  let t : ℝ := Real.sqrt (q : ℝ)
  let l : ℝ := Real.log (p : ℝ)
  let g : ℝ := (q : ℝ) - p
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hpqR : (p : ℝ) ≤ q := by exact_mod_cast hpq.le
  have hs : 0 < s := Real.sqrt_pos.mpr hpR
  have ht : 0 < t := Real.sqrt_pos.mpr hqR
  have hl : 0 ≤ l := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  have ha : a = l / s := by
    dsimp only [a, l, s]
    rw [criticalMellinAtomWeight_eq_div_sqrt,
      ArithmeticFunction.vonMangoldt_apply_prime hp]
  have hb : b = Real.log (q : ℝ) / t := by
    dsimp only [b, t]
    rw [criticalMellinAtomWeight_eq_div_sqrt,
      ArithmeticFunction.vonMangoldt_apply_prime hq]
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have hb0 : 0 ≤ b := by
    rw [hb]
    have hlog : 0 ≤ Real.log (q : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hq.one_lt.le)
    positivity
  have hlogle : l ≤ Real.log (q : ℝ) :=
    Real.log_le_log hpR hpqR
  have htan := sqrt_inverse_tangent_lower hpR hpqR
  change (1 - g / (2 * (p : ℝ))) * t ≤ s at htan
  have hrec : (1 - g / (2 * (p : ℝ))) / s ≤ 1 / t := by
    apply (div_le_div_iff₀ hs ht).mpr
    simpa only [one_mul] using htan
  have hb_lower : l / s * (1 - g / (2 * (p : ℝ))) ≤ b := by
    rw [hb]
    calc
      l / s * (1 - g / (2 * (p : ℝ))) =
          l * ((1 - g / (2 * (p : ℝ))) / s) := by ring
      _ ≤ l * (1 / t) := mul_le_mul_of_nonneg_left hrec hl
      _ ≤ Real.log (q : ℝ) * (1 / t) := by
        exact mul_le_mul_of_nonneg_right hlogle (by positivity)
      _ = Real.log (q : ℝ) / t := by ring
  have hcsq := ccmActualHeadMatchedPolarCentroid_sq p hp.pos
  change c ^ (2 : ℕ) = 4 * (p : ℝ) + a ^ (2 : ℕ) / 4 at hcsq
  have hc0 : 0 < c := ccmActualHeadMatchedPolarCentroid_pos p
  have hssq : s ^ (2 : ℕ) = (p : ℝ) := Real.sq_sqrt hpR.le
  have hc_lower : 2 * s ≤ c := by
    nlinarith only [hcsq, hssq, hc0, hs, sq_nonneg a]
  have hgap := ccmActualHeadMatchedQuantilePolarDisplacement_eq_imp_gap_mass_law
    hp.pos hpq hfree heq
  change 4 * g = (c + a / 2) * (a + b) at hgap
  have hcore : 4 * g ≥ 2 * s * (l / s * (2 - g / (2 * (p : ℝ)))) := by
    calc
      4 * g = (c + a / 2) * (a + b) := hgap
      _ ≥ 2 * s * (a + b) := by
        exact mul_le_mul_of_nonneg_right
          (by linarith only [hc_lower, ha0]) (add_nonneg ha0 hb0)
      _ ≥ 2 * s * (l / s * (2 - g / (2 * (p : ℝ)))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [ha]
        linarith only [hb_lower]
  have hident : 2 * s * (l / s * (2 - g / (2 * (p : ℝ)))) =
      4 * l - l * g / (p : ℝ) := by
    field_simp [hs.ne', hpR.ne']
    ring
  rw [hident] at hcore
  dsimp only [l, g] at *
  have hscaled : 4 * Real.log p -
      Real.log p * ((q : ℝ) - p) / (p : ℝ) ≤
        4 * ((q : ℝ) - p) := hcore
  have htmp : 4 * (Real.log p - ((q : ℝ) - p)) ≤
      Real.log p * ((q : ℝ) - p) / (p : ℝ) := by
        linarith only [hscaled]
  calc
    Real.log p - ((q : ℝ) - p) ≤
        (Real.log p * ((q : ℝ) - p) / (p : ℝ)) / 4 := by
          linarith only [htmp]
    _ = Real.log p * ((q : ℝ) - p) / (4 * p) := by ring

/-- Resonance pins a literal adjacent-prime integer gap to `log p` with
vanishing second-order error. This is the quantitative arithmetic input for
counting coherent source-active edges, not a signed-source bound by itself. -/
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
