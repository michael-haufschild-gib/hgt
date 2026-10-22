import GaloisForLFunctions.RHTower.CCM.CCMActualHeadMatchedQuantilePrimeGapDefectStability

/-!
# Quantitative displacement on actual odd-log active prime pairs

The fixed arithmetic resonance defect forces a signed matched-quantile
displacement increment of magnitude at least `1/(4 sqrt p)` across any
adjacent active odd-prime pair in a late odd-log window. This result retains
the literal von Mangoldt atoms. It does not establish a cofinal signed
prime--polar bound or RH.
-/

namespace RHTower

private theorem oddPrimeGap_displacement_product_lower
    {p q t : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (hp2 : p ≠ 2) (hpexp : Real.exp 2 ≤ (p : ℝ))
    (hloglo : ((2 * t + 1 : ℕ) : ℝ) ≤ Real.log p)
    (hloghi : Real.log p ≤ ((2 * t + 1 : ℕ) : ℝ) + 1 / 4)
    (herror : Real.log p ^ (2 : ℕ) / (2 * p) < 1 / 4)
    (hfree : ∀ k : ℕ, p < k → k < q → criticalMellinAtomWeight k = 0) :
    let d := ccmActualHeadMatchedQuantilePolarDisplacement q -
      ccmActualHeadMatchedQuantilePolarDisplacement p
    let L := 2 * ccmActualHeadMatchedPolarCentroid p +
      criticalMellinAtomWeight p + criticalMellinAtomWeight q
    2 ≤ |d| * |d - L| := by
  let d := ccmActualHeadMatchedQuantilePolarDisplacement q -
    ccmActualHeadMatchedQuantilePolarDisplacement p
  let L := 2 * ccmActualHeadMatchedPolarCentroid p +
    criticalMellinAtomWeight p + criticalMellinAtomWeight q
  let R := (ccmActualHeadMatchedPolarCentroid p + criticalMellinAtomWeight p / 2) *
    (criticalMellinAtomWeight p + criticalMellinAtomWeight q) / 4
  let g : ℝ := (q : ℝ) - p
  have hsep : 1 / 2 ≤ |g - R| :=
    ccmActualHeadMatchedQuantile_oddPrimeGap_center_separated hp hq hpq
      hp2 hpexp hloglo hloghi herror
  have hid := ccmActualHeadMatchedQuantile_activeGap_defect_identity hp.pos hpq hfree
  have hfactor : 4 * (g - R) = d * (d - L) := by
    dsimp only [g, R, d, L]
    calc
      4 * (((q : ℝ) - p) -
        (ccmActualHeadMatchedPolarCentroid p + criticalMellinAtomWeight p / 2) *
          (criticalMellinAtomWeight p + criticalMellinAtomWeight q) / 4) =
        4 * ((q : ℝ) - p) -
          (ccmActualHeadMatchedPolarCentroid p + criticalMellinAtomWeight p / 2) *
            (criticalMellinAtomWeight p + criticalMellinAtomWeight q) := by ring
      _ = _ := by simpa only using hid
  have hscaled : 2 ≤ |4 * (g - R)| := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
    nlinarith only [hsep]
  rw [hfactor, abs_mul] at hscaled
  exact hscaled

private theorem oddPrimeGap_displacement_lever_upper
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (hpexp : Real.exp 2 ≤ (p : ℝ)) :
    0 ≤ 2 * ccmActualHeadMatchedPolarCentroid p +
      criticalMellinAtomWeight p + criticalMellinAtomWeight q ∧
    2 * ccmActualHeadMatchedPolarCentroid p +
        criticalMellinAtomWeight p + criticalMellinAtomWeight q ≤
      7 * Real.sqrt p := by
  let a : ℝ := criticalMellinAtomWeight p
  let b : ℝ := criticalMellinAtomWeight q
  let c : ℝ := ccmActualHeadMatchedPolarCentroid p
  let s : ℝ := Real.sqrt (p : ℝ)
  let l : ℝ := Real.log (p : ℝ)
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hqR : (p : ℝ) ≤ q := by exact_mod_cast hpq.le
  have hs : 0 < s := Real.sqrt_pos.mpr hpR
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
  have ha0 : 0 ≤ a := by
    rw [ha]
    positivity
  have hb0 : 0 ≤ b := by
    rw [hb]
    have hlog : 0 ≤ Real.log (q : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hq.one_lt.le)
    positivity
  have hssq : s ^ (2 : ℕ) = (p : ℝ) := Real.sq_sqrt hpR.le
  have hlogle : l ≤ (p : ℝ) := Real.log_le_self hpR.le
  have ha_le : a ≤ s := by
    rw [ha]
    apply (div_le_iff₀ hs).2
    nlinarith only [hlogle, hssq]
  have hasq : a ^ (2 : ℕ) ≤ s ^ (2 : ℕ) := by
    nlinarith only [mul_nonneg ha0 (sub_nonneg.mpr ha_le)]
  have hcsq := ccmActualHeadMatchedPolarCentroid_sq p hp.pos
  change c ^ (2 : ℕ) = 4 * (p : ℝ) + a ^ (2 : ℕ) / 4 at hcsq
  have hc0 : 0 < c := ccmActualHeadMatchedPolarCentroid_pos p
  have hc_le : c ≤ (5 / 2 : ℝ) * s := by
    rw [← hssq] at hcsq
    nlinarith only [hcsq, hasq, hc0, hs]
  constructor
  · change 0 ≤ 2 * c + a + b
    positivity
  · change 2 * c + a + b ≤ 7 * s
    linarith only [hc_le, ha_le, hb_le]

/-- Quantitative, source-faithful displacement separation on an odd-log
adjacent active prime pair. The scale is inverse square root of the first
prime, so a base-vertex edge retains a nonvanishing energy contribution. -/
theorem ccmActualHeadMatchedQuantile_oddActivePrimePair_displacement_lower
    {p q t : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (hp2 : p ≠ 2) (hpexp : Real.exp 2 ≤ (p : ℝ))
    (hloglo : ((2 * t + 1 : ℕ) : ℝ) ≤ Real.log p)
    (hloghi : Real.log p ≤ ((2 * t + 1 : ℕ) : ℝ) + 1 / 4)
    (herror : Real.log p ^ (2 : ℕ) / (2 * p) < 1 / 4)
    (hfree : ∀ k : ℕ, p < k → k < q → criticalMellinAtomWeight k = 0) :
    1 / (4 * Real.sqrt p) ≤
      |ccmActualHeadMatchedQuantilePolarDisplacement q -
        ccmActualHeadMatchedQuantilePolarDisplacement p| := by
  let d := ccmActualHeadMatchedQuantilePolarDisplacement q -
    ccmActualHeadMatchedQuantilePolarDisplacement p
  let L := 2 * ccmActualHeadMatchedPolarCentroid p +
    criticalMellinAtomWeight p + criticalMellinAtomWeight q
  let s : ℝ := Real.sqrt p
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hs : 0 < s := Real.sqrt_pos.mpr hpR
  have hssq : s ^ (2 : ℕ) = (p : ℝ) := Real.sq_sqrt hpR.le
  have hpge : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hs1 : 1 ≤ s := by nlinarith only [hssq, hpge, hs]
  have hprod : 2 ≤ |d| * |d - L| :=
    oddPrimeGap_displacement_product_lower hp hq hpq hp2 hpexp
      hloglo hloghi herror hfree
  obtain ⟨hL0, hLle⟩ := oddPrimeGap_displacement_lever_upper hp hq hpq hpexp
  have hrec : 1 / s ≤ s := by
    apply (div_le_iff₀ hs).2
    nlinarith only [hs1]
  by_cases hlarge : 1 / s ≤ |d|
  · change 1 / (4 * s) ≤ |d|
    have hsmall : 1 / (4 * s) ≤ 1 / s := by
      have hrec0 : 0 ≤ 1 / s := by positivity
      have heq : 1 / (4 * s) = (1 / s) / 4 := by ring
      rw [heq]
      linarith only [hrec0]
    exact hsmall.trans hlarge
  · have hdsmall : |d| < 1 / s := lt_of_not_ge hlarge
    have htri : |d - L| ≤ |d| + |L| := abs_sub d L
    have hlever : |d - L| ≤ 8 * s := by
      rw [abs_of_nonneg hL0] at htri
      linarith only [htri, hdsmall, hLle, hrec]
    have hmul : 2 ≤ |d| * (8 * s) :=
      hprod.trans (mul_le_mul_of_nonneg_left hlever (abs_nonneg d))
    change 1 / (4 * s) ≤ |d|
    apply (div_le_iff₀ (by positivity : 0 < 4 * s)).2
    nlinarith only [hmul]

end RHTower
