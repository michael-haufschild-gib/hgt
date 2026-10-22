import GaloisForLFunctions.RHTower.CCM.CCMActualHeadMatchedQuantileActiveGapResonance

/-!
# Quantitative matched-quantile prime-gap defect

The exact active-gap law retains the signed displacement increment instead of
assuming resonance. On odd-log prime windows, parity separates the actual
arithmetic resonance center from every prime gap by at least one half. This
upgrades the prior qualitative nonresonance result. It does not control the
signed completed prime--polar--Gamma source or establish RH.
-/

namespace RHTower

/-- Exact off-resonance refinement of the matched-prime gap law. The right side
retains the signed quantile displacement increment instead of setting it to zero. -/
theorem ccmActualHeadMatchedQuantile_activeGap_defect_identity
    {m n : ℕ} (hm : 0 < m) (hmn : m < n)
    (hfree : ∀ k : ℕ, m < k → k < n → criticalMellinAtomWeight k = 0) :
    let d := ccmActualHeadMatchedQuantilePolarDisplacement n -
      ccmActualHeadMatchedQuantilePolarDisplacement m
    4 * ((n : ℝ) - m) -
      (ccmActualHeadMatchedPolarCentroid m + criticalMellinAtomWeight m / 2) *
        (criticalMellinAtomWeight m + criticalMellinAtomWeight n) =
      d * (d - (2 * ccmActualHeadMatchedPolarCentroid m +
        criticalMellinAtomWeight m + criticalMellinAtomWeight n)) := by
  let cm := ccmActualHeadMatchedPolarCentroid m
  let cn := ccmActualHeadMatchedPolarCentroid n
  let a := criticalMellinAtomWeight m
  let b := criticalMellinAtomWeight n
  let d := ccmActualHeadMatchedQuantilePolarDisplacement n -
    ccmActualHeadMatchedQuantilePolarDisplacement m
  have hq := ccmActualHeadQuantilePolarCentroid_gap_of_no_intermediate_atom hmn hfree
  rw [ccmActualHeadQuantilePolarCentroid_eq_matched_add_displacement,
    ccmActualHeadQuantilePolarCentroid_eq_matched_add_displacement] at hq
  have hsm := ccmActualHeadMatchedPolarCentroid_sq m hm
  have hsn := ccmActualHeadMatchedPolarCentroid_sq n (hm.trans hmn)
  have hq' : cn = cm + (a + b) / 2 - d := by
    dsimp only [cn, cm, a, b, d]
    linarith only [hq]
  change cm ^ (2 : ℕ) = 4 * (m : ℝ) + a ^ (2 : ℕ) / 4 at hsm
  change cn ^ (2 : ℕ) = 4 * (n : ℝ) + b ^ (2 : ℕ) / 4 at hsn
  rw [hq'] at hsn
  dsimp only
  nlinarith only [hsm, hsn]

/-- The arithmetic center of an active prime-pair gap lies below the first
prime's logarithm up to its explicit quadratic correction, independently of
whether the two quantile displacements coincide. -/
theorem ccmActualHeadMatchedQuantile_primeGap_center_upper
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (hpexp : Real.exp 2 ≤ (p : ℝ)) :
    (ccmActualHeadMatchedPolarCentroid p + criticalMellinAtomWeight p / 2) *
        (criticalMellinAtomWeight p + criticalMellinAtomWeight q) / 4 ≤
      Real.log p + Real.log p ^ (2 : ℕ) / (2 * p) := by
  let a : ℝ := criticalMellinAtomWeight p
  let b : ℝ := criticalMellinAtomWeight q
  let c : ℝ := ccmActualHeadMatchedPolarCentroid p
  let s : ℝ := Real.sqrt (p : ℝ)
  let l : ℝ := Real.log (p : ℝ)
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hqR : (p : ℝ) ≤ q := by exact_mod_cast hpq.le
  have hs : 0 < s := Real.sqrt_pos.mpr hpR
  have hl : 0 ≤ l := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
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
  have hcore : (c + a / 2) * (a + b) ≤ (2 * s + a) * (2 * a) := by
    calc
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
  have hscaled : (c + a / 2) * (a + b) ≤
      4 * Real.log p + 2 * Real.log p ^ (2 : ℕ) / (p : ℝ) := by
    simpa only [ha] using hcore
  calc
    (ccmActualHeadMatchedPolarCentroid p + criticalMellinAtomWeight p / 2) *
        (criticalMellinAtomWeight p + criticalMellinAtomWeight q) / 4 =
      (c + a / 2) * (a + b) / 4 := rfl
    _ ≤ (4 * Real.log p + 2 * Real.log p ^ (2 : ℕ) / (p : ℝ)) / 4 := by
      gcongr
    _ = _ := by ring

private theorem sqrt_inverse_tangent_lower_for_defect
    {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    (1 - (y - x) / (2 * x)) * Real.sqrt y ≤ Real.sqrt x := by
  let s := Real.sqrt x
  let t := Real.sqrt y
  have hs : 0 < s := Real.sqrt_pos.mpr hx
  have ht : 0 < t := Real.sqrt_pos.mpr (hx.trans_le hxy)
  have hssq : s ^ (2 : ℕ) = x := Real.sq_sqrt hx.le
  have htsq : t ^ (2 : ℕ) = y := Real.sq_sqrt (hx.trans_le hxy).le
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

/-- The arithmetic center of a prime-pair gap lies above the first prime's
logarithm up to the explicit inverse-square-root tangent error, without a
resonance assumption. -/
theorem ccmActualHeadMatchedQuantile_primeGap_center_lower
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    Real.log p - Real.log p * ((q : ℝ) - p) / (4 * p) ≤
      (ccmActualHeadMatchedPolarCentroid p + criticalMellinAtomWeight p / 2) *
        (criticalMellinAtomWeight p + criticalMellinAtomWeight q) / 4 := by
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
  have hlogle : l ≤ Real.log (q : ℝ) := Real.log_le_log hpR hpqR
  have htan := sqrt_inverse_tangent_lower_for_defect hpR hpqR
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
  have hcore : 2 * s * (l / s * (2 - g / (2 * (p : ℝ)))) ≤
      (c + a / 2) * (a + b) := by
    calc
      _ ≤ 2 * s * (a + b) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [ha]
        linarith only [hb_lower]
      _ ≤ (c + a / 2) * (a + b) := by
        exact mul_le_mul_of_nonneg_right
          (by linarith only [hc_lower, ha0]) (add_nonneg ha0 hb0)
  have hident : 2 * s * (l / s * (2 - g / (2 * (p : ℝ)))) =
      4 * l - l * g / (p : ℝ) := by
    field_simp [hs.ne', hpR.ne']
    ring
  rw [hident] at hcore
  dsimp only [l, g] at *
  have hscaled : 4 * Real.log p - Real.log p * ((q : ℝ) - p) / (p : ℝ) ≤
      (c + a / 2) * (a + b) := hcore
  change Real.log p - Real.log p * ((q : ℝ) - p) / (4 * p) ≤
    (c + a / 2) * (a + b) / 4
  calc
    Real.log p - Real.log p * ((q : ℝ) - p) / (4 * p) =
        (4 * Real.log p - Real.log p * ((q : ℝ) - p) / p) / 4 := by ring
    _ ≤ (c + a / 2) * (a + b) / 4 := by gcongr

/-- Quantitative odd-log nonresonance. An adjacent active odd-prime pair has
a half-unit arithmetic gap from the exact matched-quantile resonance center.
Unlike the prior inequality `displacement q ≠ displacement p`, this retains
a fixed defect for subsequent coercive estimates. -/
theorem ccmActualHeadMatchedQuantile_oddPrimeGap_center_separated
    {p q t : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (hp2 : p ≠ 2)
    (hpexp : Real.exp 2 ≤ (p : ℝ))
    (hloglo : ((2 * t + 1 : ℕ) : ℝ) ≤ Real.log p)
    (hloghi : Real.log p ≤ ((2 * t + 1 : ℕ) : ℝ) + 1 / 4)
    (herror : Real.log p ^ (2 : ℕ) / (2 * p) < 1 / 4) :
    1 / 2 ≤ |((q : ℝ) - p) -
      (ccmActualHeadMatchedPolarCentroid p + criticalMellinAtomWeight p / 2) *
        (criticalMellinAtomWeight p + criticalMellinAtomWeight q) / 4| := by
  let l : ℝ := Real.log p
  let g : ℝ := (q : ℝ) - p
  let R : ℝ := (ccmActualHeadMatchedPolarCentroid p + criticalMellinAtomWeight p / 2) *
    (criticalMellinAtomWeight p + criticalMellinAtomWeight q) / 4
  let e : ℝ := l ^ (2 : ℕ) / (2 * p)
  have hu : R ≤ l + e := ccmActualHeadMatchedQuantile_primeGap_center_upper hp hq hpq hpexp
  have hd : l - l * g / (4 * p) ≤ R :=
    ccmActualHeadMatchedQuantile_primeGap_center_lower hp hq hpq
  have he : e < 1 / 4 := herror
  by_contra hsep
  have hclose : |g - R| < 1 / 2 := lt_of_not_ge hsep
  have hclose' := abs_lt.mp hclose
  have hgUpper : g < ((2 * t + 2 : ℕ) : ℝ) := by
    have hcast : ((2 * t + 2 : ℕ) : ℝ) = ((2 * t + 1 : ℕ) : ℝ) + 1 := by
      push_cast
      ring
    rw [hcast]
    linarith only [hclose'.2, hu, he, hloghi]
  have hgapHigh : q - p < 2 * t + 2 := by
    have hcast : ((q - p : ℕ) : ℝ) < ((2 * t + 2 : ℕ) : ℝ) := by
      rw [Nat.cast_sub hpq.le]
      exact hgUpper
    exact_mod_cast hcast
  have hgapLow : 2 * t < q - p := by
    by_contra hnot
    have hnat : q - p ≤ 2 * t := by omega
    have hgLe : g ≤ ((2 * t : ℕ) : ℝ) := by
      have hcast : ((q - p : ℕ) : ℝ) ≤ ((2 * t : ℕ) : ℝ) := by
        exact_mod_cast hnat
      rw [Nat.cast_sub hpq.le] at hcast
      exact hcast
    have hgle : g ≤ l := by
      have hodd : ((2 * t : ℕ) : ℝ) + 1 = ((2 * t + 1 : ℕ) : ℝ) := by
        push_cast
        ring
      linarith only [hgLe, hloglo, hodd]
    have hl0 : 0 ≤ l := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
    have hp0 : (0 : ℝ) < 4 * p := by
      have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
      positivity
    have hprod : l * g ≤ l ^ (2 : ℕ) := by
      nlinarith only [mul_nonneg hl0 (sub_nonneg.mpr hgle)]
    have hfrac : l * g / (4 * p) ≤ l ^ (2 : ℕ) / (4 * p) :=
      div_le_div_of_nonneg_right hprod hp0.le
    have heighth : l ^ (2 : ℕ) / (4 * p) < 1 / 8 := by
      have heq : l ^ (2 : ℕ) / (4 * p) = e / 2 := by ring
      rw [heq]
      linarith only [he]
    have hgap : 1 ≤ l - g := by
      have hodd : ((2 * t : ℕ) : ℝ) + 1 = ((2 * t + 1 : ℕ) : ℝ) := by
        push_cast
        ring
      linarith only [hgLe, hloglo, hodd]
    linarith only [hd, hclose'.1, hfrac, heighth, hgap]
  have hpodd := hp.odd_of_ne_two hp2
  have hq2 : q ≠ 2 := by
    have hpge := hp.two_le
    omega
  have hqodd := hq.odd_of_ne_two hq2
  obtain ⟨a, ha⟩ := hpodd
  obtain ⟨b, hb⟩ := hqodd
  omega

/-- The arithmetic excess of an actual atom-free gap is exactly the negative
matched--quantile displacement increment times a strictly positive physical
lever.  This resolves the orientation hidden in the quadratic defect law. -/
theorem ccmActualHeadMatchedQuantile_activeGap_signed_factor
    {m n : ℕ} (hm : 0 < m) (hmn : m < n)
    (hfree : ∀ k : ℕ, m < k → k < n → criticalMellinAtomWeight k = 0) :
    4 * ((n : ℝ) - m) -
      (ccmActualHeadMatchedPolarCentroid m + criticalMellinAtomWeight m / 2) *
        (criticalMellinAtomWeight m + criticalMellinAtomWeight n) =
      -(ccmActualHeadMatchedPolarCentroid m +
        ccmActualHeadMatchedPolarCentroid n +
          (criticalMellinAtomWeight m + criticalMellinAtomWeight n) / 2) *
        (ccmActualHeadMatchedQuantilePolarDisplacement n -
          ccmActualHeadMatchedQuantilePolarDisplacement m) := by
  let a := criticalMellinAtomWeight m
  let b := criticalMellinAtomWeight n
  let c := ccmActualHeadMatchedPolarCentroid m
  let e := ccmActualHeadMatchedPolarCentroid n
  let d := ccmActualHeadMatchedQuantilePolarDisplacement n -
    ccmActualHeadMatchedQuantilePolarDisplacement m
  have hq := ccmActualHeadQuantilePolarCentroid_gap_of_no_intermediate_atom hmn hfree
  rw [ccmActualHeadQuantilePolarCentroid_eq_matched_add_displacement,
    ccmActualHeadQuantilePolarCentroid_eq_matched_add_displacement] at hq
  have hd : d = (a + b) / 2 - (e - c) := by
    dsimp only [d, a, b, c, e]
    linarith only [hq]
  have hid := ccmActualHeadMatchedQuantile_activeGap_defect_identity hm hmn hfree
  change 4 * ((n : ℝ) - m) - (c + a / 2) * (a + b) =
    -(c + e + (a + b) / 2) * d
  calc
    _ = d * (d - (2 * c + a + b)) := hid
    _ = -(c + e + (a + b) / 2) * d := by rw [hd]; ring

/-- Gap excess and matched--quantile displacement have opposite strict signs
on every literal atom-free active gap. -/
theorem ccmActualHeadMatchedQuantile_activeGap_excess_pos_iff_displacement_neg
    {m n : ℕ} (hm : 0 < m) (hmn : m < n)
    (hfree : ∀ k : ℕ, m < k → k < n → criticalMellinAtomWeight k = 0) :
    0 < 4 * ((n : ℝ) - m) -
      (ccmActualHeadMatchedPolarCentroid m + criticalMellinAtomWeight m / 2) *
        (criticalMellinAtomWeight m + criticalMellinAtomWeight n) ↔
      ccmActualHeadMatchedQuantilePolarDisplacement n -
        ccmActualHeadMatchedQuantilePolarDisplacement m < 0 := by
  rw [ccmActualHeadMatchedQuantile_activeGap_signed_factor hm hmn hfree]
  have hc : 0 < ccmActualHeadMatchedPolarCentroid m +
      ccmActualHeadMatchedPolarCentroid n +
        (criticalMellinAtomWeight m + criticalMellinAtomWeight n) / 2 := by
    have hcm := ccmActualHeadMatchedPolarCentroid_pos m
    have hcn := ccmActualHeadMatchedPolarCentroid_pos n
    have ham := criticalMellinAtomWeight_nonneg_cCMActualHeadWallGramSignedProducer m
    have han := criticalMellinAtomWeight_nonneg_cCMActualHeadWallGramSignedProducer n
    positivity
  constructor <;> intro h <;> nlinarith only [h, hc]

/-- The reverse orientation is equally exact. -/
theorem ccmActualHeadMatchedQuantile_activeGap_excess_neg_iff_displacement_pos
    {m n : ℕ} (hm : 0 < m) (hmn : m < n)
    (hfree : ∀ k : ℕ, m < k → k < n → criticalMellinAtomWeight k = 0) :
    4 * ((n : ℝ) - m) -
      (ccmActualHeadMatchedPolarCentroid m + criticalMellinAtomWeight m / 2) *
        (criticalMellinAtomWeight m + criticalMellinAtomWeight n) < 0 ↔
      0 < ccmActualHeadMatchedQuantilePolarDisplacement n -
        ccmActualHeadMatchedQuantilePolarDisplacement m := by
  rw [ccmActualHeadMatchedQuantile_activeGap_signed_factor hm hmn hfree]
  have hc : 0 < ccmActualHeadMatchedPolarCentroid m +
      ccmActualHeadMatchedPolarCentroid n +
        (criticalMellinAtomWeight m + criticalMellinAtomWeight n) / 2 := by
    have hcm := ccmActualHeadMatchedPolarCentroid_pos m
    have hcn := ccmActualHeadMatchedPolarCentroid_pos n
    have ham := criticalMellinAtomWeight_nonneg_cCMActualHeadWallGramSignedProducer m
    have han := criticalMellinAtomWeight_nonneg_cCMActualHeadWallGramSignedProducer n
    positivity
  constructor <;> intro h <;> nlinarith only [h, hc]

/-- A long atom-free prime gap in an odd-log window forces a negative
matched--quantile displacement increment. -/
theorem ccmActualHeadMatchedQuantile_oddLongPrimeGap_displacement_neg
    {p q t : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (hpexp : Real.exp 2 ≤ (p : ℝ))
    (hloghi : Real.log p ≤ ((2 * t + 1 : ℕ) : ℝ) + 1 / 4)
    (herror : Real.log p ^ (2 : ℕ) / (2 * p) < 1 / 4)
    (hlong : 2 * t + 2 ≤ q - p)
    (hfree : ∀ k : ℕ, p < k → k < q → criticalMellinAtomWeight k = 0) :
    ccmActualHeadMatchedQuantilePolarDisplacement q -
      ccmActualHeadMatchedQuantilePolarDisplacement p < 0 := by
  let R := (ccmActualHeadMatchedPolarCentroid p + criticalMellinAtomWeight p / 2) *
    (criticalMellinAtomWeight p + criticalMellinAtomWeight q) / 4
  have hR : R ≤ Real.log p + Real.log p ^ (2 : ℕ) / (2 * p) :=
    ccmActualHeadMatchedQuantile_primeGap_center_upper hp hq hpq hpexp
  have hg : ((2 * t + 2 : ℕ) : ℝ) ≤ (q : ℝ) - p := by
    have hqpp : p ≤ q := hpq.le
    have h := (show ((2 * t + 2 : ℕ) : ℝ) ≤ ((q - p : ℕ) : ℝ) by exact_mod_cast hlong)
    rw [Nat.cast_sub hqpp] at h
    exact h
  have hRg : R < (q : ℝ) - p := by
    have hcast : ((2 * t + 2 : ℕ) : ℝ) = ((2 * t + 1 : ℕ) : ℝ) + 1 := by
      push_cast
      ring
    linarith only [hR, hloghi, herror, hg, hcast]
  have hdef : 0 < 4 * ((q : ℝ) - p) -
      (ccmActualHeadMatchedPolarCentroid p + criticalMellinAtomWeight p / 2) *
        (criticalMellinAtomWeight p + criticalMellinAtomWeight q) := by
    dsimp only [R] at hRg
    linarith only [hRg]
  exact (ccmActualHeadMatchedQuantile_activeGap_excess_pos_iff_displacement_neg
    hp.pos hpq hfree).mp hdef

/-- A short atom-free prime gap in the same odd-log window forces the
opposite signed matched--quantile displacement increment. -/
theorem ccmActualHeadMatchedQuantile_oddShortPrimeGap_displacement_pos
    {p q t : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (hloglo : ((2 * t + 1 : ℕ) : ℝ) ≤ Real.log p)
    (herror : Real.log p ^ (2 : ℕ) / (2 * p) < 1 / 4)
    (hshort : q - p ≤ 2 * t)
    (hfree : ∀ k : ℕ, p < k → k < q → criticalMellinAtomWeight k = 0) :
    0 < ccmActualHeadMatchedQuantilePolarDisplacement q -
      ccmActualHeadMatchedQuantilePolarDisplacement p := by
  let R := (ccmActualHeadMatchedPolarCentroid p + criticalMellinAtomWeight p / 2) *
    (criticalMellinAtomWeight p + criticalMellinAtomWeight q) / 4
  let g : ℝ := (q : ℝ) - p
  have hR : Real.log p - Real.log p * g / (4 * p) ≤ R :=
    ccmActualHeadMatchedQuantile_primeGap_center_lower hp hq hpq
  have hg : g ≤ ((2 * t : ℕ) : ℝ) := by
    dsimp only [g]
    have h := (show ((q - p : ℕ) : ℝ) ≤ ((2 * t : ℕ) : ℝ) by exact_mod_cast hshort)
    rw [Nat.cast_sub hpq.le] at h
    exact h
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hl0 : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  have hgle : g ≤ Real.log p := by
    have hcast : ((2 * t + 1 : ℕ) : ℝ) = ((2 * t : ℕ) : ℝ) + 1 := by
      push_cast
      ring
    linarith only [hg, hloglo, hcast]
  have hprod : Real.log p * g ≤ Real.log p ^ (2 : ℕ) := by
    nlinarith only [mul_nonneg hl0 (sub_nonneg.mpr hgle)]
  have hfrac : Real.log p * g / (4 * p) < 1 / 8 := by
    have hden : 0 < 4 * (p : ℝ) := by positivity
    have hle := div_le_div_of_nonneg_right hprod hden.le
    have heq : Real.log p ^ (2 : ℕ) / (4 * p) =
        (Real.log p ^ (2 : ℕ) / (2 * p)) / 2 := by ring
    rw [heq] at hle
    linarith only [hle, herror]
  have hRg : g < R := by
    have hcast : ((2 * t + 1 : ℕ) : ℝ) = ((2 * t : ℕ) : ℝ) + 1 := by
      push_cast
      ring
    linarith only [hR, hg, hloglo, hfrac, hcast]
  have hdef : 4 * ((q : ℝ) - p) -
      (ccmActualHeadMatchedPolarCentroid p + criticalMellinAtomWeight p / 2) *
        (criticalMellinAtomWeight p + criticalMellinAtomWeight q) < 0 := by
    dsimp only [g, R] at hRg
    linarith only [hRg]
  exact (ccmActualHeadMatchedQuantile_activeGap_excess_neg_iff_displacement_pos
    hp.pos hpq hfree).mp hdef

end RHTower
