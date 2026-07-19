import GaloisForLFunctions.RHTower.XiMobiusContinuousApertureDyadicProjection
import GaloisForLFunctions.RHTower.XiMobiusContinuousApertureTangentRationalHurwitzNoGo

/-!
# Weighted cubic Möbius innovation law and reflected strip no-go

The primewise dyadic innovation has a positive cubic germ.  This module proves one general
all-prime dominated-convergence law after multiplication by any nonnegative prime value weight
whose cubic source slope is summable.  It simultaneously yields the previously missing unweighted
all-prime cubic source limit and the normalized rational-Hurwitz reflected cubic limit.

The reflected coefficient is the third logarithmic moment of the unit-damped prime seam, up to a
uniformly comparable positive source factor.  It therefore sees exactly the open critical strip,
and both its summability and its cubic germ limit hold on every Xi fibre unconditionally.
-/

namespace RHTower

noncomputable section

open Filter

/-- Logarithmic prime-square slope which dominates the cubic dyadic source innovation. -/
def xiMobiusPrimeContinuousApertureCubicSlopeTerm (p : Nat.Primes) : ℝ :=
  (xiTransversePrimeApertureDiskNode 1 p /
      (1 + xiTransversePrimeApertureDiskNode 1 p)) ^ 2 *
    Real.log (p : ℝ) ^ 3

theorem xiMobiusPrimeContinuousApertureCubicSlopeTerm_pos
    (p : Nat.Primes) :
    0 < xiMobiusPrimeContinuousApertureCubicSlopeTerm p := by
  have hq := xiTransversePrimeApertureDiskNode_pos 1 p
  have hL : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast p.prop.one_lt)
  exact mul_pos (sq_pos_of_pos (div_pos hq (by linarith))) (pow_pos hL 3)

/-- The cubic source slope is summable over all primes. -/
theorem summable_xiMobiusPrimeContinuousApertureCubicSlopeTerm :
    Summable xiMobiusPrimeContinuousApertureCubicSlopeTerm := by
  have hmajor : Summable (fun p : Nat.Primes =>
      |Real.log (p : ℝ)| ^ 3 * (p : ℝ) ^ (-(2 : ℝ))) :=
    (summable_abs_log_natCast_pow_mul_rpow_neg 3 2 (by norm_num)).comp_injective
      Subtype.coe_injective
  refine Summable.of_nonneg_of_le
    (fun p => (xiMobiusPrimeContinuousApertureCubicSlopeTerm_pos p).le) ?_ hmajor
  intro p
  let q := xiTransversePrimeApertureDiskNode 1 p
  let L := Real.log (p : ℝ)
  let P : ℝ := p
  have hp0 : 0 < P := by
    dsimp only [P]
    exact_mod_cast p.prop.pos
  have hL : 0 < L := by
    dsimp only [L]
    exact Real.log_pos (by exact_mod_cast p.prop.one_lt)
  have hq : q = P⁻¹ := xiTransversePrimeApertureDiskNode_one_eq_inv p
  have hq0 : 0 < q := xiTransversePrimeApertureDiskNode_pos 1 p
  have hdamp0 : 0 ≤ q / (1 + q) := div_nonneg hq0.le (by linarith)
  have hdamp : q / (1 + q) ≤ q := by
    rw [div_le_iff₀ (by linarith : 0 < 1 + q)]
    nlinarith [sq_nonneg q]
  have hsq : (q / (1 + q)) ^ 2 ≤ q ^ 2 := by nlinarith
  have hqpow : q ^ 2 = P ^ (-(2 : ℝ)) := by
    rw [show -(2 : ℝ) = (-1 : ℝ) + (-1 : ℝ) by ring,
      Real.rpow_add hp0, Real.rpow_neg_one, hq]
    ring
  change (q / (1 + q)) ^ 2 * L ^ 3 ≤ |L| ^ 3 * P ^ (-(2 : ℝ))
  rw [abs_of_pos hL, ← hqpow]
  simpa [mul_comm] using
    (mul_le_mul_of_nonneg_right hsq (pow_nonneg hL.le 3))

/-- Uniform cubic domination of every positive-mesh primewise dyadic innovation. -/
theorem norm_xiMobiusPrimeContinuousApertureDyadicInnovation_div_cube_le
    {h a b : ℝ} (hh : 0 < h) (ha : 0 < a) (hb : 0 < b)
    (p : Nat.Primes) :
    ‖xiMobiusPrimeContinuousApertureDyadicInnovation h a b p / h ^ 3‖ ≤
      (a * b ^ 2 / 8) * xiMobiusPrimeContinuousApertureCubicSlopeTerm p := by
  let q := xiTransversePrimeApertureDiskNode 1 p
  let d := q / (1 + q)
  let r := xiMobiusContinuousApertureDiskNode ((h / 2) * a) p
  let s := xiMobiusContinuousApertureDiskNode ((h / 2) * b) p
  let L := Real.log (p : ℝ)
  have hL : 0 < L := by
    dsimp only [L]
    exact Real.log_pos (by exact_mod_cast p.prop.one_lt)
  have hha : 0 < (h / 2) * a := mul_pos (half_pos hh) ha
  have hhb : 0 < (h / 2) * b := mul_pos (half_pos hh) hb
  have hr0 : 0 < r := xiMobiusContinuousApertureDiskNode_pos _ p
  have hs0 : 0 < s := xiMobiusContinuousApertureDiskNode_pos _ p
  have hr1 : r < 1 := xiMobiusContinuousApertureDiskNode_lt_one hha p
  have hs1 : s < 1 := xiMobiusContinuousApertureDiskNode_lt_one hhb p
  have hrs0 : 0 ≤ r * s := mul_nonneg hr0.le hs0.le
  have hrs1 : r * s < 1 :=
    mul_lt_one_of_nonneg_of_lt_one_left hr0.le hr1 hs1.le
  have hden : 0 < 1 - (r * s) ^ 2 := by
    have hsq : (r * s) ^ 2 < 1 :=
      pow_lt_one₀ hrs0 hrs1 (by norm_num)
    linarith
  have hrs_le_r : r * s ≤ r := mul_le_of_le_one_right hr0.le hs1.le
  have hrs_sq_le : (r * s) ^ 2 ≤ r * s := by
    nlinarith [mul_nonneg hrs0 (by linarith : 0 ≤ 1 - r * s)]
  have hdenLower : 1 - r ≤ 1 - (r * s) ^ 2 := by linarith
  have hfrac :
      (1 - r) ^ 2 * (1 - s) ^ 2 / (1 - (r * s) ^ 2) ≤
        (1 - r) * (1 - s) ^ 2 := by
    rw [div_le_iff₀ hden]
    have hnonneg : 0 ≤ (1 - r) * (1 - s) ^ 2 :=
      mul_nonneg (by linarith) (sq_nonneg _)
    calc
      (1 - r) ^ 2 * (1 - s) ^ 2 =
          ((1 - r) * (1 - s) ^ 2) * (1 - r) := by ring
      _ ≤ ((1 - r) * (1 - s) ^ 2) * (1 - (r * s) ^ 2) :=
        mul_le_mul_of_nonneg_left hdenLower hnonneg
  have hr_eq : r = Real.exp (-((h / 2) * a * L)) := by
    simp only [r, xiMobiusContinuousApertureDiskNode, L]
    congr 1
    ring
  have hs_eq : s = Real.exp (-((h / 2) * b * L)) := by
    simp only [s, xiMobiusContinuousApertureDiskNode, L]
    congr 1
    ring
  have hgapR : 1 - r ≤ (h / 2) * a * L := by
    rw [hr_eq]
    linarith [Real.one_sub_le_exp_neg ((h / 2) * a * L)]
  have hgapS : 1 - s ≤ (h / 2) * b * L := by
    rw [hs_eq]
    linarith [Real.one_sub_le_exp_neg ((h / 2) * b * L)]
  have hgapSq : (1 - s) ^ 2 ≤ ((h / 2) * b * L) ^ 2 :=
    pow_le_pow_left₀ (by linarith) hgapS 2
  have hgaps : (1 - r) * (1 - s) ^ 2 ≤
      h ^ 3 * (a * b ^ 2 / 8 * L ^ 3) := by
    calc
      (1 - r) * (1 - s) ^ 2 ≤
          ((h / 2) * a * L) * (((h / 2) * b * L) ^ 2) :=
        mul_le_mul hgapR hgapSq (sq_nonneg _) (by linarith)
      _ = h ^ 3 * (a * b ^ 2 / 8 * L ^ 3) := by ring
  have hinnovation : 0 ≤ xiMobiusPrimeContinuousApertureDyadicInnovation h a b p := by
    rw [xiMobiusPrimeContinuousApertureDyadicInnovation_eq_szego hh ha hb p]
    exact div_nonneg
      (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)) hden.le
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hinnovation (pow_nonneg hh.le 3))]
  rw [div_le_iff₀ (pow_pos hh 3)]
  rw [xiMobiusPrimeContinuousApertureDyadicInnovation_eq_szego hh ha hb p]
  change d ^ 2 * (1 - r) ^ 2 * (1 - s) ^ 2 / (1 - (r * s) ^ 2) ≤
    (a * b ^ 2 / 8 * (d ^ 2 * L ^ 3)) * h ^ 3
  calc
    d ^ 2 * (1 - r) ^ 2 * (1 - s) ^ 2 / (1 - (r * s) ^ 2) =
        d ^ 2 * ((1 - r) ^ 2 * (1 - s) ^ 2 / (1 - (r * s) ^ 2)) := by ring
    _ ≤ d ^ 2 * ((1 - r) * (1 - s) ^ 2) :=
      mul_le_mul_of_nonneg_left hfrac (sq_nonneg d)
    _ ≤ d ^ 2 * (h ^ 3 * (a * b ^ 2 / 8 * L ^ 3)) :=
      mul_le_mul_of_nonneg_left hgaps (sq_nonneg d)
    _ = _ := by ring

/-- Exact primewise cubic coefficient of the dyadic innovation. -/
def xiMobiusPrimeContinuousApertureCubicCoefficient
    (a b : ℝ) (p : Nat.Primes) : ℝ :=
  (xiTransversePrimeApertureDiskNode 1 p /
      (1 + xiTransversePrimeApertureDiskNode 1 p)) ^ 2 *
    (((a / 2) * Real.log (p : ℝ)) ^ 2 *
        ((b / 2) * Real.log (p : ℝ)) ^ 2 /
      ((a + b) * Real.log (p : ℝ)))

/-- The cubic coefficient is a scalar aperture dressing of the cubic prime slope. -/
theorem xiMobiusPrimeContinuousApertureCubicCoefficient_eq_slope
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (p : Nat.Primes) :
    xiMobiusPrimeContinuousApertureCubicCoefficient a b p =
      (a ^ 2 * b ^ 2 / (16 * (a + b))) *
        xiMobiusPrimeContinuousApertureCubicSlopeTerm p := by
  have hab : 0 < a + b := add_pos ha hb
  have hL : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast p.prop.one_lt)
  rw [xiMobiusPrimeContinuousApertureCubicCoefficient,
    xiMobiusPrimeContinuousApertureCubicSlopeTerm]
  field_simp [hab.ne', hL.ne']
  ring

/-- Dyadic innovation after insertion of an arbitrary prime value weight. -/
def xiMobiusContinuousApertureWeightedDyadicInnovation
    (h a b : ℝ) (w : Nat.Primes → ℝ) : ℝ :=
  ∑' p : Nat.Primes,
    xiMobiusPrimeContinuousApertureDyadicInnovation h a b p * w p

/-- Weighted all-prime cubic coefficient. -/
def xiMobiusContinuousApertureWeightedCubicLimit
    (a b : ℝ) (w : Nat.Primes → ℝ) : ℝ :=
  ∑' p : Nat.Primes,
    xiMobiusPrimeContinuousApertureCubicCoefficient a b p * w p

/-- **General weighted cubic source law.** Every nonnegative prime value weight with summable
cubic source slope passes through the all-prime dyadic innovation limit. -/
theorem tendsto_xiMobiusContinuousApertureWeightedDyadicInnovation_div_cube_of_summable
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {w : Nat.Primes → ℝ} (hw : ∀ p, 0 ≤ w p)
    (hsum : Summable (fun p : Nat.Primes =>
      xiMobiusPrimeContinuousApertureCubicSlopeTerm p * w p)) :
    Tendsto
      (fun h : ℝ =>
        xiMobiusContinuousApertureWeightedDyadicInnovation h a b w / h ^ 3)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (xiMobiusContinuousApertureWeightedCubicLimit a b w)) := by
  have hpoint (p : Nat.Primes) : Tendsto
      (fun h : ℝ =>
        (xiMobiusPrimeContinuousApertureDyadicInnovation h a b p * w p) / h ^ 3)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (xiMobiusPrimeContinuousApertureCubicCoefficient a b p * w p)) := by
    have h :=
      (tendsto_xiMobiusPrimeContinuousApertureDyadicInnovation_div_cube ha hb p).const_mul
        (w p)
    simpa [xiMobiusPrimeContinuousApertureCubicCoefficient,
      div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using h
  have hmajor : Summable (fun p : Nat.Primes =>
      (a * b ^ 2 / 8) *
        (xiMobiusPrimeContinuousApertureCubicSlopeTerm p * w p)) :=
    hsum.mul_left (a * b ^ 2 / 8)
  have hbound : ∀ᶠ h : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ∀ p : Nat.Primes,
        ‖(xiMobiusPrimeContinuousApertureDyadicInnovation h a b p * w p) /
            h ^ 3‖ ≤
          (a * b ^ 2 / 8) *
            (xiMobiusPrimeContinuousApertureCubicSlopeTerm p * w p) := by
    filter_upwards [self_mem_nhdsWithin] with h hh p
    rw [show (xiMobiusPrimeContinuousApertureDyadicInnovation h a b p * w p) /
        h ^ 3 =
      (xiMobiusPrimeContinuousApertureDyadicInnovation h a b p / h ^ 3) *
        w p by ring,
      norm_mul]
    simp only [Real.norm_eq_abs, abs_of_nonneg (hw p)]
    have hmul := mul_le_mul_of_nonneg_right
      (norm_xiMobiusPrimeContinuousApertureDyadicInnovation_div_cube_le hh ha hb p)
      (hw p)
    simpa only [Real.norm_eq_abs, mul_assoc] using hmul
  have hlimit := tendsto_tsum_of_dominated_convergence hmajor hpoint hbound
  simpa [xiMobiusContinuousApertureWeightedDyadicInnovation,
    xiMobiusContinuousApertureWeightedCubicLimit, tsum_div_const] using hlimit

/-- Completed all-prime cubic source kernel. -/
def xiMobiusContinuousApertureCubicKernel (a b : ℝ) : ℝ :=
  ∑' p : Nat.Primes, xiMobiusPrimeContinuousApertureCubicCoefficient a b p

/-- The previously primewise cubic law commutes with the all-prime source completion. -/
theorem tendsto_xiMobiusContinuousApertureDyadicInnovation_div_cube
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto
      (fun h : ℝ => xiMobiusContinuousApertureDyadicInnovation h a b / h ^ 3)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (xiMobiusContinuousApertureCubicKernel a b)) := by
  have h :=
    tendsto_xiMobiusContinuousApertureWeightedDyadicInnovation_div_cube_of_summable
      ha hb (w := fun _ => 1) (fun _ => by norm_num)
      (by simpa using summable_xiMobiusPrimeContinuousApertureCubicSlopeTerm)
  simpa [xiMobiusContinuousApertureWeightedDyadicInnovation,
    xiMobiusContinuousApertureWeightedCubicLimit,
    xiMobiusContinuousApertureCubicKernel,
    xiMobiusContinuousApertureDyadicInnovation] using h

/-- Residual local factor after extracting the third logarithmic moment of the unit-damped seam. -/
def xiMobiusContinuousApertureCubicReflectionFactor
    (a b : ℝ) (p : Nat.Primes) : ℝ :=
  let q := xiTransversePrimeApertureDiskNode 1 p
  (a ^ 2 * b ^ 2 / (64 * (a + b))) * (1 / (1 + q) ^ 2)

/-- Cubic source coefficient applied to the normalized rational-Hurwitz value reflection. -/
def xiMobiusPrimeContinuousApertureCubicNormalizedReflectionEnergy
    (a b : ℝ) (rho : ℂ) (p : Nat.Primes) : ℝ :=
  xiMobiusPrimeContinuousApertureCubicCoefficient a b p *
    normalizedScaleSeamEnergy (p : ℕ) rho

/-- On the open strip, this is literally the cubic source coefficient applied to the finite
rational-Hurwitz reflection energy. -/
theorem xiMobiusPrimeContinuousApertureCubicNormalizedReflectionEnergy_eq_rationalHurwitz
    {a b : ℝ} {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1)
    (p : Nat.Primes) :
    xiMobiusPrimeContinuousApertureCubicNormalizedReflectionEnergy a b rho p =
      xiMobiusPrimeContinuousApertureCubicCoefficient a b p *
        normalizedRationalHurwitzReflectionEnergy (p : ℕ) rho := by
  rw [xiMobiusPrimeContinuousApertureCubicNormalizedReflectionEnergy,
    normalizedRationalHurwitzReflectionEnergy_eq_scale hstrip]

/-- Exact cubic source/value splice.  Dyadic curvature inserts precisely the third logarithmic
moment and retains unit power damping. -/
theorem xiMobiusPrimeContinuousApertureCubicNormalizedReflectionEnergy_eq_factor
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (rho : ℂ) (p : Nat.Primes) :
    xiMobiusPrimeContinuousApertureCubicNormalizedReflectionEnergy a b rho p =
      xiMobiusContinuousApertureCubicReflectionFactor a b p *
        weightedPrimeClockReflectionLogMomentEnergy 3 1 rho.re p := by
  let q := xiTransversePrimeApertureDiskNode 1 p
  let L := Real.log (p : ℝ)
  let P : ℝ := p
  have hp0 : 0 < P := by
    dsimp only [P]
    exact_mod_cast p.prop.pos
  have hL : 0 < L := by
    dsimp only [L]
    exact Real.log_pos (by exact_mod_cast p.prop.one_lt)
  have hq : q = P⁻¹ := xiTransversePrimeApertureDiskNode_one_eq_inv p
  have hcore : q ^ 2 * P = P⁻¹ := by
    rw [hq]
    field_simp
  rw [xiMobiusPrimeContinuousApertureCubicNormalizedReflectionEnergy,
    xiMobiusPrimeContinuousApertureCubicCoefficient_eq_slope ha hb,
    xiMobiusPrimeContinuousApertureCubicSlopeTerm,
    normalizedScaleSeamEnergy_prime_eq_primeClockReflectionEnergy,
    xiMobiusContinuousApertureCubicReflectionFactor,
    weightedPrimeClockReflectionLogMomentEnergy]
  change (a ^ 2 * b ^ 2 / (16 * (a + b)) *
      ((q / (1 + q)) ^ 2 * L ^ 3)) *
      (P / 4 * primeClockReflectionEnergy rho.re p) =
    (a ^ 2 * b ^ 2 / (64 * (a + b)) * (1 / (1 + q) ^ 2)) *
      (|L| ^ 3 * (P ^ (-1 : ℝ) * primeClockReflectionEnergy rho.re p))
  rw [abs_of_pos hL, Real.rpow_neg_one, div_pow]
  calc
    (a ^ 2 * b ^ 2 / (16 * (a + b)) *
        (q ^ 2 / (1 + q) ^ 2 * L ^ 3)) *
        (P / 4 * primeClockReflectionEnergy rho.re p) =
      (a ^ 2 * b ^ 2 / (64 * (a + b)) * (1 / (1 + q) ^ 2)) *
        (L ^ 3 * ((q ^ 2 * P) * primeClockReflectionEnergy rho.re p)) := by
      field_simp [(add_pos ha hb).ne']
      ring
    _ = _ := by rw [hcore]

/-- Two-sided uniform comparison of the reflected cubic source factor. -/
theorem xiMobiusContinuousApertureCubicReflectionFactor_bounds
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (p : Nat.Primes) :
    let c := a ^ 2 * b ^ 2 / (64 * (a + b))
    c / 4 ≤ xiMobiusContinuousApertureCubicReflectionFactor a b p ∧
      xiMobiusContinuousApertureCubicReflectionFactor a b p ≤ c := by
  let q := xiTransversePrimeApertureDiskNode 1 p
  let c := a ^ 2 * b ^ 2 / (64 * (a + b))
  have hc : 0 < c := by positivity
  have hq0 : 0 < q := xiTransversePrimeApertureDiskNode_pos 1 p
  have hq1 : q < 1 :=
    xiTransversePrimeApertureDiskNode_lt_one (by norm_num) p
  have hlower : (1 : ℝ) / 4 ≤ 1 / (1 + q) ^ 2 := by
    rw [le_div_iff₀ (by positivity : 0 < (1 + q) ^ 2)]
    nlinarith [sq_nonneg (1 - q)]
  have hupper : 1 / (1 + q) ^ 2 ≤ (1 : ℝ) := by
    rw [div_le_one (by positivity : 0 < (1 + q) ^ 2)]
    nlinarith [sq_nonneg q]
  dsimp only
  rw [xiMobiusContinuousApertureCubicReflectionFactor]
  change c / 4 ≤ c * (1 / (1 + q) ^ 2) ∧
    c * (1 / (1 + q) ^ 2) ≤ c
  constructor <;> nlinarith

/-- **Cubic reflected no-go.** Every positive aperture pair has exactly the open-critical-strip
summability classification. -/
theorem summable_xiMobiusPrimeContinuousApertureCubicNormalizedReflectionEnergy_iff
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (rho : ℂ) :
    Summable (xiMobiusPrimeContinuousApertureCubicNormalizedReflectionEnergy a b rho) ↔
      rho.re = 1 / 2 ∨ |2 * rho.re - 1| < 1 := by
  let c := a ^ 2 * b ^ 2 / (64 * (a + b))
  rw [show xiMobiusPrimeContinuousApertureCubicNormalizedReflectionEnergy a b rho = fun p =>
      xiMobiusContinuousApertureCubicReflectionFactor a b p *
        weightedPrimeClockReflectionLogMomentEnergy 3 1 rho.re p by
    funext p
    exact xiMobiusPrimeContinuousApertureCubicNormalizedReflectionEnergy_eq_factor
      ha hb rho p]
  exact summable_mul_weightedPrimeClockReflectionLogMomentEnergy_iff
    3 1 rho.re (xiMobiusContinuousApertureCubicReflectionFactor a b)
    (c := c / 4) (C := c)
    (by positivity)
    (fun p => (xiMobiusContinuousApertureCubicReflectionFactor_bounds ha hb p).1)
    (fun p => (xiMobiusContinuousApertureCubicReflectionFactor_bounds ha hb p).2)

/-- Total dyadic source innovation after insertion of the normalized value reflection. -/
def xiMobiusContinuousApertureReflectedDyadicInnovation
    (h a b : ℝ) (rho : ℂ) : ℝ :=
  ∑' p : Nat.Primes,
    xiMobiusPrimeContinuousApertureDyadicInnovation h a b p *
      normalizedScaleSeamEnergy (p : ℕ) rho

/-- Total reflected cubic source coefficient. -/
def xiMobiusContinuousApertureReflectedCubicLimit
    (a b : ℝ) (rho : ℂ) : ℝ :=
  ∑' p : Nat.Primes,
    xiMobiusPrimeContinuousApertureCubicNormalizedReflectionEnergy a b rho p

/-- **All-prime reflected cubic germ law.** On the open strip, the normalized dyadic innovation
converges to the finite reflected cubic source coefficient. -/
theorem tendsto_xiMobiusContinuousApertureReflectedDyadicInnovation_div_cube
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1) :
    Tendsto
      (fun h : ℝ =>
        xiMobiusContinuousApertureReflectedDyadicInnovation h a b rho / h ^ 3)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (xiMobiusContinuousApertureReflectedCubicLimit a b rho)) := by
  have hreflected : Summable
      (xiMobiusPrimeContinuousApertureCubicNormalizedReflectionEnergy 1 1 rho) := by
    apply
      (summable_xiMobiusPrimeContinuousApertureCubicNormalizedReflectionEnergy_iff
        (by norm_num) (by norm_num) rho).mpr
    exact Or.inr (abs_lt.mpr ⟨by linarith, by linarith⟩)
  have hsum : Summable (fun p : Nat.Primes =>
      xiMobiusPrimeContinuousApertureCubicSlopeTerm p *
        normalizedScaleSeamEnergy (p : ℕ) rho) := by
    have hscaled := hreflected.mul_left 32
    convert hscaled using 1
    funext p
    rw [xiMobiusPrimeContinuousApertureCubicNormalizedReflectionEnergy,
      xiMobiusPrimeContinuousApertureCubicCoefficient_eq_slope
        (by norm_num) (by norm_num)]
    ring
  have h :=
    tendsto_xiMobiusContinuousApertureWeightedDyadicInnovation_div_cube_of_summable
      ha hb (w := fun p => normalizedScaleSeamEnergy (p : ℕ) rho)
      (fun p => normalizedScaleSeamEnergy_nonneg rho (p : ℕ)) hsum
  simpa [xiMobiusContinuousApertureWeightedDyadicInnovation,
    xiMobiusContinuousApertureWeightedCubicLimit,
    xiMobiusContinuousApertureReflectedDyadicInnovation,
    xiMobiusContinuousApertureReflectedCubicLimit,
    xiMobiusPrimeContinuousApertureCubicNormalizedReflectionEnergy] using h

/-- Every Xi fibre has summable reflected cubic energy for every positive aperture pair. -/
theorem summable_xiMobiusPrimeContinuousApertureCubicNormalizedReflectionEnergy_of_xi_zero
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {rho : ℂ} (hzero : xi rho = 0) :
    Summable (xiMobiusPrimeContinuousApertureCubicNormalizedReflectionEnergy a b rho) := by
  have hstrip := xi_zero_re_mem_open_unit hzero
  apply
    (summable_xiMobiusPrimeContinuousApertureCubicNormalizedReflectionEnergy_iff
      ha hb rho).mpr
  exact Or.inr (abs_lt.mpr ⟨by linarith, by linarith⟩)

/-- The reflected cubic germ law holds on every Xi fibre unconditionally. -/
theorem tendsto_xiMobiusContinuousApertureReflectedDyadicInnovation_of_xi_zero
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {rho : ℂ} (hzero : xi rho = 0) :
    Tendsto
      (fun h : ℝ =>
        xiMobiusContinuousApertureReflectedDyadicInnovation h a b rho / h ^ 3)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (xiMobiusContinuousApertureReflectedCubicLimit a b rho)) :=
  tendsto_xiMobiusContinuousApertureReflectedDyadicInnovation_div_cube
    ha hb (xi_zero_re_mem_open_unit hzero)

/-- Global Prop interface for every positive reflected cubic source sector on Xi fibres. -/
def XiMobiusAllPositiveCubicReflectionEnergySummable : Prop :=
  ∀ a b : ℝ, 0 < a → 0 < b → ∀ rho : ℂ, xi rho = 0 →
    Summable (xiMobiusPrimeContinuousApertureCubicNormalizedReflectionEnergy a b rho)

theorem xiMobiusAllPositiveCubicReflectionEnergySummable :
    XiMobiusAllPositiveCubicReflectionEnergySummable :=
  fun _ _ ha hb _ hzero =>
    summable_xiMobiusPrimeContinuousApertureCubicNormalizedReflectionEnergy_of_xi_zero
      ha hb hzero

/-- Global Prop interface for every positive reflected cubic innovation limit on Xi fibres. -/
def XiMobiusAllPositiveReflectedCubicInnovationLimit : Prop :=
  ∀ a b : ℝ, 0 < a → 0 < b → ∀ rho : ℂ, xi rho = 0 →
    Tendsto
      (fun h : ℝ =>
        xiMobiusContinuousApertureReflectedDyadicInnovation h a b rho / h ^ 3)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (xiMobiusContinuousApertureReflectedCubicLimit a b rho))

theorem xiMobiusAllPositiveReflectedCubicInnovationLimit :
    XiMobiusAllPositiveReflectedCubicInnovationLimit :=
  fun _ _ ha hb _ hzero =>
    tendsto_xiMobiusContinuousApertureReflectedDyadicInnovation_of_xi_zero
      ha hb hzero

end

end RHTower
