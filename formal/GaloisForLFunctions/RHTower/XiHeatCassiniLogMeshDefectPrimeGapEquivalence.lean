import GaloisForLFunctions.RHTower.XiHeatCassiniLogMeshLaplaceResolventDefect

/-!
# Prime-gap energy is the intrinsic Route-T mesh obstruction

At the real critical-wall point `s = -1/2`, every right-endpoint resolvent defect is positive after
removing its prime half-density.  A uniform lower Taylor estimate and two-sided comparison between
additive and logarithmic adjacent-prime gaps therefore complement the existing upper bound.

The resulting equivalence says that absolute convergence of the physical mesh defect is exactly
summability of `gap(p)^2 / p^(3/2)`.  Consequently no sharper estimate of the same right-endpoint
defect can bypass consecutive-prime-gap energy: the arithmetic series is necessary as well as
sufficient.
-/

open Complex Filter Set Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- A uniform lower quadratic bound for the negative exponential remainder on `[0,1]`. -/
theorem exp_neg_sub_one_add_quarter_sq_le
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    x ^ 2 / 4 ≤ Real.exp (-x) - 1 + x := by
  have habs : |(-x)| ≤ 1 := by rw [abs_neg, abs_of_nonneg hx0]; exact hx1
  have hTaylor := Real.exp_bound (x := -x) habs (n := 3) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero,
    Nat.cast_one, div_one, zero_add, pow_one, Nat.cast_ofNat,
    Nat.factorial] at hTaylor
  have hlower := (abs_le.mp hTaylor).1
  rw [abs_neg, abs_of_nonneg hx0] at hlower
  nlinarith [sq_nonneg x,
    mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hx1)]

/-- Under Bertrand, a logarithmic prime cell dominates half its normalized additive gap. -/
theorem primeGap_div_two_prime_le_primeLogGap (N : ℕ) :
    xiHeatCassiniOrderedPrimeGap N / (2 * (nthPrimeSubtype N : ℝ)) ≤
      xiHeatCassiniOrderedPrimeLogGap N := by
  let p : ℝ := nthPrimeSubtype N
  let q : ℝ := nthPrimeSubtype (N + 1)
  have hp : 0 < p := nthPrimeSubtype_pos N
  have hq : 0 < q := nthPrimeSubtype_pos (N + 1)
  have hpq : p ≤ q := by
    dsimp only [p, q]
    exact_mod_cast nthPrimeSubtype_strictMono.monotone (Nat.le_succ N)
  have hq2p : q ≤ 2 * p := by
    dsimp only [p, q]
    exact_mod_cast nthPrimeSubtype_succ_le_two_mul N
  have hlog : 1 - (q / p)⁻¹ ≤ Real.log (q / p) :=
    Real.one_sub_inv_le_log_of_pos (div_pos hq hp)
  have hgaplog : (q - p) / q ≤ Real.log q - Real.log p := by
    rw [Real.log_div hq.ne' hp.ne'] at hlog
    rw [inv_div] at hlog
    have hone : 1 - p / q = (q - p) / q := by
      field_simp [hq.ne']
    rw [hone] at hlog
    exact hlog
  have hgap : 0 ≤ q - p := sub_nonneg.mpr hpq
  have hdiv : (q - p) / (2 * p) ≤ (q - p) / q := by
    exact div_le_div_of_nonneg_left hgap hq hq2p
  change (q - p) / (2 * p) ≤ Real.log q - Real.log p
  exact hdiv.trans hgaplog

/-- Exact norm of one physical mesh defect at the real critical-wall point. -/
theorem norm_xiHeatCassiniLogMeshLaplaceScaledDefect_neg_half_eq
    (N : ℕ) :
    ‖xiHeatCassiniLogMeshLaplaceScaledDefect (((-1 / 2 : ℝ) : ℂ)) N‖ =
      Real.exp (xiMassNthPrimeLogHeight (N + 1) / 2) *
        (Real.exp (-(xiHeatCassiniOrderedPrimeLogGap N / 2)) - 1 +
          xiHeatCassiniOrderedPrimeLogGap N / 2) := by
  let delta : ℝ := xiHeatCassiniOrderedPrimeLogGap N
  have hdelta : 0 ≤ delta := xiHeatCassiniOrderedPrimeLogGap_nonneg N
  have hdelta1 : delta ≤ 1 := xiHeatCassiniOrderedPrimeLogGap_le_one N
  have hrem : 0 ≤ Real.exp (-(delta / 2)) - 1 + delta / 2 := by
    have h := exp_neg_sub_one_add_quarter_sq_le
      (x := delta / 2) (by positivity) (by linarith)
    nlinarith [sq_nonneg (delta / 2)]
  rw [xiHeatCassiniLogMeshLaplaceScaledDefect_eq_expRemainder, norm_mul,
    norm_xiHeatCassiniOrderedPrimeLaplacePhase_of_re_eq_neg_half (by norm_num)]
  congr 1
  have hmul : (((-1 / 2 : ℝ) : ℂ) * (delta : ℂ)) =
      ((-(delta / 2) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hmul, ← Complex.ofReal_exp]
  have hcoe :
      ((Real.exp (-(delta / 2)) : ℂ) - 1 - ((-(delta / 2) : ℝ) : ℂ)) =
        ((Real.exp (-(delta / 2)) - 1 + delta / 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hcoe]
  change ‖((Real.exp (-(delta / 2)) - 1 + delta / 2 : ℝ) : ℂ)‖ =
    Real.exp (-(delta / 2)) - 1 + delta / 2
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hrem]

/-- Normalized consecutive-prime-gap energy at the Route-T critical wall. -/
def xiHeatCassiniPrimeGapCriticalEnergy (N : ℕ) : ℝ :=
  (xiHeatCassiniOrderedPrimeGap N / (nthPrimeSubtype N : ℝ)) ^ 2 *
    Real.sqrt (nthPrimeSubtype N : ℝ)

theorem xiHeatCassiniPrimeGapCriticalEnergy_nonneg (N : ℕ) :
    0 ≤ xiHeatCassiniPrimeGapCriticalEnergy N := by
  unfold xiHeatCassiniPrimeGapCriticalEnergy
  positivity

/-- The critical prime-gap energy is bounded below by each exact physical mesh defect. -/
theorem primeGapSq_criticalWeight_le_norm_defect_neg_half (N : ℕ) :
    (1 / 64 : ℝ) *
        (xiHeatCassiniOrderedPrimeGap N / (nthPrimeSubtype N : ℝ)) ^ 2 *
          Real.sqrt (nthPrimeSubtype N : ℝ) ≤
      ‖xiHeatCassiniLogMeshLaplaceScaledDefect (((-1 / 2 : ℝ) : ℂ)) N‖ := by
  let p : ℝ := nthPrimeSubtype N
  let q : ℝ := nthPrimeSubtype (N + 1)
  let delta : ℝ := xiHeatCassiniOrderedPrimeLogGap N
  let gap : ℝ := xiHeatCassiniOrderedPrimeGap N
  have hp : 0 < p := nthPrimeSubtype_pos N
  have hq : 0 < q := nthPrimeSubtype_pos (N + 1)
  have hdelta : 0 ≤ delta := xiHeatCassiniOrderedPrimeLogGap_nonneg N
  have hdelta1 : delta ≤ 1 := xiHeatCassiniOrderedPrimeLogGap_le_one N
  have hgap : 0 ≤ gap := xiHeatCassiniOrderedPrimeGap_nonneg N
  have hratio : gap / (2 * p) ≤ delta := by
    simpa only [p, gap, delta] using primeGap_div_two_prime_le_primeLogGap N
  have hratio0 : 0 ≤ gap / (2 * p) := by positivity
  have hsq : (gap / (2 * p)) ^ 2 ≤ delta ^ 2 :=
    (sq_le_sq₀ hratio0 hdelta).mpr hratio
  have hrem := exp_neg_sub_one_add_quarter_sq_le
    (x := delta / 2) (by positivity) (by linarith)
  have hsqrt : Real.sqrt p ≤ Real.exp (xiMassNthPrimeLogHeight (N + 1) / 2) := by
    have hpq : p ≤ q := by
      dsimp only [p, q]
      exact_mod_cast nthPrimeSubtype_strictMono.monotone (Nat.le_succ N)
    have hsqrtpq := Real.sqrt_le_sqrt hpq
    have hexp : Real.exp (xiMassNthPrimeLogHeight (N + 1) / 2) = Real.sqrt q := by
      dsimp only [xiMassNthPrimeLogHeight, q]
      rw [← Real.log_sqrt hq.le, Real.exp_log (Real.sqrt_pos.mpr hq)]
    rwa [hexp]
  rw [norm_xiHeatCassiniLogMeshLaplaceScaledDefect_neg_half_eq]
  change (1 / 64 : ℝ) * (gap / p) ^ 2 * Real.sqrt p ≤
    Real.exp (xiMassNthPrimeLogHeight (N + 1) / 2) *
      (Real.exp (-(delta / 2)) - 1 + delta / 2)
  calc
    (1 / 64 : ℝ) * (gap / p) ^ 2 * Real.sqrt p =
        Real.sqrt p * ((gap / (2 * p)) ^ 2 / 16) := by ring
    _ ≤ Real.sqrt p * (delta ^ 2 / 16) := by gcongr
    _ = Real.sqrt p * ((delta / 2) ^ 2 / 4) := by ring
    _ ≤ Real.exp (xiMassNthPrimeLogHeight (N + 1) / 2) *
        (Real.exp (-(delta / 2)) - 1 + delta / 2) := by
      exact mul_le_mul hsqrt hrem (by positivity) (by positivity)

/-- **Intrinsic critical-wall obstruction.**  Absolute convergence of the physical right-endpoint
mesh defect at `s = -1/2` is equivalent to summability of normalized consecutive-prime-gap
energy.  Thus the prime-gap square is not an artifact of a one-sided Taylor majorant. -/
theorem summable_norm_xiHeatCassiniLogMeshLaplaceScaledDefect_neg_half_iff :
    Summable (fun N : ℕ =>
      ‖xiHeatCassiniLogMeshLaplaceScaledDefect (((-1 / 2 : ℝ) : ℂ)) N‖) ↔
      Summable xiHeatCassiniPrimeGapCriticalEnergy := by
  constructor
  · intro hdefect
    have hmajor := hdefect.mul_left (64 : ℝ)
    refine Summable.of_nonneg_of_le xiHeatCassiniPrimeGapCriticalEnergy_nonneg
      (fun N => ?_) hmajor
    have hlower := primeGapSq_criticalWeight_le_norm_defect_neg_half N
    unfold xiHeatCassiniPrimeGapCriticalEnergy
    nlinarith [norm_nonneg
      (xiHeatCassiniLogMeshLaplaceScaledDefect (((-1 / 2 : ℝ) : ℂ)) N)]
  · intro henergy
    let C : ℝ := 2 * ‖(((-1 / 2 : ℝ) : ℂ))‖ ^ 2 *
      Real.exp ‖(((-1 / 2 : ℝ) : ℂ))‖
    have hmajor := henergy.mul_left C
    refine Summable.of_nonneg_of_le (fun N => norm_nonneg _) (fun N => ?_) hmajor
    simpa only [C, xiHeatCassiniPrimeGapCriticalEnergy, mul_assoc] using
      (norm_xiHeatCassiniLogMeshLaplaceScaledDefect_le_primeGapSq
        (s := (((-1 / 2 : ℝ) : ℂ))) (by norm_num) N)

/-- Consecutive-prime-gap energy at negative Laplace depth `a`, with exact right-endpoint
half-density. -/
def xiHeatCassiniPrimeGapAbscissaEnergy (a : ℝ) (N : ℕ) : ℝ :=
  (xiHeatCassiniOrderedPrimeGap N / (nthPrimeSubtype N : ℝ)) ^ 2 *
    Real.exp (a * xiMassNthPrimeLogHeight (N + 1))

theorem xiHeatCassiniPrimeGapAbscissaEnergy_nonneg (a : ℝ) (N : ℕ) :
    0 ≤ xiHeatCassiniPrimeGapAbscissaEnergy a N := by
  unfold xiHeatCassiniPrimeGapAbscissaEnergy
  positivity

/-- Exact norm of one physical defect at every real negative Laplace depth. -/
theorem norm_xiHeatCassiniLogMeshLaplaceScaledDefect_neg_real_eq
    {a : ℝ} (ha : 0 ≤ a) (N : ℕ) :
    ‖xiHeatCassiniLogMeshLaplaceScaledDefect (((-a : ℝ) : ℂ)) N‖ =
      Real.exp (a * xiMassNthPrimeLogHeight (N + 1)) *
        (Real.exp (-(a * xiHeatCassiniOrderedPrimeLogGap N)) - 1 +
          a * xiHeatCassiniOrderedPrimeLogGap N) := by
  let delta : ℝ := xiHeatCassiniOrderedPrimeLogGap N
  have hdelta : 0 ≤ delta := xiHeatCassiniOrderedPrimeLogGap_nonneg N
  have hrem : 0 ≤ Real.exp (-(a * delta)) - 1 + a * delta := by
    linarith [Real.add_one_le_exp (-(a * delta))]
  rw [xiHeatCassiniLogMeshLaplaceScaledDefect_eq_expRemainder, norm_mul,
    norm_xiHeatCassiniOrderedPrimeLaplacePhase]
  congr 1
  · congr 1
    simp
  · have hmul : (((-a : ℝ) : ℂ) * (delta : ℂ)) =
        ((-(a * delta) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hmul, ← Complex.ofReal_exp]
    have hcoe :
        ((Real.exp (-(a * delta)) : ℂ) - 1 - ((-(a * delta) : ℝ) : ℂ)) =
          ((Real.exp (-(a * delta)) - 1 + a * delta : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hcoe, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hrem]

/-- Uniform lower comparison: the exact defect contains the full weighted gap-square energy. -/
theorem mul_primeGapAbscissaEnergy_le_norm_defect_neg_real
    {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) (N : ℕ) :
    (a ^ 2 / 16) * xiHeatCassiniPrimeGapAbscissaEnergy a N ≤
      ‖xiHeatCassiniLogMeshLaplaceScaledDefect (((-a : ℝ) : ℂ)) N‖ := by
  let delta : ℝ := xiHeatCassiniOrderedPrimeLogGap N
  let gap : ℝ := xiHeatCassiniOrderedPrimeGap N
  let p : ℝ := nthPrimeSubtype N
  have hdelta : 0 ≤ delta := xiHeatCassiniOrderedPrimeLogGap_nonneg N
  have hdelta1 : delta ≤ 1 := xiHeatCassiniOrderedPrimeLogGap_le_one N
  have hgap : 0 ≤ gap := xiHeatCassiniOrderedPrimeGap_nonneg N
  have hp : 0 < p := nthPrimeSubtype_pos N
  have hratio : gap / (2 * p) ≤ delta := by
    simpa only [gap, p, delta] using primeGap_div_two_prime_le_primeLogGap N
  have hratio0 : 0 ≤ gap / (2 * p) := by positivity
  have hsq : (gap / (2 * p)) ^ 2 ≤ delta ^ 2 :=
    (sq_le_sq₀ hratio0 hdelta).mpr hratio
  have hx0 : 0 ≤ a * delta := mul_nonneg ha0.le hdelta
  have hx1 : a * delta ≤ 1 := by nlinarith
  have hrem := exp_neg_sub_one_add_quarter_sq_le hx0 hx1
  rw [norm_xiHeatCassiniLogMeshLaplaceScaledDefect_neg_real_eq ha0.le]
  unfold xiHeatCassiniPrimeGapAbscissaEnergy
  change (a ^ 2 / 16) * ((gap / p) ^ 2 *
      Real.exp (a * xiMassNthPrimeLogHeight (N + 1))) ≤
    Real.exp (a * xiMassNthPrimeLogHeight (N + 1)) *
      (Real.exp (-(a * delta)) - 1 + a * delta)
  have hexp0 : 0 ≤ Real.exp (a * xiMassNthPrimeLogHeight (N + 1)) :=
    Real.exp_nonneg _
  calc
    (a ^ 2 / 16) * ((gap / p) ^ 2 *
        Real.exp (a * xiMassNthPrimeLogHeight (N + 1))) =
        Real.exp (a * xiMassNthPrimeLogHeight (N + 1)) *
          ((a ^ 2 / 16) * (gap / p) ^ 2) := by ring
    _ ≤ Real.exp (a * xiMassNthPrimeLogHeight (N + 1)) *
        (Real.exp (-(a * delta)) - 1 + a * delta) := by
      apply mul_le_mul_of_nonneg_left _ hexp0
      calc
        (a ^ 2 / 16) * (gap / p) ^ 2 =
            (a * (gap / (2 * p))) ^ 2 / 4 := by ring
        _ ≤ (a * delta) ^ 2 / 4 := by
          gcongr
        _ ≤ Real.exp (-(a * delta)) - 1 + a * delta := hrem

/-- Uniform upper comparison: no more than the same weighted gap-square energy is present. -/
theorem norm_defect_neg_real_le_mul_primeGapAbscissaEnergy
    {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) (N : ℕ) :
    ‖xiHeatCassiniLogMeshLaplaceScaledDefect (((-a : ℝ) : ℂ)) N‖ ≤
      (a ^ 2 * Real.exp a) * xiHeatCassiniPrimeGapAbscissaEnergy a N := by
  let delta : ℝ := xiHeatCassiniOrderedPrimeLogGap N
  let gap : ℝ := xiHeatCassiniOrderedPrimeGap N
  let p : ℝ := nthPrimeSubtype N
  have hdelta : 0 ≤ delta := xiHeatCassiniOrderedPrimeLogGap_nonneg N
  have hdelta1 : delta ≤ 1 := xiHeatCassiniOrderedPrimeLogGap_le_one N
  have hgap : 0 ≤ gap := xiHeatCassiniOrderedPrimeGap_nonneg N
  have hp : 0 < p := nthPrimeSubtype_pos N
  have hdle : delta ≤ gap / p := by
    simpa only [gap, p, delta] using
      xiHeatCassiniOrderedPrimeLogGap_le_gap_div_prime N
  have hratio0 : 0 ≤ gap / p := by positivity
  have hsq : delta ^ 2 ≤ (gap / p) ^ 2 :=
    (sq_le_sq₀ hdelta hratio0).mpr hdle
  have hexp : Real.exp (a * delta) ≤ Real.exp a := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hbase := norm_xiHeatCassiniLogMeshLaplaceScaledDefect_le
    (((-a : ℝ) : ℂ)) N
  rw [norm_xiHeatCassiniOrderedPrimeLaplacePhase] at hbase
  have hsre : (((-a : ℝ) : ℂ)).re = -a := rfl
  simp only [hsre, neg_mul, neg_neg] at hbase
  have hnorm : ‖(((-a : ℝ) : ℂ) * (delta : ℂ))‖ = a * delta := by
    rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_neg, abs_of_nonneg ha0.le, abs_of_nonneg hdelta]
  rw [hnorm] at hbase
  unfold xiHeatCassiniPrimeGapAbscissaEnergy
  change ‖xiHeatCassiniLogMeshLaplaceScaledDefect (((-a : ℝ) : ℂ)) N‖ ≤
    (a ^ 2 * Real.exp a) * ((gap / p) ^ 2 *
      Real.exp (a * xiMassNthPrimeLogHeight (N + 1)))
  calc
    ‖xiHeatCassiniLogMeshLaplaceScaledDefect (((-a : ℝ) : ℂ)) N‖ ≤
        Real.exp (a * xiMassNthPrimeLogHeight (N + 1)) *
          (a * delta) ^ 2 * Real.exp (a * delta) := hbase
    _ ≤ Real.exp (a * xiMassNthPrimeLogHeight (N + 1)) *
          (a ^ 2 * (gap / p) ^ 2) * Real.exp a := by
      gcongr
      nlinarith [hsq]
    _ = (a ^ 2 * Real.exp a) * ((gap / p) ^ 2 *
          Real.exp (a * xiMassNthPrimeLogHeight (N + 1))) := by ring

/-- **Route-T obstruction spectrum.**  At every negative depth `0 < a ≤ 1`, absolute convergence
of the exact physical defect is equivalent to the consecutive-prime gap-square energy with
right-endpoint density `p_(n+1)^a`. -/
theorem summable_norm_xiHeatCassiniLogMeshLaplaceScaledDefect_neg_real_iff
    {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) :
    Summable (fun N : ℕ =>
      ‖xiHeatCassiniLogMeshLaplaceScaledDefect (((-a : ℝ) : ℂ)) N‖) ↔
      Summable (xiHeatCassiniPrimeGapAbscissaEnergy a) := by
  constructor
  · intro hdefect
    have hscale0 : 0 < 16 / a ^ 2 := by positivity
    have hmajor := hdefect.mul_left (16 / a ^ 2)
    refine Summable.of_nonneg_of_le
      (xiHeatCassiniPrimeGapAbscissaEnergy_nonneg a) (fun N => ?_) hmajor
    have hlower := mul_primeGapAbscissaEnergy_le_norm_defect_neg_real ha0 ha1 N
    calc
      xiHeatCassiniPrimeGapAbscissaEnergy a N =
          (16 / a ^ 2) * ((a ^ 2 / 16) *
            xiHeatCassiniPrimeGapAbscissaEnergy a N) := by
        field_simp [ne_of_gt ha0]
      _ ≤ (16 / a ^ 2) *
          ‖xiHeatCassiniLogMeshLaplaceScaledDefect (((-a : ℝ) : ℂ)) N‖ :=
        mul_le_mul_of_nonneg_left hlower hscale0.le
  · intro henergy
    have hmajor := henergy.mul_left (a ^ 2 * Real.exp a)
    refine Summable.of_nonneg_of_le (fun N => norm_nonneg _) (fun N => ?_) hmajor
    exact norm_defect_neg_real_le_mul_primeGapAbscissaEnergy ha0 ha1 N

/-- Deeper negative abscissae carry pointwise larger prime-gap energy. -/
theorem xiHeatCassiniPrimeGapAbscissaEnergy_mono
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (N : ℕ) :
    xiHeatCassiniPrimeGapAbscissaEnergy a N ≤
      xiHeatCassiniPrimeGapAbscissaEnergy b N := by
  unfold xiHeatCassiniPrimeGapAbscissaEnergy
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_right hab (xiMassNthPrimeLogHeight_pos (N + 1)).le

/-- Summability propagates monotonically from a deeper negative abscissa to every shallower one. -/
theorem summable_primeGapAbscissaEnergy_of_le
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (h : Summable (xiHeatCassiniPrimeGapAbscissaEnergy b)) :
    Summable (xiHeatCassiniPrimeGapAbscissaEnergy a) :=
  Summable.of_nonneg_of_le (xiHeatCassiniPrimeGapAbscissaEnergy_nonneg a)
    (xiHeatCassiniPrimeGapAbscissaEnergy_mono ha hab) h

/-- The right-endpoint spectrum at depth `1/2` is exactly the intrinsic critical energy already
isolated with left-endpoint half-density. -/
theorem summable_primeGapAbscissaEnergy_half_iff_criticalEnergy :
    Summable (xiHeatCassiniPrimeGapAbscissaEnergy (1 / 2)) ↔
      Summable xiHeatCassiniPrimeGapCriticalEnergy := by
  have hspectrum :=
    summable_norm_xiHeatCassiniLogMeshLaplaceScaledDefect_neg_real_iff
      (a := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  have hreal : -(1 / 2 : ℝ) = -1 / 2 := by ring
  constructor
  · intro henergy
    have hdefect := hspectrum.mpr henergy
    apply summable_norm_xiHeatCassiniLogMeshLaplaceScaledDefect_neg_half_iff.mp
    simpa only [hreal] using hdefect
  · intro hcritical
    apply hspectrum.mp
    have hdefect :=
      summable_norm_xiHeatCassiniLogMeshLaplaceScaledDefect_neg_half_iff.mpr hcritical
    simpa only [hreal] using hdefect

/-- One critical-wall energy estimate controls the complete real obstruction spectrum above the
critical wall. -/
theorem summable_primeGapAbscissaEnergy_of_criticalEnergy
    {a : ℝ} (ha0 : 0 ≤ a) (hahalf : a ≤ 1 / 2)
    (hcritical : Summable xiHeatCassiniPrimeGapCriticalEnergy) :
    Summable (xiHeatCassiniPrimeGapAbscissaEnergy a) := by
  apply summable_primeGapAbscissaEnergy_of_le ha0 hahalf
  exact summable_primeGapAbscissaEnergy_half_iff_criticalEnergy.mpr hcritical

/-- Complex defects at any fixed spectral parameter are majorized by the energy indexed only by
their negative real part.  Imaginary height affects the constant but not the arithmetic exponent. -/
theorem norm_xiHeatCassiniLogMeshLaplaceScaledDefect_le_abscissaEnergy
    (s : ℂ) (N : ℕ) :
    ‖xiHeatCassiniLogMeshLaplaceScaledDefect s N‖ ≤
      (‖s‖ ^ 2 * Real.exp ‖s‖) *
        xiHeatCassiniPrimeGapAbscissaEnergy (-s.re) N := by
  let delta : ℝ := xiHeatCassiniOrderedPrimeLogGap N
  let gap : ℝ := xiHeatCassiniOrderedPrimeGap N
  let p : ℝ := nthPrimeSubtype N
  have hdelta : 0 ≤ delta := xiHeatCassiniOrderedPrimeLogGap_nonneg N
  have hdelta1 : delta ≤ 1 := xiHeatCassiniOrderedPrimeLogGap_le_one N
  have hgap : 0 ≤ gap := xiHeatCassiniOrderedPrimeGap_nonneg N
  have hp : 0 < p := nthPrimeSubtype_pos N
  have hdle : delta ≤ gap / p := by
    simpa only [gap, p, delta] using
      xiHeatCassiniOrderedPrimeLogGap_le_gap_div_prime N
  have hratio0 : 0 ≤ gap / p := by positivity
  have hsq : delta ^ 2 ≤ (gap / p) ^ 2 :=
    (sq_le_sq₀ hdelta hratio0).mpr hdle
  have hexp : Real.exp (‖s‖ * delta) ≤ Real.exp ‖s‖ := by
    apply Real.exp_le_exp.mpr
    nlinarith [norm_nonneg s]
  have hbase := norm_xiHeatCassiniLogMeshLaplaceScaledDefect_le s N
  rw [norm_xiHeatCassiniOrderedPrimeLaplacePhase] at hbase
  have hnorm : ‖s * (delta : ℂ)‖ = ‖s‖ * delta := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hdelta]
  rw [hnorm] at hbase
  unfold xiHeatCassiniPrimeGapAbscissaEnergy
  change ‖xiHeatCassiniLogMeshLaplaceScaledDefect s N‖ ≤
    (‖s‖ ^ 2 * Real.exp ‖s‖) * ((gap / p) ^ 2 *
      Real.exp (-s.re * xiMassNthPrimeLogHeight (N + 1)))
  calc
    ‖xiHeatCassiniLogMeshLaplaceScaledDefect s N‖ ≤
        Real.exp (-s.re * xiMassNthPrimeLogHeight (N + 1)) *
          (‖s‖ * delta) ^ 2 * Real.exp (‖s‖ * delta) := by
      simpa only [neg_mul] using hbase
    _ ≤ Real.exp (-s.re * xiMassNthPrimeLogHeight (N + 1)) *
          (‖s‖ ^ 2 * (gap / p) ^ 2) * Real.exp ‖s‖ := by
      gcongr
      nlinarith [hsq, sq_nonneg ‖s‖]
    _ = (‖s‖ ^ 2 * Real.exp ‖s‖) * ((gap / p) ^ 2 *
          Real.exp (-s.re * xiMassNthPrimeLogHeight (N + 1))) := by ring

/-- Energy at the real abscissa implies absolute convergence of the full complex defect series. -/
theorem summable_norm_xiHeatCassiniLogMeshLaplaceScaledDefect_of_abscissaEnergy
    (s : ℂ) (henergy : Summable (xiHeatCassiniPrimeGapAbscissaEnergy (-s.re))) :
    Summable (fun N : ℕ => ‖xiHeatCassiniLogMeshLaplaceScaledDefect s N‖) := by
  have hmajor := henergy.mul_left (‖s‖ ^ 2 * Real.exp ‖s‖)
  exact Summable.of_nonneg_of_le (fun N => norm_nonneg _)
    (norm_xiHeatCassiniLogMeshLaplaceScaledDefect_le_abscissaEnergy s) hmajor

/-- **Universal half-strip mesh law.**  A single critical energy estimate makes every physical
mesh-defect series absolutely convergent throughout `-1/2 ≤ re s ≤ 0`, uniformly in arithmetic
exponent (though not uniformly in imaginary height). -/
theorem summable_norm_xiHeatCassiniLogMeshLaplaceScaledDefect_of_criticalEnergy
    {s : ℂ} (hsleft : -(1 / 2 : ℝ) ≤ s.re) (hsright : s.re ≤ 0)
    (hcritical : Summable xiHeatCassiniPrimeGapCriticalEnergy) :
    Summable (fun N : ℕ => ‖xiHeatCassiniLogMeshLaplaceScaledDefect s N‖) := by
  apply summable_norm_xiHeatCassiniLogMeshLaplaceScaledDefect_of_abscissaEnergy
  apply summable_primeGapAbscissaEnergy_of_criticalEnergy
  · linarith
  · linarith
  · exact hcritical

/-- In zeta coordinates, every point in the closed critical-to-one strip shifts into the universal
mesh half-strip.  The imaginary part changes only a harmless fixed constant. -/
theorem summable_norm_xiHeatCassiniLogMeshLaplaceScaledDefect_zeroShift_of_criticalEnergy
    {rho : ℂ} (hhalf : (1 / 2 : ℝ) ≤ rho.re) (hone : rho.re ≤ 1)
    (hcritical : Summable xiHeatCassiniPrimeGapCriticalEnergy) :
    Summable (fun N : ℕ =>
      ‖xiHeatCassiniLogMeshLaplaceScaledDefect (rho - 1) N‖) := by
  apply summable_norm_xiHeatCassiniLogMeshLaplaceScaledDefect_of_criticalEnergy
  · simpa using (show -(1 / 2 : ℝ) ≤ rho.re - 1 by linarith)
  · simpa using (show rho.re - 1 ≤ 0 by linarith)
  · exact hcritical


end

end RHTower
