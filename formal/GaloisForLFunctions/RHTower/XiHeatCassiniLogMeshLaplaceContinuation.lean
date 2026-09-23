import GaloisForLFunctions.RHTower.XiHeatCassiniLogMeshDefectPrimeGapEquivalence

/-!
# Prime-gap continuation of the Route-T logarithmic mesh

The scaled right-endpoint defect is not merely pointwise summable in the critical half-strip.
One critical prime-gap energy estimate gives a locally uniform majorant, hence a continuous defect
sum.  Solving the exact finite resolvent telescope for the mesh current then produces a canonical
continuation

`(phase 0 - defect sum) / s`.

This function agrees with the original absolutely convergent mesh current on `Re s > 0` and is
continuous at every nonzero point with `-1/2 < Re s ≤ 0`.  In particular it has zero residue at
the first Wold pole attached to every zeta zero right of the critical line.  Thus, conditional only
on the already-isolated critical gap energy, logarithmic mesh continuation cannot compensate the
Wold pole.  No analytic continuation or RH statement is assumed.
-/

open Complex Filter Set Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Absolutely convergent scaled-defect sum wherever the prime-gap energy supplies convergence. -/
def xiHeatCassiniLogMeshLaplaceDefectSum (s : ℂ) : ℂ :=
  ∑' N : ℕ, xiHeatCassiniLogMeshLaplaceScaledDefect s N

/-- **Local uniformity from critical gap energy.**  The defect sum is continuous throughout the
open critical half-strip, including the imaginary boundary `Re s = 0`. -/
theorem continuousAt_xiHeatCassiniLogMeshLaplaceDefectSum_of_criticalEnergy
    {s0 : ℂ} (hsleft : -(1 / 2 : ℝ) < s0.re) (hsright : s0.re ≤ 0)
    (hcritical : Summable xiHeatCassiniPrimeGapCriticalEnergy) :
    ContinuousAt xiHeatCassiniLogMeshLaplaceDefectSum s0 := by
  let r : ℝ := (s0.re + 1 / 2) / 2
  have hr : 0 < r := by
    dsimp only [r]
    linarith
  let a : ℝ := -s0.re + r
  have ha0 : 0 ≤ a := by
    dsimp only [a, r]
    linarith
  have hahalf : a ≤ 1 / 2 := by
    dsimp only [a, r]
    linarith
  let B : ℝ := ‖s0‖ + r
  have hB0 : 0 ≤ B := by
    dsimp only [B]
    positivity
  let C : ℝ := B ^ (2 : ℕ) * Real.exp B
  have hC0 : 0 ≤ C := by
    dsimp only [C]
    positivity
  let M : ℕ → ℝ := fun N =>
    C * xiHeatCassiniPrimeGapAbscissaEnergy a N
  have hM : Summable M := by
    exact (summable_primeGapAbscissaEnergy_of_criticalEnergy ha0 hahalf hcritical).mul_left C
  have hpoint : ∀ N : ℕ,
      Tendsto (fun s : ℂ => xiHeatCassiniLogMeshLaplaceScaledDefect s N)
        (𝓝 s0) (𝓝 (xiHeatCassiniLogMeshLaplaceScaledDefect s0 N)) := by
    intro N
    apply ContinuousAt.tendsto
    simp only [xiHeatCassiniLogMeshLaplaceScaledDefect,
      xiHeatCassiniLogMeshLaplaceAtom,
      xiHeatCassiniOrderedPrimeLaplacePhase,
      xiHeatCassiniOrderedPrimeComplexNegativePhase]
    fun_prop
  have hdom : ∀ᶠ s : ℂ in 𝓝 s0, ∀ N : ℕ,
      ‖xiHeatCassiniLogMeshLaplaceScaledDefect s N‖ ≤ M N := by
    filter_upwards [Metric.ball_mem_nhds s0 hr] with s hs N
    have hdist : ‖s - s0‖ < r := by
      simpa only [Metric.mem_ball, Complex.dist_eq] using hs
    have hreabs : |s.re - s0.re| ≤ ‖s - s0‖ := by
      simpa only [Complex.sub_re] using Complex.abs_re_le_norm (s - s0)
    have hrediff : |s.re - s0.re| < r := lt_of_le_of_lt hreabs hdist
    have hsreLower : s0.re - r < s.re := by
      rw [abs_lt] at hrediff
      linarith
    have hnegRe : -s.re ≤ a := by
      dsimp only [a]
      linarith
    have hsnorm : ‖s‖ ≤ B := by
      calc
        ‖s‖ = ‖(s - s0) + s0‖ := by ring_nf
        _ ≤ ‖s - s0‖ + ‖s0‖ := norm_add_le _ _
        _ ≤ B := by
          dsimp only [B]
          linarith
    have hfactor : ‖s‖ ^ (2 : ℕ) * Real.exp ‖s‖ ≤ C := by
      dsimp only [C]
      gcongr
    have henergy :
        xiHeatCassiniPrimeGapAbscissaEnergy (-s.re) N ≤
          xiHeatCassiniPrimeGapAbscissaEnergy a N := by
      unfold xiHeatCassiniPrimeGapAbscissaEnergy
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_right hnegRe
        (xiMassNthPrimeLogHeight_pos (N + 1)).le
    calc
      ‖xiHeatCassiniLogMeshLaplaceScaledDefect s N‖ ≤
          (‖s‖ ^ (2 : ℕ) * Real.exp ‖s‖) *
            xiHeatCassiniPrimeGapAbscissaEnergy (-s.re) N :=
        norm_xiHeatCassiniLogMeshLaplaceScaledDefect_le_abscissaEnergy s N
      _ ≤ C * xiHeatCassiniPrimeGapAbscissaEnergy a N := by
        exact mul_le_mul hfactor henergy
          (xiHeatCassiniPrimeGapAbscissaEnergy_nonneg (-s.re) N) hC0
      _ = M N := rfl
  have hmain := tendsto_tsum_of_dominated_convergence hM hpoint hdom
  change Tendsto
    (fun s : ℂ => ∑' N : ℕ, xiHeatCassiniLogMeshLaplaceScaledDefect s N)
    (𝓝 s0)
    (𝓝 (∑' N : ℕ, xiHeatCassiniLogMeshLaplaceScaledDefect s0 N))
  exact hmain

/-- Exact derivative of one scaled mesh defect in exponential-remainder coordinates. -/
def xiHeatCassiniLogMeshLaplaceScaledDefectDerivative (s : ℂ) (N : ℕ) : ℂ :=
  xiHeatCassiniOrderedPrimeLaplacePhase (N + 1) s *
    (-((xiMassNthPrimeLogHeight (N + 1) : ℝ) : ℂ) *
        (Complex.exp (s * (xiHeatCassiniOrderedPrimeLogGap N : ℂ)) - 1 -
          s * (xiHeatCassiniOrderedPrimeLogGap N : ℂ)) +
      (xiHeatCassiniOrderedPrimeLogGap N : ℂ) *
        (Complex.exp (s * (xiHeatCassiniOrderedPrimeLogGap N : ℂ)) - 1))

theorem hasDerivAt_xiHeatCassiniLogMeshLaplaceScaledDefect
    (s : ℂ) (N : ℕ) :
    HasDerivAt (fun z : ℂ => xiHeatCassiniLogMeshLaplaceScaledDefect z N)
      (xiHeatCassiniLogMeshLaplaceScaledDefectDerivative s N) s := by
  have heq : (fun z : ℂ => xiHeatCassiniLogMeshLaplaceScaledDefect z N) =
      fun z : ℂ => xiHeatCassiniOrderedPrimeLaplacePhase (N + 1) z *
        (Complex.exp (z * (xiHeatCassiniOrderedPrimeLogGap N : ℂ)) - 1 -
          z * (xiHeatCassiniOrderedPrimeLogGap N : ℂ)) := by
    funext z
    exact xiHeatCassiniLogMeshLaplaceScaledDefect_eq_expRemainder z N
  rw [heq]
  let h : ℂ := (xiMassNthPrimeLogHeight (N + 1) : ℂ)
  let d : ℂ := (xiHeatCassiniOrderedPrimeLogGap N : ℂ)
  have hphaseEq : (fun z : ℂ =>
      xiHeatCassiniOrderedPrimeLaplacePhase (N + 1) z) =
      fun z : ℂ => Complex.exp (-h * z) := by
    funext z
    unfold xiHeatCassiniOrderedPrimeLaplacePhase
      xiHeatCassiniOrderedPrimeComplexNegativePhase
    congr 1
    dsimp only [h]
    ring_nf
    rw [Complex.I_sq]
    ring
  have hphase : HasDerivAt
      (fun z : ℂ => xiHeatCassiniOrderedPrimeLaplacePhase (N + 1) z)
      (-h * xiHeatCassiniOrderedPrimeLaplacePhase (N + 1) s) s := by
    have hphaseVal := congrFun hphaseEq s
    rw [hphaseEq]
    rw [hphaseVal]
    have hx := (hasDerivAt_const_mul (x := s) (-h : ℂ)).cexp
    simpa only [mul_comm] using hx
  have hlin : HasDerivAt (fun z : ℂ => z * d) d s :=
    hasDerivAt_mul_const d
  have hrem : HasDerivAt
      (fun z : ℂ => Complex.exp (z * d) - 1 - z * d)
      (Complex.exp (s * d) * d - d) s :=
    (hlin.cexp.sub_const 1).sub hlin
  have hmul := hphase.mul hrem
  change HasDerivAt
    ((fun z : ℂ => xiHeatCassiniOrderedPrimeLaplacePhase (N + 1) z) *
      fun z : ℂ => Complex.exp (z * d) - 1 - z * d)
    (xiHeatCassiniLogMeshLaplaceScaledDefectDerivative s N) s
  apply hmul.congr_deriv
  unfold xiHeatCassiniLogMeshLaplaceScaledDefectDerivative
  dsimp only [h, d]
  ring

/-- Global first-order exponential Taylor bound, used by the defect derivative estimate. -/
theorem norm_exp_sub_one_le_norm_mul_exp (w : ℂ) :
    ‖Complex.exp w - 1‖ ≤ ‖w‖ * Real.exp ‖w‖ := by
  have hTaylor := Complex.norm_exp_sub_sum_le_norm_mul_exp w 1
  simpa [Finset.sum_range_succ, Nat.factorial] using hTaylor

/-- The defect derivative is still quadratic in the log-cell width; differentiation costs only
one prime-log height. -/
theorem norm_xiHeatCassiniLogMeshLaplaceScaledDefectDerivative_le
    (s : ℂ) (N : ℕ) :
    ‖xiHeatCassiniLogMeshLaplaceScaledDefectDerivative s N‖ ≤
      ‖xiHeatCassiniOrderedPrimeLaplacePhase (N + 1) s‖ *
        (Real.exp ‖s‖ * xiHeatCassiniOrderedPrimeLogGap N ^ (2 : ℕ) *
          (xiMassNthPrimeLogHeight (N + 1) * ‖s‖ ^ (2 : ℕ) + ‖s‖)) := by
  let d : ℝ := xiHeatCassiniOrderedPrimeLogGap N
  let h : ℝ := xiMassNthPrimeLogHeight (N + 1)
  have hd0 : 0 ≤ d := xiHeatCassiniOrderedPrimeLogGap_nonneg N
  have hd1 : d ≤ 1 := xiHeatCassiniOrderedPrimeLogGap_le_one N
  have hh0 : 0 ≤ h := (xiMassNthPrimeLogHeight_pos (N + 1)).le
  let w : ℂ := s * (d : ℂ)
  have hnormw : ‖w‖ = ‖s‖ * d := by
    dsimp only [w]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hd0]
  have hrem :
      ‖Complex.exp w - 1 - w‖ ≤ ‖w‖ ^ (2 : ℕ) * Real.exp ‖w‖ := by
    have hTaylor := Complex.norm_exp_sub_sum_le_norm_mul_exp w 2
    rw [sub_sub]
    simpa [Finset.sum_range_succ, Nat.factorial] using hTaylor
  have hone := norm_exp_sub_one_le_norm_mul_exp w
  have hexp : Real.exp ‖w‖ ≤ Real.exp ‖s‖ := by
    apply Real.exp_le_exp.mpr
    rw [hnormw]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hd1 (norm_nonneg s)
  rw [xiHeatCassiniLogMeshLaplaceScaledDefectDerivative, norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  calc
    ‖(-((h : ℝ) : ℂ) * (Complex.exp w - 1 - w) +
        (d : ℂ) * (Complex.exp w - 1))‖ ≤
        ‖-((h : ℝ) : ℂ) * (Complex.exp w - 1 - w)‖ +
          ‖(d : ℂ) * (Complex.exp w - 1)‖ := norm_add_le _ _
    _ = h * ‖Complex.exp w - 1 - w‖ +
          d * ‖Complex.exp w - 1‖ := by
      rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hh0, abs_of_nonneg hd0]
    _ ≤ h * (‖w‖ ^ (2 : ℕ) * Real.exp ‖w‖) +
          d * (‖w‖ * Real.exp ‖w‖) := by gcongr
    _ = Real.exp ‖w‖ * d ^ (2 : ℕ) * (h * ‖s‖ ^ (2 : ℕ) + ‖s‖) := by
      rw [hnormw]
      ring
    _ ≤ Real.exp ‖s‖ * d ^ (2 : ℕ) * (h * ‖s‖ ^ (2 : ℕ) + ‖s‖) := by
      gcongr
    _ = _ := by rfl

/-- **Holomorphic mesh-defect theorem.**  Critical prime-gap energy gives locally normal
convergence, not just pointwise absolute convergence, throughout `-1/2 < Re s ≤ 0`.  The spare
abscissa between a compact neighborhood and the critical wall absorbs the derivative's one
log-height factor. -/
theorem analyticAt_xiHeatCassiniLogMeshLaplaceDefectSum_of_criticalEnergy
    {s0 : ℂ} (hsleft : -(1 / 2 : ℝ) < s0.re) (hsright : s0.re ≤ 0)
    (hcritical : Summable xiHeatCassiniPrimeGapCriticalEnergy) :
    AnalyticAt ℂ xiHeatCassiniLogMeshLaplaceDefectSum s0 := by
  let r : ℝ := (s0.re + 1 / 2) / 2
  have hr : 0 < r := by dsimp only [r]; linarith
  let a : ℝ := -s0.re + r
  have ha0 : 0 ≤ a := by dsimp only [a, r]; linarith
  have hahalf : a < 1 / 2 := by dsimp only [a, r]; linarith
  let b : ℝ := (a + 1 / 2) / 2
  have hb0 : 0 ≤ b := by dsimp only [b]; linarith
  have hab : a < b := by dsimp only [b]; linarith
  have hbhalf : b ≤ 1 / 2 := by dsimp only [b]; linarith
  let eps : ℝ := b - a
  have heps : 0 < eps := by dsimp only [eps]; linarith
  let B : ℝ := ‖s0‖ + r
  have hB0 : 0 ≤ B := by dsimp only [B]; positivity
  let K : ℝ := 4 / eps ^ (2 : ℕ) + 2
  have hK0 : 0 ≤ K := by dsimp only [K]; positivity
  let C : ℝ := Real.exp B * (B ^ (2 : ℕ) + B) * K
  have hC0 : 0 ≤ C := by dsimp only [C]; positivity
  let M : ℕ → ℝ := fun N => C * xiHeatCassiniPrimeGapAbscissaEnergy b N
  have hM : Summable M :=
    (summable_primeGapAbscissaEnergy_of_criticalEnergy hb0 hbhalf hcritical).mul_left C
  have hbaseNorm :=
    summable_norm_xiHeatCassiniLogMeshLaplaceScaledDefect_of_criticalEnergy
      hsleft.le hsright hcritical
  have hbase : Summable (fun N : ℕ =>
      xiHeatCassiniLogMeshLaplaceScaledDefect s0 N) := hbaseNorm.of_norm
  have hderiv : ∀ N : ℕ, ∀ s ∈ Metric.ball s0 r,
      HasDerivAt (fun z : ℂ => xiHeatCassiniLogMeshLaplaceScaledDefect z N)
        (xiHeatCassiniLogMeshLaplaceScaledDefectDerivative s N) s := by
    intro N s hs
    exact hasDerivAt_xiHeatCassiniLogMeshLaplaceScaledDefect s N
  have hbound : ∀ N : ℕ, ∀ s ∈ Metric.ball s0 r,
      ‖xiHeatCassiniLogMeshLaplaceScaledDefectDerivative s N‖ ≤ M N := by
    intro N s hs
    let d : ℝ := xiHeatCassiniOrderedPrimeLogGap N
    let h : ℝ := xiMassNthPrimeLogHeight (N + 1)
    let gapRatio : ℝ :=
      xiHeatCassiniOrderedPrimeGap N / (nthPrimeSubtype N : ℝ)
    have hd0 : 0 ≤ d := xiHeatCassiniOrderedPrimeLogGap_nonneg N
    have hh0 : 0 ≤ h := (xiMassNthPrimeLogHeight_pos (N + 1)).le
    have hratio0 : 0 ≤ gapRatio := by
      dsimp only [gapRatio]
      exact div_nonneg (xiHeatCassiniOrderedPrimeGap_nonneg N)
        (nthPrimeSubtype_pos N).le
    have hdle : d ≤ gapRatio := by
      simpa only [d, gapRatio] using
        xiHeatCassiniOrderedPrimeLogGap_le_gap_div_prime N
    have hdSq : d ^ (2 : ℕ) ≤ gapRatio ^ (2 : ℕ) :=
      (sq_le_sq₀ hd0 hratio0).mpr hdle
    have hdist : ‖s - s0‖ < r := by
      simpa only [Metric.mem_ball, Complex.dist_eq] using hs
    have hreabs : |s.re - s0.re| ≤ ‖s - s0‖ := by
      simpa only [Complex.sub_re] using Complex.abs_re_le_norm (s - s0)
    have hrediff : |s.re - s0.re| < r := lt_of_le_of_lt hreabs hdist
    have hsreLower : s0.re - r < s.re := by
      rw [abs_lt] at hrediff
      linarith
    have hnegRe : -s.re ≤ a := by dsimp only [a]; linarith
    have hsnorm : ‖s‖ ≤ B := by
      calc
        ‖s‖ = ‖(s - s0) + s0‖ := by ring_nf
        _ ≤ ‖s - s0‖ + ‖s0‖ := norm_add_le _ _
        _ ≤ B := by dsimp only [B]; linarith
    have hphase :
        ‖xiHeatCassiniOrderedPrimeLaplacePhase (N + 1) s‖ ≤
          Real.exp (a * h) := by
      rw [norm_xiHeatCassiniOrderedPrimeLaplacePhase]
      apply Real.exp_le_exp.mpr
      dsimp only [h]
      simpa only [neg_mul] using
        (mul_le_mul_of_nonneg_right hnegRe
          (xiMassNthPrimeLogHeight_pos (N + 1)).le)
    have hbracket : h * ‖s‖ ^ (2 : ℕ) + ‖s‖ ≤ (B ^ (2 : ℕ) + B) * (h + 1) := by
      have hsSq : ‖s‖ ^ (2 : ℕ) ≤ B ^ (2 : ℕ) := by gcongr
      calc
        h * ‖s‖ ^ (2 : ℕ) + ‖s‖ ≤ h * B ^ (2 : ℕ) + B := by gcongr
        _ ≤ (B ^ (2 : ℕ) + B) * (h + 1) := by
          nlinarith [mul_nonneg hB0 hh0, sq_nonneg B]
    have habsorb :
        (h + 1) * Real.exp (a * h) ≤ K * Real.exp (b * h) := by
      have hsquare := RHTower.Sieve.sq_mul_exp_neg_le_gen heps hh0
      have hexpone : Real.exp (-(eps * h)) ≤ 1 := by
        rw [← Real.exp_zero]
        apply Real.exp_le_exp.mpr
        exact neg_nonpos.mpr (mul_nonneg heps.le hh0)
      have hpoly : (h + 1) * Real.exp (-(eps * h)) ≤ K := by
        calc
          (h + 1) * Real.exp (-(eps * h)) ≤
              (h ^ (2 : ℕ) + 2) * Real.exp (-(eps * h)) := by
            apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
            nlinarith [sq_nonneg (h - 1 / 2)]
          _ = h ^ (2 : ℕ) * Real.exp (-(eps * h)) +
              2 * Real.exp (-(eps * h)) := by ring
          _ ≤ 4 / eps ^ (2 : ℕ) + 2 * 1 := by gcongr
          _ = K := by dsimp only [K]; ring
      have hexpSplit : Real.exp (a * h) =
          Real.exp (b * h) * Real.exp (-(eps * h)) := by
        rw [← Real.exp_add]
        congr 1
        dsimp only [eps]
        ring
      rw [hexpSplit]
      calc
        (h + 1) * (Real.exp (b * h) * Real.exp (-(eps * h))) =
            Real.exp (b * h) * ((h + 1) * Real.exp (-(eps * h))) := by ring
        _ ≤ Real.exp (b * h) * K :=
          mul_le_mul_of_nonneg_left hpoly (Real.exp_nonneg _)
        _ = K * Real.exp (b * h) := by ring
    calc
      ‖xiHeatCassiniLogMeshLaplaceScaledDefectDerivative s N‖ ≤
          ‖xiHeatCassiniOrderedPrimeLaplacePhase (N + 1) s‖ *
            (Real.exp ‖s‖ * d ^ (2 : ℕ) *
              (h * ‖s‖ ^ (2 : ℕ) + ‖s‖)) := by
        simpa only [d, h] using
          norm_xiHeatCassiniLogMeshLaplaceScaledDefectDerivative_le s N
      _ ≤ Real.exp (a * h) *
          (Real.exp B * gapRatio ^ (2 : ℕ) * ((B ^ (2 : ℕ) + B) * (h + 1))) := by
        gcongr
      _ = Real.exp B * (B ^ (2 : ℕ) + B) * gapRatio ^ (2 : ℕ) *
          ((h + 1) * Real.exp (a * h)) := by ring
      _ ≤ Real.exp B * (B ^ (2 : ℕ) + B) * gapRatio ^ (2 : ℕ) *
          (K * Real.exp (b * h)) := by gcongr
      _ = M N := by
        dsimp only [M, C, xiHeatCassiniPrimeGapAbscissaEnergy,
          gapRatio, h]
        ring
  rw [Complex.analyticAt_iff_eventually_differentiableAt]
  filter_upwards [Metric.ball_mem_nhds s0 hr] with s hs
  exact (hasDerivAt_tsum_of_isPreconnected hM Metric.isOpen_ball
    (convex_ball s0 r).isPreconnected hderiv hbound
    (Metric.mem_ball_self hr) hbase hs).differentiableAt

/-- Canonical resolvent continuation of the ordered logarithmic mesh. -/
def xiHeatCassiniLogMeshLaplaceContinuation (s : ℂ) : ℂ :=
  (xiHeatCassiniOrderedPrimeLaplacePhase 0 s -
      xiHeatCassiniLogMeshLaplaceDefectSum s) / s

/-- Critical energy also controls the defect series on the safe side of the wall. -/
theorem summable_norm_xiHeatCassiniLogMeshLaplaceScaledDefect_safe_of_criticalEnergy
    {s : ℂ} (hs : 0 < s.re)
    (hcritical : Summable xiHeatCassiniPrimeGapCriticalEnergy) :
    Summable (fun N : ℕ =>
      ‖xiHeatCassiniLogMeshLaplaceScaledDefect s N‖) := by
  have hzero : Summable (xiHeatCassiniPrimeGapAbscissaEnergy 0) :=
    summable_primeGapAbscissaEnergy_of_criticalEnergy (by norm_num) (by norm_num) hcritical
  have hneg : Summable (xiHeatCassiniPrimeGapAbscissaEnergy (-s.re)) := by
    refine Summable.of_nonneg_of_le
      (xiHeatCassiniPrimeGapAbscissaEnergy_nonneg (-s.re)) (fun N => ?_) hzero
    unfold xiHeatCassiniPrimeGapAbscissaEnergy
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    apply Real.exp_le_exp.mpr
    have hheight := xiMassNthPrimeLogHeight_pos (N + 1)
    nlinarith
  exact summable_norm_xiHeatCassiniLogMeshLaplaceScaledDefect_of_abscissaEnergy s hneg

/-- Every safe Laplace phase vanishes at the terminal prime. -/
theorem tendsto_xiHeatCassiniOrderedPrimeLaplacePhase_zero
    {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun N : ℕ => xiHeatCassiniOrderedPrimeLaplacePhase N s)
      atTop (𝓝 0) := by
  have hheight : Tendsto (fun N : ℕ => xiMassNthPrimeLogHeight N)
      atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp nthPrimeSubtype_strictMono.tendsto_atTop)
  have harg : Tendsto
      (fun N : ℕ => -(s.re * xiMassNthPrimeLogHeight N)) atTop atBot := by
    convert hheight.const_mul_atTop_of_neg (show -s.re < 0 by linarith) using 1
    funext N
    ring
  have hexp : Tendsto
      (fun N : ℕ => Real.exp (-(s.re * xiMassNthPrimeLogHeight N)))
      atTop (𝓝 0) := Real.tendsto_exp_atBot.comp harg
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa only [norm_xiHeatCassiniOrderedPrimeLaplacePhase] using hexp

/-- **Genuine continuation law.**  The resolvent formula is exactly the original absolutely
convergent mesh current on the safe half-plane. -/
theorem xiHeatCassiniLogMeshLaplaceContinuation_eq_current
    {s : ℂ} (hs : 0 < s.re)
    (hcritical : Summable xiHeatCassiniPrimeGapCriticalEnergy) :
    xiHeatCassiniLogMeshLaplaceContinuation s =
      xiHeatCassiniLogMeshLaplaceCurrent s := by
  have hdefNorm :=
    summable_norm_xiHeatCassiniLogMeshLaplaceScaledDefect_safe_of_criticalEnergy hs hcritical
  have hdef : Summable (fun N : ℕ =>
      xiHeatCassiniLogMeshLaplaceScaledDefect s N) := hdefNorm.of_norm
  have hdeflim := hdef.hasSum_iff_tendsto_nat.mp hdef.hasSum
  have hterminal := tendsto_xiHeatCassiniOrderedPrimeLaplacePhase_zero hs
  have hmesh := summable_xiHeatCassiniLogMeshLaplaceAtom hs
  have hmeshlim := hmesh.hasSum_iff_tendsto_nat.mp hmesh.hasSum
  have hconst : Tendsto
      (fun _ : ℕ => xiHeatCassiniOrderedPrimeLaplacePhase 0 s)
      atTop (𝓝 (xiHeatCassiniOrderedPrimeLaplacePhase 0 s)) :=
    tendsto_const_nhds
  have hright : Tendsto (fun N : ℕ =>
      xiHeatCassiniOrderedPrimeLaplacePhase 0 s -
        xiHeatCassiniOrderedPrimeLaplacePhase N s -
        s * ∑ n ∈ Finset.range N, xiHeatCassiniLogMeshLaplaceAtom s n)
      atTop
      (𝓝 (xiHeatCassiniOrderedPrimeLaplacePhase 0 s - 0 -
        s * xiHeatCassiniLogMeshLaplaceCurrent s)) := by
    exact (hconst.sub hterminal).sub
      (tendsto_const_nhds.mul (by
        simpa only [xiHeatCassiniLogMeshLaplaceCurrent] using hmeshlim))
  have hvalue : xiHeatCassiniLogMeshLaplaceDefectSum s =
      xiHeatCassiniOrderedPrimeLaplacePhase 0 s -
        s * xiHeatCassiniLogMeshLaplaceCurrent s := by
    have hright' : Tendsto (fun N : ℕ =>
        ∑ n ∈ Finset.range N,
          xiHeatCassiniLogMeshLaplaceScaledDefect s n)
        atTop
        (𝓝 (xiHeatCassiniOrderedPrimeLaplacePhase 0 s - 0 -
          s * xiHeatCassiniLogMeshLaplaceCurrent s)) := by
      apply hright.congr'
      filter_upwards with N
      exact (sum_xiHeatCassiniLogMeshLaplaceScaledDefect s N).symm
    have heq := tendsto_nhds_unique hdeflim hright'
    simpa only [xiHeatCassiniLogMeshLaplaceDefectSum, sub_zero] using heq
  rw [xiHeatCassiniLogMeshLaplaceContinuation, hvalue]
  have hs0 : s ≠ 0 := by
    intro hs0
    subst s
    norm_num at hs
  field_simp
  ring

/-- The continued mesh is holomorphic at every nonzero point of the open critical half-strip. -/
theorem analyticAt_xiHeatCassiniLogMeshLaplaceContinuation_of_criticalEnergy
    {s0 : ℂ} (hsleft : -(1 / 2 : ℝ) < s0.re) (hsright : s0.re ≤ 0)
    (hs0 : s0 ≠ 0)
    (hcritical : Summable xiHeatCassiniPrimeGapCriticalEnergy) :
    AnalyticAt ℂ xiHeatCassiniLogMeshLaplaceContinuation s0 := by
  have hphase : AnalyticAt ℂ
      (fun s : ℂ => xiHeatCassiniOrderedPrimeLaplacePhase 0 s) s0 := by
    simp only [xiHeatCassiniOrderedPrimeLaplacePhase,
      xiHeatCassiniOrderedPrimeComplexNegativePhase]
    fun_prop
  have hdef :=
    analyticAt_xiHeatCassiniLogMeshLaplaceDefectSum_of_criticalEnergy
      hsleft hsright hcritical
  unfold xiHeatCassiniLogMeshLaplaceContinuation
  exact (hphase.sub hdef).div analyticAt_id hs0

/-- Continuous regularity corollary for residue calculations. -/
theorem continuousAt_xiHeatCassiniLogMeshLaplaceContinuation_of_criticalEnergy
    {s0 : ℂ} (hsleft : -(1 / 2 : ℝ) < s0.re) (hsright : s0.re ≤ 0)
    (hs0 : s0 ≠ 0)
    (hcritical : Summable xiHeatCassiniPrimeGapCriticalEnergy) :
    ContinuousAt xiHeatCassiniLogMeshLaplaceContinuation s0 := by
  exact (analyticAt_xiHeatCassiniLogMeshLaplaceContinuation_of_criticalEnergy
    hsleft hsright hs0 hcritical).continuousAt

/-- Regularity forces zero residue at every nonzero candidate continuation point. -/
theorem xiHeatCassiniLogMeshLaplaceContinuation_zero_residue_of_criticalEnergy
    {s0 : ℂ} (hsleft : -(1 / 2 : ℝ) < s0.re) (hsright : s0.re ≤ 0)
    (hs0 : s0 ≠ 0)
    (hcritical : Summable xiHeatCassiniPrimeGapCriticalEnergy) :
    Tendsto (fun s : ℂ =>
      (s - s0) * xiHeatCassiniLogMeshLaplaceContinuation s)
      (𝓝[≠] s0) (𝓝 0) := by
  have hlinFull : Tendsto (fun s : ℂ => s - s0) (𝓝 s0) (𝓝 0) := by
    change Tendsto (id - fun _ : ℂ => s0) (𝓝 s0) (𝓝 0)
    simpa only [Pi.sub_apply, id_eq, sub_self] using
      (continuousAt_id.sub
        (continuousAt_const : ContinuousAt (fun _ : ℂ => s0) s0)).tendsto
  have hlin : Tendsto (fun s : ℂ => s - s0) (𝓝[≠] s0) (𝓝 0) :=
    hlinFull.mono_left nhdsWithin_le_nhds
  have hmesh : Tendsto xiHeatCassiniLogMeshLaplaceContinuation
      (𝓝[≠] s0) (𝓝 (xiHeatCassiniLogMeshLaplaceContinuation s0)) :=
    (continuousAt_xiHeatCassiniLogMeshLaplaceContinuation_of_criticalEnergy
      hsleft hsright hs0 hcritical).tendsto.mono_left nhdsWithin_le_nhds
  simpa using hlin.mul hmesh

/-- **Mesh noncompensation at an off-critical zero.**  Under critical gap energy, the continued
mesh has zero residue exactly where the Wold current has its nonzero first-shift pole. -/
theorem xiHeatCassiniLogMeshLaplaceContinuation_zero_residue_at_zetaPole_of_criticalEnergy
    {rho : ℂ} (hrho : 1 / 2 < rho.re)
    (hzeta : riemannZeta rho = 0)
    (hcritical : Summable xiHeatCassiniPrimeGapCriticalEnergy) :
    Tendsto (fun s : ℂ =>
      (s - (rho - 1)) * xiHeatCassiniLogMeshLaplaceContinuation s)
      (𝓝[≠] (rho - 1)) (𝓝 0) := by
  have hrhoOne : rho.re < 1 := riemannZeta_zero_re_lt_one hzeta
  apply xiHeatCassiniLogMeshLaplaceContinuation_zero_residue_of_criticalEnergy
  · simpa using (show -(1 / 2 : ℝ) < rho.re - 1 by linarith)
  · simpa using (show rho.re - 1 ≤ 0 by linarith)
  · intro hzero
    have hre := congrArg Complex.re hzero
    norm_num at hre
    linarith
  · exact hcritical

end

end RHTower
