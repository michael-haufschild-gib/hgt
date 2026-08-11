import GaloisForLFunctions.RHTower.XiHeatCassiniWoldLowerHalfShiftGevreyKernel

/-!
# Hardy polarization of the Route-T Wold residual source

The physical residual edge kernel has only negative Fourier phases.  Its real-boundary
`C^∞` regularity therefore has a stronger one-sided complex form: the whole edge series extends
holomorphically to the open lower half-plane.  The adjacent-prime chord retains one prime-log gap
there, and every phase has norm at most one.  Consequently the extension grows at most linearly;
after division by the source coordinate it is a bounded holomorphic lower-half-plane carrier.

This does not cross the forbidden upper half-shift.  It identifies its exact orientation: all
analytic wavefront obstruction is on the upper side, while the lower side is an unconditional
Hardy carrier controlled by the already-proved prime-log total variation.
-/

open Complex Filter Set Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Complex negative-frequency character on the ordered prime-log mesh. -/
def xiHeatCassiniOrderedPrimeComplexNegativePhase (N : ℕ) (z : ℂ) : ℂ :=
  Complex.exp (-(Complex.I * (xiMassNthPrimeLogHeight N : ℂ) * z))

@[simp]
theorem xiHeatCassiniOrderedPrimeComplexNegativePhase_ofReal
    (N : ℕ) (x : ℝ) :
    xiHeatCassiniOrderedPrimeComplexNegativePhase N (x : ℂ) =
      xiHeatCassiniOrderedPrimeNegativePhase N x := by
  rfl

/-- Every negative prime phase is contractive on the closed lower half-plane. -/
theorem norm_xiHeatCassiniOrderedPrimeComplexNegativePhase_le_one
    (N : ℕ) {z : ℂ} (hz : z.im ≤ 0) :
    ‖xiHeatCassiniOrderedPrimeComplexNegativePhase N z‖ ≤ 1 := by
  rw [xiHeatCassiniOrderedPrimeComplexNegativePhase, Complex.norm_exp]
  have hh : 0 ≤ xiMassNthPrimeLogHeight N :=
    (xiMassNthPrimeLogHeight_pos N).le
  have hre :
      (-(Complex.I * (xiMassNthPrimeLogHeight N : ℂ) * z)).re =
        xiMassNthPrimeLogHeight N * z.im := by
    simp [Complex.mul_re]
  rw [hre, ← Real.exp_zero]
  exact Real.exp_le_exp.mpr (mul_nonpos_of_nonneg_of_nonpos hh hz)

/-- The complex phase chord keeps one full prime-log gap on the lower half-plane. -/
theorem norm_xiHeatCassiniOrderedPrimeComplexNegativePhase_sub_succ_le
    {z : ℂ} (hz : z.im ≤ 0) (N : ℕ) :
    ‖xiHeatCassiniOrderedPrimeComplexNegativePhase N z -
        xiHeatCassiniOrderedPrimeComplexNegativePhase (N + 1) z‖ ≤
      2 * xiHeatCassiniOrderedPrimeLogGap N * ‖z‖ := by
  let h : ℝ := xiMassNthPrimeLogHeight N
  let s : ℝ := xiMassNthPrimeLogHeight (N + 1)
  let delta : ℝ := xiHeatCassiniOrderedPrimeLogGap N
  let w : ℂ := -(Complex.I * (delta : ℂ) * z)
  have hdelta : 0 ≤ delta := xiHeatCassiniOrderedPrimeLogGap_nonneg N
  have hphase :
      xiHeatCassiniOrderedPrimeComplexNegativePhase (N + 1) z =
        xiHeatCassiniOrderedPrimeComplexNegativePhase N z * Complex.exp w := by
    rw [xiHeatCassiniOrderedPrimeComplexNegativePhase,
      xiHeatCassiniOrderedPrimeComplexNegativePhase, ← Complex.exp_add]
    dsimp only [h, s, delta, w, xiHeatCassiniOrderedPrimeLogGap]
    congr 1
    push_cast
    ring
  have hwre : w.re = delta * z.im := by
    dsimp only [w]
    simp [Complex.mul_re]
  have hexpw : ‖Complex.exp w‖ ≤ 1 := by
    rw [Complex.norm_exp, ← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by rw [hwre]; exact mul_nonpos_of_nonneg_of_nonpos hdelta hz)
  have hwnorm : ‖w‖ = delta * ‖z‖ := by
    dsimp only [w]
    rw [norm_neg, norm_mul, norm_mul, Complex.norm_I, one_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hdelta]
  have hunit : ‖1 - Complex.exp w‖ ≤ 2 * ‖w‖ := by
    by_cases hsmall : ‖w‖ ≤ 1
    · have h := Complex.norm_exp_sub_one_le hsmall
      rw [← norm_neg (Complex.exp w - 1), neg_sub] at h
      exact h
    · have htwo : (2 : ℝ) ≤ 2 * ‖w‖ := by
        have : 1 ≤ ‖w‖ := le_of_lt (lt_of_not_ge hsmall)
        linarith
      exact (norm_sub_le _ _).trans <| by
        rw [norm_one]
        linarith
  rw [hphase]
  calc
    ‖xiHeatCassiniOrderedPrimeComplexNegativePhase N z -
        xiHeatCassiniOrderedPrimeComplexNegativePhase N z * Complex.exp w‖ =
        ‖xiHeatCassiniOrderedPrimeComplexNegativePhase N z *
          (1 - Complex.exp w)‖ := by congr 1 <;> ring
    _ = ‖xiHeatCassiniOrderedPrimeComplexNegativePhase N z‖ *
          ‖1 - Complex.exp w‖ := norm_mul _ _
    _ ≤ 1 * (2 * ‖w‖) := mul_le_mul
      (norm_xiHeatCassiniOrderedPrimeComplexNegativePhase_le_one N hz)
      hunit (norm_nonneg _) zero_le_one
    _ = 2 * xiHeatCassiniOrderedPrimeLogGap N * ‖z‖ := by
      rw [hwnorm]
      dsimp only [delta]
      ring

/-- One complexified residual phase edge. -/
def xiHeatCassiniWoldResidualComplexPhaseConnectionAtom
    (z : ℂ) (N : ℕ) : ℂ :=
  (xiHeatCassiniOrderedWoldResidualLogDiscrepancy N : ℂ) *
    (xiHeatCassiniOrderedPrimeComplexNegativePhase N z -
      xiHeatCassiniOrderedPrimeComplexNegativePhase (N + 1) z)

/-- Complex derivative of one residual phase edge. -/
def xiHeatCassiniWoldResidualComplexPhaseConnectionDerivAtom
    (z : ℂ) (N : ℕ) : ℂ :=
  (xiHeatCassiniOrderedWoldResidualLogDiscrepancy N : ℂ) *
    ((-Complex.I * (xiMassNthPrimeLogHeight N : ℂ)) *
        xiHeatCassiniOrderedPrimeComplexNegativePhase N z -
      (-Complex.I * (xiMassNthPrimeLogHeight (N + 1) : ℂ)) *
        xiHeatCassiniOrderedPrimeComplexNegativePhase (N + 1) z)

@[simp]
theorem xiHeatCassiniWoldResidualComplexPhaseConnectionAtom_ofReal
    (x : ℝ) (N : ℕ) :
    xiHeatCassiniWoldResidualComplexPhaseConnectionAtom (x : ℂ) N =
      xiHeatCassiniWoldResidualLowerHalfPhaseConnectionAtom x N := by
  simp [xiHeatCassiniWoldResidualComplexPhaseConnectionAtom,
    xiHeatCassiniWoldResidualLowerHalfPhaseConnectionAtom]

theorem hasDerivAt_xiHeatCassiniOrderedPrimeComplexNegativePhase
    (N : ℕ) (z : ℂ) :
    HasDerivAt (xiHeatCassiniOrderedPrimeComplexNegativePhase N)
      ((-Complex.I * (xiMassNthPrimeLogHeight N : ℂ)) *
        xiHeatCassiniOrderedPrimeComplexNegativePhase N z) z := by
  unfold xiHeatCassiniOrderedPrimeComplexNegativePhase
  let c : ℂ := -Complex.I * (xiMassNthPrimeLogHeight N : ℂ)
  have hfun :
      (fun w : ℂ => Complex.exp
        (-(Complex.I * (xiMassNthPrimeLogHeight N : ℂ) * w))) =
        fun w : ℂ => Complex.exp (c * w) := by
    funext w
    congr 1
    dsimp only [c]
    ring
  have h := ((hasDerivAt_id z).const_mul c).cexp
  have h' : HasDerivAt (fun w : ℂ => Complex.exp (c * w))
      (c * Complex.exp (c * z)) z := by
    apply h.congr_deriv
    simp only [id_eq, mul_one]
    ring
  rw [hfun]
  convert h' using 1
  dsimp only [c]
  congr 1
  ring

theorem hasDerivAt_xiHeatCassiniWoldResidualComplexPhaseConnectionAtom
    (N : ℕ) (z : ℂ) :
    HasDerivAt (xiHeatCassiniWoldResidualComplexPhaseConnectionAtom · N)
      (xiHeatCassiniWoldResidualComplexPhaseConnectionDerivAtom z N) z := by
  exact ((hasDerivAt_xiHeatCassiniOrderedPrimeComplexNegativePhase N z).sub
    (hasDerivAt_xiHeatCassiniOrderedPrimeComplexNegativePhase (N + 1) z)).const_mul _

theorem norm_xiHeatCassiniWoldResidualComplexPhaseConnectionAtom_le
    {z : ℂ} (hz : z.im ≤ 0) (N : ℕ) :
    ‖xiHeatCassiniWoldResidualComplexPhaseConnectionAtom z N‖ ≤
      2 * ‖z‖ *
        (|xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| *
          xiHeatCassiniOrderedPrimeLogGap N) := by
  rw [xiHeatCassiniWoldResidualComplexPhaseConnectionAtom, norm_mul,
    Complex.norm_real, Real.norm_eq_abs]
  have h := norm_xiHeatCassiniOrderedPrimeComplexNegativePhase_sub_succ_le hz N
  calc
    |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| *
        ‖xiHeatCassiniOrderedPrimeComplexNegativePhase N z -
          xiHeatCassiniOrderedPrimeComplexNegativePhase (N + 1) z‖ ≤
      |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| *
        (2 * xiHeatCassiniOrderedPrimeLogGap N * ‖z‖) :=
      mul_le_mul_of_nonneg_left h (abs_nonneg _)
    _ = _ := by ring

/-- Derivative atoms retain the same edge gap, with one prime-log moment. -/
theorem norm_xiHeatCassiniWoldResidualComplexPhaseConnectionDerivAtom_le
    {z : ℂ} (hz : z.im ≤ 0) (N : ℕ) :
    ‖xiHeatCassiniWoldResidualComplexPhaseConnectionDerivAtom z N‖ ≤
      |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| *
        xiHeatCassiniOrderedPrimeLogGap N *
          (2 * xiMassNthPrimeLogHeight (N + 1) * ‖z‖ + 1) := by
  let h : ℝ := xiMassNthPrimeLogHeight N
  let s : ℝ := xiMassNthPrimeLogHeight (N + 1)
  let A : ℂ := -Complex.I * (h : ℂ)
  let B : ℂ := -Complex.I * (s : ℂ)
  let pn : ℂ := xiHeatCassiniOrderedPrimeComplexNegativePhase N z
  let ps : ℂ := xiHeatCassiniOrderedPrimeComplexNegativePhase (N + 1) z
  have hh : 0 ≤ h := (xiMassNthPrimeLogHeight_pos N).le
  have hs : 0 ≤ s := (xiMassNthPrimeLogHeight_pos (N + 1)).le
  have hle : h ≤ s :=
    nthPrimeSubtype_log_strictMono.monotone (Nat.le_succ N)
  have hpn : ‖pn‖ ≤ 1 := by
    simpa only [pn] using
      norm_xiHeatCassiniOrderedPrimeComplexNegativePhase_le_one N hz
  have hps : ‖ps‖ ≤ 1 := by
    simpa only [ps] using
      norm_xiHeatCassiniOrderedPrimeComplexNegativePhase_le_one (N + 1) hz
  have hAnorm : ‖A‖ = h := by simp [A, abs_of_nonneg hh]
  have hABnorm : ‖A - B‖ = xiHeatCassiniOrderedPrimeLogGap N := by
    calc
      ‖A - B‖ = ‖Complex.I * ((s - h : ℝ) : ℂ)‖ := by
        congr 1
        dsimp only [A, B]
        push_cast
        ring
      _ = |s - h| := by
        rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
      _ = s - h := by rw [abs_of_nonneg (sub_nonneg.mpr hle)]
      _ = xiHeatCassiniOrderedPrimeLogGap N := by
        rfl
  have hchord : ‖pn - ps‖ ≤
      2 * xiHeatCassiniOrderedPrimeLogGap N * ‖z‖ := by
    simpa only [pn, ps] using
      norm_xiHeatCassiniOrderedPrimeComplexNegativePhase_sub_succ_le hz N
  rw [xiHeatCassiniWoldResidualComplexPhaseConnectionDerivAtom, norm_mul,
    Complex.norm_real, Real.norm_eq_abs]
  change |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| *
      ‖A * pn - B * ps‖ ≤ _
  have hinner : ‖A * pn - B * ps‖ ≤
      xiHeatCassiniOrderedPrimeLogGap N * (2 * s * ‖z‖ + 1) := by
    calc
      ‖A * pn - B * ps‖ = ‖A * (pn - ps) + (A - B) * ps‖ := by
        congr 1
        ring
      _ ≤ ‖A * (pn - ps)‖ + ‖(A - B) * ps‖ := norm_add_le _ _
      _ = h * ‖pn - ps‖ +
          xiHeatCassiniOrderedPrimeLogGap N * ‖ps‖ := by
        simp only [norm_mul, hAnorm, hABnorm]
      _ ≤ h * (2 * xiHeatCassiniOrderedPrimeLogGap N * ‖z‖) +
          xiHeatCassiniOrderedPrimeLogGap N * 1 := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hchord hh)
          (mul_le_mul_of_nonneg_left hps
            (xiHeatCassiniOrderedPrimeLogGap_nonneg N))
      _ ≤ s * (2 * xiHeatCassiniOrderedPrimeLogGap N * ‖z‖) +
          xiHeatCassiniOrderedPrimeLogGap N * 1 := by
        exact add_le_add
          (mul_le_mul_of_nonneg_right hle
            (mul_nonneg
              (mul_nonneg (by norm_num)
                (xiHeatCassiniOrderedPrimeLogGap_nonneg N))
              (norm_nonneg z))) le_rfl
      _ = xiHeatCassiniOrderedPrimeLogGap N * (2 * s * ‖z‖ + 1) := by ring
  calc
    |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| * ‖A * pn - B * ps‖ ≤
        |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| *
          (xiHeatCassiniOrderedPrimeLogGap N * (2 * s * ‖z‖ + 1)) :=
      mul_le_mul_of_nonneg_left hinner (abs_nonneg _)
    _ = _ := by dsimp only [s]; ring

theorem summable_xiHeatCassiniWoldResidualComplexPhaseConnectionAtom
    {z : ℂ} (hz : z.im ≤ 0) :
    Summable (xiHeatCassiniWoldResidualComplexPhaseConnectionAtom z) := by
  have hmajor :=
    summable_abs_xiHeatCassiniOrderedWoldResidual_mul_primeLogGap.mul_left
      (2 * ‖z‖)
  apply hmajor.of_norm_bounded
  intro N
  simpa only [mul_assoc] using
    norm_xiHeatCassiniWoldResidualComplexPhaseConnectionAtom_le hz N

theorem summable_xiHeatCassiniWoldResidualComplexPhaseConnectionDerivAtom
    {z : ℂ} (hz : z.im ≤ 0) :
    Summable (xiHeatCassiniWoldResidualComplexPhaseConnectionDerivAtom z) := by
  have hmajor :=
    ((summable_xiHeatCassiniWoldResidual_primeLogMoment_mul_gap 1).mul_left
      (2 * ‖z‖)).add
      summable_abs_xiHeatCassiniOrderedWoldResidual_mul_primeLogGap
  apply hmajor.of_norm_bounded
  intro N
  have h :=
    norm_xiHeatCassiniWoldResidualComplexPhaseConnectionDerivAtom_le hz N
  simpa [pow_one] using h.trans_eq (by ring)

/-- Holomorphic candidate obtained by summing every complex residual edge. -/
def xiHeatCassiniWoldResidualLowerHardyKernel (z : ℂ) : ℂ :=
  ∑' N : ℕ, xiHeatCassiniWoldResidualComplexPhaseConnectionAtom z N

@[simp]
theorem xiHeatCassiniWoldResidualLowerHardyKernel_ofReal (x : ℝ) :
    xiHeatCassiniWoldResidualLowerHardyKernel (x : ℂ) =
      xiHeatCassiniWoldResidualLowerHalfPhaseKernelLimit x := by
  simp [xiHeatCassiniWoldResidualLowerHardyKernel,
    xiHeatCassiniWoldResidualLowerHalfPhaseKernelLimit]

/-- The residual edge sum is complex differentiable at every strictly lower-half-plane point. -/
theorem hasDerivAt_xiHeatCassiniWoldResidualLowerHardyKernel
    {z : ℂ} (hz : z.im < 0) :
    HasDerivAt xiHeatCassiniWoldResidualLowerHardyKernel
      (∑' N : ℕ, xiHeatCassiniWoldResidualComplexPhaseConnectionDerivAtom z N) z := by
  let r : ℝ := -z.im / 2
  let M : ℕ → ℝ := fun N =>
    |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| *
      xiHeatCassiniOrderedPrimeLogGap N *
        (2 * xiMassNthPrimeLogHeight (N + 1) * (‖z‖ + r) + 1)
  have hr : 0 < r := by dsimp only [r]; linarith
  have hM : Summable M := by
    have hmajor :=
      ((summable_xiHeatCassiniWoldResidual_primeLogMoment_mul_gap 1).mul_left
        (2 * (‖z‖ + r))).add
        summable_abs_xiHeatCassiniOrderedWoldResidual_mul_primeLogGap
    exact hmajor.congr fun N => by dsimp only [M]; simp only [pow_one]; ring
  have hzball : z ∈ Metric.ball z r := Metric.mem_ball_self hr
  have hmain := hasDerivAt_tsum_of_isPreconnected
    (u := M) (t := Metric.ball z r)
    (g := fun N w => xiHeatCassiniWoldResidualComplexPhaseConnectionAtom w N)
    (g' := fun N w => xiHeatCassiniWoldResidualComplexPhaseConnectionDerivAtom w N)
    (y₀ := z) (y := z) hM Metric.isOpen_ball (convex_ball z r).isPreconnected
    (fun N w _ => hasDerivAt_xiHeatCassiniWoldResidualComplexPhaseConnectionAtom N w)
    (fun N w hw => by
      have hwsub : ‖w - z‖ < r := by simpa [Metric.mem_ball, dist_eq] using hw
      have hwim : w.im ≤ 0 := by
        have him : |w.im - z.im| ≤ ‖w - z‖ := by
          rw [← Complex.sub_im]
          exact Complex.abs_im_le_norm _
        have : w.im - z.im < r := lt_of_le_of_lt (le_abs_self _) (him.trans_lt hwsub)
        dsimp only [r] at this
        linarith
      have hwnorm : ‖w‖ ≤ ‖z‖ + r := by
        calc
          ‖w‖ ≤ ‖w - z‖ + ‖z‖ := by
            simpa only [sub_add_cancel] using norm_add_le (w - z) z
          _ ≤ ‖z‖ + r := by linarith
      have hraw :=
        norm_xiHeatCassiniWoldResidualComplexPhaseConnectionDerivAtom_le hwim N
      apply hraw.trans
      dsimp only [M]
      exact mul_le_mul_of_nonneg_left
        (add_le_add
          (mul_le_mul_of_nonneg_left hwnorm
            (mul_nonneg (by positivity)
              (xiMassNthPrimeLogHeight_pos (N + 1)).le))
          le_rfl)
        (mul_nonneg (abs_nonneg _)
          (xiHeatCassiniOrderedPrimeLogGap_nonneg N)))
    hzball
    (summable_xiHeatCassiniWoldResidualComplexPhaseConnectionAtom hz.le)
    hzball
  change HasDerivAt
    (fun w : ℂ => ∑' N : ℕ,
      xiHeatCassiniWoldResidualComplexPhaseConnectionAtom w N)
    (∑' N : ℕ, xiHeatCassiniWoldResidualComplexPhaseConnectionDerivAtom z N) z
  exact hmain

/-- **One-sided analytic-wavefront theorem.**  Residual source is holomorphic on whole open lower
half-plane. -/
theorem analyticOnNhd_xiHeatCassiniWoldResidualLowerHardyKernel :
    AnalyticOnNhd ℂ xiHeatCassiniWoldResidualLowerHardyKernel {z : ℂ | z.im < 0} := by
  have hopen : IsOpen {z : ℂ | z.im < 0} :=
    isOpen_lt Complex.continuous_im continuous_const
  apply DifferentiableOn.analyticOnNhd _ hopen
  intro z hz
  exact (hasDerivAt_xiHeatCassiniWoldResidualLowerHardyKernel hz).differentiableAt.differentiableWithinAt

/-- Total prime-log variation controlling the one-sided Hardy carrier. -/
def xiHeatCassiniWoldResidualPrimeLogTotalVariation : ℝ :=
  ∑' N : ℕ,
    |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| *
      xiHeatCassiniOrderedPrimeLogGap N

theorem xiHeatCassiniWoldResidualPrimeLogTotalVariation_nonneg :
    0 ≤ xiHeatCassiniWoldResidualPrimeLogTotalVariation := by
  exact tsum_nonneg fun N => mul_nonneg (abs_nonneg _)
    (xiHeatCassiniOrderedPrimeLogGap_nonneg N)

/-- Global linear-growth bound on the entire closed lower half-plane. -/
theorem norm_xiHeatCassiniWoldResidualLowerHardyKernel_le
    {z : ℂ} (hz : z.im ≤ 0) :
    ‖xiHeatCassiniWoldResidualLowerHardyKernel z‖ ≤
      2 * xiHeatCassiniWoldResidualPrimeLogTotalVariation * ‖z‖ := by
  have hs := summable_xiHeatCassiniWoldResidualComplexPhaseConnectionAtom hz
  calc
    ‖xiHeatCassiniWoldResidualLowerHardyKernel z‖ ≤
        ∑' N : ℕ, ‖xiHeatCassiniWoldResidualComplexPhaseConnectionAtom z N‖ :=
      norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' N : ℕ, 2 * ‖z‖ *
        (|xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| *
          xiHeatCassiniOrderedPrimeLogGap N) :=
      hs.norm.tsum_le_tsum
        (fun N => norm_xiHeatCassiniWoldResidualComplexPhaseConnectionAtom_le hz N)
        (summable_abs_xiHeatCassiniOrderedWoldResidual_mul_primeLogGap.mul_left
          (2 * ‖z‖))
    _ = 2 * xiHeatCassiniWoldResidualPrimeLogTotalVariation * ‖z‖ := by
      rw [xiHeatCassiniWoldResidualPrimeLogTotalVariation]
      calc
        (∑' N : ℕ, 2 * ‖z‖ *
          (|xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| *
            xiHeatCassiniOrderedPrimeLogGap N)) =
            2 * ‖z‖ * (∑' N : ℕ,
              |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| *
                xiHeatCassiniOrderedPrimeLogGap N) := by rw [tsum_mul_left]
        _ = _ := by ring

/-- Coordinate-divided residual carrier.  Zero lies on boundary, so denominator never vanishes
inside open lower half-plane. -/
def xiHeatCassiniWoldResidualLowerHardyQuotient (z : ℂ) : ℂ :=
  xiHeatCassiniWoldResidualLowerHardyKernel z / z

/-- The divided carrier is globally bounded on open lower half-plane. -/
theorem norm_xiHeatCassiniWoldResidualLowerHardyQuotient_le
    {z : ℂ} (hz : z.im < 0) :
    ‖xiHeatCassiniWoldResidualLowerHardyQuotient z‖ ≤
      2 * xiHeatCassiniWoldResidualPrimeLogTotalVariation := by
  have hz0 : z ≠ 0 := by
    intro hzero
    rw [hzero] at hz
    simp at hz
  rw [xiHeatCassiniWoldResidualLowerHardyQuotient, norm_div]
  have h := norm_xiHeatCassiniWoldResidualLowerHardyKernel_le hz.le
  rw [div_le_iff₀ (norm_pos_iff.mpr hz0)]
  exact h.trans_eq (by ring)

end

end RHTower
