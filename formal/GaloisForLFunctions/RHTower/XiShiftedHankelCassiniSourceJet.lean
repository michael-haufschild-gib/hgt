import GaloisForLFunctions.HTGeometry.IteratedDerivTranslate
import GaloisForLFunctions.RHTower.XiShiftedHankelBoundaryPadeContactParity

/-!
# Moving Cassini-source jets for every shifted Xi moment

The shift-one Cassini source does not merely remember the collision pattern of shifted Xi nodes.
At every positive mass `y`, its logarithmic derivative at the real center `1 - y` has the complete
shifted reciprocal-moment tower as its Taylor jet.  Thus the adaptive Route-U Hankel form is a jet
form of one fixed entire function; no phase-changing transport of a quadratic form is required.
-/

open Complex Filter Matrix Topology
open scoped ENNReal NNReal

namespace RHTower

noncomputable section

/-- Local ordinary moment series of the Xi reciprocal-square atoms at mass `y`. -/
def xiShiftedCassiniMomentPowerSeries (y : ℝ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (xiShiftedReciprocalMoment y)

/-- Local ordinary moment germ of the Xi reciprocal-square atoms at mass `y`. -/
def xiShiftedCassiniMomentGerm (y : ℝ) : ℂ → ℂ :=
  (xiShiftedCassiniMomentPowerSeries y).sum

theorem xiShiftedCassiniMomentGerm_eq_tsum (y : ℝ) (u : ℂ) :
    xiShiftedCassiniMomentGerm y u =
      ∑' n : ℕ, xiShiftedReciprocalMoment y n * u ^ n := by
  rw [xiShiftedCassiniMomentGerm, xiShiftedCassiniMomentPowerSeries]
  change FormalMultilinearSeries.ofScalarsSum
    (xiShiftedReciprocalMoment y) u = _
  rw [FormalMultilinearSeries.ofScalars_sum_eq]
  simp only [smul_eq_mul]

theorem norm_xiShiftedReciprocalMoment_le_absoluteMass
    {y : ℝ} (hy : 0 ≤ y) (n : ℕ) :
    ‖xiShiftedReciprocalMoment y n‖ ≤
      ∑' q : XiZeroCopy, ‖xiShiftedReciprocalSquare y q‖ := by
  rw [xiShiftedReciprocalMoment]
  calc
    ‖∑' q : XiZeroCopy, xiShiftedReciprocalSquare y q ^ (n + 1)‖ ≤
        ∑' q : XiZeroCopy, ‖xiShiftedReciprocalSquare y q ^ (n + 1)‖ :=
      norm_tsum_le_tsum_norm (summable_xiShiftedReciprocalSquare_pow hy n).norm
    _ ≤ ∑' q : XiZeroCopy,
        ‖xiShiftedReciprocalSquare y q ^ (0 + 1)‖ := by
      apply Summable.tsum_mono
        (summable_xiShiftedReciprocalSquare_pow hy n).norm
        (summable_xiShiftedReciprocalSquare_pow hy 0).norm
      intro q
      change ‖xiShiftedReciprocalSquare y q ^ (n + 1)‖ ≤
        ‖xiShiftedReciprocalSquare y q ^ (0 + 1)‖
      rw [norm_pow, pow_succ]
      have hsmall : (2 / 41 : ℝ) ≤ 1 := by norm_num
      have hpow : ‖xiShiftedReciprocalSquare y q‖ ^ n ≤ (1 : ℝ) :=
        pow_le_one₀ (norm_nonneg _)
          ((norm_xiShiftedReciprocalSquare_le hy q).trans
            ((norm_xiZeroCopyReciprocalSquare_lt_two_over_fortyOne q).le.trans
              hsmall))
      simpa using mul_le_mul_of_nonneg_right hpow
        (norm_nonneg (xiShiftedReciprocalSquare y q))
    _ = ∑' q : XiZeroCopy, ‖xiShiftedReciprocalSquare y q‖ := by
      congr 1
      funext q
      simp

theorem xiShiftedCassiniMomentPowerSeries_radius_pos
    {y : ℝ} (hy : 0 ≤ y) :
    0 < (xiShiftedCassiniMomentPowerSeries y).radius := by
  let r : ℝ≥0 := ⟨1 / 2, by norm_num⟩
  let S : ℝ := ∑' q : XiZeroCopy, ‖xiShiftedReciprocalSquare y q‖
  have hrad : (r : ℝ≥0∞) ≤ (xiShiftedCassiniMomentPowerSeries y).radius := by
    apply FormalMultilinearSeries.le_radius_of_bound
      (p := xiShiftedCassiniMomentPowerSeries y) S
    intro n
    rw [xiShiftedCassiniMomentPowerSeries,
      FormalMultilinearSeries.ofScalars_norm]
    change ‖xiShiftedReciprocalMoment y n‖ * (1 / 2 : ℝ) ^ n ≤ S
    calc
      ‖xiShiftedReciprocalMoment y n‖ * (1 / 2 : ℝ) ^ n ≤
          S * (1 / 2 : ℝ) ^ n := by
        gcongr
        exact norm_xiShiftedReciprocalMoment_le_absoluteMass hy n
      _ ≤ S := by
        exact mul_le_of_le_one_right
          (tsum_nonneg fun _ => norm_nonneg _)
          (pow_le_one₀ (by norm_num) (by norm_num))
  have hrpos : 0 < r := by
    apply NNReal.coe_pos.mp
    change (0 : ℝ) < 1 / 2
    norm_num
  exact (ENNReal.coe_pos.mpr hrpos).trans_le hrad

theorem analyticAt_xiShiftedCassiniMomentGerm
    {y : ℝ} (hy : 0 ≤ y) :
    AnalyticAt ℂ (xiShiftedCassiniMomentGerm y) 0 := by
  exact ⟨xiShiftedCassiniMomentPowerSeries y,
    (xiShiftedCassiniMomentPowerSeries y).hasFPowerSeriesOnBall
      (xiShiftedCassiniMomentPowerSeries_radius_pos hy) |>.hasFPowerSeriesAt⟩

theorem iteratedDeriv_xiShiftedCassiniMomentGerm
    {y : ℝ} (hy : 0 ≤ y) (n : ℕ) :
    iteratedDeriv n (xiShiftedCassiniMomentGerm y) 0 =
      ((n.factorial : ℕ) : ℂ) * xiShiftedReciprocalMoment y n := by
  have hp := (xiShiftedCassiniMomentPowerSeries y).hasFPowerSeriesOnBall
    (xiShiftedCassiniMomentPowerSeries_radius_pos hy)
  have hfac := hp.factorial_smul (1 : ℂ) n
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod,
    Finset.prod_const_one, one_smul] at hfac
  rw [xiShiftedCassiniMomentPowerSeries,
    FormalMultilinearSeries.ofScalars_apply_eq, one_pow, smul_eq_mul,
    mul_one] at hfac
  simpa only [xiShiftedCassiniMomentGerm,
    xiShiftedCassiniMomentPowerSeries, nsmul_eq_mul] using hfac.symm

theorem xiShiftedCassiniMomentGerm_eq_resolvent
    {y : ℝ} (hy : 0 ≤ y) {u : ℂ} (hu : ‖u‖ < 1) :
    xiShiftedCassiniMomentGerm y u =
      ∑' q : XiZeroCopy,
        xiShiftedReciprocalSquare y q /
          (1 - u * xiShiftedReciprocalSquare y q) := by
  let mu : XiZeroCopy → ℂ := xiShiftedReciprocalSquare y
  have hmu : Summable (fun q => ‖mu q‖) := by
    simpa only [mu, zero_add, pow_one] using
      (summable_xiShiftedReciprocalSquare_pow hy 0).norm
  have hgeom : Summable (fun n : ℕ => ‖u‖ ^ n) :=
    summable_geometric_of_lt_one (norm_nonneg u) hu
  have hboundTerm : ∀ (n : ℕ) (q : XiZeroCopy),
      ‖u ^ n * mu q ^ (n + 1)‖ ≤ ‖u‖ ^ n * ‖mu q‖ := by
    intro n q
    rw [norm_mul, norm_pow, pow_succ, norm_mul, norm_pow]
    have hmuPow : ‖mu q‖ ^ n ≤ 1 :=
      pow_le_one₀ (norm_nonneg _)
        ((norm_xiShiftedReciprocalSquare_le hy q).trans
          ((norm_xiZeroCopyReciprocalSquare_lt_two_over_fortyOne q).le.trans
            (by norm_num)))
    calc
      ‖u‖ ^ n * (‖mu q‖ ^ n * ‖mu q‖) ≤
          ‖u‖ ^ n * (1 * ‖mu q‖) := by gcongr
      _ = ‖u‖ ^ n * ‖mu q‖ := by ring
  have hnorm : Summable (fun p : ℕ × XiZeroCopy =>
      ‖u‖ ^ p.1 * ‖mu p.2‖) := by
    rw [summable_prod_of_nonneg
      (fun p => mul_nonneg (pow_nonneg (norm_nonneg _) _) (norm_nonneg _))]
    constructor
    · intro n
      exact hmu.mul_left (‖u‖ ^ n)
    · apply Summable.of_nonneg_of_le
        (fun n => tsum_nonneg fun _ =>
          mul_nonneg (pow_nonneg (norm_nonneg _) _) (norm_nonneg _))
        (fun n => le_rfl)
      exact (hgeom.mul_right (∑' q : XiZeroCopy, ‖mu q‖)).congr
        fun n => tsum_mul_left.symm
  have huncurry : Summable (Function.uncurry
      (fun (n : ℕ) (q : XiZeroCopy) => u ^ n * mu q ^ (n + 1))) := by
    apply Summable.of_norm_bounded hnorm
    intro p
    exact hboundTerm p.1 p.2
  rw [xiShiftedCassiniMomentGerm_eq_tsum]
  have hstep : ∀ n : ℕ,
      xiShiftedReciprocalMoment y n * u ^ n =
        ∑' q : XiZeroCopy, u ^ n * mu q ^ (n + 1) := by
    intro n
    rw [xiShiftedReciprocalMoment, ← tsum_mul_right]
    apply tsum_congr
    intro q
    dsimp only [mu]
    ring
  rw [tsum_congr hstep, ← Summable.tsum_comm huncurry]
  apply tsum_congr
  intro q
  have humu : ‖u * mu q‖ < 1 := by
    rw [norm_mul]
    have hsmall : (2 / 41 : ℝ) ≤ 1 := by norm_num
    have hu' : ‖u‖ * (1 : ℝ) < 1 := by simpa using hu
    exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_left
        ((norm_xiShiftedReciprocalSquare_le hy q).trans
          ((norm_xiZeroCopyReciprocalSquare_lt_two_over_fortyOne q).le.trans
            hsmall))
        (norm_nonneg u)) hu'
  change (∑' n : ℕ, u ^ n * mu q ^ (n + 1)) =
    mu q / (1 - u * mu q)
  calc
    (∑' n : ℕ, u ^ n * mu q ^ (n + 1)) =
        mu q * ∑' n : ℕ, (u * mu q) ^ n := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro n
      rw [mul_pow, pow_succ]
      ring
    _ = mu q / (1 - u * mu q) := by
      rw [tsum_geometric_of_norm_lt_one humu, div_eq_mul_inv]

/-- The fixed Cassini source is nonzero at every positive-mass Route-U center `1 - y`. -/
theorem xiSquaredSeamCassiniSource_one_sub_posMass_ne_zero
    {y : ℝ} (hy : 0 < y) :
    xiSquaredSeamCassiniSource (1 - (y : ℂ)) ≠ 0 := by
  let t := Real.sqrt y
  have ht : 0 < t := Real.sqrt_pos.2 hy
  have htsq : t ^ 2 = y := Real.sq_sqrt hy.le
  have harg : 1 + (-((t : ℂ) * I)) ^ 2 = 1 - (y : ℂ) := by
    apply Complex.ext
    · simp [pow_two, Complex.mul_re, Complex.mul_im]
      nlinarith [htsq]
    · simp [pow_two, Complex.mul_re, Complex.mul_im]
  rw [← harg, xiSquaredSeamCassiniSource_one_add_sq]
  exact XiC_neg_imaginaryAxis_ne_zero ht

private theorem xiShiftedReciprocalSquare_one_resolvent_eq
    {y : ℝ} (hy : 0 < y) {u : ℂ} (hu : ‖u‖ < 1) (q : XiZeroCopy) :
    xiSquaredSeamOneCoordinate q /
        (1 - ((1 - (y : ℂ)) + u) * xiSquaredSeamOneCoordinate q) =
      xiShiftedReciprocalSquare y q /
        (1 - u * xiShiftedReciprocalSquare y q) := by
  let lam := xiSquaredSeamOneCoordinate q
  have hbase : 1 + ((y - 1 : ℝ) : ℂ) * lam ≠ 0 := by
    have h := one_add_mul_xiShiftedReciprocalSquare_ne_zero
      (y := 1) (u := y - 1) (by norm_num) (by linarith) q
    rw [xiShiftedReciprocalSquare_one_eq_xiSquaredSeamOneCoordinate] at h
    simpa only [lam] using h
  have hflow : xiShiftedReciprocalSquare y q =
      lam / (1 + ((y - 1 : ℝ) : ℂ) * lam) := by
    have h := xiShiftedReciprocalSquare_add
      (y := 1) (u := y - 1) (by norm_num) (by linarith) q
    rw [xiShiftedReciprocalSquare_one_eq_xiSquaredSeamOneCoordinate] at h
    dsimp only [lam]
    convert h using 1 <;> ring
  have hshift : 1 - u * xiShiftedReciprocalSquare y q ≠ 0 := by
    have hmul : ‖u * xiShiftedReciprocalSquare y q‖ < 1 := by
      rw [norm_mul]
      have hsmall : (2 / 41 : ℝ) ≤ 1 := by norm_num
      have hu' : ‖u‖ * (1 : ℝ) < 1 := by simpa using hu
      exact lt_of_le_of_lt
        (mul_le_mul_of_nonneg_left
          ((norm_xiShiftedReciprocalSquare_le hy.le q).trans
            ((norm_xiZeroCopyReciprocalSquare_lt_two_over_fortyOne q).le.trans
              hsmall))
          (norm_nonneg u)) hu'
    intro hzero
    have hone : u * xiShiftedReciprocalSquare y q = 1 := (sub_eq_zero.mp hzero).symm
    rw [hone, norm_one] at hmul
    exact (lt_irrefl 1 hmul)
  have hmul :
      (1 + ((y - 1 : ℝ) : ℂ) * lam) * xiShiftedReciprocalSquare y q = lam := by
    rw [hflow]
    field_simp [hbase]
  have hfactor :
      1 - ((1 - (y : ℂ)) + u) * lam =
        (1 + ((y - 1 : ℝ) : ℂ) * lam) *
          (1 - u * xiShiftedReciprocalSquare y q) := by
    calc
      1 - ((1 - (y : ℂ)) + u) * lam =
          (1 + ((y - 1 : ℝ) : ℂ) * lam) - u * lam := by
        push_cast
        ring
      _ = (1 + ((y - 1 : ℝ) : ℂ) * lam) -
          u * ((1 + ((y - 1 : ℝ) : ℂ) * lam) *
            xiShiftedReciprocalSquare y q) := by rw [hmul]
      _ = (1 + ((y - 1 : ℝ) : ℂ) * lam) *
          (1 - u * xiShiftedReciprocalSquare y q) := by ring
  have hleft :
      1 - ((1 - (y : ℂ)) + u) * lam ≠ 0 := by
    rw [hfactor]
    exact mul_ne_zero hbase hshift
  change lam / (1 - ((1 - (y : ℂ)) + u) * lam) = _
  rw [hfactor, hflow]
  field_simp [hbase, hshift]

/-- **Moving fixed-source germ law.** Around every positive mass `y`, translating the one fixed
Cassini logarithmic derivative to `1 - y` gives the complete local shifted moment germ. -/
theorem negTwoCassiniLogDeriv_one_sub_add_eventuallyEq_shiftedMomentGerm
    {y : ℝ} (hy : 0 < y) :
    (fun u : ℂ => -2 * logDeriv xiSquaredSeamCassiniSource
      ((1 - (y : ℂ)) + u)) =ᶠ[𝓝 0]
      xiShiftedCassiniMomentGerm y := by
  have hsource0 := xiSquaredSeamCassiniSource_one_sub_posMass_ne_zero hy
  have hsource : ∀ᶠ u : ℂ in 𝓝 0,
      xiSquaredSeamCassiniSource ((1 - (y : ℂ)) + u) ≠ 0 :=
    by
      have hcont : ContinuousAt
          (fun u : ℂ => xiSquaredSeamCassiniSource ((1 - (y : ℂ)) + u)) 0 := by
        exact differentiable_xiSquaredSeamCassiniSource.continuous.continuousAt.comp
          (continuousAt_const.add continuousAt_id)
      exact hcont.eventually_ne (by simpa using hsource0)
  have hone : ∀ᶠ u : ℂ in 𝓝 0, (1 - (y : ℂ)) + u ≠ 1 := by
    have h0 : (1 - (y : ℂ)) ≠ 1 := by
      intro h
      have hy0 : (y : ℂ) = 0 := by linear_combination -h
      exact (ofReal_ne_zero.mpr hy.ne') hy0
    have hcont : ContinuousAt (fun u : ℂ => (1 - (y : ℂ)) + u) 0 := by
      fun_prop
    exact hcont.eventually_ne (by simpa using h0)
  have hnorm : ∀ᶠ u : ℂ in 𝓝 0, ‖u‖ < 1 :=
    tendsto_norm_zero.eventually_lt_const zero_lt_one
  filter_upwards [hsource, hone, hnorm] with u hsourceU honeU hu
  rw [neg_two_mul_logDeriv_xiSquaredSeamCassiniSource_eq_resolvent honeU hsourceU,
    xiShiftedCassiniMomentGerm_eq_resolvent hy.le hu]
  apply tsum_congr
  intro q
  exact xiShiftedReciprocalSquare_one_resolvent_eq hy hu q

/-- **All-jet adaptive-to-fixed-source bridge.** Every shifted Xi reciprocal moment is the
corresponding logarithmic-derivative jet of the same Cassini entire source, read at `1 - y`.
Unlike node-count transport, this identity retains all flat defects and the complete quadratic
form selected by a hypothetical Route-U crossing. -/
theorem neg_two_mul_cassiniLogDeriv_jet_one_sub_eq_xiShiftedMoment
    {y : ℝ} (hy : 0 < y) (n : ℕ) :
    -2 * iteratedDeriv n (logDeriv xiSquaredSeamCassiniSource)
        (1 - (y : ℂ)) =
      ((n.factorial : ℕ) : ℂ) * xiShiftedReciprocalMoment y n := by
  have hder :=
    (negTwoCassiniLogDeriv_one_sub_add_eventuallyEq_shiftedMomentGerm hy).iteratedDeriv_eq n
  have htranslate :
      (fun u : ℂ => logDeriv xiSquaredSeamCassiniSource
        ((1 - (y : ℂ)) + u)) =
        fun u : ℂ => logDeriv xiSquaredSeamCassiniSource
          (u + (1 - (y : ℂ))) := by
    funext u
    congr 1
    ring
  rw [congrFun
      (GaloisForLFunctions.iteratedDeriv_const_mul_field
        (-2 : ℂ)
        (fun u : ℂ => logDeriv xiSquaredSeamCassiniSource
          ((1 - (y : ℂ)) + u)) n) 0] at hder
  rw [htranslate] at hder
  rw [
    GaloisForLFunctions.HTGeometry.iteratedDeriv_comp_add_right
      (logDeriv xiSquaredSeamCassiniSource) (1 - (y : ℂ)) n 0,
    zero_add,
    iteratedDeriv_xiShiftedCassiniMomentGerm hy.le n] at hder
  exact hder

/-- Normalized real jet sequence of the fixed Cassini source at mass center `1 - y`. -/
def xiShiftedCassiniSourceMoment (y : ℝ) (n : ℕ) : ℝ :=
  -2 * (iteratedDeriv n (logDeriv xiSquaredSeamCassiniSource)
    (1 - (y : ℂ))).re / (n.factorial : ℝ)

theorem xiShiftedReciprocalMoment_re_eq_cassiniSourceMoment
    {y : ℝ} (hy : 0 < y) (n : ℕ) :
    (xiShiftedReciprocalMoment y n).re =
      xiShiftedCassiniSourceMoment y n := by
  have hjet := neg_two_mul_cassiniLogDeriv_jet_one_sub_eq_xiShiftedMoment hy n
  have hre := congrArg Complex.re hjet
  norm_num [Complex.mul_re, xiShiftedCassiniSourceMoment] at hre ⊢
  have hfac : (n.factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  apply (eq_div_iff hfac).2
  linear_combination -hre

/-- In the Euler convergence window, the same fixed-source jet is the source-defined
prime--Gamma shifted moment. -/
theorem primeArchShiftedReciprocalMoment_re_eq_cassiniSourceMoment
    {y : ℝ} (hy : 0 < y) (hymax : y < 41 / 2) (n : ℕ) :
    (primeArchShiftedReciprocalMoment y n).re =
      xiShiftedCassiniSourceMoment y n := by
  rw [← xiShiftedReciprocalMoment_eq_primeArchShiftedReciprocalMoment hy.le hymax]
  exact xiShiftedReciprocalMoment_re_eq_cassiniSourceMoment hy n

/-- Padé defect formed directly from normalized jets of the fixed Cassini source. -/
def xiShiftedCassiniSourceHankelBoundaryPadeDefect
    (y : ℝ) {n : ℕ} (c : Fin (n + 1) → ℝ) (k : ℕ) : ℝ :=
  HTGeometry.finiteHankelBoundaryPadeDefect
    (xiShiftedCassiniSourceMoment y) c k

/-- Every adaptive Xi Padé defect is exactly a defect of one fixed Cassini source at `1 - y`. -/
theorem xiShiftedHankelBoundaryPadeDefect_eq_cassiniSource
    {y : ℝ} (hy : 0 < y) {n : ℕ} (c : Fin (n + 1) → ℝ) (k : ℕ) :
    xiShiftedHankelBoundaryPadeDefect y c k =
      xiShiftedCassiniSourceHankelBoundaryPadeDefect y c k := by
  have hseq : (fun j => (xiShiftedReciprocalMoment y j).re) =
      xiShiftedCassiniSourceMoment y := by
    funext j
    exact xiShiftedReciprocalMoment_re_eq_cassiniSourceMoment hy j
  simp only [xiShiftedHankelBoundaryPadeDefect,
    xiShiftedCassiniSourceHankelBoundaryPadeDefect, hseq]

/-- The entire shifted Xi Hankel block is the real jet-Hankel block of the fixed Cassini source. -/
theorem xiShiftedMomentHankelMatrix_eq_cassiniSource
    {y : ℝ} (hy : 0 < y) (N : ℕ) :
    xiShiftedMomentHankelMatrix y N =
      GaloisForLFunctions.HTGeometry.finiteHankelMatrix
        (xiShiftedCassiniSourceMoment y) N := by
  ext i j
  simp only [xiShiftedMomentHankelMatrix,
    GaloisForLFunctions.HTGeometry.finiteHankelMatrix]
  exact xiShiftedReciprocalMoment_re_eq_cassiniSourceMoment hy (i + j)

/-- Every polynomial moment pairing, hence every finite quadratic sector, is retained by the
fixed-source jet representation. -/
theorem momentFunctional_xiShifted_eq_cassiniSource
    {y : ℝ} (hy : 0 < y) (A : Polynomial ℝ) :
    HTGeometry.momentFunctional
        (fun k => (xiShiftedReciprocalMoment y k).re) A =
      HTGeometry.momentFunctional (xiShiftedCassiniSourceMoment y) A := by
  congr 1
  funext k
  exact xiShiftedReciprocalMoment_re_eq_cassiniSourceMoment hy k

/-- **Window-free fixed-source crossing law.** Any genuine Route-U crossing selects an odd
contact whose complete flat defect and strictly negative shifted-square sector already occur in
the jets of the single Cassini source at `1 - y`.  Unlike the prime--Gamma wrapper, this theorem
holds at every positive mass. -/
theorem exists_negative_cassiniSource_liftedShiftedSquare_of_genuine_crossing
    {y : ℝ} (hy : 0 < y)
    {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hhead : (xiShiftedMomentHankelMatrix y n).PosDef)
    (hc : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0)
    (hright : ∀ᶠ u in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (xiShiftedMomentHankelMatrix (y + u) (n + 1)).PosSemidef)
    (hleft : ∀ᶠ u in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ¬ (xiShiftedMomentHankelMatrix (y - u) (n + 1)).PosSemidef) :
    ∃ m : ℕ,
      (∀ k < 2 * n + (2 * m + 1),
        xiShiftedCassiniSourceHankelBoundaryPadeDefect y c k = 0) ∧
      HTGeometry.momentFunctional (xiShiftedCassiniSourceMoment y)
        (Polynomial.X *
          (HTGeometry.finiteHankelNullMonicPolynomial c * Polynomial.X ^ m) ^ 2) < 0 := by
  obtain ⟨d, hd, hzero, hsigned⟩ :=
    exists_signed_first_xiShiftedHankelBoundaryPadeDefect_of_right_posSemidef
      hy c hhead hc hlast hright
  have hfirst : xiShiftedHankelBoundaryPadeDefect y c (2 * n + d) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hsigned
    exact (lt_irrefl 0 hsigned).elim
  obtain ⟨m, hm⟩ := odd_first_contact_of_genuine_xiShiftedHankel_crossing
    hy c hhead hc hlast hd hzero hfirst hright hleft
  have hdform : d = 2 * m + 1 := by omega
  have hzeroSource : ∀ k < 2 * n + (2 * m + 1),
      xiShiftedCassiniSourceHankelBoundaryPadeDefect y c k = 0 := by
    intro k hk
    rw [← xiShiftedHankelBoundaryPadeDefect_eq_cassiniSource hy]
    exact hzero k (by omega)
  refine ⟨m, hzeroSource, ?_⟩
  have hvalue :=
    xiShiftedHankelBoundaryPadeDefect_first_odd_eq_liftedShiftedSquare
    (m := m) c hlast (by
      intro k hk
      exact hzero k (by omega))
  rw [hdform] at hsigned
  have hparity : Odd (2 * m + 1) := ⟨m, by omega⟩
  rw [Odd.neg_one_pow hparity, neg_mul, hvalue] at hsigned
  rw [← momentFunctional_xiShifted_eq_cassiniSource hy]
  linarith

end

end RHTower
