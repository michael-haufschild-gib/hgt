import GaloisForLFunctions.RHTower.XiSquaredSeamCassiniGlobalJensenLaw
import GaloisForLFunctions.RHTower.ThetaCuspFourierLaplace
import GaloisForLFunctions.RHTower.ModulusSlopeBudget
import GaloisForLFunctions.RHTower.XiThermalQuadraticReflectionDefectSpectrum
import GaloisForLFunctions.RHTower.XiReciprocalSquareFixedCauchySource

/-!
# Cassini resolvent and local source-jet law

The translated square-factor source used by the Cassini--Jensen formula has a second exact
interpretation: its negative logarithmic derivative is the shift-one reciprocal resolvent of the
multiplicity-exact Xi divisor.  Functional-equation pairing supplies the factor two.

The resulting ordinary moment germ identifies every shift-one prime--Gamma moment with a local
logarithmic-derivative jet of the same entire Cassini source.  At degree 63 this rewrites the
remaining power-64 RH obstruction as an intrinsic relation between one function's radial Jensen
mass and its local jet at the Euler-safe center.
-/

open Complex Filter Topology
open scoped ENNReal NNReal

namespace RHTower

noncomputable section

/-- The Cassini source pulled back through its square cover is exactly centered Xi. -/
theorem xiSquaredSeamCassiniSource_one_add_sq (z : ℂ) :
    xiSquaredSeamCassiniSource (1 + z ^ 2) = XiC z := by
  rw [xiSquaredSeamCassiniSource]
  convert xiSquaredSeamEntireQuotient_sq z using 1
  ring

/-- Logarithmic-derivative chain rule on the regular part of the square cover. -/
theorem logDeriv_XiC_eq_two_mul_xiSquaredSeamCassiniSource
    {z : ℂ} (hz : z ≠ 0) (hXi : XiC z ≠ 0) :
    logDeriv XiC z =
      2 * z * logDeriv xiSquaredSeamCassiniSource (1 + z ^ 2) := by
  have hinner : HasDerivAt (fun w : ℂ => 1 + w ^ 2) (2 * z) z := by
    convert (hasDerivAt_const (x := z) (c := (1 : ℂ))).add
      (hasDerivAt_pow 2 z) using 1
    all_goals norm_num [pow_two]
  have houter :=
    differentiable_xiSquaredSeamCassiniSource.differentiableAt.hasDerivAt
      |>.comp z hinner
  have hderiv : deriv XiC z =
      deriv xiSquaredSeamCassiniSource (1 + z ^ 2) * (2 * z) := by
    have hcomp :
        xiSquaredSeamCassiniSource ∘ (fun w : ℂ => 1 + w ^ 2) = XiC := by
      funext w
      exact xiSquaredSeamCassiniSource_one_add_sq w
    rw [hcomp] at houter
    exact houter.deriv
  rw [logDeriv_apply, logDeriv_apply, hderiv, xiSquaredSeamCassiniSource_one_add_sq]
  field_simp [hXi]

/-- A regular Xi point misses every reciprocal-square resolvent pole. -/
theorem one_sub_sq_mul_xiZeroCopyReciprocalSquare_ne_zero
    {z : ℂ} (hXi : XiC z ≠ 0) (q : XiZeroCopy) :
    1 - z ^ 2 * xiZeroCopyReciprocalSquare q ≠ 0 := by
  intro hden
  have ha : xiSpectralPoint q ≠ 0 := xiSpectralPoint_ne_zero q
  have hsq : z ^ 2 = xiSpectralPoint q ^ 2 := by
    rw [xiZeroCopyReciprocalSquare] at hden
    field_simp [ha] at hden
    linear_combination -hden
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with hz | hz
  · exact hXi ((XiC_eq_zero_iff_exists_xiZeroCopy z).mpr ⟨q, hz.symm⟩)
  · exact hXi ((XiC_eq_zero_iff_exists_xiZeroCopy z).mpr
      ⟨xiZeroCopyReflectEquiv q, by rw [xiSpectralPoint_reflect, ← hz]⟩)

/-- Möbius translation converts each centered reciprocal-square resolvent term into its Cassini
resolvent term. -/
theorem xiReciprocalSquareResolventTerm_eq_cassiniResolventTerm
    {z : ℂ} (hXi : XiC z ≠ 0) (q : XiZeroCopy) :
    xiReciprocalSquareResolventTerm z q =
      xiSquaredSeamOneCoordinate q /
        (1 - (1 + z ^ 2) * xiSquaredSeamOneCoordinate q) := by
  rw [← xiShiftedReciprocalSquare_one_eq_xiSquaredSeamOneCoordinate]
  rw [xiReciprocalSquareResolventTerm, xiShiftedReciprocalSquare]
  simp only [Complex.ofReal_one, one_mul]
  have hplus : 1 + xiZeroCopyReciprocalSquare q ≠ 0 := by
    simpa using
      one_add_mul_xiZeroCopyReciprocalSquare_ne_zero (y := 1) (by norm_num) q
  have hden := one_sub_sq_mul_xiZeroCopyReciprocalSquare_ne_zero hXi q
  have htargetEq :
      1 - (1 + z ^ 2) *
          (xiZeroCopyReciprocalSquare q / (1 + xiZeroCopyReciprocalSquare q)) =
        (1 - z ^ 2 * xiZeroCopyReciprocalSquare q) /
          (1 + xiZeroCopyReciprocalSquare q) := by
    field_simp [hplus]
    ring
  rw [htargetEq]
  field_simp [hplus, hden]

/-- Exact Cassini resolvent identity on the square cover.  The factor two records the two Xi zero
copies identified by the square quotient. -/
theorem neg_two_mul_logDeriv_xiSquaredSeamCassiniSource_one_add_sq
    {z : ℂ} (hz : z ≠ 0) (hXi : XiC z ≠ 0) :
    -2 * logDeriv xiSquaredSeamCassiniSource (1 + z ^ 2) =
      ∑' q : XiZeroCopy,
        xiSquaredSeamOneCoordinate q /
          (1 - (1 + z ^ 2) * xiSquaredSeamOneCoordinate q) := by
  have hlog := logDeriv_XiC_eq_relativeResolventTrace hXi
  rw [xiRelativeResolventTrace_eq_reciprocalSquareResolvent hXi] at hlog
  rw [logDeriv_XiC_eq_two_mul_xiSquaredSeamCassiniSource hz hXi] at hlog
  have hcancel :
      -2 * logDeriv xiSquaredSeamCassiniSource (1 + z ^ 2) =
        ∑' q : XiZeroCopy, xiReciprocalSquareResolventTerm z q := by
    apply (mul_left_cancel₀ hz)
    linear_combination -hlog
  rw [hcancel]
  apply tsum_congr
  exact xiReciprocalSquareResolventTerm_eq_cassiniResolventTerm hXi

/-- Direct Cassini-coordinate form of the resolvent identity. -/
theorem neg_two_mul_logDeriv_xiSquaredSeamCassiniSource_eq_resolvent
    {u : ℂ} (hu : u ≠ 1) (hsource : xiSquaredSeamCassiniSource u ≠ 0) :
    -2 * logDeriv xiSquaredSeamCassiniSource u =
      ∑' q : XiZeroCopy,
        xiSquaredSeamOneCoordinate q /
          (1 - u * xiSquaredSeamOneCoordinate q) := by
  let z : ℂ := Complex.sqrt (u - 1)
  have hzsq : z ^ 2 = u - 1 := by
    exact GaloisForLFunctions.HTGeometry.complex_sqrt_sq (u - 1)
  have hz : z ≠ 0 := by
    intro hz0
    rw [hz0, zero_pow (by norm_num)] at hzsq
    apply hu
    linear_combination -hzsq
  have hXi : XiC z ≠ 0 := by
    rw [← xiSquaredSeamCassiniSource_one_add_sq]
    convert hsource using 1
    rw [hzsq]
    ring
  simpa only [show 1 + z ^ 2 = u by rw [hzsq]; ring] using
    neg_two_mul_logDeriv_xiSquaredSeamCassiniSource_one_add_sq hz hXi

/-- Source-defined ordinary moment series of the shift-one Cassini resolvent. -/
def xiSquaredSeamCassiniMomentPowerSeries : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ
    (fun n => primeArchShiftedReciprocalMoment 1 n)

/-- Analytic ordinary generating germ of the source-defined shift-one moments. -/
def xiSquaredSeamCassiniMomentGerm : ℂ → ℂ :=
  xiSquaredSeamCassiniMomentPowerSeries.sum

theorem exists_xiSquaredSeamOneCoordinate_norm_bound :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ q : XiZeroCopy, ‖xiSquaredSeamOneCoordinate q‖ ≤ M := by
  obtain ⟨M, hM, hbound⟩ := exists_xiZeroCopyReciprocalSquare_norm_bound
  refine ⟨M, hM, fun q => ?_⟩
  rw [← xiShiftedReciprocalSquare_one_eq_xiSquaredSeamOneCoordinate]
  exact (norm_xiShiftedReciprocalSquare_le (y := 1) (by norm_num) q).trans
    (hbound q)

theorem norm_primeArchShiftedReciprocalMoment_one_le
    {M : ℝ} (hbound : ∀ q : XiZeroCopy, ‖xiSquaredSeamOneCoordinate q‖ ≤ M)
    (n : ℕ) :
    ‖primeArchShiftedReciprocalMoment 1 n‖ ≤
      M ^ n * ∑' q : XiZeroCopy, ‖xiSquaredSeamOneCoordinate q‖ := by
  rw [← xiShiftedReciprocalMoment_eq_primeArchShiftedReciprocalMoment
    (y := 1) (by norm_num) (by norm_num)]
  change ‖∑' q : XiZeroCopy, xiShiftedReciprocalSquare 1 q ^ (n + 1)‖ ≤ _
  simp_rw [xiShiftedReciprocalSquare_one_eq_xiSquaredSeamOneCoordinate]
  calc
    ‖∑' q : XiZeroCopy, xiSquaredSeamOneCoordinate q ^ (n + 1)‖ ≤
        ∑' q : XiZeroCopy, ‖xiSquaredSeamOneCoordinate q ^ (n + 1)‖ :=
      norm_tsum_le_tsum_norm
        ((summable_xiShiftedReciprocalSquare_pow (y := 1) (by norm_num) n).norm.congr
          (fun q => by rw [xiShiftedReciprocalSquare_one_eq_xiSquaredSeamOneCoordinate]))
    _ ≤ ∑' q : XiZeroCopy,
        M ^ n * ‖xiSquaredSeamOneCoordinate q‖ := by
      apply Summable.tsum_mono
        ((summable_xiShiftedReciprocalSquare_pow (y := 1) (by norm_num) n).norm.congr
          (fun q => by rw [xiShiftedReciprocalSquare_one_eq_xiSquaredSeamOneCoordinate]))
        (((summable_xiShiftedReciprocalSquare_pow (y := 1) (by norm_num) 0).congr
          (fun q => by simp only [zero_add, pow_one,
            xiShiftedReciprocalSquare_one_eq_xiSquaredSeamOneCoordinate])).norm.mul_left
              (M ^ n))
      intro q
      simpa only [pow_succ, norm_mul, norm_pow] using
        (mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (norm_nonneg _) (hbound q) n)
          (norm_nonneg (xiSquaredSeamOneCoordinate q)))
    _ = M ^ n * ∑' q : XiZeroCopy, ‖xiSquaredSeamOneCoordinate q‖ := by
      rw [tsum_mul_left]

theorem xiSquaredSeamCassiniMomentPowerSeries_radius_pos :
    0 < xiSquaredSeamCassiniMomentPowerSeries.radius := by
  obtain ⟨M, hM, hbound⟩ := exists_xiSquaredSeamOneCoordinate_norm_bound
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  let r : ℝ≥0 := ⟨1 / (2 * M), by positivity⟩
  let S : ℝ := ∑' q : XiZeroCopy, ‖xiSquaredSeamOneCoordinate q‖
  have hrad : (r : ℝ≥0∞) ≤ xiSquaredSeamCassiniMomentPowerSeries.radius := by
    apply FormalMultilinearSeries.le_radius_of_bound
      (p := xiSquaredSeamCassiniMomentPowerSeries) S
    intro n
    rw [xiSquaredSeamCassiniMomentPowerSeries, FormalMultilinearSeries.ofScalars_norm]
    have hmoment := norm_primeArchShiftedReciprocalMoment_one_le hbound n
    change ‖primeArchShiftedReciprocalMoment 1 n‖ * (1 / (2 * M)) ^ n ≤ S
    calc
      ‖primeArchShiftedReciprocalMoment 1 n‖ * (1 / (2 * M)) ^ n ≤
          (M ^ n * S) * (1 / (2 * M)) ^ n :=
        mul_le_mul_of_nonneg_right hmoment (pow_nonneg (by positivity) _)
      _ = S * (M * (1 / (2 * M))) ^ n := by
        rw [mul_pow]
        ring
      _ = S * (1 / 2) ^ n := by
        rw [show M * (1 / (2 * M)) = (1 / 2 : ℝ) by field_simp]
      _ ≤ S := by
        exact mul_le_of_le_one_right (tsum_nonneg fun _ => norm_nonneg _)
          (pow_le_one₀ (by norm_num) (by norm_num))
  have hrpos : 0 < r := by
    apply NNReal.coe_pos.mp
    change 0 < 1 / (2 * M)
    positivity
  exact (ENNReal.coe_pos.mpr hrpos).trans_le hrad

theorem analyticAt_xiSquaredSeamCassiniMomentGerm :
    AnalyticAt ℂ xiSquaredSeamCassiniMomentGerm 0 := by
  exact ⟨xiSquaredSeamCassiniMomentPowerSeries,
    xiSquaredSeamCassiniMomentPowerSeries.hasFPowerSeriesOnBall
      xiSquaredSeamCassiniMomentPowerSeries_radius_pos |>.hasFPowerSeriesAt⟩

theorem xiSquaredSeamCassiniMomentGerm_eq_tsum (u : ℂ) :
    xiSquaredSeamCassiniMomentGerm u =
      ∑' n : ℕ, primeArchShiftedReciprocalMoment 1 n * u ^ n := by
  rw [xiSquaredSeamCassiniMomentGerm, xiSquaredSeamCassiniMomentPowerSeries]
  change FormalMultilinearSeries.ofScalarsSum
    (fun n => primeArchShiftedReciprocalMoment 1 n) u = _
  rw [FormalMultilinearSeries.ofScalars_sum_eq]
  simp only [smul_eq_mul]

theorem xiSquaredSeamCassiniMomentGerm_eq_resolvent
    {M : ℝ} (hM : 1 ≤ M)
    (hbound : ∀ q : XiZeroCopy, ‖xiSquaredSeamOneCoordinate q‖ ≤ M)
    {u : ℂ} (hu : ‖u‖ * M < 1) :
    xiSquaredSeamCassiniMomentGerm u =
      ∑' q : XiZeroCopy,
        xiSquaredSeamOneCoordinate q /
          (1 - u * xiSquaredSeamOneCoordinate q) := by
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  let mu : XiZeroCopy → ℂ := xiSquaredSeamOneCoordinate
  have hmu : Summable (fun q => ‖mu q‖) := by
    simpa only [mu] using
      ((summable_xiShiftedReciprocalSquare_pow (y := 1) (by norm_num) 0).congr
        (fun q => by simp only [zero_add, pow_one,
          xiShiftedReciprocalSquare_one_eq_xiSquaredSeamOneCoordinate])).norm
  let ratio : ℝ := ‖u‖ * M
  have hratio0 : 0 ≤ ratio := mul_nonneg (norm_nonneg _) hM0
  have hratio1 : ratio < 1 := by simpa only [ratio] using hu
  have hgeom : Summable (fun n : ℕ => ratio ^ n) :=
    summable_geometric_of_lt_one hratio0 hratio1
  have hboundTerm : ∀ (n : ℕ) (q : XiZeroCopy),
      ‖u ^ n * mu q ^ (n + 1)‖ ≤ ratio ^ n * ‖mu q‖ := by
    intro n q
    rw [norm_mul, norm_pow, pow_succ, norm_mul, norm_pow]
    have hmuPow : ‖mu q‖ ^ n ≤ M ^ n :=
      pow_le_pow_left₀ (norm_nonneg _) (hbound q) n
    calc
      ‖u‖ ^ n * (‖mu q‖ ^ n * ‖mu q‖) ≤
          ‖u‖ ^ n * (M ^ n * ‖mu q‖) := by gcongr
      _ = ratio ^ n * ‖mu q‖ := by
        rw [mul_pow]
        ring
  have hnorm : Summable (fun p : ℕ × XiZeroCopy =>
      ratio ^ p.1 * ‖mu p.2‖) := by
    rw [summable_prod_of_nonneg
      (fun p => mul_nonneg (pow_nonneg hratio0 _) (norm_nonneg _))]
    constructor
    · intro n
      exact hmu.mul_left (ratio ^ n)
    · apply Summable.of_nonneg_of_le
        (fun n => tsum_nonneg fun _ =>
          mul_nonneg (pow_nonneg hratio0 _) (norm_nonneg _))
        (fun n => le_rfl)
      convert hgeom.mul_right (∑' q : XiZeroCopy, ‖mu q‖) using 1
      funext n
      rw [← tsum_mul_left]
  have huncurry : Summable (Function.uncurry
      (fun (n : ℕ) (q : XiZeroCopy) => u ^ n * mu q ^ (n + 1))) := by
    apply Summable.of_norm_bounded hnorm
    intro p
    exact hboundTerm p.1 p.2
  rw [xiSquaredSeamCassiniMomentGerm_eq_tsum]
  have hstep : ∀ n : ℕ,
      primeArchShiftedReciprocalMoment 1 n * u ^ n =
        ∑' q : XiZeroCopy, u ^ n * mu q ^ (n + 1) := by
    intro n
    rw [← xiShiftedReciprocalMoment_eq_primeArchShiftedReciprocalMoment
      (y := 1) (by norm_num) (by norm_num)]
    change (∑' q : XiZeroCopy, xiShiftedReciprocalSquare 1 q ^ (n + 1)) * u ^ n = _
    rw [← tsum_mul_right]
    apply tsum_congr
    intro q
    dsimp only [mu]
    rw [xiShiftedReciprocalSquare_one_eq_xiSquaredSeamOneCoordinate]
    ring
  rw [tsum_congr hstep, ← Summable.tsum_comm huncurry]
  apply tsum_congr
  intro q
  have humu : ‖u * mu q‖ < 1 := by
    rw [norm_mul]
    exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_left (hbound q) (norm_nonneg u)) hu
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

theorem iteratedDeriv_xiSquaredSeamCassiniMomentGerm (n : ℕ) :
    iteratedDeriv n xiSquaredSeamCassiniMomentGerm 0 =
      ((n.factorial : ℕ) : ℂ) * primeArchShiftedReciprocalMoment 1 n := by
  have hp := xiSquaredSeamCassiniMomentPowerSeries.hasFPowerSeriesOnBall
    xiSquaredSeamCassiniMomentPowerSeries_radius_pos
  have hfac := hp.factorial_smul (1 : ℂ) n
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod,
    Finset.prod_const_one, one_smul] at hfac
  rw [xiSquaredSeamCassiniMomentPowerSeries,
    FormalMultilinearSeries.ofScalars_apply_eq, one_pow, smul_eq_mul,
    mul_one] at hfac
  simpa only [nsmul_eq_mul] using hfac.symm

/-- Near the Euler-safe center, the source moment germ is exactly twice the negative logarithmic
derivative of the same Cassini entire source. -/
theorem negTwoCassiniLogDeriv_eventuallyEq_momentGerm :
    (fun u : ℂ => -2 * logDeriv xiSquaredSeamCassiniSource u) =ᶠ[𝓝 0]
      xiSquaredSeamCassiniMomentGerm := by
  obtain ⟨M, hM, hbound⟩ := exists_xiSquaredSeamOneCoordinate_norm_bound
  have hratioCont : ContinuousAt (fun u : ℂ => ‖u‖ * M) 0 := by fun_prop
  have hratioTendsto : Tendsto (fun u : ℂ => ‖u‖ * M) (𝓝 0) (𝓝 0) := by
    have ht := hratioCont
    change Tendsto (fun u : ℂ => ‖u‖ * M) (𝓝 0)
      (𝓝 (‖(0 : ℂ)‖ * M)) at ht
    norm_num at ht
    exact ht
  have hratio : ∀ᶠ u : ℂ in 𝓝 0, ‖u‖ * M < 1 :=
    hratioTendsto.eventually_lt_const zero_lt_one
  have hsource : ∀ᶠ u : ℂ in 𝓝 0,
      xiSquaredSeamCassiniSource u ≠ 0 :=
    differentiable_xiSquaredSeamCassiniSource.continuous.continuousAt.eventually_ne
      xiSquaredSeamCassiniSource_zero_ne
  have hone : ∀ᶠ u : ℂ in 𝓝 0, u ≠ 1 :=
    continuousAt_id.eventually_ne (by norm_num)
  filter_upwards [hratio, hsource, hone] with u hu hsourceU huone
  rw [neg_two_mul_logDeriv_xiSquaredSeamCassiniSource_eq_resolvent huone hsourceU,
    ← xiSquaredSeamCassiniMomentGerm_eq_resolvent hM hbound hu]

/-- Local first-order source law: the prime--Gamma shift-one moment germ drives the Cassini entire
source itself, without a remaining zero-divisor interface. -/
theorem negTwoCassiniDeriv_eventuallyEq_momentGerm_mul_source :
    (fun u : ℂ => -2 * deriv xiSquaredSeamCassiniSource u) =ᶠ[𝓝 0]
      (fun u => xiSquaredSeamCassiniMomentGerm u * xiSquaredSeamCassiniSource u) := by
  have hsource : ∀ᶠ u : ℂ in 𝓝 0,
      xiSquaredSeamCassiniSource u ≠ 0 :=
    differentiable_xiSquaredSeamCassiniSource.continuous.continuousAt.eventually_ne
      xiSquaredSeamCassiniSource_zero_ne
  filter_upwards [negTwoCassiniLogDeriv_eventuallyEq_momentGerm, hsource]
    with u hmoment hsourceU
  rw [← hmoment, logDeriv_apply]
  field_simp [hsourceU]

/-- All-degree local source-jet law for the shift-one prime--Gamma moments. -/
theorem neg_two_mul_cassiniLogDeriv_jet_eq_shiftedMoment (n : ℕ) :
    -2 * iteratedDeriv n (logDeriv xiSquaredSeamCassiniSource) 0 =
      ((n.factorial : ℕ) : ℂ) * primeArchShiftedReciprocalMoment 1 n := by
  have hder := negTwoCassiniLogDeriv_eventuallyEq_momentGerm.iteratedDeriv_eq n
  rw [congrFun
    (GaloisForLFunctions.iteratedDeriv_const_mul_field
      (-2 : ℂ) (logDeriv xiSquaredSeamCassiniSource) n) 0,
    iteratedDeriv_xiSquaredSeamCassiniMomentGerm n] at hder
  exact hder

theorem primeArchShiftedReciprocalMoment_one_re_eq_cassiniLogDeriv_jet (n : ℕ) :
    (primeArchShiftedReciprocalMoment 1 n).re =
      -2 * (iteratedDeriv n (logDeriv xiSquaredSeamCassiniSource) 0).re /
        (n.factorial : ℝ) := by
  have hjet := neg_two_mul_cassiniLogDeriv_jet_eq_shiftedMoment n
  have hre := congrArg Complex.re hjet
  norm_num [Complex.mul_re] at hre
  have hfac : (n.factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  apply (eq_div_iff hfac).2
  linear_combination -hre

/-- Intrinsic one-function form of the last power-64 transverse charge. -/
theorem xiSquaredSeamPowerThirtyTwoTransverseCharge_eq_intrinsicCassiniJetResidual :
    xiSquaredSeamPowerThirtyTwoTransverseCharge =
      4096 * xiSquaredSeamCassiniPowerSixtyFourJensenIntegral.toReal +
        (iteratedDeriv 63 (logDeriv xiSquaredSeamCassiniSource) 0).re /
          ((63 : ℕ).factorial : ℝ) := by
  rw [xiSquaredSeamPowerThirtyTwoTransverseCharge_eq_cassiniJensenResidual,
    primeArchShiftedReciprocalMoment_one_re_eq_cassiniLogDeriv_jet]
  ring

theorem intrinsicCassiniJetResidual_nonneg :
    0 ≤ 4096 * xiSquaredSeamCassiniPowerSixtyFourJensenIntegral.toReal +
      (iteratedDeriv 63 (logDeriv xiSquaredSeamCassiniSource) 0).re /
        ((63 : ℕ).factorial : ℝ) := by
  rw [← xiSquaredSeamPowerThirtyTwoTransverseCharge_eq_intrinsicCassiniJetResidual]
  exact tsum_nonneg fun _ => sq_nonneg _

theorem intrinsicCassiniJetResidual_eq_zero_iff_riemannHypothesis :
    4096 * xiSquaredSeamCassiniPowerSixtyFourJensenIntegral.toReal +
        (iteratedDeriv 63 (logDeriv xiSquaredSeamCassiniSource) 0).re /
          ((63 : ℕ).factorial : ℝ) = 0 ↔ RiemannHypothesis := by
  rw [← xiSquaredSeamPowerThirtyTwoTransverseCharge_eq_intrinsicCassiniJetResidual,
    xiSquaredSeamPowerThirtyTwoTransverseCharge_eq_zero_iff_riemannHypothesis]

/-- Reflection distance of the degree-32 shift-one Cassini divisor vector. -/
def xiSquaredSeamPowerThirtyTwoReflectionDefectEnergy : ℝ :=
  ∑' q : XiZeroCopy,
    ‖xiSquaredSeamOneCoordinate q ^ 32 -
      (starRingEnd ℂ) (xiSquaredSeamOneCoordinate q ^ 32)‖ ^ 2

theorem summable_xiSquaredSeamPowerThirtyTwoReflectionDefectEnergy :
    Summable (fun q : XiZeroCopy =>
      ‖xiSquaredSeamOneCoordinate q ^ 32 -
        (starRingEnd ℂ) (xiSquaredSeamOneCoordinate q ^ 32)‖ ^ 2) := by
  apply summable_xiSquaredSeamPowerThirtyTwoTransverseCharge.mul_left 4 |>.congr
  intro q
  exact (norm_sub_conj_sq_eq_four_im_sq _).symm

/-- The Cassini reflection defect is exactly four times the remaining transverse charge. -/
theorem xiSquaredSeamPowerThirtyTwoReflectionDefectEnergy_eq_four_mul_transverseCharge :
    xiSquaredSeamPowerThirtyTwoReflectionDefectEnergy =
      4 * xiSquaredSeamPowerThirtyTwoTransverseCharge := by
  rw [xiSquaredSeamPowerThirtyTwoReflectionDefectEnergy,
    xiSquaredSeamPowerThirtyTwoTransverseCharge]
  simp_rw [norm_sub_conj_sq_eq_four_im_sq]
  exact tsum_mul_left

/-- The intrinsic Jensen/jet residual is one quarter of an exact divisor-reflection energy. -/
theorem xiSquaredSeamPowerThirtyTwoReflectionDefectEnergy_eq_four_mul_intrinsicResidual :
    xiSquaredSeamPowerThirtyTwoReflectionDefectEnergy =
      4 * (4096 * xiSquaredSeamCassiniPowerSixtyFourJensenIntegral.toReal +
        (iteratedDeriv 63 (logDeriv xiSquaredSeamCassiniSource) 0).re /
          ((63 : ℕ).factorial : ℝ)) := by
  rw [xiSquaredSeamPowerThirtyTwoReflectionDefectEnergy_eq_four_mul_transverseCharge,
    xiSquaredSeamPowerThirtyTwoTransverseCharge_eq_intrinsicCassiniJetResidual]

/-- Vanishing of the degree-32 Cassini reflection defect is exactly RH. -/
theorem xiSquaredSeamPowerThirtyTwoReflectionDefectEnergy_eq_zero_iff_riemannHypothesis :
    xiSquaredSeamPowerThirtyTwoReflectionDefectEnergy = 0 ↔ RiemannHypothesis := by
  rw [xiSquaredSeamPowerThirtyTwoReflectionDefectEnergy_eq_four_mul_transverseCharge]
  constructor
  · intro h
    apply xiSquaredSeamPowerThirtyTwoTransverseCharge_eq_zero_iff_riemannHypothesis.mp
    nlinarith
  · intro hRH
    rw [xiSquaredSeamPowerThirtyTwoTransverseCharge_eq_zero_iff_riemannHypothesis.mpr hRH]
    norm_num

/-! ## Reflection-faithful transfer to the reciprocal-square operator -/

/-- The unconditional positive dyadic prefix makes the degree-32 power reflection-faithful on
each actual shift-one Xi atom.  This statement is false for a generic complex number. -/
theorem xiSquaredSeamOneCoordinate_pow_thirtyTwo_im_eq_zero_iff
    (q : XiZeroCopy) :
    (xiSquaredSeamOneCoordinate q ^ 32).im = 0 ↔
      (xiSquaredSeamOneCoordinate q).im = 0 := by
  let z : ℂ := xiSquaredSeamOneCoordinate q
  constructor
  · intro h32
    have h16 : (z ^ 16).im = 0 := by
      apply complex_im_eq_zero_of_re_pos_of_sq_im_eq_zero
        (by simpa only [z] using xiSquaredSeamDyadic_rung_four_pos q)
      simpa only [show (z ^ 16) ^ 2 = z ^ 32 by ring] using h32
    have h8 : (z ^ 8).im = 0 := by
      apply complex_im_eq_zero_of_re_pos_of_sq_im_eq_zero
        (by simpa only [z] using xiSquaredSeamDyadic_rung_three_pos q)
      simpa only [show (z ^ 8) ^ 2 = z ^ 16 by ring] using h16
    have h4 : (z ^ 4).im = 0 := by
      apply complex_im_eq_zero_of_re_pos_of_sq_im_eq_zero
        (by simpa only [z] using xiSquaredSeamDyadic_rung_two_pos q)
      simpa only [show (z ^ 4) ^ 2 = z ^ 8 by ring] using h8
    have h2 : (z ^ 2).im = 0 := by
      apply complex_im_eq_zero_of_re_pos_of_sq_im_eq_zero
        (by simpa only [z] using xiSquaredSeamDyadic_rung_one_pos q)
      simpa only [show (z ^ 2) ^ 2 = z ^ 4 by ring] using h4
    apply complex_im_eq_zero_of_re_pos_of_sq_im_eq_zero
      (by simpa [z] using xiSquaredSeamDyadic_rung_zero_pos q)
    exact h2
  · intro him
    have hz : z = ((z.re : ℝ) : ℂ) := by
      apply Complex.ext
      · simp
      · simpa only [z] using him
    rw [show xiSquaredSeamOneCoordinate q = z by rfl, hz]
    simpa only [← Complex.ofReal_pow, Complex.ofReal_im]

/-- The degree-32 Cassini power and the unshifted reciprocal-square coordinate have exactly the
same pointwise real fibre. -/
theorem xiSquaredSeamOneCoordinate_pow_thirtyTwo_im_eq_zero_iff_reciprocalSquare
    (q : XiZeroCopy) :
    (xiSquaredSeamOneCoordinate q ^ 32).im = 0 ↔
      (xiZeroCopyReciprocalSquare q).im = 0 := by
  rw [xiSquaredSeamOneCoordinate_pow_thirtyTwo_im_eq_zero_iff,
    ← xiShiftedReciprocalSquare_one_eq_xiSquaredSeamOneCoordinate]
  exact xiShiftedReciprocalSquare_im_eq_zero_iff (y := 1) (by norm_num) q

/-- Pointwise support-faithfulness of the degree-32 Cassini reflection defect. -/
theorem xiSquaredSeamPowerThirtyTwo_reflection_eq_iff_reciprocalSquare_reflection_eq
    (q : XiZeroCopy) :
    xiSquaredSeamOneCoordinate q ^ 32 =
        (starRingEnd ℂ) (xiSquaredSeamOneCoordinate q ^ 32) ↔
      xiZeroCopyReciprocalSquare q =
        (starRingEnd ℂ) (xiZeroCopyReciprocalSquare q) := by
  constructor
  · intro h
    have him32 : (xiSquaredSeamOneCoordinate q ^ 32).im = 0 :=
      Complex.conj_eq_iff_im.mp h.symm
    have him :=
      (xiSquaredSeamOneCoordinate_pow_thirtyTwo_im_eq_zero_iff_reciprocalSquare q).mp
        him32
    exact (Complex.conj_eq_iff_im.mpr him).symm
  · intro h
    have him : (xiZeroCopyReciprocalSquare q).im = 0 :=
      Complex.conj_eq_iff_im.mp h.symm
    have him32 :=
      (xiSquaredSeamOneCoordinate_pow_thirtyTwo_im_eq_zero_iff_reciprocalSquare q).mpr
        him
    exact (Complex.conj_eq_iff_im.mpr him32).symm

/-- A zero global Cassini reflection energy is equivalent to pointwise vanishing on every
multiplicity copy. -/
theorem xiSquaredSeamPowerThirtyTwoReflectionDefectEnergy_eq_zero_iff_forall :
    xiSquaredSeamPowerThirtyTwoReflectionDefectEnergy = 0 ↔
      ∀ q : XiZeroCopy,
        xiSquaredSeamOneCoordinate q ^ 32 =
          (starRingEnd ℂ) (xiSquaredSeamOneCoordinate q ^ 32) := by
  constructor
  · intro hzero q
    let d : XiZeroCopy → ℝ := fun r =>
      ‖xiSquaredSeamOneCoordinate r ^ 32 -
        (starRingEnd ℂ) (xiSquaredSeamOneCoordinate r ^ 32)‖ ^ 2
    have hdnonneg (r : XiZeroCopy) : 0 ≤ d r := sq_nonneg _
    have hdsum : Summable d := by
      simpa only [d] using
        summable_xiSquaredSeamPowerThirtyTwoReflectionDefectEnergy
    have hdle : d q ≤ 0 := by
      apply le_of_not_gt
      intro hdpos
      have htotal : 0 < xiSquaredSeamPowerThirtyTwoReflectionDefectEnergy := by
        rw [xiSquaredSeamPowerThirtyTwoReflectionDefectEnergy]
        exact hdsum.tsum_pos hdnonneg q hdpos
      linarith
    have hdeq : d q = 0 := le_antisymm hdle (hdnonneg q)
    have hnorm : ‖xiSquaredSeamOneCoordinate q ^ 32 -
        (starRingEnd ℂ) (xiSquaredSeamOneCoordinate q ^ 32)‖ = 0 := by
      nlinarith [show 0 ≤ ‖xiSquaredSeamOneCoordinate q ^ 32 -
        (starRingEnd ℂ) (xiSquaredSeamOneCoordinate q ^ 32)‖ from norm_nonneg _]
    exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)
  · intro h
    rw [xiSquaredSeamPowerThirtyTwoReflectionDefectEnergy]
    calc
      (∑' q : XiZeroCopy,
          ‖xiSquaredSeamOneCoordinate q ^ 32 -
            (starRingEnd ℂ) (xiSquaredSeamOneCoordinate q ^ 32)‖ ^ 2) =
          ∑' _q : XiZeroCopy, (0 : ℝ) := by
        apply tsum_congr
        intro q
        rw [← h q, sub_self, norm_zero]
        norm_num
      _ = 0 := tsum_zero

/-- A zero reciprocal-square reflection energy is likewise exactly pointwise reality. -/
theorem xiThermalSquareReflectionDefectEnergy_eq_zero_iff_forall :
    xiThermalSquareReflectionDefectEnergy = 0 ↔
      ∀ q : XiZeroCopy,
        xiZeroCopyReciprocalSquare q =
          (starRingEnd ℂ) (xiZeroCopyReciprocalSquare q) := by
  constructor
  · intro hzero q
    let d : XiZeroCopy → ℝ := fun r =>
      ‖xiZeroCopyReciprocalSquare r -
        (starRingEnd ℂ) (xiZeroCopyReciprocalSquare r)‖ ^ 2
    have hdnonneg (r : XiZeroCopy) : 0 ≤ d r := sq_nonneg _
    have hdsum : Summable d := by
      simpa only [d] using summable_xiThermalSquareReflectionDefectEnergy
    have hdle : d q ≤ 0 := by
      apply le_of_not_gt
      intro hdpos
      have htotal : 0 < xiThermalSquareReflectionDefectEnergy := by
        rw [xiThermalSquareReflectionDefectEnergy]
        exact hdsum.tsum_pos hdnonneg q hdpos
      linarith
    have hdeq : d q = 0 := le_antisymm hdle (hdnonneg q)
    have hnorm : ‖xiZeroCopyReciprocalSquare q -
        (starRingEnd ℂ) (xiZeroCopyReciprocalSquare q)‖ = 0 := by
      nlinarith [show 0 ≤ ‖xiZeroCopyReciprocalSquare q -
        (starRingEnd ℂ) (xiZeroCopyReciprocalSquare q)‖ from norm_nonneg _]
    exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)
  · intro h
    rw [xiThermalSquareReflectionDefectEnergy]
    calc
      (∑' q : XiZeroCopy,
          ‖xiZeroCopyReciprocalSquare q -
            (starRingEnd ℂ) (xiZeroCopyReciprocalSquare q)‖ ^ 2) =
          ∑' _q : XiZeroCopy, (0 : ℝ) := by
        apply tsum_congr
        intro q
        rw [← h q, sub_self, norm_zero]
        norm_num
      _ = 0 := tsum_zero

/-- The degree-32 shifted reflection energy and reciprocal-square reflection energy have the
same zero fibre by a direct pointwise proof, without passing through RH. -/
theorem xiSquaredSeamPowerThirtyTwoReflectionDefectEnergy_eq_zero_iff_thermalReflectionDefect_zero :
    xiSquaredSeamPowerThirtyTwoReflectionDefectEnergy = 0 ↔
      xiThermalSquareReflectionDefectEnergy = 0 := by
  rw [xiSquaredSeamPowerThirtyTwoReflectionDefectEnergy_eq_zero_iff_forall,
    xiThermalSquareReflectionDefectEnergy_eq_zero_iff_forall]
  exact forall_congr' fun q =>
    xiSquaredSeamPowerThirtyTwo_reflection_eq_iff_reciprocalSquare_reflection_eq q

/-! ## Exact inward theta-source boundary transport -/

/-- The centered Xi function is nonzero on the whole negative imaginary ray.  Under the centered
coordinate this is the positive real axis for completed Xi: the subunit part is covered by strict
real-anchor positivity and the remaining part by the Euler half-plane. -/
theorem XiC_neg_imaginaryAxis_ne_zero
    {t : ℝ} (ht : 0 < t) : XiC (-((t : ℂ) * I)) ≠ 0 := by
  rw [XiC]
  have harg : 1 / 2 + (-((t : ℂ) * I)) * I = ((1 / 2 + t : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
  rw [harg]
  by_cases htHalf : t < 1 / 2
  · exact xi_ne_zero_real_anchor (by linarith) (by linarith)
  · exact xi_ne_zero_of_one_le_re (by simp; linarith)

/-- Inside its genuine convergence strip, the theta-cusp Fourier--Laplace transform and centered
Xi have the same logarithmic derivative. -/
theorem logDeriv_thetaCuspFourierLaplace_eq_XiC_on_strip
    {z : ℂ} (hz : z ∈ thetaCuspFourierLaplaceStrip) :
    logDeriv thetaCuspFourierLaplace z = logDeriv XiC z := by
  have hvalue := thetaCuspFourierLaplace_eq_XiC_on_strip hz
  have hderiv :=
    iteratedDeriv_thetaCuspFourierLaplace_eq_iteratedDeriv_XiC 1 hz
  have hthetaOne : iteratedDeriv 1 thetaCuspFourierLaplace z =
      deriv thetaCuspFourierLaplace z := congrFun iteratedDeriv_one z
  have hXiOne : iteratedDeriv 1 XiC z = deriv XiC z :=
    congrFun iteratedDeriv_one z
  rw [hthetaOne, hXiOne] at hderiv
  rw [logDeriv_apply, logDeriv_apply, hvalue, hderiv]

/-- **Exact inward theta-source boundary law.**  The Euler-safe Cassini coordinate `u = 0`
lifts to the boundary point `z = -I` of the theta Fourier--Laplace strip.  For every interior
approach `0 < t < 1`, `u = 1 - t²` transports the genuine theta-source logarithmic response to
the Cassini logarithmic derivative.  Thus the shift-one moment germ is a boundary source object,
not an interior consequence of generic source positivity. -/
theorem neg_two_mul_cassiniLogDeriv_eq_thetaCuspBoundaryApproach
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    -2 * logDeriv xiSquaredSeamCassiniSource ((1 - t ^ 2 : ℝ) : ℂ) =
      (-I / (t : ℂ)) *
        logDeriv thetaCuspFourierLaplace (-((t : ℂ) * I)) := by
  let z : ℂ := -((t : ℂ) * I)
  have hz0 : z ≠ 0 := by
    dsimp only [z]
    exact neg_ne_zero.mpr
      (mul_ne_zero (ofReal_ne_zero.mpr ht0.ne') I_ne_zero)
  have hXi : XiC z ≠ 0 := XiC_neg_imaginaryAxis_ne_zero ht0
  have hstrip : z ∈ thetaCuspFourierLaplaceStrip := by
    rw [thetaCuspFourierLaplaceStrip]
    dsimp only [z]
    change -1 < (-((t : ℂ) * I)).im ∧ (-((t : ℂ) * I)).im < 1
    simp only [neg_im, mul_im, ofReal_re, I_im, ofReal_im, I_re, mul_zero,
      add_zero]
    exact ⟨by linarith, by linarith⟩
  have hchain :=
    logDeriv_XiC_eq_two_mul_xiSquaredSeamCassiniSource hz0 hXi
  have hsq : 1 + z ^ 2 = ((1 - t ^ 2 : ℝ) : ℂ) := by
    dsimp only [z]
    apply Complex.ext
    all_goals simp [pow_two, mul_re, mul_im] <;> ring_nf
  rw [hsq] at hchain
  have htheta := logDeriv_thetaCuspFourierLaplace_eq_XiC_on_strip hstrip
  rw [← htheta] at hchain
  rw [hchain]
  dsimp only [z]
  field_simp [ofReal_ne_zero.mpr ht0.ne']
  rw [I_sq]
  ring

/-- Genuine theta-source response written in the Cassini coordinate `u = 1 - t²`.  Only its
restriction to `0 < u < 1` is used; there the square root lies strictly inside the theta strip. -/
def thetaCuspCassiniInwardCoordinateResponse (u : ℝ) : ℂ :=
  (-I / (Real.sqrt (1 - u) : ℂ)) *
    logDeriv thetaCuspFourierLaplace
      (-((Real.sqrt (1 - u) : ℂ) * I))

/-- Pointwise square-root reparameterization of the inward theta-boundary law. -/
theorem thetaCuspCassiniInwardCoordinateResponse_eq_cassiniLogDeriv
    {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    thetaCuspCassiniInwardCoordinateResponse u =
      -2 * logDeriv xiSquaredSeamCassiniSource (u : ℂ) := by
  have honeSub : 0 ≤ 1 - u := by linarith
  have ht0 : 0 < Real.sqrt (1 - u) :=
    Real.sqrt_pos.2 (by linarith)
  have ht1 : Real.sqrt (1 - u) < 1 :=
    (Real.sqrt_lt' one_pos).2 (by nlinarith)
  have hboundary :=
    neg_two_mul_cassiniLogDeriv_eq_thetaCuspBoundaryApproach ht0 ht1
  have hsquare : Real.sqrt (1 - u) ^ 2 = 1 - u := Real.sq_sqrt honeSub
  rw [hsquare] at hboundary
  have hucoord : 1 - (1 - u) = u := by ring
  rw [hucoord] at hboundary
  exact hboundary.symm

/-- **Boundary-germ source weld.**  On a punctured right neighborhood of the Euler-safe Cassini
center, the genuine theta-source boundary response is exactly the analytic shift-one moment germ.
Consequently all Taylor data of the latter are fixed by this inward source trace. -/
theorem thetaCuspCassiniInwardCoordinateResponse_eventuallyEq_momentGerm :
    thetaCuspCassiniInwardCoordinateResponse =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun u : ℝ => xiSquaredSeamCassiniMomentGerm (u : ℂ)) := by
  have hlt : ∀ᶠ u : ℝ in nhdsWithin 0 (Set.Ioi 0), u < 1 :=
    eventually_nhdsWithin_of_eventually_nhds (Iio_mem_nhds zero_lt_one)
  have hpos : ∀ᶠ u : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < u := by
    exact self_mem_nhdsWithin
  have htheta :
      thetaCuspCassiniInwardCoordinateResponse =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
        (fun u : ℝ => -2 *
          logDeriv xiSquaredSeamCassiniSource (u : ℂ)) := by
    filter_upwards [hpos, hlt] with u hu0 hu1
    exact thetaCuspCassiniInwardCoordinateResponse_eq_cassiniLogDeriv hu0 hu1
  have hofReal : Tendsto (fun u : ℝ => (u : ℂ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    Complex.continuous_ofReal.continuousAt.tendsto.mono_left inf_le_left
  have hmoment := hofReal.eventually negTwoCassiniLogDeriv_eventuallyEq_momentGerm
  exact htheta.trans hmoment

/-- An analytic germ at the Cassini center which continues the genuine inward theta-source
response.  The continuation is required only on the positive real side, where the square-root
coordinate stays inside the Fourier--Laplace strip. -/
def IsThetaCuspCassiniInwardAnalyticExtension (F : ℂ → ℂ) : Prop :=
  AnalyticAt ℂ F 0 ∧
    (fun u : ℝ => F (u : ℂ)) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      thetaCuspCassiniInwardCoordinateResponse

/-- The prime--Gamma shift-one moment germ is an analytic continuation of the genuine inward
theta-source response. -/
theorem isThetaCuspCassiniInwardAnalyticExtension_momentGerm :
    IsThetaCuspCassiniInwardAnalyticExtension xiSquaredSeamCassiniMomentGerm := by
  exact ⟨analyticAt_xiSquaredSeamCassiniMomentGerm,
    thetaCuspCassiniInwardCoordinateResponse_eventuallyEq_momentGerm.symm⟩

/-- **One-sided boundary-germ uniqueness.**  Two analytic continuations of the genuine inward
theta-source response agree on a full complex neighborhood of the Cassini center.  Thus no
choice of analytic extension can alter the prime--Gamma moment jets. -/
theorem IsThetaCuspCassiniInwardAnalyticExtension.eventuallyEq
    {F G : ℂ → ℂ}
    (hF : IsThetaCuspCassiniInwardAnalyticExtension F)
    (hG : IsThetaCuspCassiniInwardAnalyticExtension G) :
    F =ᶠ[nhds 0] G := by
  have hreal : (fun u : ℝ => F (u : ℂ)) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun u : ℝ => G (u : ℂ)) := hF.2.trans hG.2.symm
  let u : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have huReal : Tendsto u atTop (nhds 0) := by
    simpa [u] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have huPos : ∀ n : ℕ, u n ∈ Set.Ioi (0 : ℝ) := by
    intro n
    dsimp only [u]
    change 0 < 1 / ((n : ℝ) + 1)
    positivity
  have huRealWithin : Tendsto u atTop (nhdsWithin 0 (Set.Ioi 0)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨huReal, Filter.Eventually.of_forall huPos⟩
  have heq : ∀ᶠ n : ℕ in atTop, F (u n : ℂ) = G (u n : ℂ) :=
    huRealWithin.eventually hreal
  have huComplex : Tendsto (fun n : ℕ => (u n : ℂ)) atTop (nhds 0) := by
    have hcomp := Complex.continuous_ofReal.continuousAt.tendsto.comp huReal
    simpa [Function.comp_def] using hcomp
  have huNe (n : ℕ) : (u n : ℂ) ≠ 0 := by
    exact ofReal_ne_zero.mpr (ne_of_gt (huPos n))
  have huComplexWithin : Tendsto (fun n : ℕ => (u n : ℂ)) atTop
      (nhdsWithin 0 ({0} : Set ℂ)ᶜ) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨huComplex,
      Filter.Eventually.of_forall (fun n => by simpa using huNe n)⟩
  have hfreq : ∃ᶠ w in nhdsWithin 0 ({0} : Set ℂ)ᶜ, F w = G w :=
    huComplexWithin.frequently heq.frequently
  exact (hF.1.frequently_eq_iff_eventually_eq hG.1).mp hfreq

/-- Every analytic continuation of the genuine inward theta response is the shift-one
prime--Gamma moment germ near the Cassini center. -/
theorem IsThetaCuspCassiniInwardAnalyticExtension.eventuallyEq_momentGerm
    {F : ℂ → ℂ} (hF : IsThetaCuspCassiniInwardAnalyticExtension F) :
    F =ᶠ[nhds 0] xiSquaredSeamCassiniMomentGerm :=
  hF.eventuallyEq isThetaCuspCassiniInwardAnalyticExtension_momentGerm

/-- Every analytic continuation of the genuine inward theta response has the complete
shift-one prime--Gamma moment sequence as its Taylor jets. -/
theorem IsThetaCuspCassiniInwardAnalyticExtension.iteratedDeriv_eq_shiftedMoment
    {F : ℂ → ℂ} (hF : IsThetaCuspCassiniInwardAnalyticExtension F) (n : ℕ) :
    iteratedDeriv n F 0 =
      ((n.factorial : ℕ) : ℂ) * primeArchShiftedReciprocalMoment 1 n := by
  rw [hF.eventuallyEq_momentGerm.iteratedDeriv_eq,
    iteratedDeriv_xiSquaredSeamCassiniMomentGerm]

/-- Near the Cassini center, the logarithmic derivative of the canonical entire source is the
genuine inward theta response. -/
theorem negTwoCassiniLogDeriv_eventuallyEq_thetaCuspInwardResponse :
    (fun u : ℝ => -2 *
      logDeriv xiSquaredSeamCassiniSource (u : ℂ)) =ᶠ[
        nhdsWithin 0 (Set.Ioi 0)]
      thetaCuspCassiniInwardCoordinateResponse := by
  have hofReal : Tendsto (fun u : ℝ => (u : ℂ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    Complex.continuous_ofReal.continuousAt.tendsto.mono_left inf_le_left
  have hCassini : (fun u : ℝ => -2 *
      logDeriv xiSquaredSeamCassiniSource (u : ℂ)) =ᶠ[
        nhdsWithin 0 (Set.Ioi 0)]
      (fun u : ℝ => xiSquaredSeamCassiniMomentGerm (u : ℂ)) :=
    hofReal.eventually negTwoCassiniLogDeriv_eventuallyEq_momentGerm
  exact hCassini.trans
    thetaCuspCassiniInwardCoordinateResponse_eventuallyEq_momentGerm.symm

/-- An entire source normalized at the Euler-safe Cassini center and having the genuine inward
theta response as its boundary logarithmic derivative. -/
def IsThetaCuspCassiniEntireSource (F : ℂ → ℂ) : Prop :=
  Differentiable ℂ F ∧
    F 0 = xiSquaredSeamCassiniSource 0 ∧
      (fun u : ℝ => -2 * logDeriv F (u : ℂ)) =ᶠ[
        nhdsWithin 0 (Set.Ioi 0)]
        thetaCuspCassiniInwardCoordinateResponse

/-- The canonical Cassini entire function realizes the normalized theta-boundary source law. -/
theorem isThetaCuspCassiniEntireSource_cassiniSource :
    IsThetaCuspCassiniEntireSource xiSquaredSeamCassiniSource := by
  exact ⟨differentiable_xiSquaredSeamCassiniSource, rfl,
    negTwoCassiniLogDeriv_eventuallyEq_thetaCuspInwardResponse⟩

/-- The logarithmic response of any normalized theta--Cassini entire source is the unique
prime--Gamma moment germ near the Cassini center. -/
theorem IsThetaCuspCassiniEntireSource.negTwoLogDeriv_eventuallyEq_momentGerm
    {F : ℂ → ℂ} (hF : IsThetaCuspCassiniEntireSource F) :
    (fun u : ℂ => -2 * logDeriv F u) =ᶠ[nhds 0]
      xiSquaredSeamCassiniMomentGerm := by
  have hF0 : F 0 ≠ 0 := by
    rw [hF.2.1]
    exact xiSquaredSeamCassiniSource_zero_ne
  have hFan : AnalyticAt ℂ F 0 := hF.1.analyticAt 0
  have hlog : AnalyticAt ℂ (logDeriv F) 0 := by
    rw [show logDeriv F = fun z => deriv F z / F z by rfl]
    exact hFan.deriv.div hFan hF0
  have hresponse : IsThetaCuspCassiniInwardAnalyticExtension
      (fun u : ℂ => -2 * logDeriv F u) := by
    exact ⟨analyticAt_const.mul hlog, hF.2.2⟩
  exact hresponse.eventuallyEq_momentGerm

/-- **Global theta-source reconstruction.**  The normalized entire Cassini source is uniquely
determined by its genuine one-sided inward theta logarithmic response.  Therefore both its local
prime--Gamma jets and its global Jensen divisor functional come from one boundary datum; there is
no residual source/response continuation choice. -/
theorem IsThetaCuspCassiniEntireSource.eq_cassiniSource
    {F : ℂ → ℂ} (hF : IsThetaCuspCassiniEntireSource F) :
    F = xiSquaredSeamCassiniSource := by
  have hF0 : F 0 ≠ 0 := by
    rw [hF.2.1]
    exact xiSquaredSeamCassiniSource_zero_ne
  have hFne : ∀ᶠ u : ℂ in nhds 0, F u ≠ 0 :=
    hF.1.continuous.continuousAt.eventually_ne hF0
  have hCassiniNe : ∀ᶠ u : ℂ in nhds 0,
      xiSquaredSeamCassiniSource u ≠ 0 :=
    differentiable_xiSquaredSeamCassiniSource.continuous.continuousAt.eventually_ne
      xiSquaredSeamCassiniSource_zero_ne
  have hnegEq : (fun u : ℂ => -2 * logDeriv F u) =ᶠ[nhds 0]
      (fun u : ℂ => -2 * logDeriv xiSquaredSeamCassiniSource u) :=
    hF.negTwoLogDeriv_eventuallyEq_momentGerm.trans
      negTwoCassiniLogDeriv_eventuallyEq_momentGerm.symm
  have hlogEq : logDeriv F =ᶠ[nhds 0]
      logDeriv xiSquaredSeamCassiniSource := by
    filter_upwards [hnegEq] with u hu
    exact mul_left_cancel₀ (by norm_num : (-2 : ℂ) ≠ 0) hu
  have hall : {u : ℂ | logDeriv F u =
        logDeriv xiSquaredSeamCassiniSource u ∧
      F u ≠ 0 ∧ xiSquaredSeamCassiniSource u ≠ 0} ∈ nhds 0 := by
    filter_upwards [hlogEq, hFne, hCassiniNe] with u hlog hFu hCassiniU
    exact ⟨hlog, hFu, hCassiniU⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hall
  have hEqOnLog : Set.EqOn (logDeriv F)
      (logDeriv xiSquaredSeamCassiniSource) (Metric.ball 0 r) :=
    fun u hu => (hball hu).1
  have hFdiff : DifferentiableOn ℂ F (Metric.ball 0 r) :=
    hF.1.differentiableOn
  have hCassiniDiff : DifferentiableOn ℂ xiSquaredSeamCassiniSource
      (Metric.ball 0 r) :=
    differentiable_xiSquaredSeamCassiniSource.differentiableOn
  obtain ⟨c, hc0, hc⟩ :=
    (logDeriv_eqOn_iff hFdiff hCassiniDiff Metric.isOpen_ball
      (convex_ball (0 : ℂ) r).isPreconnected
      (fun u hu => (hball hu).2.2) (fun u hu => (hball hu).2.1)).mp hEqOnLog
  have hzeroMem : (0 : ℂ) ∈ Metric.ball 0 r := Metric.mem_ball_self hr
  have hcOne : c = 1 := by
    apply mul_right_cancel₀ xiSquaredSeamCassiniSource_zero_ne
    have hcenter := hc hzeroMem
    simpa only [Pi.smul_apply, smul_eq_mul, one_mul, hF.2.1] using hcenter.symm
  have hlocalOn : Set.EqOn F xiSquaredSeamCassiniSource (Metric.ball 0 r) := by
    intro u hu
    simpa only [Pi.smul_apply, smul_eq_mul, hcOne, one_mul] using hc hu
  have hlocal : F =ᶠ[nhds 0] xiSquaredSeamCassiniSource :=
    hlocalOn.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hzeroMem)
  have hFan : AnalyticOnNhd ℂ F Set.univ :=
    hF.1.differentiableOn.analyticOnNhd isOpen_univ
  have hCassiniAn : AnalyticOnNhd ℂ xiSquaredSeamCassiniSource Set.univ :=
    differentiable_xiSquaredSeamCassiniSource.differentiableOn.analyticOnNhd
      isOpen_univ
  have hglobal := hFan.eqOn_of_preconnected_of_eventuallyEq hCassiniAn
    isPreconnected_univ (Set.mem_univ 0) hlocal
  funext u
  exact hglobal (Set.mem_univ u)

/-- The degree-63 normalized jet of every analytic inward theta extension is the fixed
shift-one prime--Gamma moment. -/
theorem IsThetaCuspCassiniInwardAnalyticExtension.normalizedJet_sixtyThree_eq_moment_re
    {F : ℂ → ℂ} (hF : IsThetaCuspCassiniInwardAnalyticExtension F) :
    (iteratedDeriv 63 F 0).re / (((63 : ℕ).factorial : ℕ) : ℝ) =
      (primeArchShiftedReciprocalMoment 1 63).re := by
  rw [hF.iteratedDeriv_eq_shiftedMoment]
  norm_num [Complex.mul_re]

/-- **Pure theta-boundary saturation Prop.**  The global Cassini--Jensen mass is dominated by
the normalized degree-63 jet of every analytic continuation of the genuine inward theta
response.  One-sided germ uniqueness makes the universal quantifier extension-independent. -/
def ThetaCuspCassiniInwardBoundarySaturated : Prop :=
  ∀ F : ℂ → ℂ, IsThetaCuspCassiniInwardAnalyticExtension F →
    8192 * xiSquaredSeamCassiniPowerSixtyFourJensenIntegral.toReal ≤
      (iteratedDeriv 63 F 0).re / (((63 : ℕ).factorial : ℕ) : ℝ)

/-- The theta-boundary saturation Prop is exactly the earlier Cassini reverse source law. -/
theorem thetaCuspCassiniInwardBoundarySaturated_iff_cassiniJensenDominated :
    ThetaCuspCassiniInwardBoundarySaturated ↔
      XiSquaredSeamCassiniJensenDominated := by
  constructor
  · intro h
    have hmoment := h xiSquaredSeamCassiniMomentGerm
      isThetaCuspCassiniInwardAnalyticExtension_momentGerm
    rw [isThetaCuspCassiniInwardAnalyticExtension_momentGerm
      |>.normalizedJet_sixtyThree_eq_moment_re] at hmoment
    exact hmoment
  · intro hdom F hF
    rw [hF.normalizedJet_sixtyThree_eq_moment_re]
    exact hdom

/-- **Rightmost genuine theta-source RH endpoint.**  Boundary saturation of the actual inward
theta response, with no zero enumeration and no analytic-extension ambiguity, is equivalent to
the Riemann hypothesis. -/
theorem thetaCuspCassiniInwardBoundarySaturated_iff_riemannHypothesis :
    ThetaCuspCassiniInwardBoundarySaturated ↔ RiemannHypothesis :=
  thetaCuspCassiniInwardBoundarySaturated_iff_cassiniJensenDominated.trans
    xiSquaredSeamCassiniJensenDominated_iff_riemannHypothesis

/-- Cassini--Jensen domination is directly the zero fibre of the transverse charge. -/
theorem xiSquaredSeamCassiniJensenDominated_iff_transverseCharge_zero :
    XiSquaredSeamCassiniJensenDominated ↔
      xiSquaredSeamPowerThirtyTwoTransverseCharge = 0 := by
  rw [XiSquaredSeamCassiniJensenDominated,
    xiSquaredSeamCassiniPowerSixtyFourJensenIntegral_toReal]
  have hcancel : 8192 *
      (xiSquaredSeamPowerSixtyFourHermitianMass / 8192) =
        xiSquaredSeamPowerSixtyFourHermitianMass := by ring
  rw [hcancel]
  exact xiSquaredSeamPowerSixtyFourSourceDominated_iff_transverseCharge_zero

/-- The Cassini reflection energy has zero fibre exactly when its transverse charge vanishes. -/
theorem xiSquaredSeamPowerThirtyTwoReflectionDefectEnergy_eq_zero_iff_transverseCharge_zero :
    xiSquaredSeamPowerThirtyTwoReflectionDefectEnergy = 0 ↔
      xiSquaredSeamPowerThirtyTwoTransverseCharge = 0 := by
  rw [xiSquaredSeamPowerThirtyTwoReflectionDefectEnergy_eq_four_mul_transverseCharge]
  constructor <;> intro h <;> nlinarith

/-- Boundary saturation is precisely vanishing of the degree-32 Cassini vector's
anti-conjugation energy. -/
theorem thetaCuspCassiniInwardBoundarySaturated_iff_reflectionDefect_zero :
    ThetaCuspCassiniInwardBoundarySaturated ↔
      xiSquaredSeamPowerThirtyTwoReflectionDefectEnergy = 0 :=
  thetaCuspCassiniInwardBoundarySaturated_iff_cassiniJensenDominated.trans
    (xiSquaredSeamCassiniJensenDominated_iff_transverseCharge_zero.trans
      xiSquaredSeamPowerThirtyTwoReflectionDefectEnergy_eq_zero_iff_transverseCharge_zero.symm)

/-- **Direct right-to-left operator weld.**  Theta-boundary saturation is exactly vanishing of
the established reciprocal-square reflection energy.  The proof uses the pointwise faithful
degree-32 transfer, not either theorem's RH equivalence. -/
theorem thetaCuspCassiniInwardBoundarySaturated_iff_thermalReflectionDefect_zero :
    ThetaCuspCassiniInwardBoundarySaturated ↔
      xiThermalSquareReflectionDefectEnergy = 0 :=
  thetaCuspCassiniInwardBoundarySaturated_iff_reflectionDefect_zero.trans
    xiSquaredSeamPowerThirtyTwoReflectionDefectEnergy_eq_zero_iff_thermalReflectionDefect_zero

/-- Operator form of the direct weld: the inward theta boundary is saturated exactly when the
anti-Hermitian part of the reciprocal-square Hilbert--Schmidt kernel has zero energy. -/
theorem thetaCuspCassiniInwardBoundarySaturated_iff_reciprocalSquareKernel_adjointDefect_zero :
    ThetaCuspCassiniInwardBoundarySaturated ↔
      HilbertSchmidt.hsNormSq
        (HilbertSchmidt.hsPow xiReciprocalDiagonalKernel 1 -
          HilbertSchmidt.hsAdjoint
            (HilbertSchmidt.hsPow xiReciprocalDiagonalKernel 1)) = 0 := by
  rw [xiReciprocalSquareKernel_adjointDefect_hsNormSq_eq_reflectionEnergy]
  exact thetaCuspCassiniInwardBoundarySaturated_iff_thermalReflectionDefect_zero

/-! ## Countable Cauchy zero-fibre connector -/

/-- **Direct operator/source zero-fibre weld.**  The anti-Hermitian Hilbert--Schmidt energy of
the reciprocal-square kernel vanishes exactly when every regular Gaussian-rational continued-
Cauchy quadratic defect vanishes.  Neither direction invokes an RH equivalence: forward passage
uses the kernel/operator adjoint intertwiner, while reverse passage uses countable Cauchy density
and horizontal pole exhaustion to orient every exact multiplicity fibre. -/
theorem xiReciprocalSquareKernel_adjointDefect_zero_iff_gaussianRatOrientationDefectsVanish :
    HilbertSchmidt.hsNormSq
        (HilbertSchmidt.hsPow xiReciprocalDiagonalKernel 1 -
          HilbertSchmidt.hsAdjoint
            (HilbertSchmidt.hsPow xiReciprocalDiagonalKernel 1)) = 0 ↔
      XiReciprocalSquareGaussianRatOrientationDefectsVanish := by
  let K := HilbertSchmidt.hsPow xiReciprocalDiagonalKernel 1
  have hK : HilbertSchmidt.IsHS K :=
    HilbertSchmidt.isHS_hsPow isHS_xiReciprocalDiagonalKernel 1
  have hAdjNeg : HilbertSchmidt.IsHS (-HilbertSchmidt.hsAdjoint K) := by
    simpa using (HilbertSchmidt.isHS_hsAdjoint hK).smul (-1)
  have hdefect : HilbertSchmidt.IsHS (K - HilbertSchmidt.hsAdjoint K) := by
    simpa [sub_eq_add_neg] using hK.add hAdjNeg
  constructor
  · intro hzero
    have hkernel : K - HilbertSchmidt.hsAdjoint K = 0 :=
      (HilbertSchmidt.hsNormSq_eq_zero_iff hdefect).mp hzero
    have hKadj : HilbertSchmidt.hsAdjoint K = K :=
      (sub_eq_zero.mp hkernel).symm
    have hself : IsSelfAdjoint xiReciprocalSquareOperator := by
      rw [← toOperator_xiReciprocalDiagonalKernel_sq]
      rw [ContinuousLinearMap.isSelfAdjoint_iff']
      rw [HilbertSchmidt.adjoint_toOperator hK]
      exact HilbertSchmidt.toOperator_congr _ _ hKadj
    intro q
    exact (xiReciprocalSquareGaussianRatOrientationDefect_eq_zero_iff q).mpr
      (hself.isSymmetric
        (xiWeilGaussianRatContinuedCauchyLp q)
        (xiWeilGaussianRatContinuedCauchyLp q))
  · intro hvanish
    have hquadratic : XiReciprocalSquareGaussianRatCauchyQuadraticReal :=
      xiReciprocalSquareGaussianRatOrientationDefectsVanish_iff_quadraticReal.mp
        hvanish
    have hone : XiReciprocalSquareOneCauchyQuadraticReal :=
      xiReciprocalSquareOneCauchyQuadraticReal_of_gaussianRat hquadratic
    have hstar (q : XiZeroCopy) :
        (starRingEnd ℂ) (xiZeroCopyReciprocalSquare q) =
          xiZeroCopyReciprocalSquare q :=
      xiZeroCopyReciprocalSquare_star_eq_of_oneCauchyQuadraticReal hone q
    apply (HilbertSchmidt.hsNormSq_eq_zero_iff hdefect).mpr
    rw [xiReciprocalSquareKernel_sub_adjoint_eq_diagMul]
    funext p
    rcases p with ⟨q, r⟩
    by_cases hqr : q = r
    · subst r
      simp [HilbertSchmidt.diagMul, hstar q]
    · simp [HilbertSchmidt.diagMul, hqr]

/-- The theta-boundary endpoint is now connected directly to a countable family of exact scalar
continued-source defects, without routing either implication through RH. -/
theorem thetaCuspCassiniInwardBoundarySaturated_iff_gaussianRatOrientationDefectsVanish :
    ThetaCuspCassiniInwardBoundarySaturated ↔
      XiReciprocalSquareGaussianRatOrientationDefectsVanish :=
  thetaCuspCassiniInwardBoundarySaturated_iff_reciprocalSquareKernel_adjointDefect_zero.trans
    xiReciprocalSquareKernel_adjointDefect_zero_iff_gaussianRatOrientationDefectsVanish

/-- Equivalent countable quadratic-value form of the direct theta/source weld. -/
theorem thetaCuspCassiniInwardBoundarySaturated_iff_gaussianRatCauchyQuadraticReal :
    ThetaCuspCassiniInwardBoundarySaturated ↔
      XiReciprocalSquareGaussianRatCauchyQuadraticReal :=
  thetaCuspCassiniInwardBoundarySaturated_iff_gaussianRatOrientationDefectsVanish.trans
    xiReciprocalSquareGaussianRatOrientationDefectsVanish_iff_quadraticReal

/-! ## Fixed off-axis Cauchy-pole connector -/

/-- **Direct operator/single-source zero-fibre weld.**  The reciprocal-square anti-Hermitian
kernel energy vanishes exactly when the one concrete Cauchy orientation defect at `1/4+i/4`
vanishes.  The reverse implication uses the explicit quartet-variance rigidity theorem to orient
every spectral fibre; neither direction invokes an RH equivalence. -/
theorem xiReciprocalSquareKernel_adjointDefect_zero_iff_fixedCauchyOrientationDefectZero :
    HilbertSchmidt.hsNormSq
        (HilbertSchmidt.hsPow xiReciprocalDiagonalKernel 1 -
          HilbertSchmidt.hsAdjoint
            (HilbertSchmidt.hsPow xiReciprocalDiagonalKernel 1)) = 0 ↔
      XiReciprocalSquareFixedCauchyOrientationDefectZero := by
  let K := HilbertSchmidt.hsPow xiReciprocalDiagonalKernel 1
  have hK : HilbertSchmidt.IsHS K :=
    HilbertSchmidt.isHS_hsPow isHS_xiReciprocalDiagonalKernel 1
  have hAdjNeg : HilbertSchmidt.IsHS (-HilbertSchmidt.hsAdjoint K) := by
    simpa using (HilbertSchmidt.isHS_hsAdjoint hK).smul (-1)
  have hdefect : HilbertSchmidt.IsHS (K - HilbertSchmidt.hsAdjoint K) := by
    simpa [sub_eq_add_neg] using hK.add hAdjNeg
  constructor
  · intro hzero
    have hkernel : K - HilbertSchmidt.hsAdjoint K = 0 :=
      (HilbertSchmidt.hsNormSq_eq_zero_iff hdefect).mp hzero
    have hKadj : HilbertSchmidt.hsAdjoint K = K :=
      (sub_eq_zero.mp hkernel).symm
    have hself : IsSelfAdjoint xiReciprocalSquareOperator := by
      rw [← toOperator_xiReciprocalDiagonalKernel_sq]
      rw [ContinuousLinearMap.isSelfAdjoint_iff']
      rw [HilbertSchmidt.adjoint_toOperator hK]
      exact HilbertSchmidt.toOperator_congr _ _ hKadj
    unfold XiReciprocalSquareFixedCauchyOrientationDefectZero
    exact
      (xiReciprocalSquareContinuedCauchyOrientationDefect_eq_zero_iff_quadraticReal
        xiReciprocalSquareFixedCauchyPole).mpr
        (hself.isSymmetric
          (xiWeilContinuedCauchyLp xiReciprocalSquareFixedCauchyPole)
          (xiWeilContinuedCauchyLp xiReciprocalSquareFixedCauchyPole))
  · intro hfixed
    have him (q : XiZeroCopy) : (xiSpectralPoint q).im = 0 := by
      apply
        xiSpectralPoint_im_eq_zero_of_continuedCauchyOrientationDefect_eq_zero
          xiReciprocalSquareFixedCauchyPole
      · norm_num
      · norm_num
      · exact hfixed
    have hstar (q : XiZeroCopy) :
        (starRingEnd ℂ) (xiZeroCopyReciprocalSquare q) =
          xiZeroCopyReciprocalSquare q := by
      have hspectral :
          (starRingEnd ℂ) (xiSpectralPoint q) = xiSpectralPoint q :=
        Complex.conj_eq_iff_im.mpr (him q)
      rw [xiZeroCopyReciprocalSquare, map_pow, map_inv₀, hspectral]
    apply (HilbertSchmidt.hsNormSq_eq_zero_iff hdefect).mpr
    rw [xiReciprocalSquareKernel_sub_adjoint_eq_diagMul]
    funext p
    rcases p with ⟨q, r⟩
    by_cases hqr : q = r
    · subst r
      simp [HilbertSchmidt.diagMul, hstar q]
    · simp [HilbertSchmidt.diagMul, hqr]

/-- Direct collapse of the countable Gaussian-rational defect family to one concrete scalar
defect, through their common operator zero fibre and without an RH detour. -/
theorem xiReciprocalSquareFixedCauchyOrientationDefectZero_iff_gaussianRatOrientationDefectsVanish :
    XiReciprocalSquareFixedCauchyOrientationDefectZero ↔
      XiReciprocalSquareGaussianRatOrientationDefectsVanish :=
  xiReciprocalSquareKernel_adjointDefect_zero_iff_fixedCauchyOrientationDefectZero.symm.trans
    xiReciprocalSquareKernel_adjointDefect_zero_iff_gaussianRatOrientationDefectsVanish

/-- The full Cassini/theta endpoint is welded directly to one concrete source scalar. -/
theorem thetaCuspCassiniInwardBoundarySaturated_iff_fixedCauchyOrientationDefectZero :
    ThetaCuspCassiniInwardBoundarySaturated ↔
      XiReciprocalSquareFixedCauchyOrientationDefectZero :=
  thetaCuspCassiniInwardBoundarySaturated_iff_reciprocalSquareKernel_adjointDefect_zero.trans
    xiReciprocalSquareKernel_adjointDefect_zero_iff_fixedCauchyOrientationDefectZero

end

end RHTower
