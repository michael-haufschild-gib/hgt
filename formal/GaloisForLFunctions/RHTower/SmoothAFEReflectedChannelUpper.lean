import GaloisForLFunctions.RHTower.SmoothAFECofactorCellStability
import GaloisForLFunctions.RHTower.SmoothAFEZetaChiPowerBound
import GaloisForLFunctions.HTGeometry.AbelianZetaGas.PrimeWindowCount

/-!
# Uniform fixed-cofactor upper bounds for literal reflected-AFE channels

At a fixed cofactor cutoff, every actual channel is bounded by a constant times
`N^(-1/2)`, uniformly over phases and positive Gaussian smoothing scales. Prime
counting then gives a conditional energy bound of order `1/log N`, also for every
finite-node coefficient direction throughout the common-height window.

The nonsmooth remainder of the actual carrier has an exact arithmetic second moment
and the same vanishing mean-square bound. These estimates supply the small-channel
and large-prime remainder inputs for the independent recurrence producer. They do
not assert full-carrier low-moment decay, a local target law, or deterministic recurrence.
-/

noncomputable section
open Filter Topology Finset Complex
namespace RHTower

/-- Every coefficient in a fixed cofactor range has the square-root conductor envelope. -/
theorem exists_reflectedPrimalPositiveCoefficient_fixedCofactor_upper
    {d : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2) {D : ℕ} (hD : 0 < D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {N n : ℕ}, 0 < N → 0 < n → N ≤ D * n →
      ∀ tau : ℝ, (N : ℝ) ≤ tau → ∀ r : ℝ, 0 < r →
      ‖smoothAFEZetaRightReflectedPrimalPositiveCoefficient d tau r N n‖ ≤
        C * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨C, hC, hchi⟩ := exists_norm_zetaChi_fixed_right_line_le_rpow hd hdhalf
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  refine ⟨C * (D : ℝ) ^ (1 / 2 - d), by positivity, ?_⟩
  intro N n hN hn hNn tau htau r hr
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hNmax : (N : ℝ) ≤ max 1 |tau| := htau.trans ((le_abs_self _).trans (le_max_right _ _))
  have hchiN : ‖zetaChi (rightDisplacedLinePt d tau)‖ ≤ C / (N : ℝ) ^ d := by
    exact (hchi tau).trans (div_le_div_of_nonneg_left hC (by positivity)
      (Real.rpow_le_rpow hNR.le hNmax hd.le))
  have hratio : (N : ℝ) / D ≤ n := by
    rw [div_le_iff₀ hDR]
    exact_mod_cast (by simpa [Nat.mul_comm] using hNn)
  have hpow : (n : ℝ) ^ (d - 1 / 2) ≤ ((N : ℝ) / D) ^ (d - 1 / 2) :=
    Real.rpow_le_rpow_of_nonpos (div_pos hNR hDR) hratio (by linarith)
  have hre : (rightDisplacedLinePt d tau - 1).re = d - 1 / 2 := by
    rw [Complex.sub_re, rightDisplacedLinePt_re, Complex.one_re]
    ring
  rw [reflectedPrimalPositiveCoefficient_eq_power_cutoff _ _ _ _ hn,
    norm_mul, norm_mul, Complex.norm_natCast_cpow_of_pos hn, hre]
  calc
    _ ≤ (C / (N : ℝ) ^ d) * ((N : ℝ) / D) ^ (d - 1 / 2) * 1 :=
      mul_le_mul (mul_le_mul hchiN hpow (by positivity) (by positivity))
        (norm_smoothAFECutoff_le_one (mul_pos hr (div_pos hnR hNR))) (norm_nonneg _) (by positivity)
    _ = (C * (D : ℝ) ^ (1 / 2 - d)) * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
      rw [mul_one, Real.div_rpow hNR.le hDR.le, div_eq_mul_inv, div_eq_mul_inv,
        ← Real.rpow_neg hNR.le, ← Real.rpow_neg hDR.le]
      have he : -(d - 1 / 2) = 1 / 2 - d := by ring
      rw [he]
      calc
        _ = C * (D : ℝ) ^ (1 / 2 - d) *
            ((N : ℝ) ^ (-d) * (N : ℝ) ^ (d - 1 / 2)) := by ring
        _ = _ := by rw [← Real.rpow_add hNR]; congr 2; ring

/-- Uniform bound for each literal large-prime channel, with a fixed cofactor cutoff. -/
theorem exists_reflectedPrimalLargePrimeChannel_upper
    {d : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2) {D : ℕ} (hD : 0 < D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {N p : ℕ}, 0 < N → p ∈ largePrimes N (N / D) →
      ∀ tau : ℝ, (N : ℝ) ≤ tau → ∀ r : ℝ, 0 < r → ∀ omega,
      ‖steinhausLargePrimeChannel
        (smoothAFEZetaRightReflectedPrimalPositiveCoefficient d tau r N) N p omega‖ ≤
        C * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨C, hC, hcoeff⟩ :=
    exists_reflectedPrimalPositiveCoefficient_fixedCofactor_upper hd hdhalf hD
  refine ⟨D * C, by positivity, ?_⟩
  intro N p hN hp tau htau r hr omega
  obtain ⟨⟨hpN, hprime⟩, hpD⟩ := mem_largePrimes.mp hp
  have hNp : N < D * p := by
    simpa [Nat.mul_comm] using (Nat.div_lt_iff_lt_mul hD).mp hpD
  have hLD : N / p ≤ D := by
    have : N / p < D := (Nat.div_lt_iff_lt_mul hprime.pos).mpr (by simpa [Nat.mul_comm] using hNp)
    omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  calc
    _ ≤ ∑ m ∈ Icc 1 (N / p),
        ‖smoothAFEZetaRightReflectedPrimalPositiveCoefficient d tau r N (p * m) *
          SteinhausModel.X m omega‖ := norm_sum_le _ _
    _ ≤ ∑ _m ∈ Icc 1 (N / p), C * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
      apply sum_le_sum
      intro m hm
      have hmpos : 0 < m := (mem_Icc.mp hm).1
      rw [norm_mul, SteinhausModel.norm_X, mul_one]
      exact hcoeff hN (Nat.mul_pos hprime.pos hmpos)
        (hNp.le.trans (Nat.mul_le_mul_left D (by simpa using Nat.mul_le_mul_left p hmpos))) tau htau r hr
    _ = (N / p : ℕ) * (C * (N : ℝ) ^ (-(1 / 2 : ℝ))) := by simp
    _ ≤ (D : ℝ) * (C * (N : ℝ) ^ (-(1 / 2 : ℝ))) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hLD) (by positivity)
    _ = _ := by ring

private theorem eventually_primeCounting_le_twice :
    ∀ᶠ N : ℕ in atTop, (Nat.primeCounting N : ℝ) ≤ 2 * N / Real.log N := by
  have h := GaloisForLFunctions.HTGeometry.isLittleO_primeCounting_sub.bound (c := 1) zero_lt_one
  have hnat := (tendsto_natCast_atTop_atTop :
    Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop).eventually h
  filter_upwards [hnat, eventually_ge_atTop 2] with N hN hN2
  have hNR : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hmain : 0 < (N : ℝ) / Real.log N := div_pos (by linarith) (Real.log_pos hNR)
  simp only [Nat.floor_natCast, Real.norm_eq_abs, one_mul, abs_of_pos hmain] at hN
  have hupper := (abs_le.mp hN).2
  rw [mul_div_assoc]
  linarith

/-- The total literal channel energy is uniformly `O(1/log N)` for any fixed cutoff. -/
theorem exists_reflectedPrimalLargePrimeChannel_energy_upper
    {d : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2) {D : ℕ} (hD : 0 < D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop,
      ∀ tau : ℝ, (N : ℝ) ≤ tau → ∀ r : ℝ, 0 < r → ∀ omega,
      (∑ p ∈ largePrimes N (N / D),
        ‖steinhausLargePrimeChannel
          (smoothAFEZetaRightReflectedPrimalPositiveCoefficient d tau r N) N p omega‖ ^ 2)
        ≤ C / Real.log N := by
  obtain ⟨C, hC, hchannel⟩ := exists_reflectedPrimalLargePrimeChannel_upper hd hdhalf hD
  refine ⟨2 * C ^ 2, by positivity, ?_⟩
  filter_upwards [eventually_primeCounting_le_twice, eventually_ge_atTop 2] with N hcount hN
  have hNpos : 0 < N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hcard : ((largePrimes N (N / D)).card : ℝ) ≤ 2 * N / Real.log N := by
    refine le_trans ?_ hcount
    exact_mod_cast (show (largePrimes N (N / D)).card ≤ Nat.primeCounting N from
      (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Nat.primesLE_card_eq_primeCounting N))
  intro tau htau r hr omega
  have hsquare : ((N : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 = (N : ℝ)⁻¹ := by
    rw [← Real.rpow_mul_natCast hNR.le]
    norm_num [Real.rpow_neg_one]
  calc
    _ ≤ ∑ _p ∈ largePrimes N (N / D), (C * (N : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 := by
      apply Finset.sum_le_sum
      intro p hp
      exact pow_le_pow_left₀ (norm_nonneg _) (hchannel hNpos hp tau htau r hr omega) 2
    _ = ((largePrimes N (N / D)).card : ℝ) * (C ^ 2 * (N : ℝ)⁻¹) := by
      simp only [Finset.sum_const, nsmul_eq_mul, mul_pow, hsquare]
    _ ≤ (2 * N / Real.log N) * (C ^ 2 * (N : ℝ)⁻¹) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = (2 * C ^ 2) / Real.log N := by field_simp

/-- Simultaneous maximal-channel control for every fixed node and every coefficient direction. -/
theorem exists_eventually_reflectedPrimalChannel_dot_upper
    {J : ℕ} (d b : Fin J → ℝ)
    (hd : ∀ j, 0 < d j) (hdhalf : ∀ j, d j < 1 / 2) {D : ℕ} (hD : 0 < D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop,
      ∀ tau ∈ Set.Icc ((5 / 4 : ℝ) * N) ((7 / 4 : ℝ) * N),
      ∀ r : ℝ, 0 < r → ∀ omega, ∀ u : Fin J → ℂ,
      ∀ p ∈ largePrimes N (N / D),
        ‖∑ j, steinhausLargePrimeChannel
          (smoothAFEZetaRightReflectedPrimalPositiveCoefficient (d j) (tau + b j) r N)
          N p omega * u j‖ ≤ C * (N : ℝ) ^ (-(1 / 2 : ℝ)) * ‖u‖ := by
  classical
  choose C hC hchannel using fun j => exists_reflectedPrimalLargePrimeChannel_upper
    (hd j) (hdhalf j) hD
  refine ⟨∑ j, C j, sum_nonneg (fun j _ => hC j), ?_⟩
  have hoffset : ∀ᶠ N : ℕ in atTop, ∀ j, 4 * |b j| ≤ (N : ℝ) := by
    apply Filter.eventually_all.mpr
    intro j
    exact (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop).eventually
      (eventually_ge_atTop (4 * |b j|))
  filter_upwards [hoffset, eventually_ge_atTop 1] with N hbN hN
  intro tau htau r hr omega u p hp
  calc
    _ ≤ ∑ j, ‖steinhausLargePrimeChannel
        (smoothAFEZetaRightReflectedPrimalPositiveCoefficient (d j) (tau + b j) r N)
        N p omega * u j‖ := norm_sum_le _ _
    _ ≤ ∑ j, C j * (N : ℝ) ^ (-(1 / 2 : ℝ)) * ‖u‖ := by
      apply sum_le_sum
      intro j _
      rw [norm_mul]
      have ht : (N : ℝ) ≤ tau + b j := by
        have hb := hbN j
        have hlo := neg_abs_le (b j)
        linarith [htau.1]
      exact mul_le_mul (hchannel j (by omega) hp _ ht r hr omega)
        (norm_le_pi_norm u j) (norm_nonneg _)
        (mul_nonneg (hC j) (Real.rpow_nonneg (Nat.cast_nonneg N) _))
    _ = _ := by rw [sum_mul, sum_mul]

/-- The conditional covariance upper envelope is uniform in phase, smoothing, and direction. -/
theorem exists_eventually_reflectedPrimalConditional_energy_upper
    {J : ℕ} (d b : Fin J → ℝ)
    (hd : ∀ j, 0 < d j) (hdhalf : ∀ j, d j < 1 / 2) {D : ℕ} (hD : 0 < D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop,
      ∀ tau ∈ Set.Icc ((5 / 4 : ℝ) * N) ((7 / 4 : ℝ) * N),
      ∀ r : ℝ, 0 < r → ∀ omega, ∀ u : Fin J → ℂ,
        (∑ p ∈ largePrimes N (N / D),
          ‖∑ j, steinhausLargePrimeChannel
            (smoothAFEZetaRightReflectedPrimalPositiveCoefficient (d j) (tau + b j) r N)
            N p omega * u j‖ ^ 2) ≤ C / Real.log N * ‖u‖ ^ 2 := by
  obtain ⟨C, hC, hchannel⟩ :=
    exists_eventually_reflectedPrimalChannel_dot_upper d b hd hdhalf hD
  refine ⟨2 * C ^ 2, by positivity, ?_⟩
  filter_upwards [hchannel, eventually_primeCounting_le_twice, eventually_ge_atTop 2]
    with N hchannelN hcount hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hcard : ((largePrimes N (N / D)).card : ℝ) ≤ 2 * N / Real.log N := by
    refine le_trans ?_ hcount
    exact_mod_cast (show (largePrimes N (N / D)).card ≤ Nat.primeCounting N from
      (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Nat.primesLE_card_eq_primeCounting N))
  intro tau htau r hr omega u
  have hsquare : ((N : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 = (N : ℝ)⁻¹ := by
    rw [← Real.rpow_mul_natCast hNR.le]
    norm_num [Real.rpow_neg_one]
  calc
    _ ≤ ∑ _p ∈ largePrimes N (N / D),
        (C * (N : ℝ) ^ (-(1 / 2 : ℝ)) * ‖u‖) ^ 2 := by
      apply sum_le_sum
      intro p hp
      exact pow_le_pow_left₀ (norm_nonneg _) (hchannelN tau htau r hr omega u p hp) 2
    _ = ((largePrimes N (N / D)).card : ℝ) * (C ^ 2 * (N : ℝ)⁻¹ * ‖u‖ ^ 2) := by
      simp only [Finset.sum_const, nsmul_eq_mul, mul_pow, hsquare]
    _ ≤ (2 * N / Real.log N) * (C ^ 2 * (N : ℝ)⁻¹ * ‖u‖ ^ 2) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = (2 * C ^ 2) / Real.log N * ‖u‖ ^ 2 := by field_simp

/-- Fixed-cofactor conditional energy vanishes uniformly, with all quantifiers retained. -/
theorem eventually_reflectedPrimalConditional_energy_le
    {J : ℕ} (d b : Fin J → ℝ)
    (hd : ∀ j, 0 < d j) (hdhalf : ∀ j, d j < 1 / 2) {D : ℕ} (hD : 0 < D)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      ∀ tau ∈ Set.Icc ((5 / 4 : ℝ) * N) ((7 / 4 : ℝ) * N),
      ∀ r : ℝ, 0 < r → ∀ omega, ∀ u : Fin J → ℂ,
        (∑ p ∈ largePrimes N (N / D),
          ‖∑ j, steinhausLargePrimeChannel
            (smoothAFEZetaRightReflectedPrimalPositiveCoefficient (d j) (tau + b j) r N)
            N p omega * u j‖ ^ 2) ≤ ε * ‖u‖ ^ 2 := by
  obtain ⟨C, _, henergy⟩ :=
    exists_eventually_reflectedPrimalConditional_energy_upper d b hd hdhalf hD
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hdecay : Tendsto (fun N : ℕ => C / Real.log N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlog
  filter_upwards [henergy, hdecay.eventually (gt_mem_nhds hε)] with N henergyN hsmall
  intro tau htau r hr omega u
  exact (henergyN tau htau r hr omega u).trans
    (mul_le_mul_of_nonneg_right hsmall.le (sq_nonneg _))


/-- The actual nonsmooth remainder has exactly the arithmetic large-prime coefficient mass. -/
theorem integral_normSq_steinhausCarrier_sub_smooth
    (a : ℕ → ℂ) (N Y : ℕ) (hNY : N < Y * Y) :
    (∫ omega, ‖(∑ n ∈ Icc 1 N, a n * SteinhausModel.X n omega) -
      steinhausSmoothCarrier a N Y omega‖ ^ 2 ∂SteinhausModel.steinhausMeasure) =
      ∑ p ∈ largePrimes N Y, ∑ m ∈ Icc 1 (N / p), ‖a (p * m)‖ ^ 2 := by
  classical
  have hsub : Sieve.smoothUpTo (Nat.primesLE Y) N ⊆ Icc 1 N := by
    intro n hn
    exact Finset.mem_Icc.mpr (mem_smoothUpTo_iff.mp hn).1
  have hpoint : ∀ omega,
      (∑ n ∈ Icc 1 N, a n * SteinhausModel.X n omega) -
        steinhausSmoothCarrier a N Y omega =
      ∑ n ∈ (Icc 1 N) \ Sieve.smoothUpTo (Nat.primesLE Y) N,
        a n * SteinhausModel.X n omega := by
    intro omega
    exact (eq_sub_iff_add_eq.mpr (Finset.sum_sdiff
      (f := fun n => a n * SteinhausModel.X n omega) hsub)).symm
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun omega =>
    congrArg (fun z : ℂ => ‖z‖ ^ 2) (hpoint omega)))]
  rw [SteinhausModel.integral_normSq_dpoly_complex _ _ (by
    intro n hn
    exact Nat.ne_of_gt (mem_Icc.mp (mem_sdiff.mp hn).1).1)]
  have hsum := Finset.sum_sdiff (f := fun n => ‖a n‖ ^ 2) hsub
  have hmass := sum_Icc_eq_smooth_add_largePrimeSigma (fun n => ‖a n‖ ^ 2) N Y hNY
  rw [Finset.sum_sigma] at hmass
  linarith

/-- Uniform mean-square decay of the actual carrier minus its fixed-cofactor smooth background. -/
theorem exists_reflectedPrimalCarrier_sub_smooth_meanSquare_upper
    {d : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2) {D : ℕ} (hD : 0 < D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop,
      ∀ tau : ℝ, (N : ℝ) ≤ tau → ∀ r : ℝ, 0 < r →
      (∫ omega,
        ‖(∑ n ∈ Icc 1 N,
          smoothAFEZetaRightReflectedPrimalPositiveCoefficient d tau r N n *
            SteinhausModel.X n omega) -
          steinhausSmoothCarrier
            (smoothAFEZetaRightReflectedPrimalPositiveCoefficient d tau r N) N (N / D) omega‖ ^ 2
        ∂SteinhausModel.steinhausMeasure) ≤ C / Real.log N := by
  obtain ⟨C, hC, hcoeff⟩ :=
    exists_reflectedPrimalPositiveCoefficient_fixedCofactor_upper hd hdhalf hD
  refine ⟨2 * D * C ^ 2, by positivity, ?_⟩
  have hseam : ∀ᶠ N : ℕ in atTop, N < (N / D) * (N / D) := by
    filter_upwards [eventually_ge_atTop (4 * D * D)] with N hN
    have hquot : 2 * D ≤ N / D := (Nat.le_div_iff_mul_le hD).mpr (by nlinarith)
    have hNlt := Nat.lt_mul_div_succ N hD
    have hD1 : D ≤ N / D - 1 := by omega
    nlinarith
  filter_upwards [eventually_primeCounting_le_twice, hseam, eventually_ge_atTop 2]
    with N hcount hseamN hN
  have hNpos : 0 < N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hcard : ((largePrimes N (N / D)).card : ℝ) ≤ 2 * N / Real.log N := by
    refine le_trans ?_ hcount
    exact_mod_cast (show (largePrimes N (N / D)).card ≤ Nat.primeCounting N from
      (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Nat.primesLE_card_eq_primeCounting N))
  intro tau htau r hr
  rw [integral_normSq_steinhausCarrier_sub_smooth _ _ _ hseamN]
  have hsquare : ((N : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 = (N : ℝ)⁻¹ := by
    rw [← Real.rpow_mul_natCast hNR.le]
    norm_num [Real.rpow_neg_one]
  calc
    _ ≤ ∑ _p ∈ largePrimes N (N / D), (D : ℝ) * (C ^ 2 * (N : ℝ)⁻¹) := by
      apply sum_le_sum
      intro p hp
      obtain ⟨⟨_, hprime⟩, hpD⟩ := mem_largePrimes.mp hp
      have hNp : N < D * p := by
        simpa [Nat.mul_comm] using (Nat.div_lt_iff_lt_mul hD).mp hpD
      have hLD : N / p ≤ D := by
        have : N / p < D := (Nat.div_lt_iff_lt_mul hprime.pos).mpr
          (by simpa [Nat.mul_comm] using hNp)
        omega
      calc
        _ ≤ ∑ _m ∈ Icc 1 (N / p), (C * (N : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 := by
          apply sum_le_sum
          intro m hm
          have hmpos : 0 < m := (mem_Icc.mp hm).1
          exact pow_le_pow_left₀ (norm_nonneg _) (hcoeff hNpos (Nat.mul_pos hprime.pos hmpos)
            (hNp.le.trans (Nat.mul_le_mul_left D (by simpa using Nat.mul_le_mul_left p hmpos)))
            tau htau r hr) 2
        _ = (N / p : ℕ) * (C ^ 2 * (N : ℝ)⁻¹) := by
          simp only [Finset.sum_const, nsmul_eq_mul, mul_pow, hsquare, Nat.card_Icc,
            Nat.add_sub_cancel, ]
        _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hLD) (by positivity)
    _ = ((largePrimes N (N / D)).card : ℝ) * ((D : ℝ) * (C ^ 2 * (N : ℝ)⁻¹)) := by simp
    _ ≤ (2 * N / Real.log N) * ((D : ℝ) * (C ^ 2 * (N : ℝ)⁻¹)) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by field_simp

end RHTower
