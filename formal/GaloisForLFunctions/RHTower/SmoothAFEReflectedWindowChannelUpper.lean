import GaloisForLFunctions.RHTower.SteinhausGaussianIndependentCutoffMean
import GaloisForLFunctions.RHTower.SmoothAFEReflectedTruncatedGaussianTransfer
import GaloisForLFunctions.RHTower.SmoothAFEReflectedChannelUpper



open Filter Topology Finset Complex
noncomputable section
namespace RHTower

private theorem norm_cutoff_eq_re {x : ℝ} (hx : 0 < x) :
    ‖smoothAFECutoff x‖ = (smoothAFECutoff x).re := by
  have heq : smoothAFECutoff x = ((smoothAFECutoff x).re : ℂ) := by
    apply Complex.ext <;> simp [smoothAFECutoff_im_eq_zero hx]
  rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (smoothAFECutoff_re_nonneg hx)]
  rfl

/-- All truncated cofactor responses are uniformly bounded on every bounded positive
real scale range, in all phases and at every polynomial cutoff. -/
theorem exists_truncatedFullGaussianCofactor_norm_bound
    {s : ℂ} (hs : 0 < s.re) (hs1 : s.re < 1) {U : ℕ} (hU : 0 < U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → R ≤ U → ∀ L : ℕ, ∀ ω : SteinhausModel.Omega,
      ‖truncatedFullGaussianCofactor s R L ω‖ ≤ C := by
  obtain ⟨C, hC, hsum⟩ := exists_sum_norm_gaussian_direct_le
    (sub_pos.mpr hs1) (by linarith : 1 - s.re < 1)
  refine ⟨C * (U : ℝ) ^ s.re, by positivity, ?_⟩
  intro R hR hRU L ω
  have hUR : (0 : ℝ) < U := by exact_mod_cast hU
  calc
    _ ≤ ∑ n ∈ range L, ‖SteinhausModel.X (n + 1) ω * ((n + 1 : ℕ) : ℂ) ^ (s - 1) *
        smoothAFECutoff (((n + 1 : ℕ) : ℝ) / R)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ range L, ‖((n + 1 : ℕ) : ℂ) ^ (-((1 - s.re : ℝ) : ℂ)) *
        smoothAFECutoff (((n + 1 : ℕ) : ℝ) / U)‖ := by
      apply sum_le_sum
      intro n _
      have hn : 0 < n + 1 := by omega
      have hnR : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
      rw [norm_mul, norm_mul, SteinhausModel.norm_X, one_mul,
        Complex.norm_natCast_cpow_of_pos hn, Complex.sub_re, Complex.one_re,
        norm_mul, Complex.norm_natCast_cpow_of_pos hn, Complex.neg_re, Complex.ofReal_re,
        show -(1 - s.re) = s.re - 1 by ring]
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hnR.le _)
      rw [norm_cutoff_eq_re (div_pos hnR hR), norm_cutoff_eq_re (div_pos hnR hUR)]
      exact smoothAFECutoff_re_antitoneOn (div_pos hnR hUR) (div_pos hnR hR)
        (div_le_div_of_nonneg_left hnR.le hR hRU)
    _ ≤ _ := by simpa only [show 1 - (1 - s.re) = s.re by ring] using hsum U hU L

/-- Restricting free primes to (N/D,N] keeps each literal reflected channel at square-root
conductor size, uniformly over every independent polynomial cutoff. -/
theorem exists_reflectedPrimalWindowChannel_upper
    {d : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2) {D : ℕ} (hD : 0 < D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {N p : ℕ}, 0 < N → p ∈ largePrimes N (N / D) →
      ∀ L : ℕ, ∀ tau : ℝ, (N : ℝ) ≤ tau → ∀ ω,
      ‖steinhausLargePrimeChannel
        (smoothAFEZetaRightReflectedPrimalPositiveCoefficient d tau 1 N) L p ω‖ ≤
        C * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨C, hC, hchi⟩ := exists_norm_zetaChi_fixed_right_line_le_rpow hd hdhalf
  obtain ⟨B, hB, hcofactor⟩ := exists_truncatedFullGaussianCofactor_norm_bound
    (s := rightDisplacedLinePt d 0) (by rw [rightDisplacedLinePt_re]; linarith)
    (by rw [rightDisplacedLinePt_re]; linarith) hD
  refine ⟨C * (D : ℝ) ^ (1 / 2 - d) * B, by positivity, ?_⟩
  intro N p hN hp L tau htau ω
  obtain ⟨⟨hpN, hprime⟩, hpD⟩ := mem_largePrimes.mp hp
  have hNp : N < D * p := by
    simpa only [Nat.mul_comm] using (Nat.div_lt_iff_lt_mul hD).mp hpD
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hpR : (0 : ℝ) < p := by exact_mod_cast hprime.pos
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hNmax : (N : ℝ) ≤ max 1 |tau| := htau.trans ((le_abs_self _).trans (le_max_right _ _))
  have hchiN : ‖zetaChi (rightDisplacedLinePt d tau)‖ ≤ C / (N : ℝ) ^ d :=
    (hchi tau).trans (div_le_div_of_nonneg_left hC (by positivity)
      (Real.rpow_le_rpow hNR.le hNmax hd.le))
  have hratio : (N : ℝ) / D ≤ p := by
    rw [div_le_iff₀ hDR]
    exact_mod_cast (by simpa only [Nat.mul_comm] using hNp.le)
  have hRupper : (N : ℝ) / p ≤ D := by
    rw [div_le_iff₀ hpR]
    exact_mod_cast hNp.le
  have hpow : (p : ℝ) ^ (d - 1 / 2) ≤ ((N : ℝ) / D) ^ (d - 1 / 2) :=
    Real.rpow_le_rpow_of_nonpos (div_pos hNR hDR) hratio (by linarith)
  have hre : (rightDisplacedLinePt d tau - 1).re = d - 1 / 2 := by
    rw [Complex.sub_re, rightDisplacedLinePt_re, Complex.one_re]
    ring
  have hfactor := reflectedPrimalChannel_eq_truncatedFullGaussianCofactor d 0 tau N L p hN hprime.pos ω
  simp only [add_zero] at hfactor
  rw [hfactor, norm_mul, norm_mul, Complex.norm_natCast_cpow_of_pos hprime.pos, hre]
  calc
    _ ≤ ((C / (N : ℝ) ^ d) * ((N : ℝ) / D) ^ (d - 1 / 2)) * B :=
      mul_le_mul (mul_le_mul hchiN hpow (by positivity) (by positivity))
        (hcofactor ((N : ℝ) / p) (div_pos hNR hpR) hRupper (L / p) _) (norm_nonneg _) (by positivity)
    _ = _ := by
      rw [Real.div_rpow hNR.le hDR.le, div_eq_mul_inv, div_eq_mul_inv,
        ← Real.rpow_neg hNR.le, ← Real.rpow_neg hDR.le,
        show -(d - 1 / 2) = 1 / 2 - d by ring]
      calc
        _ = (C * (D : ℝ) ^ (1 / 2 - d) * B) *
            ((N : ℝ) ^ (-d) * (N : ℝ) ^ (d - 1 / 2)) := by ring
        _ = _ := by rw [← Real.rpow_add hNR]; congr 2; ring

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

theorem exists_eventually_reflectedPrimalWindowChannel_dot_upper
    {J : ℕ} (d b : Fin J → ℝ)
    (hd : ∀ j, 0 < d j) (hdhalf : ∀ j, d j < 1 / 2) {D : ℕ} (hD : 0 < D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop,
      ∀ tau ∈ Set.Icc ((5 / 4 : ℝ) * N) ((7 / 4 : ℝ) * N),
      ∀ L : ℕ, ∀ omega, ∀ u : Fin J → ℂ,
      ∀ p ∈ largePrimes N (N / D),
        ‖∑ j, steinhausLargePrimeChannel
          (smoothAFEZetaRightReflectedPrimalPositiveCoefficient (d j) (tau + b j) 1 N)
          L p omega * u j‖ ≤ C * (N : ℝ) ^ (-(1 / 2 : ℝ)) * ‖u‖ := by
  classical
  choose C hC hchannel using fun j => exists_reflectedPrimalWindowChannel_upper
    (hd j) (hdhalf j) hD
  refine ⟨∑ j, C j, sum_nonneg (fun j _ => hC j), ?_⟩
  have hoffset : ∀ᶠ N : ℕ in atTop, ∀ j, 4 * |b j| ≤ (N : ℝ) := by
    apply Filter.eventually_all.mpr
    intro j
    exact (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop).eventually
      (eventually_ge_atTop (4 * |b j|))
  filter_upwards [hoffset, eventually_ge_atTop 1] with N hbN hN
  intro tau htau L omega u p hp
  calc
    _ ≤ ∑ j, ‖steinhausLargePrimeChannel
        (smoothAFEZetaRightReflectedPrimalPositiveCoefficient (d j) (tau + b j) 1 N)
        L p omega * u j‖ := norm_sum_le _ _
    _ ≤ ∑ j, C j * (N : ℝ) ^ (-(1 / 2 : ℝ)) * ‖u‖ := by
      apply sum_le_sum
      intro j _
      rw [norm_mul]
      have ht : (N : ℝ) ≤ tau + b j := by
        have hb := hbN j
        have hlo := neg_abs_le (b j)
        linarith [htau.1]
      exact mul_le_mul (hchannel j (by omega) hp L _ ht omega)
        (norm_le_pi_norm u j) (norm_nonneg _)
        (mul_nonneg (hC j) (Real.rpow_nonneg (Nat.cast_nonneg N) _))
    _ = _ := by rw [sum_mul, sum_mul]

/-- The conditional covariance upper envelope is uniform in phase, independent polynomial cutoff, and direction. -/
theorem exists_eventually_reflectedPrimalWindowConditional_energy_upper
    {J : ℕ} (d b : Fin J → ℝ)
    (hd : ∀ j, 0 < d j) (hdhalf : ∀ j, d j < 1 / 2) {D : ℕ} (hD : 0 < D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop,
      ∀ tau ∈ Set.Icc ((5 / 4 : ℝ) * N) ((7 / 4 : ℝ) * N),
      ∀ L : ℕ, ∀ omega, ∀ u : Fin J → ℂ,
        (∑ p ∈ largePrimes N (N / D),
          ‖∑ j, steinhausLargePrimeChannel
            (smoothAFEZetaRightReflectedPrimalPositiveCoefficient (d j) (tau + b j) 1 N)
            L p omega * u j‖ ^ 2) ≤ C / Real.log N * ‖u‖ ^ 2 := by
  obtain ⟨C, hC, hchannel⟩ :=
    exists_eventually_reflectedPrimalWindowChannel_dot_upper d b hd hdhalf hD
  refine ⟨2 * C ^ 2, by positivity, ?_⟩
  filter_upwards [hchannel, eventually_primeCounting_le_twice, eventually_ge_atTop 2]
    with N hchannelN hcount hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hcard : ((largePrimes N (N / D)).card : ℝ) ≤ 2 * N / Real.log N := by
    refine le_trans ?_ hcount
    exact_mod_cast (show (largePrimes N (N / D)).card ≤ Nat.primeCounting N from
      (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Nat.primesLE_card_eq_primeCounting N))
  intro tau htau L omega u
  have hsquare : ((N : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 = (N : ℝ)⁻¹ := by
    rw [← Real.rpow_mul_natCast hNR.le]
    norm_num [Real.rpow_neg_one]
  calc
    _ ≤ ∑ _p ∈ largePrimes N (N / D),
        (C * (N : ℝ) ^ (-(1 / 2 : ℝ)) * ‖u‖) ^ 2 := by
      apply sum_le_sum
      intro p hp
      exact pow_le_pow_left₀ (norm_nonneg _) (hchannelN tau htau L omega u p hp) 2
    _ = ((largePrimes N (N / D)).card : ℝ) * (C ^ 2 * (N : ℝ)⁻¹ * ‖u‖ ^ 2) := by
      simp only [Finset.sum_const, nsmul_eq_mul, mul_pow, hsquare]
    _ ≤ (2 * N / Real.log N) * (C ^ 2 * (N : ℝ)⁻¹ * ‖u‖ ^ 2) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = (2 * C ^ 2) / Real.log N * ‖u‖ ^ 2 := by field_simp


end RHTower
