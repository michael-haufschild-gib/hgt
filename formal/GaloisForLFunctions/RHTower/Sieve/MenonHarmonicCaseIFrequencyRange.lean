import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicCaseIIFrequencyRange
import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicPrimeScaledBound
import GaloisForLFunctions.RHTower.Sieve.TwoRangeHighBound

namespace RHTower.Sieve

open Filter Topology

noncomputable section

theorem eventually_cardLength_nineteen_twentieth_le_menonFinalRangePrimeCutoffNat :
    ∀ᶠ x : ℝ in atTop,
      cardLength ((19 : ℝ) / 20) x ≤ (menonFinalRangePrimeCutoffNat x : ℝ) := by
  have hsmall := tendsto_logLog_div_logRpow (δ := (1 : ℝ) / 20) (by norm_num)
  filter_upwards [Tendsto.eventually_le_const (show (0 : ℝ) < 1 / 160 by norm_num) hsmall,
    Filter.eventually_gt_atTop (Real.exp (Real.exp (Real.exp 1))),
    (tendsto_cardLength (show (0 : ℝ) < (19 : ℝ) / 20 by norm_num)).eventually_ge_atTop 2]
      with x hsmall hx hcard
  have hx0 : (0 : ℝ) < x := lt_trans (by positivity) hx
  have hlogLower : Real.exp (Real.exp 1) < Real.log x :=
    (Real.lt_log_iff_exp_lt hx0).2 hx
  have hlog0 : (0 : ℝ) < Real.log x := lt_trans (by positivity) hlogLower
  have hllLower : Real.exp 1 < Real.log (Real.log x) :=
    (Real.lt_log_iff_exp_lt hlog0).2 hlogLower
  have hll0 : (0 : ℝ) < Real.log (Real.log x) := lt_trans (by positivity) hllLower
  have hlll : (1 : ℝ) ≤ Real.log (Real.log (Real.log x)) := by
    have := (Real.lt_log_iff_exp_lt hll0).2 hllLower
    exact this.le
  have hp : (0 : ℝ) < (Real.log x) ^ ((1 : ℝ) / 20) :=
    Real.rpow_pos_of_pos hlog0 _
  have hll : 160 * Real.log (Real.log x) ≤ (Real.log x) ^ ((1 : ℝ) / 20) := by
    rw [div_le_iff₀ hp] at hsmall
    nlinarith
  have hmain : 2 * (Real.log x) ^ ((19 : ℝ) / 20) ≤
      (Real.log x / 80) *
        (Real.log (Real.log (Real.log x)) / Real.log (Real.log x)) := by
    have hpow19 : (Real.log x) ^ ((19 : ℝ) / 20) *
        (Real.log x) ^ ((1 : ℝ) / 20) = Real.log x := by
      rw [← Real.rpow_add hlog0]
      norm_num
    rw [show (Real.log x / 80) *
        (Real.log (Real.log (Real.log x)) / Real.log (Real.log x)) =
      ((Real.log x / 80) * Real.log (Real.log (Real.log x))) /
        Real.log (Real.log x) by ring]
    rw [le_div_iff₀ hll0]
    have hstep := mul_le_mul_of_nonneg_left hll
      (Real.rpow_nonneg hlog0.le ((19 : ℝ) / 20))
    rw [← mul_assoc, hpow19] at hstep
    have hlllStep := mul_le_mul_of_nonneg_left hlll (by positivity :
      (0 : ℝ) ≤ Real.log x / 80)
    nlinarith
  have hcut : cardLength ((19 : ℝ) / 20) x ^ (2 : ℕ) ≤
      menonFinalRangePrimeCutoff x := by
    rw [cardLength, menonFinalRangePrimeCutoff, ← Real.exp_nat_mul]
    exact Real.exp_le_exp.2 (by simpa [two_mul] using hmain)
  have hplus : cardLength ((19 : ℝ) / 20) x + 1 ≤
      menonFinalRangePrimeCutoff x := by
    have hsq : cardLength ((19 : ℝ) / 20) x + 1 ≤
        cardLength ((19 : ℝ) / 20) x ^ (2 : ℕ) := by
      nlinarith [cardLength_pos ((19 : ℝ) / 20) x]
    exact hsq.trans hcut
  have hfloor := Nat.lt_floor_add_one (menonFinalRangePrimeCutoff x)
  rw [menonFinalRangePrimeCutoffNat]
  exact le_of_lt (by exact_mod_cast (show
    cardLength ((19 : ℝ) / 20) x <
      ((⌊menonFinalRangePrimeCutoff x⌋₊ : ℕ) : ℝ) from by linarith))

theorem menonFinalRangePrimeCutoffNat_le_blockLower
    {x : ℝ} {j : ℕ} (heta : 0 ≤ menonFinalRangeLadderEta x) :
    menonFinalRangePrimeCutoffNat x ≤ menonFinalRangeBlockLowerNat x j := by
  rw [menonFinalRangeBlockLowerNat, ← Nat.floor_natCast (R := ℝ)
    (menonFinalRangePrimeCutoffNat x)]
  apply Nat.floor_mono
  rw [menonFinalRangeLadderBase]
  have hstep : 1 ≤ 1 + menonFinalRangeLadderEta x := by linarith
  have hpow : 1 ≤ (1 + menonFinalRangeLadderEta x) ^ j := one_le_pow₀ hstep
  exact le_mul_of_one_le_right (by positivity) hpow

theorem eventually_twoRangeT0_le_menonHarmonicCaseIIFrequencyCeiling :
    ∀ᶠ x : ℝ in atTop,
      ∀ j ∈ Finset.range (menonFinalRangeLadderSteps x),
        twoRangeT₀ 2 100 x ≤
          menonHarmonicCaseIIFrequencyCeiling (menonFinalRangeBlockLowerNat x j) := by
  let kappa : ℝ := menonHarmonicCaseIICoreExponent
  have hk : 0 < kappa := by
    simpa only [kappa] using menonHarmonicCaseIICoreExponent_pos
  have hdecay : Tendsto (fun x : ℝ => (4 / 3 : ℝ) *
      ((Real.log x) ^ (311 : ℝ) *
        Real.exp (-(kappa * (Real.log x) ^ ((19 : ℝ) / 20))))) atTop (𝓝 0) := by
    simpa using ((tendsto_logRpow_mul_expSaving
      (d := (19 : ℝ) / 20) (s := kappa)
      (by norm_num) hk 311).const_mul ((4 : ℝ) / 3))
  filter_upwards [eventually_cardLength_nineteen_twentieth_le_menonFinalRangePrimeCutoffNat,
    eventually_menonFinalRangeLadder_basic,
    Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1) hdecay,
    Filter.eventually_gt_atTop (1 : ℝ)] with x hcut hbasic hsmall hx
  intro j hj
  have heta : 0 ≤ menonFinalRangeLadderEta x := hbasic.2.2.2.2.1
  let a : ℕ := menonFinalRangeBlockLowerNat x j
  have hca : cardLength ((19 : ℝ) / 20) x ≤ (a : ℝ) := by
    exact hcut.trans (by exact_mod_cast menonFinalRangePrimeCutoffNat_le_blockLower heta)
  have hcard0 : 0 < cardLength ((19 : ℝ) / 20) x := cardLength_pos _ _
  have harpow : cardLength ((19 : ℝ) / 20) x ^ kappa ≤ (a : ℝ) ^ kappa :=
    Real.rpow_le_rpow hcard0.le hca hk.le
  have hcardpow : cardLength ((19 : ℝ) / 20) x ^ kappa =
      Real.exp (kappa * (Real.log x) ^ ((19 : ℝ) / 20)) := by
    rw [Real.rpow_def_of_pos hcard0, log_cardLength]
    congr 1
    ring
  have hlog0 : 0 < Real.log x := Real.log_pos hx
  have hrewrite : (Real.log x) ^ (311 : ℝ) *
      Real.exp (-(kappa * (Real.log x) ^ ((19 : ℝ) / 20))) =
      (Real.log x) ^ (311 : ℝ) /
        Real.exp (kappa * (Real.log x) ^ ((19 : ℝ) / 20)) := by
    rw [Real.exp_neg]
    ring
  rw [hrewrite] at hsmall
  have hexp0 : 0 < Real.exp (kappa * (Real.log x) ^ ((19 : ℝ) / 20)) := Real.exp_pos _
  have ht : twoRangeT₀ 2 100 x ≤
      (3 / 4 : ℝ) * Real.exp (kappa * (Real.log x) ^ ((19 : ℝ) / 20)) := by
    rw [twoRangeT₀]
    norm_num
    rw [← Real.rpow_natCast (Real.log x) 311]
    have hsmall' : (4 / 3 : ℝ) * (Real.log x) ^ (311 : ℝ) /
        Real.exp (kappa * (Real.log x) ^ ((19 : ℝ) / 20)) ≤ 1 := by
      simpa only [mul_div_assoc] using hsmall
    rw [div_le_iff₀ hexp0] at hsmall'
    calc
      (Real.log x) ^ (311 : ℝ) = (3 / 4 : ℝ) *
          ((4 / 3 : ℝ) * (Real.log x) ^ (311 : ℝ)) := by ring
      _ ≤ (3 / 4 : ℝ) * Real.exp (kappa * (Real.log x) ^ ((19 : ℝ) / 20)) :=
        mul_le_mul_of_nonneg_left (by simpa only [one_mul] using hsmall') (by norm_num)
  rw [menonHarmonicCaseIIFrequencyCeiling]
  rw [← show kappa = menonHarmonicCaseIICoreExponent by rfl]
  rw [hcardpow] at harpow
  nlinarith [mul_le_mul_of_nonneg_left harpow (by norm_num : (0 : ℝ) ≤ 3 / 4)]

theorem tendsto_logPow_forty_mul_menonHarmonicCaseIRelMajorant
    {A delta Ctot : ℝ} (hdelta : 0 < delta) (hCtot : 0 < Ctot) :
    Tendsto (fun x : ℝ => (Real.log x) ^ (40 : ℝ) *
      relScaledMajorant Ctot (twoRangeWidth 2 100 x) (twoRangeLx 2 x)
        (twoRangeHmaj A 2 100 ((2 : ℝ) / 3) x)
        (twoRangeMu A delta ((2 : ℝ) / 3) x)
        (twoRangeQ ((19 : ℝ) / 20) x) (twoRangeT₀ 2 100 x)
        (twoRangeXmin ((19 : ℝ) / 20) x)) atTop (𝓝 0) := by
  have hxpos : ∀ᶠ x : ℝ in atTop, 0 < twoRangeXmin ((19 : ℝ) / 20) x :=
    Filter.Eventually.of_forall fun x => twoRangeXmin_pos ((19 : ℝ) / 20) x
  have hexpq : Tendsto (fun x : ℝ =>
      (Real.log x) ^ (2 * (2 : ℝ) + 2 * 100 + 4 + 40)
        * Real.exp (-(twoRangeMu A delta ((2 : ℝ) / 3) x *
          twoRangeQ ((19 : ℝ) / 20) x))) atTop (𝓝 0) :=
    tendsto_rpow_log_mul_exp_neg_of_ge
      (c := 2 * (2 : ℝ) + 2 * 100 + 4 + 40)
      (s := (((19 : ℝ) / 20) - 9 / 10) / 2) (by norm_num)
      (twoRangeMu_mul_twoRangeQ_ge (A := A) hdelta (by norm_num)
        (by norm_num) (by norm_num))
  have hxmin : Tendsto (fun x : ℝ =>
      (Real.log x) ^ ((2 : ℝ) + 40) /
        Real.sqrt (twoRangeXmin ((19 : ℝ) / 20) x)) atTop (𝓝 0) := by
    refine (tendsto_logRpow_mul_expSaving
      (d := (19 : ℝ) / 20) (s := (1 : ℝ) / 2)
      (by norm_num) (by norm_num) ((2 : ℝ) + 40)).congr' ?_
    filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx
    have hc0 : (0 : ℝ) < cardLength ((19 : ℝ) / 20) x := cardLength_pos _ _
    have hsq : Real.sqrt (twoRangeXmin ((19 : ℝ) / 20) x) =
        Real.exp ((Real.log x) ^ ((19 : ℝ) / 20) / 2) := by
      rw [twoRangeXmin, sqrt_eq_exp_half_log hc0, log_cardLength]
    have hexp : Real.exp (-((1 : ℝ) / 2 *
        (Real.log x) ^ ((19 : ℝ) / 20))) =
        (Real.exp ((Real.log x) ^ ((19 : ℝ) / 20) / 2))⁻¹ := by
      rw [← Real.exp_neg]
      congr 1
      ring
    rw [hsq, hexp]
    exact (div_eq_mul_inv _ _).symm
  exact tendsto_logRpow_mul_relScaledMajorant
    (b := (2 : ℝ)) (A₃ := (100 : ℝ)) (Ctot := Ctot) (e := (40 : ℝ))
    (Hmaj := fun x => twoRangeHmaj A 2 100 ((2 : ℝ) / 3) x)
    (μ := fun x => twoRangeMu A delta ((2 : ℝ) / 3) x)
    (q := fun x => twoRangeQ ((19 : ℝ) / 20) x)
    (xmin := fun x => twoRangeXmin ((19 : ℝ) / 20) x)
    (by norm_num) (by norm_num) hCtot.le (by norm_num) (by norm_num) (by norm_num)
    (twoRangeHmaj_bounds (A := A) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)) hxpos hexpq hxmin

set_option maxHeartbeats 800000 in
theorem exists_absolute_eventually_norm_menonFinalRangeActualBlock_le_logPow_of_caseI_range :
    ∃ C1 : ℝ, 0 ≤ C1 ∧
      ∀ᶠ x : ℝ in atTop,
        ∀ j ∈ Finset.range (menonFinalRangeLadderSteps x),
        ∀ w : ℝ,
        menonHarmonicCaseIIFrequencyCeiling (menonFinalRangeBlockLowerNat x j) ≤
            2 * Real.pi * |w| →
        |w| ≤ twoRangeTop ((2 : ℝ) / 3) x →
        ‖harmonicPrimeBlockPoly
            (primesRange (menonFinalRangeBlockLowerNat x j)
              (menonFinalRangeActualBlockUpperNat x j)) w‖ ≤
          C1 / (Real.log (menonFinalRangeBlockLowerNat x j : ℝ)) ^ (20 : ℕ) := by
  obtain ⟨A, delta, Ctot, tau0, hdelta, hCtot, htau0, hrouteT⟩ :=
    exists_norm_harmonicPrimeBlockPoly_scaled_le
  let C1 : ℝ := (12 / Real.log 2) * (2 : ℝ) ^ (20 : ℕ)
  have hC1 : 0 ≤ C1 := by dsimp only [C1]; positivity
  refine ⟨C1, hC1, ?_⟩
  have hrelLimit := tendsto_logPow_forty_mul_menonHarmonicCaseIRelMajorant
    (A := A) (delta := delta) (Ctot := Ctot) hdelta hCtot
  have htailLimit : Tendsto (fun x : ℝ =>
      7 * Real.exp 9 *
        ((Real.log x) ^ (40 : ℝ) / cardLength ((19 : ℝ) / 20) x))
      atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_log_div_cardLength
      (β := (19 : ℝ) / 20) (by norm_num) (40 : ℝ)).const_mul (7 * Real.exp 9))
  filter_upwards [eventually_menonFinalRangeLadder_basic,
    eventually_menonFinalRangeActualBlock_caseII_endpoints,
    eventually_cardLength_nineteen_twentieth_le_menonFinalRangePrimeCutoffNat,
    eventually_twoRangeT0_le_menonHarmonicCaseIIFrequencyCeiling,
    one_le_twoRangeWidth (b := (2 : ℝ)) (A₃ := (100 : ℝ)) (by norm_num) (by norm_num),
    twoRangeDisc_ge (b := (2 : ℝ)) (A₃ := (100 : ℝ)) (by norm_num) (by norm_num) tau0,
    twoRangeDisc_le_top (b := (2 : ℝ)) (A₃ := (100 : ℝ))
      (β := (2 : ℝ) / 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    one_le_twoRangeTop (β := (2 : ℝ) / 3) (by norm_num) (by norm_num),
    twoRangeHmaj_bounds (A := A) (b := (2 : ℝ)) (A₃ := (100 : ℝ))
      (β := (2 : ℝ) / 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1) hrelLimit,
    Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1) htailLimit,
    Real.tendsto_log_atTop.eventually_ge_atTop (2 : ℝ),
    Filter.eventually_gt_atTop (1 : ℝ)] with
      x hbasic hendpoints hcut ht0ceil hD hdisc hdisctop htop hHbounds
        hrelSmall htailSmall hlog2 hx
  intro j hj w hfreqLo hwTop
  let a : ℕ := menonFinalRangeBlockLowerNat x j
  let Y : ℕ := menonFinalRangeActualBlockUpperNat x j
  let tau : ℝ := -(2 * Real.pi * w)
  let sigma : ℝ := 2 * Real.pi * twoRangeTop ((2 : ℝ) / 3) x
  let R : ℝ := relScaledMajorant Ctot (twoRangeWidth 2 100 x) (twoRangeLx 2 x)
    (twoRangeHmaj A 2 100 ((2 : ℝ) / 3) x)
    (twoRangeMu A delta ((2 : ℝ) / 3) x)
    (twoRangeQ ((19 : ℝ) / 20) x) (twoRangeT₀ 2 100 x)
    (twoRangeXmin ((19 : ℝ) / 20) x)
  have heta : 0 ≤ menonFinalRangeLadderEta x := hbasic.2.2.2.2.1
  have hends := hendpoints j hj
  rcases hends with ⟨haLarge, haY, hYa⟩
  have ha1 : 1 ≤ a := by omega
  have hY1 : 1 ≤ Y := by omega
  have ha0 : (0 : ℝ) < (a : ℝ) := by positivity
  have hY0 : (0 : ℝ) < (Y : ℝ) := by positivity
  have hcardA : cardLength ((19 : ℝ) / 20) x ≤ (a : ℝ) := by
    exact hcut.trans (by exact_mod_cast menonFinalRangePrimeCutoffNat_le_blockLower heta)
  have hcardY : cardLength ((19 : ℝ) / 20) x ≤ (Y : ℝ) :=
    hcardA.trans (by exact_mod_cast haY.le)
  have hYtopNat : Y ≤ menonFinalRangeTopNat x := by
    dsimp only [Y, menonFinalRangeActualBlockUpperNat]
    exact min_le_left _ _
  have hYtop : (Y : ℝ) ≤ 3 * x := by
    have hcast : (Y : ℝ) ≤ (menonFinalRangeTopNat x : ℝ) := by
      exact_mod_cast hYtopNat
    exact hcast.trans (Nat.floor_le (by positivity))
  have hlogY : Real.log (Y : ℝ) ≤ twoRangeLx 2 x := by
    have hlogYtop := Real.log_le_log hY0 hYtop
    have hlog3x : Real.log (3 * x) = Real.log 3 + Real.log x :=
      Real.log_mul (by norm_num) (ne_of_gt (by linarith : 0 < x))
    rw [hlog3x] at hlogYtop
    have hlog3 : Real.log 3 ≤ 2 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
      linarith
    rw [twoRangeLx]
    rw [Real.rpow_two]
    have hlog2nn : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hsquare : Real.log x + 2 ≤ (Real.log x) ^ (2 : ℕ) := by nlinarith
    linarith
  have hq : twoRangeQ ((19 : ℝ) / 20) x ≤ Real.log (Y : ℝ) := by
    have hlogCard := Real.log_le_log (cardLength_pos _ _) hcardY
    rw [log_cardLength] at hlogCard
    exact hlogCard
  have hxmin : twoRangeXmin ((19 : ℝ) / 20) x ≤ (Y : ℝ) := by
    simpa only [twoRangeXmin] using hcardY
  have htauAbs : |tau| = 2 * Real.pi * |w| := by
    dsimp only [tau]
    rw [abs_neg, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      abs_of_pos Real.pi_pos]
  have hsigmaAbs : |sigma| = sigma := by
    apply abs_of_nonneg
    dsimp only [sigma]
    positivity
  have hlo : twoRangeT₀ 2 100 x ≤ |tau| := by
    rw [htauAbs]
    exact (ht0ceil j hj).trans hfreqLo
  have hhi : |tau| ≤ |sigma| := by
    rw [htauAbs, hsigmaAbs]
    dsimp only [sigma]
    exact mul_le_mul_of_nonneg_left hwTop (by positivity)
  have htauRoute : tau0 ≤ |tau| := by
    have hdisc' : max tau0 (16 * Real.pi / 3) ≤ twoRangeT₀ 2 100 x := by
      simpa only [two_pi_mul_twoRangeDisc] using hdisc
    exact (le_max_left _ _).trans (hdisc'.trans hlo)
  have htauLarge : 16 * Real.pi / 3 ≤ |tau| := by
    have hdisc' : max tau0 (16 * Real.pi / 3) ≤ twoRangeT₀ 2 100 x := by
      simpa only [two_pi_mul_twoRangeDisc] using hdisc
    exact (le_max_right _ _).trans (hdisc'.trans hlo)
  have hmu : twoRangeMu A delta ((2 : ℝ) / 3) x ≤
      min delta (routeTWidthPolylogLower A tau) / 2 := by
    have hanti := routeTWidthPolylogLower_antitone (A := A) (τ := tau) (σ := sigma) hhi
    exact (twoRangeMu_le (A := A) (delta := delta) (β := (2 : ℝ) / 3) x).trans
      (div_le_div_of_nonneg_right (min_le_min_left delta hanti) (by norm_num))
  have hHmaj : 1 / twoRangeT₀ 2 100 x +
      Real.log (3 * |sigma| / 2) / routeTWidthPolylogLower A sigma ≤
        twoRangeHmaj A 2 100 ((2 : ℝ) / 3) x := by
    rw [hsigmaAbs]
    dsimp only [sigma]
    rw [twoRangeHmaj, ← two_pi_mul_twoRangeDisc]
  have hrelEnvelope := relScaledEnvelope_le_uniform
    (A := A) (delta := delta) (Ctot := Ctot) (D := twoRangeWidth 2 100 x)
    (τ := tau) (x := (Y : ℝ)) hCtot.le (twoRangeWidth_pos hx) htauLarge
    (by exact_mod_cast hY1) (Lx := twoRangeLx 2 x)
    (q := twoRangeQ ((19 : ℝ) / 20) x)
    (μ := twoRangeMu A delta ((2 : ℝ) / 3) x) (t₀ := twoRangeT₀ 2 100 x)
    (σ := sigma) (xmin := twoRangeXmin ((19 : ℝ) / 20) x)
    (Hmaj := twoRangeHmaj A 2 100 ((2 : ℝ) / 3) x)
    (twoRangeT₀_pos hx) hlo hhi hlogY (twoRangeQ_nonneg hx) hq
    (twoRangeMu_nonneg hdelta.le x) hmu (twoRangeXmin_pos _ _) hxmin hHmaj
  have hR0 : 0 ≤ R := by
    dsimp only [R]
    exact relScaledMajorant_nonneg hCtot.le (twoRangeWidth_pos hx)
      (by rw [twoRangeLx]; positivity)
      hHbounds.1
      (twoRangeT₀_pos hx) (twoRangeXmin_pos _ _)
  let L40 : ℝ := (Real.log x) ^ (40 : ℝ)
  have hL40 : 0 < L40 := by
    dsimp only [L40]
    exact Real.rpow_pos_of_pos (Real.log_pos hx) _
  have hRprod : L40 * R ≤ 1 := by
    simpa only [L40, R] using hrelSmall
  have hRs : R ≤ 1 / L40 := by
    rw [le_div_iff₀ hL40]
    simpa only [mul_comm] using hRprod
  have hs0 : 0 ≤ 1 / L40 := by positivity
  have htailProd : 7 * Real.exp 9 * L40 ≤ cardLength ((19 : ℝ) / 20) x := by
    have hcard0 : 0 < cardLength ((19 : ℝ) / 20) x := cardLength_pos _ _
    have htailDiv : (7 * Real.exp 9 * L40) /
        cardLength ((19 : ℝ) / 20) x ≤ 1 := by
      simpa only [L40, mul_div_assoc] using htailSmall
    exact (div_le_one hcard0).mp htailDiv
  have htailA : 7 * Real.exp 9 * L40 ≤ ((a + 1 : ℕ) : ℝ) := by
    exact htailProd.trans (hcardA.trans (by
      exact_mod_cast (show a ≤ a + 1 by omega)))
  have htailS : 7 * Real.exp 9 ≤ ((a + 1 : ℕ) : ℝ) * (1 / L40) := by
    rw [show ((a + 1 : ℕ) : ℝ) * (1 / L40) =
      ((a + 1 : ℕ) : ℝ) / L40 by ring]
    rw [le_div_iff₀ hL40]
    simpa only [mul_comm] using htailA
  have hrelEnvelopeR : relScaledEnvelope A delta Ctot (twoRangeWidth 2 100 x)
      tau (Y : ℝ) ≤ R := by
    simpa only [R] using hrelEnvelope
  have hscaled : scaledTwistEnvelope A delta Ctot (twoRangeWidth 2 100 x)
      (-(2 * Real.pi * w)) (Y : ℝ) ≤ (Y : ℝ) * R := by
    rw [scaledTwistEnvelope_eq_mul hY0]
    exact mul_le_mul_of_nonneg_left
      (by simpa only [tau] using hrelEnvelopeR) (by positivity)
  have hYcast : (Y : ℝ) ≤ 2 * (a : ℝ) := by exact_mod_cast hYa
  have hYcoef : (Y : ℝ) ≤ 2 * ((a + 1 : ℕ) : ℝ) := by
    push_cast
    linarith
  have hYR : (Y : ℝ) * R ≤
      2 * ((a + 1 : ℕ) : ℝ) * (1 / L40) := by
    calc
      (Y : ℝ) * R ≤ (2 * ((a + 1 : ℕ) : ℝ)) * R :=
        mul_le_mul_of_nonneg_right hYcoef hR0
      _ ≤ (2 * ((a + 1 : ℕ) : ℝ)) * (1 / L40) :=
        mul_le_mul_of_nonneg_left hRs (by positivity)
      _ = 2 * ((a + 1 : ℕ) : ℝ) * (1 / L40) := by ring
  have hsum : (Y : ℝ) * R + 7 * Real.exp 9 ≤
      3 * ((a + 1 : ℕ) : ℝ) * (1 / L40) := by
    linarith
  have hden0 : (0 : ℝ) < ((a + 1 : ℕ) : ℝ) := by positivity
  have hsumDiv : ((Y : ℝ) * R + 7 * Real.exp 9) / ((a + 1 : ℕ) : ℝ) ≤
      3 * (1 / L40) := by
    rw [div_le_iff₀ hden0]
    nlinarith
  have hmaxY : max (Y : ℝ) 1 = (Y : ℝ) := max_eq_left (by exact_mod_cast hY1)
  have hraw := hrouteT (primesRange a Y) a Y (twoRangeWidth 2 100 x) w
    ha1 haY.le (fun p => mem_primesRange) hD htauRoute
  rw [hmaxY] at hraw
  have hinside :
      (scaledTwistEnvelope A delta Ctot (twoRangeWidth 2 100 x)
          (-(2 * Real.pi * w)) (Y : ℝ) + 7 * Real.exp 9) /
          ((a + 1 : ℕ) : ℝ) ≤ 3 * (1 / L40) := by
    have hadd : scaledTwistEnvelope A delta Ctot (twoRangeWidth 2 100 x)
          (-(2 * Real.pi * w)) (Y : ℝ) + 7 * Real.exp 9 ≤
        (Y : ℝ) * R + 7 * Real.exp 9 := by linarith
    exact (div_le_div_of_nonneg_right hadd hden0.le).trans hsumDiv
  have hcoef : 0 ≤ 4 / Real.log 2 := by positivity
  have hnormL : ‖harmonicPrimeBlockPoly (primesRange a Y) w‖ ≤
      (12 / Real.log 2) * (1 / L40) := by
    have hraw' : ‖harmonicPrimeBlockPoly (primesRange a Y) w‖ ≤
        4 / Real.log 2 *
          ((scaledTwistEnvelope A delta Ctot (twoRangeWidth 2 100 x)
            (-(2 * Real.pi * w)) (Y : ℝ) + 7 * Real.exp 9) /
              ((a + 1 : ℕ) : ℝ)) := by
      calc
        ‖harmonicPrimeBlockPoly (primesRange a Y) w‖ ≤
            4 / Real.log 2 *
              (scaledTwistEnvelope A delta Ctot (twoRangeWidth 2 100 x)
                (-(2 * Real.pi * w)) (Y : ℝ) + 7 * Real.exp 9) /
                ((a + 1 : ℕ) : ℝ) := hraw
        _ = 4 / Real.log 2 *
              ((scaledTwistEnvelope A delta Ctot (twoRangeWidth 2 100 x)
                (-(2 * Real.pi * w)) (Y : ℝ) + 7 * Real.exp 9) /
                  ((a + 1 : ℕ) : ℝ)) := by ring
    refine hraw'.trans ?_
    have hmul := mul_le_mul_of_nonneg_left hinside hcoef
    calc
      4 / Real.log 2 *
          ((scaledTwistEnvelope A delta Ctot (twoRangeWidth 2 100 x)
            (-(2 * Real.pi * w)) (Y : ℝ) + 7 * Real.exp 9) /
              ((a + 1 : ℕ) : ℝ))
          ≤ 4 / Real.log 2 * (3 * (1 / L40)) := hmul
      _ = (12 / Real.log 2) * (1 / L40) := by ring
  have hloga0 : 0 < Real.log (a : ℝ) := Real.log_pos (by
    exact_mod_cast (show 1 < a by omega))
  have hlogaY : Real.log (a : ℝ) ≤ Real.log (Y : ℝ) :=
    Real.log_le_log ha0 (by exact_mod_cast haY.le)
  have hlogTwoLe : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hLsq1 : (1 : ℝ) ≤ (Real.log x) ^ (2 : ℕ) := by nlinarith
  have hloga : Real.log (a : ℝ) ≤ 2 * (Real.log x) ^ (2 : ℕ) := by
    have hYbound := hlogaY.trans hlogY
    rw [twoRangeLx, Real.rpow_two] at hYbound
    linarith
  have hpowLog : (Real.log (a : ℝ)) ^ (20 : ℕ) ≤
      (2 : ℝ) ^ (20 : ℕ) * L40 := by
    have hp := pow_le_pow_left₀ hloga0.le hloga 20
    have hpowEq : (2 * (Real.log x) ^ (2 : ℕ)) ^ (20 : ℕ) =
        (2 : ℝ) ^ (20 : ℕ) * L40 := by
      rw [mul_pow, ← pow_mul]
      norm_num [L40, Real.rpow_natCast]
    exact hp.trans_eq hpowEq
  have hlogPow0 : 0 < (Real.log (a : ℝ)) ^ (20 : ℕ) := pow_pos hloga0 _
  have hscale : 1 / L40 ≤ (2 : ℝ) ^ (20 : ℕ) /
      (Real.log (a : ℝ)) ^ (20 : ℕ) := by
    rw [div_le_div_iff₀ hL40 hlogPow0]
    simpa only [one_mul] using hpowLog
  have hfinal := mul_le_mul_of_nonneg_left hscale (by positivity : 0 ≤ 12 / Real.log 2)
  simpa only [a, Y, C1, mul_div_assoc] using hnormL.trans hfinal

end

end RHTower.Sieve
