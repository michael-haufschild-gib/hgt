import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicFullIntervalProduct
import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicInitialRangeSchedule

/-!
# Full-interval assembly for Menon's initial range

This specializes the ordinary all-small harmonic Ramaré ladder to the variable-top initial prime
range.  Every cofactor is paid on the complete receiver interval, so the exceptional-set volume
does not enter this half of Menon's frequency partition.
-/

namespace RHTower.Sieve

open Filter Finset MeasureTheory

noncomputable section

/-- Menon's variable-top initial prime range controls every ordinary all-small frequency by
the full-interval cofactor mean square.  The explicit ladder cost is paid without a restricted-set
volume loss, and the literal global support defect appears exactly once. -/
theorem eventually_setIntegral_normSq_menonInitialRange_ordinary_le_fullInterval
    {a c A : ℝ} (ha : 0 < a) (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, ∀ (hN : ℕ) (W : ℝ),
      ((highBase a x : ℕ) : ℝ) < (hN : ℝ) →
      (hN : ℝ) ≤ x → 1 ≤ W →
      1 ≤ menonInitialRangeSteps a c x hN →
      W * ((hN : ℝ) + 1) ≤ 2 * x →
      let P := menonInitialRangePrimes a c x hN
      let Q := ((highBase a x : ℕ) : ℝ)
      let eta := lowEta c x
      let theta := lowTheta A x
      let L := menonInitialRangeSteps a c x hN
      let E := allBlocksSmall P Q eta L
        (fun j => ((geomBlock P Q (1 + eta) j).card : ℝ) * theta) W
      (∫ w in E,
        ‖harmonicRamareBilinear P (menonFinalRangeShell x) w‖ ^ 2) ≤
        3600 * (L : ℝ) ^ 2 * (eta + 1 / Q) ^ 2 * (theta + eta) ^ 2 +
          2 * ∫ w in E,
            ‖harmonicLadderProductDefect P ⌈x⌉₊
              (menonFinalRangeTopNat x) Q eta L w‖ ^ 2 := by
  filter_upwards [Filter.eventually_gt_atTop (Real.exp 1),
    two_le_highBase_and_le_expTop (a := a) (c := c) (β := (1 : ℝ)) ha hc]
      with x hxexp hQtwo
  intro hN W hQh hhx hW hL hWh
  dsimp only
  let P := menonInitialRangePrimes a c x hN
  let Q := ((highBase a x : ℕ) : ℝ)
  let eta := lowEta c x
  let theta := lowTheta A x
  let L := menonInitialRangeSteps a c x hN
  let E := allBlocksSmall P Q eta L
    (fun j => ((geomBlock P Q (1 + eta) j).card : ℝ) * theta) W
  have hx1 : 1 < x := by
    have he : (1 : ℝ) < Real.exp 1 := by
      nlinarith [Real.exp_one_gt_d9]
    exact he.trans hxexp
  have hxone : 1 ≤ x := hx1.le
  have hQgt : 1 < Q := by
    dsimp only [Q]
    have htwo : (2 : ℝ) ≤ ((highBase a x : ℕ) : ℝ) := by exact_mod_cast hQtwo.1
    linarith
  have hQpos : 0 < Q := zero_lt_one.trans hQgt
  have heta0 : 0 ≤ eta := (lowEta_pos (c := c) hx1).le
  have heta1 : eta ≤ 1 := by
    dsimp only [eta, lowEta]
    have hlog : 1 ≤ Real.log x := by
      have h := Real.log_le_log (Real.exp_pos 1) hxexp.le
      simpa using h
    have := Real.rpow_le_rpow_of_exponent_le hlog (by linarith : -c ≤ 0)
    simpa using this
  have hPrange : ∀ p ∈ P,
      Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + eta) ^ L := by
    simpa only [P, Q, eta, L] using
      menonInitialRangePrimes_range (a := a) (c := c) (x := x) (hN := hN) hx1
  have hprime : ∀ p ∈ P, p.Prime := by
    intro p hp
    exact (mem_primesRange.mp (by simpa only [P, menonInitialRangePrimes] using hp)).1
  have hleft : ∀ j ∈ Finset.range L,
      1 ≤ ⌈(⌈x⌉₊ : ℝ) / ((Q * (1 + eta) ^ j) * (1 + eta))⌉₊ := by
    intro j hj
    exact Nat.one_le_ceil_iff.2 (by positivity)
  have hbase :=
    setIntegral_normSq_harmonicRamareBilinear_le_ordinary_allSmall_fullInterval_exactDefect
      (P := P) (A₀ := ⌈x⌉₊) (B₀ := menonFinalRangeTopNat x) (L := L)
      (Q := Q) (eta := eta) (theta := theta) (W := W)
      hQgt heta0 hW hL hprime hPrange hleft
  have hcost : ∀ j ∈ Finset.range L,
      menonHarmonicFullIntervalProductCost P ⌈x⌉₊ (menonFinalRangeTopNat x)
        Q eta W
          (((geomBlock P Q (1 + eta) j).card : ℝ) * (theta + eta) /
            (Q * (1 + eta) ^ j)) j ≤
        1800 * (eta + 1 / Q) ^ 2 * (theta + eta) ^ 2 := by
    intro j hj
    let q : ℝ := Q * (1 + eta) ^ j
    have hjL : j < L := Finset.mem_range.mp hj
    have hq0 : 0 < q := by dsimp only [q]; positivity
    have hqQ : Q ≤ q := by
      dsimp only [q]
      have hp : (1 : ℝ) ≤ (1 + eta) ^ j := one_le_pow₀ (by linarith)
      nlinarith
    have hqTop : q ≤ 3 * x := by
      have hjle : j ≤ L := Nat.le_of_lt hjL
      have hpow : (1 + eta) ^ j ≤ (1 + eta) ^ L :=
        pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ 1 + eta) hjle
      have hqraw : q ≤ Q * (1 + eta) ^ L := by
        dsimp only [q]
        exact mul_le_mul_of_nonneg_left hpow hQpos.le
      have hfloor : Q * (1 + eta) ^ L <
          (menonInitialRangeTop a c x hN : ℝ) + 1 := by
        simpa only [Q, eta, L, menonInitialRangeTop] using
          (Nat.lt_floor_add_one (Q * (1 + eta) ^ L))
      have htopNat := menonInitialRangeTop_le (a := a) (c := c) hx1 hQh
      have htop : (menonInitialRangeTop a c x hN : ℝ) ≤ (hN : ℝ) := by
        exact_mod_cast htopNat
      nlinarith
    have hWq : W * q / x ≤ 2 := by
      have hqHN : q ≤ (hN : ℝ) + 1 := by
        have hjle : j ≤ L := Nat.le_of_lt hjL
        have hpow : (1 + eta) ^ j ≤ (1 + eta) ^ L :=
          pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ 1 + eta) hjle
        have hqraw : q ≤ Q * (1 + eta) ^ L := by
          dsimp only [q]
          exact mul_le_mul_of_nonneg_left hpow hQpos.le
        have hfloor : Q * (1 + eta) ^ L <
            (menonInitialRangeTop a c x hN : ℝ) + 1 := by
          simpa only [Q, eta, L, menonInitialRangeTop] using
            (Nat.lt_floor_add_one (Q * (1 + eta) ^ L))
        have htopNat := menonInitialRangeTop_le (a := a) (c := c) hx1 hQh
        have htop : (menonInitialRangeTop a c x hN : ℝ) ≤ (hN : ℝ) := by
          exact_mod_cast htopNat
        linarith
      have hmul : W * q ≤ W * ((hN : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left hqHN (by linarith)
      rw [div_le_iff₀ (by linarith : 0 < x)]
      exact hmul.trans hWh
    have hcard := card_geomBlock_le P hQpos heta0 j
    have hqinv : 1 / q ≤ 1 / Q := one_div_le_one_div_of_le hQpos hqQ
    have hratio : ((geomBlock P Q (1 + eta) j).card : ℝ) / q ≤
        eta + 1 / Q := by
      calc
        ((geomBlock P Q (1 + eta) j).card : ℝ) / q ≤
            (q * eta + 1) / q := div_le_div_of_nonneg_right
              (by simpa only [q] using hcard) hq0.le
        _ = eta + 1 / q := by field_simp
        _ ≤ eta + 1 / Q := by simpa [add_comm] using add_le_add_left hqinv eta
    have hV :
        ((geomBlock P Q (1 + eta) j).card : ℝ) * (theta + eta) / q ≤
          (eta + 1 / Q) * (theta + eta) := by
      have hte0 : 0 ≤ theta + eta := by
        have ht0 : 0 ≤ theta := (lowTheta_pos (A := A) hx1).le
        positivity
      calc
        ((geomBlock P Q (1 + eta) j).card : ℝ) * (theta + eta) / q =
            (((geomBlock P Q (1 + eta) j).card : ℝ) / q) * (theta + eta) := by ring
        _ ≤ (eta + 1 / Q) * (theta + eta) :=
          mul_le_mul_of_nonneg_right hratio hte0
    have hV0 : 0 ≤
        ((geomBlock P Q (1 + eta) j).card : ℝ) * (theta + eta) / q := by
      have ht0 : 0 ≤ theta := (lowTheta_pos (A := A) hx1).le
      positivity
    have hVupper0 : 0 ≤ (eta + 1 / Q) * (theta + eta) := by
      have ht0 : 0 ≤ theta := (lowTheta_pos (A := A) hx1).le
      positivity
    have hcost0 := menonFinalRangeFullIntervalProductCost_le
      (P := P)
      (V := ((geomBlock P Q (1 + eta) j).card : ℝ) * (theta + eta) /
        (Q * (1 + eta) ^ j))
      hxone hQpos heta0 heta1 (le_trans (by norm_num) hW) j
      (by simpa only [q] using hqTop)
    calc
      menonHarmonicFullIntervalProductCost P ⌈x⌉₊ (menonFinalRangeTopNat x)
          Q eta W
            (((geomBlock P Q (1 + eta) j).card : ℝ) * (theta + eta) /
              (Q * (1 + eta) ^ j)) j ≤
        600 * ((((geomBlock P Q (1 + eta) j).card : ℝ) *
          (theta + eta) / q) ^ 2) * (1 + W * q / x) := by
            simpa only [q] using hcost0
      _ ≤ 600 * (((eta + 1 / Q) * (theta + eta)) ^ 2) * 3 := by
        have hsq := pow_le_pow_left₀ hV0 hV 2
        have hfac : 0 ≤ 1 + W * q / x := by positivity
        calc
          600 * ((((geomBlock P Q (1 + eta) j).card : ℝ) *
              (theta + eta) / q) ^ 2) * (1 + W * q / x) ≤
              600 * (((eta + 1 / Q) * (theta + eta)) ^ 2) *
                (1 + W * q / x) := by gcongr
          _ ≤ 600 * (((eta + 1 / Q) * (theta + eta)) ^ 2) * 3 := by
            exact mul_le_mul_of_nonneg_left (by linarith)
              (mul_nonneg (by norm_num) (sq_nonneg _))
      _ = 1800 * (eta + 1 / Q) ^ 2 * (theta + eta) ^ 2 := by ring
  have hsum :
      (∑ j ∈ Finset.range L,
        menonHarmonicFullIntervalProductCost P ⌈x⌉₊ (menonFinalRangeTopNat x)
          Q eta W
            (((geomBlock P Q (1 + eta) j).card : ℝ) * (theta + eta) /
              (Q * (1 + eta) ^ j)) j) ≤
        (L : ℝ) * (1800 * (eta + 1 / Q) ^ 2 * (theta + eta) ^ 2) := by
    calc
      _ ≤ ∑ _j ∈ Finset.range L,
          1800 * (eta + 1 / Q) ^ 2 * (theta + eta) ^ 2 :=
        Finset.sum_le_sum hcost
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, Finset.card_range]
  have hscaled := mul_le_mul_of_nonneg_left hsum
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Nat.cast_nonneg L))
  calc
    (∫ w in E,
        ‖harmonicRamareBilinear P (menonFinalRangeShell x) w‖ ^ 2) ≤
        2 * (L : ℝ) *
            (∑ j ∈ Finset.range L,
              menonHarmonicFullIntervalProductCost P ⌈x⌉₊ (menonFinalRangeTopNat x)
                Q eta W
                  (((geomBlock P Q (1 + eta) j).card : ℝ) * (theta + eta) /
                    (Q * (1 + eta) ^ j)) j) +
          2 * ∫ w in E,
            ‖harmonicLadderProductDefect P ⌈x⌉₊
              (menonFinalRangeTopNat x) Q eta L w‖ ^ 2 := by
                simpa only [E, P, Q, eta, theta, L, menonFinalRangeShell] using hbase
    _ ≤ 2 * (L : ℝ) *
          ((L : ℝ) * (1800 * (eta + 1 / Q) ^ 2 * (theta + eta) ^ 2)) +
        2 * ∫ w in E,
          ‖harmonicLadderProductDefect P ⌈x⌉₊
            (menonFinalRangeTopNat x) Q eta L w‖ ^ 2 := add_le_add hscaled le_rfl
    _ = 3600 * (L : ℝ) ^ 2 * (eta + 1 / Q) ^ 2 * (theta + eta) ^ 2 +
        2 * ∫ w in E,
          ‖harmonicLadderProductDefect P ⌈x⌉₊
            (menonFinalRangeTopNat x) Q eta L w‖ ^ 2 := by ring

end

end RHTower.Sieve
