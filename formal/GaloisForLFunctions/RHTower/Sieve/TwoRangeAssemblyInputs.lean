import GaloisForLFunctions.RHTower.Sieve.ExceptionalMeasureSchedule
import GaloisForLFunctions.RHTower.Sieve.MoebiusDiscRate
import GaloisForLFunctions.RHTower.Sieve.TwoRangeHighBound

/-!
# The remaining inputs of the two-range assembly

Two items the substitution still needs: the harmonic mass of the **high** designated range (which
enters the large ladder group through `S' = (1+η')·M·H'`), and the disc bound at a *growing* disc
radius — `Sieve/MoebiusDiscRate`'s fibre specialisation fixes the radius, but the two-range schedule
has `w₀ = (log x)^{4b+3A₃+3}/(2π)`.
-/

namespace RHTower.Sieve

open Filter Topology Finset MeasureTheory
open scoped ArithmeticFunction.Moebius

noncomputable section

/-- The bottom of the high ladder is at least two, and below its own top. -/
theorem two_le_highBase_and_le_highTop {a b c' : ℝ} (ha : 0 < a) :
    ∀ᶠ x : ℝ in atTop, 2 ≤ highBase a x ∧ highBase a x ≤ highTop a b c' x := by
  have hpowa : Tendsto (fun x : ℝ => (Real.log x) ^ a) atTop atTop :=
    (tendsto_rpow_atTop ha).comp Real.tendsto_log_atTop
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ), hpowa.eventually_ge_atTop (1 : ℝ)]
    with x hx1 hbig
  have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
  have hη : 0 < highEta c' x := highEta_pos hx1
  have hc2 : (2 : ℝ) ≤ cardLength a x := by
    rw [cardLength]
    have h1 : (1 : ℝ) + (Real.log x) ^ a ≤ Real.exp ((Real.log x) ^ a) :=
      Real.add_one_le_exp _ |>.trans_eq' (by ring)
    linarith
  have hQ2 : (2 : ℝ) ≤ ((highBase a x : ℕ) : ℝ) := by
    have := (highBase_bounds (a := a) hx1).1
    linarith
  refine ⟨by exact_mod_cast hQ2, ?_⟩
  have hpowge : (1 : ℝ) ≤ (1 + highEta c' x) ^ (highSteps a b c' x) := one_le_pow₀ (by linarith)
  rw [highTop]
  refine Nat.le_floor ?_
  nlinarith [hQ2, hpowge]

/-- **The harmonic mass of the high designated range is below `log log x`.** -/
theorem highRange_harmonic_le {a b c' : ℝ} (ha : 0 < a) (hab : a < b) (hb1 : b < 1)
    (hc' : 0 < c') :
    ∀ᶠ x : ℝ in atTop,
      ∑ p ∈ primesRange (highBase a x) (highTop a b c' x), 1 / (p : ℝ)
        ≤ Real.log (Real.log x) := by
  have hpowa : Tendsto (fun x : ℝ => (Real.log x) ^ a) atTop atTop :=
    (tendsto_rpow_atTop ha).comp Real.tendsto_log_atTop
  have hpowb : Tendsto (fun x : ℝ => (Real.log x) ^ b) atTop atTop :=
    (tendsto_rpow_atTop (by linarith)).comp Real.tendsto_log_atTop
  have herr : Tendsto (fun x : ℝ =>
      2 * ((2 * mertensFirstConst + 1 / 2) / (Real.log x) ^ a)) atTop (𝓝 0) := by
    have := (Tendsto.div_atTop (tendsto_const_nhds
      (x := 2 * mertensFirstConst + 1 / 2)) hpowa).const_mul (2 : ℝ)
    simpa using this
  have hll : Tendsto (fun x : ℝ => Real.log (Real.log x)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ),
    two_le_highBase_and_le_highTop (a := a) (b := b) (c' := c') ha,
    highLadder_le (a := a) (b := b) (c' := c') hab.le hc',
    Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1) herr,
    hpowa.eventually_ge_atTop (1 : ℝ), hpowb.eventually_ge_atTop (1 : ℝ),
    hll.eventually_ge_atTop (3 / (1 - b + a))] with x hx1 hlow htop hsmall hpa1 hpb1 hubig
  obtain ⟨h₀, hz⟩ := hlow
  have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
  have hmass := sum_inv_primesRange_le_logLog_diff h₀ hz
  have hQ0 : (0 : ℝ) < ((highBase a x : ℕ) : ℝ) := by
    have h2 : (2 : ℝ) ≤ ((highBase a x : ℕ) : ℝ) := by exact_mod_cast h₀
    linarith
  have hl2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  -- the top
  have hTle : ((highTop a b c' x : ℕ) : ℝ) ≤ 2 * cardLength b x := by
    rw [highTop]
    refine le_trans (Nat.floor_le ?_) htop
    have hη : 0 < highEta c' x := highEta_pos hx1
    positivity
  have hT2 : (2 : ℝ) ≤ ((highTop a b c' x : ℕ) : ℝ) := by
    have : (2 : ℕ) ≤ highTop a b c' x := le_trans h₀ hz
    exact_mod_cast this
  have hlogT : Real.log ((highTop a b c' x : ℕ) : ℝ) ≤ Real.log 2 + (Real.log x) ^ b := by
    have hstep := Real.log_le_log (by linarith) hTle
    have hid : Real.log (2 * cardLength b x) = Real.log 2 + (Real.log x) ^ b := by
      rw [Real.log_mul (by norm_num) (ne_of_gt (cardLength_pos b x)), log_cardLength]
    linarith [hstep, hid]
  have hlogT0 : (0 : ℝ) < Real.log ((highTop a b c' x : ℕ) : ℝ) := by
    have := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hT2
    have hl2p : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    linarith
  have hupperT : Real.log (Real.log ((highTop a b c' x : ℕ) : ℝ))
      ≤ Real.log 2 + b * Real.log (Real.log x) := by
    have h2b : Real.log 2 + (Real.log x) ^ b ≤ 2 * (Real.log x) ^ b := by linarith
    have hstep := Real.log_le_log hlogT0 (le_trans hlogT h2b)
    have hid : Real.log (2 * (Real.log x) ^ b) = Real.log 2 + b * Real.log (Real.log x) := by
      rw [Real.log_mul (by norm_num) (ne_of_gt (Real.rpow_pos_of_pos hlogx b)),
        Real.log_rpow hlogx]
    linarith [hstep, hid]
  -- the bottom
  have hlogQ : (Real.log x) ^ a ≤ Real.log ((highBase a x : ℕ) : ℝ) := by
    have h1 := (highBase_bounds (a := a) hx1).1
    have := Real.log_le_log (cardLength_pos a x) h1
    rwa [log_cardLength] at this
  have hlogQ0 : (0 : ℝ) < Real.log ((highBase a x : ℕ) : ℝ) := by linarith
  have hlowerQ : a * Real.log (Real.log x) ≤ Real.log (Real.log ((highBase a x : ℕ) : ℝ)) := by
    have hp0 : (0 : ℝ) < (Real.log x) ^ a := Real.rpow_pos_of_pos hlogx a
    have := Real.log_le_log hp0 hlogQ
    rwa [Real.log_rpow hlogx] at this
  have herrle : 2 * ((2 * mertensFirstConst + 1 / 2) / Real.log ((highBase a x : ℕ) : ℝ))
      ≤ 2 * ((2 * mertensFirstConst + 1 / 2) / (Real.log x) ^ a) := by
    have hc0 : (0 : ℝ) ≤ 2 * mertensFirstConst + 1 / 2 := by
      have := mertensFirstConst_nonneg
      linarith
    have hp0 : (0 : ℝ) < (Real.log x) ^ a := Real.rpow_pos_of_pos hlogx a
    have := div_le_div_of_nonneg_left hc0 hp0 hlogQ
    linarith
  have hslack : 3 ≤ (1 - b + a) * Real.log (Real.log x) := by
    have hba : (0 : ℝ) < 1 - b + a := by linarith
    rw [div_le_iff₀ hba] at hubig
    nlinarith [hubig, hba]
  linarith [hmass, hupperT, hlowerQ, herrle, hsmall, hslack, hl2]

/-- The disc contribution at the two-range schedule. -/
def discBudget (β b A₃ K x : ℝ) : ℝ :=
  2 * twoRangeDisc b A₃ x
    * (K * (Real.sqrt x + cardLength β x)
        * Real.exp (-((Real.log (Real.sqrt x + cardLength β x)) ^ ((1 : ℝ) / 20)))) ^ 2

/-- **The disc bound at a growing polylogarithmic radius.** -/
theorem exists_discBudget_bound {β b A₃ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (_hb : 0 < b)
    (_hA₃ : 0 < A₃) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℝ in atTop,
      (∫ w in Set.Icc (-(twoRangeDisc b A₃ x)) (twoRangeDisc b A₃ x),
          ‖logPoly (fun n => ((μ n : ℤ) : ℂ)) (Finset.Icc 1 (twoRangeLength β x)) w‖ ^ 2)
        ≤ discBudget β b A₃ K x := by
  obtain ⟨K, hK, hmain⟩ := exists_setIntegral_disc_normSq_logPoly_moebius_le_rate
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 hmain
  have hsmall : Tendsto (fun x : ℝ =>
      (Real.log x) ^ (4 * b + 3 * A₃ + 3) / Real.sqrt x) atTop (𝓝 0) :=
    tendsto_rpow_log_div_sqrt _
  refine ⟨K, hK, ?_⟩
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ), Filter.eventually_ge_atTop (N₀ ^ 2),
    Filter.eventually_ge_atTop (4 : ℝ),
    Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1) hsmall,
    (tendsto_cardLength hβ0).eventually_ge_atTop (0 : ℝ)] with x hx1 hxN hx4 hsm hh0
  have hx0 : (0 : ℝ) < x := by linarith
  have hs0 : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hN₀le : N₀ ≤ Real.sqrt x := by
    rcases le_or_gt N₀ 0 with h | h
    · linarith
    · rw [show N₀ = Real.sqrt (N₀ ^ 2) by rw [Real.sqrt_sq h.le]]
      exact Real.sqrt_le_sqrt hxN
  have hh0' : (0 : ℝ) < cardLength β x := cardLength_pos β x
  have hNge : N₀ ≤ Real.sqrt x + cardLength β x := by linarith
  have hdisc0 : (0 : ℝ) ≤ twoRangeDisc b A₃ x := (twoRangeDisc_pos hx1).le
  have hpi : 2 * Real.pi * twoRangeDisc b A₃ x ≤ Real.sqrt x + cardLength β x := by
    rw [two_pi_mul_twoRangeDisc, twoRangeT₀]
    rw [div_le_iff₀ hs0] at hsm
    linarith
  have hbase := hN₀ (Real.sqrt x + cardLength β x) hNge (twoRangeDisc b A₃ x) hdisc0 hpi
  have hidx : (⌊Real.sqrt x + cardLength β x⌋₊ : ℕ) = twoRangeLength β x := rfl
  rw [hidx] at hbase
  exact hbase

/-- **The disc contributes nothing relative to `M²` at a polylogarithmic radius.** -/
theorem tendsto_discBudget_div_sq {β b A₃ K : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    Tendsto (fun x : ℝ =>
        discBudget β b A₃ K x / ((twoRangeLength β x : ℕ) : ℝ) ^ 2) atTop (𝓝 0) := by
  have hmaj0 := tendsto_logRpow_mul_expSaving (d := (1 : ℝ) / 20) (s := (1 : ℝ))
    (by norm_num) (by norm_num) (4 * b + 3 * A₃ + 3)
  have hmaj : Tendsto (fun x : ℝ => 4 * K ^ 2 / Real.pi
      * ((Real.log x) ^ (4 * b + 3 * A₃ + 3)
        * Real.exp (-(1 * (Real.log x) ^ ((1 : ℝ) / 20))))) atTop (𝓝 0) := by
    have := hmaj0.const_mul (4 * K ^ 2 / Real.pi)
    rw [show (4 * K ^ 2 / Real.pi * 0) = 0 by ring] at this
    exact this
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx1
    have hd : (0 : ℝ) ≤ twoRangeDisc b A₃ x := (twoRangeDisc_pos hx1).le
    have h1 : (0 : ℝ) ≤ discBudget β b A₃ K x := by
      rw [discBudget]
      positivity
    positivity
  · filter_upwards [Filter.eventually_gt_atTop (1 : ℝ), Filter.eventually_ge_atTop (16 : ℝ),
      sqrt_le_twoRangeLength hβ0, cardLength_le_sqrt hβ0 hβ1,
      Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)] with x hx1 hx16 hM hh hlog1
    have hx0 : (0 : ℝ) < x := by linarith
    have hs0 : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 hx0
    have hxx : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
    have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
    have hh0 : (0 : ℝ) < cardLength β x := cardLength_pos β x
    have hM0 : (0 : ℝ) < ((twoRangeLength β x : ℕ) : ℝ) := by linarith
    have hMx : x ≤ ((twoRangeLength β x : ℕ) : ℝ) ^ 2 := by nlinarith [hM, hs0, hxx]
    -- the exponential factor
    have hlogsum : Real.log x / 2 ≤ Real.log (Real.sqrt x + cardLength β x) := by
      have h1 : Real.sqrt x ≤ Real.sqrt x + cardLength β x := by linarith
      have h2 := Real.log_le_log hs0 h1
      have h3 : Real.log (Real.sqrt x) = Real.log x / 2 := by
        rw [Real.log_sqrt hx0.le]
      linarith [h2, h3]
    have hpow20 : (Real.log x) ^ ((1 : ℝ) / 20) / 2
        ≤ (Real.log (Real.sqrt x + cardLength β x)) ^ ((1 : ℝ) / 20) := by
      have hstep : (Real.log x / 2) ^ ((1 : ℝ) / 20)
          ≤ (Real.log (Real.sqrt x + cardLength β x)) ^ ((1 : ℝ) / 20) :=
        Real.rpow_le_rpow (by linarith) hlogsum (by norm_num)
      have hid : (Real.log x / 2) ^ ((1 : ℝ) / 20)
          = (Real.log x) ^ ((1 : ℝ) / 20) / (2 : ℝ) ^ ((1 : ℝ) / 20) := by
        rw [Real.div_rpow hlogx.le (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
      have h2 : (2 : ℝ) ^ ((1 : ℝ) / 20) ≤ 2 := by
        calc (2 : ℝ) ^ ((1 : ℝ) / 20) ≤ (2 : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          _ = 2 := Real.rpow_one 2
      have h20 : (0 : ℝ) < (2 : ℝ) ^ ((1 : ℝ) / 20) := Real.rpow_pos_of_pos (by norm_num) _
      have hp0 : (0 : ℝ) ≤ (Real.log x) ^ ((1 : ℝ) / 20) := Real.rpow_nonneg hlogx.le _
      have hfrac : (Real.log x) ^ ((1 : ℝ) / 20) / 2
          ≤ (Real.log x) ^ ((1 : ℝ) / 20) / (2 : ℝ) ^ ((1 : ℝ) / 20) :=
        div_le_div_of_nonneg_left hp0 h20 h2
      linarith [hstep, hid, hfrac]
    set E : ℝ := Real.exp (-((Real.log (Real.sqrt x + cardLength β x)) ^ ((1 : ℝ) / 20)))
      with hEdef
    have hE0 : (0 : ℝ) < E := Real.exp_pos _
    have hEsq : E ^ 2 ≤ Real.exp (-(1 * (Real.log x) ^ ((1 : ℝ) / 20))) := by
      rw [hEdef, ← Real.exp_nat_mul]
      refine Real.exp_le_exp.2 ?_
      push_cast
      nlinarith [hpow20]
    -- assemble
    have hnum : (K * (Real.sqrt x + cardLength β x) * E) ^ 2 ≤ K ^ 2 * (4 * x) * E ^ 2 := by
      have hsq : (Real.sqrt x + cardLength β x) ^ 2 ≤ 4 * x := by nlinarith [hh, hs0, hxx, hh0]
      have hid : (K * (Real.sqrt x + cardLength β x) * E) ^ 2
          = K ^ 2 * (Real.sqrt x + cardLength β x) ^ 2 * E ^ 2 := by ring
      rw [hid]
      have hKE : (0 : ℝ) ≤ K ^ 2 * E ^ 2 := by positivity
      calc K ^ 2 * (Real.sqrt x + cardLength β x) ^ 2 * E ^ 2
          = K ^ 2 * E ^ 2 * (Real.sqrt x + cardLength β x) ^ 2 := by ring
        _ ≤ K ^ 2 * E ^ 2 * (4 * x) := mul_le_mul_of_nonneg_left hsq hKE
        _ = K ^ 2 * (4 * x) * E ^ 2 := by ring
    have hdiscval : twoRangeDisc b A₃ x = (Real.log x) ^ (4 * b + 3 * A₃ + 3) / (2 * Real.pi) :=
      rfl
    have hd0 : (0 : ℝ) < twoRangeDisc b A₃ x := twoRangeDisc_pos hx1
    have hstep1 : discBudget β b A₃ K x ≤ 2 * twoRangeDisc b A₃ x * (K ^ 2 * (4 * x) * E ^ 2) := by
      rw [discBudget]
      exact mul_le_mul_of_nonneg_left hnum (by linarith)
    have hstep2 : discBudget β b A₃ K x / ((twoRangeLength β x : ℕ) : ℝ) ^ 2
        ≤ 2 * twoRangeDisc b A₃ x * (K ^ 2 * (4 * x) * E ^ 2) / x := by
      refine le_trans (div_le_div_of_nonneg_right hstep1 (by positivity)) ?_
      refine div_le_div_of_nonneg_left ?_ hx0 hMx
      have : (0 : ℝ) ≤ K ^ 2 * (4 * x) * E ^ 2 := by positivity
      nlinarith [hd0, this]
    refine hstep2.trans ?_
    have hid2 : 2 * twoRangeDisc b A₃ x * (K ^ 2 * (4 * x) * E ^ 2) / x
        = 4 * K ^ 2 / Real.pi * ((Real.log x) ^ (4 * b + 3 * A₃ + 3) * E ^ 2) := by
      rw [hdiscval]
      field_simp
    rw [hid2]
    have hcoef : (0 : ℝ) ≤ 4 * K ^ 2 / Real.pi := by
      have := Real.pi_pos
      positivity
    have hp0 : (0 : ℝ) ≤ (Real.log x) ^ (4 * b + 3 * A₃ + 3) := Real.rpow_nonneg hlogx.le _
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hEsq hp0) hcoef

end

end RHTower.Sieve
