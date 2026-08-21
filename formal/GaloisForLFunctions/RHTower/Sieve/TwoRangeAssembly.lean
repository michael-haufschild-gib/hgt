import GaloisForLFunctions.RHTower.Sieve.TwoRangeAssemblyInputs
import GaloisForLFunctions.RHTower.Sieve.TwoRangeGroupLimits
import GaloisForLFunctions.RHTower.Sieve.MoebiusHeadSmall
import GaloisForLFunctions.RHTower.Sieve.LadderAffineBounds
import GaloisForLFunctions.RHTower.Sieve.RamareLadderAnnulus
import GaloisForLFunctions.RHTower.Sieve.LargeLadderGroup

/-!
# The two-range budget at the schedule

Naming the two designated ranges, their thresholds and the resulting budget.  The budget is exactly
the right-hand side of
`Sieve/MoebiusTwoRangeWindow.integral_Icc_normSq_logPoly_moebius_le_twoRange` with the schedule
substituted and the disc bound of `Sieve/TwoRangeAssemblyInputs` in place of the free parameter.
-/

namespace RHTower.Sieve

open Filter Topology Finset MeasureTheory
open scoped ArithmeticFunction.Moebius

noncomputable section

/-- The low designated range. -/
def lowP (a c β x : ℝ) : Finset ℕ := primesRange (highBase a x) (expTop a c β x)

/-- The relative threshold on the low blocks. -/
def lowV (a c A β : ℝ) (x : ℝ) (j : ℕ) : ℝ :=
  ((geomBlock (lowP a c β x) ((highBase a x : ℕ) : ℝ) (1 + lowEta c x) j).card : ℝ)
    * lowTheta A x

/-- The high designated range. -/
def highP (a₁ b c' x : ℝ) : Finset ℕ := primesRange (highBase a₁ x) (highTop a₁ b c' x)

/-- The Route-T bound on the high blocks, made relative to the block's **cardinality**.  Route T
bounds a block by its base, and the ladder group is built on the cardinality; the two differ by
`log R_j/η'`, a polylogarithm, which the zero-free-region saving absorbs. -/
def highV (A₀ δ₀ Ctot a₁ b c' β A₃ : ℝ) (x : ℝ) (j : ℕ) : ℝ :=
  8 * twoRangeHighRho A₀ δ₀ Ctot a₁ b c' β A₃ x * (Real.log x) ^ (b + c')
    * ((geomBlock (highP a₁ b c' x) ((highBase a₁ x : ℕ) : ℝ) (1 + highEta c' x) j).card : ℝ)

theorem lowV_nonneg {a c A β : ℝ} (x : ℝ) (hx : 1 < x) (j : ℕ) : 0 ≤ lowV a c A β x j := by
  rw [lowV]
  have := (lowTheta_pos (A := A) hx).le
  positivity

/-- The exceptional half of the annulus at the schedule. -/
def lowExceptional (a c A β b A₃ : ℝ) (x : ℝ) : Set ℝ :=
  annulusLarge (allBlocksSmall (lowP a c β x) ((highBase a x : ℕ) : ℝ) (lowEta c x)
      (expSteps a c β x) (lowV a c A β x) (twoRangeTop β x))
    (twoRangeTop β x) (twoRangeDisc b A₃ x)

/-- **The two-range budget at the schedule.** -/
def twoRangeBudget (A₀ δ₀ Ctot Kd a c A β a₁ b c' A₃ : ℝ) (x : ℝ) : ℝ :=
  discBudget β b A₃ Kd x
    + ((1 + twoRangeDelta x)
        * (2 * ((expSteps a c β x : ℕ) : ℝ) * ∑ j ∈ Finset.range (expSteps a c β x),
              lowV a c A β x j ^ 2
                * ((5 * Real.pi / 2 * twoRangeTop β x
                      + 5 * Real.exp 1 / 2
                        * ((⌊((twoRangeLength β x : ℕ) : ℝ)
                            / (((highBase a x : ℕ) : ℝ) * (1 + lowEta c x) ^ j)⌋₊ : ℕ) : ℝ))
                    * ((geomCofactorBlock (twoRangeLength β x) ((highBase a x : ℕ) : ℝ)
                        (lowEta c x) j).card : ℝ))
          + 2 * ∫ w in Set.Icc (-(twoRangeTop β x)) (twoRangeTop β x),
              ‖ramareLadderError (lowP a c β x) (twoRangeLength β x) ((highBase a x : ℕ) : ℝ)
                (lowEta c x) (expSteps a c β x) w‖ ^ 2)
      + (1 + 1 / twoRangeDelta x)
          * (∫ w in Set.Icc (-(twoRangeTop β x)) (twoRangeTop β x),
              ‖logPoly (fun n => ((μ n : ℤ) : ℂ))
                (supportMeanSquareRoughSet (lowP a c β x) (twoRangeLength β x)) w‖ ^ 2))
    + ((1 + twoRangeDelta x)
        * (2 * ((highSteps a₁ b c' x : ℕ) : ℝ) * ∑ j ∈ Finset.range (highSteps a₁ b c' x),
              highV A₀ δ₀ Ctot a₁ b c' β A₃ x j ^ 2
                * ladderHMBoundRecip (twoRangeLength β x) ((highBase a₁ x : ℕ) : ℝ)
                    (highEta c' x) (twoRangeTop β x)
                    (volume.real (lowExceptional a c A β b A₃ x)) j
          + 2 * ∫ w in Set.Icc (-(twoRangeTop β x)) (twoRangeTop β x),
              ‖ramareLadderError (highP a₁ b c' x) (twoRangeLength β x)
                ((highBase a₁ x : ℕ) : ℝ) (highEta c' x) (highSteps a₁ b c' x) w‖ ^ 2)
      + (1 + 1 / twoRangeDelta x)
          * (∫ w in Set.Icc (-(twoRangeTop β x)) (twoRangeTop β x),
              ‖logPoly (fun n => ((μ n : ℤ) : ℂ))
                (supportMeanSquareRoughSet (highP a₁ b c' x) (twoRangeLength β x)) w‖ ^ 2))

/-- A prime range is no larger than its top. -/
theorem card_primesRange_le_top (z₀ z : ℕ) : ((primesRange z₀ z).card : ℝ) ≤ (z : ℝ) := by
  classical
  have hsub : primesRange z₀ z ⊆ Finset.Icc 1 z := by
    intro p hp
    rw [mem_primesRange] at hp
    rw [Finset.mem_Icc]
    exact ⟨hp.1.one_lt.le.trans' (by norm_num), hp.2.2⟩
  have hc := Finset.card_le_card hsub
  rw [Nat.card_Icc] at hc
  have : ((primesRange z₀ z).card : ℝ) ≤ ((z + 1 - 1 : ℕ) : ℝ) := by exact_mod_cast hc
  simpa using this

/-- **The top of the high ladder, from below.** -/
theorem log_highTop_ge {a b c' : ℝ} (ha : 0 < a) (hab : a < b) (hc' : 0 < c') :
    ∀ᶠ x : ℝ in atTop,
      (Real.log x) ^ b - Real.log 4 ≤ Real.log ((highTop a b c' x : ℕ) : ℝ) := by
  have hzero := tendsto_highEta (c' := c') hc'
  have hcardb := tendsto_cardLength (β := b) (by linarith)
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ),
    Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1) hzero,
    hcardb.eventually_ge_atTop (8 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)] with x hx1 hη1 hb8 hlog1
  have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
  have hη : 0 < highEta c' x := highEta_pos hx1
  have hlogr : (0 : ℝ) < Real.log (1 + highEta c' x) := Real.log_pos (by linarith)
  have hQ0 : (0 : ℝ) < ((highBase a x : ℕ) : ℝ) := by
    have h1 := (highBase_bounds (a := a) hx1).1
    have h2 := cardLength_pos a x
    linarith
  have hmono : (Real.log x) ^ a ≤ (Real.log x) ^ b :=
    Real.rpow_le_rpow_of_exponent_le hlog1 hab.le
  have hfl : ((Real.log x) ^ b - (Real.log x) ^ a) / Real.log (1 + highEta c' x)
      < ((highSteps a b c' x : ℕ) : ℝ) + 1 := by
    rw [highSteps]
    exact Nat.lt_floor_add_one _
  have hA : (Real.log x) ^ b - (Real.log x) ^ a - Real.log (1 + highEta c' x)
      < Real.log ((1 + highEta c' x) ^ (highSteps a b c' x)) := by
    rw [Real.log_pow]
    have := mul_lt_mul_of_pos_right hfl hlogr
    rw [div_mul_cancel₀ _ (ne_of_gt hlogr)] at this
    linarith
  have hB : Real.exp ((Real.log x) ^ b - (Real.log x) ^ a - Real.log (1 + highEta c' x))
      < (1 + highEta c' x) ^ (highSteps a b c' x) := by
    have hpos : (0 : ℝ) < (1 + highEta c' x) ^ (highSteps a b c' x) := by positivity
    have := Real.exp_lt_exp.2 hA
    rwa [Real.exp_log hpos] at this
  have hexpid : Real.exp ((Real.log x) ^ b - (Real.log x) ^ a - Real.log (1 + highEta c' x))
      = cardLength b x / (cardLength a x * (1 + highEta c' x)) := by
    rw [Real.exp_sub, Real.exp_sub, Real.exp_log (by linarith), cardLength, cardLength]
    field_simp
  have hQlo : cardLength a x ≤ ((highBase a x : ℕ) : ℝ) := (highBase_bounds (a := a) hx1).1
  have hprod : cardLength b x / (1 + highEta c' x)
      < ((highBase a x : ℕ) : ℝ) * (1 + highEta c' x) ^ (highSteps a b c' x) := by
    have hstep : cardLength a x
        * (cardLength b x / (cardLength a x * (1 + highEta c' x)))
        < ((highBase a x : ℕ) : ℝ) * (1 + highEta c' x) ^ (highSteps a b c' x) := by
      have h1 : cardLength a x
          * Real.exp ((Real.log x) ^ b - (Real.log x) ^ a - Real.log (1 + highEta c' x))
          < cardLength a x * (1 + highEta c' x) ^ (highSteps a b c' x) :=
        mul_lt_mul_of_pos_left hB (cardLength_pos a x)
      have h2 : cardLength a x * (1 + highEta c' x) ^ (highSteps a b c' x)
          ≤ ((highBase a x : ℕ) : ℝ) * (1 + highEta c' x) ^ (highSteps a b c' x) :=
        mul_le_mul_of_nonneg_right hQlo (by positivity)
      rw [hexpid] at h1
      linarith
    have hid : cardLength a x * (cardLength b x / (cardLength a x * (1 + highEta c' x)))
        = cardLength b x / (1 + highEta c' x) := by
      field_simp
      exact div_self (ne_of_gt (cardLength_pos a x))
    rw [hid] at hstep
    exact hstep
  have hquarter : cardLength b x / 4 ≤ ((highTop a b c' x : ℕ) : ℝ) := by
    have hlt := Nat.lt_floor_add_one (((highBase a x : ℕ) : ℝ)
      * (1 + highEta c' x) ^ (highSteps a b c' x))
    have hTdef : ((highTop a b c' x : ℕ) : ℝ)
        = ((⌊((highBase a x : ℕ) : ℝ) * (1 + highEta c' x) ^ (highSteps a b c' x)⌋₊ : ℕ) : ℝ) := by
      rw [highTop]
    have hhalf : cardLength b x / 2 ≤ cardLength b x / (1 + highEta c' x) :=
      div_le_div_of_nonneg_left (cardLength_pos b x).le (by linarith) (by linarith)
    rw [hTdef]
    linarith [hprod, hlt, hhalf, hb8]
  have hlog4 : Real.log (cardLength b x / 4) = (Real.log x) ^ b - Real.log 4 := by
    rw [Real.log_div (ne_of_gt (cardLength_pos b x)) (by norm_num), log_cardLength]
  have := Real.log_le_log (by positivity : (0 : ℝ) < cardLength b x / 4) hquarter
  rw [hlog4] at this
  exact this

/-- **The harmonic mass of the high designated range, from below.** -/
theorem highRange_harmonic_ge {a b c' : ℝ} (ha : 0 < a) (hab : a < b) (hb1 : b < 1)
    (hc' : 0 < c') :
    ∀ᶠ x : ℝ in atTop,
      (b - a) / 2 * Real.log (Real.log x)
        ≤ ∑ p ∈ primesRange (highBase a x) (highTop a b c' x), 1 / (p : ℝ) := by
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
    log_highTop_ge (a := a) (b := b) (c' := c') ha hab hc',
    Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1) herr,
    hpowa.eventually_ge_atTop (1 : ℝ), hpowb.eventually_ge_atTop (4 : ℝ),
    hll.eventually_ge_atTop (2 * (2 * Real.log 2 + 1) / (b - a))]
    with x hx1 hlow hTlow hsmall hpa1 hpb4 hubig
  obtain ⟨h₀, hz⟩ := hlow
  have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
  have hmass := sum_inv_primesRange_ge_logLog_diff h₀ hz
  have hQ0 : (0 : ℝ) < ((highBase a x : ℕ) : ℝ) := by
    have h2 : (2 : ℝ) ≤ ((highBase a x : ℕ) : ℝ) := by exact_mod_cast h₀
    linarith
  have hl2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  have hlogQup : Real.log ((highBase a x : ℕ) : ℝ) ≤ 2 * (Real.log x) ^ a := by
    have hub := (highBase_bounds (a := a) hx1).2
    have hstep : Real.log ((highBase a x : ℕ) : ℝ) ≤ Real.log (2 * cardLength a x) :=
      Real.log_le_log hQ0 hub
    have hsplit : Real.log (2 * cardLength a x) = Real.log 2 + (Real.log x) ^ a := by
      rw [Real.log_mul (by norm_num) (ne_of_gt (cardLength_pos a x)), log_cardLength]
    linarith [hstep, hsplit, hl2, hpa1]
  have hlogQ0 : (0 : ℝ) < Real.log ((highBase a x : ℕ) : ℝ) := by
    have h2 : (2 : ℝ) ≤ ((highBase a x : ℕ) : ℝ) := by exact_mod_cast h₀
    have := Real.log_le_log (by norm_num : (0 : ℝ) < 2) h2
    have hl2p : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    linarith
  have hupperQ : Real.log (Real.log ((highBase a x : ℕ) : ℝ))
      ≤ Real.log 2 + a * Real.log (Real.log x) := by
    have hstep := Real.log_le_log hlogQ0 hlogQup
    have hsplit : Real.log (2 * (Real.log x) ^ a) = Real.log 2 + a * Real.log (Real.log x) := by
      rw [Real.log_mul (by norm_num) (ne_of_gt (Real.rpow_pos_of_pos hlogx a)),
        Real.log_rpow hlogx]
    linarith [hstep, hsplit]
  have hThalf : (Real.log x) ^ b / 2 ≤ Real.log ((highTop a b c' x : ℕ) : ℝ) := by
    rw [hl4] at hTlow
    nlinarith [hTlow, hpb4, hl2]
  have hT0 : (0 : ℝ) < Real.log ((highTop a b c' x : ℕ) : ℝ) := by
    have : (0 : ℝ) < (Real.log x) ^ b / 2 := by
      have := Real.rpow_pos_of_pos hlogx b
      linarith
    linarith [hThalf]
  have hlowerT : b * Real.log (Real.log x) - Real.log 2
      ≤ Real.log (Real.log ((highTop a b c' x : ℕ) : ℝ)) := by
    have hp0 : (0 : ℝ) < (Real.log x) ^ b / 2 := by
      have := Real.rpow_pos_of_pos hlogx b
      linarith
    have hstep := Real.log_le_log hp0 hThalf
    have hsplit : Real.log ((Real.log x) ^ b / 2) = b * Real.log (Real.log x) - Real.log 2 := by
      rw [Real.log_div (ne_of_gt (Real.rpow_pos_of_pos hlogx b)) (by norm_num),
        Real.log_rpow hlogx]
    linarith [hstep, hsplit]
  have herrle : 2 * ((2 * mertensFirstConst + 1 / 2) / Real.log ((highBase a x : ℕ) : ℝ))
      ≤ 2 * ((2 * mertensFirstConst + 1 / 2) / (Real.log x) ^ a) := by
    have hc0 : (0 : ℝ) ≤ 2 * mertensFirstConst + 1 / 2 := by
      have := mertensFirstConst_nonneg
      linarith
    have hp0 : (0 : ℝ) < (Real.log x) ^ a := Real.rpow_pos_of_pos hlogx a
    have hlogQ : (Real.log x) ^ a ≤ Real.log ((highBase a x : ℕ) : ℝ) := by
      have h1 := (highBase_bounds (a := a) hx1).1
      have := Real.log_le_log (cardLength_pos a x) h1
      rwa [log_cardLength] at this
    have := div_le_div_of_nonneg_left hc0 hp0 hlogQ
    linarith
  have hslack : 2 * Real.log 2 + 1 ≤ (b - a) / 2 * Real.log (Real.log x) := by
    have hba : (0 : ℝ) < b - a := by linarith
    rw [div_le_iff₀ hba] at hubig
    nlinarith [hubig, hba]
  linarith [hmass, hupperQ, hlowerT, herrle, hsmall, hslack]

/-- The Gallagher window is below the length of the Dirichlet polynomial. -/
theorem twoRangeTop_le_length {β : ℝ} (hβ0 : 0 < β) (_hβ1 : β < 1) :
    ∀ᶠ x : ℝ in atTop, twoRangeTop β x ≤ ((twoRangeLength β x : ℕ) : ℝ) := by
  have hquot : Tendsto (fun x : ℝ =>
      (Real.log x) ^ (0 : ℝ) * (Real.log (Real.log x)) ^ 1 / cardLength β x) atTop (𝓝 0) :=
    tendsto_logMonomial_div_cardLength (β := β) hβ0 0 1
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ),
    Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1) hquot,
    Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)] with x hx1 hsm hlog1
  have hh0 : (0 : ℝ) < cardLength β x := cardLength_pos β x
  have hu0 : (0 : ℝ) ≤ Real.log (Real.log x) := Real.log_nonneg hlog1
  have hM0 : (0 : ℝ) ≤ ((twoRangeLength β x : ℕ) : ℝ) := Nat.cast_nonneg _
  have hid : (Real.log x) ^ (0 : ℝ) * (Real.log (Real.log x)) ^ 1 / cardLength β x
      = Real.log (Real.log x) / cardLength β x := by
    rw [Real.rpow_zero, pow_one, one_mul]
  rw [hid, div_le_one hh0] at hsm
  rw [twoRangeTop, twoRangeCut]
  rw [div_mul_eq_mul_div, div_le_iff₀ hh0]
  nlinarith [hsm, hM0, hh0]

private theorem mul_div_le_two {p q r s : ℝ} (_hp0 : 0 ≤ p) (hp2 : p ≤ 2) (hq0 : 0 ≤ q)
    (hqr : q ≤ r) (hs : 0 < s) : p * q / s ≤ 2 * (r / s) := by
  have h1 : p * q ≤ 2 * r := by nlinarith
  calc p * q / s ≤ 2 * r / s := div_le_div_of_nonneg_right h1 hs.le
    _ = 2 * (r / s) := by ring

/-- **The small half's ladder group vanishes at the schedule.** -/
theorem tendsto_smallLadderPiece {a c A β : ℝ} (ha : 0 < a) (hab : a < β) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hc : 0 < c) (h2A : β + c < 2 * A) :
    Tendsto (fun x : ℝ =>
      (1 + twoRangeDelta x)
        * (2 * ((expSteps a c β x : ℕ) : ℝ) * ∑ j ∈ Finset.range (expSteps a c β x),
              lowV a c A β x j ^ 2
                * ((5 * Real.pi / 2 * twoRangeTop β x
                      + 5 * Real.exp 1 / 2
                        * ((⌊((twoRangeLength β x : ℕ) : ℝ)
                            / (((highBase a x : ℕ) : ℝ) * (1 + lowEta c x) ^ j)⌋₊ : ℕ) : ℝ))
                    * ((geomCofactorBlock (twoRangeLength β x) ((highBase a x : ℕ) : ℝ)
                        (lowEta c x) j).card : ℝ)))
        / ((twoRangeLength β x : ℕ) : ℝ) ^ 2) atTop (𝓝 0) := by
  have hmain := tendsto_smallLadderGroup_div_sq (β := β) (c := c) (A := A) hβ0 hβ1 hc h2A
    (Lf := fun x => ((expSteps a c β x : ℕ) : ℝ))
    (Bf := fun x => ((highBase a x : ℕ) : ℝ) * (1 + lowEta c x) ^ (expSteps a c β x)
        * lowEta c x + 1)
    (Sf := fun x => (1 + lowEta c x) * ((twoRangeLength β x : ℕ) : ℝ)
        * rangeHarmonic (lowP a c β x))
    (Pf := fun x => ((lowP a c β x).card : ℝ))
    ?_ ?_ ?_ ?_
  · have hmul : Tendsto (fun x : ℝ => 2 * ((5 * Real.pi * ((expSteps a c β x : ℕ) : ℝ)
        * lowTheta A x ^ 2 * twoRangeTop β x
          * ((((highBase a x : ℕ) : ℝ) * (1 + lowEta c x) ^ (expSteps a c β x) * lowEta c x + 1)
              * ((1 + lowEta c x) * ((twoRangeLength β x : ℕ) : ℝ)
                * rangeHarmonic (lowP a c β x))
            + (((highBase a x : ℕ) : ℝ) * (1 + lowEta c x) ^ (expSteps a c β x) * lowEta c x + 1)
              * ((lowP a c β x).card : ℝ))
        + 5 * Real.exp 1 * ((expSteps a c β x : ℕ) : ℝ) * lowTheta A x ^ 2
          * (((1 + lowEta c x) * ((twoRangeLength β x : ℕ) : ℝ)
                * rangeHarmonic (lowP a c β x)) ^ 2
            + (((highBase a x : ℕ) : ℝ) * (1 + lowEta c x) ^ (expSteps a c β x) * lowEta c x + 1)
              * ((1 + lowEta c x) * ((twoRangeLength β x : ℕ) : ℝ)
                * rangeHarmonic (lowP a c β x))))
        / ((twoRangeLength β x : ℕ) : ℝ) ^ 2)) atTop (𝓝 0) := by
      have := hmain.const_mul (2 : ℝ)
      rw [show ((2 : ℝ) * 0) = 0 by ring] at this
      exact this
    refine squeeze_zero' ?_ ?_ hmul
    · filter_upwards [Filter.eventually_gt_atTop (Real.exp 1),
        Filter.eventually_gt_atTop (1 : ℝ), one_le_twoRangeTop hβ0 hβ1] with x hxe hx1 hW
      have hδ : (0 : ℝ) < twoRangeDelta x := twoRangeDelta_pos hxe
      have hsum : (0 : ℝ) ≤ ∑ j ∈ Finset.range (expSteps a c β x),
          lowV a c A β x j ^ 2
            * ((5 * Real.pi / 2 * twoRangeTop β x
                  + 5 * Real.exp 1 / 2
                    * ((⌊((twoRangeLength β x : ℕ) : ℝ)
                        / (((highBase a x : ℕ) : ℝ) * (1 + lowEta c x) ^ j)⌋₊ : ℕ) : ℝ))
                * ((geomCofactorBlock (twoRangeLength β x) ((highBase a x : ℕ) : ℝ)
                    (lowEta c x) j).card : ℝ)) := by
        refine Finset.sum_nonneg fun j _ => ?_
        have h1 : (0 : ℝ) ≤ 5 * Real.pi / 2 * twoRangeTop β x
            + 5 * Real.exp 1 / 2
              * ((⌊((twoRangeLength β x : ℕ) : ℝ)
                  / (((highBase a x : ℕ) : ℝ) * (1 + lowEta c x) ^ j)⌋₊ : ℕ) : ℝ) := by
          have := Real.pi_pos
          have h2 : (0 : ℝ) ≤ twoRangeTop β x := by linarith
          positivity
        have h2 : (0 : ℝ) ≤ ((geomCofactorBlock (twoRangeLength β x) ((highBase a x : ℕ) : ℝ)
            (lowEta c x) j).card : ℝ) := Nat.cast_nonneg _
        have := mul_nonneg h1 h2
        positivity
      have hL0 : (0 : ℝ) ≤ ((expSteps a c β x : ℕ) : ℝ) := Nat.cast_nonneg _
      refine div_nonneg (mul_nonneg (by linarith) ?_) (by positivity)
      exact mul_nonneg (by positivity) hsum
    · filter_upwards [Filter.eventually_gt_atTop (Real.exp 1),
        Filter.eventually_gt_atTop (1 : ℝ), one_le_twoRangeTop hβ0 hβ1,
        two_le_highBase_and_le_expTop (a := a) (c := c) (β := β) ha hc,
        one_le_expSteps (a := a) (c := c) (β := β) ha hab hc,
        one_le_twoRangeLength hβ0,
        Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1) tendsto_twoRangeDelta]
        with x hxe hx1 hW hlow hL hM1 hδ1
      have hM0 : (0 : ℝ) < ((twoRangeLength β x : ℕ) : ℝ) := by linarith
      have hR0 : (0 : ℝ) < ((highBase a x : ℕ) : ℝ) := by
        have : (2 : ℝ) ≤ ((highBase a x : ℕ) : ℝ) := by exact_mod_cast hlow.1
        linarith
      have hδ : (0 : ℝ) < twoRangeDelta x := twoRangeDelta_pos hxe
      have hcong : ∀ j : ℕ, lowV a c A β x j ^ 2
          = (lowTheta A x * ((geomBlock (lowP a c β x) ((highBase a x : ℕ) : ℝ)
              (1 + lowEta c x) j).card : ℝ)) ^ 2 := by
        intro j
        rw [lowV]
        ring
      have hgroup := smallLadderGroup_le (P := lowP a c β x) (twoRangeLength β x)
        (R := ((highBase a x : ℕ) : ℝ)) (η := lowEta c x) (W := twoRangeTop β x)
        (θ := lowTheta A x) hR0 (lowEta_pos hx1).le (by linarith) hL
        (primesRange_ladder_bounds_self rfl (lowEta_pos hx1).le hR0.le rfl)
      rw [Finset.sum_congr rfl (fun j _ => by rw [hcong j])]
      have hnn : (0 : ℝ) ≤ 2 * ((expSteps a c β x : ℕ) : ℝ)
          * ∑ j ∈ Finset.range (expSteps a c β x),
            (lowTheta A x * ((geomBlock (lowP a c β x) ((highBase a x : ℕ) : ℝ)
                (1 + lowEta c x) j).card : ℝ)) ^ 2
              * ((5 * Real.pi / 2 * twoRangeTop β x
                    + 5 * Real.exp 1 / 2
                      * ((⌊((twoRangeLength β x : ℕ) : ℝ)
                          / (((highBase a x : ℕ) : ℝ) * (1 + lowEta c x) ^ j)⌋₊ : ℕ) : ℝ))
                  * ((geomCofactorBlock (twoRangeLength β x) ((highBase a x : ℕ) : ℝ)
                      (lowEta c x) j).card : ℝ)) := by
        refine mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ => ?_)
        have h1 : (0 : ℝ) ≤ 5 * Real.pi / 2 * twoRangeTop β x
            + 5 * Real.exp 1 / 2
              * ((⌊((twoRangeLength β x : ℕ) : ℝ)
                  / (((highBase a x : ℕ) : ℝ) * (1 + lowEta c x) ^ j)⌋₊ : ℕ) : ℝ) := by
          have := Real.pi_pos
          have h2 : (0 : ℝ) ≤ twoRangeTop β x := by linarith
          positivity
        have h2 : (0 : ℝ) ≤ ((geomCofactorBlock (twoRangeLength β x) ((highBase a x : ℕ) : ℝ)
            (lowEta c x) j).card : ℝ) := Nat.cast_nonneg _
        have := mul_nonneg h1 h2
        positivity
      have hq0 : (0 : ℝ) ≤ (2 * ((expSteps a c β x : ℕ) : ℝ)
          * ∑ j ∈ Finset.range (expSteps a c β x),
            (lowTheta A x * ((geomBlock (lowP a c β x) ((highBase a x : ℕ) : ℝ)
                (1 + lowEta c x) j).card : ℝ)) ^ 2
              * ((5 * Real.pi / 2 * twoRangeTop β x
                    + 5 * Real.exp 1 / 2
                      * ((⌊((twoRangeLength β x : ℕ) : ℝ)
                          / (((highBase a x : ℕ) : ℝ) * (1 + lowEta c x) ^ j)⌋₊ : ℕ) : ℝ))
                  * ((geomCofactorBlock (twoRangeLength β x) ((highBase a x : ℕ) : ℝ)
                      (lowEta c x) j).card : ℝ))) := hnn
      exact mul_div_le_two (by linarith) (by linarith) hq0 hgroup (by positivity)
  · filter_upwards [expSteps_le (a := a) (c := c) (β := β) ha hc hβ0] with x hle
    exact ⟨Nat.cast_nonneg _, hle⟩
  · filter_upwards [Filter.eventually_gt_atTop (1 : ℝ),
      expTop_le_cardLength (a := a) (c := c) (β := β) ha hab hc] with x hx1 htop
    have hη0 : (0 : ℝ) < lowEta c x := lowEta_pos hx1
    have hR0 : (0 : ℝ) ≤ ((highBase a x : ℕ) : ℝ) := Nat.cast_nonneg _
    refine ⟨by positivity, ?_⟩
    have : ((highBase a x : ℕ) : ℝ) * (1 + lowEta c x) ^ (expSteps a c β x) * lowEta c x
        ≤ cardLength β x * lowEta c x :=
      mul_le_mul_of_nonneg_right htop hη0.le
    have hηid : (Real.log x) ^ (-c) = lowEta c x := rfl
    rw [hηid]
    linarith [this]
  · filter_upwards [Filter.eventually_gt_atTop (1 : ℝ),
      expRange_harmonic_le (a := a) (c := c) (β := β) ha hab hc,
      Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1) (tendsto_lowEta hc),
      Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ),
      one_le_twoRangeLength hβ0] with x hx1 hH hη1 hlog1 hM1
    have hη0 : (0 : ℝ) < lowEta c x := lowEta_pos hx1
    have hu0 : (0 : ℝ) ≤ Real.log (Real.log x) := Real.log_nonneg hlog1
    have hH0 : (0 : ℝ) ≤ rangeHarmonic (lowP a c β x) :=
      Finset.sum_nonneg fun p _ => by positivity
    refine ⟨by positivity, ?_⟩
    have hHu : rangeHarmonic (lowP a c β x) ≤ Real.log (Real.log x) := by
      have : rangeHarmonic (lowP a c β x) ≤ β * Real.log (Real.log x) := hH
      nlinarith [this, hu0, hβ1]
    have hMH : (0 : ℝ) ≤ ((twoRangeLength β x : ℕ) : ℝ) * rangeHarmonic (lowP a c β x) := by
      have hM0 : (0 : ℝ) ≤ ((twoRangeLength β x : ℕ) : ℝ) := Nat.cast_nonneg _
      exact mul_nonneg hM0 hH0
    have hstep1 : (1 + lowEta c x) * ((twoRangeLength β x : ℕ) : ℝ)
          * rangeHarmonic (lowP a c β x)
        ≤ 2 * (((twoRangeLength β x : ℕ) : ℝ) * rangeHarmonic (lowP a c β x)) := by
      nlinarith [hη1, hMH]
    have hstep2 : 2 * (((twoRangeLength β x : ℕ) : ℝ) * rangeHarmonic (lowP a c β x))
        ≤ 2 * ((twoRangeLength β x : ℕ) : ℝ) * Real.log (Real.log x) := by
      have hM0 : (0 : ℝ) ≤ ((twoRangeLength β x : ℕ) : ℝ) := Nat.cast_nonneg _
      nlinarith [hHu, hM0]
    linarith
  · filter_upwards [Filter.eventually_gt_atTop (1 : ℝ),
      expTop_le_cardLength (a := a) (c := c) (β := β) ha hab hc] with x hx1 htop
    refine ⟨Nat.cast_nonneg _, ?_⟩
    have h1 : ((lowP a c β x).card : ℝ) ≤ ((expTop a c β x : ℕ) : ℝ) :=
      card_primesRange_le_top _ _
    have h2 : ((expTop a c β x : ℕ) : ℝ) ≤ cardLength β x := by
      rw [expTop]
      refine le_trans (Nat.floor_le ?_) htop
      have hη0 : (0 : ℝ) < lowEta c x := lowEta_pos hx1
      positivity
    linarith

/-- **A ladder's discrepancy group vanishes at the schedule.**  The statement is range-agnostic:
`Q` is the ladder's bottom, `η = (log x)^{−c}` its step ratio, `L` its step count and `hR` its top. -/
theorem tendsto_defectPiece {β γ ℓ c K : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ0 : 0 < γ)
    (hγ1 : γ < 1) (hℓ : 1 + ℓ < 2 * c) (hK1 : 1 < K) (hK2 : 1 + c < 2 * K) (hc0 : 0 < c)
    {P : ℝ → Finset ℕ} {Q Lf HR : ℝ → ℝ} {Ls : ℝ → ℕ}
    (hprime : ∀ᶠ x : ℝ in atTop, ∀ p ∈ P x, p.Prime)
    (hQ1 : ∀ᶠ x : ℝ in atTop, 1 < Q x)
    (hlogQ : ∀ᶠ x : ℝ in atTop, 1 ≤ Real.log (Q x))
    (hQK : ∀ᶠ x : ℝ in atTop, (Real.log x) ^ K ≤ Q x)
    (hPge : ∀ᶠ x : ℝ in atTop, ∀ p ∈ P x, Q x ≤ (p : ℝ))
    (hLdef : ∀ᶠ x : ℝ in atTop, Lf x = ((Ls x : ℕ) : ℝ))
    (hLf : ∀ᶠ x : ℝ in atTop, Lf x ≤ 2 * (Real.log x) ^ ℓ)
    (htop : ∀ᶠ x : ℝ in atTop, Q x * (1 + lowEta c x) ^ (Ls x) ≤ HR x)
    (hHR : ∀ᶠ x : ℝ in atTop, 0 ≤ HR x ∧ HR x ≤ 2 * cardLength γ x) :
    Tendsto (fun x : ℝ =>
      (1 + twoRangeDelta x)
        * (2 * ∫ w in Set.Icc (-(twoRangeTop β x)) (twoRangeTop β x),
            ‖ramareLadderError (P x) (twoRangeLength β x) (Q x) (lowEta c x) (Ls x) w‖ ^ 2)
        / ((twoRangeLength β x : ℕ) : ℝ) ^ 2) atTop (𝓝 0) := by
  set Cf : ℝ → ℝ := fun x => 5 * Real.pi / 2 * twoRangeTop β x
      + 5 * Real.exp 1 / 2
        * ((⌊((twoRangeLength β x : ℕ) : ℝ) * (1 + lowEta c x)⌋₊ : ℕ) : ℝ) with hCfdef
  set Rf : ℝ → ℝ := fun x =>
      Real.log ((⌊((twoRangeLength β x : ℕ) : ℝ) * (1 + lowEta c x)⌋₊ : ℕ) : ℝ)
        / Real.log (Q x) with hRfdef
  have hbase := tendsto_defectGroup_div_sq (β := β) (γ := γ) (ℓ := ℓ) (c := c) (K := K)
    hβ0 hβ1 hγ0 hγ1 hℓ hK1 hK2 (Cf := Cf) (Rf := Rf) (Lf := Lf) (Qf := Q) (HRf := HR)
    ?_ ?_ ?_ hQK hHR
  · have hg : Tendsto (fun x : ℝ => 4 * (Cf x * (Rf x * (Lf x * ((1 + ((twoRangeLength β x : ℕ) : ℝ))
          * ((Real.log x) ^ (-c)) ^ 2 + 5)
        + 5 * HR x
        + ((Real.log x) ^ (-c) * ((twoRangeLength β x : ℕ) : ℝ)
            + (1 + ((twoRangeLength β x : ℕ) : ℝ)) * (Real.log x) ^ (-c))
          * (2 / (Q x * (Real.log x) ^ (-c)))
        + ((twoRangeLength β x : ℕ) : ℝ) * (2 / (Q x ^ 2 * (Real.log x) ^ (-c)))))
        / ((twoRangeLength β x : ℕ) : ℝ) ^ 2)) atTop (𝓝 0) := by
      have := hbase.const_mul (4 : ℝ)
      rw [show ((4 : ℝ) * 0) = 0 by ring] at this
      exact this
    refine squeeze_zero' ?_ ?_ hg
    · filter_upwards [Filter.eventually_gt_atTop (Real.exp 1)] with x hxe
      have hδ : (0 : ℝ) < twoRangeDelta x := twoRangeDelta_pos hxe
      have hI : (0 : ℝ) ≤ ∫ w in Set.Icc (-(twoRangeTop β x)) (twoRangeTop β x),
          ‖ramareLadderError (P x) (twoRangeLength β x) (Q x) (lowEta c x) (Ls x) w‖ ^ 2 := by
        refine MeasureTheory.setIntegral_nonneg measurableSet_Icc fun w _ => by positivity
      refine div_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity)
    · filter_upwards [Filter.eventually_gt_atTop (Real.exp 1), Filter.eventually_gt_atTop (1 : ℝ),
        one_le_twoRangeTop hβ0 hβ1, hprime, hQ1, hPge, hLdef, htop,
        Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1) tendsto_twoRangeDelta,
        Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1) (tendsto_lowEta hc0),
        one_le_twoRangeLength hβ0]
        with x hxe hx1 hW hpr hQ1x hPgex hLdx htopx hδ1 hη1 hM1
      have hη0 : (0 : ℝ) < lowEta c x := lowEta_pos hx1
      have hM0 : (0 : ℝ) < ((twoRangeLength β x : ℕ) : ℝ) := by linarith
      have hCf0 : (0 : ℝ) ≤ Cf x := by
        rw [hCfdef]
        have := Real.pi_pos
        have h2 : (0 : ℝ) ≤ twoRangeTop β x := by linarith
        positivity
      have hint := integral_normSq_ramareLadderError_le_defectSum (P := P x)
        (twoRangeLength β x) (Q := Q x) (η := lowEta c x) (W := twoRangeTop β x) (L := Ls x)
        hQ1x hη0.le hW hpr hPgex
      have hdef := ladderDefectSum_le (B₀ := twoRangeLength β x) (Q := Q x) (η := lowEta c x)
        (hR := HR x) (L := Ls x) hQ1x hη0 hη1 htopx
      have hchain : (∫ w in Set.Icc (-(twoRangeTop β x)) (twoRangeTop β x),
            ‖ramareLadderError (P x) (twoRangeLength β x) (Q x) (lowEta c x) (Ls x) w‖ ^ 2)
          ≤ Cf x * (Rf x * (Lf x * ((1 + ((twoRangeLength β x : ℕ) : ℝ))
                * ((Real.log x) ^ (-c)) ^ 2 + 5)
              + 5 * HR x
              + ((Real.log x) ^ (-c) * ((twoRangeLength β x : ℕ) : ℝ)
                  + (1 + ((twoRangeLength β x : ℕ) : ℝ)) * (Real.log x) ^ (-c))
                * (2 / (Q x * (Real.log x) ^ (-c)))
              + ((twoRangeLength β x : ℕ) : ℝ) * (2 / (Q x ^ 2 * (Real.log x) ^ (-c))))) := by
        refine hint.trans ?_
        rw [hLdx]
        exact mul_le_mul_of_nonneg_left hdef hCf0
      have hI0 : (0 : ℝ) ≤ 2 * ∫ w in Set.Icc (-(twoRangeTop β x)) (twoRangeTop β x),
          ‖ramareLadderError (P x) (twoRangeLength β x) (Q x) (lowEta c x) (Ls x) w‖ ^ 2 := by
        have : (0 : ℝ) ≤ ∫ w in Set.Icc (-(twoRangeTop β x)) (twoRangeTop β x),
            ‖ramareLadderError (P x) (twoRangeLength β x) (Q x) (lowEta c x) (Ls x) w‖ ^ 2 :=
          MeasureTheory.setIntegral_nonneg measurableSet_Icc fun w _ => by positivity
        linarith
      have hstep := mul_div_le_two (p := 1 + twoRangeDelta x)
        (q := 2 * ∫ w in Set.Icc (-(twoRangeTop β x)) (twoRangeTop β x),
            ‖ramareLadderError (P x) (twoRangeLength β x) (Q x) (lowEta c x) (Ls x) w‖ ^ 2)
        (r := 2 * (Cf x * (Rf x * (Lf x * ((1 + ((twoRangeLength β x : ℕ) : ℝ))
                * ((Real.log x) ^ (-c)) ^ 2 + 5)
              + 5 * HR x
              + ((Real.log x) ^ (-c) * ((twoRangeLength β x : ℕ) : ℝ)
                  + (1 + ((twoRangeLength β x : ℕ) : ℝ)) * (Real.log x) ^ (-c))
                * (2 / (Q x * (Real.log x) ^ (-c)))
              + ((twoRangeLength β x : ℕ) : ℝ) * (2 / (Q x ^ 2 * (Real.log x) ^ (-c)))))))
        (s := ((twoRangeLength β x : ℕ) : ℝ) ^ 2)
        (by have := twoRangeDelta_pos hxe; linarith) (by linarith) hI0 (by linarith)
        (by positivity)
      refine hstep.trans (le_of_eq ?_)
      field_simp
      ring
  · filter_upwards [Filter.eventually_gt_atTop (Real.exp 1), Filter.eventually_gt_atTop (1 : ℝ),
      one_le_twoRangeTop hβ0 hβ1, twoRangeTop_le_length hβ0 hβ1,
      Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1) (tendsto_lowEta hc0),
      one_le_twoRangeLength hβ0] with x hxe hx1 hW hWM hη1 hM1
    have hη0 : (0 : ℝ) < lowEta c x := lowEta_pos hx1
    have hM0 : (0 : ℝ) < ((twoRangeLength β x : ℕ) : ℝ) := by linarith
    have hfl : ((⌊((twoRangeLength β x : ℕ) : ℝ) * (1 + lowEta c x)⌋₊ : ℕ) : ℝ)
        ≤ 2 * ((twoRangeLength β x : ℕ) : ℝ) := by
      refine le_trans (Nat.floor_le (by positivity)) ?_
      nlinarith [hη1, hM0]
    have hpi : Real.pi < 3.15 := Real.pi_lt_d2
    have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    have hCf0 : (0 : ℝ) ≤ Cf x := by
      rw [hCfdef]
      have := Real.pi_pos
      have h2 : (0 : ℝ) ≤ twoRangeTop β x := by linarith
      positivity
    refine ⟨hCf0, ?_⟩
    rw [hCfdef]
    nlinarith [hWM, hfl, hpi, he, hM0, Real.pi_pos, (Real.exp_pos (1 : ℝ))]
  · filter_upwards [Filter.eventually_gt_atTop (1 : ℝ), hQ1, hQK,
      Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1) (tendsto_lowEta hc0),
      one_le_twoRangeLength hβ0, twoRangeLength_le_two_sqrt hβ0 hβ1,
      Filter.eventually_ge_atTop (16 : ℝ), hlogQ]
      with x hx1 hQ1x hQKx hη1 hM1 hM2 hx16 hlogQ1
    have hη0 : (0 : ℝ) < lowEta c x := lowEta_pos hx1
    have hM0 : (0 : ℝ) < ((twoRangeLength β x : ℕ) : ℝ) := by linarith
    have hlogQ0 : (0 : ℝ) < Real.log (Q x) := by linarith
    have hfl1 : (1 : ℝ) ≤ ((⌊((twoRangeLength β x : ℕ) : ℝ) * (1 + lowEta c x)⌋₊ : ℕ) : ℝ) := by
      have : (1 : ℕ) ≤ ⌊((twoRangeLength β x : ℕ) : ℝ) * (1 + lowEta c x)⌋₊ := by
        refine Nat.le_floor ?_
        push_cast
        nlinarith [hM1, hη0]
      exact_mod_cast this
    have hfl : ((⌊((twoRangeLength β x : ℕ) : ℝ) * (1 + lowEta c x)⌋₊ : ℕ) : ℝ)
        ≤ 4 * Real.sqrt x := by
      refine le_trans (Nat.floor_le (by positivity)) ?_
      nlinarith [hη1, hM0, hM2]
    have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt (by linarith)
    have hs0 : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
    have hlogfl : Real.log ((⌊((twoRangeLength β x : ℕ) : ℝ) * (1 + lowEta c x)⌋₊ : ℕ) : ℝ)
        ≤ Real.log x := by
      refine Real.log_le_log (by linarith) ?_
      nlinarith [hfl, hs0, hsq, hx16]
    have hnum0 : (0 : ℝ)
        ≤ Real.log ((⌊((twoRangeLength β x : ℕ) : ℝ) * (1 + lowEta c x)⌋₊ : ℕ) : ℝ) :=
      Real.log_nonneg hfl1
    refine ⟨by rw [hRfdef]; positivity, ?_⟩
    rw [hRfdef]
    rw [div_le_iff₀ hlogQ0]
    nlinarith [hlogfl, hlogQ1, Real.log_pos hx1]
  · filter_upwards [hLdef, hLf] with x hd hl
    exact ⟨by rw [hd]; exact Nat.cast_nonneg _, hl⟩

set_option maxHeartbeats 4000000 in
/-- **Every high block's base is at most a polylogarithm times its cardinality.** -/
theorem highBlock_base_le_card {a₁ b c' : ℝ} (ha₁ : 0 < a₁) (hab : a₁ < b) (hb1 : b < 1)
    (hc' : 0 < c') :
    ∀ᶠ x : ℝ in atTop, ∀ j ∈ Finset.range (highSteps a₁ b c' x),
      ((highBase a₁ x : ℕ) : ℝ) * (1 + highEta c' x) ^ j
        ≤ 8 * (Real.log x) ^ (b + c')
          * ((geomBlock (highP a₁ b c' x) ((highBase a₁ x : ℕ) : ℝ)
              (1 + highEta c' x) j).card : ℝ) := by
  obtain ⟨C, c₀, hc₀, hC, hcnt⟩ := exists_card_windowPrimes_ge
  obtain ⟨y₀, hy₀⟩ := Filter.eventually_atTop.1 hcnt
  have hd1 : Tendsto (fun x : ℝ =>
      (Real.log x) ^ c' * (16 * C * Real.exp (-(c₀ * (Real.log x) ^ (a₁ / 2))))) atTop (𝓝 0) := by
    have h := tendsto_logRpow_mul_expSaving (d := a₁ / 2) (s := c₀) (by linarith) hc₀ c'
    have := h.const_mul (16 * C)
    rw [show ((16 : ℝ) * C * 0) = 0 by ring] at this
    refine this.congr fun x => ?_
    ring
  have hd2 : Tendsto (fun x : ℝ =>
      (Real.log x) ^ c' * (96 * Real.exp (-(1 / 4 * (Real.log x) ^ a₁)))) atTop (𝓝 0) := by
    have h := tendsto_logRpow_mul_expSaving (d := a₁) (s := (1 : ℝ) / 4) ha₁ (by norm_num) c'
    have := h.const_mul (96 : ℝ)
    rw [show ((96 : ℝ) * 0) = 0 by ring] at this
    refine this.congr fun x => ?_
    ring
  have hzero := tendsto_highEta (c' := c') hc'
  have hpowa : Tendsto (fun x : ℝ => (Real.log x) ^ a₁) atTop atTop :=
    (tendsto_rpow_atTop ha₁).comp Real.tendsto_log_atTop
  have hcarda := tendsto_cardLength (β := a₁) ha₁
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ),
    Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1) hzero,
    Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 2) hd1,
    Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 2) hd2,
    hcarda.eventually_ge_atTop (max y₀ (Real.exp 2)),
    hpowa.eventually_ge_atTop (2 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ),
    highLadder_le (a := a₁) (b := b) (c' := c') hab.le hc',
    two_le_highBase_and_le_highTop (a := a₁) (b := b) (c' := c') ha₁]
    with x hx1 hη1 hdec1 hdec2 hbigcard hpa2 hlog1 htop hlow2
  intro j hj
  have hjL : j + 1 ≤ highSteps a₁ b c' x := Finset.mem_range.1 hj
  set R : ℝ := ((highBase a₁ x : ℕ) : ℝ) with hRdef
  set η : ℝ := highEta c' x with hηdef
  have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
  have hη0 : (0 : ℝ) < η := highEta_pos hx1
  have hRlo : cardLength a₁ x ≤ R := (highBase_bounds (a := a₁) hx1).1
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le (cardLength_pos a₁ x) hRlo
  have hpowj : (1 : ℝ) ≤ (1 + η) ^ j := one_le_pow₀ (by linarith)
  have hRj0 : (0 : ℝ) < R * (1 + η) ^ j := by positivity
  have hRjlo : cardLength a₁ x ≤ R * (1 + η) ^ j := by
    nlinarith [hRlo, hpowj, cardLength_pos a₁ x]
  have hRjy₀ : max y₀ (Real.exp 2) ≤ R * (1 + η) ^ j := le_trans hbigcard hRjlo
  have hlogRjlo : (Real.log x) ^ a₁ ≤ Real.log (R * (1 + η) ^ j) := by
    have := Real.log_le_log (cardLength_pos a₁ x) hRjlo
    rwa [log_cardLength] at this
  have hlogRj0 : (0 : ℝ) < Real.log (R * (1 + η) ^ j) := by linarith [hpa2, hlogRjlo]
  have hmono : (1 + η) ^ j ≤ (1 + η) ^ (highSteps a₁ b c' x) :=
    pow_le_pow_right₀ (by linarith) (by omega)
  have hRjhi : R * (1 + η) ^ j ≤ 2 * cardLength b x :=
    le_trans (mul_le_mul_of_nonneg_left hmono hR0.le) htop
  have hlogRjhi : Real.log (R * (1 + η) ^ j) ≤ 2 * (Real.log x) ^ b := by
    have hstep := Real.log_le_log hRj0 hRjhi
    have hid : Real.log (2 * cardLength b x) = Real.log 2 + (Real.log x) ^ b := by
      rw [Real.log_mul (by norm_num) (ne_of_gt (cardLength_pos b x)), log_cardLength]
    have hl2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    have hpb1 : (1 : ℝ) ≤ (Real.log x) ^ b := Real.one_le_rpow hlog1 (by linarith)
    linarith [hstep, hid]
  -- the prime count
  have hsqrtlo : (Real.log x) ^ (a₁ / 2) ≤ Real.sqrt (Real.log (R * (1 + η) ^ j)) := by
    have h1 : Real.sqrt ((Real.log x) ^ a₁) ≤ Real.sqrt (Real.log (R * (1 + η) ^ j)) :=
      Real.sqrt_le_sqrt hlogRjlo
    have h2 : Real.sqrt ((Real.log x) ^ a₁) = (Real.log x) ^ (a₁ / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hlogx.le]
      congr 1
      ring
    linarith [h1, h2]
  have hηinv : η * (Real.log x) ^ c' = 1 := by
    rw [hηdef, highEta, ← Real.rpow_add hlogx]
    simp
  have hterm1 : 16 * C * Real.exp (-c₀ * Real.sqrt (Real.log (R * (1 + η) ^ j))) ≤ η / 2 := by
    have hmono2 : Real.exp (-c₀ * Real.sqrt (Real.log (R * (1 + η) ^ j)))
        ≤ Real.exp (-(c₀ * (Real.log x) ^ (a₁ / 2))) :=
      Real.exp_le_exp.2 (by nlinarith [hsqrtlo, hc₀])
    have hstep : 16 * C * Real.exp (-c₀ * Real.sqrt (Real.log (R * (1 + η) ^ j)))
        ≤ 16 * C * Real.exp (-(c₀ * (Real.log x) ^ (a₁ / 2))) := by
      nlinarith [hmono2, hC, Real.exp_pos (-(c₀ * (Real.log x) ^ (a₁ / 2)))]
    have hmul := mul_le_mul_of_nonneg_left hdec1 (le_of_lt hη0)
    have hid : η * ((Real.log x) ^ c' * (16 * C * Real.exp (-(c₀ * (Real.log x) ^ (a₁ / 2)))))
        = 16 * C * Real.exp (-(c₀ * (Real.log x) ^ (a₁ / 2))) := by
      rw [show η * ((Real.log x) ^ c' * (16 * C * Real.exp (-(c₀ * (Real.log x) ^ (a₁ / 2)))))
          = (η * (Real.log x) ^ c') * (16 * C * Real.exp (-(c₀ * (Real.log x) ^ (a₁ / 2)))) by
        ring, hηinv, one_mul]
    rw [hid] at hmul
    linarith [hstep, hmul]
  have hq0 : (0 : ℝ) < (R * (1 + η) ^ j) ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hRj0 _
  have hlogq : Real.log (R * (1 + η) ^ j) ≤ 4 * (R * (1 + η) ^ j) ^ ((1 : ℝ) / 4) := by
    have h := Real.log_le_rpow_div hRj0.le (show (0 : ℝ) < 1 / 4 by norm_num)
    have hid : (R * (1 + η) ^ j) ^ ((1 : ℝ) / 4) / ((1 : ℝ) / 4)
        = 4 * (R * (1 + η) ^ j) ^ ((1 : ℝ) / 4) := by ring
    linarith [h, hid]
  have hexpq : Real.exp ((Real.log x) ^ a₁ / 4) ≤ (R * (1 + η) ^ j) ^ ((1 : ℝ) / 4) := by
    have h1 : (cardLength a₁ x) ^ ((1 : ℝ) / 4) ≤ (R * (1 + η) ^ j) ^ ((1 : ℝ) / 4) :=
      Real.rpow_le_rpow (cardLength_pos a₁ x).le hRjlo (by norm_num)
    have h2 : (cardLength a₁ x) ^ ((1 : ℝ) / 4) = Real.exp ((Real.log x) ^ a₁ / 4) := by
      rw [cardLength, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
      congr 1
      ring
    linarith [h1, h2]
  have hsq : Real.sqrt (R * (1 + η) ^ j)
      = (R * (1 + η) ^ j) ^ ((1 : ℝ) / 4) * (R * (1 + η) ^ j) ^ ((1 : ℝ) / 4) := by
    rw [← Real.rpow_add hRj0, Real.sqrt_eq_rpow]
    norm_num
  have hterm2 : 24 * Real.log (R * (1 + η) ^ j) / Real.sqrt (R * (1 + η) ^ j) ≤ η / 2 := by
    have hstep : 24 * Real.log (R * (1 + η) ^ j) / Real.sqrt (R * (1 + η) ^ j)
        ≤ 96 * Real.exp (-(1 / 4 * (Real.log x) ^ a₁)) := by
      rw [hsq]
      have hA : 24 * Real.log (R * (1 + η) ^ j) ≤ 96 * (R * (1 + η) ^ j) ^ ((1 : ℝ) / 4) := by
        linarith [hlogq]
      calc 24 * Real.log (R * (1 + η) ^ j)
              / ((R * (1 + η) ^ j) ^ ((1 : ℝ) / 4) * (R * (1 + η) ^ j) ^ ((1 : ℝ) / 4))
          ≤ 96 * (R * (1 + η) ^ j) ^ ((1 : ℝ) / 4)
              / ((R * (1 + η) ^ j) ^ ((1 : ℝ) / 4) * (R * (1 + η) ^ j) ^ ((1 : ℝ) / 4)) :=
            div_le_div_of_nonneg_right hA (by positivity)
        _ = 96 / (R * (1 + η) ^ j) ^ ((1 : ℝ) / 4) := by field_simp
        _ ≤ 96 / Real.exp ((Real.log x) ^ a₁ / 4) :=
            div_le_div_of_nonneg_left (by norm_num) (Real.exp_pos _) hexpq
        _ = 96 * Real.exp (-(1 / 4 * (Real.log x) ^ a₁)) := by
            rw [show -(1 / 4 * (Real.log x) ^ a₁) = -((Real.log x) ^ a₁ / 4) by ring,
              Real.exp_neg]
            field_simp
    have hmul := mul_le_mul_of_nonneg_left hdec2 (le_of_lt hη0)
    have hid : η * ((Real.log x) ^ c' * (96 * Real.exp (-(1 / 4 * (Real.log x) ^ a₁))))
        = 96 * Real.exp (-(1 / 4 * (Real.log x) ^ a₁)) := by
      rw [show η * ((Real.log x) ^ c' * (96 * Real.exp (-(1 / 4 * (Real.log x) ^ a₁))))
          = (η * (Real.log x) ^ c') * (96 * Real.exp (-(1 / 4 * (Real.log x) ^ a₁))) by ring,
        hηinv, one_mul]
    rw [hid] at hmul
    linarith [hstep, hmul]
  have hcountj := card_geomBlock_primesRange_ge (C := C) (c := c₀) (y₀ := y₀) hy₀
    (z₀ := highBase a₁ x) (L := highSteps a₁ b c' x) (j := j) (R := R) (η := η)
    rfl hR0 hη0 hη1 hjL (le_trans (le_max_left _ _) hRjy₀) (by linarith [hterm1, hterm2])
  -- turn the count into the base bound
  have hηid : η = (Real.log x) ^ (-c') := rfl
  have hpc : (Real.log x) ^ (b + c') = (Real.log x) ^ b * (Real.log x) ^ c' := by
    rw [← Real.rpow_add hlogx]
  have hηrec : (1 : ℝ) / η = (Real.log x) ^ c' := by
    rw [eq_comm, eq_div_iff (ne_of_gt hη0)]
    linarith [hηinv]
  have hkey : R * (1 + η) ^ j
      ≤ 8 * (Real.log x) ^ (b + c')
        * ((geomBlock (primesRange (highBase a₁ x)
            ⌊R * (1 + η) ^ (highSteps a₁ b c' x)⌋₊) R (1 + η) j).card : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hcountj
      (by positivity : (0 : ℝ) ≤ 4 * Real.log (R * (1 + η) ^ j) / η)
    have hid : 4 * Real.log (R * (1 + η) ^ j) / η
        * (R * (1 + η) ^ j * η / (4 * Real.log (R * (1 + η) ^ j))) = R * (1 + η) ^ j := by
      field_simp
    rw [hid] at hmul
    refine hmul.trans ?_
    have hcoef : 4 * Real.log (R * (1 + η) ^ j) / η ≤ 8 * (Real.log x) ^ (b + c') := by
      rw [div_le_iff₀ hη0]
      have hid2 : 8 * (Real.log x) ^ (b + c') * η = 8 * (Real.log x) ^ b := by
        rw [hpc]
        calc 8 * ((Real.log x) ^ b * (Real.log x) ^ c') * η
            = 8 * (Real.log x) ^ b * (η * (Real.log x) ^ c') := by ring
          _ = 8 * (Real.log x) ^ b := by rw [hηinv]; ring
      rw [hid2]
      linarith [hlogRjhi]
    exact mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg _)
  exact hkey

/-- **The head mean square is below the two-range budget.** -/
theorem twoRangeBudget_bound {A₀ δ₀ Ctot Kd a c A β a₁ b c' A₃ : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (ha : 0 < a) (hab : a < β) (hc : 0 < c) (_hA : 0 < A)
    (ha₁ : 0 < a₁) (ha₁b : a₁ < b) (hb1 : b < 1) (hc' : 0 < c') (hb0 : 0 < b)
    (hhigh : ∀ᶠ x : ℝ in atTop, ∀ T : Set ℝ, ∀ j ∈ Finset.range (highSteps a₁ b c' x),
        ∀ w ∈ annulusLarge T (twoRangeTop β x) (twoRangeDisc b A₃ x),
          ‖primeBlockPoly (geomBlock (primesRange (highBase a₁ x) (highTop a₁ b c' x))
              ((highBase a₁ x : ℕ) : ℝ) (1 + highEta c' x) j) w‖
            ≤ twoRangeHighRho A₀ δ₀ Ctot a₁ b c' β A₃ x
                * (((highBase a₁ x : ℕ) : ℝ) * (1 + highEta c' x) ^ j))
    (hdiscb : ∀ᶠ x : ℝ in atTop,
      (∫ w in Set.Icc (-(twoRangeDisc b A₃ x)) (twoRangeDisc b A₃ x),
          ‖logPoly (fun n => ((μ n : ℤ) : ℂ)) (Finset.Icc 1 (twoRangeLength β x)) w‖ ^ 2)
        ≤ discBudget β b A₃ Kd x)
    (hρ0 : ∀ᶠ x : ℝ in atTop, 0 ≤ twoRangeHighRho A₀ δ₀ Ctot a₁ b c' β A₃ x)
    (hA₃ : 0 < A₃) :
    ∀ᶠ x : ℝ in atTop,
      (∫ w in Set.Icc (-(twoRangeTop β x)) (twoRangeTop β x),
          ‖logPoly (fun n => ((μ n : ℤ) : ℂ)) (Finset.Icc 1 (twoRangeLength β x)) w‖ ^ 2)
        ≤ twoRangeBudget A₀ δ₀ Ctot Kd a c A β a₁ b c' A₃ x := by
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ),
    Filter.eventually_gt_atTop (Real.exp 1),
    two_le_highBase_and_le_expTop (a := a) (c := c) (β := β) ha hc,
    two_le_highBase_and_le_highTop (a := a₁) (b := b) (c' := c') ha₁,
    one_le_twoRangeTop hβ0 hβ1,
    twoRangeDisc_le_top (b := b) (A₃ := A₃) hb0 hA₃ hβ0 hβ1,
    one_le_expSteps (a := a) (c := c) (β := β) ha hab hc,
    one_le_highSteps (a := a₁) (b := b) (c' := c') ha₁ ha₁b hc',
    one_le_floor_div_highLadder (a := a₁) (b := b) (c' := c') (β := β) ha₁b.le hc' hb1 hb0,
    hhigh, hdiscb, hρ0,
    highBlock_base_le_card (a₁ := a₁) (b := b) (c' := c') ha₁ ha₁b hb1 hc']
    with x hx1 hxe hlow hlow' hW hwW hL hL' hNj hbnd hdsc hρ hcardb
  have hR1 : (1 : ℝ) ≤ ((highBase a x : ℕ) : ℝ) := by
    have : (2 : ℝ) ≤ ((highBase a x : ℕ) : ℝ) := by exact_mod_cast hlow.1
    linarith
  have hR'0 : (0 : ℝ) < ((highBase a₁ x : ℕ) : ℝ) := by
    have : (2 : ℝ) ≤ ((highBase a₁ x : ℕ) : ℝ) := by exact_mod_cast hlow'.1
    linarith
  exact integral_Icc_normSq_logPoly_moebius_le_twoRange
    (P := lowP a c β x) (P' := highP a₁ b c' x) (twoRangeLength β x)
    (R := ((highBase a x : ℕ) : ℝ)) (η := lowEta c x)
    (R' := ((highBase a₁ x : ℕ) : ℝ)) (η' := highEta c' x)
    (W := twoRangeTop β x) (w₀ := twoRangeDisc b A₃ x) (δ := twoRangeDelta x)
    (Bdisc := discBudget β b A₃ Kd x)
    hR1 (lowEta_pos hx1).le hR'0 (highEta_pos hx1).le hW hwW hL hL' (twoRangeDelta_pos hxe)
    (fun q hq => (mem_primesRange.1 hq).1)
    (primesRange_ladder_bounds_self rfl (lowEta_pos hx1).le (by linarith) rfl)
    (fun q hq => (mem_primesRange.1 hq).1)
    (highRange_bounds hx1)
    (lowV a c A β x) (highV A₀ δ₀ Ctot a₁ b c' β A₃ x)
    (fun j => lowV_nonneg x hx1 j) hNj
    (fun j hj w hw => by
      refine le_trans (hbnd _ j hj w hw) ?_
      rw [highV]
      have hc := hcardb j hj
      nlinarith [hc, hρ]) hdsc


/-- The Route-T relative size is nonnegative. -/
theorem twoRangeHighRho_nonneg {A₀ δ₀ Ctot a₁ b c' β A₃ : ℝ} (hCtot : 0 ≤ Ctot) (hb : 0 < b)
    (hA₃ : 0 < A₃) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∀ᶠ x : ℝ in atTop, 0 ≤ twoRangeHighRho A₀ δ₀ Ctot a₁ b c' β A₃ x := by
  filter_upwards [twoRangeHmaj_bounds (A := A₀) (b := b) (A₃ := A₃) (β := β) hb hA₃ hβ0 hβ1,
    Filter.eventually_gt_atTop (1 : ℝ)] with x hHm hx1
  have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
  have hLx0 : (0 : ℝ) ≤ twoRangeLx b x := by
    rw [twoRangeLx]
    have h1 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have h2 : (0 : ℝ) ≤ (Real.log x) ^ b := Real.rpow_nonneg hlogx.le b
    linarith
  have hrel0 : (0 : ℝ) ≤ relScaledMajorant Ctot (twoRangeWidth b A₃ x) (twoRangeLx b x)
      (twoRangeHmaj A₀ b A₃ β x) (twoRangeMu A₀ δ₀ β x) (twoRangeQ a₁ x)
      (twoRangeT₀ b A₃ x) (twoRangeXmin a₁ x) :=
    relScaledMajorant_nonneg hCtot (twoRangeWidth_pos hx1) hLx0 hHm.1
      (twoRangeT₀_pos hx1) (twoRangeXmin_pos a₁ x)
  have hR0 : (0 : ℝ) < ((highBase a₁ x : ℕ) : ℝ) := by
    have h1 := (highBase_bounds (a := a₁) hx1).1
    have h2 := cardLength_pos a₁ x
    linarith
  have hη : (0 : ℝ) < highEta c' x := highEta_pos hx1
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rw [twoRangeHighRho]
  have h1 : (0 : ℝ) ≤ (1 + highEta c' x)
      * relScaledMajorant Ctot (twoRangeWidth b A₃ x) (twoRangeLx b x)
          (twoRangeHmaj A₀ b A₃ β x) (twoRangeMu A₀ δ₀ β x) (twoRangeQ a₁ x)
          (twoRangeT₀ b A₃ x) (twoRangeXmin a₁ x) := mul_nonneg (by linarith) hrel0
  have h2 : (0 : ℝ) ≤ 7 * Real.exp 9 / ((highBase a₁ x : ℕ) : ℝ) := by positivity
  have h3 : (0 : ℝ) ≤ 4 / Real.log 2 := by positivity
  exact mul_nonneg h3 (by linarith)

/-- **A rough group vanishes at the schedule.**  Range-agnostic: the designated range enters only
through a lower bound `cA·log log x` for its harmonic mass and an upper bound `2·exp((log x)^γ)`
for its cardinality. -/
theorem tendsto_roughPiece {β γ cA : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hcA : 0 < cA) {P : ℝ → Finset ℕ}
    (hprime : ∀ᶠ x : ℝ in atTop, ∀ p ∈ P x, p.Prime)
    (hA : ∀ᶠ x : ℝ in atTop,
      cA * Real.log (Real.log x) ≤ ∑ p ∈ P x, (1 : ℝ) / (p : ℝ))
    (hPc : ∀ᶠ x : ℝ in atTop, ((P x).card : ℝ) ≤ 2 * cardLength γ x) :
    Tendsto (fun x : ℝ =>
      (1 + 1 / twoRangeDelta x)
        * (∫ w in Set.Icc (-(twoRangeTop β x)) (twoRangeTop β x),
            ‖logPoly (fun n => ((μ n : ℤ) : ℂ))
              (supportMeanSquareRoughSet (P x) (twoRangeLength β x)) w‖ ^ 2)
        / ((twoRangeLength β x : ℕ) : ℝ) ^ 2) atTop (𝓝 0) := by
  -- the part that does not see the cardinality
  have hzero := tendsto_roughGroup_div_sq (β := β) (cA := cA) hβ0 hβ1 hcA
    (Af := fun x => ∑ p ∈ P x, (1 : ℝ) / (p : ℝ)) (Pf := fun _ => (0 : ℝ))
    hA (Filter.Eventually.of_forall fun x => ⟨le_refl 0, (cardLength_pos β x).le⟩)
  have hzero' : Tendsto (fun x : ℝ =>
      (1 + 1 / twoRangeDelta x)
        * (10 * twoRangeTop β x
              / ((∑ p ∈ P x, (1 : ℝ) / (p : ℝ)) * ((twoRangeLength β x : ℕ) : ℝ))
            + 7 / (∑ p ∈ P x, (1 : ℝ) / (p : ℝ)))) atTop (𝓝 0) := by
    refine hzero.congr fun x => ?_
    simp
  -- the part that does
  have hextra : Tendsto (fun x : ℝ =>
      (1 + 1 / twoRangeDelta x)
        * (20 * twoRangeTop β x * ((P x).card : ℝ)
              / ((∑ p ∈ P x, (1 : ℝ) / (p : ℝ)) * ((twoRangeLength β x : ℕ) : ℝ) ^ 2)
            + 14 * ((P x).card : ℝ)
              / ((∑ p ∈ P x, (1 : ℝ) / (p : ℝ)) * ((twoRangeLength β x : ℕ) : ℝ))))
      atTop (𝓝 0) := by
    have hmaj0 := tendsto_logMonomial_mul_cardLength_div_sqrt (β := γ) hγ0 hγ1 (0 : ℝ) 1
    have hmaj : Tendsto (fun x : ℝ => 136 / cA
        * ((Real.log x) ^ (0 : ℝ) * (Real.log (Real.log x)) ^ 1
          * (cardLength γ x / Real.sqrt x))) atTop (𝓝 0) := by
      have := hmaj0.const_mul (136 / cA)
      rw [show (136 / cA * 0) = 0 by ring] at this
      exact this
    refine squeeze_zero' ?_ ?_ hmaj
    · filter_upwards [Filter.eventually_gt_atTop (Real.exp 1), Filter.eventually_gt_atTop (1 : ℝ),
        one_le_twoRangeTop hβ0 hβ1, hA,
        Real.tendsto_log_atTop.eventually_ge_atTop (Real.exp 1)] with x hxe hx1 hW hAx hlbig
      have hu1 : (1 : ℝ) ≤ Real.log (Real.log x) := by
        have := Real.log_le_log (Real.exp_pos 1) hlbig
        rwa [Real.log_exp] at this
      have hA0 : (0 : ℝ) < ∑ p ∈ P x, (1 : ℝ) / (p : ℝ) := lt_of_lt_of_le (by positivity) hAx
      have hδ : (0 : ℝ) < twoRangeDelta x := twoRangeDelta_pos hxe
      have h1δ : (0 : ℝ) ≤ 1 + 1 / twoRangeDelta x := by positivity
      have hP0 : (0 : ℝ) ≤ ((P x).card : ℝ) := Nat.cast_nonneg _
      have hW0 : (0 : ℝ) ≤ twoRangeTop β x := by linarith
      have hM0 : (0 : ℝ) ≤ ((twoRangeLength β x : ℕ) : ℝ) := Nat.cast_nonneg _
      have h1 : (0 : ℝ) ≤ 20 * twoRangeTop β x * ((P x).card : ℝ)
          / ((∑ p ∈ P x, (1 : ℝ) / (p : ℝ)) * ((twoRangeLength β x : ℕ) : ℝ) ^ 2) := by
        positivity
      have h2 : (0 : ℝ) ≤ 14 * ((P x).card : ℝ)
          / ((∑ p ∈ P x, (1 : ℝ) / (p : ℝ)) * ((twoRangeLength β x : ℕ) : ℝ)) := by positivity
      exact mul_nonneg h1δ (by linarith)
    · filter_upwards [Filter.eventually_gt_atTop (Real.exp 1), Filter.eventually_gt_atTop (1 : ℝ),
        one_le_twoRangeTop hβ0 hβ1, hA, hPc, one_le_twoRangeLength hβ0,
        sqrt_le_twoRangeLength hβ0, twoRangeTop_le_length hβ0 hβ1,
        Real.tendsto_log_atTop.eventually_ge_atTop (Real.exp 1),
        (tendsto_cardLength hβ0).eventually_ge_atTop (1 : ℝ),
        Filter.eventually_ge_atTop (16 : ℝ)]
        with x hxe hx1 hW hAx hPcx hM1 hMsq hWM hlbig hh1 hx16
      have hu1 : (1 : ℝ) ≤ Real.log (Real.log x) := by
        have := Real.log_le_log (Real.exp_pos 1) hlbig
        rwa [Real.log_exp] at this
      have hu0 : (0 : ℝ) < Real.log (Real.log x) := by linarith
      have hA0 : (0 : ℝ) < ∑ p ∈ P x, (1 : ℝ) / (p : ℝ) := lt_of_lt_of_le (by positivity) hAx
      have hδ : (0 : ℝ) < twoRangeDelta x := twoRangeDelta_pos hxe
      have hM0 : (0 : ℝ) < ((twoRangeLength β x : ℕ) : ℝ) := by linarith
      have hs0 : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
      have hhγ0 : (0 : ℝ) < cardLength γ x := cardLength_pos γ x
      have hP0 : (0 : ℝ) ≤ ((P x).card : ℝ) := Nat.cast_nonneg _
      have hW0 : (0 : ℝ) ≤ twoRangeTop β x := by linarith
      have hd1 : 1 / twoRangeDelta x = (Real.log (Real.log x)) ^ ((1 : ℝ) / 2) := by
        rw [twoRangeDelta, show (-(1 : ℝ) / 2) = -((1 : ℝ) / 2) by ring, Real.rpow_neg hu0.le,
          one_div, inv_inv]
      have hD : 1 / twoRangeDelta x ≤ Real.log (Real.log x) := by
        rw [hd1]
        calc (Real.log (Real.log x)) ^ ((1 : ℝ) / 2)
            ≤ (Real.log (Real.log x)) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hu1 (by norm_num)
          _ = Real.log (Real.log x) := Real.rpow_one _
      have hAcA : cA * Real.log (Real.log x) ≤ ∑ p ∈ P x, (1 : ℝ) / (p : ℝ) := hAx
      have hMM : Real.sqrt x * ((twoRangeLength β x : ℕ) : ℝ)
          ≤ ((twoRangeLength β x : ℕ) : ℝ) * ((twoRangeLength β x : ℕ) : ℝ) := by
        nlinarith [hMsq, hM0]
      have hden : cA * Real.log (Real.log x) * (Real.sqrt x * ((twoRangeLength β x : ℕ) : ℝ))
          ≤ (∑ p ∈ P x, (1 : ℝ) / (p : ℝ))
            * (((twoRangeLength β x : ℕ) : ℝ) * ((twoRangeLength β x : ℕ) : ℝ)) :=
        mul_le_mul hAcA hMM (by positivity) (by positivity)
      have hk1 : 20 * twoRangeTop β x * ((P x).card : ℝ)
            / ((∑ p ∈ P x, (1 : ℝ) / (p : ℝ)) * ((twoRangeLength β x : ℕ) : ℝ) ^ 2)
          ≤ 40 * cardLength γ x / (cA * Real.log (Real.log x) * Real.sqrt x) := by
        have hnum : 20 * twoRangeTop β x * ((P x).card : ℝ)
            ≤ 40 * cardLength γ x * ((twoRangeLength β x : ℕ) : ℝ) := by
          nlinarith [hWM, hPcx, hP0, hW0, hM0, hhγ0]
        have hstep : 20 * twoRangeTop β x * ((P x).card : ℝ)
              / ((∑ p ∈ P x, (1 : ℝ) / (p : ℝ)) * ((twoRangeLength β x : ℕ) : ℝ) ^ 2)
            ≤ 40 * cardLength γ x * ((twoRangeLength β x : ℕ) : ℝ)
              / (cA * Real.log (Real.log x)
                * (Real.sqrt x * ((twoRangeLength β x : ℕ) : ℝ))) := by
          refine div_le_div₀ (by positivity) hnum (by positivity) ?_
          nlinarith [hden]
        refine hstep.trans (le_of_eq ?_)
        field_simp
      have hk2 : 14 * ((P x).card : ℝ)
            / ((∑ p ∈ P x, (1 : ℝ) / (p : ℝ)) * ((twoRangeLength β x : ℕ) : ℝ))
          ≤ 28 * cardLength γ x / (cA * Real.log (Real.log x) * Real.sqrt x) := by
        have hnum : 14 * ((P x).card : ℝ) ≤ 28 * cardLength γ x := by
          nlinarith [hPcx, hhγ0]
        have hden2 : cA * Real.log (Real.log x) * Real.sqrt x
            ≤ (∑ p ∈ P x, (1 : ℝ) / (p : ℝ)) * ((twoRangeLength β x : ℕ) : ℝ) :=
          mul_le_mul hAcA hMsq (by positivity) (by positivity)
        exact div_le_div₀ (by positivity) hnum (by positivity) hden2
      have hsum2 : 20 * twoRangeTop β x * ((P x).card : ℝ)
              / ((∑ p ∈ P x, (1 : ℝ) / (p : ℝ)) * ((twoRangeLength β x : ℕ) : ℝ) ^ 2)
            + 14 * ((P x).card : ℝ)
              / ((∑ p ∈ P x, (1 : ℝ) / (p : ℝ)) * ((twoRangeLength β x : ℕ) : ℝ))
          ≤ 68 * cardLength γ x / (cA * Real.log (Real.log x) * Real.sqrt x) := by
        have hid : 40 * cardLength γ x / (cA * Real.log (Real.log x) * Real.sqrt x)
            + 28 * cardLength γ x / (cA * Real.log (Real.log x) * Real.sqrt x)
            = 68 * cardLength γ x / (cA * Real.log (Real.log x) * Real.sqrt x) := by ring
        linarith [hk1, hk2, hid]
      have hsum0 : (0 : ℝ) ≤ 68 * cardLength γ x
          / (cA * Real.log (Real.log x) * Real.sqrt x) := by positivity
      have hDle : 1 + 1 / twoRangeDelta x ≤ 2 * Real.log (Real.log x) := by linarith [hD, hu1]
      have hfin : (1 + 1 / twoRangeDelta x)
            * (68 * cardLength γ x / (cA * Real.log (Real.log x) * Real.sqrt x))
          ≤ 136 / cA * ((Real.log x) ^ (0 : ℝ) * (Real.log (Real.log x)) ^ 1
            * (cardLength γ x / Real.sqrt x)) := by
        have hstep := mul_le_mul_of_nonneg_right hDle hsum0
        refine hstep.trans ?_
        rw [Real.rpow_zero, pow_one]
        have hid : 2 * Real.log (Real.log x)
              * (68 * cardLength γ x / (cA * Real.log (Real.log x) * Real.sqrt x))
            = 136 * cardLength γ x / (cA * Real.sqrt x) := by
          field_simp
          try ring
        have hid2 : 136 / cA * (1 * Real.log (Real.log x) * (cardLength γ x / Real.sqrt x))
            = Real.log (Real.log x) * (136 * cardLength γ x / (cA * Real.sqrt x)) := by
          field_simp
          try ring
        rw [hid, hid2]
        nlinarith [hu1, (by positivity : (0 : ℝ) ≤ 136 * cardLength γ x / (cA * Real.sqrt x))]
      have h1δ : (0 : ℝ) ≤ 1 + 1 / twoRangeDelta x := by positivity
      exact le_trans (mul_le_mul_of_nonneg_left hsum2 h1δ) hfin
  have hsum := hzero'.add hextra
  rw [show ((0 : ℝ) + 0) = 0 by ring] at hsum
  refine squeeze_zero' ?_ ?_ hsum
  · filter_upwards [Filter.eventually_gt_atTop (Real.exp 1)] with x hxe
    have hδ : (0 : ℝ) < twoRangeDelta x := twoRangeDelta_pos hxe
    have hI : (0 : ℝ) ≤ ∫ w in Set.Icc (-(twoRangeTop β x)) (twoRangeTop β x),
        ‖logPoly (fun n => ((μ n : ℤ) : ℂ))
          (supportMeanSquareRoughSet (P x) (twoRangeLength β x)) w‖ ^ 2 :=
      MeasureTheory.setIntegral_nonneg measurableSet_Icc fun w _ => by positivity
    have h1δ : (0 : ℝ) ≤ 1 + 1 / twoRangeDelta x := by positivity
    exact div_nonneg (mul_nonneg h1δ hI) (by positivity)
  · filter_upwards [Filter.eventually_gt_atTop (Real.exp 1), Filter.eventually_gt_atTop (1 : ℝ),
      one_le_twoRangeTop hβ0 hβ1, hprime, hA, one_le_twoRangeLength hβ0,
      Real.tendsto_log_atTop.eventually_ge_atTop (Real.exp 1)] with x hxe hx1 hW hpr hAx hM1 hlbig
    have hδ : (0 : ℝ) < twoRangeDelta x := twoRangeDelta_pos hxe
    have hM0 : (0 : ℝ) < ((twoRangeLength β x : ℕ) : ℝ) := by linarith
    have hu1 : (1 : ℝ) ≤ Real.log (Real.log x) := by
      have := Real.log_le_log (Real.exp_pos 1) hlbig
      rwa [Real.log_exp] at this
    have hA0 : (0 : ℝ) < ∑ p ∈ P x, (1 : ℝ) / (p : ℝ) := lt_of_lt_of_le (by positivity) hAx
    have hint := integral_Icc_normSq_roughPoly_le_harmonic (P := P x) hpr
      (twoRangeLength β x) (W := twoRangeTop β x) hW hA0
    have hrough := roughGroup_le (W := twoRangeTop β x) (M := ((twoRangeLength β x : ℕ) : ℝ))
      (A := ∑ p ∈ P x, (1 : ℝ) / (p : ℝ)) (cP := ((P x).card : ℝ))
      (by linarith) hM0 hA0 (Nat.cast_nonneg _)
    have hid : ((twoRangeLength β x : ℕ) : ℝ) / (∑ p ∈ P x, (1 : ℝ) / (p : ℝ))
          + 2 * ((P x).card : ℝ) / (∑ p ∈ P x, (1 : ℝ) / (p : ℝ))
        = (((twoRangeLength β x : ℕ) : ℝ) + 2 * ((P x).card : ℝ))
          / (∑ p ∈ P x, (1 : ℝ) / (p : ℝ)) := by
      field_simp
    rw [hid] at hint
    have hstep : (∫ w in Set.Icc (-(twoRangeTop β x)) (twoRangeTop β x),
          ‖logPoly (fun n => ((μ n : ℤ) : ℂ))
            (supportMeanSquareRoughSet (P x) (twoRangeLength β x)) w‖ ^ 2)
          / ((twoRangeLength β x : ℕ) : ℝ) ^ 2
        ≤ 10 * twoRangeTop β x
              / ((∑ p ∈ P x, (1 : ℝ) / (p : ℝ)) * ((twoRangeLength β x : ℕ) : ℝ))
            + 20 * twoRangeTop β x * ((P x).card : ℝ)
              / ((∑ p ∈ P x, (1 : ℝ) / (p : ℝ)) * ((twoRangeLength β x : ℕ) : ℝ) ^ 2)
            + 7 / (∑ p ∈ P x, (1 : ℝ) / (p : ℝ))
            + 14 * ((P x).card : ℝ)
              / ((∑ p ∈ P x, (1 : ℝ) / (p : ℝ)) * ((twoRangeLength β x : ℕ) : ℝ)) :=
      le_trans (div_le_div_of_nonneg_right hint (by positivity)) hrough
    have h1δ : (0 : ℝ) ≤ 1 + 1 / twoRangeDelta x := by positivity
    have hid2 : (1 + 1 / twoRangeDelta x)
          * (∫ w in Set.Icc (-(twoRangeTop β x)) (twoRangeTop β x),
              ‖logPoly (fun n => ((μ n : ℤ) : ℂ))
                (supportMeanSquareRoughSet (P x) (twoRangeLength β x)) w‖ ^ 2)
          / ((twoRangeLength β x : ℕ) : ℝ) ^ 2
        = (1 + 1 / twoRangeDelta x)
          * ((∫ w in Set.Icc (-(twoRangeTop β x)) (twoRangeTop β x),
              ‖logPoly (fun n => ((μ n : ℤ) : ℂ))
                (supportMeanSquareRoughSet (P x) (twoRangeLength β x)) w‖ ^ 2)
            / ((twoRangeLength β x : ℕ) : ℝ) ^ 2) := by ring
    rw [hid2]
    have := mul_le_mul_of_nonneg_left hstep h1δ
    linarith [this]

/-- **The large half's Halász–Montgomery ladder group vanishes at the schedule.** -/
theorem tendsto_largeLadderPiece {A₀ δ₀ Ctot a c A β a₁ b c' A₃ E : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hb0 : 0 < b) (hb1 : b < 1) (ha₁ : 0 < a₁) (ha₁b : a₁ < b)
    (hc' : 0 < c') (hE : b + c' + 2 ≤ 2 * E) (hE0 : 0 ≤ E)
    (hρ0 : ∀ᶠ x : ℝ in atTop, 0 ≤ twoRangeHighRho A₀ δ₀ Ctot a₁ b c' β A₃ x)
    (hρ : Tendsto (fun x : ℝ => (Real.log x) ^ E
        * (8 * twoRangeHighRho A₀ δ₀ Ctot a₁ b c' β A₃ x * (Real.log x) ^ (b + c')))
      atTop (𝓝 0))
    (hUf : Tendsto (fun x : ℝ => (Real.log x) ^ (b + c')
        * (plainKernelFarConst
              ⌊((twoRangeLength β x : ℕ) : ℝ) / ((highBase a₁ x : ℕ) : ℝ)⌋₊
              (2 * Real.pi * twoRangeTop β x)
            * (2 * Real.pi * volume.real (lowExceptional a c A β b A₃ x)))
        * (cardLength b x * Real.log (Real.log x) / ((twoRangeLength β x : ℕ) : ℝ)
          + cardLength b x ^ 2 / ((twoRangeLength β x : ℕ) : ℝ) ^ 2)) atTop (𝓝 0)) :
    Tendsto (fun x : ℝ =>
      (1 + twoRangeDelta x)
        * (2 * ((highSteps a₁ b c' x : ℕ) : ℝ) * ∑ j ∈ Finset.range (highSteps a₁ b c' x),
            highV A₀ δ₀ Ctot a₁ b c' β A₃ x j ^ 2
              * ladderHMBoundRecip (twoRangeLength β x) ((highBase a₁ x : ℕ) : ℝ)
                  (highEta c' x) (twoRangeTop β x)
                  (volume.real (lowExceptional a c A β b A₃ x)) j)
        / ((twoRangeLength β x : ℕ) : ℝ) ^ 2) atTop (𝓝 0) := by
  have hbase := tendsto_largeLadderGroup_div_sq (β := β) (b := b) (c' := c') (E := E)
    hβ0 hβ1 hb0 hb1 hE hE0
    (Lf := fun x => ((highSteps a₁ b c' x : ℕ) : ℝ))
    (ρf := fun x => 8 * twoRangeHighRho A₀ δ₀ Ctot a₁ b c' β A₃ x * (Real.log x) ^ (b + c'))
    (Bf := fun x => ((highBase a₁ x : ℕ) : ℝ) * (1 + highEta c' x) ^ (highSteps a₁ b c' x)
        * highEta c' x + 1)
    (Sf := fun x => (1 + highEta c' x) * ((twoRangeLength β x : ℕ) : ℝ)
        * rangeHarmonic (highP a₁ b c' x))
    (Pf := fun x => ((highP a₁ b c' x).card : ℝ))
    (Uf := fun x => plainKernelFarConst
        ⌊((twoRangeLength β x : ℕ) : ℝ) / ((highBase a₁ x : ℕ) : ℝ)⌋₊
        (2 * Real.pi * twoRangeTop β x)
      * (2 * Real.pi * volume.real (lowExceptional a c A β b A₃ x)))
    ?_ ?_ hρ ?_ ?_ ?_ ?_ hUf
  · have hg := hbase.const_mul (2 : ℝ)
    rw [show ((2 : ℝ) * 0) = 0 by ring] at hg
    refine squeeze_zero' ?_ ?_ hg
    · filter_upwards [Filter.eventually_gt_atTop (Real.exp 1), Filter.eventually_gt_atTop (1 : ℝ),
        one_le_twoRangeTop hβ0 hβ1] with x hxe hx1 hW
      have hδ : (0 : ℝ) < twoRangeDelta x := twoRangeDelta_pos hxe
      have hvol : (0 : ℝ) ≤ volume.real (lowExceptional a c A β b A₃ x) :=
        ENNReal.toReal_nonneg
      have hsum : (0 : ℝ) ≤ ∑ j ∈ Finset.range (highSteps a₁ b c' x),
          highV A₀ δ₀ Ctot a₁ b c' β A₃ x j ^ 2
            * ladderHMBoundRecip (twoRangeLength β x) ((highBase a₁ x : ℕ) : ℝ)
                (highEta c' x) (twoRangeTop β x)
                (volume.real (lowExceptional a c A β b A₃ x)) j := by
        refine Finset.sum_nonneg fun j _ => ?_
        refine mul_nonneg (sq_nonneg _) ?_
        rw [ladderHMBoundRecip, hmMassRecip]
        have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
        have hfc : (0 : ℝ) ≤ plainKernelFarConst
            ⌊((twoRangeLength β x : ℕ) : ℝ)
              / (((highBase a₁ x : ℕ) : ℝ) * (1 + highEta c' x) ^ j)⌋₊
            (2 * Real.pi * twoRangeTop β x) := by
          refine plainKernelFarConst_nonneg _ ?_
          nlinarith [hW, Real.pi_gt_three]
        have hlog : (0 : ℝ) ≤ Real.log (2 + 2 * (2 * Real.pi * twoRangeTop β x)) := by
          refine Real.log_nonneg ?_
          nlinarith [hW, hπ]
        positivity
      refine div_nonneg (mul_nonneg (by linarith) ?_) (by positivity)
      have hL0 : (0 : ℝ) ≤ ((highSteps a₁ b c' x : ℕ) : ℝ) := Nat.cast_nonneg _
      positivity
    · filter_upwards [Filter.eventually_gt_atTop (Real.exp 1), Filter.eventually_gt_atTop (1 : ℝ),
        one_le_twoRangeTop hβ0 hβ1,
        two_le_highBase_and_le_highTop (a := a₁) (b := b) (c' := c') ha₁,
        one_le_highSteps (a := a₁) (b := b) (c' := c') ha₁ ha₁b hc',
        one_le_twoRangeLength hβ0,
        Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1) tendsto_twoRangeDelta]
        with x hxe hx1 hW hlow hL hM1 hδ1
      have hR0 : (0 : ℝ) < ((highBase a₁ x : ℕ) : ℝ) := by
        have : (2 : ℝ) ≤ ((highBase a₁ x : ℕ) : ℝ) := by exact_mod_cast hlow.1
        linarith
      have hvol : (0 : ℝ) ≤ volume.real (lowExceptional a c A β b A₃ x) :=
        ENNReal.toReal_nonneg
      have hgroup := largeLadderGroup_le (P := highP a₁ b c' x) (twoRangeLength β x)
        (R := ((highBase a₁ x : ℕ) : ℝ)) (η := highEta c' x) (W := twoRangeTop β x)
        (ρ := 8 * twoRangeHighRho A₀ δ₀ Ctot a₁ b c' β A₃ x * (Real.log x) ^ (b + c'))
        (volE := volume.real (lowExceptional a c A β b A₃ x))
        hR0 (highEta_pos hx1).le hW hvol hL (highRange_bounds hx1)
      have hcong : ∀ j : ℕ, highV A₀ δ₀ Ctot a₁ b c' β A₃ x j ^ 2
          = ((8 * twoRangeHighRho A₀ δ₀ Ctot a₁ b c' β A₃ x * (Real.log x) ^ (b + c'))
            * ((geomBlock (highP a₁ b c' x) ((highBase a₁ x : ℕ) : ℝ)
                (1 + highEta c' x) j).card : ℝ)) ^ 2 := by
        intro j
        rw [highV]
      rw [Finset.sum_congr rfl (fun j _ => by rw [hcong j])]
      have hnn : (0 : ℝ) ≤ 2 * ((highSteps a₁ b c' x : ℕ) : ℝ)
          * ∑ j ∈ Finset.range (highSteps a₁ b c' x),
            ((8 * twoRangeHighRho A₀ δ₀ Ctot a₁ b c' β A₃ x * (Real.log x) ^ (b + c'))
              * ((geomBlock (highP a₁ b c' x) ((highBase a₁ x : ℕ) : ℝ)
                  (1 + highEta c' x) j).card : ℝ)) ^ 2
              * ladderHMBoundRecip (twoRangeLength β x) ((highBase a₁ x : ℕ) : ℝ)
                  (highEta c' x) (twoRangeTop β x)
                  (volume.real (lowExceptional a c A β b A₃ x)) j := by
        refine mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ => ?_)
        refine mul_nonneg (sq_nonneg _) ?_
        rw [ladderHMBoundRecip, hmMassRecip]
        have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
        have hfc : (0 : ℝ) ≤ plainKernelFarConst
            ⌊((twoRangeLength β x : ℕ) : ℝ)
              / (((highBase a₁ x : ℕ) : ℝ) * (1 + highEta c' x) ^ j)⌋₊
            (2 * Real.pi * twoRangeTop β x) := by
          refine plainKernelFarConst_nonneg _ ?_
          nlinarith [hW, Real.pi_gt_three]
        have hlog : (0 : ℝ) ≤ Real.log (2 + 2 * (2 * Real.pi * twoRangeTop β x)) := by
          refine Real.log_nonneg ?_
          nlinarith [hW, hπ]
        positivity
      have hδ : (0 : ℝ) < twoRangeDelta x := twoRangeDelta_pos hxe
      exact mul_div_le_two (by linarith) (by linarith) hnn hgroup (by positivity)
  · filter_upwards [highSteps_le (a := a₁) (b := b) (c' := c') ha₁ ha₁b.le hc'] with x hle
    exact ⟨Nat.cast_nonneg _, hle⟩
  · filter_upwards [hρ0, Filter.eventually_gt_atTop (1 : ℝ)] with x hr hx1
    have : (0 : ℝ) ≤ (Real.log x) ^ (b + c') := Real.rpow_nonneg (Real.log_pos hx1).le _
    positivity
  · filter_upwards [Filter.eventually_gt_atTop (1 : ℝ),
      highLadder_le (a := a₁) (b := b) (c' := c') ha₁b.le hc',
      Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1) (tendsto_highEta hc'),
      (tendsto_cardLength (β := b) hb0).eventually_ge_atTop (1 : ℝ)] with x hx1 htop hη1 hcl1
    have hη0 : (0 : ℝ) < highEta c' x := highEta_pos hx1
    refine ⟨by positivity, ?_⟩
    have hmul : ((highBase a₁ x : ℕ) : ℝ) * (1 + highEta c' x) ^ (highSteps a₁ b c' x)
          * highEta c' x
        ≤ 2 * cardLength b x * highEta c' x := mul_le_mul_of_nonneg_right htop hη0.le
    nlinarith [hmul, hη1, hcl1, cardLength_pos b x]
  · filter_upwards [Filter.eventually_gt_atTop (1 : ℝ),
      highRange_harmonic_le (a := a₁) (b := b) (c' := c') ha₁ ha₁b hb1 hc',
      Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1) (tendsto_highEta hc'),
      Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ),
      one_le_twoRangeLength hβ0] with x hx1 hH hη1 hlog1 hM1
    have hη0 : (0 : ℝ) < highEta c' x := highEta_pos hx1
    have hu0 : (0 : ℝ) ≤ Real.log (Real.log x) := Real.log_nonneg hlog1
    have hH0 : (0 : ℝ) ≤ rangeHarmonic (highP a₁ b c' x) :=
      Finset.sum_nonneg fun p _ => by positivity
    refine ⟨by positivity, ?_⟩
    have hMH : (0 : ℝ) ≤ ((twoRangeLength β x : ℕ) : ℝ) * rangeHarmonic (highP a₁ b c' x) := by
      have hM0 : (0 : ℝ) ≤ ((twoRangeLength β x : ℕ) : ℝ) := Nat.cast_nonneg _
      exact mul_nonneg hM0 hH0
    have hstep1 : (1 + highEta c' x) * ((twoRangeLength β x : ℕ) : ℝ)
          * rangeHarmonic (highP a₁ b c' x)
        ≤ 2 * (((twoRangeLength β x : ℕ) : ℝ) * rangeHarmonic (highP a₁ b c' x)) := by
      nlinarith [hη1, hMH]
    have hstep2 : 2 * (((twoRangeLength β x : ℕ) : ℝ) * rangeHarmonic (highP a₁ b c' x))
        ≤ 2 * ((twoRangeLength β x : ℕ) : ℝ) * Real.log (Real.log x) := by
      have hM0 : (0 : ℝ) ≤ ((twoRangeLength β x : ℕ) : ℝ) := Nat.cast_nonneg _
      have hHr : rangeHarmonic (highP a₁ b c' x) ≤ Real.log (Real.log x) := hH
      have := mul_le_mul_of_nonneg_left hHr hM0
      linarith
    linarith
  · filter_upwards [Filter.eventually_gt_atTop (1 : ℝ),
      highLadder_le (a := a₁) (b := b) (c' := c') ha₁b.le hc',
      (tendsto_cardLength (β := b) hb0).eventually_ge_atTop (1 : ℝ)] with x hx1 htop hcl1
    refine ⟨Nat.cast_nonneg _, ?_⟩
    have h1 : ((highP a₁ b c' x).card : ℝ) ≤ ((highTop a₁ b c' x : ℕ) : ℝ) :=
      card_primesRange_le_top _ _
    have h2 : ((highTop a₁ b c' x : ℕ) : ℝ) ≤ 2 * cardLength b x := by
      rw [highTop]
      refine le_trans (Nat.floor_le ?_) htop
      have hη0 : (0 : ℝ) < highEta c' x := highEta_pos hx1
      positivity
    linarith
  · filter_upwards [Filter.eventually_gt_atTop (1 : ℝ), one_le_twoRangeTop hβ0 hβ1]
      with x hx1 hW
    have hvol : (0 : ℝ) ≤ volume.real (lowExceptional a c A β b A₃ x) := ENNReal.toReal_nonneg
    have hfc : (0 : ℝ) ≤ plainKernelFarConst
        ⌊((twoRangeLength β x : ℕ) : ℝ) / ((highBase a₁ x : ℕ) : ℝ)⌋₊
        (2 * Real.pi * twoRangeTop β x) := by
      refine plainKernelFarConst_nonneg _ ?_
      nlinarith [hW, Real.pi_gt_three]
    have := Real.pi_pos
    positivity

/-- The exponential bottom dominates every power of the logarithm. -/
theorem rpow_log_le_highBase {a : ℝ} (ha : 0 < a) (K : ℝ) :
    ∀ᶠ x : ℝ in atTop, (Real.log x) ^ K ≤ ((highBase a x : ℕ) : ℝ) := by
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ),
    Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1)
      (tendsto_rpow_log_div_cardLength (β := a) ha K)] with x hx1 hsm
  have hc0 : (0 : ℝ) < cardLength a x := cardLength_pos a x
  rw [div_le_one hc0] at hsm
  have := (highBase_bounds (a := a) hx1).1
  linarith

/-- The logarithm of the exponential bottom is at least one. -/
theorem one_le_log_highBase {a : ℝ} (ha : 0 < a) :
    ∀ᶠ x : ℝ in atTop, 1 ≤ Real.log ((highBase a x : ℕ) : ℝ) := by
  have hpowa : Tendsto (fun x : ℝ => (Real.log x) ^ a) atTop atTop :=
    (tendsto_rpow_atTop ha).comp Real.tendsto_log_atTop
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ), hpowa.eventually_ge_atTop (1 : ℝ)]
    with x hx1 hbig
  have h1 := (highBase_bounds (a := a) hx1).1
  have := Real.log_le_log (cardLength_pos a x) h1
  rw [log_cardLength] at this
  linarith

/-- The exponential bottom exceeds one. -/
theorem one_lt_highBase {a : ℝ} (ha : 0 < a) :
    ∀ᶠ x : ℝ in atTop, 1 < ((highBase a x : ℕ) : ℝ) := by
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ), one_le_log_highBase ha] with x hx1 hlog
  by_contra hcon
  have hle : ((highBase a x : ℕ) : ℝ) ≤ 1 := le_of_not_gt hcon
  have h0 : (0 : ℝ) < ((highBase a x : ℕ) : ℝ) := by
    have h1 := (highBase_bounds (a := a) hx1).1
    have h2 := cardLength_pos a x
    linarith
  have := Real.log_le_log h0 hle
  rw [Real.log_one] at this
  linarith

/-- **The two-range budget vanishes relative to `M²`.** -/
theorem tendsto_twoRangeBudget_div_sq {A₀ δ₀ Ctot Kd a c A β a₁ b c' A₃ E : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (ha : 0 < a) (hab : a < β) (hc : 1 + β < c)
    (h2A : β + c < 2 * A)
    (ha₁ : 0 < a₁) (ha₁b : a₁ < b) (hb0 : 0 < b) (hb1 : b < 1) (hc' : 1 + b < c')
    (hE : b + c' + 2 ≤ 2 * E) (hE0 : 0 ≤ E)
    (hρ0 : ∀ᶠ x : ℝ in atTop, 0 ≤ twoRangeHighRho A₀ δ₀ Ctot a₁ b c' β A₃ x)
    (hρ : Tendsto (fun x : ℝ => (Real.log x) ^ E
        * (8 * twoRangeHighRho A₀ δ₀ Ctot a₁ b c' β A₃ x * (Real.log x) ^ (b + c')))
      atTop (𝓝 0))
    (hUf : Tendsto (fun x : ℝ => (Real.log x) ^ (b + c')
        * (plainKernelFarConst
              ⌊((twoRangeLength β x : ℕ) : ℝ) / ((highBase a₁ x : ℕ) : ℝ)⌋₊
              (2 * Real.pi * twoRangeTop β x)
            * (2 * Real.pi * volume.real (lowExceptional a c A β b A₃ x)))
        * (cardLength b x * Real.log (Real.log x) / ((twoRangeLength β x : ℕ) : ℝ)
          + cardLength b x ^ 2 / ((twoRangeLength β x : ℕ) : ℝ) ^ 2)) atTop (𝓝 0)) :
    Tendsto (fun x : ℝ =>
      twoRangeBudget A₀ δ₀ Ctot Kd a c A β a₁ b c' A₃ x
        / ((twoRangeLength β x : ℕ) : ℝ) ^ 2) atTop (𝓝 0) := by
  have hc0 : (0 : ℝ) < c := by linarith
  have hc'0 : (0 : ℝ) < c' := by linarith
  have t1 := tendsto_discBudget_div_sq (β := β) (b := b) (A₃ := A₃) (K := Kd) hβ0 hβ1
  have t2 := tendsto_smallLadderPiece (a := a) (c := c) (A := A) (β := β) ha hab hβ0 hβ1 hc0 h2A
  have t3 : Tendsto (fun x : ℝ =>
      (1 + twoRangeDelta x)
        * (2 * ∫ w in Set.Icc (-(twoRangeTop β x)) (twoRangeTop β x),
            ‖ramareLadderError (lowP a c β x) (twoRangeLength β x) ((highBase a x : ℕ) : ℝ)
              (lowEta c x) (expSteps a c β x) w‖ ^ 2)
        / ((twoRangeLength β x : ℕ) : ℝ) ^ 2) atTop (𝓝 0) :=
    tendsto_defectPiece (β := β) (γ := β) (ℓ := β + c) (c := c) (K := 1 + c)
      hβ0 hβ1 hβ0 hβ1 (by linarith) (by linarith) (by linarith) hc0
      (Filter.Eventually.of_forall fun x p hp => (mem_primesRange.1 hp).1)
      (one_lt_highBase ha) (one_le_log_highBase ha) (rpow_log_le_highBase ha (1 + c))
      (by
        filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx1 p hp
        exact (primesRange_ladder_bounds_self (Q := ((highBase a x : ℕ) : ℝ)) rfl
          (lowEta_pos hx1).le (Nat.cast_nonneg _) rfl p hp).1.le)
      (Filter.Eventually.of_forall fun x => rfl)
      (expSteps_le ha hc0 hβ0)
      (expTop_le_cardLength ha hab hc0)
      (Filter.Eventually.of_forall fun x =>
        ⟨(cardLength_pos β x).le, by linarith [cardLength_pos β x]⟩)
  have t4 := tendsto_roughPiece (β := β) (γ := β) (cA := (β - a) / 2) hβ0 hβ1 hβ0 hβ1
    (by linarith) (P := fun x => lowP a c β x)
    (Filter.Eventually.of_forall fun x p hp => (mem_primesRange.1 hp).1)
    (expRange_harmonic_ge ha hab hc0)
    (by
      filter_upwards [expTop_le_cardLength ha hab hc0, Filter.eventually_gt_atTop (1 : ℝ)]
        with x htop hx1
      have h1 : ((lowP a c β x).card : ℝ) ≤ ((expTop a c β x : ℕ) : ℝ) :=
        card_primesRange_le_top _ _
      have h2 : ((expTop a c β x : ℕ) : ℝ) ≤ cardLength β x := by
        rw [expTop]
        refine le_trans (Nat.floor_le ?_) htop
        have hη0 : (0 : ℝ) < lowEta c x := lowEta_pos hx1
        positivity
      linarith [cardLength_pos β x])
  have t5 := tendsto_largeLadderPiece (A₀ := A₀) (δ₀ := δ₀) (Ctot := Ctot) (a := a) (c := c)
    (A := A) (β := β) (a₁ := a₁) (b := b) (c' := c') (A₃ := A₃) (E := E)
    hβ0 hβ1 hb0 hb1 ha₁ ha₁b hc'0 hE hE0 hρ0 hρ hUf
  have t6 : Tendsto (fun x : ℝ =>
      (1 + twoRangeDelta x)
        * (2 * ∫ w in Set.Icc (-(twoRangeTop β x)) (twoRangeTop β x),
            ‖ramareLadderError (highP a₁ b c' x) (twoRangeLength β x)
              ((highBase a₁ x : ℕ) : ℝ) (highEta c' x) (highSteps a₁ b c' x) w‖ ^ 2)
        / ((twoRangeLength β x : ℕ) : ℝ) ^ 2) atTop (𝓝 0) :=
    tendsto_defectPiece (β := β) (γ := b) (ℓ := b + c') (c := c') (K := 1 + c')
      hβ0 hβ1 hb0 hb1 (by linarith) (by linarith) (by linarith) hc'0
      (Filter.Eventually.of_forall fun x p hp => (mem_primesRange.1 hp).1)
      (one_lt_highBase ha₁) (one_le_log_highBase ha₁) (rpow_log_le_highBase ha₁ (1 + c'))
      (by
        filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx1 p hp
        exact (primesRange_ladder_bounds_self (Q := ((highBase a₁ x : ℕ) : ℝ)) rfl
          (highEta_pos hx1).le (Nat.cast_nonneg _) rfl p hp).1.le)
      (Filter.Eventually.of_forall fun x => rfl)
      (highSteps_le ha₁ ha₁b.le hc'0)
      (highLadder_le ha₁b.le hc'0)
      (Filter.Eventually.of_forall fun x =>
        ⟨by linarith [cardLength_pos b x], le_refl _⟩)
  have t7 := tendsto_roughPiece (β := β) (γ := b) (cA := (b - a₁) / 2) hβ0 hβ1 hb0 hb1
    (by linarith) (P := fun x => highP a₁ b c' x)
    (Filter.Eventually.of_forall fun x p hp => (mem_primesRange.1 hp).1)
    (highRange_harmonic_ge ha₁ ha₁b hb1 hc'0)
    (by
      filter_upwards [highLadder_le ha₁b.le hc'0, Filter.eventually_gt_atTop (1 : ℝ)]
        with x htop hx1
      have h1 : ((highP a₁ b c' x).card : ℝ) ≤ ((highTop a₁ b c' x : ℕ) : ℝ) :=
        card_primesRange_le_top _ _
      have h2 : ((highTop a₁ b c' x : ℕ) : ℝ) ≤ 2 * cardLength b x := by
        rw [highTop]
        refine le_trans (Nat.floor_le ?_) htop
        have hη0 : (0 : ℝ) < highEta c' x := highEta_pos hx1
        positivity
      linarith)
  have hsum := ((((((t1.add t2).add t3).add t4).add t5).add t6).add t7)
  rw [show ((0 : ℝ) + 0 + 0 + 0 + 0 + 0 + 0) = 0 by ring] at hsum
  refine hsum.congr fun x => ?_
  rw [twoRangeBudget, lowExceptional]
  ring

/-- The binary logarithm against the natural one. -/
theorem natLog_two_le {N : ℕ} (hN : 1 ≤ N) : ((Nat.log 2 N : ℕ) : ℝ) ≤ 2 * Real.log (N : ℝ) := by
  have hN0 : N ≠ 0 := by omega
  have h := Nat.pow_log_le_self 2 hN0
  have hc : ((2 : ℝ)) ^ (Nat.log 2 N) ≤ (N : ℝ) := by exact_mod_cast h
  have hlog := Real.log_le_log (by positivity) hc
  rw [Real.log_pow] at hlog
  have hl2 : (0.6 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hlogN : (0 : ℝ) ≤ Real.log (N : ℝ) := by
    refine Real.log_nonneg ?_
    exact_mod_cast hN
  nlinarith [hlog, hl2, hlogN, Nat.cast_nonneg (α := ℝ) (Nat.log 2 N)]

/-- **The Halász–Montgomery far constant at the schedule.** -/
theorem plainKernelFarConst_schedule_le {β a₁ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∀ᶠ x : ℝ in atTop,
      plainKernelFarConst ⌊((twoRangeLength β x : ℕ) : ℝ) / ((highBase a₁ x : ℕ) : ℝ)⌋₊
          (2 * Real.pi * twoRangeTop β x)
        ≤ 1000000 * Real.log x * Real.sqrt (Real.sqrt x) := by
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ), Filter.eventually_ge_atTop (16 : ℝ),
    one_le_twoRangeTop hβ0 hβ1, twoRangeTop_le_length hβ0 hβ1,
    twoRangeLength_le_two_sqrt hβ0 hβ1, one_le_twoRangeLength hβ0,
    Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)] with x hx1 hx16 hW hWM hM2 hM1 hlog1
  have hx0 : (0 : ℝ) < x := by linarith
  have hs0 : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hsqrt4 : (2 : ℝ) ≤ Real.sqrt x := by
    rw [show (2 : ℝ) = Real.sqrt 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  have hqq : (1 : ℝ) ≤ Real.sqrt (Real.sqrt x) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
    exact Real.sqrt_le_sqrt (by linarith)
  have hpi : Real.pi < 3.15 := Real.pi_lt_d2
  have hT : 2 * Real.pi * twoRangeTop β x ≤ 13 * Real.sqrt x := by
    nlinarith [hWM, hM2, hW, Real.pi_pos, hpi, hs0]
  have hT1 : (1 : ℝ) ≤ 2 * Real.pi * twoRangeTop β x := by
    nlinarith [hW, Real.pi_gt_three]
  -- the square root factor
  have hsq : Real.sqrt (2 * (2 * Real.pi * twoRangeTop β x)) ≤ 6 * Real.sqrt (Real.sqrt x) := by
    have h1 : Real.sqrt (2 * (2 * Real.pi * twoRangeTop β x)) ≤ Real.sqrt (26 * Real.sqrt x) :=
      Real.sqrt_le_sqrt (by linarith)
    have h2 : Real.sqrt (26 * Real.sqrt x) = Real.sqrt 26 * Real.sqrt (Real.sqrt x) :=
      Real.sqrt_mul (by norm_num) _
    have h3 : Real.sqrt 26 ≤ 6 := by
      rw [show (6 : ℝ) = Real.sqrt 36 by
        rw [show (36 : ℝ) = 6 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by norm_num)
    nlinarith [h1, h2, h3, Real.sqrt_nonneg (Real.sqrt x)]
  -- the two binary logarithms
  have hceil : ((⌈2 * (2 * Real.pi * twoRangeTop β x)⌉₊ : ℕ) : ℝ) ≤ 27 * Real.sqrt x := by
    have := Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ 2 * (2 * Real.pi * twoRangeTop β x))
    linarith [hT, hsqrt4]
  have hceil1 : 1 ≤ ⌈2 * (2 * Real.pi * twoRangeTop β x)⌉₊ := by
    refine Nat.one_le_ceil_iff.2 ?_
    linarith
  have hlogceil : ((Nat.log 2 ⌈2 * (2 * Real.pi * twoRangeTop β x)⌉₊ : ℕ) : ℝ)
      ≤ 12 + Real.log x := by
    have h1 := natLog_two_le hceil1
    have h2 : Real.log ((⌈2 * (2 * Real.pi * twoRangeTop β x)⌉₊ : ℕ) : ℝ)
        ≤ Real.log (27 * Real.sqrt x) := by
      refine Real.log_le_log ?_ hceil
      exact_mod_cast Nat.lt_of_lt_of_le zero_lt_one hceil1
    have h3 : Real.log (27 * Real.sqrt x) = Real.log 27 + Real.log x / 2 := by
      rw [Real.log_mul (by norm_num) (ne_of_gt hs0), Real.log_sqrt hx0.le]
    have h4 : Real.log 27 ≤ 6 := by
      have h3 : Real.log 3 ≤ 2 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
        linarith
      have hid : Real.log 27 = 3 * Real.log 3 := by
        rw [show (27 : ℝ) = 3 ^ 3 by norm_num, Real.log_pow]
        push_cast
        ring
      linarith
    linarith [h1, h2, h3, h4]
  have hN1 : 1 ≤ ⌊((twoRangeLength β x : ℕ) : ℝ) / ((highBase a₁ x : ℕ) : ℝ)⌋₊ ∨
      ⌊((twoRangeLength β x : ℕ) : ℝ) / ((highBase a₁ x : ℕ) : ℝ)⌋₊ = 0 := by
    rcases Nat.eq_zero_or_pos ⌊((twoRangeLength β x : ℕ) : ℝ) / ((highBase a₁ x : ℕ) : ℝ)⌋₊
      with h | h
    · exact Or.inr h
    · exact Or.inl h
  have hlogN : ((Nat.log 2 ⌊((twoRangeLength β x : ℕ) : ℝ)
      / ((highBase a₁ x : ℕ) : ℝ)⌋₊ : ℕ) : ℝ) ≤ 2 + Real.log x := by
    rcases hN1 with h | h
    · have h1 := natLog_two_le h
      have hfl : ((⌊((twoRangeLength β x : ℕ) : ℝ) / ((highBase a₁ x : ℕ) : ℝ)⌋₊ : ℕ) : ℝ)
          ≤ 2 * Real.sqrt x := by
        refine le_trans (Nat.floor_le ?_) ?_
        · positivity
        · refine le_trans ?_ hM2
          refine div_le_self (by linarith) ?_
          have h2 : (1 : ℝ) ≤ ((highBase a₁ x : ℕ) : ℝ) := by
            have := (highBase_bounds (a := a₁) hx1).1
            have hc : (1 : ℝ) ≤ cardLength a₁ x := by
              rw [cardLength]
              exact Real.one_le_exp (Real.rpow_nonneg (Real.log_pos hx1).le a₁)
            linarith
          exact h2
      have h2 : Real.log ((⌊((twoRangeLength β x : ℕ) : ℝ)
          / ((highBase a₁ x : ℕ) : ℝ)⌋₊ : ℕ) : ℝ) ≤ Real.log (2 * Real.sqrt x) := by
        refine Real.log_le_log ?_ hfl
        exact_mod_cast Nat.lt_of_lt_of_le zero_lt_one h
      have h3 : Real.log (2 * Real.sqrt x) = Real.log 2 + Real.log x / 2 := by
        rw [Real.log_mul (by norm_num) (ne_of_gt hs0), Real.log_sqrt hx0.le]
      have h4 : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
        linarith
      linarith [h1, h2, h3, h4]
    · rw [h]
      simp only [Nat.log_zero_right, Nat.cast_zero]
      linarith
  rw [plainKernelFarConst]
  nlinarith [hlogceil, hlogN, hsq, hqq, hlog1, Real.sqrt_nonneg (2 * (2 * Real.pi * twoRangeTop β x))]

/-- **A power of the logarithm against the growing moment order, the window and the outer scale.** -/
theorem tendsto_expSubLinear_cardLength_div_rpow {a₀ b₂ D e s : ℝ} (ha₀0 : 0 < a₀)
    (_ha₀1 : a₀ < 1) (_hb₂0 : 0 < b₂) (hb₂1 : b₂ < 1) (hD : 0 ≤ D) (hs : 0 < s) :
    Tendsto (fun x : ℝ => (Real.log x) ^ e
        * Real.exp (D * (Real.log x) ^ (1 - a₀) * Real.log (Real.log x))
        * cardLength b₂ x / x ^ s) atTop (𝓝 0) := by
  have hmaj := tendsto_logRpow_mul_expSaving (d := (1 : ℝ)) (s := s / 2) (by norm_num)
    (by linarith) e
  have hsmall := tendsto_logMonomial (e := -a₀) (by linarith) 1
  have hbs : Tendsto (fun x : ℝ => (Real.log x) ^ (b₂ - 1)) atTop (𝓝 0) :=
    tendsto_rpow_log_of_neg (by linarith)
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx1
    have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
    have h1 : (0 : ℝ) ≤ (Real.log x) ^ e := Real.rpow_nonneg hlogx.le e
    have h2 : (0 : ℝ) < x ^ s := Real.rpow_pos_of_pos (by linarith) s
    have h3 : (0 : ℝ) < cardLength b₂ x := cardLength_pos b₂ x
    positivity
  · filter_upwards [Filter.eventually_gt_atTop (1 : ℝ),
      Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ),
      Tendsto.eventually_le_const (show (0 : ℝ) < s / (4 * (D + 1)) by positivity) hsmall,
      Tendsto.eventually_le_const (show (0 : ℝ) < s / 4 by positivity) hbs] with x hx1 hlog1 hsm hbm
    have hx0 : (0 : ℝ) < x := by linarith
    have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
    have hnn : (0 : ℝ) ≤ (Real.log x) ^ e := Real.rpow_nonneg hlogx.le e
    have hll : (0 : ℝ) ≤ Real.log (Real.log x) := Real.log_nonneg hlog1
    rw [pow_one] at hsm
    have hprod : (Real.log x) ^ (-a₀) * Real.log x = (Real.log x) ^ (1 - a₀) := by
      rw [show (1 : ℝ) - a₀ = -a₀ + 1 by ring, Real.rpow_add hlogx, Real.rpow_one]
    have hmul := mul_le_mul_of_nonneg_right hsm hlogx.le
    have hid : (Real.log x) ^ (-a₀) * Real.log (Real.log x) * Real.log x
        = (Real.log x) ^ (1 - a₀) * Real.log (Real.log x) := by
      rw [← hprod]
      ring
    rw [hid] at hmul
    have hDfrac : D * (s / (4 * (D + 1))) ≤ s / 4 := by
      have hpos : (0 : ℝ) < 4 * (D + 1) := by positivity
      rw [← mul_div_assoc, div_le_div_iff₀ hpos (by norm_num : (0 : ℝ) < 4)]
      nlinarith [hD, hs]
    have hkey : D * (Real.log x) ^ (1 - a₀) * Real.log (Real.log x) ≤ s / 4 * Real.log x := by
      nlinarith [hmul, hD, hlogx, hDfrac]
    have hprod2 : (Real.log x) ^ (b₂ - 1) * Real.log x = (Real.log x) ^ b₂ := by
      have h1 : (Real.log x) ^ b₂ = (Real.log x) ^ (b₂ - 1) * (Real.log x) ^ (1 : ℝ) := by
        rw [← Real.rpow_add hlogx]
        congr 1
        ring
      rw [h1, Real.rpow_one]
    have hbkey : (Real.log x) ^ b₂ ≤ s / 4 * Real.log x := by
      have := mul_le_mul_of_nonneg_right hbm hlogx.le
      rw [hprod2] at this
      linarith
    have hxs : x ^ s = Real.exp (s * Real.log x) := by
      rw [Real.rpow_def_of_pos hx0]
      congr 1
      ring
    have hcl : cardLength b₂ x = Real.exp ((Real.log x) ^ b₂) := rfl
    rw [hxs, hcl]
    have hdiv : (Real.log x) ^ e * Real.exp (D * (Real.log x) ^ (1 - a₀) * Real.log (Real.log x))
          * Real.exp ((Real.log x) ^ b₂) / Real.exp (s * Real.log x)
        = (Real.log x) ^ e
          * Real.exp (D * (Real.log x) ^ (1 - a₀) * Real.log (Real.log x)
            + (Real.log x) ^ b₂ - s * Real.log x) := by
      rw [Real.exp_sub, Real.exp_add]
      ring
    rw [hdiv]
    have hexple : Real.exp (D * (Real.log x) ^ (1 - a₀) * Real.log (Real.log x)
          + (Real.log x) ^ b₂ - s * Real.log x)
        ≤ Real.exp (-(s / 2 * (Real.log x) ^ (1 : ℝ))) := by
      rw [Real.rpow_one]
      exact Real.exp_le_exp.2 (by linarith)
    exact mul_le_mul_of_nonneg_left hexple hnn

set_option maxHeartbeats 4000000 in
/-- **The exceptional-measure factor of the large ladder group vanishes.**  This is the hypothesis
`hUf` of `tendsto_largeLadderPiece`, and the only place the moment method enters the budget. -/
theorem tendsto_exceptionalFactor {a c A β a₁ b c' A₃ : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (ha : 0 < a) (hab : a < β) (ha1 : a < 1) (hc : 0 < c)
    (hA : 0 < A) (hb0 : 0 < b) (hb1 : b < 1) (_hc' : 0 < c') :
    Tendsto (fun x : ℝ => (Real.log x) ^ (b + c')
        * (plainKernelFarConst
              ⌊((twoRangeLength β x : ℕ) : ℝ) / ((highBase a₁ x : ℕ) : ℝ)⌋₊
              (2 * Real.pi * twoRangeTop β x)
            * (2 * Real.pi * volume.real (lowExceptional a c A β b A₃ x)))
        * (cardLength b x * Real.log (Real.log x) / ((twoRangeLength β x : ℕ) : ℝ)
          + cardLength b x ^ 2 / ((twoRangeLength β x : ℕ) : ℝ) ^ 2)) atTop (𝓝 0) := by
  set b₂ : ℝ := (b + 1) / 2 with hb₂def
  have hb₂0 : 0 < b₂ := by rw [hb₂def]; linarith
  have hb₂1 : b₂ < 1 := by rw [hb₂def]; linarith
  have hbb₂ : b < b₂ := by rw [hb₂def]; linarith
  set D : ℝ := c + 2 * A + β + 2 with hDdef
  have hD0 : (0 : ℝ) ≤ D := by rw [hDdef]; linarith
  set e₄ : ℝ := b + c' + 1 + (β + c) + (1 + β - a) with he₄def
  have hmaj0 := tendsto_expSubLinear_cardLength_div_rpow (a₀ := a) (b₂ := b₂)
    (D := 3 * D) (e := e₄) (s := (1 : ℝ) / 4) ha ha1 hb₂0 hb₂1 (by linarith) (by norm_num)
  have hmaj : Tendsto (fun x : ℝ => 144000000 * Real.pi
      * ((Real.log x) ^ e₄ * Real.exp (3 * D * (Real.log x) ^ (1 - a) * Real.log (Real.log x))
        * cardLength b₂ x / x ^ ((1 : ℝ) / 4))) atTop (𝓝 0) := by
    have := hmaj0.const_mul (144000000 * Real.pi)
    rw [show (144000000 * Real.pi * 0) = 0 by ring] at this
    exact this
  -- the shrinking of the window factor
  have hcls : Tendsto (fun x : ℝ => (Real.log x) ^ (b - b₂)) atTop (𝓝 0) :=
    tendsto_rpow_log_of_neg (by linarith)
  have hus : Tendsto (fun x : ℝ =>
      (Real.log x) ^ (-b₂) * (Real.log (Real.log x)) ^ 1) atTop (𝓝 0) :=
    tendsto_logMonomial (e := -b₂) (by linarith) 1
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [Filter.eventually_gt_atTop (1 : ℝ), one_le_twoRangeTop hβ0 hβ1,
      Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)] with x hx1 hW hlog1
    have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
    have hu0 : (0 : ℝ) ≤ Real.log (Real.log x) := Real.log_nonneg hlog1
    have hvol : (0 : ℝ) ≤ volume.real (lowExceptional a c A β b A₃ x) := ENNReal.toReal_nonneg
    have hF : (0 : ℝ) ≤ plainKernelFarConst
        ⌊((twoRangeLength β x : ℕ) : ℝ) / ((highBase a₁ x : ℕ) : ℝ)⌋₊
        (2 * Real.pi * twoRangeTop β x) := by
      refine plainKernelFarConst_nonneg _ ?_
      nlinarith [hW, Real.pi_gt_three]
    have hpe : (0 : ℝ) ≤ (Real.log x) ^ (b + c') := Real.rpow_nonneg hlogx.le _
    have hcl : (0 : ℝ) < cardLength b x := cardLength_pos b x
    have hM : (0 : ℝ) ≤ ((twoRangeLength β x : ℕ) : ℝ) := Nat.cast_nonneg _
    have hZ : (0 : ℝ) ≤ cardLength b x * Real.log (Real.log x) / ((twoRangeLength β x : ℕ) : ℝ)
        + cardLength b x ^ 2 / ((twoRangeLength β x : ℕ) : ℝ) ^ 2 := by positivity
    have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
    have hmid : (0 : ℝ) ≤ plainKernelFarConst
        ⌊((twoRangeLength β x : ℕ) : ℝ) / ((highBase a₁ x : ℕ) : ℝ)⌋₊
        (2 * Real.pi * twoRangeTop β x) * (2 * Real.pi
          * volume.real (lowExceptional a c A β b A₃ x)) := by positivity
    exact mul_nonneg (mul_nonneg hpe hmid) hZ
  · filter_upwards [Filter.eventually_gt_atTop (1 : ℝ), Filter.eventually_ge_atTop (16 : ℝ),
      one_le_twoRangeTop hβ0 hβ1, twoRangeLength_le_two_sqrt hβ0 hβ1,
      sqrt_le_twoRangeLength hβ0, one_le_twoRangeLength hβ0,
      Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ),
      twoRangeTop_le_length hβ0 hβ1,
      plainKernelFarConst_schedule_le (β := β) (a₁ := a₁) hβ0 hβ1,
      measureReal_annulusLarge_schedule (a := a) (c := c) (A := A) (β := β) ha hab hβ1 hc hA,
      expSteps_le (a := a) (c := c) (β := β) ha hc hβ0,
      Tendsto.eventually_le_const (show (0 : ℝ) < 1 / 2 by norm_num) hcls,
      Tendsto.eventually_le_const (show (0 : ℝ) < 1 / 4 by norm_num) hus,
      Filter.eventually_ge_atTop (Real.exp 1),
      Real.tendsto_log_atTop.eventually_ge_atTop (Real.exp 1)]
      with x hx1 hx16 hW hM2 hMsq hM1 hlog1 hWMx hFC hvolbd hLbd hclsm hussm hxe hlbig
    have hx0 : (0 : ℝ) < x := by linarith
    have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
    have hu0 : (0 : ℝ) ≤ Real.log (Real.log x) := Real.log_nonneg hlog1
    have hs0 : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 hx0
    have hsq1 : (1 : ℝ) ≤ Real.sqrt x := by
      rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
      exact Real.sqrt_le_sqrt (by linarith)
    have hxx : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
    have hM0 : (0 : ℝ) < ((twoRangeLength β x : ℕ) : ℝ) := by linarith
    have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
    have hclb : (0 : ℝ) < cardLength b x := cardLength_pos b x
    have hclb₂ : (0 : ℝ) < cardLength b₂ x := cardLength_pos b₂ x
    have hu1 : (1 : ℝ) ≤ Real.log (Real.log x) := by
      have := Real.log_le_log (Real.exp_pos 1) hlbig
      rwa [Real.log_exp] at this
    -- the window factor
    have hpb : (Real.log x) ^ b ≤ (Real.log x) ^ b₂ / 2 := by
      have hp₂ : (0 : ℝ) < (Real.log x) ^ b₂ := Real.rpow_pos_of_pos hlogx b₂
      have hid : (Real.log x) ^ b = (Real.log x) ^ (b - b₂) * (Real.log x) ^ b₂ := by
        rw [← Real.rpow_add hlogx]
        congr 1
        ring
      rw [hid]
      nlinarith [hclsm, hp₂]
    have hulog : Real.log (Real.log (Real.log x)) ≤ (Real.log x) ^ b₂ / 2 := by
      have hp₂ : (0 : ℝ) < (Real.log x) ^ b₂ := Real.rpow_pos_of_pos hlogx b₂
      have hle : Real.log (Real.log (Real.log x)) ≤ Real.log (Real.log x) := by
        have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < Real.log (Real.log x))
        linarith
      have hid : (Real.log x) ^ (-b₂) * (Real.log (Real.log x)) ^ 1
          = Real.log (Real.log x) / (Real.log x) ^ b₂ := by
        rw [pow_one, Real.rpow_neg hlogx.le]
        field_simp
      rw [hid, div_le_iff₀ hp₂] at hussm
      linarith [hle, hussm, hp₂]
    have hcl1 : cardLength b x * Real.log (Real.log x) ≤ cardLength b₂ x := by
      have hexp : Real.log (Real.log x) ≤ Real.exp ((Real.log x) ^ b₂ / 2) := by
        have h1 : Real.log (Real.log (Real.log x)) ≤ (Real.log x) ^ b₂ / 2 := hulog
        have h2 := Real.exp_le_exp.2 h1
        rwa [Real.exp_log (by linarith)] at h2
      rw [cardLength, cardLength]
      calc Real.exp ((Real.log x) ^ b) * Real.log (Real.log x)
          ≤ Real.exp ((Real.log x) ^ b₂ / 2) * Real.exp ((Real.log x) ^ b₂ / 2) := by
            refine mul_le_mul (Real.exp_le_exp.2 hpb) hexp (by linarith) (by positivity)
        _ = Real.exp ((Real.log x) ^ b₂) := by
            rw [← Real.exp_add]
            congr 1
            ring
    have hcl2 : cardLength b x ^ 2 ≤ cardLength b₂ x := by
      rw [cardLength, cardLength, ← Real.exp_nat_mul]
      refine Real.exp_le_exp.2 ?_
      push_cast
      linarith [hpb]
    have hZ : cardLength b x * Real.log (Real.log x) / ((twoRangeLength β x : ℕ) : ℝ)
          + cardLength b x ^ 2 / ((twoRangeLength β x : ℕ) : ℝ) ^ 2
        ≤ 2 * (cardLength b₂ x / Real.sqrt x) := by
      have h1 : cardLength b x * Real.log (Real.log x) / ((twoRangeLength β x : ℕ) : ℝ)
          ≤ cardLength b₂ x / Real.sqrt x := by
        refine div_le_div₀ (by positivity) hcl1 hs0 hMsq
      have h2 : cardLength b x ^ 2 / ((twoRangeLength β x : ℕ) : ℝ) ^ 2
          ≤ cardLength b₂ x / Real.sqrt x := by
        refine div_le_div₀ (by positivity) hcl2 hs0 ?_
        nlinarith [hMsq, hs0, hsq1]
      linarith
    -- the measure factor
    have hk3 : ((momentOrder a x : ℕ) : ℝ) ≤ 3 * (Real.log x) ^ (1 - a) := by
      refine momentOrder_le hx1 ?_
      exact Real.one_le_rpow hlog1 (by linarith)
    have hk0 : (0 : ℝ) ≤ ((momentOrder a x : ℕ) : ℝ) := Nat.cast_nonneg _
    have hnmax : Real.log 2 + (Real.log x) ^ β ≤ 2 * (Real.log x) ^ β := by
      have hl2 : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
        linarith
      have := Real.one_le_rpow hlog1 hβ0.le
      linarith
    have hexpk : Real.exp (((momentOrder a x : ℕ) : ℝ) * (D * Real.log (Real.log x)))
        ≤ Real.exp (3 * D * (Real.log x) ^ (1 - a) * Real.log (Real.log x)) := by
      refine Real.exp_le_exp.2 ?_
      have h1 : (0 : ℝ) ≤ D * Real.log (Real.log x) := mul_nonneg hD0 hu0
      have h2 := mul_le_mul_of_nonneg_right hk3 h1
      linarith [h2]
    have hWM : twoRangeTop β x ≤ ((twoRangeLength β x : ℕ) : ℝ) := hWMx
    have hpow1 : (1 : ℝ) ≤ (Real.log x) ^ (1 + β - a) :=
      Real.one_le_rpow hlog1 (by linarith)
    have hpowβc : (0 : ℝ) < (Real.log x) ^ (β + c) := Real.rpow_pos_of_pos hlogx _
    have hexp1 : (1 : ℝ) ≤ Real.exp (3 * D * (Real.log x) ^ (1 - a) * Real.log (Real.log x)) := by
      refine Real.one_le_exp ?_
      have h1 : (0 : ℝ) ≤ (Real.log x) ^ (1 - a) := Real.rpow_nonneg hlogx.le _
      exact mul_nonneg (mul_nonneg (by linarith) h1) hu0
    have hV : volume.real (lowExceptional a c A β b A₃ x)
        ≤ 36 * ((Real.log x) ^ ((β + c) + (1 + β - a))
          * Real.exp (3 * D * (Real.log x) ^ (1 - a) * Real.log (Real.log x))) := by
      refine (hvolbd (twoRangeDisc b A₃ x)).trans ?_
      have hWx : 2 * twoRangeTop β x / x ≤ 4 := by
        rw [div_le_iff₀ hx0]
        nlinarith [hWM, hM2, hs0, hsq1, hxx]
      have hnm : 2 * (1 + ((momentOrder a x : ℕ) : ℝ) * (Real.log 2 + (Real.log x) ^ β))
            * Real.exp (((momentOrder a x : ℕ) : ℝ) * (D * Real.log (Real.log x)))
          ≤ 14 * ((Real.log x) ^ (1 + β - a)
            * Real.exp (3 * D * (Real.log x) ^ (1 - a) * Real.log (Real.log x))) := by
        have hprod : (Real.log x) ^ (1 - a) * (Real.log x) ^ β = (Real.log x) ^ (1 + β - a) := by
          rw [← Real.rpow_add hlogx]
          congr 1
          ring
        have hnum : 1 + ((momentOrder a x : ℕ) : ℝ) * (Real.log 2 + (Real.log x) ^ β)
            ≤ 7 * (Real.log x) ^ (1 + β - a) := by
          have hpβ : (0 : ℝ) < (Real.log x) ^ β := Real.rpow_pos_of_pos hlogx β
          have h1 : ((momentOrder a x : ℕ) : ℝ) * (Real.log 2 + (Real.log x) ^ β)
              ≤ 3 * (Real.log x) ^ (1 - a) * (2 * (Real.log x) ^ β) := by
            have hl2n : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
            refine mul_le_mul hk3 hnmax (by linarith [hpβ, hl2n]) (by positivity)
          have h2 : 3 * (Real.log x) ^ (1 - a) * (2 * (Real.log x) ^ β)
              = 6 * (Real.log x) ^ (1 + β - a) := by
            rw [← hprod]
            ring
          linarith [h1, h2, hpow1]
        have hnum0 : (0 : ℝ) ≤ 1 + ((momentOrder a x : ℕ) : ℝ)
            * (Real.log 2 + (Real.log x) ^ β) := by
          have hpβ : (0 : ℝ) < (Real.log x) ^ β := Real.rpow_pos_of_pos hlogx β
          have hl2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
          positivity
        nlinarith [hnum, hexpk, hnum0, hexp1, Real.exp_pos
          (((momentOrder a x : ℕ) : ℝ) * (D * Real.log (Real.log x)))]
      have hinner : 2 * twoRangeTop β x / x
            + 2 * (1 + ((momentOrder a x : ℕ) : ℝ) * (Real.log 2 + (Real.log x) ^ β))
              * Real.exp (((momentOrder a x : ℕ) : ℝ) * (D * Real.log (Real.log x)))
          ≤ 18 * ((Real.log x) ^ (1 + β - a)
            * Real.exp (3 * D * (Real.log x) ^ (1 - a) * Real.log (Real.log x))) := by
        nlinarith [hWx, hnm, hpow1, hexp1]
      have hinner0 : (0 : ℝ) ≤ 18 * ((Real.log x) ^ (1 + β - a)
          * Real.exp (3 * D * (Real.log x) ^ (1 - a) * Real.log (Real.log x))) := by positivity
      have hstep := mul_le_mul hLbd hinner (by
        have hpβ : (0 : ℝ) < (Real.log x) ^ β := Real.rpow_pos_of_pos hlogx β
        have hl2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
        have hW0 : (0 : ℝ) ≤ 2 * twoRangeTop β x / x := by positivity
        have h2 : (0 : ℝ) ≤ 2 * (1 + ((momentOrder a x : ℕ) : ℝ)
            * (Real.log 2 + (Real.log x) ^ β))
            * Real.exp (((momentOrder a x : ℕ) : ℝ) * (D * Real.log (Real.log x))) := by
          positivity
        linarith) (by positivity)
      refine hstep.trans (le_of_eq ?_)
      have hprodlog : (Real.log x) ^ (β + c) * (Real.log x) ^ (1 + β - a)
          = (Real.log x) ^ ((β + c) + (1 + β - a)) := by
        rw [← Real.rpow_add hlogx]
      calc 2 * (Real.log x) ^ (β + c)
            * (18 * ((Real.log x) ^ (1 + β - a)
              * Real.exp (3 * D * (Real.log x) ^ (1 - a) * Real.log (Real.log x))))
          = 36 * ((Real.log x) ^ (β + c) * (Real.log x) ^ (1 + β - a)
            * Real.exp (3 * D * (Real.log x) ^ (1 - a) * Real.log (Real.log x))) := by ring
        _ = 36 * ((Real.log x) ^ ((β + c) + (1 + β - a))
            * Real.exp (3 * D * (Real.log x) ^ (1 - a) * Real.log (Real.log x))) := by
            rw [hprodlog]
    -- assemble
    have hV0 : (0 : ℝ) ≤ volume.real (lowExceptional a c A β b A₃ x) := ENNReal.toReal_nonneg
    have hF0 : (0 : ℝ) ≤ plainKernelFarConst
        ⌊((twoRangeLength β x : ℕ) : ℝ) / ((highBase a₁ x : ℕ) : ℝ)⌋₊
        (2 * Real.pi * twoRangeTop β x) := by
      refine plainKernelFarConst_nonneg _ ?_
      nlinarith [hW, Real.pi_gt_three]
    have hpe0 : (0 : ℝ) ≤ (Real.log x) ^ (b + c') := Real.rpow_nonneg hlogx.le _
    have hZ0 : (0 : ℝ) ≤ cardLength b x * Real.log (Real.log x) / ((twoRangeLength β x : ℕ) : ℝ)
        + cardLength b x ^ 2 / ((twoRangeLength β x : ℕ) : ℝ) ^ 2 := by positivity
    have hmid : plainKernelFarConst
          ⌊((twoRangeLength β x : ℕ) : ℝ) / ((highBase a₁ x : ℕ) : ℝ)⌋₊
          (2 * Real.pi * twoRangeTop β x)
        * (2 * Real.pi * volume.real (lowExceptional a c A β b A₃ x))
        ≤ (1000000 * Real.log x * Real.sqrt (Real.sqrt x))
          * (2 * Real.pi * (36 * ((Real.log x) ^ ((β + c) + (1 + β - a))
            * Real.exp (3 * D * (Real.log x) ^ (1 - a) * Real.log (Real.log x))))) := by
      refine mul_le_mul hFC ?_ (by positivity) (by positivity)
      nlinarith [hV, hπ]
    have hchain : (Real.log x) ^ (b + c')
          * (plainKernelFarConst
              ⌊((twoRangeLength β x : ℕ) : ℝ) / ((highBase a₁ x : ℕ) : ℝ)⌋₊
              (2 * Real.pi * twoRangeTop β x)
            * (2 * Real.pi * volume.real (lowExceptional a c A β b A₃ x)))
          * (cardLength b x * Real.log (Real.log x) / ((twoRangeLength β x : ℕ) : ℝ)
            + cardLength b x ^ 2 / ((twoRangeLength β x : ℕ) : ℝ) ^ 2)
        ≤ (Real.log x) ^ (b + c')
          * ((1000000 * Real.log x * Real.sqrt (Real.sqrt x))
            * (2 * Real.pi * (36 * ((Real.log x) ^ ((β + c) + (1 + β - a))
              * Real.exp (3 * D * (Real.log x) ^ (1 - a) * Real.log (Real.log x))))))
          * (2 * (cardLength b₂ x / Real.sqrt x)) := by
      refine mul_le_mul (mul_le_mul_of_nonneg_left hmid hpe0) hZ hZ0 ?_
      have := Real.sqrt_nonneg (Real.sqrt x)
      positivity
    refine hchain.trans (le_of_eq ?_)
    have hxq : x ^ ((1 : ℝ) / 4) = Real.sqrt (Real.sqrt x) := by
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hx0.le]
      norm_num
    have hq0 : (0 : ℝ) < Real.sqrt (Real.sqrt x) := Real.sqrt_pos.2 hs0
    have hqq : Real.sqrt (Real.sqrt x) * Real.sqrt (Real.sqrt x) = Real.sqrt x :=
      Real.mul_self_sqrt hs0.le
    have hprodlog2 : (Real.log x) ^ (b + c') * Real.log x
          * (Real.log x) ^ ((β + c) + (1 + β - a))
        = (Real.log x) ^ e₄ := by
      have e1 : (Real.log x) ^ e₄
          = (Real.log x) ^ (b + c') * ((Real.log x) ^ (1 : ℝ)
            * (Real.log x) ^ ((β + c) + (1 + β - a))) := by
        rw [← Real.rpow_add hlogx, ← Real.rpow_add hlogx, he₄def]
        congr 1
        ring
      rw [e1, Real.rpow_one]
      ring
    rw [hxq, ← hprodlog2]
    field_simp
    linear_combination (144000000 : ℝ) * Real.sq_sqrt hs0.le

set_option maxHeartbeats 4000000 in
/-- **The averaged short-interval mean square for the Möbius function at window
`h = exp((log x)^β)`, for every `0 < β < 1`.**

The two-range architecture: a low designated range `exp((log x)^{β/2}) < p ≤ h` thresholded at
`(log x)^{-(β+2)}`, and a high range `exp((log x)^{19/20}) < q ≤ exp((log x)^{99/100})` carrying the
Route-T zero-free-region bound everywhere on the annulus.  The exceptional half of the annulus is
paid by Halász–Montgomery with the Kuzmin–Landau kernel, and its measure by the moment method at
the growing order `⌈2(log x)^{1-β/2}⌉`. -/
theorem averagedMeanSquare_moebius_cardLength_all {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    AveragedMeanSquare (fun n => ((μ n : ℤ) : ℝ)) (cardLength β) := by
  obtain ⟨A₀, δ₀, Ctot, hδ₀, hCtot, hhigh, hlim⟩ :=
    exists_twoRange_high_bound (a := 19 / 20) (b := 99 / 100) (c' := 3) (β := β) (A₃ := 8)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hβ0 hβ1 (by norm_num)
  obtain ⟨Kd, hKd, hdiscb⟩ :=
    exists_discBudget_bound (β := β) (b := 99 / 100) (A₃ := 8) hβ0 hβ1 (by norm_num) (by norm_num)
  have hρ0 := twoRangeHighRho_nonneg (A₀ := A₀) (δ₀ := δ₀) (Ctot := Ctot) (a₁ := 19 / 20)
    (b := 99 / 100) (c' := 3) (β := β) (A₃ := 8) hCtot.le (by norm_num) (by norm_num) hβ0 hβ1
  have hρ : Tendsto (fun x : ℝ => (Real.log x) ^ (3 : ℝ)
      * (8 * twoRangeHighRho A₀ δ₀ Ctot (19 / 20) (99 / 100) 3 β 8 x
        * (Real.log x) ^ (99 / 100 + (3 : ℝ)))) atTop (𝓝 0) := by
    have h := hlim ((3 : ℝ) + 99 / 100 + 3) (by norm_num) (by norm_num)
    have h8 := h.const_mul (8 : ℝ)
    rw [show ((8 : ℝ) * 0) = 0 by ring] at h8
    refine h8.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx
    have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx
    have hid : (Real.log x) ^ ((3 : ℝ) + 99 / 100 + 3)
        = (Real.log x) ^ (3 : ℝ) * (Real.log x) ^ (99 / 100 + (3 : ℝ)) := by
      rw [show (3 : ℝ) + 99 / 100 + 3 = 3 + (99 / 100 + 3) by ring, Real.rpow_add hlogx]
    rw [hid]
    ring
  have hUf := tendsto_exceptionalFactor (a := β / 2) (c := 2 + β) (A := β + 2) (β := β)
    (a₁ := 19 / 20) (b := 99 / 100) (c' := 3) (A₃ := 8) hβ0 hβ1 (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
  have hbnd := twoRangeBudget_bound (A₀ := A₀) (δ₀ := δ₀) (Ctot := Ctot) (Kd := Kd)
    (a := β / 2) (c := 2 + β) (A := β + 2) (β := β) (a₁ := 19 / 20) (b := 99 / 100) (c' := 3)
    (A₃ := 8) hβ0 hβ1 (by linarith) (by linarith) (by linarith) (by linarith)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hhigh hdiscb hρ0 (by norm_num)
  have hrel := tendsto_twoRangeBudget_div_sq (A₀ := A₀) (δ₀ := δ₀) (Ctot := Ctot) (Kd := Kd)
    (a := β / 2) (c := 2 + β) (A := β + 2) (β := β) (a₁ := 19 / 20) (b := 99 / 100) (c' := 3)
    (A₃ := 8) (E := 3) hβ0 hβ1 (by linarith) (by linarith) (by linarith) (by linarith)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hρ0 hρ hUf
  refine averagedMeanSquare_moebius_of_headSmall (hh := cardLength β)
    (ω := fun x => Real.log (Real.log x))
    (B := fun x => twoRangeBudget A₀ δ₀ Ctot Kd (β / 2) (2 + β) (β + 2) β (19 / 20)
      (99 / 100) 3 8 x)
    (tendsto_cardLength hβ0) ?_ ?_ hrel
  · filter_upwards [Filter.eventually_ge_atTop (4 : ℝ), Filter.eventually_gt_atTop (1 : ℝ),
      (tendsto_cardLength hβ0).eventually_ge_atTop (1 : ℝ), cardLength_le_sqrt hβ0 hβ1,
      Real.tendsto_log_atTop.eventually_ge_atTop (Real.exp 1), hbnd,
      one_le_twoRangeTop hβ0 hβ1] with x hx4 hx1 hh1 hhs hlbig hb hW
    have hu1 : (1 : ℝ) ≤ Real.log (Real.log x) := by
      have := Real.log_le_log (Real.exp_pos 1) hlbig
      rwa [Real.log_exp] at this
    have hI : (0 : ℝ) ≤ ∫ w in Set.Icc (-(twoRangeTop β x)) (twoRangeTop β x),
        ‖logPoly (fun n => ((μ n : ℤ) : ℂ)) (Finset.Icc 1 (twoRangeLength β x)) w‖ ^ 2 :=
      MeasureTheory.setIntegral_nonneg measurableSet_Icc fun w _ => by positivity
    exact ⟨hx4, hh1, hhs, hu1, le_trans hI hb, hb⟩
  · exact Real.tendsto_log_atTop.comp Real.tendsto_log_atTop

end

end RHTower.Sieve
