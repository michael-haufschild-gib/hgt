import GaloisForLFunctions.RHTower.Sieve.SiftingRangeRatio
import GaloisForLFunctions.RHTower.Sieve.LogLogSmall
import GaloisForLFunctions.RHTower.Sieve.AlmostPrimeGlobalCount
import GaloisForLFunctions.RHTower.MobiusWholeAnchorGlobalTerminalCapacity
import GaloisForLFunctions.RHTower.Sieve.BlockCount

/-!
# The parameters of the spectral estimate

The short-interval argument fixes a window length `h = exp((log x)^β)`, a bottom `Q = exp((log x)^{γβ})`
for the designated primes, a ladder of ratio `1 + η` with `η = (log x)^{γβ−1}`, a polylogarithmic
smoothing width, a Gallagher cut at `B₀/h` and an annulus threshold that is polylogarithmic.  This
file records those choices and their elementary properties.
-/

namespace RHTower.Sieve

open Filter Topology

noncomputable section

/-- The ratio of the ladder's steps.  The exponent is forced by the ladder defect: the defect
contributes `(log B₀/log Q)·L·η²` to the affine constant, and `L ≍ (log x)^β/η`, so `η` must be
below `(log x)^{γβ−β−1}` for that to be `O(1)` after normalisation. -/
def ladderEta (β γ x : ℝ) : ℝ := (Real.log x) ^ (γ * β - β - 5 / 4)

/-- The smoothing width of the twisted contour. -/
def ladderWidth (β x : ℝ) : ℝ := (Real.log (2 * cardLength β x)) ^ 4

/-- The number of steps of the ladder. -/
def ladderSteps (β γ x : ℝ) : ℕ :=
  ⌊Real.log (cardLength β x / ((siftStart (γ * β) x : ℕ) : ℝ))
    / Real.log (1 + ladderEta β γ x)⌋₊

/-- The top of the ladder. -/
def ladderTop (β γ x : ℝ) : ℕ :=
  ⌊((siftStart (γ * β) x : ℕ) : ℝ) * (1 + ladderEta β γ x) ^ (ladderSteps β γ x)⌋₊

/-- The Gallagher cut. -/
def gallagherCut (β x : ℝ) : ℝ :=
  ((⌊Real.sqrt x + cardLength β x⌋₊ : ℕ) : ℝ) / cardLength β x

/-- The threshold above which the prime polynomial carries cancellation.  The exponent must exceed
`12β + 1 − γβ`, which is below `13` for every admissible pair. -/
def annulusStart (β x : ℝ) : ℝ := (Real.log x) ^ (13 : ℝ)

theorem ladderEta_pos {β γ x : ℝ} (hx : 1 < x) : 0 < ladderEta β γ x :=
  Real.rpow_pos_of_pos (Real.log_pos hx) _

/-- **The step ratio vanishes.** -/
theorem tendsto_ladderEta {β γ : ℝ} (hβ0 : 0 < β) (h : γ * β < 1) :
    Tendsto (fun x : ℝ => ladderEta β γ x) atTop (𝓝 0) := by
  have hδ : (0 : ℝ) < 5 / 4 + β - γ * β := by linarith
  have hmaj := tendsto_log_rpow_neg hδ
  refine hmaj.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx
  have hlog : 0 < Real.log x := Real.log_pos hx
  rw [ladderEta]
  congr 1
  ring

/-- The smoothing width is at least one. -/
theorem one_le_ladderWidth {β : ℝ} (hβ : 0 < β) :
    ∀ᶠ x : ℝ in atTop, 1 ≤ ladderWidth β x := by
  have hpow : Tendsto (fun x : ℝ => (Real.log x) ^ β) atTop atTop :=
    (tendsto_rpow_atTop hβ).comp Real.tendsto_log_atTop
  filter_upwards [hpow.eventually_ge_atTop (1 : ℝ), Filter.eventually_gt_atTop (1 : ℝ)]
    with x hbig hx1
  have hlog : Real.log (2 * cardLength β x) = Real.log 2 + (Real.log x) ^ β := by
    rw [Real.log_mul (by norm_num) (ne_of_gt (cardLength_pos β x)), log_cardLength]
  have hl2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h1 : (1 : ℝ) ≤ Real.log (2 * cardLength β x) := by
    rw [hlog]
    linarith
  rw [ladderWidth]
  exact one_le_pow₀ h1

/-- The designated range is non-degenerate. -/
theorem eventually_siftStart_lt_cardLength {β γ : ℝ} (hβ : 0 < β) (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    ∀ᶠ x : ℝ in atTop, 2 * ((siftStart (γ * β) x : ℕ) : ℝ) ≤ cardLength β x := by
  have hab : (0 : ℝ) < γ * β := mul_pos hγ0 hβ
  have hpowA : Tendsto (fun x : ℝ => (Real.log x) ^ (γ * β)) atTop atTop :=
    (tendsto_rpow_atTop hab).comp Real.tendsto_log_atTop
  have hpowB : Tendsto (fun x : ℝ => (Real.log x) ^ (β - γ * β)) atTop atTop :=
    (tendsto_rpow_atTop (by nlinarith)).comp Real.tendsto_log_atTop
  filter_upwards [hpowA.eventually_ge_atTop (2 * Real.log 2 + 2),
    hpowB.eventually_ge_atTop (2 : ℝ), Filter.eventually_gt_atTop (1 : ℝ)] with x hA hB hx1
  have hlog : 0 < Real.log x := Real.log_pos hx1
  set u : ℝ := (Real.log x) ^ (γ * β) with hu
  have hu1 : (1 : ℝ) ≤ u := by
    have hl2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    linarith
  have hsplit : (Real.log x) ^ β = u * (Real.log x) ^ (β - γ * β) := by
    rw [hu, ← Real.rpow_add hlog]
    congr 1
    ring
  have hbig : u + Real.log 2 + 1 ≤ (Real.log x) ^ β := by
    rw [hsplit]
    nlinarith [hB, hu1, hA]
  -- the ceiling costs at most one
  have hceil : ((siftStart (γ * β) x : ℕ) : ℝ) ≤ Real.exp u + 1 := by
    rw [siftStart, ← hu]
    exact le_of_lt (Nat.ceil_lt_add_one (Real.exp_pos u).le)
  have he1 : (1 : ℝ) ≤ Real.exp u := Real.one_le_exp (by linarith)
  have hstep : 2 * (Real.exp u + 1) ≤ 4 * Real.exp u := by linarith
  have hfour : (4 : ℝ) * Real.exp u ≤ cardLength β x := by
    have hexp : Real.exp (u + Real.log 2 + 1) ≤ cardLength β x := by
      rw [cardLength]
      exact Real.exp_le_exp.2 hbig
    have hval : Real.exp (u + Real.log 2 + 1) = Real.exp u * 2 * Real.exp 1 := by
      rw [Real.exp_add, Real.exp_add, Real.exp_log (by norm_num : (0:ℝ) < 2)]
    rw [hval] at hexp
    have he : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.exp_one_gt_d9
      linarith
    nlinarith [hexp, he, he1]
  linarith [hceil, hstep, hfour]

/-- **The ladder does not overshoot the window length.** -/
theorem ladderPow_le {β γ x : ℝ} (hQ : 1 ≤ ((siftStart (γ * β) x : ℕ) : ℝ))
    (hQh : ((siftStart (γ * β) x : ℕ) : ℝ) ≤ cardLength β x) (hη : 0 < ladderEta β γ x) :
    ((siftStart (γ * β) x : ℕ) : ℝ) * (1 + ladderEta β γ x) ^ (ladderSteps β γ x)
      ≤ cardLength β x := by
  set Q : ℝ := ((siftStart (γ * β) x : ℕ) : ℝ) with hQdef
  set η : ℝ := ladderEta β γ x with hηdef
  have hQ0 : (0 : ℝ) < Q := by linarith
  have hr : (1 : ℝ) < 1 + η := by linarith
  have hlogr : (0 : ℝ) < Real.log (1 + η) := Real.log_pos hr
  have hratio : (1 : ℝ) ≤ cardLength β x / Q := (one_le_div hQ0).2 hQh
  have hlogratio : (0 : ℝ) ≤ Real.log (cardLength β x / Q) := Real.log_nonneg hratio
  have hfl : ((ladderSteps β γ x : ℕ) : ℝ) ≤ Real.log (cardLength β x / Q) / Real.log (1 + η) := by
    rw [ladderSteps, ← hQdef, ← hηdef]
    exact Nat.floor_le (div_nonneg hlogratio hlogr.le)
  have hmul : ((ladderSteps β γ x : ℕ) : ℝ) * Real.log (1 + η)
      ≤ Real.log (cardLength β x / Q) := (le_div_iff₀ hlogr).1 hfl
  have hlogpow : Real.log ((1 + η) ^ (ladderSteps β γ x))
      = ((ladderSteps β γ x : ℕ) : ℝ) * Real.log (1 + η) := Real.log_pow _ _
  have hpow0 : (0 : ℝ) < (1 + η) ^ (ladderSteps β γ x) := by positivity
  have hle : (1 + η) ^ (ladderSteps β γ x) ≤ cardLength β x / Q := by
    have h := Real.log_le_log_iff hpow0 (by positivity : (0:ℝ) < cardLength β x / Q)
    rw [← h, hlogpow]
    exact hmul
  rw [le_div_iff₀ hQ0] at hle
  linarith [hle]

/-- The ladder has at least one step. -/
theorem one_le_ladderSteps {β γ : ℝ} (hβ : 0 < β) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hγβ : γ * β < 1) :
    ∀ᶠ x : ℝ in atTop, 1 ≤ ladderSteps β γ x := by
  have hzero := tendsto_ladderEta (β := β) (γ := γ) hβ hγβ
  filter_upwards [eventually_siftStart_lt_cardLength hβ hγ0 hγ1,
    eventually_le_siftStart (mul_pos hγ0 hβ) 1,
    Filter.eventually_gt_atTop (1 : ℝ),
    Tendsto.eventually_le_const (Real.log_pos (by norm_num) : (0:ℝ) < Real.log 2) hzero] with x h2Q hQ1 hx1 hηsmall
  have hQ : (1 : ℝ) ≤ ((siftStart (γ * β) x : ℕ) : ℝ) := by exact_mod_cast hQ1
  have hQ0 : (0 : ℝ) < ((siftStart (γ * β) x : ℕ) : ℝ) := by linarith
  have hη : 0 < ladderEta β γ x := ladderEta_pos hx1
  have hr : (1 : ℝ) < 1 + ladderEta β γ x := by linarith
  have hlogr : (0 : ℝ) < Real.log (1 + ladderEta β γ x) := Real.log_pos hr
  have hlogsmall : Real.log (1 + ladderEta β γ x) ≤ Real.log 2 := by
    refine le_trans (Real.log_le_sub_one_of_pos (by linarith)) ?_
    linarith [hηsmall]
  have hratio : (2 : ℝ) ≤ cardLength β x / ((siftStart (γ * β) x : ℕ) : ℝ) :=
    (le_div_iff₀ hQ0).2 (by linarith [h2Q])
  have hlogratio : Real.log 2
      ≤ Real.log (cardLength β x / ((siftStart (γ * β) x : ℕ) : ℝ)) :=
    Real.log_le_log (by norm_num) hratio
  have hone : (1 : ℝ)
      ≤ Real.log (cardLength β x / ((siftStart (γ * β) x : ℕ) : ℝ))
        / Real.log (1 + ladderEta β γ x) := by
    rw [le_div_iff₀ hlogr]
    linarith [hlogratio, hlogsmall]
  rw [ladderSteps]
  exact Nat.le_floor (by exact_mod_cast hone)

/-- The ladder's top is below the window length and above the designated bottom. -/
theorem ladderTop_bounds {β γ x : ℝ} (hQ : 1 ≤ ((siftStart (γ * β) x : ℕ) : ℝ))
    (hQh : ((siftStart (γ * β) x : ℕ) : ℝ) ≤ cardLength β x) (hη : 0 < ladderEta β γ x) :
    siftStart (γ * β) x ≤ ladderTop β γ x
      ∧ ((ladderTop β γ x : ℕ) : ℝ) ≤ cardLength β x := by
  have hpow1 : (1 : ℝ) ≤ (1 + ladderEta β γ x) ^ (ladderSteps β γ x) :=
    one_le_pow₀ (by linarith)
  have hQ0 : (0 : ℝ) < ((siftStart (γ * β) x : ℕ) : ℝ) := by linarith
  have hge : ((siftStart (γ * β) x : ℕ) : ℝ)
      ≤ ((siftStart (γ * β) x : ℕ) : ℝ) * (1 + ladderEta β γ x) ^ (ladderSteps β γ x) := by
    nlinarith [hpow1, hQ0]
  have hle := ladderPow_le hQ hQh hη
  constructor
  · rw [ladderTop]
    exact Nat.le_floor hge
  · refine le_trans (Nat.floor_le ?_) hle
    positivity

/-- **The ladder reaches within one step of the window length.** -/
theorem ladderPow_ge {β γ x : ℝ} (hQ : 1 ≤ ((siftStart (γ * β) x : ℕ) : ℝ))
    (hQh : ((siftStart (γ * β) x : ℕ) : ℝ) ≤ cardLength β x) (hη : 0 < ladderEta β γ x) :
    cardLength β x / (1 + ladderEta β γ x)
      ≤ ((siftStart (γ * β) x : ℕ) : ℝ) * (1 + ladderEta β γ x) ^ (ladderSteps β γ x) := by
  set Q : ℝ := ((siftStart (γ * β) x : ℕ) : ℝ) with hQdef
  set η : ℝ := ladderEta β γ x with hηdef
  have hQ0 : (0 : ℝ) < Q := by linarith
  have hr : (1 : ℝ) < 1 + η := by linarith
  have hlogr : (0 : ℝ) < Real.log (1 + η) := Real.log_pos hr
  have hratio : (1 : ℝ) ≤ cardLength β x / Q := (one_le_div hQ0).2 hQh
  have hlogratio : (0 : ℝ) ≤ Real.log (cardLength β x / Q) := Real.log_nonneg hratio
  have hfl : Real.log (cardLength β x / Q) / Real.log (1 + η)
      < ((ladderSteps β γ x : ℕ) : ℝ) + 1 := by
    rw [ladderSteps, ← hQdef, ← hηdef]
    exact Nat.lt_floor_add_one _
  have hmul : Real.log (cardLength β x / Q)
      < (((ladderSteps β γ x : ℕ) : ℝ) + 1) * Real.log (1 + η) := by
    rw [div_lt_iff₀ hlogr] at hfl
    linarith [hfl]
  have hlogpow : Real.log ((1 + η) ^ (ladderSteps β γ x))
      = ((ladderSteps β γ x : ℕ) : ℝ) * Real.log (1 + η) := Real.log_pow _ _
  have hpow0 : (0 : ℝ) < (1 + η) ^ (ladderSteps β γ x) := by positivity
  have hstep : Real.log (cardLength β x / Q) - Real.log (1 + η)
      < Real.log ((1 + η) ^ (ladderSteps β γ x)) := by
    rw [hlogpow]
    nlinarith [hmul]
  have hr0 : (0 : ℝ) < 1 + η := by linarith
  have hQr0 : (0 : ℝ) < Q * (1 + η) := mul_pos hQ0 hr0
  have hlhs : Real.log (cardLength β x / Q) - Real.log (1 + η)
      = Real.log (cardLength β x / (Q * (1 + η))) := by
    rw [Real.log_div (ne_of_gt (cardLength_pos β x)) (ne_of_gt hQ0),
      Real.log_div (ne_of_gt (cardLength_pos β x)) (ne_of_gt hQr0),
      Real.log_mul (ne_of_gt hQ0) (ne_of_gt hr0)]
    ring
  rw [hlhs] at hstep
  have hle : cardLength β x / (Q * (1 + η)) ≤ (1 + η) ^ (ladderSteps β γ x) := by
    have h := Real.log_le_log_iff (div_pos (cardLength_pos β x) hQr0) hpow0
    rw [← h]
    linarith [hstep]
  rw [div_le_iff₀ hQr0] at hle
  rw [div_le_iff₀ hr0]
  nlinarith [hle, hQ0, hpow0]

/-- The constant of the harmonic-mass lower bound. -/
def ladderMassConst : ℝ :=
  meisselMertensConst - (2 * mertensFirstConst + 1 / 2) / Real.log 2 - mertensUpperConst

/-- **The harmonic mass of the ladder, from Mertens' second theorem.** -/
theorem ladderMass_ge {β γ x : ℝ} (ha : 2 ≤ ladderTop β γ x) (hb : 2 ≤ siftStart (γ * β) x) :
    Real.log (Real.log ((ladderTop β γ x : ℕ) : ℝ))
        - Real.log (Real.log ((siftStart (γ * β) x : ℕ) : ℝ)) + ladderMassConst
      ≤ mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x) := by
  have h1 := logLog_sub_le_mertensS ha
  have h2 := mertensS_le_logLog_add hb
  rw [logLog] at h1
  rw [logLog] at h2
  rw [ladderMassConst]
  linarith [h1, h2]

/-- The ladder's top is a fixed proportion of the window length. -/
theorem ladderTop_ge_quarter {β γ x : ℝ} (hQ : 1 ≤ ((siftStart (γ * β) x : ℕ) : ℝ))
    (hQh : ((siftStart (γ * β) x : ℕ) : ℝ) ≤ cardLength β x) (hη : 0 < ladderEta β γ x)
    (hη1 : ladderEta β γ x ≤ 1) (hh4 : 4 ≤ cardLength β x) :
    cardLength β x / 4 ≤ ((ladderTop β γ x : ℕ) : ℝ) := by
  have hge := ladderPow_ge hQ hQh hη
  have hfl : ((siftStart (γ * β) x : ℕ) : ℝ) * (1 + ladderEta β γ x) ^ (ladderSteps β γ x) - 1
      ≤ ((ladderTop β γ x : ℕ) : ℝ) := by
    rw [ladderTop]
    have := Nat.lt_floor_add_one
      (((siftStart (γ * β) x : ℕ) : ℝ) * (1 + ladderEta β γ x) ^ (ladderSteps β γ x))
    linarith
  have hhalf : cardLength β x / 2 ≤ cardLength β x / (1 + ladderEta β γ x) := by
    refine div_le_div_of_nonneg_left (cardLength_pos β x).le (by linarith) (by linarith)
  linarith [hge, hfl, hhalf]

/-- **The harmonic mass of the designated range, bounded below.** -/
theorem ladderMass_lower {β γ : ℝ} (hβ0 : 0 < β) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hγβ : γ * β < 1) :
    ∀ᶠ x : ℝ in atTop,
      (β - γ * β) * Real.log (Real.log x) - 2 * Real.log 2 + ladderMassConst
        ≤ mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x) := by
  have hab : (0 : ℝ) < γ * β := mul_pos hγ0 hβ0
  have hpowA : Tendsto (fun x : ℝ => (Real.log x) ^ (γ * β)) atTop atTop :=
    (tendsto_rpow_atTop hab).comp Real.tendsto_log_atTop
  have hpowB : Tendsto (fun x : ℝ => (Real.log x) ^ β) atTop atTop :=
    (tendsto_rpow_atTop hβ0).comp Real.tendsto_log_atTop
  have hzero := tendsto_ladderEta (β := β) (γ := γ) hβ0 hγβ
  filter_upwards [eventually_siftStart_lt_cardLength hβ0 hγ0 hγ1,
    eventually_le_siftStart hab 2,
    Filter.eventually_gt_atTop (1 : ℝ),
    Tendsto.eventually_le_const (by norm_num : (0:ℝ) < 1) hzero,
    hpowB.eventually_ge_atTop (max (2 * Real.log 4) (Real.log 4 + 1)),
    hpowA.eventually_ge_atTop (Real.log 2),
    log_siftStart_le hab] with x h2Q hQ2 hx1 hη1 hbigB hbigA hlogS
  have hQ1 : (1 : ℝ) ≤ ((siftStart (γ * β) x : ℕ) : ℝ) := by
    have : (1 : ℕ) ≤ siftStart (γ * β) x := by omega
    exact_mod_cast this
  have hQ2R : (2 : ℝ) ≤ ((siftStart (γ * β) x : ℕ) : ℝ) := by exact_mod_cast hQ2
  have hQh : ((siftStart (γ * β) x : ℕ) : ℝ) ≤ cardLength β x := by linarith
  have hη : 0 < ladderEta β γ x := ladderEta_pos hx1
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  have hlogh : Real.log (cardLength β x) = (Real.log x) ^ β := log_cardLength β x
  have hl4 : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
  have hbig1 : Real.log 4 + 1 ≤ (Real.log x) ^ β := le_trans (le_max_right _ _) hbigB
  have hbig2 : 2 * Real.log 4 ≤ (Real.log x) ^ β := le_trans (le_max_left _ _) hbigB
  have hh4 : (4 : ℝ) ≤ cardLength β x := by
    rw [cardLength]
    have : Real.log 4 ≤ (Real.log x) ^ β := by linarith
    calc (4 : ℝ) = Real.exp (Real.log 4) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp ((Real.log x) ^ β) := Real.exp_le_exp.2 this
  have htop := ladderTop_ge_quarter hQ1 hQh hη hη1 hh4
  have htop0 : (0 : ℝ) < ((ladderTop β γ x : ℕ) : ℝ) := by
    have : (0 : ℝ) < cardLength β x / 4 := by positivity
    linarith
  have htop2 : 2 ≤ ladderTop β γ x := by
    have hR : (2 : ℝ) ≤ ((ladderTop β γ x : ℕ) : ℝ) := by
      have hq : (2 : ℝ) ≤ cardLength β x / 4 := by
        rw [le_div_iff₀ (by norm_num : (0:ℝ) < 4), cardLength]
        have hle : Real.log 8 ≤ (Real.log x) ^ β := by
          have h84 : Real.log 8 ≤ 2 * Real.log 4 := by
            rw [show (8:ℝ) = 2^(3 : ℕ) by norm_num, show (4:ℝ) = 2^(2 : ℕ) by norm_num,
              Real.log_pow, Real.log_pow]
            have := Real.log_pos (by norm_num : (1:ℝ) < 2)
            push_cast
            linarith
          linarith
        calc (2 : ℝ) * 4 = 8 := by norm_num
          _ = Real.exp (Real.log 8) := (Real.exp_log (by norm_num)).symm
          _ ≤ Real.exp ((Real.log x) ^ β) := Real.exp_le_exp.2 hle
      linarith
    exact_mod_cast hR
  -- the two logarithms
  have hlogtop : (Real.log x) ^ β / 2 ≤ Real.log ((ladderTop β γ x : ℕ) : ℝ) := by
    have hstep : Real.log (cardLength β x / 4) ≤ Real.log ((ladderTop β γ x : ℕ) : ℝ) :=
      Real.log_le_log (by positivity) htop
    have hval : Real.log (cardLength β x / 4) = (Real.log x) ^ β - Real.log 4 := by
      rw [Real.log_div (ne_of_gt (cardLength_pos β x)) (by norm_num), hlogh]
    rw [hval] at hstep
    linarith [hstep, hbig2]
  have hlogsift : Real.log ((siftStart (γ * β) x : ℕ) : ℝ) ≤ 2 * (Real.log x) ^ (γ * β) := by
    linarith [hlogS, hbigA]
  have hlogsift0 : (0 : ℝ) < Real.log ((siftStart (γ * β) x : ℕ) : ℝ) :=
    Real.log_pos (by linarith)
  have hpowA0 : (0 : ℝ) < (Real.log x) ^ (γ * β) := Real.rpow_pos_of_pos hlogx _
  have hpowB0 : (0 : ℝ) < (Real.log x) ^ β := Real.rpow_pos_of_pos hlogx _
  -- compare the iterated logarithms
  have hL1 : Real.log ((Real.log x) ^ β / 2) ≤ Real.log (Real.log ((ladderTop β γ x : ℕ) : ℝ)) :=
    Real.log_le_log (by positivity) hlogtop
  have hL2 : Real.log (Real.log ((siftStart (γ * β) x : ℕ) : ℝ))
      ≤ Real.log (2 * (Real.log x) ^ (γ * β)) :=
    Real.log_le_log hlogsift0 hlogsift
  have hv1 : Real.log ((Real.log x) ^ β / 2) = β * Real.log (Real.log x) - Real.log 2 := by
    rw [Real.log_div (ne_of_gt hpowB0) (by norm_num), Real.log_rpow hlogx]
  have hv2 : Real.log (2 * (Real.log x) ^ (γ * β))
      = Real.log 2 + γ * β * Real.log (Real.log x) := by
    rw [Real.log_mul (by norm_num) (ne_of_gt hpowA0), Real.log_rpow hlogx]
  have hmass := ladderMass_ge (β := β) (γ := γ) (x := x) htop2 hQ2
  rw [hv1] at hL1
  rw [hv2] at hL2
  linarith [hmass, hL1, hL2]


/-- **The harmonic mass of the designated range grows.**  This is where `γ < 1` is used. -/
theorem tendsto_ladderMass {β γ : ℝ} (hβ0 : 0 < β) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hγβ : γ * β < 1) :
    Tendsto (fun x : ℝ => mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x))
      atTop atTop := by
  have hgap : (0 : ℝ) < β - γ * β := by nlinarith
  have hloglog : Tendsto (fun x : ℝ => Real.log (Real.log x)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have hmin : Tendsto (fun x : ℝ =>
      (β - γ * β) * Real.log (Real.log x) - 2 * Real.log 2 + ladderMassConst) atTop atTop := by
    have h1 : Tendsto (fun x : ℝ => (β - γ * β) * Real.log (Real.log x)) atTop atTop :=
      Filter.Tendsto.const_mul_atTop hgap hloglog
    have h2 := Filter.tendsto_atTop_add_const_right atTop
      (-(2 * Real.log 2) + ladderMassConst) h1
    exact h2.congr fun x => by ring
  exact Filter.tendsto_atTop_mono' _ (ladderMass_lower hβ0 hγ0 hγ1 hγβ) hmin

/-- **The ladder's top, eventually.** -/
theorem eventually_ladderTop_facts {β γ : ℝ} (hβ0 : 0 < β) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hγβ : γ * β < 1) :
    ∀ᶠ x : ℝ in atTop,
      2 ≤ ladderTop β γ x ∧ ((ladderTop β γ x : ℕ) : ℝ) ≤ cardLength β x
        ∧ siftStart (γ * β) x ≤ ladderTop β γ x := by
  have hab : (0 : ℝ) < γ * β := mul_pos hγ0 hβ0
  have hzero := tendsto_ladderEta (β := β) (γ := γ) hβ0 hγβ
  filter_upwards [eventually_siftStart_lt_cardLength hβ0 hγ0 hγ1,
    eventually_le_siftStart hab 1, Filter.eventually_gt_atTop (1 : ℝ),
    Tendsto.eventually_le_const (by norm_num : (0:ℝ) < 1) hzero,
    (tendsto_cardLength hβ0).eventually_ge_atTop (8 : ℝ)] with x h2Q hQ1 hx1 hη1 hh8
  have hQ : (1 : ℝ) ≤ ((siftStart (γ * β) x : ℕ) : ℝ) := by exact_mod_cast hQ1
  have hQh : ((siftStart (γ * β) x : ℕ) : ℝ) ≤ cardLength β x := by linarith
  have hη : 0 < ladderEta β γ x := ladderEta_pos hx1
  have hbounds := ladderTop_bounds hQ hQh hη
  have hquarter := ladderTop_ge_quarter hQ hQh hη hη1 (by linarith)
  refine ⟨?_, hbounds.2, hbounds.1⟩
  have hR : (2 : ℝ) ≤ ((ladderTop β γ x : ℕ) : ℝ) := by linarith [hquarter, hh8]
  exact_mod_cast hR

/-- The logarithm of `1 + η` is at least `η/2` for `η ≤ 1`. -/
theorem log_one_add_ge_half {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    η / 2 ≤ Real.log (1 + η) := by
  have hbase := log_one_add_ge (ε := η) hη.le
  have hdiv : η / 2 ≤ η / (1 + η) :=
    div_le_div_of_nonneg_left hη.le (by linarith) (by linarith)
  linarith

/-- The number of ladder steps, bounded. -/
theorem ladderSteps_le {β γ : ℝ} (hβ0 : 0 < β) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hγβ : γ * β < 1) :
    ∀ᶠ x : ℝ in atTop,
      ((ladderSteps β γ x : ℕ) : ℝ) ≤ 2 * (Real.log x) ^ β / ladderEta β γ x := by
  have hab : (0 : ℝ) < γ * β := mul_pos hγ0 hβ0
  have hzero := tendsto_ladderEta (β := β) (γ := γ) hβ0 hγβ
  filter_upwards [eventually_le_siftStart hab 1, Filter.eventually_gt_atTop (1 : ℝ),
    Tendsto.eventually_le_const (by norm_num : (0:ℝ) < 1) hzero,
    eventually_siftStart_lt_cardLength hβ0 hγ0 hγ1] with x hQ1 hx1 hη1 h2Q
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  have hη : 0 < ladderEta β γ x := ladderEta_pos hx1
  have hQ : (1 : ℝ) ≤ ((siftStart (γ * β) x : ℕ) : ℝ) := by exact_mod_cast hQ1
  have hQ0 : (0 : ℝ) < ((siftStart (γ * β) x : ℕ) : ℝ) := by linarith
  have hh0 : (0 : ℝ) < cardLength β x := cardLength_pos β x
  have hlogr : (0 : ℝ) < Real.log (1 + ladderEta β γ x) := Real.log_pos (by linarith)
  have hhalf := log_one_add_ge_half hη hη1
  have hratio : Real.log (cardLength β x / ((siftStart (γ * β) x : ℕ) : ℝ))
      ≤ (Real.log x) ^ β := by
    rw [Real.log_div (ne_of_gt hh0) (ne_of_gt hQ0), log_cardLength]
    have : (0 : ℝ) ≤ Real.log ((siftStart (γ * β) x : ℕ) : ℝ) := Real.log_nonneg hQ
    linarith
  have hfl : ((ladderSteps β γ x : ℕ) : ℝ)
      ≤ Real.log (cardLength β x / ((siftStart (γ * β) x : ℕ) : ℝ))
        / Real.log (1 + ladderEta β γ x) := by
    rw [ladderSteps]
    refine Nat.floor_le ?_
    refine div_nonneg ?_ hlogr.le
    refine Real.log_nonneg ?_
    rw [le_div_iff₀ hQ0, one_mul]
    linarith [h2Q, hQ0]
  refine hfl.trans ?_
  refine div_le_div₀ (by positivity) hratio (by linarith) hhalf |>.trans (le_of_eq ?_)
  field_simp

end

end RHTower.Sieve
