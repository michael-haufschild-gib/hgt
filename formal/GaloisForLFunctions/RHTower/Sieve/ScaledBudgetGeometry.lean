import GaloisForLFunctions.RHTower.Sieve.ScaledCardLength
import GaloisForLFunctions.RHTower.Sieve.BudgetSubstitution

/-!
# The budget geometry at a scaled window

The parameters of the spectral estimate that depend on the window length — the fibre index range,
the Gallagher cut, the height at which the Route-T saving expires and the shortest cofactor block —
at the window `scaledLength c β x = c · cardLength β x`.

Every estimate is the corpus's with the window shrunk by a constant `c ∈ (0,1]`: the cut only grows,
so the facts it must satisfy are inherited from the unscaled ones.
-/

namespace RHTower.Sieve

open Filter Topology

noncomputable section

/-- The fibre index range at a scaled window. -/
def budgetBS (c β x : ℝ) : ℕ := ⌊Real.sqrt x + scaledLength c β x⌋₊

/-- The Gallagher cut at a scaled window. -/
def gallagherCutS (c β x : ℝ) : ℝ := ((budgetBS c β x : ℕ) : ℝ) / scaledLength c β x

/-- The height at which the Route-T saving expires, at a scaled window. -/
def budgetTS (c β x : ℝ) : ℝ := ((budgetBS c β x : ℕ) : ℝ)

/-- The shortest cofactor block at a scaled window. -/
def budgetNminS (c β x : ℝ) : ℝ := ((⌊gallagherCutS c β x⌋₊ : ℕ) : ℝ)

theorem budgetBS_ge (c β x : ℝ) :
    Real.sqrt x + scaledLength c β x - 1 ≤ ((budgetBS c β x : ℕ) : ℝ) := by
  have := Nat.lt_floor_add_one (Real.sqrt x + scaledLength c β x)
  rw [budgetBS]
  linarith

/-- The quarter-exponential bounds the ratio of the outer scale to the window. -/
theorem exp_quarter_le_sqrt_div_cardLength {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∀ᶠ x : ℝ in atTop, Real.exp (Real.log x / 4) ≤ Real.sqrt x / cardLength β x := by
  have hδ : (0 : ℝ) < 1 - β := by linarith
  have hsmall := tendsto_log_rpow_neg hδ
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ),
    Tendsto.eventually_le_const (by norm_num : (0:ℝ) < 1 / 4) hsmall] with x hx1 hsm
  have hx0 : (0 : ℝ) < x := by linarith
  have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
  have hid : (Real.log x) ^ (-(1 - β)) * Real.log x = (Real.log x) ^ β := by
    rw [show -(1 - β) = β + -1 by ring, Real.rpow_add hlogx, Real.rpow_neg_one]
    field_simp
  have hquarter : (Real.log x) ^ β ≤ Real.log x / 4 := by
    have h1 : (Real.log x) ^ (-(1 - β)) * Real.log x ≤ 1 / 4 * Real.log x :=
      mul_le_mul_of_nonneg_right hsm hlogx.le
    rw [hid] at h1
    linarith
  have hsx : Real.sqrt x = Real.exp (Real.log x / 2) := by
    have hl : Real.log (Real.sqrt x) = Real.log x / 2 := Real.log_sqrt hx0.le
    rw [← hl, Real.exp_log (Real.sqrt_pos.2 hx0)]
  rw [hsx, cardLength, le_div_iff₀ (Real.exp_pos _), ← Real.exp_add]
  exact Real.exp_le_exp.2 (by linarith)

/-- **The scaled cut dominates the unscaled ratio.** -/
theorem sqrt_div_cardLength_le_gallagherCutS {c β : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hβ0 : 0 < β) :
    ∀ᶠ x : ℝ in atTop,
      Real.sqrt x / cardLength β x ≤ gallagherCutS c β x := by
  filter_upwards [(tendsto_scaledLength hc0 hβ0).eventually_ge_atTop (1 : ℝ),
    Filter.eventually_ge_atTop (0 : ℝ)] with x hh1 hx0
  have hs0 : (0 : ℝ) < scaledLength c β x := scaledLength_pos hc0 β x
  have hh0 : (0 : ℝ) < cardLength β x := cardLength_pos β x
  have hsx : (0 : ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hstep : Real.sqrt x / cardLength β x ≤ Real.sqrt x / scaledLength c β x := by
    refine div_le_div_of_nonneg_left hsx hs0 ?_
    rw [scaledLength]
    nlinarith [hh0, hc1]
  refine hstep.trans ?_
  rw [gallagherCutS, div_le_div_iff₀ hs0 hs0]
  nlinarith [budgetBS_ge c β x, hh1, hsx]

/-- **The cut is at least one.** -/
theorem one_le_gallagherCutS {c β : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∀ᶠ x : ℝ in atTop, 1 ≤ gallagherCutS c β x := by
  filter_upwards [sqrt_div_cardLength_le_gallagherCutS hc0 hc1 hβ0,
    exp_quarter_le_sqrt_div_cardLength hβ0 hβ1, Filter.eventually_ge_atTop (1 : ℝ)]
    with x hcut hexp hx1
  have h1 : (1 : ℝ) ≤ Real.exp (Real.log x / 4) := by
    refine Real.one_le_exp ?_
    have : (0 : ℝ) ≤ Real.log x := Real.log_nonneg hx1
    linarith
  linarith

/-- **The cut is below the expiry height.** -/
theorem gallagherCutS_le_budgetTS {c β : ℝ} (hc0 : 0 < c) (hβ0 : 0 < β) :
    ∀ᶠ x : ℝ in atTop, gallagherCutS c β x ≤ budgetTS c β x := by
  filter_upwards [(tendsto_scaledLength hc0 hβ0).eventually_ge_atTop (1 : ℝ)] with x hh1
  have hh0 : (0 : ℝ) < scaledLength c β x := scaledLength_pos hc0 β x
  have hB0 : (0 : ℝ) ≤ ((budgetBS c β x : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [gallagherCutS, budgetTS, div_le_iff₀ hh0]
  nlinarith [hB0, hh1]

/-- **The annulus threshold is below the scaled cut.** -/
theorem annulusStart_le_gallagherCutS {c β : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) :
    ∀ᶠ x : ℝ in atTop, annulusStart β x ≤ gallagherCutS c β x := by
  have hc : (0 : ℝ) ≤ (13 : ℝ) := by norm_num
  filter_upwards [sqrt_div_cardLength_le_gallagherCutS hc0 hc1 hβ0,
    exp_quarter_le_sqrt_div_cardLength hβ0 hβ1, eventually_rpow_log_le_exp hc] with x hcut hexp hlx
  rw [annulusStart]
  linarith

/-- **The scaled cut grows.** -/
theorem tendsto_gallagherCutS {c β : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) (hβ0 : 0 < β) (hβ1 : β < 1) :
    Tendsto (fun x : ℝ => gallagherCutS c β x) atTop atTop := by
  refine Filter.tendsto_atTop_mono' _ ?_
    (Filter.tendsto_atTop_add_const_right atTop (-1) (tendsto_gallagherCut hβ0 hβ1))
  filter_upwards [sqrt_div_cardLength_le_gallagherCutS hc0 hc1 hβ0,
    (tendsto_cardLength hβ0).eventually_ge_atTop (1 : ℝ),
    Filter.eventually_ge_atTop (0 : ℝ)] with x hcut hh1 hx0
  have hh0 : (0 : ℝ) < cardLength β x := cardLength_pos β x
  have hsx : (0 : ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hfl : ((budgetB β x : ℕ) : ℝ) ≤ Real.sqrt x + cardLength β x := by
    rw [budgetB]
    exact Nat.floor_le (by positivity)
  refine le_trans ?_ hcut
  have hle : gallagherCut β x ≤ Real.sqrt x / cardLength β x + 1 := by
    rw [gallagherCut, div_add' _ _ _ (ne_of_gt hh0), div_le_div_iff₀ hh0 hh0]
    have hid : ((⌊Real.sqrt x + cardLength β x⌋₊ : ℕ) : ℝ) = ((budgetB β x : ℕ) : ℝ) := rfl
    rw [hid]
    nlinarith [hfl, hh0]
  linarith

/-- **The shortest cofactor block grows.** -/
theorem tendsto_budgetNminS {c β : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) (hβ0 : 0 < β) (hβ1 : β < 1) :
    Tendsto (fun x : ℝ => budgetNminS c β x) atTop atTop := by
  have hG := tendsto_gallagherCutS hc0 hc1 hβ0 hβ1
  refine Filter.tendsto_atTop_mono' _ ?_
    (Filter.tendsto_atTop_add_const_right atTop (-1) hG)
  filter_upwards [hG.eventually_ge_atTop (0 : ℝ)] with x hx
  rw [budgetNminS]
  have := Nat.lt_floor_add_one (gallagherCutS c β x)
  linarith

/-- **The contour parameter at the shortest scaled block beats every power.** -/
theorem eventually_contourParam_budgetNminS {c β : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (M : ℝ) :
    ∀ᶠ x : ℝ in atTop, M ≤ ((contourParam (budgetNminS c β x) : ℕ) : ℝ) := by
  have h := tendsto_contourParam.comp (tendsto_budgetNminS hc0 hc1 hβ0 hβ1)
  exact h.eventually_ge_atTop M

/-- The shortest cofactor block of the *unscaled* ladder, at the scaled index range.  This is the
`Nmin` the master theorem's block condition wants: the ladder keeps its corpus top `cardLength β x`,
so `Nmin ≤ ⌊B₀/(Q(1+η)^j)⌋` follows from `Sieve/LadderBlockFacts.le_floor_cofactor` for every step. -/
def budgetNminL (c β x : ℝ) : ℝ :=
  ((⌊((budgetBS c β x : ℕ) : ℝ) / cardLength β x⌋₊ : ℕ) : ℝ)

theorem tendsto_sqrt_div_cardLength {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    Tendsto (fun x : ℝ => Real.sqrt x / cardLength β x) atTop atTop := by
  have hexp : Tendsto (fun x : ℝ => Real.exp (Real.log x / 4)) atTop atTop := by
    refine Real.tendsto_exp_atTop.comp ?_
    exact Real.tendsto_log_atTop.atTop_div_const (by norm_num)
  refine Filter.tendsto_atTop_mono' _ ?_ hexp
  filter_upwards [exp_quarter_le_sqrt_div_cardLength hβ0 hβ1] with x hx
  exact hx

/-- **The ladder-matched block grows.** -/
theorem tendsto_budgetNminL {c β : ℝ} (hc0 : 0 < c) (hβ0 : 0 < β) (hβ1 : β < 1) :
    Tendsto (fun x : ℝ => budgetNminL c β x) atTop atTop := by
  have hq : Tendsto (fun x : ℝ => Real.sqrt x / cardLength β x - 2) atTop atTop :=
    Filter.tendsto_atTop_add_const_right atTop (-2) (tendsto_sqrt_div_cardLength hβ0 hβ1)
  refine Filter.tendsto_atTop_mono' _ ?_ hq
  filter_upwards [(tendsto_cardLength hβ0).eventually_ge_atTop (1 : ℝ),
    Filter.eventually_ge_atTop (0 : ℝ)] with x hh1 hx0
  have hh0 : (0 : ℝ) < cardLength β x := cardLength_pos β x
  have hs0 : (0 : ℝ) < scaledLength c β x := scaledLength_pos hc0 β x
  have hsx : (0 : ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hdiv : Real.sqrt x / cardLength β x - 1
      ≤ ((budgetBS c β x : ℕ) : ℝ) / cardLength β x := by
    rw [sub_le_iff_le_add, div_add' _ _ _ (ne_of_gt hh0), div_le_div_iff₀ hh0 hh0]
    nlinarith [budgetBS_ge c β x, hh1, hs0.le]
  have hfl : ((budgetBS c β x : ℕ) : ℝ) / cardLength β x - 1 ≤ budgetNminL c β x := by
    rw [budgetNminL]
    have := Nat.lt_floor_add_one (((budgetBS c β x : ℕ) : ℝ) / cardLength β x)
    linarith
  linarith

/-- **The contour parameter at the ladder-matched block beats every power.** -/
theorem eventually_contourParam_budgetNminL {c β : ℝ} (hc0 : 0 < c) (hβ0 : 0 < β) (hβ1 : β < 1)
    (M : ℝ) :
    ∀ᶠ x : ℝ in atTop, M ≤ ((contourParam (budgetNminL c β x) : ℕ) : ℝ) := by
  have h := tendsto_contourParam.comp (tendsto_budgetNminL hc0 hβ0 hβ1)
  exact h.eventually_ge_atTop M

/-- The scaled index range is inside the unscaled one. -/
theorem budgetBS_le_budgetB {c β : ℝ} (hc1 : c ≤ 1) (x : ℝ) :
    budgetBS c β x ≤ budgetB β x := by
  rw [budgetBS, budgetB]
  refine Nat.floor_mono ?_
  have hh0 : (0 : ℝ) < cardLength β x := cardLength_pos β x
  have : scaledLength c β x ≤ cardLength β x := by
    rw [scaledLength]
    nlinarith [hh0, hc1]
  linarith

/-- **The scaled cut is below the unscaled expiry height.** -/
theorem gallagherCutS_le_budgetT {c β : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) (hβ0 : 0 < β) :
    ∀ᶠ x : ℝ in atTop, gallagherCutS c β x ≤ budgetT β x := by
  filter_upwards [(tendsto_scaledLength hc0 hβ0).eventually_ge_atTop (1 : ℝ)] with x hh1
  have hh0 : (0 : ℝ) < scaledLength c β x := scaledLength_pos hc0 β x
  have hBB : ((budgetBS c β x : ℕ) : ℝ) ≤ ((budgetB β x : ℕ) : ℝ) :=
    Nat.cast_le.2 (budgetBS_le_budgetB hc1 x)
  have hB0 : (0 : ℝ) ≤ ((budgetBS c β x : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [gallagherCutS, budgetT, div_le_iff₀ hh0]
  nlinarith [hBB, hB0, hh1]

/-- **The ladder-matched block exceeds `x^{1/5}`.** -/
theorem eventually_budgetNminL_ge_exp {c β : ℝ} (hc0 : 0 < c) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∀ᶠ x : ℝ in atTop, Real.exp (Real.log x / 5) ≤ budgetNminL c β x := by
  filter_upwards [exp_quarter_le_sqrt_div_cardLength hβ0 hβ1,
    (tendsto_cardLength hβ0).eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (20 * Real.log 3),
    Filter.eventually_ge_atTop (1 : ℝ)] with x hexp hh1 hlog20 hx1
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hh0 : (0 : ℝ) < cardLength β x := cardLength_pos β x
  have hs0 : (0 : ℝ) < scaledLength c β x := scaledLength_pos hc0 β x
  have hsx : (0 : ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hdiv : Real.sqrt x / cardLength β x - 1
      ≤ ((budgetBS c β x : ℕ) : ℝ) / cardLength β x := by
    rw [sub_le_iff_le_add, div_add' _ _ _ (ne_of_gt hh0), div_le_div_iff₀ hh0 hh0]
    nlinarith [budgetBS_ge c β x, hh1, hs0.le]
  have hfl : ((budgetBS c β x : ℕ) : ℝ) / cardLength β x - 1 ≤ budgetNminL c β x := by
    rw [budgetNminL]
    have := Nat.lt_floor_add_one (((budgetBS c β x : ℕ) : ℝ) / cardLength β x)
    linarith
  have hlogx : (0 : ℝ) ≤ Real.log x := Real.log_nonneg hx1
  have h3 : (3 : ℝ) ≤ Real.exp (Real.log x / 20) := by
    have hle : Real.log 3 ≤ Real.log x / 20 := by linarith
    calc (3 : ℝ) = Real.exp (Real.log 3) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp (Real.log x / 20) := Real.exp_le_exp.2 hle
  have hsplit : Real.exp (Real.log x / 4)
      = Real.exp (Real.log x / 5) * Real.exp (Real.log x / 20) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hone : (1 : ℝ) ≤ Real.exp (Real.log x / 5) := Real.one_le_exp (by linarith)
  have hstep : Real.exp (Real.log x / 5) ≤ Real.exp (Real.log x / 4) - 2 := by
    rw [hsplit]
    nlinarith [h3, hone]
  linarith

/-- **The annulus threshold is admissible at the ladder-matched block.** -/
theorem eventually_annulus_admissibleL {c β : ℝ} (hc0 : 0 < c) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∀ᶠ x : ℝ in atTop,
      5 + 8 * Real.pi * annulusStart β x ≤ ((contourParam (budgetNminL c β x) : ℕ) : ℝ) := by
  have hk : (0 : ℝ) < (1 : ℝ) / 5 ^ ((1 : ℝ) / 10) := by
    have : (0 : ℝ) < (5 : ℝ) ^ ((1 : ℝ) / 10) := Real.rpow_pos_of_pos (by norm_num) _
    positivity
  have hgrow := tendsto_exp_rpow_div_rpow (a := (1 : ℝ) / 10)
    (k := (1 : ℝ) / 5 ^ ((1 : ℝ) / 10)) (c := (13 : ℝ)) (by norm_num) hk
  have hcomp := hgrow.comp Real.tendsto_log_atTop
  filter_upwards [hcomp.eventually_ge_atTop (8 * Real.pi + 5),
    Filter.eventually_ge_atTop (Real.exp 1), Filter.eventually_gt_atTop (1 : ℝ),
    (tendsto_budgetNminL hc0 hβ0 hβ1).eventually_ge_atTop (1 : ℝ),
    eventually_budgetNminL_ge_exp hc0 hβ0 hβ1] with x hx hxe hx1 hN1 hGexp
  have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
  have hlog1 : (1 : ℝ) ≤ Real.log x := by
    have := Real.log_le_log (Real.exp_pos 1) hxe
    rwa [Real.log_exp] at this
  have hpow0 : (0 : ℝ) < (Real.log x) ^ (13 : ℝ) := Real.rpow_pos_of_pos hlogx 13
  have hNlog : Real.log x / 5 ≤ Real.log (budgetNminL c β x) := by
    have h2 := Real.log_le_log (Real.exp_pos _) hGexp
    rwa [Real.log_exp] at h2
  have hcp : Real.exp ((Real.log (budgetNminL c β x)) ^ ((1 : ℝ) / 10))
      ≤ ((contourParam (budgetNminL c β x) : ℕ) : ℝ) := contourParam_ge
  have hmono : ((1 : ℝ) / 5 ^ ((1 : ℝ) / 10)) * (Real.log x) ^ ((1 : ℝ) / 10)
      ≤ (Real.log (budgetNminL c β x)) ^ ((1 : ℝ) / 10) := by
    have hdiv : (Real.log x / 5) ^ ((1 : ℝ) / 10)
        = (Real.log x) ^ ((1 : ℝ) / 10) / (5 : ℝ) ^ ((1 : ℝ) / 10) := by
      rw [Real.div_rpow hlogx.le (by norm_num)]
    have hstep : (Real.log x / 5) ^ ((1 : ℝ) / 10)
        ≤ (Real.log (budgetNminL c β x)) ^ ((1 : ℝ) / 10) :=
      Real.rpow_le_rpow (by positivity) hNlog (by norm_num)
    rw [hdiv] at hstep
    calc ((1 : ℝ) / 5 ^ ((1 : ℝ) / 10)) * (Real.log x) ^ ((1 : ℝ) / 10)
        = (Real.log x) ^ ((1 : ℝ) / 10) / (5 : ℝ) ^ ((1 : ℝ) / 10) := by ring
      _ ≤ (Real.log (budgetNminL c β x)) ^ ((1 : ℝ) / 10) := hstep
  have hchain : Real.exp (((1 : ℝ) / 5 ^ ((1 : ℝ) / 10)) * (Real.log x) ^ ((1 : ℝ) / 10))
      ≤ ((contourParam (budgetNminL c β x) : ℕ) : ℝ) :=
    le_trans (Real.exp_le_exp.2 hmono) hcp
  have hxx : (8 * Real.pi + 5)
      ≤ Real.exp (((1 : ℝ) / 5 ^ ((1 : ℝ) / 10)) * (Real.log x) ^ ((1 : ℝ) / 10))
        / (Real.log x) ^ (13 : ℝ) := hx
  rw [le_div_iff₀ hpow0] at hxx
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hp1 : (1 : ℝ) ≤ (Real.log x) ^ (13 : ℝ) := Real.one_le_rpow hlog1 (by norm_num)
  rw [annulusStart]
  nlinarith [hxx, hchain, hp1, hpi, hpow0]

end

end RHTower.Sieve
