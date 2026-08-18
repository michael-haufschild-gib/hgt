import GaloisForLFunctions.RHTower.Sieve.OmegaBudgetMaster
import GaloisForLFunctions.RHTower.Sieve.LadderBlockFacts
import GaloisForLFunctions.RHTower.Sieve.NonSpectralBudget

/-!
# The parameters substituted into the budget

The parameters of the short-interval argument are fixed here as functions of the scale, and every
side condition of the master budget theorem is verified for them.
-/

namespace RHTower.Sieve

open Filter Topology Finset

noncomputable section

/-- The length of the fibre index range. -/
def budgetB (β x : ℝ) : ℕ := ⌊Real.sqrt x + cardLength β x⌋₊

/-- The height at which the Route-T saving expires. -/
def budgetT (β x : ℝ) : ℝ := ((budgetB β x : ℕ) : ℝ)

/-- The shortest cofactor block. -/
def budgetNmin (β x : ℝ) : ℝ := ((⌊gallagherCut β x⌋₊ : ℕ) : ℝ)

theorem budgetB_eq (β x : ℝ) : budgetB β x = ⌊Real.sqrt x + cardLength β x⌋₊ := rfl

/-- The Gallagher cut is at least one once the window is below the outer scale. -/
theorem one_le_gallagherCut {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∀ᶠ x : ℝ in atTop, 1 ≤ gallagherCut β x := by
  filter_upwards [cardLength_le_sqrt hβ0 hβ1, Filter.eventually_gt_atTop (1 : ℝ),
    (tendsto_cardLength hβ0).eventually_ge_atTop (1 : ℝ)] with x hhs hx1 hh1
  have hh0 : (0 : ℝ) < cardLength β x := cardLength_pos β x
  have hfl : Real.sqrt x + cardLength β x - 1 ≤ ((budgetB β x : ℕ) : ℝ) := by
    rw [budgetB]
    have := Nat.lt_floor_add_one (Real.sqrt x + cardLength β x)
    linarith
  rw [gallagherCut, le_div_iff₀ hh0, one_mul]
  have : ((⌊Real.sqrt x + cardLength β x⌋₊ : ℕ) : ℝ) = ((budgetB β x : ℕ) : ℝ) := rfl
  rw [this]
  linarith [hfl, hhs]

/-- The Gallagher cut is below the height at which the Route-T saving expires. -/
theorem gallagherCut_le_budgetT {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∀ᶠ x : ℝ in atTop, gallagherCut β x ≤ budgetT β x := by
  filter_upwards [(tendsto_cardLength hβ0).eventually_ge_atTop (1 : ℝ)] with x hh1
  have hh0 : (0 : ℝ) < cardLength β x := cardLength_pos β x
  have hB0 : (0 : ℝ) ≤ ((budgetB β x : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [gallagherCut, budgetT, div_le_iff₀ hh0]
  have : ((⌊Real.sqrt x + cardLength β x⌋₊ : ℕ) : ℝ) = ((budgetB β x : ℕ) : ℝ) := rfl
  rw [this]
  nlinarith [hB0, hh1]

/-- The Gallagher cut grows. -/
theorem tendsto_gallagherCut {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    Tendsto (fun x : ℝ => gallagherCut β x) atTop atTop := by
  have hmin : Tendsto (fun x : ℝ => Real.sqrt x / cardLength β x - 1) atTop atTop := by
    have hquot : Tendsto (fun x : ℝ => Real.sqrt x / cardLength β x) atTop atTop := by
      have hexp : Tendsto (fun x : ℝ => Real.exp (Real.log x / 2 - (Real.log x) ^ β))
          atTop atTop := by
        refine Real.tendsto_exp_atTop.comp ?_
        have hδ : (0 : ℝ) < 1 - β := by linarith
        have hsmall := tendsto_log_rpow_neg hδ
        have hhalf : Tendsto (fun x : ℝ => Real.log x / 4) atTop atTop :=
          Real.tendsto_log_atTop.atTop_div_const (by norm_num)
        refine Filter.tendsto_atTop_mono' _ ?_ hhalf
        filter_upwards [Filter.eventually_gt_atTop (1 : ℝ),
          Tendsto.eventually_le_const (by norm_num : (0:ℝ) < 1 / 4) hsmall] with x hx1 hsm
        have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
        have hid : (Real.log x) ^ (-(1 - β)) * Real.log x = (Real.log x) ^ β := by
          rw [show -(1 - β) = β + -1 by ring, Real.rpow_add hlogx, Real.rpow_neg_one]
          field_simp
        have h1 : (Real.log x) ^ (-(1 - β)) * Real.log x ≤ 1 / 4 * Real.log x :=
          mul_le_mul_of_nonneg_right hsm hlogx.le
        rw [hid] at h1
        linarith
      refine hexp.congr' ?_
      filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx1
      have hx0 : (0 : ℝ) < x := by linarith
      have hsx : Real.sqrt x = Real.exp (Real.log x / 2) := by
        have hl : Real.log (Real.sqrt x) = Real.log x / 2 := Real.log_sqrt hx0.le
        rw [← hl, Real.exp_log (Real.sqrt_pos.2 hx0)]
      rw [hsx, cardLength, ← Real.exp_sub]
    exact Filter.tendsto_atTop_add_const_right _ (-1) hquot
  refine Filter.tendsto_atTop_mono' _ ?_ hmin
  filter_upwards [(tendsto_cardLength hβ0).eventually_ge_atTop (1 : ℝ)] with x hh1
  have hh0 : (0 : ℝ) < cardLength β x := cardLength_pos β x
  have hfl : Real.sqrt x + cardLength β x - 1 ≤ ((budgetB β x : ℕ) : ℝ) := by
    rw [budgetB]
    have := Nat.lt_floor_add_one (Real.sqrt x + cardLength β x)
    linarith
  rw [gallagherCut]
  have hid : ((⌊Real.sqrt x + cardLength β x⌋₊ : ℕ) : ℝ) = ((budgetB β x : ℕ) : ℝ) := rfl
  rw [hid, le_div_iff₀ hh0]
  have hsub : (Real.sqrt x / cardLength β x - 1) * cardLength β x
      = Real.sqrt x - cardLength β x := by
    field_simp
  rw [hsub]
  linarith [hfl, hh1]

/-- A quarter-exponential beats every real power. -/
theorem tendsto_exp_quarter_div_rpow (c : ℝ) :
    Tendsto (fun u : ℝ => Real.exp (u / 4) / u ^ c) atTop atTop := by
  have h1 : Tendsto (fun v : ℝ => Real.exp v / v ^ c) atTop atTop := tendsto_exp_div_rpow_atTop c
  have h2 : Tendsto (fun u : ℝ => u / 4) atTop atTop :=
    tendsto_id.atTop_div_const (by norm_num)
  have hc : (0 : ℝ) < ((1 : ℝ) / 4) ^ c := Real.rpow_pos_of_pos (by norm_num) c
  have h3 := (h1.comp h2).atTop_mul_const hc
  refine h3.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with u hu
  have h4 : (u / 4) ^ c = u ^ c * ((1 : ℝ) / 4) ^ c := by
    rw [show u / 4 = u * (1 / 4) by ring, Real.mul_rpow hu.le (by norm_num)]
  have hup : (0 : ℝ) < u ^ c := Real.rpow_pos_of_pos hu c
  simp only [Function.comp_apply]
  rw [h4]
  field_simp

/-- Every power of the logarithm is eventually below the quarter-exponential. -/
theorem eventually_rpow_log_le_exp {c : ℝ} (hc : 0 ≤ c) :
    ∀ᶠ x : ℝ in atTop, (Real.log x) ^ c + 1 ≤ Real.exp (Real.log x / 4) := by
  have h := (tendsto_exp_quarter_div_rpow c).comp Real.tendsto_log_atTop
  filter_upwards [h.eventually_ge_atTop (2 : ℝ), Filter.eventually_ge_atTop (Real.exp 1),
    Filter.eventually_gt_atTop (1 : ℝ)] with x hx hxe hx1
  have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
  have hlog1 : (1 : ℝ) ≤ Real.log x := by
    have := Real.log_le_log (Real.exp_pos 1) hxe
    rwa [Real.log_exp] at this
  have hpow1 : (1 : ℝ) ≤ (Real.log x) ^ c := Real.one_le_rpow hlog1 hc
  have hpow0 : (0 : ℝ) < (Real.log x) ^ c := by linarith
  have hx' : (2 : ℝ) ≤ Real.exp (Real.log x / 4) / (Real.log x) ^ c := hx
  rw [le_div_iff₀ hpow0] at hx'
  linarith

/-- The annulus threshold is below the Gallagher cut. -/
theorem annulusStart_le_gallagherCut {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∀ᶠ x : ℝ in atTop, annulusStart β x ≤ gallagherCut β x := by
  have hc : (0 : ℝ) ≤ (13 : ℝ) := by norm_num
  have hδ : (0 : ℝ) < 1 - β := by linarith
  have hsmall := tendsto_log_rpow_neg hδ
  filter_upwards [eventually_rpow_log_le_exp hc,
    (tendsto_cardLength hβ0).eventually_ge_atTop (1 : ℝ),
    Filter.eventually_gt_atTop (1 : ℝ),
    Tendsto.eventually_le_const (by norm_num : (0:ℝ) < 1 / 4) hsmall] with x hexp hh1 hx1 hsm
  have hx0 : (0 : ℝ) < x := by linarith
  have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
  have hh0 : (0 : ℝ) < cardLength β x := cardLength_pos β x
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
  have hratio : Real.exp (Real.log x / 4) ≤ Real.sqrt x / cardLength β x := by
    rw [hsx, cardLength, le_div_iff₀ (Real.exp_pos _), ← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  have hfl : Real.sqrt x + cardLength β x - 1 ≤ ((budgetB β x : ℕ) : ℝ) := by
    rw [budgetB]
    have := Nat.lt_floor_add_one (Real.sqrt x + cardLength β x)
    linarith
  rw [annulusStart, gallagherCut]
  have hidB : ((⌊Real.sqrt x + cardLength β x⌋₊ : ℕ) : ℝ) = ((budgetB β x : ℕ) : ℝ) := rfl
  rw [hidB, le_div_iff₀ hh0]
  have hstep : ((Real.log x) ^ (13 : ℝ) + 1) * cardLength β x
      ≤ Real.exp (Real.log x / 4) * cardLength β x :=
    mul_le_mul_of_nonneg_right hexp hh0.le
  have hstep2 : Real.exp (Real.log x / 4) * cardLength β x ≤ Real.sqrt x := by
    rw [← le_div_iff₀ hh0]
    exact hratio
  nlinarith [hstep, hstep2, hfl, hh1]

/-- A stretched exponential beats every power. -/
theorem tendsto_rpow_sub_log {a c : ℝ} (ha : 0 < a) :
    Tendsto (fun t : ℝ => t ^ a - c * Real.log t) atTop atTop := by
  have hsmall := tendsto_log_div_rpow ha
  have hbig : Tendsto (fun t : ℝ => t ^ a / 2) atTop atTop :=
    (tendsto_rpow_atTop ha).atTop_div_const (by norm_num)
  refine Filter.tendsto_atTop_mono' _ ?_ hbig
  filter_upwards [Tendsto.eventually_le_const
      (by positivity : (0 : ℝ) < 1 / (2 * (|c| + 1))) hsmall,
    Filter.eventually_ge_atTop (1 : ℝ)] with t hsm ht1
  have ht0 : (0 : ℝ) < t := by linarith
  have hlog : (0 : ℝ) ≤ Real.log t := Real.log_nonneg ht1
  have hpow : (0 : ℝ) < t ^ a := Real.rpow_pos_of_pos ht0 a
  rw [div_le_iff₀ hpow] at hsm
  have hc : c * Real.log t ≤ |c| * Real.log t :=
    mul_le_mul_of_nonneg_right (le_abs_self c) hlog
  have hkey : |c| * Real.log t ≤ t ^ a / 2 := by
    have h1 : |c| * Real.log t ≤ |c| * (1 / (2 * (|c| + 1)) * t ^ a) :=
      mul_le_mul_of_nonneg_left hsm (abs_nonneg c)
    have h2 : |c| * (1 / (2 * (|c| + 1)) * t ^ a) ≤ t ^ a / 2 := by
      have hden : (0 : ℝ) < 2 * (|c| + 1) := by positivity
      have hid : |c| * (1 / (2 * (|c| + 1)) * t ^ a)
          = (|c| / (|c| + 1)) * (t ^ a / 2) := by
        field_simp
      rw [hid]
      have hfrac : |c| / (|c| + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith
      nlinarith [hfrac, hpow]
    linarith
  linarith

/-- The contour parameter at the shortest cofactor block beats every power of the logarithm. -/
theorem eventually_contourParam_budgetNmin {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (M : ℝ) :
    ∀ᶠ x : ℝ in atTop, M ≤ ((contourParam (budgetNmin β x) : ℕ) : ℝ) := by
  have hNtop : Tendsto (fun x : ℝ => budgetNmin β x) atTop atTop := by
    have hG := tendsto_gallagherCut hβ0 hβ1
    refine Filter.tendsto_atTop_mono' _ ?_ (Filter.tendsto_atTop_add_const_right atTop (-1) hG)
    filter_upwards [hG.eventually_ge_atTop (0 : ℝ)] with x hx
    rw [budgetNmin]
    have := Nat.lt_floor_add_one (gallagherCut β x)
    linarith
  have h := tendsto_contourParam.comp hNtop
  exact h.eventually_ge_atTop M

/-- The shortest cofactor block grows. -/
theorem tendsto_budgetNmin {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    Tendsto (fun x : ℝ => budgetNmin β x) atTop atTop := by
  have hG := tendsto_gallagherCut hβ0 hβ1
  refine Filter.tendsto_atTop_mono' _ ?_
    (Filter.tendsto_atTop_add_const_right atTop (-1) hG)
  filter_upwards [hG.eventually_ge_atTop (0 : ℝ)] with x hx
  rw [budgetNmin]
  have := Nat.lt_floor_add_one (gallagherCut β x)
  linarith

/-- A scaled stretched exponential beats every power. -/
theorem tendsto_exp_rpow_div_rpow {a k c : ℝ} (ha : 0 < a) (hk : 0 < k) :
    Tendsto (fun t : ℝ => Real.exp (k * t ^ a) / t ^ c) atTop atTop := by
  have hbig : Tendsto (fun t : ℝ => k * (t ^ a - (c / k) * Real.log t)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hk (tendsto_rpow_sub_log (c := c / k) ha)
  have hexp : Tendsto (fun t : ℝ => Real.exp (k * (t ^ a - (c / k) * Real.log t)))
      atTop atTop := Real.tendsto_exp_atTop.comp hbig
  refine hexp.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with t ht1
  have ht0 : (0 : ℝ) < t := by linarith
  have hpow : (0 : ℝ) < t ^ c := Real.rpow_pos_of_pos ht0 c
  have hid : t ^ c = Real.exp (c * Real.log t) := by
    rw [Real.rpow_def_of_pos ht0]
    ring_nf
  rw [hid, ← Real.exp_sub]
  congr 1
  field_simp

/-- The shortest cofactor block is at least a fixed power of the scale. -/
theorem eventually_gallagherCut_ge_exp {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∀ᶠ x : ℝ in atTop, Real.exp (Real.log x / 5) ≤ budgetNmin β x := by
  have hδ : (0 : ℝ) < 1 - β := by linarith
  have hsmall := tendsto_log_rpow_neg hδ
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ),
    (tendsto_cardLength hβ0).eventually_ge_atTop (1 : ℝ),
    Tendsto.eventually_le_const (by norm_num : (0:ℝ) < 1 / 4) hsmall,
    Real.tendsto_log_atTop.eventually_ge_atTop (20 * Real.log 2)] with x hx1 hh1 hsm hlog20
  have hx0 : (0 : ℝ) < x := by linarith
  have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
  have hh0 : (0 : ℝ) < cardLength β x := cardLength_pos β x
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
  have hratio : Real.exp (Real.log x / 4) ≤ Real.sqrt x / cardLength β x := by
    rw [hsx, cardLength, le_div_iff₀ (Real.exp_pos _), ← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  have hfl : Real.sqrt x + cardLength β x - 1 ≤ ((budgetB β x : ℕ) : ℝ) := by
    rw [budgetB]
    have := Nat.lt_floor_add_one (Real.sqrt x + cardLength β x)
    linarith
  have hGge : Real.sqrt x / cardLength β x ≤ gallagherCut β x := by
    rw [gallagherCut]
    have hid2 : ((⌊Real.sqrt x + cardLength β x⌋₊ : ℕ) : ℝ) = ((budgetB β x : ℕ) : ℝ) := rfl
    rw [hid2]
    rw [div_le_div_iff₀ hh0 hh0]
    nlinarith [hfl, hh1, hh0]
  have hNge : gallagherCut β x - 1 ≤ budgetNmin β x := by
    rw [budgetNmin]
    have := Nat.lt_floor_add_one (gallagherCut β x)
    linarith
  have hstep : Real.exp (Real.log x / 5) ≤ Real.exp (Real.log x / 4) - 1 := by
    have h2 : (2 : ℝ) ≤ Real.exp (Real.log x / 20) := by
      have : Real.log 2 ≤ Real.log x / 20 := by linarith
      calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
        _ ≤ Real.exp (Real.log x / 20) := Real.exp_le_exp.2 this
    have hsplit : Real.exp (Real.log x / 4)
        = Real.exp (Real.log x / 5) * Real.exp (Real.log x / 20) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hpos : (1 : ℝ) ≤ Real.exp (Real.log x / 5) :=
      Real.one_le_exp (by linarith)
    rw [hsplit]
    nlinarith [h2, hpos]
  linarith [hstep, hratio, hGge, hNge]

/-- **The annulus threshold is admissible for the Möbius contour bound.** -/
theorem eventually_annulus_admissible {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∀ᶠ x : ℝ in atTop,
      5 + 8 * Real.pi * annulusStart β x ≤ ((contourParam (budgetNmin β x) : ℕ) : ℝ) := by
  have hk : (0 : ℝ) < (1 : ℝ) / 5 ^ ((1 : ℝ) / 10) := by
    have : (0 : ℝ) < (5 : ℝ) ^ ((1 : ℝ) / 10) := Real.rpow_pos_of_pos (by norm_num) _
    positivity
  have hgrow := tendsto_exp_rpow_div_rpow (a := (1 : ℝ) / 10)
    (k := (1 : ℝ) / 5 ^ ((1 : ℝ) / 10)) (c := (13 : ℝ)) (by norm_num) hk
  have hcomp := hgrow.comp Real.tendsto_log_atTop
  have hNbig := (tendsto_budgetNmin hβ0 hβ1)
  filter_upwards [hcomp.eventually_ge_atTop (8 * Real.pi + 5),
    Filter.eventually_ge_atTop (Real.exp 1), Filter.eventually_gt_atTop (1 : ℝ),
    hNbig.eventually_ge_atTop (1 : ℝ),
    eventually_gallagherCut_ge_exp hβ0 hβ1] with x hx hxe hx1 hN1 hGexp
  have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
  have hlog1 : (1 : ℝ) ≤ Real.log x := by
    have := Real.log_le_log (Real.exp_pos 1) hxe
    rwa [Real.log_exp] at this
  have hpow0 : (0 : ℝ) < (Real.log x) ^ (13 : ℝ) :=
    Real.rpow_pos_of_pos hlogx 13
  -- the shortest block is at least `x^{1/5}`
  have hNlog : Real.log x / 5 ≤ Real.log (budgetNmin β x) := by
    have h1 : Real.exp (Real.log x / 5) ≤ budgetNmin β x := hGexp
    have h2 := Real.log_le_log (Real.exp_pos _) h1
    rwa [Real.log_exp] at h2
  have hcp : Real.exp ((Real.log (budgetNmin β x)) ^ ((1 : ℝ) / 10))
      ≤ ((contourParam (budgetNmin β x) : ℕ) : ℝ) := contourParam_ge
  have hmono : ((1 : ℝ) / 5 ^ ((1 : ℝ) / 10)) * (Real.log x) ^ ((1 : ℝ) / 10)
      ≤ (Real.log (budgetNmin β x)) ^ ((1 : ℝ) / 10) := by
    have hdiv : (Real.log x / 5) ^ ((1 : ℝ) / 10)
        = (Real.log x) ^ ((1 : ℝ) / 10) / (5 : ℝ) ^ ((1 : ℝ) / 10) := by
      rw [Real.div_rpow hlogx.le (by norm_num)]
    have hstep : (Real.log x / 5) ^ ((1 : ℝ) / 10)
        ≤ (Real.log (budgetNmin β x)) ^ ((1 : ℝ) / 10) :=
      Real.rpow_le_rpow (by positivity) hNlog (by norm_num)
    rw [hdiv] at hstep
    calc ((1 : ℝ) / 5 ^ ((1 : ℝ) / 10)) * (Real.log x) ^ ((1 : ℝ) / 10)
        = (Real.log x) ^ ((1 : ℝ) / 10) / (5 : ℝ) ^ ((1 : ℝ) / 10) := by ring
      _ ≤ (Real.log (budgetNmin β x)) ^ ((1 : ℝ) / 10) := hstep
  have hchain : Real.exp (((1 : ℝ) / 5 ^ ((1 : ℝ) / 10)) * (Real.log x) ^ ((1 : ℝ) / 10))
      ≤ ((contourParam (budgetNmin β x) : ℕ) : ℝ) :=
    le_trans (Real.exp_le_exp.2 hmono) hcp
  have hxx : (8 * Real.pi + 5)
      ≤ Real.exp (((1 : ℝ) / 5 ^ ((1 : ℝ) / 10)) * (Real.log x) ^ ((1 : ℝ) / 10))
        / (Real.log x) ^ (13 : ℝ) := hx
  rw [le_div_iff₀ hpow0] at hxx
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hp1 : (1 : ℝ) ≤ (Real.log x) ^ (13 : ℝ) :=
    Real.one_le_rpow hlog1 (by norm_num)
  rw [annulusStart]
  nlinarith [hxx, hchain, hp1, hpi, hpow0]

/-- The width surrogate at the top of the annulus. -/
def budgetMu (A delta β x : ℝ) : ℝ :=
  min delta (routeTWidthPolylogLower A (2 * Real.pi * budgetT β x)) / 2

/-- The height cost at the top of the annulus. -/
def budgetHmaj (A β x : ℝ) : ℝ :=
  1 / (2 * Real.pi * annulusStart β x)
    + Real.log (3 * (2 * Real.pi * budgetT β x) / 2)
      / routeTWidthPolylogLower A (2 * Real.pi * budgetT β x)

/-- The annulus constant at the chosen parameters. -/
def budgetRho (A delta Ctot β γ x : ℝ) : ℝ :=
  ladderRho Ctot (ladderWidth β x) ((Real.log x) ^ β) (budgetHmaj A β x)
    (budgetMu A delta β x) (Real.log ((siftStart (γ * β) x : ℕ) : ℝ)) (annulusStart β x)
    ((siftStart (γ * β) x : ℕ) : ℝ) ((siftStart (γ * β) x : ℕ) : ℝ) (ladderEta β γ x)

/-- The disc constant at the chosen parameters. -/
def budgetS (β x : ℝ) : ℝ := relMoebiusSharp (budgetNmin β x)

/-- **Every side condition of the master budget theorem holds for the chosen parameters.** -/
theorem exists_eventually_omegaBudget_le {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ0 : 0 < γ)
    (hγ1 : γ < 1) (hγβ : γ * β < 1) :
    ∃ (A delta Ctot : ℝ), 0 < delta ∧ 0 < Ctot ∧
      ∀ᶠ x : ℝ in atTop,
        omegaBudget x (cardLength β x) (siftStart (γ * β) x) (ladderTop β γ x)
          ≤ 16 * Real.sqrt x
              * (2 * (fibreWidth x (cardLength β x)) ^ 2
                  * (ladderAffineSlope (ladderSteps β γ x) (budgetB β x)
                        ((siftStart (γ * β) x : ℕ) : ℝ) (ladderEta β γ x)
                        (budgetRho A delta Ctot β γ x) * gallagherCut β x
                    + ladderAffineConst (siftStart (γ * β) x) (ladderTop β γ x)
                        (ladderSteps β γ x) (budgetB β x) ((siftStart (γ * β) x : ℕ) : ℝ)
                        (ladderEta β γ x) (budgetRho A delta Ctot β γ x) (budgetS β x)
                        (annulusStart β x))
                + (4 * (ladderAffineSlope (ladderSteps β γ x) (budgetB β x)
                          ((siftStart (γ * β) x : ℕ) : ℝ) (ladderEta β γ x)
                          (budgetRho A delta Ctot β γ x)
                        + 5 * Real.pi / 2
                          * (∑ n ∈ Finset.Icc 1 (budgetB β x),
                              ‖omegaCoeff (primesRange (siftStart (γ * β) x)
                                (ladderTop β γ x)) n‖ ^ 2)
                        + 5 * Real.exp 1 / 2 * ((budgetB β x : ℕ) : ℝ)
                          * (∑ n ∈ Finset.Icc 1 (budgetB β x),
                              ‖omegaCoeff (primesRange (siftStart (γ * β) x)
                                (ladderTop β γ x)) n‖ ^ 2) / budgetT β x)
                      / (Real.pi ^ 2 * gallagherCut β x)
                    + 4 * ladderAffineConst (siftStart (γ * β) x) (ladderTop β γ x)
                          (ladderSteps β γ x) (budgetB β x) ((siftStart (γ * β) x : ℕ) : ℝ)
                          (ladderEta β γ x) (budgetRho A delta Ctot β γ x) (budgetS β x)
                          (annulusStart β x)
                      / (3 * Real.pi ^ 2 * (gallagherCut β x) ^ 2)))
            + 204 * (((primesRange (siftStart (γ * β) x) (ladderTop β γ x)).card : ℝ) + 1) ^ 2
                * (Real.sqrt x + 1)
            + 2 * (cardLength β x + 1) * (2 * cardLength β x + 1)
                * (4 * (Real.sqrt x / 2 + cardLength β x + 1) * mertensS (ladderTop β γ x)
                  + 4 * ((Nat.primesLE (ladderTop β γ x)).card : ℝ)
                  + 8 * ((Nat.primesLE (ladderTop β γ x)).card : ℝ) ^ 2) := by
  obtain ⟨A, delta, Ctot, τ₀, K₀, N₁, hdelta, hCtot, hτ₀, hmaster⟩ := exists_omegaBudget_master
  refine ⟨A, delta, Ctot, hdelta, hCtot, ?_⟩
  have hab : (0 : ℝ) < γ * β := mul_pos hγ0 hβ0
  have hzero := tendsto_ladderEta (β := β) (γ := γ) hβ0 hγβ
  have hpolylog : Tendsto (fun x : ℝ => 2 * Real.pi * annulusStart β x) atTop atTop := by
    have h : Tendsto (fun x : ℝ => annulusStart β x) atTop atTop :=
      (tendsto_rpow_atTop (by norm_num : (0:ℝ) < (13:ℝ))).comp Real.tendsto_log_atTop
    exact Filter.Tendsto.const_mul_atTop (by positivity) h
  filter_upwards [one_le_gallagherCut hβ0 hβ1, gallagherCut_le_budgetT hβ0 hβ1,
    annulusStart_le_gallagherCut hβ0 hβ1,
    (tendsto_cardLength hβ0).eventually_ge_atTop (1 : ℝ),
    cardLength_le_sqrt hβ0 hβ1, Filter.eventually_gt_atTop (1 : ℝ),
    eventually_le_siftStart hab 2, one_le_ladderWidth hβ0,
    one_le_ladderSteps hβ0 hγ0 hγ1 hγβ,
    eventually_siftStart_lt_cardLength hβ0 hγ0 hγ1,
    Tendsto.eventually_le_const (by norm_num : (0:ℝ) < 1) hzero,
    hpolylog.eventually_ge_atTop (max τ₀ (16 * Real.pi / 3)),
    eventually_contourParam_budgetNmin hβ0 hβ1 (K₀ : ℝ),
    (tendsto_budgetNmin hβ0 hβ1).eventually_ge_atTop N₁,
    eventually_annulus_admissible hβ0 hβ1]
    with x hG1 hGT hwG hh1 hhs hx1 hQ2 hD1 hL1 h2Q hη1 hw₀τ hCP hN₁ hadm
  have hx0 : (0 : ℝ) < x := by linarith
  have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hh0 : (0 : ℝ) < cardLength β x := cardLength_pos β x
  have hQR2 : (2 : ℝ) ≤ ((siftStart (γ * β) x : ℕ) : ℝ) := by exact_mod_cast hQ2
  have hQ0 : (0 : ℝ) < ((siftStart (γ * β) x : ℕ) : ℝ) := by linarith
  have hQ1R : (1 : ℝ) ≤ ((siftStart (γ * β) x : ℕ) : ℝ) := by linarith
  have hz₀1 : 1 ≤ siftStart (γ * β) x := by omega
  have hη0 : 0 < ladderEta β γ x := ladderEta_pos hx1
  have hQh : ((siftStart (γ * β) x : ℕ) : ℝ) ≤ cardLength β x := by linarith
  have hple := ladderPow_le hQ1R hQh hη0
  have hδpos : 0 < fibreWidth x (cardLength β x) := by
    rw [fibreWidth]
    refine Real.log_pos ?_
    have : (0 : ℝ) < cardLength β x / Real.sqrt x := by positivity
    linarith
  have hB0 : (0 : ℝ) < ((budgetB β x : ℕ) : ℝ) := by
    have h1 : 1 ≤ budgetB β x := by
      rw [budgetB]
      exact Nat.le_floor (by push_cast; linarith [hsx.le, hh1])
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one h1
  have hlogh : Real.log (cardLength β x) = (Real.log x) ^ β := log_cardLength β x
  have hLxj : ∀ j ∈ Finset.range (ladderSteps β γ x),
      Real.log (max ((⌊((siftStart (γ * β) x : ℕ) : ℝ) * (1 + ladderEta β γ x) ^ (j + 1)⌋₊ : ℕ) : ℝ) 1)
        ≤ (Real.log x) ^ β := by
    intro j hj
    have hjL : j + 1 ≤ ladderSteps β γ x := Finset.mem_range.1 hj
    have hb := max_ladderBlock_le hQ0 hη0.le hjL hple hh1
    have hmax0 : (0 : ℝ) < max ((⌊((siftStart (γ * β) x : ℕ) : ℝ)
        * (1 + ladderEta β γ x) ^ (j + 1)⌋₊ : ℕ) : ℝ) 1 :=
      lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    have := Real.log_le_log hmax0 hb
    rwa [hlogh] at this
  have hqj : ∀ j ∈ Finset.range (ladderSteps β γ x),
      Real.log ((siftStart (γ * β) x : ℕ) : ℝ)
        ≤ Real.log (max ((⌊((siftStart (γ * β) x : ℕ) : ℝ)
            * (1 + ladderEta β γ x) ^ (j + 1)⌋₊ : ℕ) : ℝ) 1) := by
    intro j _
    exact Real.log_le_log hQ0 (le_max_ladderBlock rfl hη0.le hz₀1 j)
  have hxminj : ∀ j ∈ Finset.range (ladderSteps β γ x),
      ((siftStart (γ * β) x : ℕ) : ℝ)
        ≤ max ((⌊((siftStart (γ * β) x : ℕ) : ℝ)
            * (1 + ladderEta β γ x) ^ (j + 1)⌋₊ : ℕ) : ℝ) 1 := fun j _ =>
    le_max_ladderBlock rfl hη0.le hz₀1 j
  have hNj : ∀ j ∈ Finset.range (ladderSteps β γ x),
      budgetNmin β x ≤ ((⌊((budgetB β x : ℕ) : ℝ)
        / (((siftStart (γ * β) x : ℕ) : ℝ) * (1 + ladderEta β γ x) ^ j)⌋₊ : ℕ) : ℝ) := by
    intro j hj
    exact le_floor_cofactor hQ0 hη0.le (Finset.mem_range.1 hj) hple rfl
  have hNmin1 : (1 : ℝ) ≤ budgetNmin β x := by
    rw [budgetNmin]
    have : 1 ≤ ⌊gallagherCut β x⌋₊ := Nat.le_floor (by exact_mod_cast hG1)
    exact_mod_cast this
  have hK : K₀ ≤ contourParam (budgetNmin β x) := by exact_mod_cast hCP
  have hμ0 : (0 : ℝ) ≤ budgetMu A delta β x := by
    rw [budgetMu]
    have h1 : (0 : ℝ) < routeTWidthPolylogLower A (2 * Real.pi * budgetT β x) :=
      routeTWidthPolylogLower_pos _ _
    have : (0 : ℝ) ≤ min delta (routeTWidthPolylogLower A (2 * Real.pi * budgetT β x)) :=
      le_min hdelta.le h1.le
    linarith
  have hw₀0 : (0 : ℝ) ≤ annulusStart β x := by
    rw [annulusStart]
    exact Real.rpow_nonneg (Real.log_nonneg hx1.le) _
  exact hmaster x (cardLength β x) (siftStart (γ * β) x) (ladderTop β γ x)
    (ladderSteps β γ x) (budgetB β x) ((siftStart (γ * β) x : ℕ) : ℝ) (ladderEta β γ x)
    (ladderWidth β x) (annulusStart β x) (budgetT β x) (gallagherCut β x) ((Real.log x) ^ β)
    (Real.log ((siftStart (γ * β) x : ℕ) : ℝ)) (budgetMu A delta β x)
    ((siftStart (γ * β) x : ℕ) : ℝ) (budgetHmaj A β x) (budgetNmin β x)
    hδpos rfl hB0 hz₀1 rfl (by linarith) hη0 hL1 rfl hG1 hGT hw₀0 hwG hD1 hw₀τ
    (Real.rpow_nonneg (Real.log_nonneg hx1.le) β) hLxj (Real.log_nonneg hQ1R) hqj hμ0 le_rfl
    hQ0 hxminj le_rfl
    hNmin1 hN₁ hNj hK hadm

end

end RHTower.Sieve
