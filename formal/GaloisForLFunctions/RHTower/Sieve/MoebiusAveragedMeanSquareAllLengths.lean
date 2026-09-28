import GaloisForLFunctions.RHTower.Sieve.MoebiusHeadWindowAllLengths

/-!
# Matomäki–Radziwiłł for the Möbius function at every length

For every short-interval length `h(x) → ∞` with `h(x) ≤ √x`, the fibre sums of `μ` have small
averaged mean square.  The head window has width `W = M/√h` over a polynomial of length
`M = ⌊√x + h⌋`; the ladder of prime ranges starts at the scale
`ν = min((log h/6)^{1/5}, (log x)^{1/40})` (so that the whole first range lies below `√h = M/W`)
and ends at the scale `T = (log x)^{1/40}`.  The relative budget is

`disc + 3000/log ν + (high group, ladder error, rough class) + exceptional set`,

and every term tends to zero: the disc by Route T, the ladder because `ν → ∞`, the high range
because its Route-T saving beats every power of `log x`, and the exceptional set because its
measure carries the saving `exp(−5 log x/log log x)` against `exp((log x)^{99/100})`.
-/

namespace RHTower.Sieve

open Filter Topology Finset MeasureTheory
open scoped ArithmeticFunction.Moebius

noncomputable section

/-- The scale parameter of the ladder at `x`: capped by the length `h` and by `(log x)^{1/40}`. -/
def headNu (hh : ℝ → ℝ) (x : ℝ) : ℝ :=
  min ((Real.log (hh x) / 6) ^ ((1 : ℝ) / 5)) ((Real.log x) ^ ((1 : ℝ) / 40))

/-- The target scale `T = (log x)^{1/40}` of the last range. -/
def headT (x : ℝ) : ℝ := (Real.log x) ^ ((1 : ℝ) / 40)

/-- The number of high steps is at most `2·headLam`. -/
def headLam (x : ℝ) : ℝ := (Real.log x) ^ ((99 : ℝ) / 100 + 3)

/-- The relative budget of the head window at `x`. -/
def headBudget (K : ℝ) (ρ hh : ℝ → ℝ) (x : ℝ) : ℝ :=
  2 * twoRangeDisc (99 / 100) 8 x * K ^ 2 * Real.exp (-((Real.log x / 2) ^ ((1 : ℝ) / 20))) ^ 2
    + 3000 / Real.log (headNu hh x)
    + (1848 * headLam x * (8 * ρ x * headLam x) ^ 2 * (Real.log x) ^ 3
        + 240 * (highEta 3 x + 6 / ((highBase (19 / 20) x : ℕ) : ℝ))
        + 108 / ((99 / 100 - 19 / 20) / 2 * Real.log (Real.log x)))
    + 126 * headLam x * (60000 * Real.log x) * Real.log x * cardLength (99 / 100) x
        * (8 * ρ x * headLam x) ^ 2 * Real.exp (-(headT x ^ 40 / (8 * Real.log (headT x))))

theorem tendsto_headNu {hh : ℝ → ℝ} (hgrow : Tendsto hh atTop atTop) :
    Tendsto (headNu hh) atTop atTop := by
  have h1 : Tendsto (fun x => (Real.log (hh x) / 6) ^ ((1 : ℝ) / 5)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp
      ((Real.tendsto_log_atTop.comp hgrow).atTop_div_const (by norm_num))
  have h2 : Tendsto (fun x : ℝ => (Real.log x) ^ ((1 : ℝ) / 40)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp Real.tendsto_log_atTop
  rw [tendsto_atTop]
  intro b
  filter_upwards [h1.eventually_ge_atTop b, h2.eventually_ge_atTop b] with x hx1 hx2
  exact le_min hx1 hx2

/-- The exponential saving of the exceptional set at `T = (log x)^{1/40}`. -/
theorem headT_saving {x : ℝ} (hx : 1 < Real.log x) :
    headT x ^ 40 / (8 * Real.log (headT x)) = 5 * Real.log x / Real.log (Real.log x) := by
  have hl0 : 0 < Real.log x := by linarith
  have h40 : headT x ^ 40 = Real.log x := by
    rw [headT, ← Real.rpow_natCast, ← Real.rpow_mul hl0.le]; norm_num
  have hlog : Real.log (headT x) = Real.log (Real.log x) / 40 := by
    rw [headT, Real.log_rpow hl0]; ring
  rw [h40, hlog]
  have : 0 < Real.log (Real.log x) := Real.log_pos hx
  field_simp
  ring

theorem tendsto_headBudget {K : ℝ} {ρ hh : ℝ → ℝ} (hgrow : Tendsto hh atTop atTop)
    (hρ : Tendsto (fun x => (Real.log x) ^ ((1497 : ℝ) / 200) * ρ x) atTop (𝓝 0)) :
    Tendsto (headBudget K ρ hh) atTop (𝓝 0) := by
  -- the disc
  have hdisc : Tendsto (fun x : ℝ => 2 * twoRangeDisc (99 / 100) 8 x * K ^ 2
      * Real.exp (-((Real.log x / 2) ^ ((1 : ℝ) / 20))) ^ 2) atTop (𝓝 0) := by
    set s : ℝ := 2 * (1 / 2 : ℝ) ^ ((1 : ℝ) / 20) with hs
    have hs0 : 0 < s := by positivity
    have hbase := (tendsto_logRpow_mul_expSaving (d := (1 : ℝ) / 20) (s := s) (by norm_num) hs0
      (4 * (99 / 100 : ℝ) + 3 * 8 + 3)).const_mul (2 * K ^ 2 / (2 * Real.pi))
    rw [mul_zero] at hbase
    refine hbase.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx
    have hl0 : 0 ≤ Real.log x := (Real.log_pos hx).le
    have hsplit : (Real.log x / 2) ^ ((1 : ℝ) / 20)
        = (1 / 2 : ℝ) ^ ((1 : ℝ) / 20) * (Real.log x) ^ ((1 : ℝ) / 20) := by
      rw [div_eq_mul_one_div, Real.mul_rpow hl0 (by norm_num)]; ring
    have hsq : Real.exp (-((Real.log x / 2) ^ ((1 : ℝ) / 20))) ^ 2
        = Real.exp (-(s * (Real.log x) ^ ((1 : ℝ) / 20))) := by
      rw [← Real.exp_nat_mul, hsplit, hs]; congr 1; push_cast; ring
    rw [hsq, twoRangeDisc]
    have hpi := Real.pi_pos
    field_simp
  -- the ladder
  have hlad : Tendsto (fun x => 3000 / Real.log (headNu hh x)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp (tendsto_headNu hgrow))
  -- the high group
  set E : ℝ := 1497 / 200 with hEdef
  have hgrp : Tendsto (fun x => 1848 * headLam x * (8 * ρ x * headLam x) ^ 2 * (Real.log x) ^ 3)
      atTop (𝓝 0) := by
    have h := (hρ.pow 2).const_mul 118272
    rw [show (118272 : ℝ) * 0 ^ 2 = 0 by norm_num] at h
    refine h.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx
    have hl0 : 0 < Real.log x := Real.log_pos hx
    have e1 : headLam x ^ 3 * (Real.log x) ^ 3 = ((Real.log x) ^ E) ^ 2 := by
      rw [headLam, ← Real.rpow_natCast ((Real.log x) ^ ((99 : ℝ) / 100 + 3)) 3,
        ← Real.rpow_mul hl0.le, ← Real.rpow_natCast (Real.log x) 3, ← Real.rpow_add hl0,
        ← Real.rpow_natCast ((Real.log x) ^ E) 2, ← Real.rpow_mul hl0.le, hEdef]
      norm_num
    calc 118272 * ((Real.log x) ^ E * ρ x) ^ 2
        = 1848 * 64 * ρ x ^ 2 * ((Real.log x) ^ E) ^ 2 := by ring
      _ = 1848 * 64 * ρ x ^ 2 * (headLam x ^ 3 * (Real.log x) ^ 3) := by rw [e1]
      _ = 1848 * headLam x * (8 * ρ x * headLam x) ^ 2 * (Real.log x) ^ 3 := by ring
  -- the error and the rough class
  have hR : Tendsto (fun x => ((highBase (19 / 20) x : ℕ) : ℝ)) atTop atTop := by
    have hev : cardLength (19 / 20) ≤ᶠ[atTop] fun x => ((highBase (19 / 20) x : ℕ) : ℝ) := by
      filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx
      exact (highBase_bounds hx).1
    exact tendsto_atTop_mono' atTop hev (tendsto_cardLength (β := (19 / 20 : ℝ)) (by norm_num))
  have herr : Tendsto (fun x => 240 * (highEta 3 x + 6 / ((highBase (19 / 20) x : ℕ) : ℝ)))
      atTop (𝓝 0) := by
    have h6 : Tendsto (fun x => (6 : ℝ) / ((highBase (19 / 20) x : ℕ) : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hR
    have h := ((tendsto_highEta (c' := (3 : ℝ)) (by norm_num)).add h6).const_mul (240 : ℝ)
    simpa using h
  have hrough : Tendsto (fun x : ℝ => 108 / ((99 / 100 - 19 / 20) / 2 * Real.log (Real.log x)))
      atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      ((Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).const_mul_atTop (by norm_num))
  -- the exceptional set
  have hexc : Tendsto (fun x => 126 * headLam x * (60000 * Real.log x) * Real.log x
      * cardLength (99 / 100) x * (8 * ρ x * headLam x) ^ 2
      * Real.exp (-(headT x ^ 40 / (8 * Real.log (headT x))))) atTop (𝓝 0) := by
    have hmaj := (hρ.pow 2).const_mul 483840000
    rw [show (483840000 : ℝ) * 0 ^ 2 = 0 by norm_num] at hmaj
    have hll := tendsto_logRpow_mul_logLogPow (e := -(1 : ℝ) / 100) (by norm_num) 1
    refine squeeze_zero' ?_ ?_ hmaj
    · filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx
      have hl0 : 0 < Real.log x := Real.log_pos hx
      have : 0 ≤ headLam x := Real.rpow_nonneg hl0.le _
      have := cardLength_pos (99 / 100) x
      positivity
    · filter_upwards [Filter.eventually_gt_atTop (Real.exp 1),
        Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1) hll] with x hx hsmall
      have hx1 : 1 < x := lt_trans (by have := Real.add_one_le_exp (1 : ℝ); linarith) hx
      have hl0 : 0 < Real.log x := Real.log_pos hx1
      have hl1 : 1 < Real.log x := by
        rw [← Real.log_exp 1]; exact Real.log_lt_log (Real.exp_pos 1) hx
      have hll0 : 0 < Real.log (Real.log x) := Real.log_pos hl1
      rw [headT_saving hl1]
      have hsave : cardLength (99 / 100) x * Real.exp (-(5 * Real.log x / Real.log (Real.log x)))
          ≤ 1 := by
        rw [cardLength, ← Real.exp_add, Real.exp_le_one_iff]
        have hsm : Real.log (Real.log x) ≤ (Real.log x) ^ ((1 : ℝ) / 100) := by
          rw [pow_one, show (-(1 : ℝ) / 100) = -((1 : ℝ) / 100) by ring,
            Real.rpow_neg hl0.le] at hsmall
          have hp : 0 < (Real.log x) ^ ((1 : ℝ) / 100) := Real.rpow_pos_of_pos hl0 _
          rw [inv_mul_le_iff₀ hp, mul_one] at hsmall
          exact hsmall
        have hsplit : (Real.log x) ^ ((99 : ℝ) / 100) * (Real.log x) ^ ((1 : ℝ) / 100)
            = Real.log x := by
          rw [← Real.rpow_add hl0]; norm_num
        have hkey : (Real.log x) ^ ((99 : ℝ) / 100) * Real.log (Real.log x) ≤ 5 * Real.log x := by
          have := mul_le_mul_of_nonneg_left hsm (Real.rpow_nonneg hl0.le ((99 : ℝ) / 100))
          linarith
        rw [add_neg_le_iff_le_add, zero_add, le_div_iff₀ hll0]
        exact hkey
      have hl1' : 1 ≤ Real.log x := hl1.le
      have e1 : headLam x ^ 3 * (Real.log x) ^ 2 ≤ ((Real.log x) ^ E) ^ 2 := by
        have h3 : headLam x ^ 3 * (Real.log x) ^ 3 = ((Real.log x) ^ E) ^ 2 := by
          rw [headLam, ← Real.rpow_natCast ((Real.log x) ^ ((99 : ℝ) / 100 + 3)) 3,
            ← Real.rpow_mul hl0.le, ← Real.rpow_natCast (Real.log x) 3, ← Real.rpow_add hl0,
            ← Real.rpow_natCast ((Real.log x) ^ E) 2, ← Real.rpow_mul hl0.le, hEdef]
          norm_num
        have hL0 : 0 ≤ headLam x ^ 3 := by
          have : 0 ≤ headLam x := Real.rpow_nonneg hl0.le _
          positivity
        rw [← h3]
        have : (Real.log x) ^ 2 ≤ (Real.log x) ^ 3 := pow_le_pow_right₀ hl1' (by norm_num)
        exact mul_le_mul_of_nonneg_left this hL0
      have hρ2 : 0 ≤ ρ x ^ 2 := sq_nonneg _
      calc 126 * headLam x * (60000 * Real.log x) * Real.log x * cardLength (99 / 100) x
            * (8 * ρ x * headLam x) ^ 2 * Real.exp (-(5 * Real.log x / Real.log (Real.log x)))
          = 483840000 * ρ x ^ 2 * (headLam x ^ 3 * (Real.log x) ^ 2)
            * (cardLength (99 / 100) x * Real.exp (-(5 * Real.log x / Real.log (Real.log x)))) := by
            ring
        _ ≤ 483840000 * ρ x ^ 2 * ((Real.log x) ^ E) ^ 2 * 1 := by
            have h0 : 0 ≤ 483840000 * ρ x ^ 2 := by positivity
            have h1 : 0 ≤ cardLength (99 / 100) x
                * Real.exp (-(5 * Real.log x / Real.log (Real.log x))) := by
              have := cardLength_pos (99 / 100) x; positivity
            have := mul_le_mul (mul_le_mul_of_nonneg_left e1 h0) hsave h1 (by positivity)
            linarith
        _ = 483840000 * ((Real.log x) ^ E * ρ x) ^ 2 := by ring
  have hsum := ((hdisc.add hlad).add ((hgrp.add herr).add hrough)).add hexc
  simp only [add_zero] at hsum
  exact hsum

/-- **The Möbius head window at every length, pointwise in `x`.** -/
theorem eventually_integral_head_le_budget {hh : ℝ → ℝ} (hgrow : Tendsto hh atTop atTop)
    (hsq : ∀ᶠ x : ℝ in atTop, hh x ≤ Real.sqrt x) {K A₀ δ₀ Ctot : ℝ} (hCtot : 0 < Ctot)
    (hdiscr : ∀ᶠ N : ℝ in atTop, ∀ w₀ : ℝ, 0 ≤ w₀ → 2 * Real.pi * w₀ ≤ N →
      (∫ w in Set.Icc (-w₀) w₀, ‖logPoly moebiusCoeff (Finset.Icc 1 ⌊N⌋₊) w‖ ^ 2)
        ≤ 2 * w₀ * (K * N * Real.exp (-((Real.log N) ^ ((1 : ℝ) / 20)))) ^ 2)
    (hhigh : ∀ᶠ x : ℝ in atTop, ∀ T : Set ℝ, ∀ j ∈ Finset.range (highSteps (19 / 20) (99 / 100) 3 x),
        ∀ w ∈ annulusLarge T (headTop x) (twoRangeDisc (99 / 100) 8 x),
          ‖primeBlockPoly (geomBlock (primesRange (highBase (19 / 20) x)
              (highTop (19 / 20) (99 / 100) 3 x)) ((highBase (19 / 20) x : ℕ) : ℝ)
              (1 + highEta 3 x) j) w‖
            ≤ topHighRho A₀ δ₀ Ctot (19 / 20) (99 / 100) 3 8 headTop x
                * (((highBase (19 / 20) x : ℕ) : ℝ) * (1 + highEta 3 x) ^ j)) :
    ∀ᶠ x : ℝ in atTop,
      (∫ w in Set.Icc (-(headT₀ x (hh x) (Real.sqrt (hh x)))) (headT₀ x (hh x) (Real.sqrt (hh x))),
          ‖logPoly (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ))
            (fibreIndex x (hh x)) w‖ ^ (2 : ℕ))
        ≤ ((⌊Real.sqrt x + hh x⌋₊ : ℕ) : ℝ) ^ 2
          * headBudget K (fun x => topHighRho A₀ δ₀ Ctot (19 / 20) (99 / 100) 3 8 headTop x) hh x := by
  set ρ := fun x => topHighRho A₀ δ₀ Ctot (19 / 20) (99 / 100) 3 8 headTop x with hρdef
  have htop := headTop_facts
  have hρ0 := topHighRho_nonneg (A₀ := A₀) (δ₀ := δ₀) (a₁ := 19 / 20) (c' := 3) hCtot.le
    (by norm_num : (0 : ℝ) < 99 / 100) (by norm_num : (0 : ℝ) < 8) (htop.mono fun x hx => hx.1)
    (htop.mono fun x hx => hx.2.1)
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 hdiscr
  set N : ℝ := max 3000 (4 * mertensFirstConst + 1) with hNdef
  have hN3 : (3000 : ℝ) ≤ N := le_max_left _ _
  have hlogx40 : Tendsto (fun x : ℝ => (Real.log x) ^ ((1 : ℝ) / 40)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp Real.tendsto_log_atTop
  have hsmallC := tendsto_rpow_log_div_sqrt (4 * (99 / 100 : ℝ) + 3 * 8 + 3)
  filter_upwards [hsq, hgrow.eventually_ge_atTop (Real.exp (6 * N ^ 5)),
    hgrow.eventually_ge_atTop 1, hlogx40.eventually_ge_atTop N,
    Filter.eventually_ge_atTop (max (N₀ ^ 2) 10000),
    Tendsto.eventually_le_const (show (0 : ℝ) < 1 by norm_num) hsmallC,
    htop, hhigh, hρ0, plainKernelFarConst_head_le,
    Filter.eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ),
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop (1 : ℝ),
    two_le_highBase_and_le_highTop (a := (19 / 20 : ℝ)) (b := 99 / 100) (c' := 3) (by norm_num),
    one_le_highSteps (a := (19 / 20 : ℝ)) (b := 99 / 100) (c' := 3) (by norm_num) (by norm_num)
      (by norm_num),
    highSteps_le (a := (19 / 20 : ℝ)) (b := 99 / 100) (c' := 3) (by norm_num) (by norm_num)
      (by norm_num),
    highLadder_le (a := (19 / 20 : ℝ)) (b := 99 / 100) (c' := 3) (by norm_num) (by norm_num),
    highRange_harmonic_le (a := (19 / 20 : ℝ)) (b := 99 / 100) (c' := 3) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num),
    highRange_harmonic_ge (a := (19 / 20 : ℝ)) (b := 99 / 100) (c' := 3) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num),
    Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1) (tendsto_highEta (c' := 3) (by norm_num)),
    (tendsto_rpow_log_mul_cardLength_div_sqrt (β := (99 / 100 : ℝ)) (by norm_num) (by norm_num)
      0).eventually_le_const (show (0 : ℝ) < 1 / 3 by norm_num),
    highBlock_base_le_card (a₁ := (19 / 20 : ℝ)) (b := 99 / 100) (c' := 3) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)]
    with x hhx hhbig hh1 hxN hxbig hsmall hxtop hhighx hρx hFCx hx1 hlog1 hll1 hbase hL1 hLup hQ
      hHup hHlo hη1 hcl3 hcard8
  set h := hh x with hhdef
  set M : ℕ := ⌊Real.sqrt x + h⌋₊ with hMdef
  have hx0 : 0 < x := by linarith
  have hs0 : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hxx : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
  have hx4 : 10000 ≤ x := le_trans (le_max_right _ _) hxbig
  have hs100 : 100 ≤ Real.sqrt x := by
    rw [show (100 : ℝ) = Real.sqrt (100 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  have hMlo : Real.sqrt x ≤ M := by
    have := Nat.lt_floor_add_one (Real.sqrt x + h)
    linarith
  have hMhi : (M : ℝ) ≤ 2 * Real.sqrt x := by
    have := Nat.floor_le (show 0 ≤ Real.sqrt x + h by linarith)
    linarith
  have hM0 : (0 : ℝ) < M := by linarith
  -- the ladder parameters
  have hlogh : 6 * N ^ 5 ≤ Real.log h := by
    have := Real.log_le_log (Real.exp_pos _) hhbig
    rwa [Real.log_exp] at this
  have hN0 : 0 ≤ N := by linarith
  have hνh : N ≤ (Real.log h / 6) ^ ((1 : ℝ) / 5) := by
    have h5 : N ^ 5 ≤ Real.log h / 6 := by linarith
    have e : (N ^ 5) ^ ((1 : ℝ) / 5) = N := by
      rw [show ((1 : ℝ) / 5) = ((5 : ℕ) : ℝ)⁻¹ by norm_num]
      exact Real.pow_rpow_inv_natCast hN0 (by norm_num)
    calc N = (N ^ 5) ^ ((1 : ℝ) / 5) := e.symm
      _ ≤ (Real.log h / 6) ^ ((1 : ℝ) / 5) :=
          Real.rpow_le_rpow (by positivity) h5 (by norm_num)
  have hνlo : N ≤ headNu hh x := le_min hνh hxN
  have hν : 3000 ≤ headNu hh x := le_trans hN3 hνlo
  have hc : 4 * mertensFirstConst + 1 ≤ headNu hh x := le_trans (le_max_right _ _) hνlo
  have hνT : headNu hh x ≤ headT x := min_le_right _ _
  have hl0 : 0 < Real.log x := by linarith
  have hT40 : headT x ^ 40 = Real.log x := by
    rw [headT, ← Real.rpow_natCast, ← Real.rpow_mul hl0.le]; norm_num
  have hMlo' : headT x ^ 40 / 2 ≤ Real.log M := by
    rw [hT40]
    have := Real.log_le_log hs0 hMlo
    rwa [Real.log_sqrt hx0.le] at this
  have hMhi' : Real.log M ≤ headT x ^ 40 := by
    rw [hT40]
    exact Real.log_le_log hM0 (by nlinarith)
  -- the window
  have hh0 : 0 < h := by linarith
  have hsh0 : 0 < Real.sqrt h := Real.sqrt_pos.mpr hh0
  have hshh : Real.sqrt h * Real.sqrt h = h := Real.mul_self_sqrt hh0.le
  have hsh1 : 1 ≤ Real.sqrt h := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hh1
  set W := headT₀ x h (Real.sqrt h) with hWdef
  have hWeq : W = M / Real.sqrt h := by
    rw [hWdef, headT₀, headG, ← hMdef, div_mul_eq_mul_div,
      div_eq_div_iff hh0.ne' hsh0.ne', mul_assoc, hshh]
  have hshM : Real.sqrt h ≤ M := by
    have : Real.sqrt h ≤ h := by
      calc Real.sqrt h = Real.sqrt h * 1 := (mul_one _).symm
        _ ≤ Real.sqrt h * Real.sqrt h := mul_le_mul_of_nonneg_left hsh1 hsh0.le
        _ = h := hshh
    linarith
  have hW : 1 ≤ W := by rw [hWeq, le_div_iff₀ hsh0, one_mul]; exact hshM
  have hWM : W ≤ M := by rw [hWeq]; exact div_le_self hM0.le hsh1
  have hW2 : W ≤ 2 * Real.sqrt x := le_trans hWM hMhi
  have hW0 : W * rangeLadderTopReal (headNu hh x) 0 ≤ M := by
    have hν0 : 0 < headNu hh x := by linarith
    have hν5 : headNu hh x ^ 5 ≤ Real.log h / 6 := by
      have h1 : headNu hh x ≤ (Real.log h / 6) ^ ((1 : ℝ) / 5) := min_le_left _ _
      have h2 := pow_le_pow_left₀ hν0.le h1 5
      have e : ((Real.log h / 6) ^ ((1 : ℝ) / 5)) ^ 5 = Real.log h / 6 := by
        rw [show ((1 : ℝ) / 5) = ((5 : ℕ) : ℝ)⁻¹ by norm_num]
        have : 0 ≤ N ^ 5 := by positivity
        exact Real.rpow_inv_natCast_pow (by linarith) (by norm_num)
      rwa [e] at h2
    have hQ0 : rangeLadderTopReal (headNu hh x) 0 ≤ Real.sqrt h := by
      have hlogQ := log_rangeLadderTopReal_le (by linarith : (2 : ℝ) ≤ headNu hh x) 0
      rw [rangeLadderNu, pow_zero, pow_one] at hlogQ
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hh0,
        ← Real.exp_log (rangeLadderTopReal_pos hν0 0)]
      exact Real.exp_le_exp.mpr (by linarith)
    rw [hWeq]
    calc (M : ℝ) / Real.sqrt h * rangeLadderTopReal (headNu hh x) 0
        ≤ (M : ℝ) / Real.sqrt h * Real.sqrt h :=
          mul_le_mul_of_nonneg_left hQ0 (by positivity)
      _ = M := by field_simp
  -- the disc
  set w₀ := twoRangeDisc (99 / 100) 8 x with hw₀def
  have hw₀0 : 0 ≤ w₀ := (twoRangeDisc_pos hx1).le
  have h2pw : 2 * Real.pi * w₀ ≤ M := by
    rw [hw₀def, two_pi_mul_twoRangeDisc, twoRangeT₀]
    rw [div_le_one hs0] at hsmall
    linarith
  have hMN : N₀ ≤ (M : ℝ) := by
    have hsN : |N₀| ≤ Real.sqrt x := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt (le_trans (le_max_left _ _) hxbig)
    linarith [le_abs_self N₀]
  have hdisc := hN₀ (M : ℝ) hMN w₀ hw₀0 h2pw
  rw [Nat.floor_natCast] at hdisc
  -- the high range
  have hP' := highRange_bounds (a := (19 / 20 : ℝ)) (b := 99 / 100) (c' := 3) hx1
  simp only [highP] at hcard8
  set P' := primesRange (highBase (19 / 20) x) (highTop (19 / 20) (99 / 100) 3 x) with hP'def
  set R' : ℝ := ((highBase (19 / 20) x : ℕ) : ℝ) with hR'def
  set η' := highEta 3 x with hη'def
  set L' := highSteps (19 / 20) (99 / 100) 3 x with hL'def
  set cL := cardLength (99 / 100) x with hcLdef
  have hη : 0 < η' := highEta_pos hx1
  have hR2 : (2 : ℝ) ≤ R' := by rw [hR'def]; exact_mod_cast hbase.1
  have hcl1 : 1 ≤ cL := by
    rw [hcLdef, cardLength]; exact Real.one_le_exp (Real.rpow_nonneg hl0.le _)
  have hPprime : ∀ q ∈ P', q.Prime := fun q hq => (mem_primesRange.1 hq).1
  have hcard : (P'.card : ℝ) ≤ 2 * cL := by
    refine (card_primesRange_le_top _ _).trans ((Nat.floor_le (by positivity)).trans hQ)
  clear_value P' R' η' L' cL
  have hcl3' : cL ≤ Real.sqrt x / 3 := by
    rw [Real.rpow_zero, one_mul, div_le_iff₀ hs0] at hcl3
    linarith
  have hclM : 3 * cL ≤ M := by linarith
  have hll : Real.log (Real.log x) ≤ Real.log x := by
    have := Real.log_le_sub_one_of_pos hl0; linarith
  have hH : rangeHarmonic P' ≤ Real.log x := le_trans hHup hll
  have hll1' : 1 ≤ Real.log (Real.log x) := hll1
  have hA : 0 < (99 / 100 - 19 / 20) / 2 * Real.log (Real.log x) := by
    have : (0 : ℝ) < Real.log (Real.log x) := by linarith only [hll1']
    positivity
  have hΛ : 2 * (L' : ℝ) * (2 * Real.pi)⁻¹ ≤ headLam x := by
    have hpi3 := Real.pi_gt_three
    rw [mul_inv_le_iff₀ (by positivity), headLam]
    have : (0 : ℝ) ≤ (Real.log x) ^ ((99 : ℝ) / 100 + 3) := by positivity
    nlinarith only [hLup, this, hpi3]
  have hΛ0 : 0 ≤ headLam x := Real.rpow_nonneg hl0.le _
  have hlogW : Real.log (2 + 2 * (2 * Real.pi * W)) ≤ Real.log x := by
    have hpi4 := Real.pi_le_four
    refine Real.log_le_log (by positivity) ?_
    nlinarith only [hW2, hpi4, hW, hs100, hxx, Real.pi_pos]
  have hR0 : 0 < R' := lt_of_lt_of_le (by norm_num) hR2
  have h1η : 1 ≤ 1 + η' := le_add_of_nonneg_right hη.le
  have hN1 : 1 ≤ ⌊(M : ℝ) / R'⌋₊ := by
    refine Nat.le_floor ?_
    rw [Nat.cast_one, le_div_iff₀ hR0, one_mul]
    have : R' ≤ R' * (1 + η') ^ L' := le_mul_of_one_le_right hR0.le (one_le_pow₀ h1η)
    linarith only [this, hQ, hcl3', hMlo, hs0]
  have hN2 : ((⌊(M : ℝ) / R'⌋₊ : ℕ) : ℝ) ≤ 2 * Real.sqrt x := by
    have h1 := Nat.floor_le (div_nonneg hM0.le hR0.le)
    have h2 : (M : ℝ) / R' ≤ M := div_le_self hM0.le (le_trans (by norm_num) hR2)
    linarith only [h1, h2, hMhi]
  have hFC := hFCx ⌊(M : ℝ) / R'⌋₊ hN1 hN2 W hW hW2
  have hNj : ∀ j ∈ Finset.range L', 1 ≤ ⌊(M : ℝ) / (R' * (1 + η') ^ j)⌋₊ := by
    intro j hj
    refine Nat.le_floor ?_
    have hRj : 0 < R' * (1 + η') ^ j := mul_pos hR0 (pow_pos (lt_of_lt_of_le one_pos h1η) j)
    rw [Nat.cast_one, le_div_iff₀ hRj, one_mul]
    have : R' * (1 + η') ^ j ≤ R' * (1 + η') ^ L' :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1η (Finset.mem_range.mp hj).le) hR0.le
    linarith only [this, hQ, hcl3', hMlo, hs0]
  have hbound' : ∀ j ∈ Finset.range L', ∀ w ∈ annulusLarge (rangeUnionSmall
      (rangeLadderP (headNu hh x)) (rangeLadderR (headNu hh x)) (rangeLadderEta (headNu hh x))
      (rangeLadderSteps (headNu hh x))
      (powerThreshold (rangeLadderR (headNu hh x)) (rangeLadderEta (headNu hh x)) rangeLadderAlpha)
      W (rangeLadderLast (headNu hh x) (headT x) + 1)) W w₀,
      ‖primeBlockPoly (geomBlock P' R' (1 + η') j) w‖
        ≤ (8 * ρ x * headLam x) * ((geomBlock P' R' (1 + η') j).card : ℝ) := by
    intro j hj w hw
    have hw' := annulusLarge_subset_of_le hW2 hw
    have hb := hhighx _ j hj w hw'
    have hc := hcard8 j hj
    have hρ' : 0 ≤ ρ x := hρx
    calc ‖primeBlockPoly (geomBlock P' R' (1 + η') j) w‖ ≤ ρ x * (R' * (1 + η') ^ j) := hb
      _ ≤ ρ x * (8 * (Real.log x) ^ ((99 : ℝ) / 100 + 3) * ((geomBlock P' R' (1 + η') j).card : ℝ)) :=
          mul_le_mul_of_nonneg_left hc hρ'
      _ = (8 * ρ x * headLam x) * ((geomBlock P' R' (1 + η') j).card : ℝ) := by
          rw [headLam]; ring
  have hmain := integral_head_le_ladder hν hc hνT M hMlo' hMhi' hW hWM hW0 hdisc hPprime
    (ρ' := 8 * ρ x * headLam x) (K := 60000 * Real.log x)
    (le_trans (by norm_num) hR2) hη hη1 hL1 hΛ hP' hcard hQ hcl1 hclM hlog1 hH hA hHlo hlogW hFC
    hNj hbound'
    hΛ0 (by positivity)
  have hfib : fibreIndex x h = Finset.Icc 1 M := rfl
  rw [hfib]
  refine hmain.trans ?_
  -- the disc against its budget
  have hE : Real.exp (-((Real.log (M : ℝ)) ^ ((1 : ℝ) / 20)))
      ≤ Real.exp (-((Real.log x / 2) ^ ((1 : ℝ) / 20))) := by
    refine Real.exp_le_exp.mpr (neg_le_neg ?_)
    have hlx : Real.log x / 2 ≤ Real.log (M : ℝ) := by
      have := Real.log_le_log hs0 hMlo
      rwa [Real.log_sqrt hx0.le] at this
    exact Real.rpow_le_rpow (by positivity) hlx (by norm_num)
  have hE0 : 0 ≤ Real.exp (-((Real.log (M : ℝ)) ^ ((1 : ℝ) / 20))) := (Real.exp_pos _).le
  have hdisc' : 2 * w₀ * (K * M * Real.exp (-((Real.log (M : ℝ)) ^ ((1 : ℝ) / 20)))) ^ 2
      ≤ (M : ℝ) ^ 2 * (2 * w₀ * K ^ 2 * Real.exp (-((Real.log x / 2) ^ ((1 : ℝ) / 20))) ^ 2) := by
    have hsq := pow_le_pow_left₀ hE0 hE 2
    have hc : 0 ≤ 2 * w₀ * K ^ 2 * (M : ℝ) ^ 2 := by positivity
    calc 2 * w₀ * (K * M * Real.exp (-((Real.log (M : ℝ)) ^ ((1 : ℝ) / 20)))) ^ 2
        = 2 * w₀ * K ^ 2 * (M : ℝ) ^ 2 * Real.exp (-((Real.log (M : ℝ)) ^ ((1 : ℝ) / 20))) ^ 2 := by
          ring
      _ ≤ 2 * w₀ * K ^ 2 * (M : ℝ) ^ 2 * Real.exp (-((Real.log x / 2) ^ ((1 : ℝ) / 20))) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq hc
      _ = (M : ℝ) ^ 2 * (2 * w₀ * K ^ 2 * Real.exp (-((Real.log x / 2) ^ ((1 : ℝ) / 20))) ^ 2) := by
          ring
  have hbud : (M : ℝ) ^ 2 * headBudget K ρ hh x
      = (M : ℝ) ^ 2 * (2 * w₀ * K ^ 2 * Real.exp (-((Real.log x / 2) ^ ((1 : ℝ) / 20))) ^ 2)
        + 3000 * (M : ℝ) ^ 2 / Real.log (headNu hh x)
        + (M : ℝ) ^ 2 * (1848 * headLam x * (8 * ρ x * headLam x) ^ 2 * (Real.log x) ^ 3
            + 240 * (η' + 6 / R') + 108 / ((99 / 100 - 19 / 20) / 2 * Real.log (Real.log x)))
        + 126 * headLam x * (60000 * Real.log x) * Real.log x * cL * (8 * ρ x * headLam x) ^ 2
            * (M : ℝ) ^ 2 * Real.exp (-(headT x ^ 40 / (8 * Real.log (headT x)))) := by
    rw [headBudget, hη'def, hR'def, hcLdef, hw₀def]
    ring
  rw [hbud]
  exact add_le_add (add_le_add (add_le_add hdisc' le_rfl) le_rfl) le_rfl

/-- **Matomäki–Radziwiłł for the Möbius function at every length.**  For every `hh → ∞` with
`hh ≤ √x`, the fibre sums of `μ` have small averaged mean square. -/
theorem averagedMeanSquare_moebius_of_tendsto {hh : ℝ → ℝ} (hgrow : Tendsto hh atTop atTop)
    (hsq : ∀ᶠ x : ℝ in atTop, hh x ≤ Real.sqrt x) :
    AveragedMeanSquare (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) hh := by
  have htop := headTop_facts
  obtain ⟨A₀, δ₀, Ctot, -, hCtot, hhigh, hlim⟩ :=
    exists_top_high_bound (a := 19 / 20) (b := 99 / 100) (c' := 3) (A₃ := 8) (top := headTop)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (htop.mono fun x hx => hx.1) (htop.mono fun x hx => hx.2.1) (htop.mono fun x hx => hx.2.2)
  obtain ⟨K, -, hdiscr⟩ := exists_setIntegral_disc_normSq_logPoly_moebius_le_rate
  have hρ : Tendsto (fun x => (Real.log x) ^ ((1497 : ℝ) / 200)
      * topHighRho A₀ δ₀ Ctot (19 / 20) (99 / 100) 3 8 headTop x) atTop (𝓝 0) :=
    hlim _ (by norm_num) (by norm_num)
  have hbudget := tendsto_headBudget (K := K) hgrow hρ
  have hkey := eventually_integral_head_le_budget hgrow hsq hCtot hdiscr hhigh
  refine averagedMeanSquare_moebius_of_headSmall (ω := fun x => Real.sqrt (hh x))
    (B := fun x => ∫ w in Set.Icc (-(headT₀ x (hh x) (Real.sqrt (hh x))))
        (headT₀ x (hh x) (Real.sqrt (hh x))),
      ‖logPoly (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ))
        (fibreIndex x (hh x)) w‖ ^ (2 : ℕ)) hgrow ?_ (Real.tendsto_sqrt_atTop.comp hgrow) ?_
  · filter_upwards [Filter.eventually_ge_atTop (4 : ℝ), hgrow.eventually_ge_atTop 1, hsq]
      with x hx4 hh1 hhx
    refine ⟨hx4, hh1, hhx, ?_, ?_, le_rfl⟩
    · rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hh1
    · exact MeasureTheory.setIntegral_nonneg measurableSet_Icc fun w _ => by positivity
  · refine squeeze_zero' ?_ ?_ hbudget
    · filter_upwards with x
      have : 0 ≤ ∫ w in Set.Icc (-(headT₀ x (hh x) (Real.sqrt (hh x))))
          (headT₀ x (hh x) (Real.sqrt (hh x))),
          ‖logPoly (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ))
            (fibreIndex x (hh x)) w‖ ^ (2 : ℕ) :=
        MeasureTheory.setIntegral_nonneg measurableSet_Icc fun w _ => by positivity
      positivity
    · filter_upwards [hkey, Filter.eventually_ge_atTop (4 : ℝ), hgrow.eventually_ge_atTop 1]
        with x hx hx4 hh1
      have hM : (0 : ℝ) < ((⌊Real.sqrt x + hh x⌋₊ : ℕ) : ℝ) := by
        have hs : (2 : ℝ) ≤ Real.sqrt x := by
          rw [show (2 : ℝ) = Real.sqrt 4 by
            rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
          exact Real.sqrt_le_sqrt hx4
        have := Nat.lt_floor_add_one (Real.sqrt x + hh x)
        linarith
      rw [div_le_iff₀ (by positivity), mul_comm]
      exact hx

end

end RHTower.Sieve
