import GaloisForLFunctions.RHTower.Sieve.JointNonSpectral
import GaloisForLFunctions.RHTower.Sieve.JointSpectralDivisor

/-!
# The slope row of the joint budget

The third of the four rows.  After `Sieve/JointBudgetMaster` the spectral part of the budget is
`16√x·(3α/Wc + 3β₀/Wc²)` with `α = (5π/2 + 5e/2·B₀/T₀)·Ec`; dividing by `(W_PW_Q)²h²√x` and
substituting the schedule's cut `Wc = √x/h` and expiry height `T₀ = Wc·ω` turns the first summand
into

```text
   48·(5π/2 + 5e/2·B₀/T₀)·Ec / ((W_PW_Q)²·h·√x)  ≤  (480π/h + 960e/ω)·X ,
```

`X = (1/W_Q + 1/W_P + 1/(W_PW_Q)) + #P·#Q/(W_PW_Q√x) + 1`, which is eventually below `3`.  Both
`1/h` and `1/ω` vanish, so the row does.

The coefficient energy enters at its **true** size `≍ B₀·(W_PW_Q)²`
(`Sieve/JointOmegaBudgetFromLadder.energy_jointOmegaCoeff_le_variance`); the divisor bound `(log x)²`
is *not* enough here, because the `5e·h/ω` half of the prefactor would then leave
`(log x)^(4 : ℕ)/(log x)^{β/2} → ∞`.
-/

namespace RHTower.Sieve

open Filter Topology

noncomputable section

/-- **The slope row, majorised.** -/
theorem jointSlope_quotient_le {h sx B₀ WP WQ NP NQ Ec ratio ω : ℝ}
    (hh : 1 ≤ h) (hsx : 0 < sx) (hWP : 0 < WP) (hWQ : 0 < WQ)
    (hNP : 0 ≤ NP) (hNQ : 0 ≤ NQ) (hB0 : B₀ ≤ 2 * sx)
    (hratio0 : 0 ≤ ratio) (hω : 0 < ω) (hratio : ratio ≤ 2 * h / ω)
    (hEc : Ec ≤ 2 * (B₀ * (WP * WQ) * (WP + WQ + 1) + 2 * (WP * WQ) * NP * NQ)
      + 2 * B₀ * (WP * WQ) ^ 2) :
    48 * ((5 * Real.pi / 2 + 5 * Real.exp 1 / 2 * ratio) * Ec)
        / ((sx / h) * (WP * WQ) ^ 2 * h ^ 2)
      ≤ (480 * Real.pi / h + 960 * Real.exp 1 / ω)
        * ((1 / WQ + 1 / WP + 1 / (WP * WQ)) + NP * NQ / (WP * WQ * sx) + 1) := by
  have hh0 : (0 : ℝ) < h := by linarith
  have hW : (0 : ℝ) < WP * WQ := mul_pos hWP hWQ
  have hNN : (0 : ℝ) ≤ NP * NQ := mul_nonneg hNP hNQ
  set X : ℝ := (1 / WQ + 1 / WP + 1 / (WP * WQ)) + NP * NQ / (WP * WQ * sx) + 1 with hXdef
  have hX0 : (0 : ℝ) ≤ X := by
    rw [hXdef]
    have h1 : (0 : ℝ) ≤ 1 / WQ := by positivity
    have h2 : (0 : ℝ) ≤ 1 / WP := by positivity
    have h3 : (0 : ℝ) ≤ 1 / (WP * WQ) := by positivity
    have h4 : (0 : ℝ) ≤ NP * NQ / (WP * WQ * sx) := by positivity
    linarith
  set A : ℝ := 5 * Real.pi / 2 + 5 * Real.exp 1 / 2 * ratio with hAdef
  have hA0 : (0 : ℝ) ≤ A := by
    rw [hAdef]
    have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
    have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
    positivity
  -- the denominator collapses
  have hden : (sx / h) * (WP * WQ) ^ 2 * h ^ 2 = (WP * WQ) ^ 2 * h * sx := by
    field_simp
    try ring
  rw [hden]
  -- the energy against the majorant
  have hXval : 4 * X * (WP * WQ) ^ 2 * sx
      = 4 * sx * ((WP * WQ) * (WP + WQ + 1)) + 4 * (WP * WQ) * (NP * NQ)
        + 4 * sx * (WP * WQ) ^ 2 := by
    rw [hXdef]
    field_simp
    try ring
  have hEc' : Ec ≤ 4 * X * (WP * WQ) ^ 2 * sx := by
    rw [hXval]
    have hWs : (0 : ℝ) ≤ WP + WQ + 1 := by linarith
    have hp1 : B₀ * ((WP * WQ) * (WP + WQ + 1)) ≤ 2 * sx * ((WP * WQ) * (WP + WQ + 1)) :=
      mul_le_mul_of_nonneg_right hB0 (mul_nonneg hW.le hWs)
    have hp2 : B₀ * (WP * WQ) ^ 2 ≤ 2 * sx * (WP * WQ) ^ 2 :=
      mul_le_mul_of_nonneg_right hB0 (sq_nonneg _)
    nlinarith [hEc, hp1, hp2]
  -- divide
  have hpos : (0 : ℝ) < (WP * WQ) ^ 2 * h * sx := by positivity
  have hstep1 : 48 * (A * Ec) / ((WP * WQ) ^ 2 * h * sx)
      ≤ 48 * (A * (4 * X * (WP * WQ) ^ 2 * sx)) / ((WP * WQ) ^ 2 * h * sx) := by
    gcongr
  refine hstep1.trans ?_
  have hval : 48 * (A * (4 * X * (WP * WQ) ^ 2 * sx)) / ((WP * WQ) ^ 2 * h * sx)
      = 192 * A * X / h := by
    field_simp
    try ring
  rw [hval]
  -- the prefactor
  have hAle : A ≤ 5 * Real.pi / 2 + 5 * Real.exp 1 * h / ω := by
    rw [hAdef]
    have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
    have hstep : 5 * Real.exp 1 / 2 * ratio ≤ 5 * Real.exp 1 / 2 * (2 * h / ω) :=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    have hval2 : 5 * Real.exp 1 / 2 * (2 * h / ω) = 5 * Real.exp 1 * h / ω := by
      field_simp
      try ring
    linarith [hstep, hval2.le, hval2.ge]
  have hfin : 192 * A * X / h
      ≤ 192 * (5 * Real.pi / 2 + 5 * Real.exp 1 * h / ω) * X / h := by
    gcongr
  refine hfin.trans (le_of_eq ?_)
  field_simp
  try ring

/-! ## The slope row vanishes -/

/-- **The slope-row majorant vanishes.**  The first factor is `O(1/h) + O(1/ω)` and the second
tends to one. -/
theorem tendsto_jointSlopeMajorant {c β a b : ℝ} (hc0 : 0 < c) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hb0 : 0 < b) (hb1 : b < 1) (ha0 : 0 < a) (hab : a < b) (hβb : β ≤ b) :
    Tendsto (fun x : ℝ =>
      (480 * Real.pi / scaledLength c β x + 960 * Real.exp 1 / (Real.log x) ^ (β / 2))
        * ((1 / Joint.mass (jointLongSet a b x) + 1 / Joint.mass (jointShortSet β x)
              + 1 / (Joint.mass (jointShortSet β x) * Joint.mass (jointLongSet a b x)))
            + ((jointShortSet β x).card : ℝ) * ((jointLongSet a b x).card : ℝ)
                / (Joint.mass (jointShortSet β x) * Joint.mass (jointLongSet a b x)
                  * Real.sqrt x)
            + 1)) atTop (𝓝 0) := by
  have hβ2 : (0 : ℝ) < β / 2 := by linarith
  have hWP := tendsto_jointShortMass hβ0 hβ1
  have hWQ := tendsto_jointLongMass ha0 hab
  have hinvP : Tendsto (fun x : ℝ => 1 / Joint.mass (jointShortSet β x)) atTop (𝓝 0) := by
    refine (hWP.inv_tendsto_atTop).congr fun x => ?_
    rw [Pi.inv_apply, ← one_div]
  have hinvQ : Tendsto (fun x : ℝ => 1 / Joint.mass (jointLongSet a b x)) atTop (𝓝 0) := by
    refine (hWQ.inv_tendsto_atTop).congr fun x => ?_
    rw [Pi.inv_apply, ← one_div]
  have hinvPQ : Tendsto (fun x : ℝ =>
      1 / (Joint.mass (jointShortSet β x) * Joint.mass (jointLongSet a b x)))
      atTop (𝓝 0) := by
    refine ((hWP.atTop_mul_atTop₀ hWQ).inv_tendsto_atTop).congr fun x => ?_
    rw [Pi.inv_apply, ← one_div]
  have hcards := tendsto_jointCards_div_sqrt hβ0 hβ1 hβb hb0 hb1 ha0 hab
  have hcross : Tendsto (fun x : ℝ =>
      ((jointShortSet β x).card : ℝ) * ((jointLongSet a b x).card : ℝ)
        / (Joint.mass (jointShortSet β x) * Joint.mass (jointLongSet a b x) * Real.sqrt x))
      atTop (𝓝 0) := by
    have hmul := hcards.mul hinvPQ
    rw [mul_zero] at hmul
    refine hmul.congr' ?_
    filter_upwards [hWP.eventually_gt_atTop 0, hWQ.eventually_gt_atTop 0,
      Filter.eventually_gt_atTop (1 : ℝ)] with x h1 h2 hx1
    have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
    field_simp
  -- the first factor
  have hinvh : Tendsto (fun x : ℝ => 1 / scaledLength c β x) atTop (𝓝 0) := by
    refine ((tendsto_scaledLength hc0 hβ0).inv_tendsto_atTop).congr fun x => ?_
    rw [Pi.inv_apply, ← one_div]
  have hω : Tendsto (fun x : ℝ => (Real.log x) ^ (β / 2)) atTop atTop :=
    (tendsto_rpow_atTop hβ2).comp Real.tendsto_log_atTop
  have hinvω : Tendsto (fun x : ℝ => 1 / (Real.log x) ^ (β / 2)) atTop (𝓝 0) := by
    refine (hω.inv_tendsto_atTop).congr fun x => ?_
    rw [Pi.inv_apply, ← one_div]
  have hfirst : Tendsto (fun x : ℝ =>
      480 * Real.pi / scaledLength c β x + 960 * Real.exp 1 / (Real.log x) ^ (β / 2))
      atTop (𝓝 0) := by
    have h1 := hinvh.const_mul (480 * Real.pi)
    have h2 := hinvω.const_mul (960 * Real.exp 1)
    have hsum := h1.add h2
    rw [show (480 * Real.pi) * 0 + (960 * Real.exp 1) * 0 = 0 by ring] at hsum
    refine hsum.congr fun x => ?_
    field_simp
  -- the second factor
  have hsecond : Tendsto (fun x : ℝ =>
      (1 / Joint.mass (jointLongSet a b x) + 1 / Joint.mass (jointShortSet β x)
          + 1 / (Joint.mass (jointShortSet β x) * Joint.mass (jointLongSet a b x)))
        + ((jointShortSet β x).card : ℝ) * ((jointLongSet a b x).card : ℝ)
            / (Joint.mass (jointShortSet β x) * Joint.mass (jointLongSet a b x) * Real.sqrt x)
        + 1) atTop (𝓝 1) := by
    have hbase := (((hinvQ.add hinvP).add hinvPQ).add hcross).add
      (tendsto_const_nhds (x := (1 : ℝ)) (f := (atTop : Filter ℝ)))
    rw [show (0 : ℝ) + 0 + 0 + 0 + 1 = 1 by ring] at hbase
    exact hbase
  have hmul := hfirst.mul hsecond
  rw [zero_mul] at hmul
  exact hmul

/-- **The slope row of the joint budget vanishes.** -/
theorem tendsto_jointSlopeRow {c β a b : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hβb : β ≤ b) (hb0 : 0 < b) (hb1 : b < 1) (ha0 : 0 < a) (hab : a < b)
    (hβa : β < a) :
    Tendsto (fun x : ℝ =>
      48 * ((5 * Real.pi / 2
            + 5 * Real.exp 1 / 2 * (((⌊Real.sqrt x + scaledLength c β x⌋₊ : ℕ) : ℝ)
                / jointExpiry c β x))
          * ∑ n ∈ fibreIndex x (scaledLength c β x),
              ‖jointOmegaCoeff (jointShortSet β x) (jointLongSet a b x) n‖ ^ 2)
        / (jointCut c β x
          * (Joint.mass (jointShortSet β x) * Joint.mass (jointLongSet a b x)) ^ 2
          * scaledLength c β x ^ 2)) atTop (𝓝 0) := by
  have hβ2 : (0 : ℝ) < β / 2 := by linarith
  have hWP := tendsto_jointShortMass hβ0 hβ1
  have hWQ := tendsto_jointLongMass ha0 hab
  refine squeeze_zero' ?_ ?_ (tendsto_jointSlopeMajorant hc0 hβ0 hβ1 hb0 hb1 ha0 hab hβb)
  · filter_upwards [Filter.eventually_gt_atTop (1 : ℝ), hWP.eventually_gt_atTop 0,
      hWQ.eventually_gt_atTop 0] with x hx1 hP0 hQ0
    have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
    have hh0 : (0 : ℝ) < scaledLength c β x := scaledLength_pos hc0 β x
    have hω : (0 : ℝ) < (Real.log x) ^ (β / 2) :=
      Real.rpow_pos_of_pos (Real.log_pos hx1) _
    have hcut : (0 : ℝ) < jointCut c β x := by
      rw [jointCut]; positivity
    have hexp : (0 : ℝ) < jointExpiry c β x := by
      rw [jointExpiry]; positivity
    have hE0 : (0 : ℝ) ≤ ∑ n ∈ fibreIndex x (scaledLength c β x),
        ‖jointOmegaCoeff (jointShortSet β x) (jointLongSet a b x) n‖ ^ 2 :=
      Finset.sum_nonneg fun n _ => by positivity
    have hpre : (0 : ℝ) ≤ 5 * Real.pi / 2
        + 5 * Real.exp 1 / 2 * (((⌊Real.sqrt x + scaledLength c β x⌋₊ : ℕ) : ℝ)
            / jointExpiry c β x) := by
      have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
      have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
      have hr : (0 : ℝ) ≤ ((⌊Real.sqrt x + scaledLength c β x⌋₊ : ℕ) : ℝ) / jointExpiry c β x :=
        div_nonneg (Nat.cast_nonneg _) hexp.le
      positivity
    positivity
  · filter_upwards [Filter.eventually_ge_atTop (4 : ℝ), hWP.eventually_gt_atTop 0,
      hWQ.eventually_gt_atTop 0, (tendsto_scaledLength hc0 hβ0).eventually_ge_atTop (1 : ℝ),
      scaledLength_le_sqrt hc1 hβ0 hβ1, eventually_jointSets_disjoint hβ0 hβ1 hβa]
      with x hx4 hP0 hQ0 hh1 hslsx hdisj
    have hx1 : (1 : ℝ) < x := by linarith
    have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
    have hω : (0 : ℝ) < (Real.log x) ^ (β / 2) :=
      Real.rpow_pos_of_pos (Real.log_pos hx1) _
    have hB0le : ((⌊Real.sqrt x + scaledLength c β x⌋₊ : ℕ) : ℝ) ≤ 2 * Real.sqrt x := by
      have hsl0 : (0 : ℝ) < scaledLength c β x := scaledLength_pos hc0 β x
      have := Nat.floor_le (by linarith : (0 : ℝ) ≤ Real.sqrt x + scaledLength c β x)
      linarith
    have hcutval : jointCut c β x = Real.sqrt x / scaledLength c β x := rfl
    have hexpval : jointExpiry c β x = jointCut c β x * (Real.log x) ^ (β / 2) := rfl
    have hexp0 : (0 : ℝ) < jointExpiry c β x := by
      rw [hexpval, hcutval]
      have hsl0 : (0 : ℝ) < scaledLength c β x := scaledLength_pos hc0 β x
      positivity
    have hratio0 : (0 : ℝ)
        ≤ ((⌊Real.sqrt x + scaledLength c β x⌋₊ : ℕ) : ℝ) / jointExpiry c β x :=
      div_nonneg (Nat.cast_nonneg _) hexp0.le
    have hratio : ((⌊Real.sqrt x + scaledLength c β x⌋₊ : ℕ) : ℝ) / jointExpiry c β x
        ≤ 2 * scaledLength c β x / (Real.log x) ^ (β / 2) := by
      have hsl0 : (0 : ℝ) < scaledLength c β x := scaledLength_pos hc0 β x
      rw [div_le_div_iff₀ hexp0 hω]
      have hTexp : 2 * scaledLength c β x * jointExpiry c β x
          = 2 * Real.sqrt x * (Real.log x) ^ (β / 2) := by
        rw [hexpval, hcutval]
        field_simp
        try ring
      rw [hTexp]
      nlinarith [hB0le, hω]
    have hEc := energy_jointOmegaCoeff_le_variance (jointShortSet_prime β x)
      (jointLongSet_prime a b x) hdisj (⌊Real.sqrt x + scaledLength c β x⌋₊)
    have hidx : fibreIndex x (scaledLength c β x)
        = Finset.Icc 1 ⌊Real.sqrt x + scaledLength c β x⌋₊ := rfl
    rw [← hidx] at hEc
    rw [hcutval]
    exact jointSlope_quotient_le hh1 hsx hP0 hQ0 (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      hB0le hratio0 hω hratio hEc

end

end RHTower.Sieve
