import GaloisForLFunctions.HTGeometry.FDNLS.CouplingCoefficient

/-!
# Decay and absolute summability of the quasi-Riesz coupling coefficients

Zhong--Malomed--Yan, arXiv:2407.12441, Section II A/D.

The paper computes the coupling coefficients `D_ℓ^{(α)}` of equation (10) only numerically for
general `α`, and records their large-`|ℓ|` asymptotics in equations (12) and (13).  What the exact
dispersion relation (33) actually needs is the *absolute summability* of the whole family, which the
paper never isolates.  This file supplies it, together with the explicit decay rate behind it.

Writing `J_ℓ = ∫_0^π sin(ℓ k) k^{α-1} dk` for the integral of the integrated-by-parts form
(equation (10), second form), the estimate is obtained by splitting `[0, π]` at `k = 1/ℓ`:

* on `[0, 1/ℓ]` one uses `|sin (ℓ k)| ≤ ℓ k`, giving `ℓ^{-α}/(α+1)`;
* on `[1/ℓ, π]` one integrates by parts once more — legitimately, since the singular point `0` has
  been excised — giving `2π/ℓ + 2ℓ^{-α}`.

Together `|J_ℓ| ≤ (2π + 3) ℓ^{-min(α,1)}`, hence `|D_ℓ^{(α)}| ≤ C_α ℓ^{-1-min(α,1)}`, which is
summable for every `α > 0`.

## Main results

* `abs_integral_sin_rpow_near`, `abs_integral_sin_rpow_far` — the two halves of the split.
* `abs_integral_sin_rpow` — `|J_ℓ| ≤ (2π + 3) ℓ^{-min(α,1)}`.
* `abs_quasiRieszCoupling_le` — `|D_ℓ^{(α)}| ≤ (α(2π+3)/π) ℓ^{-1-min(α,1)}` for `ℓ ≥ 1`.
* `quasiRieszCoupling_summable_abs`, `quasiRieszCoupling_summable` — absolute summability of the
  full two-sided family, for every Lévy index `α ∈ (0, 2]`.
-/

open MeasureTheory Set Filter Topology intervalIntegral

namespace GaloisForLFunctions.HTGeometry.FDNLS

/-- `(1/L)^y = L^{-y}` for `L > 0`. -/
theorem one_div_rpow_eq {L : ℝ} (hL : 0 < L) (y : ℝ) : (1 / L) ^ y = L ^ (-y) := by
  rw [one_div, Real.inv_rpow hL.le, ← Real.rpow_neg hL.le]

/-- The primitive used for the second integration by parts, away from the origin. -/
theorem hasDerivAt_cosRpowPrimitive {α L : ℝ} (hL : L ≠ 0) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun k : ℝ => -(Real.cos (L * k) * k ^ (α - 1)) / L)
      (Real.sin (L * x) * x ^ (α - 1) - (α - 1) / L * (Real.cos (L * x) * x ^ (α - 2))) x := by
  have h2 : HasDerivAt (fun k : ℝ => k ^ (α - 1)) ((α - 1) * x ^ (α - 1 - 1)) x :=
    Real.hasDerivAt_rpow_const (Or.inl hx)
  have h3 := (((hasDerivAt_cosLin L x).mul h2).neg).div_const L
  simp only [Pi.mul_def] at h3
  refine h3.congr_deriv ?_
  rw [show α - 1 - 1 = α - 2 by ring]
  field_simp
  ring

/-- Real powers are continuous away from the origin. -/
theorem continuousOn_rpow_pos {r : ℝ} {s : Set ℝ} (hs : ∀ x ∈ s, x ≠ 0) :
    ContinuousOn (fun x : ℝ => x ^ r) s := fun x hx =>
  (Real.continuousAt_rpow_const x r (Or.inl (hs x hx))).continuousWithinAt

/-! ## The near-origin piece -/

/-- On `[0, 1/L]` the oscillation is not yet effective, and the crude bound
`|sin (L k)| ≤ L k` already yields the full decay rate `L^{-α}`. -/
theorem abs_integral_sin_rpow_near {α : ℝ} (hα : 0 < α) {L : ℝ} (hL : 1 ≤ L) :
    |∫ k in (0:ℝ)..(1 / L), Real.sin (L * k) * k ^ (α - 1)| ≤ L ^ (-α) := by
  have hL0 : (0:ℝ) < L := lt_of_lt_of_le one_pos hL
  have hc : (0:ℝ) < 1 / L := by positivity
  have hstep1 : |∫ k in (0:ℝ)..(1 / L), Real.sin (L * k) * k ^ (α - 1)|
      ≤ ∫ k in (0:ℝ)..(1 / L), |Real.sin (L * k) * k ^ (α - 1)| :=
    intervalIntegral.abs_integral_le_integral_abs hc.le
  have hintabs :
      IntervalIntegrable (fun k : ℝ => |Real.sin (L * k) * k ^ (α - 1)|) volume 0 (1 / L) :=
    (sin_rpow_intervalIntegrable hα L 0 (1 / L)).abs
  have hintg : IntervalIntegrable (fun k : ℝ => L * k ^ α) volume 0 (1 / L) :=
    ((continuous_rpow_const hα.le).const_mul L).intervalIntegrable _ _
  have hptw : ∀ k ∈ Icc (0:ℝ) (1 / L), |Real.sin (L * k) * k ^ (α - 1)| ≤ L * k ^ α := by
    intro k hk
    rcases eq_or_lt_of_le hk.1 with rfl | hk0
    · have h0 : Real.sin (L * 0) = 0 := by simp
      rw [h0]
      simp only [zero_mul, abs_zero]
      positivity
    · have hsin : |Real.sin (L * k)| ≤ L * k := by
        calc |Real.sin (L * k)| ≤ |L * k| := Real.abs_sin_le_abs
        _ = L * k := abs_of_nonneg (by positivity)
      have hpow : |k ^ (α - 1)| = k ^ (α - 1) := abs_of_nonneg (Real.rpow_nonneg hk0.le _)
      have hmul : k * k ^ (α - 1) = k ^ α := by
        have h := Real.rpow_add hk0 1 (α - 1)
        rw [Real.rpow_one, show (1:ℝ) + (α - 1) = α by ring] at h
        exact h.symm
      rw [abs_mul, hpow]
      calc |Real.sin (L * k)| * k ^ (α - 1) ≤ (L * k) * k ^ (α - 1) :=
            mul_le_mul_of_nonneg_right hsin (Real.rpow_nonneg hk0.le _)
      _ = L * (k * k ^ (α - 1)) := by ring
      _ = L * k ^ α := by rw [hmul]
  have hstep2 : (∫ k in (0:ℝ)..(1 / L), |Real.sin (L * k) * k ^ (α - 1)|)
      ≤ ∫ k in (0:ℝ)..(1 / L), L * k ^ α :=
    intervalIntegral.integral_mono_on hc.le hintabs hintg hptw
  have hval : (∫ k in (0:ℝ)..(1 / L), L * k ^ α) = L * ((1 / L) ^ (α + 1) / (α + 1)) := by
    rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith : (-1:ℝ) < α)),
      Real.zero_rpow (by linarith : α + 1 ≠ 0)]
    ring
  have hkey : L * ((1 / L) ^ (α + 1)) = L ^ (-α) := by
    rw [one_div, Real.inv_rpow hL0.le]
    have h := Real.rpow_sub hL0 1 (α + 1)
    rw [Real.rpow_one, show (1:ℝ) - (α + 1) = -α by ring] at h
    rw [h, div_eq_mul_inv]
  have hfin : L * ((1 / L) ^ (α + 1) / (α + 1)) ≤ L ^ (-α) := by
    rw [show L * ((1 / L) ^ (α + 1) / (α + 1)) = (L * (1 / L) ^ (α + 1)) / (α + 1) by ring, hkey]
    exact div_le_self (Real.rpow_nonneg hL0.le _) (by linarith)
  linarith [hstep1, hstep2, hfin]

/-! ## The far piece -/

/-- On `[1/L, π]` the singular point has been excised, so a second integration by parts is
legitimate and produces the decay `2π/L + 2L^{-α}`. -/
theorem abs_integral_sin_rpow_far {α : ℝ} (hα2 : α ≤ 2) {L : ℝ} (hL : 1 ≤ L) :
    |∫ k in (1 / L)..Real.pi, Real.sin (L * k) * k ^ (α - 1)|
      ≤ 2 * Real.pi / L + 2 * L ^ (-α) := by
  have hL0 : (0:ℝ) < L := lt_of_lt_of_le one_pos hL
  have hpi3 : (3:ℝ) < Real.pi := Real.pi_gt_three
  set c : ℝ := 1 / L with hcdef
  have hc0 : (0:ℝ) < c := by positivity
  have hc1 : c ≤ 1 := by rw [hcdef, div_le_one hL0]; exact hL
  have hcpi : c ≤ Real.pi := by linarith
  have hmem : ∀ x ∈ uIcc c Real.pi, x ≠ 0 := by
    intro x hx
    rw [Set.uIcc_of_le hcpi] at hx
    exact ne_of_gt (lt_of_lt_of_le hc0 hx.1)
  have hmem' : ∀ x ∈ Icc c Real.pi, (0:ℝ) < x := fun x hx => lt_of_lt_of_le hc0 hx.1
  have hcont1 : ContinuousOn (fun k : ℝ => Real.sin (L * k) * k ^ (α - 1)) (uIcc c Real.pi) :=
    (continuous_sinLin L).continuousOn.mul (continuousOn_rpow_pos hmem)
  have hcont2 : ContinuousOn (fun k : ℝ => Real.cos (L * k) * k ^ (α - 2)) (uIcc c Real.pi) :=
    (continuous_cosLin L).continuousOn.mul (continuousOn_rpow_pos hmem)
  have hcont3 : ContinuousOn (fun k : ℝ => k ^ (α - 2)) (uIcc c Real.pi) :=
    continuousOn_rpow_pos hmem
  have hint1 : IntervalIntegrable (fun k : ℝ => Real.sin (L * k) * k ^ (α - 1)) volume c Real.pi :=
    hcont1.intervalIntegrable
  have hint2 : IntervalIntegrable (fun k : ℝ => Real.cos (L * k) * k ^ (α - 2)) volume c Real.pi :=
    hcont2.intervalIntegrable
  have hint3 : IntervalIntegrable (fun k : ℝ => k ^ (α - 2)) volume c Real.pi :=
    hcont3.intervalIntegrable
  have hintF : IntervalIntegrable
      (fun k : ℝ => Real.sin (L * k) * k ^ (α - 1)
        - (α - 1) / L * (Real.cos (L * k) * k ^ (α - 2))) volume c Real.pi :=
    hint1.sub (hint2.const_mul _)
  have hsub := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun k : ℝ => -(Real.cos (L * k) * k ^ (α - 1)) / L)
    (fun x hx => hasDerivAt_cosRpowPrimitive (ne_of_gt hL0) (hmem x hx)) hintF
  rw [intervalIntegral.integral_sub hint1 (hint2.const_mul _),
    intervalIntegral.integral_const_mul] at hsub
  set X : ℝ := ∫ k in c..Real.pi, Real.cos (L * k) * k ^ (α - 2) with hX
  set A : ℝ := Real.pi ^ (α - 1) with hA
  set B : ℝ := c ^ (α - 1) with hB
  have hA0 : (0:ℝ) ≤ A := Real.rpow_nonneg (by linarith) _
  have hB0 : (0:ℝ) ≤ B := Real.rpow_nonneg hc0.le _
  have hApi : A ≤ Real.pi := by
    calc A ≤ Real.pi ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    _ = Real.pi := Real.rpow_one _
  have hBval : B / L = L ^ (-α) := by
    rw [hB, hcdef, one_div_rpow_eq hL0, show -(α - 1) = 1 - α by ring]
    have h := Real.rpow_add hL0 (1 - α) (-1)
    rw [show (1 - α) + (-1 : ℝ) = -α by ring, Real.rpow_neg_one] at h
    rw [h, div_eq_mul_inv]
  have hmain : ∫ k in c..Real.pi, Real.sin (L * k) * k ^ (α - 1)
      = (-(Real.cos (L * Real.pi) * A) / L - -(Real.cos (L * c) * B) / L)
        + (α - 1) / L * X := by
    rw [hA, hB, hX]; linarith [hsub]
  rw [hmain]
  have hb1 : |(-(Real.cos (L * Real.pi) * A) / L)| ≤ Real.pi / L := by
    rw [abs_div, abs_of_pos hL0, abs_neg, abs_mul, abs_of_nonneg hA0]
    refine (div_le_div_iff_of_pos_right hL0).mpr ?_
    calc |Real.cos (L * Real.pi)| * A ≤ 1 * A :=
          mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) hA0
    _ = A := one_mul A
    _ ≤ Real.pi := hApi
  have hb2 : |(-(Real.cos (L * c) * B) / L)| ≤ L ^ (-α) := by
    rw [abs_div, abs_of_pos hL0, abs_neg, abs_mul, abs_of_nonneg hB0, ← hBval]
    refine (div_le_div_iff_of_pos_right hL0).mpr ?_
    calc |Real.cos (L * c)| * B ≤ 1 * B :=
          mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) hB0
    _ = B := one_mul B
  have hXbound : |X| ≤ ∫ k in c..Real.pi, k ^ (α - 2) := by
    calc |X| ≤ ∫ k in c..Real.pi, |Real.cos (L * k) * k ^ (α - 2)| :=
          intervalIntegral.abs_integral_le_integral_abs hcpi
    _ ≤ ∫ k in c..Real.pi, k ^ (α - 2) := by
          refine intervalIntegral.integral_mono_on hcpi hint2.abs hint3 fun k hk => ?_
          have hk0 : (0:ℝ) < k := hmem' k hk
          rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hk0.le _)]
          calc |Real.cos (L * k)| * k ^ (α - 2) ≤ 1 * k ^ (α - 2) :=
                mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) (Real.rpow_nonneg hk0.le _)
          _ = k ^ (α - 2) := one_mul _
  have hYnonneg : (0:ℝ) ≤ ∫ k in c..Real.pi, k ^ (α - 2) := by
    refine intervalIntegral.integral_nonneg hcpi fun k hk => Real.rpow_nonneg ?_ _
    exact (hmem' k hk).le
  have hb3 : |(α - 1) / L * X| ≤ Real.pi / L + L ^ (-α) := by
    set Y : ℝ := ∫ k in c..Real.pi, k ^ (α - 2) with hY
    rcases eq_or_ne α 1 with hα1 | hα1
    · have hz : (α - 1) / L * X = 0 := by rw [hα1]; simp
      rw [hz, abs_zero]
      have h1 : (0:ℝ) ≤ Real.pi / L := by positivity
      have h2 : (0:ℝ) ≤ L ^ (-α) := Real.rpow_nonneg hL0.le _
      linarith
    · have hne : α - 1 ≠ 0 := sub_ne_zero.mpr hα1
      have hYval : (α - 1) * Y = A - B := by
        have hne2 : α - 2 ≠ -1 := by intro h; apply hne; linarith
        have h0 : (0:ℝ) ∉ uIcc c Real.pi := by
          rw [Set.uIcc_of_le hcpi]
          intro h
          exact absurd h.1 (not_le.mpr hc0)
        have hI := integral_rpow (a := c) (b := Real.pi) (r := α - 2) (Or.inr ⟨hne2, h0⟩)
        rw [show α - 2 + 1 = α - 1 by ring] at hI
        rw [hY, hI, hA, hB]
        field_simp
      have habs : |α - 1| * Y = |A - B| := by
        rw [← abs_of_nonneg hYnonneg, ← abs_mul, hYval]
      have hstep : |(α - 1) / L * X| ≤ |α - 1| / L * Y := by
        rw [abs_mul, abs_div, abs_of_pos hL0]
        exact mul_le_mul_of_nonneg_left hXbound (by positivity)
      have hfin : |α - 1| / L * Y = |A - B| / L := by rw [div_mul_eq_mul_div, habs]
      rw [hfin] at hstep
      refine hstep.trans ?_
      have h1 : |A - B| ≤ A + B :=
        (abs_sub A B).trans (by rw [abs_of_nonneg hA0, abs_of_nonneg hB0])
      calc |A - B| / L ≤ (A + B) / L := (div_le_div_iff_of_pos_right hL0).mpr h1
      _ = A / L + B / L := by ring
      _ ≤ Real.pi / L + L ^ (-α) := by
            rw [hBval]
            have h2 : A / L ≤ Real.pi / L := (div_le_div_iff_of_pos_right hL0).mpr hApi
            linarith
  set P1 : ℝ := -(Real.cos (L * Real.pi) * A) / L with hP1
  set P2 : ℝ := -(Real.cos (L * c) * B) / L with hP2
  set P3 : ℝ := (α - 1) / L * X with hP3
  calc |P1 - P2 + P3| ≤ |P1 - P2| + |P3| := abs_add_le _ _
  _ ≤ (|P1| + |P2|) + |P3| := add_le_add (abs_sub P1 P2) le_rfl
  _ ≤ (Real.pi / L + L ^ (-α)) + (Real.pi / L + L ^ (-α)) :=
        add_le_add (add_le_add hb1 hb2) hb3
  _ = 2 * Real.pi / L + 2 * L ^ (-α) := by ring

/-! ## The combined decay estimate -/

/-- **The decay of the oscillatory integral.**  For every Lévy index `α ∈ (0, 2]` and every
`L ≥ 1`, `|∫_0^π sin (L k) k^{α-1} dk| ≤ (2π + 3) L^{-min(α,1)}`. -/
theorem abs_integral_sin_rpow {α : ℝ} (hα0 : 0 < α) (hα2 : α ≤ 2) {L : ℝ} (hL : 1 ≤ L) :
    |∫ k in (0:ℝ)..Real.pi, Real.sin (L * k) * k ^ (α - 1)|
      ≤ (2 * Real.pi + 3) * L ^ (-(min α 1)) := by
  have hL0 : (0:ℝ) < L := lt_of_lt_of_le one_pos hL
  have hsplit : (∫ k in (0:ℝ)..(1 / L), Real.sin (L * k) * k ^ (α - 1))
      + (∫ k in (1 / L)..Real.pi, Real.sin (L * k) * k ^ (α - 1))
      = ∫ k in (0:ℝ)..Real.pi, Real.sin (L * k) * k ^ (α - 1) :=
    intervalIntegral.integral_add_adjacent_intervals
      (sin_rpow_intervalIntegrable hα0 L 0 (1 / L))
      (sin_rpow_intervalIntegrable hα0 L (1 / L) Real.pi)
  have hβ1 : min α 1 ≤ 1 := min_le_right _ _
  have hβα : min α 1 ≤ α := min_le_left _ _
  have hmono1 : L ^ (-α) ≤ L ^ (-(min α 1)) :=
    Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  have hmono2 : (1:ℝ) / L ≤ L ^ (-(min α 1)) := by
    have h1 : L ^ (-(1:ℝ)) ≤ L ^ (-(min α 1)) :=
      Real.rpow_le_rpow_of_exponent_le hL (by linarith)
    rwa [Real.rpow_neg_one, ← one_div] at h1
  have hnear := abs_integral_sin_rpow_near hα0 hL
  have hfar := abs_integral_sin_rpow_far hα2 hL
  have hpi0 : (0:ℝ) < Real.pi := Real.pi_pos
  have htotal : |∫ k in (0:ℝ)..Real.pi, Real.sin (L * k) * k ^ (α - 1)|
      ≤ L ^ (-α) + (2 * Real.pi / L + 2 * L ^ (-α)) := by
    rw [← hsplit]
    exact (abs_add_le _ _).trans (add_le_add hnear hfar)
  have hpiL : 2 * Real.pi / L = 2 * Real.pi * (1 / L) := by ring
  have hbound : L ^ (-α) + (2 * Real.pi / L + 2 * L ^ (-α))
      ≤ (2 * Real.pi + 3) * L ^ (-(min α 1)) := by
    rw [hpiL]
    have h1 : 2 * Real.pi * (1 / L) ≤ 2 * Real.pi * L ^ (-(min α 1)) := by
      exact mul_le_mul_of_nonneg_left hmono2 (by positivity)
    nlinarith [hmono1, h1]
  linarith [htotal, hbound]

/-- **The decay of the coupling coefficients.**  For every Lévy index `α ∈ (0, 2]` and every site
separation `ℓ ≥ 1`, `|D_ℓ^{(α)}| ≤ (α(2π+3)/π) ℓ^{-1-min(α,1)}`. -/
theorem abs_quasiRieszCoupling_le {α : ℝ} (hα0 : 0 < α) (hα2 : α ≤ 2) {ℓ : ℤ} (hℓ : 1 ≤ ℓ) :
    |quasiRieszCoupling α ℓ|
      ≤ (α * (2 * Real.pi + 3) / Real.pi) * (ℓ : ℝ) ^ (-(1 + min α 1)) := by
  have hpi0 : (0:ℝ) < Real.pi := Real.pi_pos
  have hL : (1:ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ
  have hL0 : (0:ℝ) < (ℓ : ℝ) := lt_of_lt_of_le one_pos hL
  have hℓ0 : ℓ ≠ 0 := by omega
  rw [quasiRieszCoupling_integration_by_parts hα0 hℓ0]
  rw [abs_mul, abs_neg, abs_div, abs_of_pos hα0, abs_of_pos (by positivity : (0:ℝ) < Real.pi * ℓ)]
  have hJ := abs_integral_sin_rpow hα0 hα2 hL
  have hsplit : ((ℓ : ℝ)) ^ (-(1 + min α 1)) = ((ℓ : ℝ)) ^ (-(1:ℝ)) * ((ℓ : ℝ)) ^ (-(min α 1)) := by
    rw [← Real.rpow_add hL0]
    ring_nf
  have hstep : α / (Real.pi * (ℓ : ℝ))
      * |∫ k in (0:ℝ)..Real.pi, Real.sin ((ℓ : ℝ) * k) * k ^ (α - 1)|
      ≤ α / (Real.pi * (ℓ : ℝ)) * ((2 * Real.pi + 3) * ((ℓ : ℝ)) ^ (-(min α 1))) :=
    mul_le_mul_of_nonneg_left hJ (by positivity)
  refine hstep.trans (le_of_eq ?_)
  rw [hsplit, Real.rpow_neg_one]
  field_simp

/-! ## Absolute summability -/

/-- The `p`-series bound in the shape needed below. -/
theorem summable_nat_succ_rpow {p : ℝ} (hp : 1 < p) :
    Summable fun n : ℕ => (((n : ℝ) + 1)) ^ (-p) := by
  have hbase : Summable fun n : ℕ => (((n : ℝ)) ^ p)⁻¹ := Real.summable_nat_rpow_inv.mpr hp
  have hshift : Summable fun n : ℕ => ((((n + 1 : ℕ) : ℝ)) ^ p)⁻¹ :=
    (summable_nat_add_iff 1).mpr hbase
  refine hshift.congr fun n => ?_
  have h0 : (0:ℝ) ≤ ((n : ℝ) + 1) := by positivity
  rw [Real.rpow_neg h0]
  norm_num

/-- **Absolute summability of the quasi-Riesz coupling family.**  For every Lévy index
`α ∈ (0, 2]` the two-sided family `(D_ℓ^{(α)})_{ℓ ∈ ℤ}` is absolutely summable.  This is the
input that turns the formal series of equation (32) into a genuine convergent sum. -/
theorem quasiRieszCoupling_summable_abs {α : ℝ} (hα0 : 0 < α) (hα2 : α ≤ 2) :
    Summable fun ℓ : ℤ => |quasiRieszCoupling α ℓ| := by
  have hpi0 : (0:ℝ) < Real.pi := Real.pi_pos
  set C : ℝ := α * (2 * Real.pi + 3) / Real.pi with hC
  have hC0 : (0:ℝ) ≤ C := by positivity
  have hp : (1:ℝ) < 1 + min α 1 := by
    have : (0:ℝ) < min α 1 := lt_min hα0 one_pos
    linarith
  have hmajor : Summable fun n : ℕ => C * (((n : ℝ) + 1)) ^ (-(1 + min α 1)) :=
    (summable_nat_succ_rpow hp).mul_left C
  have hpos : Summable fun n : ℕ => |quasiRieszCoupling α ((n : ℤ) + 1)| := by
    refine hmajor.of_nonneg_of_le (fun n => abs_nonneg _) fun n => ?_
    have hle := abs_quasiRieszCoupling_le hα0 hα2 (ℓ := (n : ℤ) + 1) (by omega)
    have hcast : (((n : ℤ) + 1 : ℤ) : ℝ) = ((n : ℝ) + 1) := by push_cast; ring
    rwa [hcast] at hle
  have hnat : Summable fun n : ℕ => |quasiRieszCoupling α (n : ℤ)| := by
    refine (summable_nat_add_iff 1).mp ?_
    refine hpos.congr fun n => ?_
    congr 2
  have hneg : Summable fun n : ℕ => |quasiRieszCoupling α (-(n : ℤ))| := by
    refine hnat.congr fun n => ?_
    rw [quasiRieszCoupling_neg]
  exact Summable.of_nat_of_neg hnat hneg

/-- The coupling family is summable. -/
theorem quasiRieszCoupling_summable {α : ℝ} (hα0 : 0 < α) (hα2 : α ≤ 2) :
    Summable fun ℓ : ℤ => quasiRieszCoupling α ℓ :=
  Summable.of_abs (quasiRieszCoupling_summable_abs hα0 hα2)

end GaloisForLFunctions.HTGeometry.FDNLS
