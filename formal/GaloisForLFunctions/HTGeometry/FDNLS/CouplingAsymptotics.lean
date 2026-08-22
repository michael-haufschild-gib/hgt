import GaloisForLFunctions.HTGeometry.FDNLS.MellinSine
import GaloisForLFunctions.HTGeometry.FDNLS.CouplingDecay

/-!
# Large-distance asymptotics of the quasi-Riesz coupling coefficients

Zhong--Malomed--Yan, arXiv:2407.12441, Section II A, equations (12) and (13).

Below the crossover `α = 1` the coupling decays like `|ℓ|^{-α-1}` with the Mellin-sine constant,

`D_ℓ^{(α)} ∼ -(α Γ(α)/π) sin(πα/2) |ℓ|^{-α-1}`  (equation (12)),

while above it the decay is governed by the endpoint `k = π` of the symbol and becomes the
alternating inverse square

`D_ℓ^{(α)} ∼ (-1)^ℓ α π^{α-2} ℓ^{-2}`  (equation (13)).

The first limit is the Mellin transform of the sine after the rescaling `k = s/ℓ`; the second is a
second integration by parts, whose boundary term at `k = 0` vanishes precisely because `α > 1`, plus
the decay of `∫_0^π cos(ℓk) k^{α-2} dk`, which is proved here by the same split-at-`1/ℓ` estimate
that governs the coupling itself.

## Main results

* `abs_integral_cos_rpow_le` — the decay of `∫_0^π cos(Lk) k^β dk` for `-1 < β ≤ 0`.
* `integral_sin_rpow_scale` — the rescaling `k = s/L`.
* `tendsto_quasiRieszCoupling_subcritical` — **equation (12)**.
* `tendsto_quasiRieszCoupling_supercritical` — **equation (13)**.
-/

open MeasureTheory Set Filter Topology intervalIntegral

namespace GaloisForLFunctions.HTGeometry.FDNLS

/-! ## The cosine integral with a mildly singular weight -/

theorem cos_rpow_intervalIntegrable' {β : ℝ} (hβ : -1 < β) (L a b : ℝ) :
    IntervalIntegrable (fun k : ℝ => Real.cos (L * k) * k ^ β) volume a b := by
  have hbase : IntervalIntegrable (fun x : ℝ => x ^ β) volume a b := intervalIntegrable_rpow' hβ
  refine hbase.mono_fun ?_ ?_
  · exact ((continuous_cosLin L).measurable.mul (measurable_id.pow_const β)).aestronglyMeasurable
  · filter_upwards with k
    simp only [norm_mul, Real.norm_eq_abs]
    nlinarith [Real.abs_cos_le_one (L * k), abs_nonneg (k ^ β), abs_nonneg (Real.cos (L * k))]

/-- **The decay of the cosine integral.**  For `-1 < β ≤ 0` the weight `k^β` is bounded by one on
`[1/L, π]`, and splitting at `1/L` gives an explicit rate. -/
theorem abs_integral_cos_rpow_le {β L : ℝ} (hβ0 : -1 < β) (hβ1 : β ≤ 0) (hL : 1 ≤ L) :
    |∫ k in (0:ℝ)..Real.pi, Real.cos (L * k) * k ^ β|
      ≤ (1 / (β + 1) + 2) * L ^ (-(β + 1)) + 2 / L := by
  have hL0 : (0:ℝ) < L := lt_of_lt_of_le one_pos hL
  have hpi3 : (3:ℝ) < Real.pi := Real.pi_gt_three
  have hβ1' : (0:ℝ) < β + 1 := by linarith
  set c : ℝ := 1 / L with hcdef
  have hc0 : (0:ℝ) < c := by positivity
  have hc1 : c ≤ 1 := by rw [hcdef, div_le_one hL0]; exact hL
  have hcpi : c ≤ Real.pi := by linarith
  have hmem : ∀ x ∈ uIcc c Real.pi, x ≠ 0 := by
    intro x hx
    rw [Set.uIcc_of_le hcpi] at hx
    exact ne_of_gt (lt_of_lt_of_le hc0 hx.1)
  have hmem' : ∀ x ∈ Icc c Real.pi, (0:ℝ) < x := fun x hx => lt_of_lt_of_le hc0 hx.1
  -- the near piece
  have hnear : |∫ k in (0:ℝ)..c, Real.cos (L * k) * k ^ β| ≤ 1 / (β + 1) * L ^ (-(β + 1)) := by
    have hstep1 : |∫ k in (0:ℝ)..c, Real.cos (L * k) * k ^ β|
        ≤ ∫ k in (0:ℝ)..c, |Real.cos (L * k) * k ^ β| :=
      intervalIntegral.abs_integral_le_integral_abs hc0.le
    have hbase : IntervalIntegrable (fun x : ℝ => x ^ β) volume 0 c := intervalIntegrable_rpow' hβ0
    have hptw : ∀ k ∈ Icc (0:ℝ) c, |Real.cos (L * k) * k ^ β| ≤ k ^ β := by
      intro k hk
      rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hk.1 _)]
      nlinarith [Real.abs_cos_le_one (L * k), Real.rpow_nonneg hk.1 β,
        abs_nonneg (Real.cos (L * k))]
    have hstep2 : (∫ k in (0:ℝ)..c, |Real.cos (L * k) * k ^ β|) ≤ ∫ k in (0:ℝ)..c, k ^ β :=
      intervalIntegral.integral_mono_on hc0.le
        (cos_rpow_intervalIntegrable' hβ0 L 0 c).abs hbase hptw
    have hval : (∫ k in (0:ℝ)..c, k ^ β) = c ^ (β + 1) / (β + 1) := by
      rw [integral_rpow (Or.inl hβ0), Real.zero_rpow (by linarith)]
      ring
    have hceq : c ^ (β + 1) = L ^ (-(β + 1)) := by
      rw [hcdef, one_div_rpow_eq hL0]
    rw [hval, hceq] at hstep2
    calc |∫ k in (0:ℝ)..c, Real.cos (L * k) * k ^ β| ≤ L ^ (-(β + 1)) / (β + 1) := by linarith
    _ = 1 / (β + 1) * L ^ (-(β + 1)) := by ring
  -- the far piece
  have hcont1 : ContinuousOn (fun k : ℝ => Real.cos (L * k) * k ^ β) (uIcc c Real.pi) :=
    (continuous_cosLin L).continuousOn.mul (continuousOn_rpow_pos hmem)
  have hcont2 : ContinuousOn (fun k : ℝ => Real.sin (L * k) * k ^ (β - 1)) (uIcc c Real.pi) :=
    (continuous_sinLin L).continuousOn.mul (continuousOn_rpow_pos hmem)
  have hcont3 : ContinuousOn (fun k : ℝ => k ^ (β - 1)) (uIcc c Real.pi) :=
    continuousOn_rpow_pos hmem
  have hint1 : IntervalIntegrable (fun k : ℝ => Real.cos (L * k) * k ^ β) volume c Real.pi :=
    hcont1.intervalIntegrable
  have hint2 : IntervalIntegrable (fun k : ℝ => Real.sin (L * k) * k ^ (β - 1)) volume c Real.pi :=
    hcont2.intervalIntegrable
  have hint3 : IntervalIntegrable (fun k : ℝ => k ^ (β - 1)) volume c Real.pi :=
    hcont3.intervalIntegrable
  have hintF : IntervalIntegrable
      (fun k : ℝ => Real.cos (L * k) * k ^ β
        + β / L * (Real.sin (L * k) * k ^ (β - 1))) volume c Real.pi :=
    hint1.add (hint2.const_mul _)
  have hsub := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun k : ℝ => Real.sin (L * k) * k ^ β / L)
    (fun x hx => hasDerivAt_sinRpowPrimitive (ne_of_gt hL0) (hmem x hx)) hintF
  rw [intervalIntegral.integral_add hint1 (hint2.const_mul _),
    intervalIntegral.integral_const_mul] at hsub
  set X : ℝ := ∫ k in c..Real.pi, Real.sin (L * k) * k ^ (β - 1) with hX
  set A : ℝ := Real.pi ^ β with hA
  set B : ℝ := c ^ β with hB
  have hA0 : (0:ℝ) ≤ A := Real.rpow_nonneg (by linarith) _
  have hB0 : (0:ℝ) ≤ B := Real.rpow_nonneg hc0.le _
  have hAone : A ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) hβ1
  have hBval : B / L = L ^ (-(β + 1)) := by
    rw [hB, hcdef, one_div_rpow_eq hL0]
    have h := Real.rpow_add hL0 (-β) (-1)
    rw [show (-β) + (-1 : ℝ) = -(β + 1) by ring, Real.rpow_neg_one] at h
    rw [h, div_eq_mul_inv]
  have hfar : |∫ k in c..Real.pi, Real.cos (L * k) * k ^ β|
      ≤ 2 / L + 2 * L ^ (-(β + 1)) := by
    have hmain : (∫ k in c..Real.pi, Real.cos (L * k) * k ^ β)
        = (Real.sin (L * Real.pi) * A / L - Real.sin (L * c) * B / L) - β / L * X := by
      rw [hA, hB, hX]; linarith [hsub]
    rw [hmain]
    have hb1 : |Real.sin (L * Real.pi) * A / L| ≤ 1 / L := by
      rw [abs_div, abs_of_pos hL0, abs_mul, abs_of_nonneg hA0]
      refine (div_le_div_iff_of_pos_right hL0).mpr ?_
      nlinarith [Real.abs_sin_le_one (L * Real.pi), abs_nonneg (Real.sin (L * Real.pi))]
    have hb2 : |Real.sin (L * c) * B / L| ≤ L ^ (-(β + 1)) := by
      rw [abs_div, abs_of_pos hL0, abs_mul, abs_of_nonneg hB0, ← hBval]
      refine (div_le_div_iff_of_pos_right hL0).mpr ?_
      nlinarith [Real.abs_sin_le_one (L * c), abs_nonneg (Real.sin (L * c))]
    have hXbound : |X| ≤ ∫ k in c..Real.pi, k ^ (β - 1) := by
      calc |X| ≤ ∫ k in c..Real.pi, |Real.sin (L * k) * k ^ (β - 1)| :=
            intervalIntegral.abs_integral_le_integral_abs hcpi
      _ ≤ ∫ k in c..Real.pi, k ^ (β - 1) := by
            refine intervalIntegral.integral_mono_on hcpi hint2.abs hint3 fun k hk => ?_
            have hk0 : (0:ℝ) < k := hmem' k hk
            rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hk0.le _)]
            nlinarith [Real.abs_sin_le_one (L * k), Real.rpow_nonneg hk0.le (β - 1),
              abs_nonneg (Real.sin (L * k))]
    have hYnonneg : (0:ℝ) ≤ ∫ k in c..Real.pi, k ^ (β - 1) :=
      intervalIntegral.integral_nonneg hcpi fun k hk => Real.rpow_nonneg (hmem' k hk).le _
    have hb3 : |β / L * X| ≤ 1 / L + L ^ (-(β + 1)) := by
      set Y : ℝ := ∫ k in c..Real.pi, k ^ (β - 1) with hY
      rcases eq_or_ne β 0 with hβ | hβ
      · have hz : β / L * X = 0 := by rw [hβ]; simp
        rw [hz, abs_zero]
        have h1 : (0:ℝ) ≤ 1 / L := by positivity
        have h2 : (0:ℝ) ≤ L ^ (-(β + 1)) := Real.rpow_nonneg hL0.le _
        linarith
      · have hne2 : β - 1 ≠ -1 := by intro h; apply hβ; linarith
        have h0 : (0:ℝ) ∉ uIcc c Real.pi := by
          rw [Set.uIcc_of_le hcpi]
          intro h
          exact absurd h.1 (not_le.mpr hc0)
        have hI := integral_rpow (a := c) (b := Real.pi) (r := β - 1) (Or.inr ⟨hne2, h0⟩)
        rw [show β - 1 + 1 = β by ring] at hI
        have hYval : β * Y = A - B := by
          rw [hY, hI, hA, hB]
          field_simp
        have habs : |β| * Y = |A - B| := by
          rw [← abs_of_nonneg hYnonneg, ← abs_mul, hYval]
        have hstep : |β / L * X| ≤ |β| / L * Y := by
          rw [abs_mul, abs_div, abs_of_pos hL0]
          exact mul_le_mul_of_nonneg_left hXbound (by positivity)
        have hfin : |β| / L * Y = |A - B| / L := by rw [div_mul_eq_mul_div, habs]
        rw [hfin] at hstep
        refine hstep.trans ?_
        have h1 : |A - B| ≤ A + B :=
          (abs_sub A B).trans (by rw [abs_of_nonneg hA0, abs_of_nonneg hB0])
        calc |A - B| / L ≤ (A + B) / L := (div_le_div_iff_of_pos_right hL0).mpr h1
        _ = A / L + B / L := by ring
        _ ≤ 1 / L + L ^ (-(β + 1)) := by
              rw [hBval]
              have : A / L ≤ 1 / L := (div_le_div_iff_of_pos_right hL0).mpr hAone
              linarith
    calc |(Real.sin (L * Real.pi) * A / L - Real.sin (L * c) * B / L) - β / L * X|
        ≤ |Real.sin (L * Real.pi) * A / L - Real.sin (L * c) * B / L| + |β / L * X| :=
          abs_sub _ _
    _ ≤ (|Real.sin (L * Real.pi) * A / L| + |Real.sin (L * c) * B / L|) + |β / L * X| :=
          add_le_add (abs_sub _ _) le_rfl
    _ ≤ (1 / L + L ^ (-(β + 1))) + (1 / L + L ^ (-(β + 1))) :=
          add_le_add (add_le_add hb1 hb2) hb3
    _ = 2 / L + 2 * L ^ (-(β + 1)) := by ring
  have hsplit : (∫ k in (0:ℝ)..c, Real.cos (L * k) * k ^ β)
      + (∫ k in c..Real.pi, Real.cos (L * k) * k ^ β)
      = ∫ k in (0:ℝ)..Real.pi, Real.cos (L * k) * k ^ β :=
    intervalIntegral.integral_add_adjacent_intervals
      (cos_rpow_intervalIntegrable' hβ0 L 0 c) (cos_rpow_intervalIntegrable' hβ0 L c Real.pi)
  rw [← hsplit]
  refine (abs_add_le _ _).trans ?_
  linarith [hnear, hfar]

/-! ## The subcritical asymptotics -/

/-- The rescaling `k = s/L` of the oscillatory integral. -/
theorem integral_sin_rpow_scale {α L : ℝ} (hL : 0 < L) :
    (∫ k in (0:ℝ)..Real.pi, Real.sin (L * k) * k ^ (α - 1))
      = L ^ (-α) * ∫ s in (0:ℝ)..(L * Real.pi), s ^ (α - 1) * Real.sin s := by
  have hcomp := intervalIntegral.integral_comp_mul_left
    (a := (0:ℝ)) (b := Real.pi) (c := L)
    (fun s : ℝ => s ^ (α - 1) * Real.sin s) (ne_of_gt hL)
  rw [mul_zero] at hcomp
  have hleft : (∫ k in (0:ℝ)..Real.pi, (L * k) ^ (α - 1) * Real.sin (L * k))
      = L ^ (α - 1) * ∫ k in (0:ℝ)..Real.pi, Real.sin (L * k) * k ^ (α - 1) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun k hk => ?_
    rw [Set.uIcc_of_le Real.pi_pos.le] at hk
    rw [Real.mul_rpow hL.le hk.1]
    ring
  rw [hleft, smul_eq_mul] at hcomp
  have hLpow : L ^ (α - 1) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hL _)
  have hkey : L ^ (α - 1) * (L ^ (-α) * ∫ s in (0:ℝ)..(L * Real.pi), s ^ (α - 1) * Real.sin s)
      = L⁻¹ * ∫ s in (0:ℝ)..(L * Real.pi), s ^ (α - 1) * Real.sin s := by
    have h := Real.rpow_add hL (α - 1) (-α)
    rw [show (α - 1) + -α = (-1 : ℝ) by ring, Real.rpow_neg_one] at h
    rw [← mul_assoc, ← h]
  rw [← hkey] at hcomp
  exact mul_left_cancel₀ hLpow hcomp

/-- **Equation (12).**  For `0 < α < 1` the coupling coefficients decay like `ℓ^{-α-1}` with the
Mellin-sine constant. -/
theorem tendsto_quasiRieszCoupling_subcritical {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    Tendsto (fun ℓ : ℕ => ((ℓ : ℝ)) ^ (α + 1) * quasiRieszCoupling α (ℓ : ℤ)) atTop
      (𝓝 (-(α * Real.Gamma α / Real.pi) * Real.sin (Real.pi * α / 2))) := by
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have hval : ∀ ℓ : ℕ, 1 ≤ ℓ →
      ((ℓ : ℝ)) ^ (α + 1) * quasiRieszCoupling α (ℓ : ℤ)
        = -(α / Real.pi) * ∫ s in (0:ℝ)..((ℓ : ℝ) * Real.pi), s ^ (α - 1) * Real.sin s := by
    intro ℓ hℓ
    have hL : (0:ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ
    have hℓ0 : (ℓ : ℤ) ≠ 0 := by
      simp only [ne_eq, Int.natCast_eq_zero]
      omega
    rw [quasiRieszCoupling_integration_by_parts hα0 hℓ0]
    have hcast : (((ℓ : ℤ) : ℝ)) = ((ℓ : ℝ)) := by push_cast; ring
    rw [hcast, integral_sin_rpow_scale hL]
    set Y : ℝ := ∫ s in (0:ℝ)..((ℓ : ℝ) * Real.pi), s ^ (α - 1) * Real.sin s with hY
    have hpow : ((ℓ : ℝ)) ^ (α + 1) * ((ℓ : ℝ)) ^ (-α) = (ℓ : ℝ) := by
      rw [← Real.rpow_add hL, show (α + 1) + -α = (1:ℝ) by ring, Real.rpow_one]
    have hne : ((ℓ : ℝ)) ≠ 0 := ne_of_gt hL
    have hpi' : Real.pi ≠ 0 := ne_of_gt hpi
    have hstep : ((ℓ : ℝ)) ^ (α + 1) * (-(α / (Real.pi * ((ℓ : ℝ)))) * (((ℓ : ℝ)) ^ (-α) * Y))
        = -(α / Real.pi) * ((((ℓ : ℝ)) ^ (α + 1) * ((ℓ : ℝ)) ^ (-α)) * Y) * ((ℓ : ℝ))⁻¹ := by
      field_simp
    rw [hstep, hpow]
    field_simp
  have hlim : Tendsto (fun ℓ : ℕ => ∫ s in (0:ℝ)..((ℓ : ℝ) * Real.pi), s ^ (α - 1) * Real.sin s)
      atTop (𝓝 (Real.Gamma α * Real.sin (Real.pi * α / 2))) := by
    refine (tendsto_integral_rpow_mul_sin hα0 hα1).comp ?_
    exact Filter.Tendsto.atTop_mul_const hpi tendsto_natCast_atTop_atTop
  have hfin := hlim.const_mul (-(α / Real.pi))
  have heqval : -(α * Real.Gamma α / Real.pi) * Real.sin (Real.pi * α / 2)
      = -(α / Real.pi) * (Real.Gamma α * Real.sin (Real.pi * α / 2)) := by ring
  rw [heqval]
  refine hfin.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with ℓ hℓ
  exact (hval ℓ hℓ).symm

/-! ## The supercritical asymptotics -/

/-- The second integration by parts, legitimate for `α > 1` because the boundary term at the origin
then vanishes. -/
theorem integral_sin_rpow_second_ibp {α L : ℝ} (hα : 1 < α) (hL : 0 < L) :
    (∫ k in (0:ℝ)..Real.pi, Real.sin (L * k) * k ^ (α - 1))
      = -(Real.cos (L * Real.pi) * Real.pi ^ (α - 1)) / L
        + (α - 1) / L * ∫ k in (0:ℝ)..Real.pi, Real.cos (L * k) * k ^ (α - 2) := by
  set g : ℝ → ℝ := fun k => -(Real.cos (L * k) * k ^ (α - 1)) / L with hg
  have hcontRpow : Continuous fun x : ℝ => x ^ (α - 1) :=
    continuous_rpow_const (by linarith)
  have hcontg : Continuous g := ((continuous_cosLin L).mul hcontRpow).neg.div_const L
  have hint1 : IntervalIntegrable (fun k : ℝ => Real.sin (L * k) * k ^ (α - 1)) volume 0 Real.pi :=
    ((continuous_sinLin L).mul hcontRpow).intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun k : ℝ => Real.cos (L * k) * k ^ (α - 2)) volume 0 Real.pi :=
    cos_rpow_intervalIntegrable' (by linarith) L 0 Real.pi
  have hintG : IntervalIntegrable
      (fun k : ℝ => Real.sin (L * k) * k ^ (α - 1)
        - (α - 1) / L * (Real.cos (L * k) * k ^ (α - 2))) volume 0 Real.pi :=
    hint1.sub (hint2.const_mul _)
  have hsub : ∫ y in (0:ℝ)..Real.pi,
      (Real.sin (L * y) * y ^ (α - 1) - (α - 1) / L * (Real.cos (L * y) * y ^ (α - 2)))
      = g Real.pi - g 0 := by
    refine intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le Real.pi_pos.le
      hcontg.continuousOn (fun x hx => ?_) hintG
    exact (hasDerivAt_cosRpowPrimitive (ne_of_gt hL) (ne_of_gt hx.1)).hasDerivWithinAt
  rw [intervalIntegral.integral_sub hint1 (hint2.const_mul _),
    intervalIntegral.integral_const_mul] at hsub
  have hg0 : g 0 = 0 := by
    rw [hg]
    simp [Real.zero_rpow (by linarith : α - 1 ≠ 0)]
  have hgpi : g Real.pi = -(Real.cos (L * Real.pi) * Real.pi ^ (α - 1)) / L := rfl
  rw [hgpi, hg0] at hsub
  linarith [hsub]

/-- The algebraic identity assembling the supercritical asymptotics. -/
theorem supercritical_algebra {S N a p₁ p₂ K c : ℝ} (hS : S * S = 1) (hN : N ≠ 0) (hc : c ≠ 0)
    (hp : p₁ = p₂ * c) :
    S * N ^ 2 * (-(a / (c * N)) * (-(S * p₁) / N + (a - 1) / N * K))
      = a * p₂ - S * (a * (a - 1) / c) * K := by
  have h1 : S * N ^ 2 * (-(a / (c * N)) * (-(S * p₁) / N + (a - 1) / N * K))
      = (S * S) * (a * p₁ / c) - S * (a * (a - 1) / c) * K := by
    field_simp
    ring
  rw [h1, hS, hp]
  field_simp

/-- **Equation (13).**  For `1 < α ≤ 2` the coupling coefficients decay like the alternating
inverse square `(-1)^ℓ α π^{α-2} ℓ^{-2}`. -/
theorem tendsto_quasiRieszCoupling_supercritical {α : ℝ} (hα1 : 1 < α) (hα2 : α ≤ 2) :
    Tendsto (fun ℓ : ℕ => (-1 : ℝ) ^ ℓ * ((ℓ : ℝ)) ^ 2 * quasiRieszCoupling α (ℓ : ℤ)) atTop
      (𝓝 (α * Real.pi ^ (α - 2))) := by
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have hβ0 : (-1 : ℝ) < α - 2 := by linarith
  have hβ1 : α - 2 ≤ 0 := by linarith
  have hKlim : Tendsto
      (fun ℓ : ℕ => ∫ k in (0:ℝ)..Real.pi, Real.cos ((ℓ : ℝ) * k) * k ^ (α - 2))
      atTop (𝓝 0) := by
    have hmaj : Tendsto (fun ℓ : ℕ => (1 / (α - 1) + 2) * ((ℓ : ℝ)) ^ (-(α - 1)) + 2 / (ℓ : ℝ))
        atTop (𝓝 0) := by
      have h1 : Tendsto (fun ℓ : ℕ => ((ℓ : ℝ)) ^ (-(α - 1))) atTop (𝓝 0) :=
        (tendsto_rpow_neg_atTop (y := α - 1) (by linarith)).comp tendsto_natCast_atTop_atTop
      have h2 : Tendsto (fun ℓ : ℕ => 2 / (ℓ : ℝ)) atTop (𝓝 0) := by
        simpa [div_eq_mul_inv] using
          (tendsto_natCast_atTop_atTop (R := ℝ)).inv_tendsto_atTop.const_mul (2:ℝ)
      simpa using (h1.const_mul (1 / (α - 1) + 2)).add h2
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero' ?_ ?_ hmaj
    · filter_upwards with ℓ using dist_nonneg
    · filter_upwards [eventually_ge_atTop 1] with ℓ hℓ
      rw [Real.dist_eq, sub_zero]
      have hL : (1:ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ
      have h := abs_integral_cos_rpow_le hβ0 hβ1 hL
      rw [show α - 2 + 1 = α - 1 by ring] at h
      exact h
  have hval : ∀ ℓ : ℕ, 1 ≤ ℓ →
      (-1 : ℝ) ^ ℓ * ((ℓ : ℝ)) ^ 2 * quasiRieszCoupling α (ℓ : ℤ)
        = α * Real.pi ^ (α - 2) - (-1 : ℝ) ^ ℓ * (α * (α - 1) / Real.pi)
          * ∫ k in (0:ℝ)..Real.pi, Real.cos ((ℓ : ℝ) * k) * k ^ (α - 2) := by
    intro ℓ hℓ
    have hL : (0:ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ
    have hℓ0 : (ℓ : ℤ) ≠ 0 := by
      simp only [ne_eq, Int.natCast_eq_zero]
      omega
    have hcast : (((ℓ : ℤ) : ℝ)) = ((ℓ : ℝ)) := by push_cast; ring
    have hcos : Real.cos ((ℓ : ℝ) * Real.pi) = (-1 : ℝ) ^ ℓ := by
      have h := Real.cos_int_mul_pi (ℓ : ℤ)
      rw [hcast] at h
      rw [h, zpow_natCast]
    have hsq : ((-1 : ℝ) ^ ℓ) * ((-1 : ℝ) ^ ℓ) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]
      norm_num
    have hpipow : Real.pi ^ (α - 1) = Real.pi ^ (α - 2) * Real.pi := by
      rw [← Real.rpow_add_one (ne_of_gt hpi)]
      congr 1
      ring
    rw [quasiRieszCoupling_integration_by_parts (by linarith : (0:ℝ) < α) hℓ0, hcast,
      integral_sin_rpow_second_ibp hα1 hL, hcos]
    exact supercritical_algebra hsq (ne_of_gt hL) (ne_of_gt hpi) hpipow
  have hsmall : Tendsto (fun ℓ : ℕ => (-1 : ℝ) ^ ℓ * (α * (α - 1) / Real.pi)
      * ∫ k in (0:ℝ)..Real.pi, Real.cos ((ℓ : ℝ) * k) * k ^ (α - 2)) atTop (𝓝 0) := by
    have hb : Tendsto (fun ℓ : ℕ => |α * (α - 1) / Real.pi|
        * |∫ k in (0:ℝ)..Real.pi, Real.cos ((ℓ : ℝ) * k) * k ^ (α - 2)|) atTop (𝓝 0) := by
      simpa using hKlim.abs.const_mul (|α * (α - 1) / Real.pi|)
    refine squeeze_zero_norm ?_ hb
    intro ℓ
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  have hconst : Tendsto (fun _ : ℕ => α * Real.pi ^ (α - 2)) atTop
      (𝓝 (α * Real.pi ^ (α - 2))) := tendsto_const_nhds
  have hlim : Tendsto (fun ℓ : ℕ =>
      α * Real.pi ^ (α - 2) - (-1 : ℝ) ^ ℓ * (α * (α - 1) / Real.pi)
        * ∫ k in (0:ℝ)..Real.pi, Real.cos ((ℓ : ℝ) * k) * k ^ (α - 2)) atTop
      (𝓝 (α * Real.pi ^ (α - 2))) := by
    simpa using hconst.sub hsmall
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with ℓ hℓ
  exact (hval ℓ hℓ).symm

end GaloisForLFunctions.HTGeometry.FDNLS
