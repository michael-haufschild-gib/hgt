import GaloisForLFunctions.RHTower.XiMassWindowDiscrepancyTail

/-!
# Penetration of the entropy--action caustic

At the balance slope the exterior action vanishes, `g_u(κ_B u) = 0`, and its slope there is
`-m_B` with `m_B = 2a² − 1/2`.  Retreating from the caustic by `r` therefore costs at most

`g_u(κ_B u − r) ≤ r · (a H/√(H²−u²) − 1/2)`,  `H = κ_B u − r`,

an inequality equivalent to the exact minimum principle

`a H − ½√(H²−u²) ≥ u √(a² − ¼)`,

which is a completed square.  Quantifying the slope factor gives

`g_u(κ_B u − r) ≤ m_B r + 4a² r x`,  `x = 2κ_B r/(u(κ_B²−1))`,

so a sublinear retreat `r = L u^{1/10}` costs only `m_B L u^{1/10} + O(u^{-4/5})`.
-/

open Complex MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-! ## The caustic slope -/

theorem sharpSlope_pos {a : ℝ} (ha : 1 / 2 < a) : 0 < xiMassSpacelikeSharpSlope a := by
  have hpos : (0 : ℝ) < a ^ 2 - 1 / 4 := by nlinarith
  have ha0 : (0 : ℝ) < a := lt_trans (by norm_num) ha
  rw [xiMassSpacelikeSharpSlope]
  exact div_pos ha0 (Real.sqrt_pos.2 hpos)

theorem sharpSlope_mul_sqrt {a : ℝ} (ha : 1 / 2 < a) :
    xiMassSpacelikeSharpSlope a * Real.sqrt (a ^ 2 - 1 / 4) = a := by
  have hpos : (0 : ℝ) < a ^ 2 - 1 / 4 := by nlinarith
  have hne : Real.sqrt (a ^ 2 - 1 / 4) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hpos)
  rw [xiMassSpacelikeSharpSlope, div_mul_cancel₀ a hne]

theorem sharpSlope_sq_sub_one {a : ℝ} (ha : 1 / 2 < a) :
    xiMassSpacelikeSharpSlope a ^ 2 - 1 = (1 / 4) / (a ^ 2 - 1 / 4) := by
  have hpos : (0 : ℝ) < a ^ 2 - 1 / 4 := by nlinarith
  have hs : Real.sqrt (a ^ 2 - 1 / 4) ^ 2 = a ^ 2 - 1 / 4 := Real.sq_sqrt hpos.le
  have hne : Real.sqrt (a ^ 2 - 1 / 4) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hpos)
  have hne2 : a ^ 2 - 1 / 4 ≠ 0 := ne_of_gt hpos
  rw [eq_div_iff hne2, xiMassSpacelikeSharpSlope, div_pow, hs, sub_mul,
    div_mul_cancel₀ _ hne2]
  ring

/-- **The caustic ratio.**  `κ_B = 2a√(κ_B²−1)`. -/
theorem sharpSlope_eq_two_mul_sqrt {a : ℝ} (ha : 1 / 2 < a) :
    xiMassSpacelikeSharpSlope a
      = 2 * a * Real.sqrt (xiMassSpacelikeSharpSlope a ^ 2 - 1) := by
  have hpos : (0 : ℝ) < a ^ 2 - 1 / 4 := by nlinarith
  have hne : Real.sqrt (a ^ 2 - 1 / 4) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hpos)
  have hval : Real.sqrt (xiMassSpacelikeSharpSlope a ^ 2 - 1)
      = (1 / 2) / Real.sqrt (a ^ 2 - 1 / 4) := by
    rw [sharpSlope_sq_sub_one ha, Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1 / 4)]
    congr 1
    rw [show (1 : ℝ) / 4 = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  rw [hval, xiMassSpacelikeSharpSlope]
  field_simp

/-! ## The exact minimum principle -/

/-- **The completed-square minimum of the exterior action.** -/
theorem sharpAction_min {a u H : ℝ} (ha : 1 / 2 < a) (hu : 0 < u) (huH : u ≤ H) :
    u * Real.sqrt (a ^ 2 - 1 / 4) ≤ a * H - (1 / 2) * Real.sqrt (H ^ 2 - u ^ 2) := by
  have ha0 : (0 : ℝ) < a := lt_trans (by norm_num) ha
  have hpos : (0 : ℝ) < a ^ 2 - 1 / 4 := by nlinarith
  have hs : Real.sqrt (a ^ 2 - 1 / 4) ^ 2 = a ^ 2 - 1 / 4 := Real.sq_sqrt hpos.le
  have hgap : (0 : ℝ) ≤ H ^ 2 - u ^ 2 := by nlinarith
  have hQ : Real.sqrt (H ^ 2 - u ^ 2) ^ 2 = H ^ 2 - u ^ 2 := Real.sq_sqrt hgap
  have hkey : ((1 / 2) * Real.sqrt (H ^ 2 - u ^ 2) + u * Real.sqrt (a ^ 2 - 1 / 4)) ^ 2
      ≤ (a * H) ^ 2 := by
    nlinarith [sq_nonneg (Real.sqrt (a ^ 2 - 1 / 4) * Real.sqrt (H ^ 2 - u ^ 2) - u / 2), hs, hQ]
  have hrhs : (0 : ℝ) ≤ (1 / 2) * Real.sqrt (H ^ 2 - u ^ 2) + u * Real.sqrt (a ^ 2 - 1 / 4) := by
    positivity
  have hlhs : (0 : ℝ) ≤ a * H := by nlinarith
  have hstep := Real.sqrt_le_sqrt hkey
  rw [Real.sqrt_sq hrhs, Real.sqrt_sq hlhs] at hstep
  linarith

/-- The algebraic form of the retreat estimate. -/
private theorem action_slope_algebra {a u H Q s kappa : ℝ}
    (hQpos : 0 < Q) (hQ : Q ^ 2 = H ^ 2 - u ^ 2) (hks : kappa * s = a)
    (hu : 0 < u) (hkap : 0 < kappa) (hA : u * s ≤ a * H - (1 / 2) * Q) :
    H / 2 - a * Q ≤ (kappa * u - H) * (a * H / Q - 1 / 2) := by
  have hQne : Q ≠ 0 := ne_of_gt hQpos
  have hdiv : a * H / Q * Q = a * H := div_mul_cancel₀ (a * H) hQne
  have hid : ((kappa * u - H) * (a * H / Q - 1 / 2) - (H / 2 - a * Q)) * Q
      = u * kappa * (a * H - (1 / 2) * Q - u * s) := by
    calc ((kappa * u - H) * (a * H / Q - 1 / 2) - (H / 2 - a * Q)) * Q
        = (kappa * u - H) * (a * H / Q * Q) - (kappa * u - H) * (1 / 2) * Q
            - (H / 2 - a * Q) * Q := by ring
      _ = (kappa * u - H) * (a * H) - (kappa * u - H) * (1 / 2) * Q
            - (H / 2 - a * Q) * Q := by rw [hdiv]
      _ = u * kappa * (a * H - (1 / 2) * Q - u * s) := by
            linear_combination a * hQ + u ^ 2 * hks
  have hnn : 0 ≤ u * kappa * (a * H - (1 / 2) * Q - u * s) :=
    mul_nonneg (mul_nonneg hu.le hkap.le) (by linarith)
  rw [← hid] at hnn
  nlinarith [hnn, hQpos]

/-- **The retreat cost of the caustic.** -/
theorem xiMassAction_le_slope {a u H : ℝ} (ha : 1 / 2 < a) (hu : 0 < u) (huH : u < H) :
    H / 2 - a * Real.sqrt (H ^ 2 - u ^ 2)
      ≤ (xiMassSpacelikeSharpSlope a * u - H)
        * (a * H / Real.sqrt (H ^ 2 - u ^ 2) - 1 / 2) := by
  have hgap : (0 : ℝ) < H ^ 2 - u ^ 2 := by nlinarith
  have hQpos : 0 < Real.sqrt (H ^ 2 - u ^ 2) := Real.sqrt_pos.2 hgap
  have hQ : Real.sqrt (H ^ 2 - u ^ 2) ^ 2 = H ^ 2 - u ^ 2 := Real.sq_sqrt hgap.le
  exact action_slope_algebra hQpos hQ (sharpSlope_mul_sqrt ha) hu (sharpSlope_pos ha)
    (sharpAction_min ha hu huH.le)

/-! ## The quantitative retreat estimate -/

/-- The height ratio at a retreat, in terms of the relative retreat `x`. -/
theorem height_ratio_le {kappa q u r x H : ℝ} (hkappa : 1 < kappa) (hq : 0 < q)
    (hq2 : q ^ 2 = kappa ^ 2 - 1) (hu : 0 < u) (hr : 0 < r)
    (hxdef : x * (u * q ^ 2) = 2 * kappa * r) (hx0 : 0 ≤ x) (hxhalf : x ≤ 1 / 2)
    (hH : H = kappa * u - r) :
    H / Real.sqrt (H ^ 2 - u ^ 2) ≤ kappa / q * (1 + 2 * x) := by
  have hkappa0 : (0 : ℝ) < kappa := lt_trans zero_lt_one hkappa
  have hq2pos : (0 : ℝ) < q ^ 2 := by positivity
  have hgapeq : H ^ 2 - u ^ 2 = u ^ 2 * q ^ 2 * (1 - x) + r ^ 2 := by
    rw [hH]
    linear_combination (-(u ^ 2)) * hq2 + u * hxdef
  have hx1 : (0 : ℝ) ≤ 1 - x := by linarith
  have hgappos : (0 : ℝ) < H ^ 2 - u ^ 2 := by
    rw [hgapeq]
    have h1 : (0 : ℝ) < u ^ 2 * q ^ 2 * (1 - x) := by
      have : (0 : ℝ) < 1 - x := by linarith
      positivity
    nlinarith [sq_nonneg r]
  have hHpos : 0 < H := by
    have hupos : (0 : ℝ) < u * q ^ 2 := by positivity
    have hr' : 2 * kappa * r ≤ (1 / 2) * (u * q ^ 2) := by
      rw [← hxdef]
      exact mul_le_mul_of_nonneg_right hxhalf hupos.le
    rw [hq2] at hr'
    rw [hH]
    nlinarith [hr', hu, hkappa0, hkappa, mul_pos hkappa0 hu]
  have hQpos : 0 < Real.sqrt (H ^ 2 - u ^ 2) := Real.sqrt_pos.2 hgappos
  have hsx : 0 < Real.sqrt (1 - x) := Real.sqrt_pos.2 (by linarith)
  have hsx2 : Real.sqrt (1 - x) ^ 2 = 1 - x := Real.sq_sqrt hx1
  have hQge : u * q * Real.sqrt (1 - x) ≤ Real.sqrt (H ^ 2 - u ^ 2) := by
    have h1 : (u * q * Real.sqrt (1 - x)) ^ 2 ≤ H ^ 2 - u ^ 2 := by
      rw [mul_pow, mul_pow, hsx2, hgapeq]
      nlinarith [sq_nonneg r]
    have h2 : (0 : ℝ) ≤ u * q * Real.sqrt (1 - x) := by positivity
    have hstep := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_sq h2] at hstep
  have hHle : H ≤ kappa * u := by rw [hH]; linarith
  have hstep : H / Real.sqrt (H ^ 2 - u ^ 2) ≤ kappa * u / (u * q * Real.sqrt (1 - x)) :=
    div_le_div₀ (by positivity) hHle (by positivity) hQge
  refine hstep.trans ?_
  have hval : kappa * u / (u * q * Real.sqrt (1 - x)) = kappa / q * (1 / Real.sqrt (1 - x)) := by
    field_simp
  rw [hval]
  have hkey : (1 : ℝ) ≤ (1 + 2 * x) * Real.sqrt (1 - x) := by
    have hsq : (1 : ℝ) ≤ ((1 + 2 * x) * Real.sqrt (1 - x)) ^ 2 := by
      rw [mul_pow, hsx2]
      nlinarith [mul_nonneg hx0 (by nlinarith : (0 : ℝ) ≤ 3 - 4 * x ^ 2)]
    have hnn : (0 : ℝ) ≤ (1 + 2 * x) * Real.sqrt (1 - x) := by positivity
    nlinarith [hsq, hnn]
  have hbern : 1 / Real.sqrt (1 - x) ≤ 1 + 2 * x := by
    rw [div_le_iff₀ hsx]
    linarith
  have hcoef : (0 : ℝ) ≤ kappa / q := by positivity
  exact mul_le_mul_of_nonneg_left hbern hcoef

/-- **The quantitative retreat cost.** -/
theorem xiMassAction_penetration_le {a u r : ℝ} (ha : 1 / 2 < a) (hu : 0 < u) (hr : 0 < r)
    (hx : 2 * xiMassSpacelikeSharpSlope a * r
      ≤ (1 / 2) * (u * (xiMassSpacelikeSharpSlope a ^ 2 - 1))) :
    (xiMassSpacelikeSharpSlope a * u - r) / 2
        - a * Real.sqrt ((xiMassSpacelikeSharpSlope a * u - r) ^ 2 - u ^ 2)
      ≤ (2 * a ^ 2 - 1 / 2) * r
        + 4 * a ^ 2 * r * (2 * xiMassSpacelikeSharpSlope a * r
          / (u * (xiMassSpacelikeSharpSlope a ^ 2 - 1))) := by
  have ha0 : (0 : ℝ) < a := lt_trans (by norm_num) ha
  have hkap : 0 < xiMassSpacelikeSharpSlope a := sharpSlope_pos ha
  have hkone : 1 < xiMassSpacelikeSharpSlope a := one_lt_xiMassSpacelikeSharpSlope ha
  have hk2 : (0 : ℝ) < xiMassSpacelikeSharpSlope a ^ 2 - 1 := by nlinarith
  have hq : (0 : ℝ) < Real.sqrt (xiMassSpacelikeSharpSlope a ^ 2 - 1) := Real.sqrt_pos.2 hk2
  have hq2 : Real.sqrt (xiMassSpacelikeSharpSlope a ^ 2 - 1) ^ 2
      = xiMassSpacelikeSharpSlope a ^ 2 - 1 := Real.sq_sqrt hk2.le
  obtain ⟨x, hxdefe⟩ : ∃ x : ℝ, 2 * xiMassSpacelikeSharpSlope a * r
      / (u * (xiMassSpacelikeSharpSlope a ^ 2 - 1)) = x := ⟨_, rfl⟩
  have hxmul : x * (u * Real.sqrt (xiMassSpacelikeSharpSlope a ^ 2 - 1) ^ 2)
      = 2 * xiMassSpacelikeSharpSlope a * r := by
    rw [hq2, ← hxdefe]
    field_simp
  have hx0 : 0 ≤ x := by
    rw [← hxdefe]
    positivity
  have hxhalf : x ≤ 1 / 2 := by
    rw [← hxdefe, div_le_iff₀ (by positivity : (0 : ℝ) < u * (xiMassSpacelikeSharpSlope a ^ 2 - 1))]
    linarith
  obtain ⟨H, hH⟩ : ∃ H : ℝ, xiMassSpacelikeSharpSlope a * u - r = H := ⟨_, rfl⟩
  have hratio := height_ratio_le (kappa := xiMassSpacelikeSharpSlope a)
    (q := Real.sqrt (xiMassSpacelikeSharpSlope a ^ 2 - 1)) (u := u) (r := r) (x := x) (H := H)
    hkone hq hq2 hu hr hxmul hx0 hxhalf hH.symm
  have hkq : xiMassSpacelikeSharpSlope a
      / Real.sqrt (xiMassSpacelikeSharpSlope a ^ 2 - 1) = 2 * a := by
    rw [div_eq_iff (ne_of_gt hq)]
    exact sharpSlope_eq_two_mul_sqrt ha
  rw [hkq] at hratio
  -- the gap is positive
  have hgapeq : H ^ 2 - u ^ 2
      = u ^ 2 * Real.sqrt (xiMassSpacelikeSharpSlope a ^ 2 - 1) ^ 2 * (1 - x) + r ^ 2 := by
    rw [← hH]
    linear_combination (-(u ^ 2)) * hq2 + u * hxmul
  have hgappos : (0 : ℝ) < H ^ 2 - u ^ 2 := by
    rw [hgapeq]
    have h1 : (0 : ℝ) < u ^ 2 * Real.sqrt (xiMassSpacelikeSharpSlope a ^ 2 - 1) ^ 2 * (1 - x) := by
      have : (0 : ℝ) < 1 - x := by linarith
      positivity
    nlinarith [sq_nonneg r]
  have hHu : u < H := by nlinarith [hgappos, hu]
  have hbase := xiMassAction_le_slope ha hu hHu
  rw [hH]
  have hslope : a * H / Real.sqrt (H ^ 2 - u ^ 2) - 1 / 2
      ≤ (2 * a ^ 2 - 1 / 2) + 4 * a ^ 2 * x := by
    have hmul : a * H / Real.sqrt (H ^ 2 - u ^ 2)
        = a * (H / Real.sqrt (H ^ 2 - u ^ 2)) := by ring
    rw [hmul]
    nlinarith [hratio, ha0]
  have hrr : xiMassSpacelikeSharpSlope a * u - H = r := by rw [← hH]; ring
  rw [hrr] at hbase
  have hfinal : r * (a * H / Real.sqrt (H ^ 2 - u ^ 2) - 1 / 2)
      ≤ r * ((2 * a ^ 2 - 1 / 2) + 4 * a ^ 2 * x) :=
    mul_le_mul_of_nonneg_left hslope hr.le
  rw [hxdefe]
  nlinarith [hbase, hfinal]

/-! ## The sublinear retreat of the discrepancy exponent -/

/-- A concave power decreases by at most its linear rate under a retreat. -/
theorem rpow_sub_le {A B p : ℝ} (hA : 0 < A) (hB : 0 ≤ B) (hBA : B ≤ A)
    (hp0 : 0 < p) (hp1 : p ≤ 1) :
    A ^ p - A ^ (p - 1) * B ≤ (A - B) ^ p := by
  have ht1 : (0 : ℝ) ≤ 1 - B / A := by
    have : B / A ≤ 1 := (div_le_one hA).2 hBA
    linarith
  have ht0 : (0 : ℝ) ≤ B / A := by positivity
  have hfac : A - B = A * (1 - B / A) := by field_simp
  have hpow : (A - B) ^ p = A ^ p * (1 - B / A) ^ p := by
    rw [hfac, Real.mul_rpow hA.le ht1]
  have hbern : 1 - B / A ≤ (1 - B / A) ^ p := by
    rcases eq_or_lt_of_le ht1 with h | h
    · simp [← h, Real.zero_rpow (ne_of_gt hp0)]
    · have hstep := Real.rpow_le_rpow_of_exponent_ge h (by linarith) hp1
      rwa [Real.rpow_one] at hstep
  have hstep : A ^ p * (1 - B / A) ≤ A ^ p * (1 - B / A) ^ p :=
    mul_le_mul_of_nonneg_left hbern (Real.rpow_nonneg hA.le p)
  rw [hpow]
  refine le_trans (le_of_eq ?_) hstep
  have hAp : A ^ (p - 1) * B = A ^ p * (B / A) := by
    rw [Real.rpow_sub hA, Real.rpow_one]
    field_simp
  rw [hAp]
  ring

/-! ## The two-point convexity estimate -/

/-- **The exterior action is convex.**  Its value at a retreated height is at most the value at
the outer height plus the linear extrapolation from the inner slope. -/
theorem xiMassAction_le_slope_general {a u H K : ℝ} (ha : 0 < a) (hu : 0 < u) (huH : u < H)
    (hHK : H ≤ K) :
    H / 2 - a * Real.sqrt (H ^ 2 - u ^ 2)
      ≤ (K / 2 - a * Real.sqrt (K ^ 2 - u ^ 2))
        + (K - H) * (a * H / Real.sqrt (H ^ 2 - u ^ 2) - 1 / 2) := by
  have hgapH : (0 : ℝ) < H ^ 2 - u ^ 2 := by nlinarith
  have hgapK : (0 : ℝ) ≤ K ^ 2 - u ^ 2 := by nlinarith
  have hQH : 0 < Real.sqrt (H ^ 2 - u ^ 2) := Real.sqrt_pos.2 hgapH
  have hQHsq : Real.sqrt (H ^ 2 - u ^ 2) ^ 2 = H ^ 2 - u ^ 2 := Real.sq_sqrt hgapH.le
  have hQKsq : Real.sqrt (K ^ 2 - u ^ 2) ^ 2 = K ^ 2 - u ^ 2 := Real.sq_sqrt hgapK
  have hQKnn : 0 ≤ Real.sqrt (K ^ 2 - u ^ 2) := Real.sqrt_nonneg _
  have hnn : (0 : ℝ) ≤ K * H - u ^ 2 := by nlinarith
  have hprod : Real.sqrt (H ^ 2 - u ^ 2) * Real.sqrt (K ^ 2 - u ^ 2) ≤ K * H - u ^ 2 := by
    have hsq : (Real.sqrt (H ^ 2 - u ^ 2) * Real.sqrt (K ^ 2 - u ^ 2)) ^ 2
        ≤ (K * H - u ^ 2) ^ 2 := by
      rw [mul_pow, hQHsq, hQKsq]
      nlinarith [sq_nonneg (u * (H - K))]
    have hstep := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (mul_nonneg hQH.le hQKnn), Real.sqrt_sq hnn] at hstep
  have hdiv : a * H / Real.sqrt (H ^ 2 - u ^ 2) * Real.sqrt (H ^ 2 - u ^ 2) = a * H :=
    div_mul_cancel₀ (a * H) (ne_of_gt hQH)
  have hid : ((K / 2 - a * Real.sqrt (K ^ 2 - u ^ 2))
        + (K - H) * (a * H / Real.sqrt (H ^ 2 - u ^ 2) - 1 / 2)
        - (H / 2 - a * Real.sqrt (H ^ 2 - u ^ 2))) * Real.sqrt (H ^ 2 - u ^ 2)
      = a * (K * H - u ^ 2
        - Real.sqrt (H ^ 2 - u ^ 2) * Real.sqrt (K ^ 2 - u ^ 2)) := by
    calc ((K / 2 - a * Real.sqrt (K ^ 2 - u ^ 2))
          + (K - H) * (a * H / Real.sqrt (H ^ 2 - u ^ 2) - 1 / 2)
          - (H / 2 - a * Real.sqrt (H ^ 2 - u ^ 2))) * Real.sqrt (H ^ 2 - u ^ 2)
        = (K / 2 - a * Real.sqrt (K ^ 2 - u ^ 2)) * Real.sqrt (H ^ 2 - u ^ 2)
          + (K - H) * (a * H / Real.sqrt (H ^ 2 - u ^ 2) * Real.sqrt (H ^ 2 - u ^ 2))
          - (K - H) * (1 / 2) * Real.sqrt (H ^ 2 - u ^ 2)
          - (H / 2 - a * Real.sqrt (H ^ 2 - u ^ 2)) * Real.sqrt (H ^ 2 - u ^ 2) := by ring
      _ = (K / 2 - a * Real.sqrt (K ^ 2 - u ^ 2)) * Real.sqrt (H ^ 2 - u ^ 2)
          + (K - H) * (a * H)
          - (K - H) * (1 / 2) * Real.sqrt (H ^ 2 - u ^ 2)
          - (H / 2 - a * Real.sqrt (H ^ 2 - u ^ 2)) * Real.sqrt (H ^ 2 - u ^ 2) := by
            rw [hdiv]
      _ = a * (K * H - u ^ 2
          - Real.sqrt (H ^ 2 - u ^ 2) * Real.sqrt (K ^ 2 - u ^ 2)) := by
            linear_combination a * hQHsq
  have hpos : 0 ≤ a * (K * H - u ^ 2
      - Real.sqrt (H ^ 2 - u ^ 2) * Real.sqrt (K ^ 2 - u ^ 2)) :=
    mul_nonneg ha.le (by linarith)
  rw [← hid] at hpos
  nlinarith [hpos, hQH]

end

end RHTower
