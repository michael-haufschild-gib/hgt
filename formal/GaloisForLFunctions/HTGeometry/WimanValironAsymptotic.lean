import GaloisForLFunctions.HTGeometry.WimanValironSmallWindow
import GaloisForLFunctions.HTGeometry.CentralIndexDivergence
import GaloisForLFunctions.HTGeometry.BorelGrowthExponent

/-!
# The Wiman--Valiron asymptotic

For a transcendental entire function, `z f'(z)/f(z)` agrees with the central index `ν(r)` to within
any prescribed relative error, at arbitrarily large radii and at a point of the maximum circle.

The parameters are driven by a single scale `w`.  Writing `T₀ = ν(r) + 1`, put

```text
w = T₀^{1/100},   δ = T₀^{-1/4} = w^{-25},   s = w^{64},   H = 6 (log s)/s.
```

The Borel growth lemma at exponent `1/4` supplies a radius at which `ν` does not double across the
step `δ`, so the rise of `ν` across the sampling interval `[x, x + δ/2 + 2H]` is below `T₀ = w^{100}`.
The window `H` is below `δ/4`, so that interval sits inside the Borel step; and `2 H w^{100}/s < δ/2`
reduces to `1536 log w < w³`.  That is the selection condition of the narrow-window estimate, whose
bound `30 s^{3/2}(1 + log(ν + 4s)/log s)` is then `77.4 w^{96}` against a central index at least
`w^{100}/2` — a relative error of `155/w⁴`.

Every exponent is an integer power of `w`, which is why the scale is taken to be the hundredth root.
-/

namespace GaloisForLFunctions.HTGeometry

/-- Basic estimates for the scale parameter. -/
theorem wv_scale_facts {w : ℝ} (hw : (40 : ℝ) ≤ w) :
    (0 : ℝ) < w ∧ (3 : ℝ) ≤ Real.log w ∧ Real.log w ≤ w := by
  have hw0 : (0 : ℝ) < w := by linarith
  refine ⟨hw0, ?_, ?_⟩
  · have he : Real.exp 3 ≤ 40 := by
      have h2 : Real.exp 1 ≤ 2.7182818286 := Real.exp_one_lt_d9.le
      calc Real.exp 3 = (Real.exp 1) ^ (3 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
        _ ≤ (2.7182818286 : ℝ) ^ (3 : ℕ) := pow_le_pow_left₀ (Real.exp_pos 1).le h2 3
        _ ≤ 40 := by norm_num
    have := Real.log_le_log (Real.exp_pos 3) (le_trans he hw)
    rwa [Real.log_exp] at this
  · have := Real.log_le_sub_one_of_pos hw0
    linarith

/-- The window is short enough to sit inside the Borel step. -/
theorem wv_window_le {w : ℝ} (hw : (40 : ℝ) ≤ w) :
    2 * (3 * Real.log (w ^ 64)) / w ^ 64 ≤ (w ^ 25)⁻¹ / 4 := by
  obtain ⟨hw0, hlow, hhigh⟩ := wv_scale_facts hw
  have hlogpow : Real.log (w ^ 64) = 64 * Real.log w := by
    rw [Real.log_pow]; push_cast; ring
  have h64 : (0 : ℝ) < w ^ 64 := by positivity
  have h25 : (0 : ℝ) < w ^ 25 := by positivity
  rw [hlogpow]
  rw [div_le_div_iff₀ h64 (by norm_num : (0:ℝ) < 4)]
  rw [inv_eq_one_div, div_mul_eq_mul_div, le_div_iff₀ h25]
  have hkey : 2 * (3 * (64 * Real.log w)) * 4 * w ^ 25 ≤ w ^ 64 := by
    have h1 : 2 * (3 * (64 * Real.log w)) * 4 * w ^ 25 = 1536 * Real.log w * w ^ 25 := by ring
    have h2 : (1536 : ℝ) * Real.log w * w ^ 25 ≤ 1536 * w * w ^ 25 := by
      have hp : (0 : ℝ) ≤ w ^ 25 := (pow_pos hw0 25).le
      nlinarith [hhigh, hp]
    have h3 : (1536 : ℝ) ≤ w ^ 2 := by nlinarith [hw]
    have h4 : w ^ 2 ≤ w ^ 38 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have h5 : (1536 : ℝ) * w * w ^ 25 ≤ w ^ 38 * w * w ^ 25 := by
      have hp : (0 : ℝ) < w * w ^ 25 := by positivity
      nlinarith [h3, h4, hp]
    have h6 : w ^ 38 * w * w ^ 25 = w ^ 64 := by ring
    linarith [h1, h2, h5, h6]
  linarith [hkey]

/-- The selection condition holds at the chosen parameters. -/
theorem wv_selection_lt {w : ℝ} (hw : (40 : ℝ) ≤ w) :
    2 * (2 * (3 * Real.log (w ^ 64)) / w ^ 64) * w ^ 100 / w ^ 64 < (w ^ 25)⁻¹ / 2 := by
  obtain ⟨hw0, hlow, hhigh⟩ := wv_scale_facts hw
  have hlogpow : Real.log (w ^ 64) = 64 * Real.log w := by
    rw [Real.log_pow]; push_cast; ring
  have h64 : (0 : ℝ) < w ^ 64 := by positivity
  have h25 : (0 : ℝ) < w ^ 25 := by positivity
  have h128 : (0 : ℝ) < w ^ 128 := by positivity
  have hlhs : 2 * (2 * (3 * Real.log (w ^ 64)) / w ^ 64) * w ^ 100 / w ^ 64
      = 768 * Real.log w * w ^ 100 / w ^ 128 := by
    rw [hlogpow]
    field_simp
    ring
  have hrhs : (w ^ 25)⁻¹ / 2 = 1 / (2 * w ^ 25) := by
    rw [inv_eq_one_div]
    field_simp
  rw [hlhs, hrhs, div_lt_div_iff₀ h128 (by positivity)]
  have hgoal : 768 * Real.log w * w ^ 100 * (2 * w ^ 25) = 1536 * Real.log w * w ^ 125 := by
    ring
  rw [hgoal, one_mul]
  have hcube : 1536 * Real.log w < w ^ 3 := by
    have h1 : (1536 : ℝ) * Real.log w ≤ 1536 * w := by linarith
    have hsq : (1600 : ℝ) ≤ w ^ 2 := by nlinarith [hw]
    have h2 : (1536 : ℝ) * w < w ^ 3 := by nlinarith [hsq, hw0, hw]
    linarith
  have h125 : (0 : ℝ) < w ^ 125 := by positivity
  have hmul : 1536 * Real.log w * w ^ 125 < w ^ 3 * w ^ 125 := by
    exact mul_lt_mul_of_pos_right hcube h125
  have heq : w ^ 3 * w ^ 125 = w ^ 128 := by ring
  linarith [hmul, heq]

/-- The collapsed bound is below `ε` times the central index. -/
theorem wv_error_le {w eps nu : ℝ} (hw : (40 : ℝ) ≤ w) (heps : 0 < eps)
    (hweps : 155 / eps ≤ w ^ 4)
    (hlow : w ^ 100 / 2 ≤ nu) (hhigh : nu ≤ 2 * w ^ 100) :
    30 * (w ^ 64 * Real.sqrt (w ^ 64))
        * (1 + Real.log (nu + 4 * w ^ 64) / Real.log (w ^ 64)) ≤ eps * nu := by
  obtain ⟨hw0, hlogw, hhighw⟩ := wv_scale_facts hw
  have hsqrt : Real.sqrt (w ^ 64) = w ^ 32 := by
    rw [show w ^ 64 = (w ^ 32) ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)
  have hlogpow : Real.log (w ^ 64) = 64 * Real.log w := by
    rw [Real.log_pow]; push_cast; ring
  have hlog6 : Real.log 6 ≤ 2 := by
    have he : (6 : ℝ) ≤ Real.exp 2 := by
      have h2 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
      calc (6 : ℝ) ≤ (2.7182818283 : ℝ) ^ (2 : ℕ) := by norm_num
        _ ≤ (Real.exp 1) ^ (2 : ℕ) := by
            refine pow_le_pow_left₀ (by norm_num) h2.le 2
        _ = Real.exp 2 := by rw [← Real.exp_nat_mul]; norm_num
    have := Real.log_le_log (by norm_num) he
    rwa [Real.log_exp] at this
  have hpowle : w ^ 64 ≤ w ^ 100 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have harg : nu + 4 * w ^ 64 ≤ 6 * w ^ 100 := by linarith
  have hargpos : (0 : ℝ) < nu + 4 * w ^ 64 := by
    have : (0 : ℝ) < w ^ 100 := by positivity
    have : (0 : ℝ) < w ^ 64 := by positivity
    linarith [hlow, pow_pos hw0 100]
  have hloga : Real.log (nu + 4 * w ^ 64) ≤ Real.log 6 + 100 * Real.log w := by
    have h1 : Real.log (nu + 4 * w ^ 64) ≤ Real.log (6 * w ^ 100) :=
      Real.log_le_log hargpos harg
    have h2 : Real.log (6 * w ^ 100) = Real.log 6 + 100 * Real.log w := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      push_cast
      ring
    linarith
  have hlogpos : (0 : ℝ) < Real.log w := by linarith
  have hLam : Real.log (nu + 4 * w ^ 64) / Real.log (w ^ 64) ≤ 1.58 := by
    rw [hlogpow, div_le_iff₀ (by positivity)]
    nlinarith [hloga, hlog6, hlogw]
  have hfac : 1 + Real.log (nu + 4 * w ^ 64) / Real.log (w ^ 64) ≤ 2.58 := by linarith
  have hfacnn : (0 : ℝ) ≤ 1 + Real.log (nu + 4 * w ^ 64) / Real.log (w ^ 64) := by
    have : (0 : ℝ) ≤ Real.log (nu + 4 * w ^ 64) / Real.log (w ^ 64) := by
      refine div_nonneg ?_ (by rw [hlogpow]; linarith)
      refine Real.log_nonneg ?_
      have h100 : (1 : ℝ) ≤ w ^ 100 := one_le_pow₀ (by linarith)
      have h64one : (1 : ℝ) ≤ w ^ 64 := one_le_pow₀ (by linarith)
      linarith
    linarith
  have hbase : (0 : ℝ) < 30 * (w ^ 64 * Real.sqrt (w ^ 64)) := by
    rw [hsqrt]; positivity
  have hstep : 30 * (w ^ 64 * Real.sqrt (w ^ 64))
      * (1 + Real.log (nu + 4 * w ^ 64) / Real.log (w ^ 64))
      ≤ 30 * (w ^ 64 * Real.sqrt (w ^ 64)) * 2.58 :=
    mul_le_mul_of_nonneg_left hfac hbase.le
  have hval : 30 * (w ^ 64 * Real.sqrt (w ^ 64)) * 2.58 = 77.4 * w ^ 96 := by
    rw [hsqrt]; ring
  have hfinal : (77.4 : ℝ) * w ^ 96 ≤ eps * nu := by
    have h96 : (0 : ℝ) < w ^ 96 := by positivity
    have hkey : (155 : ℝ) * w ^ 96 ≤ eps * w ^ 100 := by
      have h1 : (155 : ℝ) ≤ eps * w ^ 4 := by
        rw [div_le_iff₀ heps] at hweps
        linarith
      have h2 : (155 : ℝ) * w ^ 96 ≤ (eps * w ^ 4) * w ^ 96 :=
        mul_le_mul_of_nonneg_right h1 h96.le
      have h3 : eps * w ^ 4 * w ^ 96 = eps * w ^ 100 := by ring
      linarith
    have h4 : eps * (w ^ 100 / 2) ≤ eps * nu := mul_le_mul_of_nonneg_left hlow heps.le
    have h5 : eps * (w ^ 100 / 2) = eps * w ^ 100 / 2 := by ring
    linarith
  linarith [hstep, hval, hfinal]

variable {a : ℕ → ℂ}

open Filter

set_option maxHeartbeats 1000000 in
/-- **The Wiman--Valiron asymptotic.**  For a transcendental entire function, at arbitrarily large
radii there is a point of the maximum circle at which `z f'(z)/f(z)` agrees with the central index to
within any prescribed relative error. -/
theorem exists_radius_point_logDeriv_close_centralIndex
    (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0)
    (htrans : ∀ M : ℕ, ∃ n, M ≤ n ∧ a n ≠ 0)
    {eps : ℝ} (heps : 0 < eps) (R : ℝ) :
    ∃ x, R ≤ x ∧ ∃ z : ℂ, ‖z‖ = Real.exp x ∧
      maxTerm a (Real.exp x) ≤ ‖coeffFun a z‖ ∧
      ‖z * deriv (coeffFun a) z / coeffFun a z - (centralIndex a (Real.exp x) : ℂ)‖
        ≤ eps * (centralIndex a (Real.exp x) : ℝ) := by
  classical
  -- the scale threshold
  set w₀ : ℝ := max 40 ((155 / eps) ^ ((1 : ℝ) / 4)) with hw₀def
  have hw₀40 : (40 : ℝ) ≤ w₀ := le_max_left _ _
  have hw₀0 : (0 : ℝ) < w₀ := by linarith
  have hw₀eps : 155 / eps ≤ w₀ ^ 4 := by
    have hge : ((155 / eps) ^ ((1 : ℝ) / 4)) ≤ w₀ := le_max_right _ _
    have hnn : (0 : ℝ) ≤ 155 / eps := by positivity
    have hpow : ((155 / eps) ^ ((1 : ℝ) / 4)) ^ (4 : ℕ) = 155 / eps := by
      rw [← Real.rpow_natCast ((155 / eps) ^ ((1 : ℝ) / 4)) 4, ← Real.rpow_mul hnn]
      norm_num
    calc 155 / eps = ((155 / eps) ^ ((1 : ℝ) / 4)) ^ (4 : ℕ) := hpow.symm
      _ ≤ w₀ ^ 4 := pow_le_pow_left₀ (Real.rpow_nonneg hnn _) hge 4
  -- a radius beyond which the central index exceeds the threshold
  have htop : Tendsto (fun x : ℝ => centralIndex a (Real.exp x)) atTop atTop :=
    (tendsto_centralIndex_atTop ha htrans).comp Real.tendsto_exp_atTop
  obtain ⟨R₁, hR₁⟩ := Filter.eventually_atTop.mp (htop.eventually_ge_atTop ⌈w₀ ^ (100 : ℕ)⌉₊)
  have hR₁' : ∀ x : ℝ, R₁ ≤ x → w₀ ^ (100 : ℕ) ≤ (centralIndex a (Real.exp x) : ℝ) := by
    intro x hx
    have h := hR₁ x hx
    have hcast : ((⌈w₀ ^ (100 : ℕ)⌉₊ : ℕ) : ℝ) ≤ (centralIndex a (Real.exp x) : ℝ) := by
      exact_mod_cast h
    exact le_trans (Nat.le_ceil _) hcast
  -- Borel selection
  set Tlog : ℝ → ℝ := fun y => (centralIndex a (Real.exp y) : ℝ) + 1 with hTdef
  have hTmono : Monotone Tlog := by
    intro p q hpq
    have := monotone_centralIndex_exp ha hn₀ hpq
    rw [hTdef]
    simpa using this
  have hT1 : ∀ y, 1 ≤ Tlog y := by
    intro y
    rw [hTdef]
    have : (0 : ℝ) ≤ (centralIndex a (Real.exp y) : ℝ) := Nat.cast_nonneg _
    linarith
  obtain ⟨x, hxR, hborel⟩ :=
    Nevanlinna.exists_ge_lt_two_mul_rpow hTmono hT1 (by norm_num : (0:ℝ) < 1/4) (max R R₁)
  have hxR0 : R ≤ x := le_trans (le_max_left _ _) hxR
  have hxR1 : R₁ ≤ x := le_trans (le_max_right _ _) hxR
  set T₀ : ℝ := Tlog x with hT₀def
  have hT₀0 : (0 : ℝ) < T₀ := lt_of_lt_of_le zero_lt_one (hT1 x)
  set w : ℝ := T₀ ^ ((1 : ℝ) / 100) with hwdef
  have hw100 : w ^ (100 : ℕ) = T₀ := by
    rw [hwdef, ← Real.rpow_natCast (T₀ ^ ((1 : ℝ) / 100)) 100, ← Real.rpow_mul hT₀0.le]
    norm_num
  have hT₀big : w₀ ^ (100 : ℕ) ≤ T₀ := by
    have := hR₁' x hxR1
    rw [hT₀def, hTdef]
    linarith
  have hwpos : (0 : ℝ) < w := by
    rw [hwdef]
    exact Real.rpow_pos_of_pos hT₀0 _
  have hw₀w : w₀ ≤ w := by
    by_contra hcon
    push Not at hcon
    have hlt : w ^ (100 : ℕ) < w₀ ^ (100 : ℕ) :=
      pow_lt_pow_left₀ hcon hwpos.le (by norm_num)
    rw [hw100] at hlt
    linarith [hT₀big]
  have hw40 : (40 : ℝ) ≤ w := le_trans hw₀40 hw₀w
  have hweps : 155 / eps ≤ w ^ 4 := by
    refine le_trans hw₀eps ?_
    exact pow_le_pow_left₀ hw₀0.le hw₀w 4
  -- the Borel step length
  have hw25 : w ^ (25 : ℕ) = T₀ ^ ((1 : ℝ) / 4) := by
    rw [hwdef, ← Real.rpow_natCast (T₀ ^ ((1 : ℝ) / 100)) 25, ← Real.rpow_mul hT₀0.le]
    norm_num
  set δ : ℝ := T₀ ^ (-((1 : ℝ) / 4)) with hδdef
  have hδ25 : δ = (w ^ (25 : ℕ))⁻¹ := by
    rw [hδdef, hw25, ← Real.rpow_neg hT₀0.le]
  have hδ0 : (0 : ℝ) < δ := by
    rw [hδ25]
    positivity
  have hνδ : (centralIndex a (Real.exp (x + δ)) : ℝ) < 2 * T₀ - 1 := by
    have h := hborel
    rw [hTdef] at h
    simp only at h
    linarith [h]
  -- the parameters
  set s : ℝ := w ^ (64 : ℕ) with hsdef
  have hs100 : (100 : ℝ) ≤ s := by
    have h2 : (100 : ℝ) ≤ w ^ 2 := by nlinarith [hw40]
    have h64 : w ^ 2 ≤ w ^ 64 := pow_le_pow_right₀ (by linarith) (by norm_num)
    rw [hsdef]
    linarith
  set Hw : ℝ := 2 * (3 * Real.log s) / s with hHdef
  have hHle : Hw ≤ δ / 4 := by
    rw [hHdef, hsdef, hδ25]
    exact wv_window_le hw40
  have hHpos : (0 : ℝ) < Hw := by
    rw [hHdef, hsdef]
    have hlog : (0 : ℝ) < Real.log (w ^ (64 : ℕ)) := by
      rw [Real.log_pow]
      have : (3 : ℝ) ≤ Real.log w := (wv_scale_facts hw40).2.1
      positivity
    positivity
  have hmono := monotone_centralIndex_exp ha hn₀
  -- the selection condition
  have hsmall : 2 * (2 * (3 * Real.log s) / s)
      * ((centralIndex a (Real.exp (x + δ / 2 + 2 * (2 * (3 * Real.log s) / s))) : ℝ)
        - (centralIndex a (Real.exp x) : ℝ)) / s < x + δ / 2 - x := by
    have hle : x + δ / 2 + 2 * Hw ≤ x + δ := by linarith
    have hν1 : (centralIndex a (Real.exp (x + δ / 2 + 2 * Hw)) : ℝ)
        ≤ (centralIndex a (Real.exp (x + δ)) : ℝ) := hmono hle
    have hνx : (centralIndex a (Real.exp x) : ℝ) = T₀ - 1 := by
      rw [hT₀def, hTdef]
      ring
    have hΔ : (centralIndex a (Real.exp (x + δ / 2 + 2 * Hw)) : ℝ)
        - (centralIndex a (Real.exp x) : ℝ) ≤ w ^ (100 : ℕ) := by
      rw [hνx, hw100]
      linarith [hν1, hνδ]
    have hstep : 2 * Hw * ((centralIndex a (Real.exp (x + δ / 2 + 2 * Hw)) : ℝ)
          - (centralIndex a (Real.exp x) : ℝ)) / s
        ≤ 2 * Hw * w ^ (100 : ℕ) / s := by
      refine div_le_div_of_nonneg_right ?_ (by linarith : (0:ℝ) ≤ s)
      exact mul_le_mul_of_nonneg_left hΔ (by linarith)
    have hkey : 2 * Hw * w ^ (100 : ℕ) / s < δ / 2 := by
      rw [hHdef, hsdef, hδ25]
      exact wv_selection_lt hw40
    have hrw : x + δ / 2 - x = δ / 2 := by ring
    rw [hrw, ← hHdef]
    linarith [hstep, hkey]
  -- apply the narrow-window estimate
  obtain ⟨y, hy, z, hz, hfz, hbound⟩ :=
    exists_radius_point_wiman_valiron_small_window ha hn₀ (by linarith : x ≤ x + δ / 2)
      hs100 (by rw [hsdef] at hsmall ⊢; exact hsmall)
  rw [← hHdef] at hy
  have hy1 : x ≤ y := by
    have := hy.1
    linarith
  have hy2 : y ≤ x + δ := by
    have := hy.2
    linarith
  refine ⟨y, le_trans hxR0 hy1, z, hz, hfz, le_trans hbound ?_⟩
  have hνlow : w ^ (100 : ℕ) / 2 ≤ (centralIndex a (Real.exp y) : ℝ) := by
    have h1 : (centralIndex a (Real.exp x) : ℝ) ≤ (centralIndex a (Real.exp y) : ℝ) := hmono hy1
    have hνx : (centralIndex a (Real.exp x) : ℝ) = T₀ - 1 := by
      rw [hT₀def, hTdef]; ring
    have h2 : (2 : ℝ) ≤ w ^ (100 : ℕ) := by
      have : (2 : ℝ) ≤ w := by linarith
      calc (2 : ℝ) ≤ w := this
        _ = w ^ (1 : ℕ) := by ring
        _ ≤ w ^ (100 : ℕ) := pow_le_pow_right₀ (by linarith) (by norm_num)
    rw [hνx] at h1
    rw [hw100] at h2
    rw [hw100]
    linarith
  have hνhigh : (centralIndex a (Real.exp y) : ℝ) ≤ 2 * w ^ (100 : ℕ) := by
    have h1 : (centralIndex a (Real.exp y) : ℝ) ≤ (centralIndex a (Real.exp (x + δ)) : ℝ) :=
      hmono hy2
    rw [hw100]
    linarith [hνδ]
  rw [hsdef]
  exact wv_error_le hw40 heps hweps hνlow hνhigh

theorem exists_radius_point_logDeriv_close_centralIndex_window
    (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0)
    (htrans : ∀ M : ℕ, ∃ n, M ≤ n ∧ a n ≠ 0)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ R₁ : ℝ, ∀ R : ℝ, R₁ ≤ R →
    ∃ x ∈ Set.Icc R (R + Nevanlinna.borelWindow ((1 : ℝ) / 4) + 1), ∃ z : ℂ,
      ‖z‖ = Real.exp x ∧
      maxTerm a (Real.exp x) ≤ ‖coeffFun a z‖ ∧
      ‖z * deriv (coeffFun a) z / coeffFun a z - (centralIndex a (Real.exp x) : ℂ)‖
        ≤ eps * (centralIndex a (Real.exp x) : ℝ) := by
  classical
  -- the scale threshold
  set w₀ : ℝ := max 40 ((155 / eps) ^ ((1 : ℝ) / 4)) with hw₀def
  have hw₀40 : (40 : ℝ) ≤ w₀ := le_max_left _ _
  have hw₀0 : (0 : ℝ) < w₀ := by linarith
  have hw₀eps : 155 / eps ≤ w₀ ^ 4 := by
    have hge : ((155 / eps) ^ ((1 : ℝ) / 4)) ≤ w₀ := le_max_right _ _
    have hnn : (0 : ℝ) ≤ 155 / eps := by positivity
    have hpow : ((155 / eps) ^ ((1 : ℝ) / 4)) ^ (4 : ℕ) = 155 / eps := by
      rw [← Real.rpow_natCast ((155 / eps) ^ ((1 : ℝ) / 4)) 4, ← Real.rpow_mul hnn]
      norm_num
    calc 155 / eps = ((155 / eps) ^ ((1 : ℝ) / 4)) ^ (4 : ℕ) := hpow.symm
      _ ≤ w₀ ^ 4 := pow_le_pow_left₀ (Real.rpow_nonneg hnn _) hge 4
  -- a radius beyond which the central index exceeds the threshold
  have htop : Tendsto (fun x : ℝ => centralIndex a (Real.exp x)) atTop atTop :=
    (tendsto_centralIndex_atTop ha htrans).comp Real.tendsto_exp_atTop
  obtain ⟨R₁, hR₁⟩ := Filter.eventually_atTop.mp (htop.eventually_ge_atTop ⌈w₀ ^ (100 : ℕ)⌉₊)
  refine ⟨R₁, fun R hRR₁ => ?_⟩
  have hR₁' : ∀ x : ℝ, R₁ ≤ x → w₀ ^ (100 : ℕ) ≤ (centralIndex a (Real.exp x) : ℝ) := by
    intro x hx
    have h := hR₁ x hx
    have hcast : ((⌈w₀ ^ (100 : ℕ)⌉₊ : ℕ) : ℝ) ≤ (centralIndex a (Real.exp x) : ℝ) := by
      exact_mod_cast h
    exact le_trans (Nat.le_ceil _) hcast
  -- Borel selection
  set Tlog : ℝ → ℝ := fun y => (centralIndex a (Real.exp y) : ℝ) + 1 with hTdef
  have hTmono : Monotone Tlog := by
    intro p q hpq
    have := monotone_centralIndex_exp ha hn₀ hpq
    rw [hTdef]
    simpa using this
  have hT1 : ∀ y, 1 ≤ Tlog y := by
    intro y
    rw [hTdef]
    have : (0 : ℝ) ≤ (centralIndex a (Real.exp y) : ℝ) := Nat.cast_nonneg _
    linarith
  obtain ⟨x, hxmem, hborel⟩ :=
    Nevanlinna.exists_mem_Icc_lt_two_mul_rpow_window hTmono hT1
      (by norm_num : (0:ℝ) < 1/4) R
  have hxR0 : R ≤ x := hxmem.1
  have hxwin : x ≤ R + Nevanlinna.borelWindow ((1 : ℝ) / 4) := hxmem.2
  have hxR1 : R₁ ≤ x := le_trans hRR₁ hxR0
  set T₀ : ℝ := Tlog x with hT₀def
  have hT₀0 : (0 : ℝ) < T₀ := lt_of_lt_of_le zero_lt_one (hT1 x)
  set w : ℝ := T₀ ^ ((1 : ℝ) / 100) with hwdef
  have hw100 : w ^ (100 : ℕ) = T₀ := by
    rw [hwdef, ← Real.rpow_natCast (T₀ ^ ((1 : ℝ) / 100)) 100, ← Real.rpow_mul hT₀0.le]
    norm_num
  have hT₀big : w₀ ^ (100 : ℕ) ≤ T₀ := by
    have := hR₁' x hxR1
    rw [hT₀def, hTdef]
    linarith
  have hwpos : (0 : ℝ) < w := by
    rw [hwdef]
    exact Real.rpow_pos_of_pos hT₀0 _
  have hw₀w : w₀ ≤ w := by
    by_contra hcon
    push Not at hcon
    have hlt : w ^ (100 : ℕ) < w₀ ^ (100 : ℕ) :=
      pow_lt_pow_left₀ hcon hwpos.le (by norm_num)
    rw [hw100] at hlt
    linarith [hT₀big]
  have hw40 : (40 : ℝ) ≤ w := le_trans hw₀40 hw₀w
  have hweps : 155 / eps ≤ w ^ 4 := by
    refine le_trans hw₀eps ?_
    exact pow_le_pow_left₀ hw₀0.le hw₀w 4
  -- the Borel step length
  have hw25 : w ^ (25 : ℕ) = T₀ ^ ((1 : ℝ) / 4) := by
    rw [hwdef, ← Real.rpow_natCast (T₀ ^ ((1 : ℝ) / 100)) 25, ← Real.rpow_mul hT₀0.le]
    norm_num
  set δ : ℝ := T₀ ^ (-((1 : ℝ) / 4)) with hδdef
  have hδ25 : δ = (w ^ (25 : ℕ))⁻¹ := by
    rw [hδdef, hw25, ← Real.rpow_neg hT₀0.le]
  have hδ0 : (0 : ℝ) < δ := by
    rw [hδ25]
    positivity
  have hνδ : (centralIndex a (Real.exp (x + δ)) : ℝ) < 2 * T₀ - 1 := by
    have h := hborel
    rw [hTdef] at h
    simp only at h
    linarith [h]
  -- the parameters
  set s : ℝ := w ^ (64 : ℕ) with hsdef
  have hs100 : (100 : ℝ) ≤ s := by
    have h2 : (100 : ℝ) ≤ w ^ 2 := by nlinarith [hw40]
    have h64 : w ^ 2 ≤ w ^ 64 := pow_le_pow_right₀ (by linarith) (by norm_num)
    rw [hsdef]
    linarith
  set Hw : ℝ := 2 * (3 * Real.log s) / s with hHdef
  have hHle : Hw ≤ δ / 4 := by
    rw [hHdef, hsdef, hδ25]
    exact wv_window_le hw40
  have hHpos : (0 : ℝ) < Hw := by
    rw [hHdef, hsdef]
    have hlog : (0 : ℝ) < Real.log (w ^ (64 : ℕ)) := by
      rw [Real.log_pow]
      have : (3 : ℝ) ≤ Real.log w := (wv_scale_facts hw40).2.1
      positivity
    positivity
  have hmono := monotone_centralIndex_exp ha hn₀
  -- the selection condition
  have hsmall : 2 * (2 * (3 * Real.log s) / s)
      * ((centralIndex a (Real.exp (x + δ / 2 + 2 * (2 * (3 * Real.log s) / s))) : ℝ)
        - (centralIndex a (Real.exp x) : ℝ)) / s < x + δ / 2 - x := by
    have hle : x + δ / 2 + 2 * Hw ≤ x + δ := by linarith
    have hν1 : (centralIndex a (Real.exp (x + δ / 2 + 2 * Hw)) : ℝ)
        ≤ (centralIndex a (Real.exp (x + δ)) : ℝ) := hmono hle
    have hνx : (centralIndex a (Real.exp x) : ℝ) = T₀ - 1 := by
      rw [hT₀def, hTdef]
      ring
    have hΔ : (centralIndex a (Real.exp (x + δ / 2 + 2 * Hw)) : ℝ)
        - (centralIndex a (Real.exp x) : ℝ) ≤ w ^ (100 : ℕ) := by
      rw [hνx, hw100]
      linarith [hν1, hνδ]
    have hstep : 2 * Hw * ((centralIndex a (Real.exp (x + δ / 2 + 2 * Hw)) : ℝ)
          - (centralIndex a (Real.exp x) : ℝ)) / s
        ≤ 2 * Hw * w ^ (100 : ℕ) / s := by
      refine div_le_div_of_nonneg_right ?_ (by linarith : (0:ℝ) ≤ s)
      exact mul_le_mul_of_nonneg_left hΔ (by linarith)
    have hkey : 2 * Hw * w ^ (100 : ℕ) / s < δ / 2 := by
      rw [hHdef, hsdef, hδ25]
      exact wv_selection_lt hw40
    have hrw : x + δ / 2 - x = δ / 2 := by ring
    rw [hrw, ← hHdef]
    linarith [hstep, hkey]
  -- apply the narrow-window estimate
  obtain ⟨y, hy, z, hz, hfz, hbound⟩ :=
    exists_radius_point_wiman_valiron_small_window ha hn₀ (by linarith : x ≤ x + δ / 2)
      hs100 (by rw [hsdef] at hsmall ⊢; exact hsmall)
  rw [← hHdef] at hy
  have hy1 : x ≤ y := by
    have := hy.1
    linarith
  have hy2 : y ≤ x + δ := by
    have := hy.2
    linarith
  refine ⟨y, ⟨le_trans hxR0 hy1, ?_⟩, z, hz, hfz, le_trans hbound ?_⟩
  · exact le_trans hy2 (by
      have : δ ≤ 1 := by
        rw [hδ25]
        have h1 : (1 : ℝ) ≤ w ^ (25 : ℕ) := one_le_pow₀ (by linarith)
        rw [inv_le_one₀ (by positivity)]
        exact h1
      have hWpos : (1 : ℝ) ≤ Nevanlinna.borelWindow ((1 : ℝ) / 4) :=
        Nevanlinna.one_le_borelWindow _
      linarith [hxwin])
  have hνlow : w ^ (100 : ℕ) / 2 ≤ (centralIndex a (Real.exp y) : ℝ) := by
    have h1 : (centralIndex a (Real.exp x) : ℝ) ≤ (centralIndex a (Real.exp y) : ℝ) := hmono hy1
    have hνx : (centralIndex a (Real.exp x) : ℝ) = T₀ - 1 := by
      rw [hT₀def, hTdef]; ring
    have h2 : (2 : ℝ) ≤ w ^ (100 : ℕ) := by
      have : (2 : ℝ) ≤ w := by linarith
      calc (2 : ℝ) ≤ w := this
        _ = w ^ (1 : ℕ) := by ring
        _ ≤ w ^ (100 : ℕ) := pow_le_pow_right₀ (by linarith) (by norm_num)
    rw [hνx] at h1
    rw [hw100] at h2
    rw [hw100]
    linarith
  have hνhigh : (centralIndex a (Real.exp y) : ℝ) ≤ 2 * w ^ (100 : ℕ) := by
    have h1 : (centralIndex a (Real.exp y) : ℝ) ≤ (centralIndex a (Real.exp (x + δ)) : ℝ) :=
      hmono hy2
    rw [hw100]
    linarith [hνδ]
  rw [hsdef]
  exact wv_error_le hw40 heps hweps hνlow hνhigh


end GaloisForLFunctions.HTGeometry
