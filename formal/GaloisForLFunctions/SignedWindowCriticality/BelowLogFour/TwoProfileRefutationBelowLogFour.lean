import GaloisForLFunctions.SignedWindowCriticality.BelowLogFour.GaugeExtensionInvarianceAndHalfNormDual
import GaloisForLFunctions.WindowTowerOfSpecZ.TheFirstFoldPaysANegativeFrozenDirection
import GaloisForLFunctions.RHTower.HarmonicSecondErrorBounds

/-!
# Explicit Two-Profile Refutation of Variance-Dropping Signed Certificates Below `log 4`

At half-aperture `c₀ = 17/25` (`2c₀ = 34/25 = 1.36 ∈ (log 3, log 4)`), both primes `2` and `3` act on
the window `(−c₀, c₀)` while `4` lies strictly outside. On the scaled odd polynomial sources

    G₁(x) = u (1 − u²)²|_[−1,1],   G₂(x) = (9/2) u (u² − 1/4) (1 − u²)²|_[−1,1]   (u = x / c₀),

the two-profile `L^{1/2}` dual functional satisfies

    markovEnergy(G₁) + markovEnergy(G₂) < 2 (∫_{−c₀}^{c₀} √(G₁² + G₂²) |sinh(x/2)| dx)².

Mollifying `(G₁, G₂)` by `CHMDDoobGraph.smooth` produces `C²_c` odd test functions `(F₁, F₂)`
supported inside `[−273/400, 273/400]` (`273/200 = 1.365 < log 4`) with strictly negative two-profile
`L^{1/2}` dual on every window `(−c, c)` with `273/400 < c < log 2` (`273/200 < 2c < log 4`).

Combined with `GaugeExtensionInvarianceAndHalfNormDual`, this unconditionally refutes on every such
window below `log 4`:
* every odd sinh-charged supersolution `ω ∈ C²_c(ℝ)` (`not_exists_odd_sinhCharged_gauge_below_log_four`),
* every odd non-compact theta-gauge outside-charge certificate (`not_exists_odd_thetaGauge_certificate_below_log_four`),
* every shifted ground state window lower bound `ω_a` (`a > 0`) (`exists_shiftedGroundState_windowLower_neg_below_log_four`).
-/

open Real MeasureTheory Set Filter Topology intervalIntegral Zeta23
open scoped CompactlySupported
open _root_.RHTower _root_.RHTower.ArchimedeanAnomaly
open _root_.RHTower.WeilLevyPoleGauss _root_.RHTower.WeilMarkovPole

noncomputable section

namespace GaloisForLFunctions.SignedWindowCriticality.BelowLogFour

open GaloisForLFunctions.ArithmeticCriticalityTheory
open GaloisForLFunctions.ArithmeticPositivityTheory
open GaloisForLFunctions.SignedWindowCriticality
open GaloisForLFunctions.WindowTowerOfSpecZ
open GaloisForLFunctions.BiScaleUncertainty
open GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open SpacingScaleHarmonicAnalysis

/-! ### 1. Algebraic hyperbolic Taylor inequalities and quartic Lévy kernel bound -/

/-- `z ≤ sinh z` for `z ≥ 0`. -/
lemma self_le_sinh_of_nonneg {z : ℝ} (hz : 0 ≤ z) : z ≤ Real.sinh z := by
  have hd : ∀ u : ℝ, HasDerivAt (fun t => Real.sinh t - t) (Real.cosh u - 1) u := fun u =>
    (Real.hasDerivAt_sinh u).sub (hasDerivAt_id u)
  have hc : Continuous fun u : ℝ => Real.cosh u - 1 := Real.continuous_cosh.sub continuous_const
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u)
    (hc.intervalIntegrable 0 z)
  have hnn : 0 ≤ ∫ u in (0 : ℝ)..z, (Real.cosh u - 1) := by
    rw [intervalIntegral.integral_of_le hz]
    exact setIntegral_nonneg measurableSet_Ioc fun u _ => sub_nonneg.mpr (Real.one_le_cosh u)
  simp only [Real.sinh_zero, sub_self, sub_zero] at hftc
  linarith

/-- `1 + z²/2 ≤ cosh z` for all `z : ℝ`. -/
lemma one_add_sq_div_two_le_cosh (z : ℝ) : 1 + z ^ 2 / 2 ≤ Real.cosh z := by
  suffices h : ∀ w : ℝ, 0 ≤ w → 1 + w ^ 2 / 2 ≤ Real.cosh w by
    have := h |z| (abs_nonneg z)
    rwa [sq_abs, Real.cosh_abs] at this
  intro w hw
  have hd : ∀ u : ℝ, HasDerivAt (fun t => Real.cosh t - 1 - t ^ 2 / 2) (Real.sinh u - u) u :=
    fun u => by
      have h1 := (Real.hasDerivAt_cosh u).sub (hasDerivAt_const u 1)
      have h2 := (hasDerivAt_pow 2 u).div_const 2
      exact (h1.sub h2).congr_deriv (by ring)
  have hc : Continuous fun u : ℝ => Real.sinh u - u := Real.continuous_sinh.sub continuous_id
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u)
    (hc.intervalIntegrable 0 w)
  have hnn : 0 ≤ ∫ u in (0 : ℝ)..w, (Real.sinh u - u) := by
    rw [intervalIntegral.integral_of_le hw]
    exact setIntegral_nonneg measurableSet_Ioc fun u hu =>
      sub_nonneg.mpr (self_le_sinh_of_nonneg hu.1.le)
  have h0 : Real.cosh 0 - 1 - (0 : ℝ) ^ 2 / 2 = 0 := by norm_num [Real.cosh_zero]
  rw [h0, sub_zero] at hftc
  linarith

/-- `z + z³/6 ≤ sinh z` for `z ≥ 0`. -/
lemma cubic_le_sinh_of_nonneg {z : ℝ} (hz : 0 ≤ z) : z + z ^ 3 / 6 ≤ Real.sinh z := by
  have hd : ∀ u : ℝ,
      HasDerivAt (fun t => Real.sinh t - t - t ^ 3 / 6) (Real.cosh u - 1 - u ^ 2 / 2) u :=
    fun u => by
      have h1 := (Real.hasDerivAt_sinh u).sub (hasDerivAt_id u)
      have h2 := (hasDerivAt_pow 3 u).div_const 6
      exact (h1.sub h2).congr_deriv (by ring)
  have hc : Continuous fun u : ℝ => Real.cosh u - 1 - u ^ 2 / 2 :=
    (Real.continuous_cosh.sub continuous_const).sub ((continuous_pow 2).div_const 2)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u)
    (hc.intervalIntegrable 0 z)
  have hnn : 0 ≤ ∫ u in (0 : ℝ)..z, (Real.cosh u - 1 - u ^ 2 / 2) := by
    rw [intervalIntegral.integral_of_le hz]
    exact setIntegral_nonneg measurableSet_Ioc fun u _ => by
      linarith [one_add_sq_div_two_le_cosh u]
  have h0 : Real.sinh 0 - 0 - (0 : ℝ) ^ 3 / 6 = 0 := by norm_num [Real.sinh_zero]
  rw [h0, sub_zero] at hftc
  linarith

/-- **Global quartic algebraic upper bound on the archimedean Lévy density.**
For every `y > 0`,
`2 * archLevyDensity y ≤ 1 / y + 1 / 2 − y / 24 − y² / 16 + y³ / 576 + y⁴ / 128`. -/
theorem two_mul_archLevyDensity_le_quartic {y : ℝ} (hy : 0 < y) :
    2 * archLevyDensity y ≤
      1 / y + 1 / 2 - y / 24 - y ^ 2 / 16 + y ^ 3 / 576 + y ^ 4 / 128 := by
  set z : ℝ := y / 2 with hz_def
  have hz : 0 < z := half_pos hy
  have hsh_pos : 0 < Real.sinh z := Real.sinh_pos_iff.mpr hz
  have hch_pos : 0 < Real.cosh z := Real.cosh_pos z
  -- Step 1: `2 * archLevyDensity y = 1 / (2 * sinh z) + 1 / (2 * cosh z)`
  have hdecomp : 2 * archLevyDensity y = 1 / (2 * Real.sinh z) + 1 / (2 * Real.cosh z) := by
    set q : ℝ := Real.exp (-z) with hq_def
    have hq_pos : 0 < q := Real.exp_pos _
    have hq_lt : q < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    have hqe : q * Real.exp z = 1 := by rw [hq_def, ← Real.exp_add, neg_add_cancel, Real.exp_zero]
    have hexp_z : Real.exp z = 1 / q := eq_one_div_of_mul_eq_one_right hqe
    have hsh_q : 2 * Real.sinh z = (1 - q ^ 2) / q := by
      rw [Real.sinh_eq, hexp_z, ← hq_def]; field_simp [hq_pos.ne']
    have hch_q : 2 * Real.cosh z = (1 + q ^ 2) / q := by
      rw [Real.cosh_eq, hexp_z, ← hq_def]; field_simp [hq_pos.ne']
    have hexp2y : Real.exp (-2 * y) = q ^ 4 := by
      rw [hq_def, ← Real.exp_nat_mul]; congr 1; rw [hz_def]; ring
    have hω : archLevyDensity y = q / (1 - q ^ 4) := by
      unfold archLevyDensity
      rw [show -y / 2 = -z by rw [hz_def]; ring, ← hq_def, hexp2y]
    have h1mq2 : 1 - q ^ 2 ≠ 0 := by nlinarith
    have h1pq2 : 1 + q ^ 2 ≠ 0 := by positivity
    have h1mq4 : 1 - q ^ 4 ≠ 0 := by
      have : 1 - q ^ 4 = (1 - q ^ 2) * (1 + q ^ 2) := by ring
      rw [this]; exact mul_ne_zero h1mq2 h1pq2
    rw [hω, hsh_q, hch_q]
    field_simp [hq_pos.ne', h1mq2, h1pq2, h1mq4]
    ring
  -- Step 2: `1 / (2 * sinh z) ≤ (1 / z − z / 6 + z³ / 36) / 2`
  have hp_sh_pos : 0 < 1 / z - z / 6 + z ^ 3 / 36 := by
    have hnum : 0 < (z ^ 2 - 3) ^ 2 + 27 := by positivity
    have hid : 1 / z - z / 6 + z ^ 3 / 36 = ((z ^ 2 - 3) ^ 2 + 27) / (36 * z) := by
      field_simp [hz.ne']; ring
    rw [hid]; exact div_pos hnum (by positivity)
  have hsh_prod : 1 ≤ Real.sinh z * (1 / z - z / 6 + z ^ 3 / 36) := by
    have h1 : 1 ≤ (z + z ^ 3 / 6) * (1 / z - z / 6 + z ^ 3 / 36) := by
      have hid : (z + z ^ 3 / 6) * (1 / z - z / 6 + z ^ 3 / 36) = 1 + z ^ 6 / 216 := by
        field_simp [hz.ne']; ring
      have hnn : 0 ≤ z ^ 6 / 216 := by positivity
      linarith
    exact h1.trans (mul_le_mul_of_nonneg_right (cubic_le_sinh_of_nonneg hz.le) hp_sh_pos.le)
  have hsh_ub : 1 / (2 * Real.sinh z) ≤ (1 / z - z / 6 + z ^ 3 / 36) / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 2)]
    linarith
  -- Step 3: `1 / (2 * cosh z) ≤ (1 − z² / 2 + z⁴ / 4) / 2`
  have hp_ch_pos : 0 < 1 - z ^ 2 / 2 + z ^ 4 / 4 := by
    have hid : 1 - z ^ 2 / 2 + z ^ 4 / 4 = ((z ^ 2 - 1) ^ 2 + 3) / 4 := by ring
    rw [hid]; positivity
  have hch_prod : 1 ≤ Real.cosh z * (1 - z ^ 2 / 2 + z ^ 4 / 4) := by
    have h1 : 1 ≤ (1 + z ^ 2 / 2) * (1 - z ^ 2 / 2 + z ^ 4 / 4) := by
      have hid : (1 + z ^ 2 / 2) * (1 - z ^ 2 / 2 + z ^ 4 / 4) = 1 + z ^ 6 / 8 := by ring
      have hnn : 0 ≤ z ^ 6 / 8 := by positivity
      linarith
    exact h1.trans (mul_le_mul_of_nonneg_right (one_add_sq_div_two_le_cosh z) hp_ch_pos.le)
  have hch_ub : 1 / (2 * Real.cosh z) ≤ (1 - z ^ 2 / 2 + z ^ 4 / 4) / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 2)]
    linarith
  -- Step 4: Combine and substitute `z = y / 2`
  have hsum : (1 / z - z / 6 + z ^ 3 / 36) / 2 + (1 - z ^ 2 / 2 + z ^ 4 / 4) / 2 =
      1 / y + 1 / 2 - y / 24 - y ^ 2 / 16 + y ^ 3 / 576 + y ^ 4 / 128 := by
    rw [hz_def]; field_simp [hy.ne']; ring
  linarith

/-! ### 2. Certified enclosure of `EF.gammaBracket 0 + 2 Ω(34/25)` -/

private def omegaInZ (t : ℝ) : ℝ :=
  (1 / 2) * (Real.log (1 + t) - Real.log (1 - t)) + Real.arctan t

private lemma hasDerivAt_omegaInZ {t : ℝ} (ht : |t| < 1) :
    HasDerivAt omegaInZ (2 / (1 - t ^ 4)) t := by
  have habs := abs_lt.mp ht
  have h1p : 0 < 1 + t := by linarith
  have h1m : 0 < 1 - t := by linarith
  have hl1 : HasDerivAt (fun u : ℝ => Real.log (1 + u)) (1 / (1 + t)) t := by
    simpa using ((hasDerivAt_id t).const_add 1).log h1p.ne'
  have hl2 : HasDerivAt (fun u : ℝ => Real.log (1 - u)) (-1 / (1 - t)) t := by
    have hsub : HasDerivAt (fun u : ℝ => 1 - u) (-1) t := by
      simpa using (hasDerivAt_id t).const_sub (1 : ℝ)
    exact (hsub.log h1m.ne').congr_deriv (by ring)
  have hc := ((hl1.sub hl2).const_mul (1 / 2 : ℝ)).add (Real.hasDerivAt_arctan t)
  refine hc.congr_deriv ?_
  have hd3 : 1 + t ^ 2 ≠ 0 := by positivity
  have hd4 : 1 - t ^ 4 ≠ 0 := by
    have : 1 - t ^ 4 = (1 - t) * (1 + t) * (1 + t ^ 2) := by ring
    rw [this]; positivity
  field_simp [h1p.ne', h1m.ne', hd3, hd4]
  ring

private lemma omegaInZ_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b < 1) :
    omegaInZ a ≤ omegaInZ b := by
  have hc : ContinuousOn (fun t : ℝ => 2 / (1 - t ^ 4)) (uIcc a b) := by
    rw [uIcc_of_le hab]
    refine ContinuousOn.div continuousOn_const (continuousOn_const.sub (continuous_pow 4).continuousOn)
      fun t ht => ?_
    have ht4 : t ^ 4 < 1 := by
      have h1 : t < 1 := lt_of_le_of_lt ht.2 hb
      have h0 : 0 ≤ t := le_trans ha ht.1
      nlinarith [sq_nonneg t, pow_lt_pow_left₀ h1 h0 (by norm_num : 4 ≠ 0)]
    linarith
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hasDerivAt_omegaInZ (by
      rw [uIcc_of_le hab] at ht
      exact abs_lt.mpr ⟨by linarith [ht.1], lt_of_le_of_lt ht.2 hb⟩))
    hc.intervalIntegrable
  have hnn : 0 ≤ ∫ t in a..b, 2 / (1 - t ^ 4) := by
    rw [intervalIntegral.integral_of_le hab]
    exact setIntegral_nonneg measurableSet_Ioc fun t ht => by
      have ht1 : t < 1 := lt_of_le_of_lt ht.2 hb
      have ht0 : 0 ≤ t := le_trans ha ht.1.le
      have ht4 : t ^ 4 < 1 := by simpa using pow_lt_pow_left₀ ht1 ht0 (by norm_num : 4 ≠ 0)
      exact div_nonneg (by norm_num) (by linarith)
  linarith

private lemma omegaInZ_le_quintic {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) :
    omegaInZ z ≤ 2 * z + (2 / 5) * z ^ 5 / (1 - z ^ 4) := by
  have hz4 : z ^ 4 < 1 := by simpa using pow_lt_pow_left₀ hz1 hz0 (by norm_num : 4 ≠ 0)
  have hd : ∀ t ∈ uIcc 0 z,
      HasDerivAt (fun u => 2 * u + (2 / 5) * u ^ 5 / (1 - z ^ 4) - omegaInZ u)
        (2 + 2 * t ^ 4 / (1 - z ^ 4) - 2 / (1 - t ^ 4)) t := fun t ht => by
    rw [uIcc_of_le hz0] at ht
    have h1 := (hasDerivAt_id t).const_mul (2 : ℝ)
    have h2 := ((hasDerivAt_pow 5 t).const_mul (2 / 5 : ℝ)).div_const (1 - z ^ 4)
    have h3 := hasDerivAt_omegaInZ (abs_lt.mpr ⟨by linarith [ht.1], lt_of_le_of_lt ht.2 hz1⟩)
    exact ((h1.add h2).sub h3).congr_deriv (by ring)
  have hc : ContinuousOn (fun t : ℝ => 2 + 2 * t ^ 4 / (1 - z ^ 4) - 2 / (1 - t ^ 4)) (uIcc 0 z) := by
    rw [uIcc_of_le hz0]
    refine (continuousOn_const.add (((continuous_pow 4).const_mul 2).div_const _).continuousOn).sub ?_
    refine ContinuousOn.div continuousOn_const (continuousOn_const.sub (continuous_pow 4).continuousOn)
      fun t ht => ?_
    have ht4 : t ^ 4 < 1 := by simpa using pow_lt_pow_left₀ (lt_of_le_of_lt ht.2 hz1) ht.1 (by norm_num : 4 ≠ 0)
    linarith
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable
  have h0 : 2 * (0 : ℝ) + (2 / 5) * (0 : ℝ) ^ 5 / (1 - z ^ 4) - omegaInZ 0 = 0 := by
    unfold omegaInZ; simp
  rw [h0, sub_zero] at hftc
  have hnn : 0 ≤ ∫ t in (0 : ℝ)..z, (2 + 2 * t ^ 4 / (1 - z ^ 4) - 2 / (1 - t ^ 4)) := by
    rw [intervalIntegral.integral_of_le hz0]
    refine setIntegral_nonneg measurableSet_Ioc fun t ht => ?_
    have ht4_le : t ^ 4 ≤ z ^ 4 := pow_le_pow_left₀ ht.1.le ht.2 4
    have h1mt4 : 0 < 1 - t ^ 4 := by linarith
    have h1mz4 : 0 < 1 - z ^ 4 := by linarith
    have hid : 2 + 2 * t ^ 4 / (1 - z ^ 4) - 2 / (1 - t ^ 4) =
        2 * t ^ 4 * (z ^ 4 - t ^ 4) / ((1 - z ^ 4) * (1 - t ^ 4)) := by
      field_simp [h1mt4.ne', h1mz4.ne']; ring
    rw [hid]
    exact div_nonneg (mul_nonneg (by positivity) (by linarith)) (mul_pos h1mz4 h1mt4).le
  linarith

private lemma exp_ge_quintic_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 + x ^ 5 / 120 ≤ Real.exp x := by
  -- Bootstrap degree by degree from `1 ≤ exp u` on `[0, x]`
  have step : ∀ {P P' : ℝ → ℝ}, P 0 = 1 → Continuous P' →
      (∀ u, HasDerivAt P (P' u) u) → (∀ u, 0 ≤ u → P' u ≤ Real.exp u) →
      ∀ w, 0 ≤ w → P w ≤ Real.exp w := fun {P P'} hP0 hcP' hdP hle w hw => by
    have hd : ∀ u, HasDerivAt (fun t => Real.exp t - P t) (Real.exp u - P' u) u :=
      fun u => (Real.hasDerivAt_exp u).sub (hdP u)
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u)
      ((Real.continuous_exp.sub hcP').intervalIntegrable 0 w)
    have hnn : 0 ≤ ∫ u in (0 : ℝ)..w, (Real.exp u - P' u) := by
      rw [intervalIntegral.integral_of_le hw]
      exact setIntegral_nonneg measurableSet_Ioc fun u hu => sub_nonneg.mpr (hle u hu.1.le)
    rw [Real.exp_zero, hP0, sub_self, sub_zero] at hftc
    linarith
  have h1 : ∀ w, 0 ≤ w → 1 + w ≤ Real.exp w :=
    step (P' := fun _ => 1) (by norm_num) (by fun_prop)
      (fun u => ((hasDerivAt_const u (1 : ℝ)).add (hasDerivAt_id u)).congr_deriv (by ring))
      (fun u hu => Real.one_le_exp hu)
  have h2 : ∀ w, 0 ≤ w → 1 + w + w ^ 2 / 2 ≤ Real.exp w :=
    step (P' := fun u => 1 + u) (by norm_num) (by fun_prop)
      (fun u => (((hasDerivAt_const u (1 : ℝ)).add (hasDerivAt_id u)).add
        ((hasDerivAt_pow 2 u).div_const 2)).congr_deriv (by ring)) h1
  have h3 : ∀ w, 0 ≤ w → 1 + w + w ^ 2 / 2 + w ^ 3 / 6 ≤ Real.exp w :=
    step (P' := fun u => 1 + u + u ^ 2 / 2) (by norm_num) (by fun_prop)
      (fun u => ((((hasDerivAt_const u (1 : ℝ)).add (hasDerivAt_id u)).add
        ((hasDerivAt_pow 2 u).div_const 2)).add ((hasDerivAt_pow 3 u).div_const 6)).congr_deriv
        (by ring)) h2
  have h4 : ∀ w, 0 ≤ w → 1 + w + w ^ 2 / 2 + w ^ 3 / 6 + w ^ 4 / 24 ≤ Real.exp w :=
    step (P' := fun u => 1 + u + u ^ 2 / 2 + u ^ 3 / 6) (by norm_num) (by fun_prop)
      (fun u => (((((hasDerivAt_const u (1 : ℝ)).add (hasDerivAt_id u)).add
        ((hasDerivAt_pow 2 u).div_const 2)).add ((hasDerivAt_pow 3 u).div_const 6)).add
        ((hasDerivAt_pow 4 u).div_const 24)).congr_deriv (by ring)) h3
  exact step (P' := fun u => 1 + u + u ^ 2 / 2 + u ^ 3 / 6 + u ^ 4 / 24)
    (by norm_num) (by fun_prop)
    (fun u => ((((((hasDerivAt_const u (1 : ℝ)).add (hasDerivAt_id u)).add
      ((hasDerivAt_pow 2 u).div_const 2)).add ((hasDerivAt_pow 3 u).div_const 6)).add
      ((hasDerivAt_pow 4 u).div_const 24)).add ((hasDerivAt_pow 5 u).div_const 120)).congr_deriv
      (by ring)) h4 x hx

private lemma log_one_add_ge_quad {x : ℝ} (hx : 0 ≤ x) : x - x ^ 2 / 2 ≤ Real.log (1 + x) := by
  have hd : ∀ t ∈ uIcc 0 x,
      HasDerivAt (fun u => Real.log (1 + u) - (u - u ^ 2 / 2)) (t ^ 2 / (1 + t)) t := fun t ht => by
    rw [uIcc_of_le hx] at ht
    have h1 : 0 < 1 + t := by linarith [ht.1]
    have hl : HasDerivAt (fun u : ℝ => Real.log (1 + u)) (1 / (1 + t)) t := by
      simpa using ((hasDerivAt_id t).const_add 1).log h1.ne'
    have hp : HasDerivAt (fun u : ℝ => u - u ^ 2 / 2) (1 - t) t :=
      ((hasDerivAt_id t).sub ((hasDerivAt_pow 2 t).div_const 2)).congr_deriv (by ring)
    exact (hl.sub hp).congr_deriv (by field_simp [h1.ne']; ring)
  have hc : ContinuousOn (fun t : ℝ => t ^ 2 / (1 + t)) (uIcc 0 x) := by
    rw [uIcc_of_le hx]
    exact ContinuousOn.div (continuous_pow 2).continuousOn
      (continuousOn_const.add continuousOn_id) fun t ht => by linarith [ht.1]
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable
  have h0 : Real.log (1 + (0 : ℝ)) - ((0 : ℝ) - (0 : ℝ) ^ 2 / 2) = 0 := by simp
  rw [h0, sub_zero] at hftc
  have hnn : 0 ≤ ∫ t in (0 : ℝ)..x, t ^ 2 / (1 + t) := by
    rw [intervalIntegral.integral_of_le hx]
    exact setIntegral_nonneg measurableSet_Ioc fun t ht =>
      div_nonneg (sq_nonneg t) (by linarith [ht.1])
  linarith

/-- Certified rational upper bound `EF.gammaBracket 0 + 2 * archLevyAntideriv (34/25) ≤ −3316/1000`. -/
theorem gammaBracket_add_two_archLevyAntideriv_34_25_le :
    EF.gammaBracket 0 + 2 * archLevyAntideriv (34 / 25) ≤ -(3316 / 1000 : ℝ) := by
  -- 1. Euler–Mascheroni lower bound `5769 / 10000 < γ` at `n = 8`
  have hγ : (5769 / 10000 : ℝ) < Real.eulerMascheroniConstant := by
    have h := RHTower.harmonic_mascheroni_le_half_sub_twelfth (n := 8) (by norm_num)
    have hlog8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]; norm_num
    norm_num [harmonic, Finset.sum_range_succ, hlog8] at h
    linarith [Real.log_two_lt_d9]
  -- 2. `log π = log 3 + log(π/3)` quadratic lower bound
  have hlog_pi : Real.log 3 + ((283 / 6000 : ℝ) - (283 / 6000 : ℝ) ^ 2 / 2) ≤ Real.log Real.pi := by
    set x : ℝ := Real.pi / 3 - 1
    have hx_lo : (283 / 6000 : ℝ) ≤ x := by unfold x; linarith [Real.pi_gt_d4]
    have hx_hi : x ≤ 1 / 3 := by unfold x; linarith [Real.pi_lt_d4]
    have hq := log_one_add_ge_quad (show 0 ≤ x by linarith)
    have h1x : 1 + x = Real.pi / 3 := by unfold x; ring
    rw [h1x, Real.log_div Real.pi_ne_zero (by norm_num)] at hq
    have hmono : (283 / 6000 : ℝ) - (283 / 6000 : ℝ) ^ 2 / 2 ≤ x - x ^ 2 / 2 := by
      have hid : (x - x ^ 2 / 2) - ((283 / 6000 : ℝ) - (283 / 6000 : ℝ) ^ 2 / 2) =
          (x - 283 / 6000) * (1 - (x + 283 / 6000) / 2) := by ring
      nlinarith
    linarith
  -- 3. `exp(−17/25) ≤ 5067 / 10000` and `archLevyAntideriv (34/25)` bound
  have hz_le : Real.exp (-(17 / 25 : ℝ)) ≤ 5067 / 10000 := by
    have hexp := exp_ge_quintic_of_nonneg (show (0 : ℝ) ≤ 17 / 25 by norm_num)
    have hprod : Real.exp (-(17 / 25 : ℝ)) * Real.exp (17 / 25) = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    have hgt : (1 : ℝ) < (5067 / 10000) *
        (1 + (17 / 25 : ℝ) + (17 / 25) ^ 2 / 2 + (17 / 25) ^ 3 / 6 +
          (17 / 25) ^ 4 / 24 + (17 / 25) ^ 5 / 120) := by norm_num
    have hm := mul_le_mul_of_nonneg_left hexp (Real.exp_pos (-(17 / 25 : ℝ))).le
    nlinarith [Real.exp_pos (17 / 25 : ℝ)]
  have hω_le : archLevyAntideriv (34 / 25) ≤
      2 * (5067 / 10000 : ℝ) + (2 / 5) * (5067 / 10000 : ℝ) ^ 5 / (1 - (5067 / 10000 : ℝ) ^ 4) := by
    have heq : archLevyAntideriv (34 / 25) = omegaInZ (Real.exp (-(17 / 25 : ℝ))) := by
      unfold archLevyAntideriv omegaInZ
      congr 2 <;> ring_nf
    rw [heq]
    exact (omegaInZ_mono (Real.exp_pos _).le hz_le (by norm_num)).trans
      (omegaInZ_le_quintic (by norm_num) (by norm_num))
  have he := neg_gammaBracket_zero_eq
  linarith [Real.log_two_gt_d9, Real.log_three_gt_d9, Real.pi_gt_d4]

/-! ### 3. Two-profile polynomial sources on `(−17/25, 17/25)` and exact correlations -/

/-- Reference half-aperture `c₀ = 17/25` (`2c₀ = 34/25 = 1.36 ∈ (log 3, log 4)`). -/
private abbrev c₀ : ℝ := 17 / 25

private def poly₁ (u : ℝ) : ℝ := u - 2 * u ^ 3 + u ^ 5

private def poly₂ (u : ℝ) : ℝ :=
  -(1 / 4 : ℝ) * u + (3 / 2 : ℝ) * u ^ 3 - (9 / 4 : ℝ) * u ^ 5 + u ^ 7

/-- First odd compact polynomial source on `[−1, 1]`: `u max(1 − u², 0)²`. -/
def unitSource₁ (u : ℝ) : ℝ := u * max (1 - u ^ 2) 0 ^ 2

/-- Second odd compact polynomial source on `[−1, 1]`: `u (u² − 1/4) max(1 − u², 0)²`. -/
def unitSource₂ (u : ℝ) : ℝ := u * (u ^ 2 - 1 / 4) * max (1 - u ^ 2) 0 ^ 2

/-- First scaled odd source `G₁(x) = unitSource₁(x / c₀)` supported in `[−17/25, 17/25]`. -/
def refutationSource₁ (x : ℝ) : ℝ := unitSource₁ (x / c₀)

/-- Second scaled odd source `G₂(x) = (9/2) unitSource₂(x / c₀)` supported in `[−17/25, 17/25]`. -/
def refutationSource₂ (x : ℝ) : ℝ := (9 / 2 : ℝ) * unitSource₂ (x / c₀)

private lemma unitSource₁_inside {u : ℝ} (hl : -1 ≤ u) (hr : u ≤ 1) :
    unitSource₁ u = poly₁ u := by
  unfold unitSource₁ poly₁
  rw [max_eq_left (by nlinarith)]
  ring

private lemma unitSource₂_inside {u : ℝ} (hl : -1 ≤ u) (hr : u ≤ 1) :
    unitSource₂ u = poly₂ u := by
  unfold unitSource₂ poly₂
  rw [max_eq_left (by nlinarith)]
  ring

private lemma unitSource₁_outside {u : ℝ} (hu : 1 ≤ |u|) : unitSource₁ u = 0 := by
  unfold unitSource₁
  have hsq : 1 ≤ u ^ 2 := by
    have := pow_le_pow_left₀ zero_le_one hu 2
    rwa [one_pow, sq_abs] at this
  rw [max_eq_right (by linarith), zero_pow (by norm_num), mul_zero]

private lemma unitSource₂_outside {u : ℝ} (hu : 1 ≤ |u|) : unitSource₂ u = 0 := by
  unfold unitSource₂
  have hsq : 1 ≤ u ^ 2 := by
    have := pow_le_pow_left₀ zero_le_one hu 2
    rwa [one_pow, sq_abs] at this
  rw [max_eq_right (by linarith), zero_pow (by norm_num), mul_zero]

lemma continuous_refutationSource₁ : Continuous refutationSource₁ := by
  unfold refutationSource₁ unitSource₁; fun_prop

lemma continuous_refutationSource₂ : Continuous refutationSource₂ := by
  unfold refutationSource₂ unitSource₂; fun_prop

lemma refutationSource₁_odd (x : ℝ) : refutationSource₁ (-x) = -refutationSource₁ x := by
  unfold refutationSource₁ unitSource₁
  rw [neg_div, neg_sq]
  ring

lemma refutationSource₂_odd (x : ℝ) : refutationSource₂ (-x) = -refutationSource₂ x := by
  unfold refutationSource₂ unitSource₂
  rw [neg_div, neg_sq]
  ring

lemma refutationSource₁_eq_zero_of_far {x : ℝ} (hx : c₀ ≤ |x|) : refutationSource₁ x = 0 := by
  have hc0 : (0 : ℝ) < c₀ := by unfold c₀; norm_num
  unfold refutationSource₁
  apply unitSource₁_outside
  rw [abs_div, abs_of_pos hc0, one_le_div hc0]
  exact hx

lemma refutationSource₂_eq_zero_of_far {x : ℝ} (hx : c₀ ≤ |x|) : refutationSource₂ x = 0 := by
  have hc0 : (0 : ℝ) < c₀ := by unfold c₀; norm_num
  unfold refutationSource₂
  rw [unitSource₂_outside, mul_zero]
  rw [abs_div, abs_of_pos hc0, one_le_div hc0]
  exact hx

lemma compact_refutationSource₁ : HasCompactSupport refutationSource₁ :=
  HasCompactSupport.intro (isCompact_Icc (a := -c₀) (b := c₀)) fun _ hx =>
    refutationSource₁_eq_zero_of_far (le_of_lt (not_le.mp fun h => hx (abs_le.mp h)))

lemma compact_refutationSource₂ : HasCompactSupport refutationSource₂ :=
  HasCompactSupport.intro (isCompact_Icc (a := -c₀) (b := c₀)) fun _ hx =>
    refutationSource₂_eq_zero_of_far (le_of_lt (not_le.mp fun h => hx (abs_le.mp h)))

private lemma refutationSource₁_inside {x : ℝ} (hl : -c₀ ≤ x) (hr : x ≤ c₀) :
    refutationSource₁ x = poly₁ (x / c₀) := by
  have hc0 : (0 : ℝ) < c₀ := by unfold c₀; norm_num
  exact unitSource₁_inside ((le_div_iff₀ hc0).mpr (by linarith))
    ((div_le_iff₀ hc0).mpr (by linarith))

private lemma refutationSource₂_inside {x : ℝ} (hl : -c₀ ≤ x) (hr : x ≤ c₀) :
    refutationSource₂ x = (9 / 2 : ℝ) * poly₂ (x / c₀) := by
  have hc0 : (0 : ℝ) < c₀ := by unfold c₀; norm_num
  unfold refutationSource₂
  rw [unitSource₂_inside ((le_div_iff₀ hc0).mpr (by linarith))
    ((div_le_iff₀ hc0).mpr (by linarith))]

private lemma abs_refutationSource₁_le (x : ℝ) : |refutationSource₁ x| ≤ 1 := by
  by_cases hx : c₀ ≤ |x|
  · rw [refutationSource₁_eq_zero_of_far hx, abs_zero]; norm_num
  · push Not at hx
    have hc0 : (0 : ℝ) < c₀ := by unfold c₀; norm_num
    unfold refutationSource₁ unitSource₁
    have hu : |x / c₀| < 1 := by
      rw [abs_div, abs_of_pos hc0, div_lt_one hc0]
      exact hx
    have hu2 : 0 ≤ 1 - (x / c₀) ^ 2 ∧ 1 - (x / c₀) ^ 2 ≤ 1 := by
      have h := abs_lt.mp hu
      exact ⟨by nlinarith [h.1, h.2], by nlinarith [sq_nonneg (x / c₀)]⟩
    rw [abs_mul, max_eq_left hu2.1, abs_pow, abs_of_nonneg hu2.1]
    have hp : (1 - (x / c₀) ^ 2) ^ 2 ≤ 1 := by nlinarith [hu2.1, hu2.2]
    nlinarith [abs_nonneg (x / c₀), hu.le]

private lemma abs_refutationSource₂_le (x : ℝ) : |refutationSource₂ x| ≤ 9 / 2 := by
  by_cases hx : c₀ ≤ |x|
  · rw [refutationSource₂_eq_zero_of_far hx, abs_zero]; norm_num
  · push Not at hx
    have hc0 : (0 : ℝ) < c₀ := by unfold c₀; norm_num
    unfold refutationSource₂ unitSource₂
    have hu : |x / c₀| < 1 := by
      rw [abs_div, abs_of_pos hc0, div_lt_one hc0]
      exact hx
    have hu_bounds := abs_lt.mp hu
    have hu2 : 0 ≤ 1 - (x / c₀) ^ 2 ∧ 1 - (x / c₀) ^ 2 ≤ 1 :=
      ⟨by nlinarith [hu_bounds.1, hu_bounds.2], by nlinarith [sq_nonneg (x / c₀)]⟩
    have hq : |(x / c₀) ^ 2 - 1 / 4| ≤ 1 := abs_le.mpr
      ⟨by nlinarith [sq_nonneg (x / c₀)], by nlinarith [hu_bounds.1, hu_bounds.2]⟩
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 9 / 2),
      max_eq_left hu2.1, abs_pow, abs_of_nonneg hu2.1]
    have hp : (1 - (x / c₀) ^ 2) ^ 2 ≤ 1 := by nlinarith [hu2.1, hu2.2]
    have hm1 : |x / c₀| * |(x / c₀) ^ 2 - 1 / 4| ≤ 1 :=
      (mul_le_mul hu.le hq (abs_nonneg _) zero_le_one).trans_eq (by ring)
    have hm2 : |x / c₀| * |(x / c₀) ^ 2 - 1 / 4| * (1 - (x / c₀) ^ 2) ^ 2 ≤ 1 :=
      (mul_le_mul hm1 hp (sq_nonneg _) zero_le_one).trans_eq (by ring)
    linarith

private lemma hasDerivAt_succ_pow (c : ℝ) (k : ℕ) (x : ℝ) :
    HasDerivAt (fun u : ℝ => c * u ^ (k + 1)) (c * (((k : ℝ) + 1) * x ^ k)) x := by
  simpa [Nat.add_sub_cancel] using (hasDerivAt_pow (k + 1) x).const_mul c

private lemma hasDerivAt_scaled {F F' : ℝ → ℝ} {x : ℝ}
    (hF : HasDerivAt F (F' (x / c₀)) (x / c₀)) :
    HasDerivAt (fun z : ℝ => c₀ * F (z / c₀)) (F' (x / c₀)) x := by
  have hc0 : (c₀ : ℝ) ≠ 0 := by unfold c₀; norm_num
  have h1 := (hF.comp x ((hasDerivAt_id x).div_const c₀)).const_mul c₀
  exact h1.congr_deriv (by field_simp [hc0])

/-- Exact positive-lag unit correlation polynomial `C₁(s)` (`0 ≤ s ≤ 2`). -/
def corrPoly₁ (s : ℝ) : ℝ :=
  (256 / 3465 : ℝ) - (128 / 315 : ℝ) * s ^ 2 + (16 / 21 : ℝ) * s ^ 4 -
    (8 / 15 : ℝ) * s ^ 5 + (8 / 105 : ℝ) * s ^ 7 - (1 / 126 : ℝ) * s ^ 9 +
    (1 / 2772 : ℝ) * s ^ 11

/-- Exact positive-lag unit correlation polynomial `C₂(s)` (`0 ≤ s ≤ 2`). -/
def corrPoly₂ (s : ℝ) : ℝ :=
  (16 / 9009 : ℝ) - (184 / 5005 : ℝ) * s ^ 2 + (17 / 77 : ℝ) * s ^ 4 -
    (3 / 10 : ℝ) * s ^ 5 + (4 / 45 : ℝ) * s ^ 6 + (3 / 70 : ℝ) * s ^ 7 -
    (41 / 2016 : ℝ) * s ^ 9 + (101 / 24640 : ℝ) * s ^ 11 - (1 / 2288 : ℝ) * s ^ 13 +
    (1 / 51480 : ℝ) * s ^ 15

private def corrAnti₁ (s x : ℝ) : ℝ :=
  (1 / 11 : ℝ) * x ^ 11 +
    ((1 / 2 : ℝ) * s) * x ^ 10 +
    ((10 / 9 : ℝ) * s ^ 2 + (-4 / 9 : ℝ)) * x ^ 9 +
    ((5 / 4 : ℝ) * s ^ 3 + (-2 : ℝ) * s) * x ^ 8 +
    ((5 / 7 : ℝ) * s ^ 4 + (-26 / 7 : ℝ) * s ^ 2 + (6 / 7 : ℝ)) * x ^ 7 +
    ((1 / 6 : ℝ) * s ^ 5 + (-11 / 3 : ℝ) * s ^ 3 + (3 : ℝ) * s) * x ^ 6 +
    ((-2 : ℝ) * s ^ 4 + (22 / 5 : ℝ) * s ^ 2 + (-4 / 5 : ℝ)) * x ^ 5 +
    ((-1 / 2 : ℝ) * s ^ 5 + (7 / 2 : ℝ) * s ^ 3 + (-2 : ℝ) * s) * x ^ 4 +
    ((5 / 3 : ℝ) * s ^ 4 + (-2 : ℝ) * s ^ 2 + (1 / 3 : ℝ)) * x ^ 3 +
    ((1 / 2 : ℝ) * s ^ 5 + (-1 : ℝ) * s ^ 3 + (1 / 2 : ℝ) * s) * x ^ 2

private lemma hasDerivAt_corrAnti₁ (s x : ℝ) :
    HasDerivAt (corrAnti₁ s) (poly₁ x * poly₁ (x + s)) x := by
  unfold corrAnti₁
  refine ((((((((((hasDerivAt_succ_pow _ 10 x).add (hasDerivAt_succ_pow _ 9 x)).add
    (hasDerivAt_succ_pow _ 8 x)).add (hasDerivAt_succ_pow _ 7 x)).add
    (hasDerivAt_succ_pow _ 6 x)).add (hasDerivAt_succ_pow _ 5 x)).add
    (hasDerivAt_succ_pow _ 4 x)).add (hasDerivAt_succ_pow _ 3 x)).add
    (hasDerivAt_succ_pow _ 2 x)).add (hasDerivAt_succ_pow _ 1 x)).congr_deriv ?_
  unfold poly₁
  ring

private def corrAnti₂ (s x : ℝ) : ℝ :=
  (1 / 15 : ℝ) * x ^ 15 +
    ((1 / 2 : ℝ) * s) * x ^ 14 +
    ((21 / 13 : ℝ) * s ^ 2 + (-9 / 26 : ℝ)) * x ^ 13 +
    ((35 / 12 : ℝ) * s ^ 3 + (-9 / 4 : ℝ) * s) * x ^ 12 +
    ((35 / 11 : ℝ) * s ^ 4 + (-279 / 44 : ℝ) * s ^ 2 + (129 / 176 : ℝ)) * x ^ 11 +
    ((21 / 10 : ℝ) * s ^ 5 + (-81 / 8 : ℝ) * s ^ 3 + (129 / 32 : ℝ) * s) * x ^ 10 +
    ((7 / 9 : ℝ) * s ^ 6 + (-10 : ℝ) * s ^ 4 + (77 / 8 : ℝ) * s ^ 2 + (-29 / 36 : ℝ)) * x ^ 9 +
    ((1 / 8 : ℝ) * s ^ 7 + (-99 / 16 : ℝ) * s ^ 5 + (837 / 64 : ℝ) * s ^ 3 + (-29 / 8 : ℝ) * s) * x ^ 8 +
    ((-9 / 4 : ℝ) * s ^ 6 + (1245 / 112 : ℝ) * s ^ 4 + (-393 / 56 : ℝ) * s ^ 2 + (27 / 56 : ℝ)) * x ^ 7 +
    ((-3 / 8 : ℝ) * s ^ 7 + (195 / 32 : ℝ) * s ^ 5 + (-367 / 48 : ℝ) * s ^ 3 + (27 / 16 : ℝ) * s) * x ^ 6 +
    ((21 / 10 : ℝ) * s ^ 6 + (-41 / 8 : ℝ) * s ^ 4 + (99 / 40 : ℝ) * s ^ 2 + (-3 / 20 : ℝ)) * x ^ 5 +
    ((3 / 8 : ℝ) * s ^ 7 + (-69 / 32 : ℝ) * s ^ 5 + (63 / 32 : ℝ) * s ^ 3 + (-3 / 8 : ℝ) * s) * x ^ 4 +
    ((-7 / 12 : ℝ) * s ^ 6 + (15 / 16 : ℝ) * s ^ 4 + (-3 / 8 : ℝ) * s ^ 2 + (1 / 48 : ℝ)) * x ^ 3 +
    ((-1 / 8 : ℝ) * s ^ 7 + (9 / 32 : ℝ) * s ^ 5 + (-3 / 16 : ℝ) * s ^ 3 + (1 / 32 : ℝ) * s) * x ^ 2

private lemma hasDerivAt_corrAnti₂ (s x : ℝ) :
    HasDerivAt (corrAnti₂ s) (poly₂ x * poly₂ (x + s)) x := by
  unfold corrAnti₂
  refine ((((((((((((((hasDerivAt_succ_pow _ 14 x).add (hasDerivAt_succ_pow _ 13 x)).add
    (hasDerivAt_succ_pow _ 12 x)).add (hasDerivAt_succ_pow _ 11 x)).add
    (hasDerivAt_succ_pow _ 10 x)).add (hasDerivAt_succ_pow _ 9 x)).add
    (hasDerivAt_succ_pow _ 8 x)).add (hasDerivAt_succ_pow _ 7 x)).add
    (hasDerivAt_succ_pow _ 6 x)).add (hasDerivAt_succ_pow _ 5 x)).add
    (hasDerivAt_succ_pow _ 4 x)).add (hasDerivAt_succ_pow _ 3 x)).add
    (hasDerivAt_succ_pow _ 2 x)).add (hasDerivAt_succ_pow _ 1 x)).congr_deriv ?_
  unfold poly₂
  ring

theorem autocorr_refutationSource₁ {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 34 / 25) :
    autocorr refutationSource₁ t = c₀ * corrPoly₁ (t / c₀) := by
  change (∫ x, refutationSource₁ x * refutationSource₁ (x + t)) = c₀ * corrPoly₁ (t / c₀)
  set s : ℝ := t / c₀ with hs_def
  have hc0 : (c₀ : ℝ) ≠ 0 := by unfold c₀; norm_num
  have he : (fun x => refutationSource₁ x * refutationSource₁ (x + t)) =
      (Icc (-c₀) (c₀ - t)).indicator
        (fun x => poly₁ (x / c₀) * poly₁ (x / c₀ + s)) := by
    funext x
    by_cases hx : x ∈ Icc (-c₀) (c₀ - t)
    · rw [indicator_of_mem hx, refutationSource₁_inside hx.1 (by linarith [hx.2]),
        refutationSource₁_inside (by linarith [hx.1]) (by linarith [hx.2]),
        show (x + t) / c₀ = x / c₀ + s by rw [hs_def, add_div]]
    · rw [indicator_of_notMem hx]
      by_cases hl : x < -c₀
      · rw [refutationSource₁_eq_zero_of_far (by rw [abs_of_neg (by unfold c₀ at hl; linarith)]; linarith),
          zero_mul]
      · have hr : c₀ < x + t := by
          have := not_le.mp (fun h => hx ⟨not_lt.mp hl, h⟩)
          linarith
        rw [refutationSource₁_eq_zero_of_far (x := x + t)
          (by rw [abs_of_pos (by unfold c₀ at hr; linarith)]; linarith), mul_zero]
  have hle : -c₀ ≤ c₀ - t := by unfold c₀; linarith
  rw [he, MeasureTheory.integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hle,
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => hasDerivAt_scaled (F := corrAnti₁ s) (F' := fun u => poly₁ u * poly₁ (u + s))
        (hasDerivAt_corrAnti₁ s (x / c₀)))
      ((by unfold poly₁; fun_prop : Continuous fun x : ℝ =>
        poly₁ (x / c₀) * poly₁ (x / c₀ + s)).intervalIntegrable _ _)]
  have he1 : (c₀ - t) / c₀ = 1 - s := by rw [sub_div, div_self hc0, ← hs_def]
  have he2 : (-c₀) / c₀ = -1 := by rw [neg_div, div_self hc0]
  rw [he1, he2]
  unfold corrAnti₁ corrPoly₁
  ring

theorem autocorr_refutationSource₂ {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 34 / 25) :
    autocorr refutationSource₂ t = (9 / 2 : ℝ) ^ 2 * (c₀ * corrPoly₂ (t / c₀)) := by
  change (∫ x, refutationSource₂ x * refutationSource₂ (x + t)) =
    (9 / 2 : ℝ) ^ 2 * (c₀ * corrPoly₂ (t / c₀))
  set s : ℝ := t / c₀ with hs_def
  have hc0 : (c₀ : ℝ) ≠ 0 := by unfold c₀; norm_num
  have he : (fun x => refutationSource₂ x * refutationSource₂ (x + t)) =
      (Icc (-c₀) (c₀ - t)).indicator
        (fun x => (9 / 2 : ℝ) ^ 2 * (poly₂ (x / c₀) * poly₂ (x / c₀ + s))) := by
    funext x
    by_cases hx : x ∈ Icc (-c₀) (c₀ - t)
    · rw [indicator_of_mem hx, refutationSource₂_inside hx.1 (by linarith [hx.2]),
        refutationSource₂_inside (by linarith [hx.1]) (by linarith [hx.2]),
        show (x + t) / c₀ = x / c₀ + s by rw [hs_def, add_div]]
      ring
    · rw [indicator_of_notMem hx]
      by_cases hl : x < -c₀
      · rw [refutationSource₂_eq_zero_of_far (by rw [abs_of_neg (by unfold c₀ at hl; linarith)]; linarith),
          zero_mul]
      · have hr : c₀ < x + t := by
          have := not_le.mp (fun h => hx ⟨not_lt.mp hl, h⟩)
          linarith
        rw [refutationSource₂_eq_zero_of_far (x := x + t)
          (by rw [abs_of_pos (by unfold c₀ at hr; linarith)]; linarith), mul_zero]
  have hle : -c₀ ≤ c₀ - t := by unfold c₀; linarith
  rw [he, MeasureTheory.integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hle,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => hasDerivAt_scaled (F := corrAnti₂ s) (F' := fun u => poly₂ u * poly₂ (u + s))
        (hasDerivAt_corrAnti₂ s (x / c₀)))
      ((by unfold poly₂; fun_prop : Continuous fun x : ℝ =>
        poly₂ (x / c₀) * poly₂ (x / c₀ + s)).intervalIntegrable _ _)]
  have he1 : (c₀ - t) / c₀ = 1 - s := by rw [sub_div, div_self hc0, ← hs_def]
  have he2 : (-c₀) / c₀ = -1 := by rw [neg_div, div_self hc0]
  rw [he1, he2]
  unfold corrAnti₂ corrPoly₂
  ring

private lemma autocorr_refutationSource₁_zero :
    autocorr refutationSource₁ 0 = c₀ * (256 / 3465 : ℝ) := by
  rw [autocorr_refutationSource₁ le_rfl (by norm_num)]
  unfold corrPoly₁; norm_num

private lemma autocorr_refutationSource₂_zero :
    autocorr refutationSource₂ 0 = (9 / 2 : ℝ) ^ 2 * (c₀ * (16 / 9009 : ℝ)) := by
  rw [autocorr_refutationSource₂ le_rfl (by norm_num)]
  unfold corrPoly₂; norm_num

private lemma autocorr_refutationSource₁_tail {t : ℝ} (ht : 34 / 25 < t) :
    autocorr refutationSource₁ t = 0 :=
  autocorr_eq_zero_of_far (fun _ hx => refutationSource₁_eq_zero_of_far hx.le)
    (by rw [abs_of_pos (by linarith)]; unfold c₀; linarith)

private lemma autocorr_refutationSource₂_tail {t : ℝ} (ht : 34 / 25 < t) :
    autocorr refutationSource₂ t = 0 :=
  autocorr_eq_zero_of_far (fun _ hx => refutationSource₂_eq_zero_of_far hx.le)
    (by rw [abs_of_pos (by linarith)]; unfold c₀; linarith)

/-! ### 4. Lévy jump bounds, prime correlation enclosures, and Markov energy sum -/

private def levyRegPoly (s : ℝ) : ℝ :=
  (1 / 2 : ℝ) - (c₀ / 24) * s - (c₀ ^ 2 / 16) * s ^ 2 +
    (c₀ ^ 3 / 576) * s ^ 3 + (c₀ ^ 4 / 128) * s ^ 4

private def jumpDivS₁ (s : ℝ) : ℝ :=
  (128 / 315 : ℝ) * s - (16 / 21 : ℝ) * s ^ 3 + (8 / 15 : ℝ) * s ^ 4 -
    (8 / 105 : ℝ) * s ^ 6 + (1 / 126 : ℝ) * s ^ 8 - (1 / 2772 : ℝ) * s ^ 10

private def jumpDivS₂ (s : ℝ) : ℝ :=
  (184 / 5005 : ℝ) * s - (17 / 77 : ℝ) * s ^ 3 + (3 / 10 : ℝ) * s ^ 4 -
    (4 / 45 : ℝ) * s ^ 5 - (3 / 70 : ℝ) * s ^ 6 + (41 / 2016 : ℝ) * s ^ 8 -
    (101 / 24640 : ℝ) * s ^ 10 + (1 / 2288 : ℝ) * s ^ 12 - (1 / 51480 : ℝ) * s ^ 14

private def jumpMajorant₁ (s : ℝ) : ℝ :=
  jumpDivS₁ s + c₀ * s * jumpDivS₁ s * levyRegPoly s

private def jumpMajorant₂ (s : ℝ) : ℝ :=
  jumpDivS₂ s + c₀ * s * jumpDivS₂ s * levyRegPoly s

private def jumpAnti₁ (s : ℝ) : ℝ :=
  (64 / 315 : ℝ) * s ^ 2 +
    (1088 / 23625 : ℝ) * s ^ 3 +
    (-113656 / 590625 : ℝ) * s ^ 4 +
    (1310696 / 24609375 : ℝ) * s ^ 5 +
    (108617896 / 3322265625 : ℝ) * s ^ 6 +
    (-218505143 / 21533203125 : ℝ) * s ^ 7 +
    (-10828711 / 2362500000 : ℝ) * s ^ 8 +
    (64503511 / 66445312500 : ℝ) * s ^ 9 +
    (236324497 / 492187500000 : ℝ) * s ^ 10 +
    (-35209337 / 714656250000 : ℝ) * s ^ 11 +
    (-131802479 / 4331250000000 : ℝ) * s ^ 12 +
    (3086231 / 4054050000000 : ℝ) * s ^ 13 +
    (3100103 / 2695000000000 : ℝ) * s ^ 14 +
    (-83521 / 9355500000000 : ℝ) * s ^ 15 +
    (-1419857 / 55440000000000 : ℝ) * s ^ 16

private lemma hasDerivAt_jumpAnti₁ (s : ℝ) :
    HasDerivAt jumpAnti₁ (jumpMajorant₁ s) s := by
  unfold jumpAnti₁
  refine (((((((((((((((hasDerivAt_succ_pow _ 1 s).add (hasDerivAt_succ_pow _ 2 s)).add
    (hasDerivAt_succ_pow _ 3 s)).add (hasDerivAt_succ_pow _ 4 s)).add
    (hasDerivAt_succ_pow _ 5 s)).add (hasDerivAt_succ_pow _ 6 s)).add
    (hasDerivAt_succ_pow _ 7 s)).add (hasDerivAt_succ_pow _ 8 s)).add
    (hasDerivAt_succ_pow _ 9 s)).add (hasDerivAt_succ_pow _ 10 s)).add
    (hasDerivAt_succ_pow _ 11 s)).add (hasDerivAt_succ_pow _ 12 s)).add
    (hasDerivAt_succ_pow _ 13 s)).add (hasDerivAt_succ_pow _ 14 s)).add
    (hasDerivAt_succ_pow _ 15 s)).congr_deriv ?_
  unfold jumpMajorant₁ jumpDivS₁ levyRegPoly c₀
  ring

private def jumpAnti₂ (s : ℝ) : ℝ :=
  (92 / 5005 : ℝ) * s ^ 2 +
    (1564 / 375375 : ℝ) * s ^ 3 +
    (-1039261 / 18768750 : ℝ) * s ^ 4 +
    (35068251 / 782031250 : ℝ) * s ^ 5 +
    (152892913 / 52787109375 : ℝ) * s ^ 6 +
    (-524203114601 / 49267968750000 : ℝ) * s ^ 7 +
    (-979021381 / 415800000000 : ℝ) * s ^ 8 +
    (1408921081 / 556875000000 : ℝ) * s ^ 9 +
    (8165489351 / 10125000000000 : ℝ) * s ^ 10 +
    (-119743496561 / 285862500000000 : ℝ) * s ^ 11 +
    (-31912966933 / 207900000000000 : ℝ) * s ^ 12 +
    (33962353123 / 843242400000000 : ℝ) * s ^ 13 +
    (90903082091 / 5045040000000000 : ℝ) * s ^ 14 +
    (-2116563073 / 1081080000000000 : ℝ) * s ^ 15 +
    (-71530350169 / 57657600000000000 : ℝ) * s ^ 16 +
    (48739 / 1544400000000 : ℝ) * s ^ 17 +
    (22604713 / 463320000000000 : ℝ) * s ^ 18 +
    (-83521 / 220077000000000 : ℝ) * s ^ 19 +
    (-1419857 / 1287000000000000 : ℝ) * s ^ 20

private lemma hasDerivAt_jumpAnti₂ (s : ℝ) :
    HasDerivAt jumpAnti₂ (jumpMajorant₂ s) s := by
  unfold jumpAnti₂
  refine (((((((((((((((((((hasDerivAt_succ_pow _ 1 s).add (hasDerivAt_succ_pow _ 2 s)).add
    (hasDerivAt_succ_pow _ 3 s)).add (hasDerivAt_succ_pow _ 4 s)).add
    (hasDerivAt_succ_pow _ 5 s)).add (hasDerivAt_succ_pow _ 6 s)).add
    (hasDerivAt_succ_pow _ 7 s)).add (hasDerivAt_succ_pow _ 8 s)).add
    (hasDerivAt_succ_pow _ 9 s)).add (hasDerivAt_succ_pow _ 10 s)).add
    (hasDerivAt_succ_pow _ 11 s)).add (hasDerivAt_succ_pow _ 12 s)).add
    (hasDerivAt_succ_pow _ 13 s)).add (hasDerivAt_succ_pow _ 14 s)).add
    (hasDerivAt_succ_pow _ 15 s)).add (hasDerivAt_succ_pow _ 16 s)).add
    (hasDerivAt_succ_pow _ 17 s)).add (hasDerivAt_succ_pow _ 18 s)).add
    (hasDerivAt_succ_pow _ 19 s)).congr_deriv ?_
  unfold jumpMajorant₂ jumpDivS₂ levyRegPoly c₀
  ring

private lemma deficit_nonneg_of_compact {G : ℝ → ℝ} (hGc : HasCompactSupport G)
    (hG : Continuous G) (t : ℝ) : 0 ≤ autocorr G 0 - autocorr G t := by
  have h := integral_sub_shift_sq hGc hG t
  have hn : 0 ≤ ∫ x, (G x - G (x + t)) ^ 2 := integral_nonneg fun _ => sq_nonneg _
  linarith

private lemma jump_inner_le_and_integrable₁ :
    IntegrableOn (fun t => (autocorr refutationSource₁ 0 - autocorr refutationSource₁ t) *
        archLevySinhWeight t) (Ioi (0 : ℝ)) ∧
      biScaleLevyEnergy refutationSource₁ ≤
        (16553078103020896 / 114317083740234375 : ℝ) +
          2 * archLevyAntideriv (34 / 25) * autocorr refutationSource₁ 0 := by
  have hpt : ∀ t ∈ Ioc (0 : ℝ) (34 / 25),
      0 ≤ (autocorr refutationSource₁ 0 - autocorr refutationSource₁ t) * archLevySinhWeight t ∧
        (autocorr refutationSource₁ 0 - autocorr refutationSource₁ t) * archLevySinhWeight t ≤
          jumpMajorant₁ (t / c₀) := fun t ht => by
    have hd_nn := deficit_nonneg_of_compact compact_refutationSource₁ continuous_refutationSource₁ t
    have hw_eq : archLevySinhWeight t = 2 * archLevyDensity t := by
      rw [archLevySinhWeight, exp_half_div_sinh_eq ht.1]
    refine ⟨mul_nonneg hd_nn (archLevySinhWeight_pos ht.1).le, ?_⟩
    rw [hw_eq]
    have hlev := mul_le_mul_of_nonneg_left (two_mul_archLevyDensity_le_quartic ht.1) hd_nn
    rw [autocorr_refutationSource₁_zero, autocorr_refutationSource₁ ht.1.le ht.2] at hlev ⊢
    refine hlev.trans_eq ?_
    have hc0 : (c₀ : ℝ) ≠ 0 := by unfold c₀; norm_num
    unfold jumpMajorant₁ jumpDivS₁ levyRegPoly corrPoly₁ c₀
    field_simp [ht.1.ne']
    ring
  have hmaj_cont : Continuous fun t : ℝ => jumpMajorant₁ (t / c₀) := by
    unfold jumpMajorant₁ jumpDivS₁ levyRegPoly c₀; fun_prop
  have hmaj_int : IntegrableOn (fun t : ℝ => jumpMajorant₁ (t / c₀)) (Ioc (0 : ℝ) (34 / 25)) :=
    hmaj_cont.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hmeas : AEStronglyMeasurable
      (fun t => (autocorr refutationSource₁ 0 - autocorr refutationSource₁ t) * archLevySinhWeight t)
      (volume.restrict (Ioc (0 : ℝ) (34 / 25))) := by
    have hc : Continuous fun t : ℝ => c₀ * (256 / 3465 : ℝ) - c₀ * corrPoly₁ (t / c₀) := by
      unfold corrPoly₁ c₀; fun_prop
    have hw := continuousOn_archLevySinhWeight_pos_halfLine.mono
      (show Ioc (0 : ℝ) (34 / 25) ⊆ Ioi 0 from fun _ ht => ht.1)
    refine ((hc.continuousOn.mul hw).aestronglyMeasurable measurableSet_Ioc).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    simp only [Pi.mul_apply, autocorr_refutationSource₁_zero, autocorr_refutationSource₁ ht.1.le ht.2]
  have hint_in : IntegrableOn
      (fun t => (autocorr refutationSource₁ 0 - autocorr refutationSource₁ t) * archLevySinhWeight t)
      (Ioc (0 : ℝ) (34 / 25)) := by
    refine hmaj_int.mono' hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (hpt t ht).1]
    exact (hpt t ht).2
  have htail_eq : ∀ t ∈ Ioi (34 / 25 : ℝ),
      (autocorr refutationSource₁ 0 - autocorr refutationSource₁ t) * archLevySinhWeight t =
        (autocorr refutationSource₁ 0 * 2) * archLevyDensity t := fun t ht => by
    have ht0 : 0 < t := by linarith [mem_Ioi.mp ht]
    rw [autocorr_refutationSource₁_tail ht, sub_zero, archLevySinhWeight, exp_half_div_sinh_eq ht0]
    ring
  have hint_tail : IntegrableOn
      (fun t => (autocorr refutationSource₁ 0 - autocorr refutationSource₁ t) * archLevySinhWeight t)
      (Ioi (34 / 25 : ℝ)) := by
    refine ((WeilLevyCoshCrossover.integrableOn_archLevyDensity_Ioi
      (by norm_num : (0 : ℝ) < 34 / 25)).const_mul
      (autocorr refutationSource₁ 0 * 2)).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (htail_eq t ht).symm
  have hint_all : IntegrableOn
      (fun t => (autocorr refutationSource₁ 0 - autocorr refutationSource₁ t) * archLevySinhWeight t)
      (Ioi (0 : ℝ)) := by
    have h := hint_in.union hint_tail
    rwa [Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 34 / 25)] at h
  refine ⟨hint_all, ?_⟩
  have hin_le : (∫ t in Ioc (0 : ℝ) (34 / 25),
      (autocorr refutationSource₁ 0 - autocorr refutationSource₁ t) * archLevySinhWeight t) ≤
        16553078103020896 / 114317083740234375 := by
    have hm := setIntegral_mono_on hint_in hmaj_int measurableSet_Ioc fun t ht => (hpt t ht).2
    have hval : (∫ t in Ioc (0 : ℝ) (34 / 25), jumpMajorant₁ (t / c₀)) =
        16553078103020896 / 114317083740234375 := by
      rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 34 / 25),
        intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun t _ => hasDerivAt_scaled (F := jumpAnti₁) (F' := jumpMajorant₁)
            (hasDerivAt_jumpAnti₁ (t / c₀)))
          (hmaj_cont.intervalIntegrable _ _)]
      unfold jumpAnti₁ c₀
      norm_num
    linarith
  have htail_val : (∫ t in Ioi (34 / 25 : ℝ),
      (autocorr refutationSource₁ 0 - autocorr refutationSource₁ t) * archLevySinhWeight t) =
        2 * archLevyAntideriv (34 / 25) * autocorr refutationSource₁ 0 := by
    rw [setIntegral_congr_fun measurableSet_Ioi htail_eq, MeasureTheory.integral_const_mul,
      WeilLevyCoshCrossover.integral_archLevyDensity_Ioi (by norm_num : (0 : ℝ) < 34 / 25)]
    ring
  unfold biScaleLevyEnergy
  rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 34 / 25),
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hint_in hint_tail, htail_val]
  linarith

private lemma jump_inner_le_and_integrable₂ :
    IntegrableOn (fun t => (autocorr refutationSource₂ 0 - autocorr refutationSource₂ t) *
        archLevySinhWeight t) (Ioi (0 : ℝ)) ∧
      biScaleLevyEnergy refutationSource₂ ≤
        (9 / 2 : ℝ) ^ 2 * (41150207385674038 / 9412106561279296875 : ℝ) +
          2 * archLevyAntideriv (34 / 25) * autocorr refutationSource₂ 0 := by
  have hpt : ∀ t ∈ Ioc (0 : ℝ) (34 / 25),
      0 ≤ (autocorr refutationSource₂ 0 - autocorr refutationSource₂ t) * archLevySinhWeight t ∧
        (autocorr refutationSource₂ 0 - autocorr refutationSource₂ t) * archLevySinhWeight t ≤
          (9 / 2 : ℝ) ^ 2 * jumpMajorant₂ (t / c₀) := fun t ht => by
    have hd_nn := deficit_nonneg_of_compact compact_refutationSource₂ continuous_refutationSource₂ t
    have hw_eq : archLevySinhWeight t = 2 * archLevyDensity t := by
      rw [archLevySinhWeight, exp_half_div_sinh_eq ht.1]
    refine ⟨mul_nonneg hd_nn (archLevySinhWeight_pos ht.1).le, ?_⟩
    rw [hw_eq]
    have hlev := mul_le_mul_of_nonneg_left (two_mul_archLevyDensity_le_quartic ht.1) hd_nn
    rw [autocorr_refutationSource₂_zero, autocorr_refutationSource₂ ht.1.le ht.2] at hlev ⊢
    refine hlev.trans_eq ?_
    unfold jumpMajorant₂ jumpDivS₂ levyRegPoly corrPoly₂ c₀
    field_simp [ht.1.ne']
    ring
  have hmaj_cont : Continuous fun t : ℝ => jumpMajorant₂ (t / c₀) := by
    unfold jumpMajorant₂ jumpDivS₂ levyRegPoly c₀; fun_prop
  have hmaj_int : IntegrableOn (fun t : ℝ => (9 / 2 : ℝ) ^ 2 * jumpMajorant₂ (t / c₀))
      (Ioc (0 : ℝ) (34 / 25)) :=
    (hmaj_cont.const_mul _).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hmeas : AEStronglyMeasurable
      (fun t => (autocorr refutationSource₂ 0 - autocorr refutationSource₂ t) * archLevySinhWeight t)
      (volume.restrict (Ioc (0 : ℝ) (34 / 25))) := by
    have hc : Continuous fun t : ℝ =>
        (9 / 2 : ℝ) ^ 2 * (c₀ * (16 / 9009 : ℝ)) - (9 / 2 : ℝ) ^ 2 * (c₀ * corrPoly₂ (t / c₀)) := by
      unfold corrPoly₂ c₀; fun_prop
    have hw := continuousOn_archLevySinhWeight_pos_halfLine.mono
      (show Ioc (0 : ℝ) (34 / 25) ⊆ Ioi 0 from fun _ ht => ht.1)
    refine ((hc.continuousOn.mul hw).aestronglyMeasurable measurableSet_Ioc).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    simp only [Pi.mul_apply, autocorr_refutationSource₂_zero, autocorr_refutationSource₂ ht.1.le ht.2]
  have hint_in : IntegrableOn
      (fun t => (autocorr refutationSource₂ 0 - autocorr refutationSource₂ t) * archLevySinhWeight t)
      (Ioc (0 : ℝ) (34 / 25)) := by
    refine hmaj_int.mono' hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (hpt t ht).1]
    exact (hpt t ht).2
  have htail_eq : ∀ t ∈ Ioi (34 / 25 : ℝ),
      (autocorr refutationSource₂ 0 - autocorr refutationSource₂ t) * archLevySinhWeight t =
        (autocorr refutationSource₂ 0 * 2) * archLevyDensity t := fun t ht => by
    have ht0 : 0 < t := by linarith [mem_Ioi.mp ht]
    rw [autocorr_refutationSource₂_tail ht, sub_zero, archLevySinhWeight, exp_half_div_sinh_eq ht0]
    ring
  have hint_tail : IntegrableOn
      (fun t => (autocorr refutationSource₂ 0 - autocorr refutationSource₂ t) * archLevySinhWeight t)
      (Ioi (34 / 25 : ℝ)) := by
    refine ((WeilLevyCoshCrossover.integrableOn_archLevyDensity_Ioi
      (by norm_num : (0 : ℝ) < 34 / 25)).const_mul
      (autocorr refutationSource₂ 0 * 2)).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (htail_eq t ht).symm
  have hint_all : IntegrableOn
      (fun t => (autocorr refutationSource₂ 0 - autocorr refutationSource₂ t) * archLevySinhWeight t)
      (Ioi (0 : ℝ)) := by
    have h := hint_in.union hint_tail
    rwa [Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 34 / 25)] at h
  refine ⟨hint_all, ?_⟩
  have hin_le : (∫ t in Ioc (0 : ℝ) (34 / 25),
      (autocorr refutationSource₂ 0 - autocorr refutationSource₂ t) * archLevySinhWeight t) ≤
        (9 / 2 : ℝ) ^ 2 * (41150207385674038 / 9412106561279296875 : ℝ) := by
    have hm := setIntegral_mono_on hint_in hmaj_int measurableSet_Ioc fun t ht => (hpt t ht).2
    have hval : (∫ t in Ioc (0 : ℝ) (34 / 25), (9 / 2 : ℝ) ^ 2 * jumpMajorant₂ (t / c₀)) =
        (9 / 2 : ℝ) ^ 2 * (41150207385674038 / 9412106561279296875 : ℝ) := by
      rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 34 / 25),
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun t _ => hasDerivAt_scaled (F := jumpAnti₂) (F' := jumpMajorant₂)
            (hasDerivAt_jumpAnti₂ (t / c₀)))
          (hmaj_cont.intervalIntegrable _ _)]
      unfold jumpAnti₂ c₀
      norm_num
    linarith
  have htail_val : (∫ t in Ioi (34 / 25 : ℝ),
      (autocorr refutationSource₂ 0 - autocorr refutationSource₂ t) * archLevySinhWeight t) =
        2 * archLevyAntideriv (34 / 25) * autocorr refutationSource₂ 0 := by
    rw [setIntegral_congr_fun measurableSet_Ioi htail_eq, MeasureTheory.integral_const_mul,
      WeilLevyCoshCrossover.integral_archLevyDensity_Ioi (by norm_num : (0 : ℝ) < 34 / 25)]
    ring
  unfold biScaleLevyEnergy
  rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 34 / 25),
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hint_in hint_tail, htail_val]
  linarith

private lemma poly_ge_of_deriv_bound {P P' : ℝ → ℝ} {a b s₀ s M : ℝ}
    (ha : a ≤ s₀) (hs₀ : s₀ ≤ b) (has : a ≤ s) (hsb : s ≤ b)
    (hcP' : Continuous P') (hdP : ∀ u, HasDerivAt P (P' u) u)
    (hbP' : ∀ u ∈ Icc a b, |P' u| ≤ M) :
    P s₀ - M * |s - s₀| ≤ P s := by
  rcases le_total s₀ s with hle | hle
  · have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun u _ => hdP u) (hcP'.intervalIntegrable s₀ s)
    rw [intervalIntegral.integral_of_le hle] at hftc
    have hm := setIntegral_mono_on
      ((continuous_const : Continuous fun _ : ℝ => -M).integrableOn_Ioc (μ := volume))
      (hcP'.integrableOn_Ioc (μ := volume)) measurableSet_Ioc
      fun u hu => (abs_le.mp (hbP' u ⟨le_trans ha hu.1.le, le_trans hu.2 hsb⟩)).1
    rw [setIntegral_const, Real.volume_real_Ioc, max_eq_left (by linarith), smul_eq_mul, hftc] at hm
    rw [abs_of_nonneg (by linarith)]
    linarith
  · have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun u _ => hdP u) (hcP'.intervalIntegrable s s₀)
    rw [intervalIntegral.integral_of_le hle] at hftc
    have hm := setIntegral_mono_on
      (hcP'.integrableOn_Ioc (μ := volume))
      ((continuous_const : Continuous fun _ : ℝ => M).integrableOn_Ioc (μ := volume))
      measurableSet_Ioc
      fun u hu => (abs_le.mp (hbP' u ⟨le_trans has hu.1.le, le_trans hu.2 hs₀⟩)).2
    rw [setIntegral_const, Real.volume_real_Ioc, max_eq_left (by linarith), smul_eq_mul, hftc] at hm
    rw [abs_of_nonpos (by linarith)]
    linarith

private def corrPoly₁Deriv (u : ℝ) : ℝ :=
  (-256 / 315 : ℝ) * u + (64 / 21 : ℝ) * u ^ 3 - (8 / 3 : ℝ) * u ^ 4 +
    (8 / 15 : ℝ) * u ^ 6 - (1 / 14 : ℝ) * u ^ 8 + (1 / 252 : ℝ) * u ^ 10

private def corrPoly₂Deriv (u : ℝ) : ℝ :=
  (-368 / 5005 : ℝ) * u + (68 / 77 : ℝ) * u ^ 3 - (3 / 2 : ℝ) * u ^ 4 +
    (8 / 15 : ℝ) * u ^ 5 + (3 / 10 : ℝ) * u ^ 6 - (41 / 224 : ℝ) * u ^ 8 +
    (101 / 2240 : ℝ) * u ^ 10 - (1 / 176 : ℝ) * u ^ 12 + (1 / 3432 : ℝ) * u ^ 14

private lemma hasDerivAt_corrPoly₁ (u : ℝ) : HasDerivAt corrPoly₁ (corrPoly₁Deriv u) u := by
  unfold corrPoly₁
  refine (((((((hasDerivAt_const u (256 / 3465 : ℝ)).sub
    (hasDerivAt_succ_pow (128 / 315) 1 u)).add
    (hasDerivAt_succ_pow (16 / 21) 3 u)).sub
    (hasDerivAt_succ_pow (8 / 15) 4 u)).add
    (hasDerivAt_succ_pow (8 / 105) 6 u)).sub
    (hasDerivAt_succ_pow (1 / 126) 8 u)).add
    (hasDerivAt_succ_pow (1 / 2772) 10 u)).congr_deriv ?_
  unfold corrPoly₁Deriv; ring

private lemma hasDerivAt_corrPoly₂ (u : ℝ) : HasDerivAt corrPoly₂ (corrPoly₂Deriv u) u := by
  unfold corrPoly₂
  refine ((((((((((hasDerivAt_const u (16 / 9009 : ℝ)).sub
    (hasDerivAt_succ_pow (184 / 5005) 1 u)).add
    (hasDerivAt_succ_pow (17 / 77) 3 u)).sub
    (hasDerivAt_succ_pow (3 / 10) 4 u)).add
    (hasDerivAt_succ_pow (4 / 45) 5 u)).add
    (hasDerivAt_succ_pow (3 / 70) 6 u)).sub
    (hasDerivAt_succ_pow (41 / 2016) 8 u)).add
    (hasDerivAt_succ_pow (101 / 24640) 10 u)).sub
    (hasDerivAt_succ_pow (1 / 2288) 12 u)).add
    (hasDerivAt_succ_pow (1 / 51480) 14 u)).congr_deriv ?_
  unfold corrPoly₂Deriv; ring

private lemma prime_corr_bounds :
    -(34565 / 1000000 : ℝ) ≤ corrPoly₁ (Real.log 2 / c₀) ∧
      -(1936 / 1000000 : ℝ) ≤ corrPoly₁ (Real.log 3 / c₀) ∧
      (865 / 1000000 : ℝ) ≤ corrPoly₂ (Real.log 2 / c₀) ∧
      -(303 / 1000000 : ℝ) ≤ corrPoly₂ (Real.log 3 / c₀) := by
  set s₂ := Real.log 2 / c₀
  set s₃ := Real.log 3 / c₀
  have hs₂_ball : |s₂ - (101933 / 100000 : ℝ)| ≤ 5 / 1000000 := by
    rw [abs_le]; unfold s₂ c₀
    exact ⟨by linarith [Real.log_two_gt_d9], by linarith [Real.log_two_lt_d9]⟩
  have hs₃_ball : |s₃ - (161561 / 100000 : ℝ)| ≤ 4 / 1000000 := by
    rw [abs_le]; unfold s₃ c₀
    exact ⟨by linarith [Real.log_three_gt_d9], by linarith [Real.log_three_lt_d9]⟩
  have hs₂_in : s₂ ∈ Icc (1 : ℝ) (33 / 32) := by
    unfold s₂ c₀
    exact ⟨by linarith [Real.log_two_gt_d9], by linarith [Real.log_two_lt_d9]⟩
  have hs₃_in : s₃ ∈ Icc (8 / 5 : ℝ) (13 / 8) := by
    unfold s₃ c₀
    exact ⟨by linarith [Real.log_three_gt_d9], by linarith [Real.log_three_lt_d9]⟩
  have hb1_2 : ∀ u ∈ Icc (1 : ℝ) (33 / 32), |corrPoly₁Deriv u| ≤ 1 / 2 := fun u hu => by
    have h0 : 0 ≤ u := by linarith [hu.1]
    have p3l := pow_le_pow_left₀ zero_le_one hu.1 3
    have p3u := pow_le_pow_left₀ h0 hu.2 3
    have p4l := pow_le_pow_left₀ zero_le_one hu.1 4
    have p4u := pow_le_pow_left₀ h0 hu.2 4
    have p6l := pow_le_pow_left₀ zero_le_one hu.1 6
    have p6u := pow_le_pow_left₀ h0 hu.2 6
    have p8l := pow_le_pow_left₀ zero_le_one hu.1 8
    have p8u := pow_le_pow_left₀ h0 hu.2 8
    have p10l := pow_le_pow_left₀ zero_le_one hu.1 10
    have p10u := pow_le_pow_left₀ h0 hu.2 10
    rw [abs_le]; unfold corrPoly₁Deriv
    exact ⟨by linarith [hu.1, hu.2], by linarith [hu.1, hu.2]⟩
  have hb1_3 : ∀ u ∈ Icc (8 / 5 : ℝ) (13 / 8), |corrPoly₁Deriv u| ≤ 2 := fun u hu => by
    have ha : (0 : ℝ) ≤ 8 / 5 := by norm_num
    have h0 : 0 ≤ u := by linarith [hu.1]
    have p3l := pow_le_pow_left₀ ha hu.1 3
    have p3u := pow_le_pow_left₀ h0 hu.2 3
    have p4l := pow_le_pow_left₀ ha hu.1 4
    have p4u := pow_le_pow_left₀ h0 hu.2 4
    have p6l := pow_le_pow_left₀ ha hu.1 6
    have p6u := pow_le_pow_left₀ h0 hu.2 6
    have p8l := pow_le_pow_left₀ ha hu.1 8
    have p8u := pow_le_pow_left₀ h0 hu.2 8
    have p10l := pow_le_pow_left₀ ha hu.1 10
    have p10u := pow_le_pow_left₀ h0 hu.2 10
    rw [abs_le]; unfold corrPoly₁Deriv
    exact ⟨by linarith [hu.1, hu.2], by linarith [hu.1, hu.2]⟩
  have hb2_2 : ∀ u ∈ Icc (1 : ℝ) (33 / 32), |corrPoly₂Deriv u| ≤ 1 / 2 := fun u hu => by
    have h0 : 0 ≤ u := by linarith [hu.1]
    have p3l := pow_le_pow_left₀ zero_le_one hu.1 3
    have p3u := pow_le_pow_left₀ h0 hu.2 3
    have p4l := pow_le_pow_left₀ zero_le_one hu.1 4
    have p4u := pow_le_pow_left₀ h0 hu.2 4
    have p5l := pow_le_pow_left₀ zero_le_one hu.1 5
    have p5u := pow_le_pow_left₀ h0 hu.2 5
    have p6l := pow_le_pow_left₀ zero_le_one hu.1 6
    have p6u := pow_le_pow_left₀ h0 hu.2 6
    have p8l := pow_le_pow_left₀ zero_le_one hu.1 8
    have p8u := pow_le_pow_left₀ h0 hu.2 8
    have p10l := pow_le_pow_left₀ zero_le_one hu.1 10
    have p10u := pow_le_pow_left₀ h0 hu.2 10
    have p12l := pow_le_pow_left₀ zero_le_one hu.1 12
    have p12u := pow_le_pow_left₀ h0 hu.2 12
    have p14l := pow_le_pow_left₀ zero_le_one hu.1 14
    have p14u := pow_le_pow_left₀ h0 hu.2 14
    rw [abs_le]; unfold corrPoly₂Deriv
    exact ⟨by linarith [hu.1, hu.2], by linarith [hu.1, hu.2]⟩
  have hb2_3 : ∀ u ∈ Icc (8 / 5 : ℝ) (13 / 8), |corrPoly₂Deriv u| ≤ 2 := fun u hu => by
    have ha : (0 : ℝ) ≤ 8 / 5 := by norm_num
    have h0 : 0 ≤ u := by linarith [hu.1]
    have p3l := pow_le_pow_left₀ ha hu.1 3
    have p3u := pow_le_pow_left₀ h0 hu.2 3
    have p4l := pow_le_pow_left₀ ha hu.1 4
    have p4u := pow_le_pow_left₀ h0 hu.2 4
    have p5l := pow_le_pow_left₀ ha hu.1 5
    have p5u := pow_le_pow_left₀ h0 hu.2 5
    have p6l := pow_le_pow_left₀ ha hu.1 6
    have p6u := pow_le_pow_left₀ h0 hu.2 6
    have p8l := pow_le_pow_left₀ ha hu.1 8
    have p8u := pow_le_pow_left₀ h0 hu.2 8
    have p10l := pow_le_pow_left₀ ha hu.1 10
    have p10u := pow_le_pow_left₀ h0 hu.2 10
    have p12l := pow_le_pow_left₀ ha hu.1 12
    have p12u := pow_le_pow_left₀ h0 hu.2 12
    have p14l := pow_le_pow_left₀ ha hu.1 14
    have p14u := pow_le_pow_left₀ h0 hu.2 14
    rw [abs_le]; unfold corrPoly₂Deriv
    exact ⟨by linarith [hu.1, hu.2], by linarith [hu.1, hu.2]⟩
  have hc1 : Continuous corrPoly₁Deriv := by unfold corrPoly₁Deriv; fun_prop
  have hc2 : Continuous corrPoly₂Deriv := by unfold corrPoly₂Deriv; fun_prop
  have h12 := poly_ge_of_deriv_bound (s₀ := 101933 / 100000) (s := s₂) (by norm_num) (by norm_num)
    hs₂_in.1 hs₂_in.2 hc1 hasDerivAt_corrPoly₁ hb1_2
  have h13 := poly_ge_of_deriv_bound (s₀ := 161561 / 100000) (s := s₃) (by norm_num) (by norm_num)
    hs₃_in.1 hs₃_in.2 hc1 hasDerivAt_corrPoly₁ hb1_3
  have h22 := poly_ge_of_deriv_bound (s₀ := 101933 / 100000) (s := s₂) (by norm_num) (by norm_num)
    hs₂_in.1 hs₂_in.2 hc2 hasDerivAt_corrPoly₂ hb2_2
  have h23 := poly_ge_of_deriv_bound (s₀ := 161561 / 100000) (s := s₃) (by norm_num) (by norm_num)
    hs₃_in.1 hs₃_in.2 hc2 hasDerivAt_corrPoly₂ hb2_3
  have hv12 : (-(34565 / 1000000 : ℝ)) < corrPoly₁ (101933 / 100000) - (1 / 2) * (5 / 1000000) := by
    unfold corrPoly₁; norm_num
  have hv13 : (-(1936 / 1000000 : ℝ)) < corrPoly₁ (161561 / 100000) - 2 * (4 / 1000000) := by
    unfold corrPoly₁; norm_num
  have hv22 : (865 / 1000000 : ℝ) < corrPoly₂ (101933 / 100000) - (1 / 2) * (5 / 1000000) := by
    unfold corrPoly₂; norm_num
  have hv23 : (-(303 / 1000000 : ℝ)) < corrPoly₂ (161561 / 100000) - 2 * (4 / 1000000) := by
    unfold corrPoly₂; norm_num
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

private lemma primeJumpWeight_two_three_bounds :
    ((693147 / 1000000 : ℝ) / (141422 / 100000) ≤ primeJumpWeight 2 ∧
      primeJumpWeight 2 ≤ (693148 / 1000000 : ℝ) / (141421 / 100000)) ∧
    ((1098612 / 1000000 : ℝ) / (173206 / 100000) ≤ primeJumpWeight 3 ∧
      primeJumpWeight 3 ≤ (1098613 / 1000000 : ℝ) / (173205 / 100000)) := by
  have hs2_lo : (141421 / 100000 : ℝ) ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hs2_hi : Real.sqrt 2 ≤ 141422 / 100000 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hs3_lo : (173205 / 100000 : ℝ) ≤ Real.sqrt 3 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg 3]
  have hs3_hi : Real.sqrt 3 ≤ 173206 / 100000 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg 3]
  have hp3 : Nat.Prime 3 := by decide
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · unfold primeJumpWeight
    rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    norm_num only [Nat.cast_ofNat]
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith [Real.log_two_gt_d9]
  · unfold primeJumpWeight
    rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    norm_num only [Nat.cast_ofNat]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [Real.log_two_lt_d9]
  · unfold primeJumpWeight
    rw [ArithmeticFunction.vonMangoldt_apply_prime hp3]
    norm_num only [Nat.cast_ofNat]
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith [Real.log_three_gt_d9]
  · unfold primeJumpWeight
    rw [ArithmeticFunction.vonMangoldt_apply_prime hp3]
    norm_num only [Nat.cast_ofNat]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [Real.log_three_lt_d9]

/-- Exact cancellation of the polar term against `2 * oddPoleMoment G ^ 2` for any odd compact
continuous source supported inside `[−17/25, 17/25]` (`34/25 < log 4`). -/
private lemma odd_source_weilQuad_add_two_oddPole_sq_eq (G : C_c(ℝ, ℝ))
    (hodd : ∀ x, G (-x) = -G x) (hsupp : ∀ x, c₀ ≤ |x| → G x = 0)
    (hJ : IntegrableOn (fun t => (autocorr G 0 - autocorr G t) * archLevySinhWeight t)
      (Ioi (0 : ℝ))) :
    weilQuad G + 2 * oddPoleMoment G ^ 2 =
      EF.gammaBracket 0 * autocorr G 0 + biScaleLevyEnergy G -
        2 * primeJumpWeight 2 * autocorr G (Real.log 2) -
        2 * primeJumpWeight 3 * autocorr G (Real.log 3) := by
  have hfull := re_weilFullFunctional_eq_of_compact_finite_jump G hJ
  change weilQuad G = EF.gammaBracket 0 * autocorr G 0 +
    biScaleLevyEnergy G - 2 * fullPairing (autocorr G) at hfull
  have hprime : (∑' n : ℕ, primeTerm (autocorr G) n) =
      primeJumpWeight 2 * autocorr G (Real.log 2) +
        primeJumpWeight 3 * autocorr G (Real.log 3) := by
    rw [tsum_eq_sum (s := ({2, 3} : Finset ℕ)) (fun n hn => ?_),
      Finset.sum_pair (by decide : (2 : ℕ) ≠ 3)]
    · unfold primeTerm SignedPrimePolar.primeWeight primeJumpWeight
      rw [if_pos (by norm_num : 2 ≤ (2 : ℕ)), if_pos (by norm_num : 2 ≤ (3 : ℕ))]
      norm_num only [Nat.cast_ofNat]
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
      by_cases h2 : 2 ≤ n
      · have h4 : (4 : ℝ) ≤ n := by exact_mod_cast (show 4 ≤ n by omega)
        have hlog4 : (34 / 25 : ℝ) < Real.log 4 := by
          rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
          norm_num
          linarith [Real.log_two_gt_d9]
        have hlog : 2 * c₀ < |Real.log n| := by
          have hln : (34 / 25 : ℝ) < Real.log n :=
            lt_of_lt_of_le hlog4 (Real.log_le_log (by norm_num) h4)
          rw [abs_of_pos (by linarith)]
          unfold c₀; linarith
        have hz : autocorr (G : ℝ → ℝ) (Real.log n) = 0 :=
          autocorr_eq_zero_of_far (fun _ hx => hsupp _ hx.le) hlog
        simp only [primeTerm, if_pos h2, hz, mul_zero]
      · simp only [primeTerm, if_neg h2]
  have hpolar : 2 * (∫ t in Ici (0 : ℝ), polarDensity t * autocorr G t) =
      -(2 * oddPoleMoment G ^ 2) := by
    have hm := integral_polar_autocorr_eq_moments G
    have hp := pole_eq_pairings G (map_continuous G) G.hasCompactSupport
    have hc := coshPairing_eq_zero_of_odd hodd
    have he1 : (∫ u, Real.exp (u / 2) * G u) = ∫ u, G u * Real.exp (u / 2) :=
      integral_congr_ae (Eventually.of_forall fun _ => mul_comm _ _)
    have he2 : (∫ u, Real.exp (-(u / 2)) * G u) = ∫ u, G u * Real.exp (-u / 2) :=
      integral_congr_ae (Eventually.of_forall fun u => by
        dsimp only
        rw [show -(u / 2) = -u / 2 by ring, mul_comm])
    rw [he1, he2] at hm
    change (∫ t in Ici (0 : ℝ), polarDensity t * autocorr G t) = _ at hm
    have hsp : sinhPairing G = 2 * oddPoleMoment G := by
      unfold sinhPairing oddPoleMoment
      rw [← MeasureTheory.integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall fun _ => by dsimp only; ring)
    rw [hm]
    rw [hc, hsp] at hp
    nlinarith [hp]
  rw [fullPairing, hprime] at hfull
  linarith

private def ccSource₁ : C_c(ℝ, ℝ) :=
  ⟨⟨refutationSource₁, continuous_refutationSource₁⟩, compact_refutationSource₁⟩

private def ccSource₂ : C_c(ℝ, ℝ) :=
  ⟨⟨refutationSource₂, continuous_refutationSource₂⟩, compact_refutationSource₂⟩

private lemma neg_two_mul_le_pos {w W c C A : ℝ}
    (hw0 : 0 ≤ w) (hw : w ≤ W) (hc : 0 ≤ c) (hA : 0 ≤ A) (hC : -A ≤ C) :
    -2 * w * (c * C) ≤ 2 * W * (c * A) := by
  have h1 : 0 ≤ w * (c * (C + A)) := mul_nonneg hw0 (mul_nonneg hc (by linarith))
  have h2 : 0 ≤ (W - w) * (c * A) := mul_nonneg (by linarith) (mul_nonneg hc hA)
  linarith

private lemma neg_two_mul_le_neg {w₀ w c A C : ℝ}
    (hw₀ : 0 ≤ w₀) (hw : w₀ ≤ w) (hc : 0 ≤ c) (hA : 0 ≤ A) (hC : A ≤ C) :
    -2 * w * (c * C) ≤ -2 * w₀ * (c * A) := by
  have h1 : 0 ≤ w * (c * (C - A)) := mul_nonneg (hw₀.trans hw) (mul_nonneg hc (by linarith))
  have h2 : 0 ≤ (w - w₀) * (c * A) := mul_nonneg (by linarith) (mul_nonneg hc hA)
  linarith

private lemma refutation_markovSum_le :
    (weilQuad refutationSource₁ + 2 * oddPoleMoment refutationSource₁ ^ 2) +
      (weilQuad refutationSource₂ + 2 * oddPoleMoment refutationSource₂ ^ 2) ≤
        404 / 100000 := by
  have heq1 := odd_source_weilQuad_add_two_oddPole_sq_eq ccSource₁ refutationSource₁_odd
    (fun _ hx => refutationSource₁_eq_zero_of_far hx) jump_inner_le_and_integrable₁.1
  have heq2 := odd_source_weilQuad_add_two_oddPole_sq_eq ccSource₂ refutationSource₂_odd
    (fun _ hx => refutationSource₂_eq_zero_of_far hx) jump_inner_le_and_integrable₂.1
  have hcc1 : (ccSource₁ : ℝ → ℝ) = refutationSource₁ := rfl
  have hcc2 : (ccSource₂ : ℝ → ℝ) = refutationSource₂ := rfl
  rw [hcc1] at heq1
  rw [hcc2] at heq2
  have hj1 := jump_inner_le_and_integrable₁.2
  have hj2 := jump_inner_le_and_integrable₂.2
  have hconst := gammaBracket_add_two_archLevyAntideriv_34_25_le
  obtain ⟨hc12, hc13, hc22, hc23⟩ := prime_corr_bounds
  obtain ⟨⟨hw2_lo, hw2_hi⟩, ⟨hw3_lo, hw3_hi⟩⟩ := primeJumpWeight_two_three_bounds
  have hl2_in : 0 ≤ Real.log 2 ∧ Real.log 2 ≤ 34 / 25 :=
    ⟨by linarith [Real.log_two_gt_d9], by linarith [Real.log_two_lt_d9]⟩
  have hl3_in : 0 ≤ Real.log 3 ∧ Real.log 3 ≤ 34 / 25 :=
    ⟨by linarith [Real.log_three_gt_d9], by linarith [Real.log_three_lt_d9]⟩
  rw [autocorr_refutationSource₁ hl2_in.1 hl2_in.2, autocorr_refutationSource₁ hl3_in.1 hl3_in.2] at heq1
  rw [autocorr_refutationSource₂ hl2_in.1 hl2_in.2, autocorr_refutationSource₂ hl3_in.1 hl3_in.2] at heq2
  rw [autocorr_refutationSource₁_zero] at heq1 hj1
  rw [autocorr_refutationSource₂_zero] at heq2 hj2
  -- Bound `-2 * w_p * autocorr` term by term
  have hp12 : -2 * primeJumpWeight 2 * (c₀ * corrPoly₁ (Real.log 2 / c₀)) ≤
      2 * ((693148 / 1000000 : ℝ) / (141421 / 100000)) * (c₀ * (34565 / 1000000 : ℝ)) :=
    neg_two_mul_le_pos (le_trans (by norm_num) hw2_lo) hw2_hi (by unfold c₀; norm_num)
      (by norm_num) hc12
  have hp13 : -2 * primeJumpWeight 3 * (c₀ * corrPoly₁ (Real.log 3 / c₀)) ≤
      2 * ((1098613 / 1000000 : ℝ) / (173205 / 100000)) * (c₀ * (1936 / 1000000 : ℝ)) :=
    neg_two_mul_le_pos (le_trans (by norm_num) hw3_lo) hw3_hi (by unfold c₀; norm_num)
      (by norm_num) hc13
  have hp22 : -2 * primeJumpWeight 2 * ((9 / 2 : ℝ) ^ 2 * (c₀ * corrPoly₂ (Real.log 2 / c₀))) ≤
      -2 * ((693147 / 1000000 : ℝ) / (141422 / 100000)) *
        ((9 / 2 : ℝ) ^ 2 * (c₀ * (865 / 1000000 : ℝ))) := by
    have h := neg_two_mul_le_neg (c := (9 / 2 : ℝ) ^ 2 * c₀) (by norm_num) hw2_lo
      (by unfold c₀; norm_num) (by norm_num) hc22
    simpa only [mul_assoc] using h
  have hp23 : -2 * primeJumpWeight 3 * ((9 / 2 : ℝ) ^ 2 * (c₀ * corrPoly₂ (Real.log 3 / c₀))) ≤
      2 * ((1098613 / 1000000 : ℝ) / (173205 / 100000)) *
        ((9 / 2 : ℝ) ^ 2 * (c₀ * (303 / 1000000 : ℝ))) := by
    have h := neg_two_mul_le_pos (c := (9 / 2 : ℝ) ^ 2 * c₀) (le_trans (by norm_num) hw3_lo) hw3_hi
      (by unfold c₀; norm_num) (by norm_num) hc23
    simpa only [mul_assoc] using h
  have hm1 : weilQuad refutationSource₁ + 2 * oddPoleMoment refutationSource₁ ^ 2 ≤
      295 / 100000 := by
    unfold c₀ at heq1 hj1 hp12 hp13
    linarith
  have hm2 : weilQuad refutationSource₂ + 2 * oddPoleMoment refutationSource₂ ^ 2 ≤
      109 / 100000 := by
    unfold c₀ at heq2 hj2 hp22 hp23
    linarith
  linarith

/-! ### 5. Three-chord Pythagorean `L^{1/2}` lower bound -/

private lemma linear_le_sqrt_add_sq {α β A B : ℝ} (hu : α ^ 2 + β ^ 2 = 1) :
    α * A + β * B ≤ Real.sqrt (A ^ 2 + B ^ 2) := by
  by_cases hneg : α * A + β * B ≤ 0
  · exact hneg.trans (Real.sqrt_nonneg _)
  · push Not at hneg
    have hsq : (α * A + β * B) ^ 2 ≤ A ^ 2 + B ^ 2 := by
      have hid : (A ^ 2 + B ^ 2) - (α * A + β * B) ^ 2 = (β * A - α * B) ^ 2 := by
        linear_combination -(A ^ 2 + B ^ 2) * hu
      nlinarith [sq_nonneg (β * A - α * B)]
    exact (Real.sqrt_sq hneg.le).symm.trans_le (Real.sqrt_le_sqrt hsq)

private def chordPoly₁ (u : ℝ) : ℝ :=
  (58956 / 85625 : ℝ) * u ^ 2 + (-289025143 / 107031250 : ℝ) * u ^ 4 +
    (354209093 / 107031250 : ℝ) * u ^ 6 + (-136122757 / 107031250 : ℝ) * u ^ 8 +
    (-2756193 / 107031250 : ℝ) * u ^ 10

private def chordAnti₁ (u : ℝ) : ℝ :=
  (19652 / 85625 : ℝ) * u ^ 3 + (-289025143 / 535156250 : ℝ) * u ^ 5 +
    (50601299 / 107031250 : ℝ) * u ^ 7 + (-136122757 / 963281250 : ℝ) * u ^ 9 +
    (-250563 / 107031250 : ℝ) * u ^ 11

private def chordPoly₂ (u : ℝ) : ℝ :=
  (14739 / 25000 : ℝ) * u ^ 2 + (-218798143 / 125000000 : ℝ) * u ^ 4 +
    (537770333 / 312500000 : ℝ) * u ^ 6 + (-343009187 / 625000000 : ℝ) * u ^ 8 +
    (-1753941 / 156250000 : ℝ) * u ^ 10

private def chordAnti₂ (u : ℝ) : ℝ :=
  (4913 / 25000 : ℝ) * u ^ 3 + (-218798143 / 625000000 : ℝ) * u ^ 5 +
    (537770333 / 2187500000 : ℝ) * u ^ 7 + (-343009187 / 5625000000 : ℝ) * u ^ 9 +
    (-1753941 / 1718750000 : ℝ) * u ^ 11

private def chordPoly₃ (u : ℝ) : ℝ :=
  (-867 / 36250 : ℝ) * u ^ 2 + (9265051 / 6250000 : ℝ) * u ^ 4 +
    (-259678349 / 90625000 : ℝ) * u ^ 6 + (249993959 / 181250000 : ℝ) * u ^ 8 +
    (250563 / 9062500 : ℝ) * u ^ 10

private def chordAnti₃ (u : ℝ) : ℝ :=
  (-289 / 36250 : ℝ) * u ^ 3 + (9265051 / 31250000 : ℝ) * u ^ 5 +
    (-37096907 / 90625000 : ℝ) * u ^ 7 + (249993959 / 1631250000 : ℝ) * u ^ 9 +
    (250563 / 99687500 : ℝ) * u ^ 11

private lemma refutation_halfNorm_ge :
    (4554 / 100000 : ℝ) ≤
      ∫ x in Ioo (-c₀) c₀,
        Real.sqrt (refutationSource₁ x ^ 2 + refutationSource₂ x ^ 2) * |Real.sinh (x / 2)| := by
  set g : ℝ → ℝ := fun x =>
    Real.sqrt (refutationSource₁ x ^ 2 + refutationSource₂ x ^ 2) * |Real.sinh (x / 2)|
  have hg_cont : Continuous g :=
    (Real.continuous_sqrt.comp
      (((continuous_pow 2).comp continuous_refutationSource₁).add
        ((continuous_pow 2).comp continuous_refutationSource₂))).mul
      (continuous_abs.comp (Real.continuous_sinh.comp (continuous_id.div_const 2)))
  have hg_even : ∀ x, g (-x) = g x := fun x => by
    dsimp only [g]
    rw [refutationSource₁_odd, refutationSource₂_odd, neg_sq, neg_sq,
      show -x / 2 = -(x / 2) by ring, Real.sinh_neg, abs_neg]
  -- Symmetry: `∫_{Ioo (-c₀) c₀} g = 2 * ∫_0^{c₀} g`
  have hsym : (∫ x in Ioo (-c₀) c₀, g x) = 2 * ∫ x in (0 : ℝ)..c₀, g x := by
    rw [← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by unfold c₀; norm_num),
      ← intervalIntegral.integral_add_adjacent_intervals
        (hg_cont.intervalIntegrable (-c₀) 0) (hg_cont.intervalIntegrable 0 c₀)]
    have hleft : (∫ x in (-c₀)..0, g x) = ∫ x in (0 : ℝ)..c₀, g x := by
      have hc := intervalIntegral.integral_comp_neg g (a := 0) (b := c₀)
      rw [neg_zero] at hc
      rw [← hc]
      exact intervalIntegral.integral_congr fun x _ => hg_even x
    rw [hleft]
    ring
  -- Split `0..c₀` at `(7/20)*c₀` and `(1/2)*c₀`
  have hsplit : 2 * (∫ x in (0 : ℝ)..c₀, g x) =
      2 * (∫ x in (0 : ℝ)..(7 / 20 * c₀), g x) +
        2 * (∫ x in (7 / 20 * c₀)..(1 / 2 * c₀), g x) +
        2 * (∫ x in (1 / 2 * c₀)..c₀, g x) := by
    have h1 := intervalIntegral.integral_add_adjacent_intervals
      (hg_cont.intervalIntegrable (μ := volume) 0 (7 / 20 * c₀))
      (hg_cont.intervalIntegrable (μ := volume) (7 / 20 * c₀) (1 / 2 * c₀))
    have h2 := intervalIntegral.integral_add_adjacent_intervals
      (hg_cont.intervalIntegrable (μ := volume) 0 (1 / 2 * c₀))
      (hg_cont.intervalIntegrable (μ := volume) (1 / 2 * c₀) c₀)
    linarith
  -- Pointwise lower bound helper for any Pythagorean unit chord `(α, β)` on `[0, c₀]`
  have hpt_chord : ∀ {α β x : ℝ}, α ^ 2 + β ^ 2 = 1 → 0 ≤ x → x ≤ c₀ →
      (α * poly₁ (x / c₀) + β * ((9 / 2 : ℝ) * poly₂ (x / c₀))) *
        (x / 2 + (x / 2) ^ 3 / 6) ≤ g x := fun {α β x} hu hx0 hxc => by
    dsimp only [g]
    have hx_half : 0 ≤ x / 2 := by positivity
    have hsh_nn : 0 ≤ x / 2 + (x / 2) ^ 3 / 6 := by positivity
    have hsh : x / 2 + (x / 2) ^ 3 / 6 ≤ |Real.sinh (x / 2)| :=
      (cubic_le_sinh_of_nonneg hx_half).trans (le_abs_self _)
    have hpyth : α * poly₁ (x / c₀) + β * ((9 / 2 : ℝ) * poly₂ (x / c₀)) ≤
        Real.sqrt (refutationSource₁ x ^ 2 + refutationSource₂ x ^ 2) := by
      rw [refutationSource₁_inside (by unfold c₀; linarith) hxc,
        refutationSource₂_inside (by unfold c₀; linarith) hxc]
      exact linear_le_sqrt_add_sq hu
    exact (mul_le_mul_of_nonneg_right hpyth hsh_nn).trans
      (mul_le_mul_of_nonneg_left hsh (Real.sqrt_nonneg _))
  -- Chord 1 on `[0, 7/20 * c₀]` with `(105/137, -88/137)`
  have hc1 : (7296 / 1000000 : ℝ) ≤ 2 * ∫ x in (0 : ℝ)..(7 / 20 * c₀), g x := by
    have hd : ∀ u : ℝ, HasDerivAt chordAnti₁ (chordPoly₁ u) u := fun u => by
      unfold chordAnti₁
      refine (((((hasDerivAt_succ_pow _ 2 u).add (hasDerivAt_succ_pow _ 4 u)).add
        (hasDerivAt_succ_pow _ 6 u)).add (hasDerivAt_succ_pow _ 8 u)).add
        (hasDerivAt_succ_pow _ 10 u)).congr_deriv (by unfold chordPoly₁; ring)
    have hcp : Continuous fun x : ℝ => (1 / (2 * c₀)) * chordPoly₁ (x / c₀) := by
      unfold chordPoly₁ c₀; fun_prop
    have hm := intervalIntegral.integral_mono_on (by unfold c₀; norm_num)
      (hcp.intervalIntegrable (μ := volume) 0 (7 / 20 * c₀))
      (hg_cont.intervalIntegrable (μ := volume) 0 (7 / 20 * c₀))
      fun x hx => by
        have h := hpt_chord (α := 105 / 137) (β := -(88 / 137)) (by norm_num) hx.1
          (by unfold c₀ at hx ⊢; linarith [hx.2])
        exact (show (1 / (2 * c₀)) * chordPoly₁ (x / c₀) = _ by
          unfold chordPoly₁ poly₁ poly₂ c₀; ring).trans_le h
    have hint : (∫ x in (0 : ℝ)..(7 / 20 * c₀), (1 / (2 * c₀)) * chordPoly₁ (x / c₀)) =
        (1 / 2 : ℝ) * (chordAnti₁ (7 / 20) - chordAnti₁ 0) := by
      have hd_x : ∀ x : ℝ, HasDerivAt (fun z => (1 / (2 * c₀)) * (c₀ * chordAnti₁ (z / c₀)))
          ((1 / (2 * c₀)) * chordPoly₁ (x / c₀)) x := fun x =>
        (hasDerivAt_scaled (F := chordAnti₁) (F' := chordPoly₁) (hd (x / c₀))).const_mul _
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd_x x)
        (hcp.intervalIntegrable _ _)]
      have h7 : (7 / 20 * c₀) / c₀ = 7 / 20 := by unfold c₀; norm_num
      have h0 : (0 : ℝ) / c₀ = 0 := by norm_num
      rw [h7, h0]; unfold c₀; ring
    rw [hint] at hm
    have hnum : (7296 / 1000000 : ℝ) ≤ chordAnti₁ (7 / 20) - chordAnti₁ 0 := by
      unfold chordAnti₁; norm_num
    linarith
  -- Chord 2 on `[7/20 * c₀, 1/2 * c₀]` with `(24/25, -7/25)`
  have hc2 : (8685 / 1000000 : ℝ) ≤ 2 * ∫ x in (7 / 20 * c₀)..(1 / 2 * c₀), g x := by
    have hd : ∀ u : ℝ, HasDerivAt chordAnti₂ (chordPoly₂ u) u := fun u => by
      unfold chordAnti₂
      refine (((((hasDerivAt_succ_pow _ 2 u).add (hasDerivAt_succ_pow _ 4 u)).add
        (hasDerivAt_succ_pow _ 6 u)).add (hasDerivAt_succ_pow _ 8 u)).add
        (hasDerivAt_succ_pow _ 10 u)).congr_deriv (by unfold chordPoly₂; ring)
    have hcp : Continuous fun x : ℝ => (1 / (2 * c₀)) * chordPoly₂ (x / c₀) := by
      unfold chordPoly₂ c₀; fun_prop
    have hm := intervalIntegral.integral_mono_on (by unfold c₀; norm_num)
      (hcp.intervalIntegrable (μ := volume) (7 / 20 * c₀) (1 / 2 * c₀))
      (hg_cont.intervalIntegrable (μ := volume) (7 / 20 * c₀) (1 / 2 * c₀))
      fun x hx => by
        have h := hpt_chord (α := 24 / 25) (β := -(7 / 25)) (x := x) (by norm_num)
          (by unfold c₀ at hx; linarith [hx.1]) (by unfold c₀ at hx ⊢; linarith [hx.2])
        exact (show (1 / (2 * c₀)) * chordPoly₂ (x / c₀) = _ by
          unfold chordPoly₂ poly₁ poly₂ c₀; ring).trans_le h
    have hint : (∫ x in (7 / 20 * c₀)..(1 / 2 * c₀), (1 / (2 * c₀)) * chordPoly₂ (x / c₀)) =
        (1 / 2 : ℝ) * (chordAnti₂ (1 / 2) - chordAnti₂ (7 / 20)) := by
      have hd_x : ∀ x : ℝ, HasDerivAt (fun z => (1 / (2 * c₀)) * (c₀ * chordAnti₂ (z / c₀)))
          ((1 / (2 * c₀)) * chordPoly₂ (x / c₀)) x := fun x =>
        (hasDerivAt_scaled (F := chordAnti₂) (F' := chordPoly₂) (hd (x / c₀))).const_mul _
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd_x x)
        (hcp.intervalIntegrable _ _)]
      have h12 : (1 / 2 * c₀) / c₀ = 1 / 2 := by unfold c₀; norm_num
      have h7 : (7 / 20 * c₀) / c₀ = 7 / 20 := by unfold c₀; norm_num
      rw [h12, h7]; unfold c₀; ring
    rw [hint] at hm
    have hnum : (8685 / 1000000 : ℝ) ≤ chordAnti₂ (1 / 2) - chordAnti₂ (7 / 20) := by
      unfold chordAnti₂; norm_num
    linarith
  -- Chord 3 on `[1/2 * c₀, c₀]` with `(21/29, 20/29)`
  have hc3 : (29559 / 1000000 : ℝ) ≤ 2 * ∫ x in (1 / 2 * c₀)..c₀, g x := by
    have hd : ∀ u : ℝ, HasDerivAt chordAnti₃ (chordPoly₃ u) u := fun u => by
      unfold chordAnti₃
      refine (((((hasDerivAt_succ_pow _ 2 u).add (hasDerivAt_succ_pow _ 4 u)).add
        (hasDerivAt_succ_pow _ 6 u)).add (hasDerivAt_succ_pow _ 8 u)).add
        (hasDerivAt_succ_pow _ 10 u)).congr_deriv (by unfold chordPoly₃; ring)
    have hcp : Continuous fun x : ℝ => (1 / (2 * c₀)) * chordPoly₃ (x / c₀) := by
      unfold chordPoly₃ c₀; fun_prop
    have hm := intervalIntegral.integral_mono_on (by unfold c₀; norm_num)
      (hcp.intervalIntegrable (μ := volume) (1 / 2 * c₀) c₀)
      (hg_cont.intervalIntegrable (μ := volume) (1 / 2 * c₀) c₀)
      fun x hx => by
        have h := hpt_chord (α := 21 / 29) (β := 20 / 29) (by norm_num)
          (by unfold c₀ at hx; linarith [hx.1]) hx.2
        exact (show (1 / (2 * c₀)) * chordPoly₃ (x / c₀) = _ by
          unfold chordPoly₃ poly₁ poly₂ c₀; ring).trans_le h
    have hint : (∫ x in (1 / 2 * c₀)..c₀, (1 / (2 * c₀)) * chordPoly₃ (x / c₀)) =
        (1 / 2 : ℝ) * (chordAnti₃ 1 - chordAnti₃ (1 / 2)) := by
      have hd_x : ∀ x : ℝ, HasDerivAt (fun z => (1 / (2 * c₀)) * (c₀ * chordAnti₃ (z / c₀)))
          ((1 / (2 * c₀)) * chordPoly₃ (x / c₀)) x := fun x =>
        (hasDerivAt_scaled (F := chordAnti₃) (F' := chordPoly₃) (hd (x / c₀))).const_mul _
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd_x x)
        (hcp.intervalIntegrable _ _)]
      have h1 : c₀ / c₀ = 1 := by unfold c₀; norm_num
      have h12 : (1 / 2 * c₀) / c₀ = 1 / 2 := by unfold c₀; norm_num
      rw [h1, h12]; unfold c₀; ring
    rw [hint] at hm
    have hnum : (29559 / 1000000 : ℝ) ≤ chordAnti₃ 1 - chordAnti₃ (1 / 2) := by
      unfold chordAnti₃; norm_num
    linarith
  rw [hsym, hsplit]
  linarith

/-! ### 6. Mollification and unconditional refutation theorems below `log 4` -/

private lemma mollifier_even' (k : ℕ) (t : ℝ) :
    CHMDDoobGraph.mollifier k (-t) = CHMDDoobGraph.mollifier k t := by
  unfold CHMDDoobGraph.mollifier
  rw [ContDiffBump.normed_def, ContDiffBump.normed_def, ContDiffBump.neg]

private lemma smooth_odd_of_odd {G : ℝ → ℝ} (hodd : ∀ x, G (-x) = -G x) (k : ℕ) (x : ℝ) :
    CHMDDoobGraph.smooth G k (-x) = -CHMDDoobGraph.smooth G k x := by
  change (∫ t, CHMDDoobGraph.mollifier k t * G (-x - t)) =
    -(∫ t, CHMDDoobGraph.mollifier k t * G (x - t))
  rw [← integral_neg_eq_self (fun t => CHMDDoobGraph.mollifier k t * G (-x - t)) volume,
    ← MeasureTheory.integral_neg]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  dsimp only
  rw [mollifier_even', show -x - -t = -(x - t) by ring, hodd, mul_neg]

private lemma smooth_eq_zero_of_narrow {G : ℝ → ℝ} {R : ℝ} (hR : ∀ x, R ≤ |x| → G x = 0)
    {k : ℕ} (hk : 100 ≤ k) {x : ℝ} (hx : R + 1 / 400 < |x|) :
    CHMDDoobGraph.smooth G k x = 0 := by
  have hkr : (100 : ℝ) ≤ k := by exact_mod_cast hk
  have hrad : 1 / (4 * ((k : ℝ) + 1)) ≤ (1 / 400 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  change (∫ t, CHMDDoobGraph.mollifier k t * G (x - t)) = 0
  refine integral_eq_zero_of_ae (Eventually.of_forall fun t => ?_)
  dsimp only [Pi.zero_apply]
  by_cases ht : 1 / (4 * ((k : ℝ) + 1)) ≤ |t|
  · have hm : CHMDDoobGraph.mollifier k t = 0 := by
      apply Function.notMem_support.mp
      change t ∉ Function.support ((_root_.RHTower.WeilOneSided.narrowBump k).normed volume)
      rw [(_root_.RHTower.WeilOneSided.narrowBump k).support_normed_eq, Metric.mem_ball,
        dist_zero_right, Real.norm_eq_abs]
      exact not_lt.mpr ht
    rw [hm, zero_mul]
  · have hsub : R ≤ |x - t| := by linarith [abs_sub_abs_le_abs_sub x t, not_le.mp ht]
    rw [hR (x - t) hsub, mul_zero]

private lemma oddPoleMoment_smooth_tendsto {G : ℝ → ℝ} (hG : Continuous G) (hGc : HasCompactSupport G)
    {M R : ℝ} (hM0 : 0 ≤ M) (hM : ∀ x, |G x| ≤ M) (hR : ∀ x, R < |x| → G x = 0) :
    Tendsto (fun k : ℕ => oddPoleMoment (CHMDDoobGraph.smooth G k)) atTop (𝓝 (oddPoleMoment G)) := by
  have hf2 : MemLp G 2 volume := hG.memLp_of_hasCompactSupport hGc
  have hsh : Continuous fun x : ℝ => Real.sinh (x / 2) :=
    Real.continuous_sinh.comp (continuous_id.div_const 2)
  have hbint : Integrable (fun x => (Icc (-(R + 1)) (R + 1)).indicator
      (fun x => M * |Real.sinh (x / 2)|) x) :=
    (((continuous_const.mul (continuous_abs.comp hsh)).integrableOn_Icc
      (μ := volume)).integrable_indicator measurableSet_Icc)
  unfold oddPoleMoment
  refine tendsto_integral_of_dominated_convergence _ (fun k => ?_) hbint (fun k => ?_) ?_
  · exact (((CHMDDoobGraph.smooth_contDiff hf2 k).continuous).mul hsh).aestronglyMeasurable
  · refine Eventually.of_forall fun x => ?_
    by_cases hx : x ∈ Icc (-(R + 1)) (R + 1)
    · rw [indicator_of_mem hx, Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (CHMDDoobGraph.smooth_bound hM0 hM k x) (abs_nonneg _)
    · have hx' : R + 1 < |x| := not_le.mp fun h => hx (abs_le.mp h)
      rw [indicator_of_notMem hx, smooth_eq_zero_of_far hR k hx', zero_mul, norm_zero]
  · exact Eventually.of_forall fun x =>
      (smooth_tendsto_of_continuous hG x).mul_const (Real.sinh (x / 2))

private lemma halfNorm_smooth_tendsto {c : ℝ} :
    Tendsto (fun k : ℕ => ∫ x in Ioo (-c) c,
        Real.sqrt (CHMDDoobGraph.smooth refutationSource₁ k x ^ 2 +
          CHMDDoobGraph.smooth refutationSource₂ k x ^ 2) * |Real.sinh (x / 2)|)
      atTop
      (𝓝 (∫ x in Ioo (-c) c,
        Real.sqrt (refutationSource₁ x ^ 2 + refutationSource₂ x ^ 2) * |Real.sinh (x / 2)|)) := by
  have hf1 : MemLp refutationSource₁ 2 volume :=
    continuous_refutationSource₁.memLp_of_hasCompactSupport compact_refutationSource₁
  have hf2 : MemLp refutationSource₂ 2 volume :=
    continuous_refutationSource₂.memLp_of_hasCompactSupport compact_refutationSource₂
  have hsh : Continuous fun x : ℝ => |Real.sinh (x / 2)| :=
    continuous_abs.comp (Real.continuous_sinh.comp (continuous_id.div_const 2))
  have hbint : IntegrableOn (fun x => Real.sqrt (1 + (9 / 2 : ℝ) ^ 2) * |Real.sinh (x / 2)|)
      (Ioo (-c) c) :=
    (continuous_const.mul hsh).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  refine tendsto_integral_of_dominated_convergence _ (fun k => ?_) hbint (fun k => ?_) ?_
  · have hc1 := (CHMDDoobGraph.smooth_contDiff hf1 k).continuous
    have hc2 := (CHMDDoobGraph.smooth_contDiff hf2 k).continuous
    exact ((Real.continuous_sqrt.comp
      (((continuous_pow 2).comp hc1).add ((continuous_pow 2).comp hc2))).mul
      hsh).continuousOn.aestronglyMeasurable measurableSet_Ioo
  · refine ae_restrict_of_forall_mem measurableSet_Ioo fun x _ => ?_
    have hb1 := CHMDDoobGraph.smooth_bound zero_le_one abs_refutationSource₁_le k x
    have hb2 := CHMDDoobGraph.smooth_bound (by norm_num : (0 : ℝ) ≤ 9 / 2) abs_refutationSource₂_le k x
    have hs1 : CHMDDoobGraph.smooth refutationSource₁ k x ^ 2 ≤ 1 := by
      have h := pow_le_pow_left₀ (abs_nonneg _) hb1 2; rwa [sq_abs, one_pow] at h
    have hs2 : CHMDDoobGraph.smooth refutationSource₂ k x ^ 2 ≤ (9 / 2 : ℝ) ^ 2 := by
      have h := pow_le_pow_left₀ (abs_nonneg _) hb2 2; rwa [sq_abs] at h
    rw [Real.norm_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _))]
    exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (by linarith)) (abs_nonneg _)
  · exact Eventually.of_forall fun x =>
      ((Real.continuous_sqrt.tendsto _).comp
        (((smooth_tendsto_of_continuous continuous_refutationSource₁ x).pow 2).add
          ((smooth_tendsto_of_continuous continuous_refutationSource₂ x).pow 2))).mul_const _

/-- **Explicit smooth two-profile witness with strictly negative `L^{1/2}` dual below `log 4`.**
For every half-aperture `c > 273/400` (`2c > 273/200 = 1.365`), including every
`c ∈ (273/400, log 2)` (`2c ∈ (273/200, log 4)`), there exist `C²_c` odd tests `F₁, F₂` supported
strictly inside `(−c, c)` whose Markov energy sum is strictly less than twice the squared
`L^{1/2}` sinh-weighted norm of `√(F₁² + F₂²)`. -/
theorem exists_two_odd_tests_halfNormDual_neg_below_log_four {c : ℝ} (hc : 273 / 400 < c) :
    ∃ F₁ F₂ : ℝ → ℝ,
      ContDiff ℝ 2 F₁ ∧ HasCompactSupport F₁ ∧ (∀ x, F₁ (-x) = -F₁ x) ∧
        (∀ x, (273 / 400 : ℝ) < |x| → F₁ x = 0) ∧
      ContDiff ℝ 2 F₂ ∧ HasCompactSupport F₂ ∧ (∀ x, F₂ (-x) = -F₂ x) ∧
        (∀ x, (273 / 400 : ℝ) < |x| → F₂ x = 0) ∧
      markovEnergy (fun x => (F₁ x : ℂ)) + markovEnergy (fun x => (F₂ x : ℂ)) <
        2 * (∫ x in Ioo (-c) c, Real.sqrt (F₁ x ^ 2 + F₂ x ^ 2) * |Real.sinh (x / 2)|) ^ 2 := by
  have hc0_lt : c₀ < c := by unfold c₀; linarith
  -- Extend `Ioo (-c₀) c₀` lower bound to `Ioo (-c) c`
  have hI_ge : (4554 / 100000 : ℝ) ≤
      ∫ x in Ioo (-c) c,
        Real.sqrt (refutationSource₁ x ^ 2 + refutationSource₂ x ^ 2) * |Real.sinh (x / 2)| := by
    refine refutation_halfNorm_ge.trans (setIntegral_mono_set ?_ ?_ ?_)
    · exact ((Real.continuous_sqrt.comp
        (((continuous_pow 2).comp continuous_refutationSource₁).add
          ((continuous_pow 2).comp continuous_refutationSource₂))).mul
        (continuous_abs.comp (Real.continuous_sinh.comp
          (continuous_id.div_const 2)))).integrableOn_Icc.mono_set Ioo_subset_Icc_self
    · exact Eventually.of_forall fun _ => mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)
    · exact Eventually.of_forall fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hstrict_lim :
      (weilQuad refutationSource₁ + 2 * oddPoleMoment refutationSource₁ ^ 2) +
        (weilQuad refutationSource₂ + 2 * oddPoleMoment refutationSource₂ ^ 2) <
        2 * (∫ x in Ioo (-c) c,
          Real.sqrt (refutationSource₁ x ^ 2 + refutationSource₂ x ^ 2) * |Real.sinh (x / 2)|) ^ 2 := by
    have hsq := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4554 / 100000) hI_ge 2
    nlinarith [refutation_markovSum_le]
  -- Pass to `CHMDDoobGraph.smooth _ k` along `k → ∞`
  have hf1_2 : MemLp refutationSource₁ 2 volume :=
    continuous_refutationSource₁.memLp_of_hasCompactSupport compact_refutationSource₁
  have hf2_2 : MemLp refutationSource₂ 2 volume :=
    continuous_refutationSource₂.memLp_of_hasCompactSupport compact_refutationSource₂
  have hQ1 : Tendsto (fun k : ℕ => weilQuad (CHMDDoobGraph.smooth refutationSource₁ k))
      atTop (𝓝 (weilQuad refutationSource₁)) :=
    re_weilFullFunctional_smooth_tendsto ccSource₁ jump_inner_le_and_integrable₁.1
  have hQ2 : Tendsto (fun k : ℕ => weilQuad (CHMDDoobGraph.smooth refutationSource₂ k))
      atTop (𝓝 (weilQuad refutationSource₂)) :=
    re_weilFullFunctional_smooth_tendsto ccSource₂ jump_inner_le_and_integrable₂.1
  have hO1 := oddPoleMoment_smooth_tendsto continuous_refutationSource₁ compact_refutationSource₁
    zero_le_one abs_refutationSource₁_le (fun _ hx => refutationSource₁_eq_zero_of_far hx.le)
  have hO2 := oddPoleMoment_smooth_tendsto continuous_refutationSource₂ compact_refutationSource₂
    (by norm_num) abs_refutationSource₂_le (fun _ hx => refutationSource₂_eq_zero_of_far hx.le)
  have hLHS := (hQ1.add ((hO1.pow 2).const_mul 2)).add (hQ2.add ((hO2.pow 2).const_mul 2))
  have hRHS := ((halfNorm_smooth_tendsto (c := c)).pow 2).const_mul 2
  have hev := (hLHS.sub hRHS).eventually (Iio_mem_nhds (sub_neg.mpr hstrict_lim))
  obtain ⟨k, hk100, hk_neg⟩ := ((eventually_ge_atTop 100).and hev).exists
  set F₁ := CHMDDoobGraph.smooth refutationSource₁ k
  set F₂ := CHMDDoobGraph.smooth refutationSource₂ k
  have hF₁_diff : ContDiff ℝ 2 F₁ := (CHMDDoobGraph.smooth_contDiff hf1_2 k).of_le (by simp)
  have hF₂_diff : ContDiff ℝ 2 F₂ := (CHMDDoobGraph.smooth_contDiff hf2_2 k).of_le (by simp)
  have hF₁_cs : HasCompactSupport F₁ := CHMDDoobGraph.smooth_compact compact_refutationSource₁ k
  have hF₂_cs : HasCompactSupport F₂ := CHMDDoobGraph.smooth_compact compact_refutationSource₂ k
  have hF₁_odd : ∀ x, F₁ (-x) = -F₁ x := smooth_odd_of_odd refutationSource₁_odd k
  have hF₂_odd : ∀ x, F₂ (-x) = -F₂ x := smooth_odd_of_odd refutationSource₂_odd k
  have hF₁_supp : ∀ x, (273 / 400 : ℝ) < |x| → F₁ x = 0 := fun x hx =>
    smooth_eq_zero_of_narrow (fun _ h => refutationSource₁_eq_zero_of_far h) hk100
      (by unfold c₀; linarith)
  have hF₂_supp : ∀ x, (273 / 400 : ℝ) < |x| → F₂ x = 0 := fun x hx =>
    smooth_eq_zero_of_narrow (fun _ h => refutationSource₂_eq_zero_of_far h) hk100
      (by unfold c₀; linarith)
  refine ⟨F₁, F₂, hF₁_diff, hF₁_cs, hF₁_odd, hF₁_supp,
    hF₂_diff, hF₂_cs, hF₂_odd, hF₂_supp, ?_⟩
  rw [markovEnergy_eq_weilQuad_add_odd_sq_of_odd hF₁_diff hF₁_cs hF₁_odd,
    markovEnergy_eq_weilQuad_add_odd_sq_of_odd hF₂_diff hF₂_cs hF₂_odd]
  exact sub_neg.mp hk_neg

/-- **Unconditional refutation of all `C²_c` odd pole-charged supersolutions below `log 4`.**
For every half-aperture `c > 273/400` (in particular every `c ∈ (273/400, log 2)`, i.e., window
length `2c ∈ (273/200, log 4)`), no compactly supported `C²` gauge `ω` (even if extended
arbitrarily outside `(−c, c)`), odd on `(−c, c)` and strictly positive on `(0, c)`, can satisfy
both the sinh-charged supersolution defect inequality on `(−c, c)` and nonnegativity of `J_{Φω}`
on even `C²_c` profiles supported in `(−c, c)`. -/
theorem not_exists_odd_sinhCharged_gauge_below_log_four {c : ℝ} (hc : 273 / 400 < c) :
    ¬ ∃ ω : ℝ → ℝ, ContDiff ℝ 2 ω ∧ HasCompactSupport ω ∧
      (∀ x ∈ Ioo (-c) c, ω (-x) = -ω x) ∧
      (∀ x ∈ Ioo (0 : ℝ) c, 0 < ω x) ∧
      (∀ x ∈ Ioo (-c) c, 0 ≤ ω x * (markovDefect ω x -
        2 * sinhCharge ω (Ioo (-c) c) * (riemannKernelReal x * Real.sinh (x / 2)))) ∧
      (∀ u : ℝ → ℝ, ContDiff ℝ 2 u → HasCompactSupport u → (∀ x, u (-x) = u x) →
        (∀ x, x ∉ Ioo (-c) c → u x = 0) →
        0 ≤ signedJumpEnergy (fun y => riemannKernelReal y * ω y) u) := by
  obtain ⟨F₁, F₂, hF₁, hF₁c, hF₁odd, hF₁supp, hF₂, hF₂c, hF₂odd, hF₂supp, hdual⟩ :=
    exists_two_odd_tests_halfNormDual_neg_below_log_four hc
  exact not_exists_odd_sinhCharged_gauge_of_two_odd_tests (by norm_num) hc
    hF₁ hF₁c hF₁odd hF₁supp hF₂ hF₂c hF₂odd hF₂supp hdual

/-- **Unconditional refutation of all odd non-compact theta-gauge outside-charge certificates
below `log 4`.** For every half-aperture `c > 273/400` (in particular every `c ∈ (273/400, log 2)`),
and every finite theta-translate gauge `ω = translateSpan s α b` whose coordinate `M = Φω` is odd
and positive on `(0, c)`, there exists a smooth even profile `u` supported in `(−c, c)` on which
`J_M(u) + 2 τ_s^S ∫ u² M sinh(x/2) < 0`. -/
theorem exists_odd_thetaGauge_outsideCharge_neg_below_log_four {c : ℝ} (hc : 273 / 400 < c)
    {ι : Type*} (s : Finset ι) (α b : ι → ℝ)
    (hModd : ∀ x, riemannKernelReal (-x) * translateSpan s α b (-x) =
      -(riemannKernelReal x * translateSpan s α b x))
    (hωpos : ∀ x ∈ Ioo (0 : ℝ) c, 0 < translateSpan s α b x) :
    ∃ u : ℝ → ℝ, ContDiff ℝ 2 u ∧ HasCompactSupport u ∧ (∀ x, u (-x) = u x) ∧
      (∀ x, x ∉ Ioo (-c) c → u x = 0) ∧
      signedJumpEnergy (fun y => riemannKernelReal y * translateSpan s α b y) u +
        2 * (translateSinhCoefficient s α b / 2 - sinhCharge (translateSpan s α b) (Ioo (-c) c)) *
          (∫ x, u x ^ 2 * (riemannKernelReal x * translateSpan s α b x * Real.sinh (x / 2))) < 0 := by
  obtain ⟨F₁, F₂, hF₁, hF₁c, hF₁odd, hF₁supp, hF₂, hF₂c, hF₂odd, hF₂supp, hdual⟩ :=
    exists_two_odd_tests_halfNormDual_neg_below_log_four hc
  exact not_exists_odd_thetaGauge_certificate_of_two_odd_tests (by norm_num) hc
    hF₁ hF₁c hF₁odd hF₁supp hF₂ hF₂c hF₂odd hF₂supp hdual s α b hModd hωpos

/-- **Negated-universal form of the odd theta-gauge refutation below `log 4`.** -/
theorem not_exists_odd_thetaGauge_certificate_below_log_four {c : ℝ} (hc : 273 / 400 < c)
    {ι : Type*} (s : Finset ι) (α b : ι → ℝ) :
    ¬ ((∀ x, riemannKernelReal (-x) * translateSpan s α b (-x) =
          -(riemannKernelReal x * translateSpan s α b x)) ∧
        (∀ x ∈ Ioo (0 : ℝ) c, 0 < translateSpan s α b x) ∧
        (∀ u : ℝ → ℝ, ContDiff ℝ 2 u → HasCompactSupport u → (∀ x, u (-x) = u x) →
          (∀ x, x ∉ Ioo (-c) c → u x = 0) →
          0 ≤ signedJumpEnergy (fun y => riemannKernelReal y * translateSpan s α b y) u +
            2 * (translateSinhCoefficient s α b / 2 - sinhCharge (translateSpan s α b) (Ioo (-c) c)) *
              (∫ x, u x ^ 2 *
                (riemannKernelReal x * translateSpan s α b x * Real.sinh (x / 2))))) := by
  rintro ⟨hModd, hωpos, hall⟩
  obtain ⟨u, hu, huc, hue, huoff, hneg⟩ :=
    exists_odd_thetaGauge_outsideCharge_neg_below_log_four hc s α b hModd hωpos
  linarith [hall u hu huc hue huoff]

/-- **Unconditional refutation of every shifted ground state window lower bound `ω_a` (`a > 0`)
below `log 4`.** For every `a > 0` and every `c > 273/400` (in particular every
`c ∈ (273/400, log 2)`, i.e., `2c ∈ (273/200, log 4)`), there exists a smooth even profile `u`
supported inside `(−c, c)` on which `2 S_a(u) − D_a(u) + 8 τ_c(a) ∫_{x>0} u² m_a sinh(x/2) < 0`. -/
theorem exists_shiftedGroundState_windowLower_neg_below_log_four {a c : ℝ}
    (ha : 0 < a) (hc : 273 / 400 < c) :
    ∃ u : ℝ → ℝ, ContDiff ℝ 2 u ∧ HasCompactSupport u ∧
      (∀ x, u (-x) = u x) ∧ (∀ x, x ∉ Ioo (-c) c → u x = 0) ∧
      2 * sameSideEnergy (shiftedGroundState a) u -
        reflectedDifferenceEnergy (shiftedGroundState a) u +
        8 * outsideCharge a c *
          (∫ x in Ioi (0 : ℝ), u x ^ 2 * shiftDifference a x * Real.sinh (x / 2)) < 0 := by
  obtain ⟨F₁, F₂, hF₁, hF₁c, hF₁odd, hF₁supp, hF₂, hF₂c, hF₂odd, hF₂supp, hdual⟩ :=
    exists_two_odd_tests_halfNormDual_neg_below_log_four hc
  exact exists_shiftedGroundState_windowLower_neg_of_two_odd_tests (by norm_num) hc
    hF₁ hF₁c hF₁odd hF₁supp hF₂ hF₂c hF₂odd hF₂supp hdual ha

end GaloisForLFunctions.SignedWindowCriticality.BelowLogFour

