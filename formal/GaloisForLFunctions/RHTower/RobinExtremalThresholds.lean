import GaloisForLFunctions.RHTower.RobinExtremalNumbers
import GaloisForLFunctions.RHTower.RobinLcmCriterion

/-!
# Exponent thresholds of the Robin extremal numbers

With the parameter `ε(x) = log(1 + 1/x)/log x` the extremal exponents satisfy:
* `a_p ≥ 1` exactly for the primes `p ≤ x`;
* `a_p ≥ 2` for `p ≤ (5/4)√x` and `a_p ≤ 1` for `p > (3/2)√x`, for large `x`;
* `p^{a_p + 1} > Q_p ≥ x/4` for `p ≤ x`.

Also `(Σ_{c√x < p ≤ x} p^{-2}) √x log x ≥ 2/c - δ` eventually, for `c ≥ 1` (prime number theorem).
-/

open MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-- The parameter `ε(x) = log(1 + 1/x)/log x`. -/
def robinParameter (x : ℝ) : ℝ := Real.log (1 + 1 / x) / Real.log x

theorem robinParameter_pos {x : ℝ} (hx : 1 < x) : 0 < robinParameter x := by
  have hx0 : 0 < x := by linarith
  have h1 : 0 < 1 / x := by positivity
  unfold robinParameter
  exact div_pos (Real.log_pos (by linarith)) (Real.log_pos hx)

theorem robinParameter_le {x : ℝ} (hx : 1 < x) : robinParameter x ≤ 1 / (x * Real.log x) := by
  have hx0 : 0 < x := by linarith
  have hl := Real.log_pos hx
  have h1 : Real.log (1 + 1 / x) ≤ 1 / x := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + 1 / x by positivity)
    linarith
  unfold robinParameter
  rw [div_le_iff₀ hl]
  calc Real.log (1 + 1 / x) ≤ 1 / x := h1
    _ = 1 / (x * Real.log x) * Real.log x := by field_simp

theorem le_robinParameter {x : ℝ} (hx : 1 < x) : 1 / ((x + 1) * Real.log x) ≤ robinParameter x := by
  have hx0 : 0 < x := by linarith
  have hl := Real.log_pos hx
  have h1 : 1 / (x + 1) ≤ Real.log (1 + 1 / x) := by
    have := Real.one_sub_inv_le_log_of_pos (show 0 < 1 + 1 / x by positivity)
    have e : 1 - (1 + 1 / x)⁻¹ = 1 / (x + 1) := by field_simp; ring
    linarith
  unfold robinParameter
  rw [le_div_iff₀ hl]
  calc 1 / ((x + 1) * Real.log x) * Real.log x = 1 / (x + 1) := by field_simp
    _ ≤ _ := h1

/-- `log(1 + 1/t)/log t` is strictly antitone on `(1, ∞)`. -/
theorem log_one_add_inv_div_log_lt {s t : ℝ} (hs : 1 < s) (hst : s < t) :
    Real.log (1 + 1 / t) / Real.log t < Real.log (1 + 1 / s) / Real.log s := by
  have hs0 : 0 < s := by linarith
  have ht0 : 0 < t := by linarith
  have hls := Real.log_pos hs
  have hlt : Real.log s < Real.log t := Real.log_lt_log hs0 hst
  have h1 : Real.log (1 + 1 / t) < Real.log (1 + 1 / s) := by
    refine Real.log_lt_log (by positivity) ?_
    have : 1 / t < 1 / s := one_div_lt_one_div_of_lt hs0 hst
    linarith
  have ht1 : 0 < 1 / t := by positivity
  have h0 : 0 < Real.log (1 + 1 / t) := Real.log_pos (by linarith)
  rw [div_lt_div_iff₀ (by linarith) hls]
  nlinarith

/-- `1 ≤ a_p ⟺ p^ε ≤ 1 + 1/p`. -/
theorem one_le_robinExponent_iff {ε : ℝ} (hε : 0 < ε) {p : ℕ} (hp : p.Prime) :
    1 ≤ robinExponent ε p ↔ (p : ℝ) ^ ε ≤ 1 + 1 / p := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hd : 0 < (p : ℝ) ^ ε - 1 := by have := Real.one_lt_rpow hp1 hε; linarith
  have e : 1 - 1 / (p : ℝ) = ((p : ℝ) - 1) * (1 / p) := by field_simp
  rw [le_robinExponent_iff hε hp, pow_one, robinThreshold]
  have h1 : (p : ℝ) ≤ 1 + (1 - 1 / (p : ℝ)) / ((p : ℝ) ^ ε - 1)
      ↔ ((p : ℝ) - 1) * ((p : ℝ) ^ ε - 1) ≤ ((p : ℝ) - 1) * (1 / p) := by
    rw [e]
    constructor
    · intro h
      exact (le_div_iff₀ hd).mp (by linarith)
    · intro h
      have := (le_div_iff₀ hd).mpr h
      linarith
  rw [h1, mul_le_mul_iff_of_pos_left (by linarith)]
  constructor <;> intro h <;> linarith

/-- At `ε(x)`, `1 ≤ a_p ⟺ p ≤ x`. -/
theorem one_le_robinExponent_iff_le {x : ℝ} (hx : 1 < x) {p : ℕ} (hp : p.Prime) :
    1 ≤ robinExponent (robinParameter x) p ↔ (p : ℝ) ≤ x := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hlp := Real.log_pos hp1
  rw [one_le_robinExponent_iff (robinParameter_pos hx) hp, ← Real.log_le_log_iff
    (Real.rpow_pos_of_pos hp0 _) (by positivity), Real.log_rpow hp0, robinParameter]
  rw [div_mul_eq_mul_div, div_le_iff₀ (Real.log_pos hx)]
  constructor
  · intro h
    by_contra hc
    push Not at hc
    have := log_one_add_inv_div_log_lt hx hc
    rw [div_lt_div_iff₀ hlp (Real.log_pos hx)] at this
    linarith
  · intro h
    rcases eq_or_lt_of_le h with he | hlt
    · rw [he]
    · have := log_one_add_inv_div_log_lt hp1 hlt
      rw [div_lt_div_iff₀ (Real.log_pos hx) hlp] at this
      linarith

/-- Beyond `x` the extremal exponent vanishes. -/
theorem robinExponent_eq_zero_of_lt {x : ℝ} (hx : 1 < x) {p : ℕ} (hp : p.Prime)
    (hpx : x < p) : robinExponent (robinParameter x) p = 0 := by
  have := (one_le_robinExponent_iff_le hx hp).not.mpr (not_le.mpr hpx)
  omega

/-- `e^u - 1 ≤ u + 2u²` for `0 < u ≤ 1/2`. -/
theorem exp_sub_one_le_add_two_sq {u : ℝ} (hu : 0 < u) (hu2 : u ≤ 1 / 2) :
    Real.exp u - 1 ≤ u + 2 * u ^ 2 := by
  have h := Real.exp_bound_div_one_sub_of_interval' hu (by linarith)
  have h2 : 1 / (1 - u) ≤ 1 + u + 2 * u ^ 2 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  linarith

/-- `p^ε - 1 = e^{ε log p} - 1 ∈ [u, u + 2u²]`, `u = ε log p`. -/
theorem rpow_sub_one_mem {ε : ℝ} (hε : 0 < ε) {p : ℕ} (hp : p.Prime)
    (hu : ε * Real.log p ≤ 1 / 2) :
    ε * Real.log p ≤ (p : ℝ) ^ ε - 1
      ∧ (p : ℝ) ^ ε - 1 ≤ ε * Real.log p + 2 * (ε * Real.log p) ^ 2 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hlp := Real.log_pos hp1
  have hu0 : 0 < ε * Real.log p := mul_pos hε hlp
  rw [Real.rpow_def_of_pos hp0, mul_comm (Real.log p) ε]
  constructor
  · have := Real.add_one_le_exp (ε * Real.log p); linarith
  · exact exp_sub_one_le_add_two_sq hu0 hu

/-- `p² ≤ Q_p(ε)` follows from `(p + 1) p (p^ε - 1) ≤ 1`. -/
theorem two_le_robinExponent_of_mul_le {ε : ℝ} (hε : 0 < ε) {p : ℕ} (hp : p.Prime)
    (hkey : ((p : ℝ) + 1) * p * ((p : ℝ) ^ ε - 1) ≤ 1) : 2 ≤ robinExponent ε p := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  rw [le_robinExponent_iff hε hp, robinThreshold]
  have hq : 1 - 1 / (p : ℝ) = ((p : ℝ) - 1) * (1 / p) := by field_simp
  have hpe : 0 < (p : ℝ) ^ ε - 1 := by have := Real.one_lt_rpow hp1 hε; linarith
  rw [← sub_le_iff_le_add', le_div_iff₀ hpe, hq]
  have e : ((p : ℝ) ^ 2 - 1) * ((p : ℝ) ^ ε - 1)
      = ((p : ℝ) - 1) * (1 / p) * (((p : ℝ) + 1) * p * ((p : ℝ) ^ ε - 1)) := by
    field_simp
    ring
  rw [e]
  have : 0 ≤ ((p : ℝ) - 1) * (1 / p) := by
    have : 0 ≤ (p : ℝ) - 1 := by linarith
    positivity
  calc ((p : ℝ) - 1) * (1 / p) * (((p : ℝ) + 1) * p * ((p : ℝ) ^ ε - 1))
      ≤ ((p : ℝ) - 1) * (1 / p) * 1 := mul_le_mul_of_nonneg_left hkey this
    _ = ((p : ℝ) - 1) * (1 / p) := mul_one _

/-- **Squares below `c√x`, `c < √2`.**  For `1 ≤ c` with `c² < 2`, eventually every prime
`p ≤ c√x` has `a_p(ε(x)) ≥ 2`. -/
theorem eventually_two_le_robinExponent_mul {c : ℝ} (hc1 : 1 ≤ c) (hc : c ^ 2 < 2) :
    ∀ᶠ x : ℝ in atTop, ∀ p : ℕ, p.Prime → (p : ℝ) ≤ c * Real.sqrt x →
      2 ≤ robinExponent (robinParameter x) p := by
  have hc0 : 0 < c := by linarith
  have hlc : 0 ≤ Real.log c := Real.log_nonneg hc1
  -- the limiting factor `c²/2 < 1`
  have hF : Tendsto (fun x : ℝ => (c ^ 2 + c / Real.sqrt x)
      * (1 / 2 + Real.log c / Real.log x) * (1 + 2 / x)) atTop (𝓝 (c ^ 2 * (1 / 2) * 1)) := by
    have h1 : Tendsto (fun x : ℝ => c ^ 2 + c / Real.sqrt x) atTop (𝓝 (c ^ 2 + 0)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop)
    have h2 : Tendsto (fun x : ℝ => 1 / 2 + Real.log c / Real.log x) atTop (𝓝 (1 / 2 + 0)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.div_atTop Real.tendsto_log_atTop)
    have h3 : Tendsto (fun x : ℝ => 1 + 2 / x) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_id)
    rw [add_zero] at h1 h2 h3
    exact (h1.mul h2).mul h3
  filter_upwards [hF.eventually (gt_mem_nhds (show c ^ 2 * (1 / 2) * 1 < 1 by nlinarith)),
    eventually_ge_atTop (4 : ℝ), Real.tendsto_sqrt_atTop.eventually (eventually_ge_atTop c)]
    with x hFx hx hsxc p hp hpx
  have hx1 : 1 < x := by linarith
  have hx0 : 0 < x := by linarith
  have hlx : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]; have := Real.exp_one_lt_d9; linarith
  have hε := robinParameter_pos hx1
  have hεle := robinParameter_le hx1
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hlp := Real.log_pos hp1
  have hxx : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
  have hsx0 : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hlogp : Real.log p ≤ Real.log x / 2 + Real.log c := by
    have h1 : Real.log p ≤ Real.log (c * Real.sqrt x) := Real.log_le_log hp0 hpx
    rw [Real.log_mul hc0.ne' hsx0.ne', Real.log_sqrt hx0.le] at h1
    linarith
  have hpx' : (p : ℝ) ≤ x := by
    calc (p : ℝ) ≤ c * Real.sqrt x := hpx
      _ ≤ Real.sqrt x * Real.sqrt x := mul_le_mul_of_nonneg_right hsxc hsx0.le
      _ = x := hxx
  have hlogp' : Real.log p ≤ Real.log x := Real.log_le_log hp0 hpx'
  set ε := robinParameter x with hεdef
  set u := ε * Real.log p with hu
  have hu0 : 0 < u := mul_pos hε hlp
  have hule : u ≤ Real.log p / (x * Real.log x) := by
    rw [hu]
    calc ε * Real.log p ≤ 1 / (x * Real.log x) * Real.log p :=
          mul_le_mul_of_nonneg_right hεle hlp.le
      _ = Real.log p / (x * Real.log x) := by ring
  have hux : u ≤ 1 / x := by
    refine hule.trans ?_
    rw [div_le_div_iff₀ (by positivity) hx0]
    have := mul_le_mul_of_nonneg_right hlogp' hx0.le
    linarith
  have hu2 : u ≤ 1 / 2 := hux.trans (by rw [div_le_iff₀ hx0]; linarith)
  obtain ⟨_, hup⟩ := rpow_sub_one_mem hε hp hu2
  refine two_le_robinExponent_of_mul_le hε hp ?_
  have h1 : (p : ℝ) ^ ε - 1 ≤ u * (1 + 2 / x) := by
    have : 2 * u ^ 2 ≤ u * (2 / x) := by
      have := mul_le_mul_of_nonneg_left hux hu0.le
      calc 2 * u ^ 2 = 2 * (u * u) := by ring
        _ ≤ 2 * (u * (1 / x)) := by linarith
        _ = u * (2 / x) := by ring
    linarith
  have h2 : ((p : ℝ) + 1) * p ≤ c ^ 2 * x + c * Real.sqrt x := by
    have h3 : (p : ℝ) * p ≤ (c * Real.sqrt x) * (c * Real.sqrt x) :=
      mul_le_mul hpx hpx hp0.le (by positivity)
    have e : (c * Real.sqrt x) * (c * Real.sqrt x) = c ^ 2 * x := by
      rw [show (c * Real.sqrt x) * (c * Real.sqrt x) = c ^ 2 * (Real.sqrt x * Real.sqrt x) by
        ring, hxx]
    nlinarith
  have hpos : 0 ≤ (p : ℝ) ^ ε - 1 := by
    have := Real.one_lt_rpow hp1 hε; linarith
  have e : (c ^ 2 * x + c * Real.sqrt x)
      * ((Real.log x / 2 + Real.log c) / (x * Real.log x) * (1 + 2 / x))
      = (c ^ 2 + c / Real.sqrt x) * (1 / 2 + Real.log c / Real.log x) * (1 + 2 / x) := by
    have hl0 : Real.log x ≠ 0 := by linarith
    have e1 : (c ^ 2 * x + c * Real.sqrt x) / x = c ^ 2 + c / Real.sqrt x := by
      have e2 : c * Real.sqrt x / x = c / Real.sqrt x := by
        rw [div_eq_div_iff hx0.ne' hsx0.ne', mul_assoc, hxx]
      rw [add_div, e2]; field_simp
    have e3 : (Real.log x / 2 + Real.log c) / Real.log x = 1 / 2 + Real.log c / Real.log x := by
      field_simp
    rw [← e1, ← e3]
    field_simp
  calc ((p : ℝ) + 1) * p * ((p : ℝ) ^ ε - 1)
      ≤ (c ^ 2 * x + c * Real.sqrt x) * (u * (1 + 2 / x)) :=
        mul_le_mul h2 h1 hpos (by positivity)
    _ ≤ (c ^ 2 * x + c * Real.sqrt x)
          * ((Real.log x / 2 + Real.log c) / (x * Real.log x) * (1 + 2 / x)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ (by positivity))
          (by positivity)
        exact hule.trans (div_le_div_of_nonneg_right hlogp (by positivity))
    _ = _ := e
    _ ≤ 1 := hFx.le

/-- **Squares below `(5/4)√x`.**  Eventually, every prime `p ≤ (5/4)√x` has `a_p(ε(x)) ≥ 2`. -/
theorem eventually_two_le_robinExponent :
    ∀ᶠ x : ℝ in atTop, ∀ p : ℕ, p.Prime → (p : ℝ) ≤ 5 / 4 * Real.sqrt x →
      2 ≤ robinExponent (robinParameter x) p :=
  eventually_two_le_robinExponent_mul (by norm_num) (by norm_num)

/-- **No squares beyond `c√x`, `c > √2`.**  If `1 ≤ c` and `2x + 3 < c²x`, every prime
`p > c√x` has `a_p(ε(x)) ≤ 1`. -/
theorem robinExponent_le_one_of_gt_mul {x c : ℝ} (hc : 1 ≤ c) (hx : 1 < x)
    (hcx : 2 * x + 3 < c ^ 2 * x) {p : ℕ} (hp : p.Prime) (hpx : c * Real.sqrt x < p) :
    robinExponent (robinParameter x) p ≤ 1 := by
  have hx0 : 0 < x := by linarith
  have hc0 : 0 < c := by linarith
  have hε := robinParameter_pos hx
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hlx := Real.log_pos hx
  have hsx0 : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hlogp : Real.log x / 2 ≤ Real.log p := by
    have h1 : Real.log (c * Real.sqrt x) ≤ Real.log p :=
      Real.log_le_log (by positivity) hpx.le
    rw [Real.log_mul hc0.ne' hsx0.ne', Real.log_sqrt hx0.le] at h1
    have : 0 ≤ Real.log c := Real.log_nonneg hc
    linarith
  set ε := robinParameter x with hεdef
  have hd : 1 / (2 * (x + 1)) ≤ (p : ℝ) ^ ε - 1 := by
    have h1 : ε * Real.log p ≤ (p : ℝ) ^ ε - 1 := by
      rw [Real.rpow_def_of_pos hp0, mul_comm (Real.log p) ε]
      have := Real.add_one_le_exp (ε * Real.log p); linarith
    have h2 : 1 / ((x + 1) * Real.log x) * (Real.log x / 2) ≤ ε * Real.log p :=
      mul_le_mul (le_robinParameter hx) hlogp (by positivity) hε.le
    have e : 1 / ((x + 1) * Real.log x) * (Real.log x / 2) = 1 / (2 * (x + 1)) := by
      field_simp
    linarith
  have hd0 : 0 < (p : ℝ) ^ ε - 1 := lt_of_lt_of_le (by positivity) hd
  have hQ : robinThreshold ε p ≤ 2 * x + 3 := by
    unfold robinThreshold
    have h1 : (1 - 1 / (p : ℝ)) / ((p : ℝ) ^ ε - 1) ≤ 1 / ((p : ℝ) ^ ε - 1) := by
      refine div_le_div_of_nonneg_right ?_ hd0.le
      have : 0 ≤ 1 / (p : ℝ) := by positivity
      linarith
    have h2 : 1 / ((p : ℝ) ^ ε - 1) ≤ 2 * (x + 1) := by
      rw [div_le_iff₀ hd0]
      have h3 := mul_le_mul_of_nonneg_left hd (show (0 : ℝ) ≤ 2 * (x + 1) by positivity)
      have e : 2 * (x + 1) * (1 / (2 * (x + 1))) = 1 := by field_simp
      linarith
    linarith
  have hpsq : c ^ 2 * x < (p : ℝ) ^ 2 := by
    have h := mul_lt_mul'' hpx hpx (by positivity) (by positivity)
    have e : c * Real.sqrt x * (c * Real.sqrt x) = c ^ 2 * x := by
      rw [show c * Real.sqrt x * (c * Real.sqrt x) = c ^ 2 * (Real.sqrt x * Real.sqrt x) by ring,
        Real.mul_self_sqrt hx0.le]
    nlinarith
  by_contra hcon
  push Not at hcon
  have h2 := (le_robinExponent_iff hε hp 2).mp (by omega)
  linarith

/-- **No squares beyond `(3/2)√x`.**  For `x > 12`, every prime `p > (3/2)√x` has
`a_p(ε(x)) ≤ 1`. -/
theorem robinExponent_le_one_of_gt {x : ℝ} (hx : 12 < x) {p : ℕ} (hp : p.Prime)
    (hpx : 3 / 2 * Real.sqrt x < p) : robinExponent (robinParameter x) p ≤ 1 :=
  robinExponent_le_one_of_gt_mul (by norm_num) (by linarith) (by nlinarith) hp hpx

/-- **The cut-off threshold.**  For `x ≥ 16` and a prime `p ≤ x`, `Q_p(ε(x)) ≥ x/4`. -/
theorem robinThreshold_ge {x : ℝ} (hx : 16 ≤ x) {p : ℕ} (hp : p.Prime) (hpx : (p : ℝ) ≤ x) :
    x / 4 ≤ robinThreshold (robinParameter x) p := by
  have hx1 : 1 < x := by linarith
  have hx0 : 0 < x := by linarith
  have hε := robinParameter_pos hx1
  have hεle := robinParameter_le hx1
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hlp := Real.log_pos hp1
  have hlx := Real.log_pos hx1
  set ε := robinParameter x with hεdef
  have hlpx : Real.log p ≤ Real.log x := Real.log_le_log hp0 hpx
  have hux : ε * Real.log p ≤ 1 / x := by
    calc ε * Real.log p ≤ 1 / (x * Real.log x) * Real.log x :=
          mul_le_mul hεle hlpx hlp.le (by positivity)
      _ = 1 / x := by field_simp
  have hu2 : ε * Real.log p ≤ 1 / 2 := hux.trans (by rw [div_le_iff₀ hx0]; linarith)
  obtain ⟨hlow, hup⟩ := rpow_sub_one_mem hε hp hu2
  have hu0 : 0 < ε * Real.log p := mul_pos hε hlp
  have hd0 : 0 < (p : ℝ) ^ ε - 1 := lt_of_lt_of_le hu0 hlow
  have hd : (p : ℝ) ^ ε - 1 ≤ 2 / x := by
    have h1 : 2 * (ε * Real.log p) ^ 2 ≤ ε * Real.log p := by
      have h3 := mul_le_mul_of_nonneg_left hu2 hu0.le
      calc 2 * (ε * Real.log p) ^ 2 = 2 * ((ε * Real.log p) * (ε * Real.log p)) := by ring
        _ ≤ 2 * ((ε * Real.log p) * (1 / 2)) := by linarith
        _ = ε * Real.log p := by ring
    calc (p : ℝ) ^ ε - 1 ≤ ε * Real.log p + 2 * (ε * Real.log p) ^ 2 := hup
      _ ≤ 2 * (ε * Real.log p) := by linarith
      _ ≤ 2 * (1 / x) := by linarith
      _ = 2 / x := by ring
  have hq : 1 / 2 ≤ 1 - 1 / (p : ℝ) := by
    have : 1 / (p : ℝ) ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hp.two_le)
    linarith
  unfold robinThreshold
  have h1 : x / 4 ≤ (1 - 1 / (p : ℝ)) / ((p : ℝ) ^ ε - 1) := by
    rw [le_div_iff₀ hd0]
    calc x / 4 * ((p : ℝ) ^ ε - 1) ≤ x / 4 * (2 / x) :=
          mul_le_mul_of_nonneg_left hd (by positivity)
      _ = 1 / 2 := by field_simp; norm_num
      _ ≤ _ := hq
  linarith

/-- `p^{a_p + 1} > Q_p`. -/
theorem robinThreshold_lt_pow {ε : ℝ} (hε : 0 < ε) {p : ℕ} (hp : p.Prime) :
    robinThreshold ε p < (p : ℝ) ^ (robinExponent ε p + 1) := by
  by_contra hc
  push Not at hc
  have := (le_robinExponent_iff hε hp _).mpr hc
  omega

/-! ## Prime squares beyond `c√x` -/

theorem tendsto_log_div_affine_log {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    Tendsto (fun x : ℝ => Real.log x / (a + b * Real.log x)) atTop (𝓝 (1 / b)) := by
  have h1 : Tendsto (fun x : ℝ => a / Real.log x + b) atTop (𝓝 (0 + b)) :=
    (tendsto_const_nhds.div_atTop Real.tendsto_log_atTop).add tendsto_const_nhds
  rw [zero_add] at h1
  have h2 := h1.inv₀ hb.ne'
  rw [← one_div] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hl := Real.log_pos hx
  have : 0 < a + b * Real.log x := by positivity
  field_simp

/-- **Prime squares beyond `c√x`, from below.**  For `c ≥ 1` and `δ > 0`, eventually
`(Σ_{c√x < p ≤ x} 1/p²) √x log x ≥ 2/c - δ`. -/
theorem eventually_sum_prime_inv_sq_scaled_ge {c δ : ℝ} (hc : 1 ≤ c) (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, 2 / c - δ ≤
      (∑ p ∈ ((Finset.Icc 0 ⌊x⌋₊).filter Nat.Prime).filter (fun p : ℕ => c * Real.sqrt x < p),
        1 / (p : ℝ) ^ 2) * (Real.sqrt x * Real.log x) := by
  have hc0 : 0 < c := by linarith
  have hlc : 0 ≤ Real.log c := Real.log_nonneg hc
  set η := c * δ / 16 with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨t₀, ht₀⟩ := eventually_atTop.mp ((tendsto_iff_norm_sub_tendsto_zero.mp
    tendsto_theta_div_self).eventually (gt_mem_nhds hη0))
  have hB := tendsto_log_div_affine_log (a := c * Real.log c) (b := c / 2) (by positivity)
    (by positivity)
  have hlogy : Tendsto (fun x : ℝ => 1 / (Real.log c + Real.log x / 2)) atTop (𝓝 0) := by
    refine tendsto_const_nhds.div_atTop ?_
    exact tendsto_atTop_add_const_left _ _ (Real.tendsto_log_atTop.atTop_div_const (by norm_num))
  have hsq : Tendsto (fun x : ℝ => (1 + η) / Real.sqrt x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop
  have h1c : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hLB := (hB.mul ((h1c.sub hlogy).sub_const (4 * η))).sub hsq
  have hlim : 1 / (c / 2) * (1 - 0 - 4 * η) - 0 = 2 / c - δ / 2 := by
    rw [hη]; field_simp; ring
  rw [hlim] at hLB
  filter_upwards [hLB.eventually (lt_mem_nhds (show 2 / c - δ < 2 / c - δ / 2 by linarith)),
    Real.tendsto_sqrt_atTop.eventually (eventually_ge_atTop (max (max 16 (t₀ / c)) c))]
    with x hLx hsx
  have hsx16 : 16 ≤ Real.sqrt x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hsx
  have hsxc : c ≤ Real.sqrt x := le_trans (le_max_right _ _) hsx
  have hsx0 : 0 < Real.sqrt x := by linarith
  have hx0 : 0 < x := Real.sqrt_pos.mp hsx0
  have hxx : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
  set y := c * Real.sqrt x with hy
  have hy16 : 16 ≤ y := by
    calc (16 : ℝ) ≤ Real.sqrt x := hsx16
      _ ≤ c * Real.sqrt x := le_mul_of_one_le_left hsx0.le hc
  have hyt : t₀ ≤ y := by
    have : t₀ / c ≤ Real.sqrt x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hsx
    rw [div_le_iff₀ hc0] at this; rw [hy]; linarith
  have hyx : y ≤ x := by
    calc y = c * Real.sqrt x := hy
      _ ≤ Real.sqrt x * Real.sqrt x := mul_le_mul_of_nonneg_right hsxc hsx0.le
      _ = x := hxx
  have hS : ∀ t : ℝ, y ≤ t → t ≤ x → |Chebyshev.theta t - t| ≤ η * t := by
    intro t ht _
    have ht0 : 0 < t := by linarith
    have h := ht₀ t (le_trans hyt ht)
    rw [Real.norm_eq_abs, show Chebyshev.theta t / t - 1 = (Chebyshev.theta t - t) / t by
      field_simp, abs_div, abs_of_pos ht0, div_lt_iff₀ ht0] at h
    linarith
  have hb := abs_sum_prime_inv_sq_sub_le_of_relative hη0.le hS hy16 hyx
  rw [← sum_filter_prime_inv_sq_eq (by linarith : (0 : ℝ) ≤ y)] at hb
  set S := ∑ p ∈ ((Finset.Icc 0 ⌊x⌋₊).filter Nat.Prime).filter (fun p : ℕ => y < p),
    1 / (p : ℝ) ^ 2 with hSdef
  have hlx : 0 < Real.log x := Real.log_pos (by nlinarith)
  have hlogy' : Real.log y = Real.log c + Real.log x / 2 := by
    rw [hy, Real.log_mul hc0.ne' hsx0.ne', Real.log_sqrt hx0.le]
  have hly : 0 < Real.log y := by rw [hlogy']; positivity
  have hD : 0 < Real.sqrt x * Real.log x := mul_pos hsx0 hlx
  have hlow : 1 / (y * Real.log y) - (1 / (x * Real.log x) + 1 / (y * Real.log y ^ 2)
      + η * (1 / (x * Real.log x) + 4 / (y * Real.log y))) ≤ S := by
    have := (abs_le.mp hb).1; linarith
  have e1 : 1 / (x * Real.log x) * (Real.sqrt x * Real.log x) = 1 / Real.sqrt x := by
    calc 1 / (x * Real.log x) * (Real.sqrt x * Real.log x)
        = Real.sqrt x / (Real.sqrt x * Real.sqrt x) := by rw [hxx]; field_simp
      _ = 1 / Real.sqrt x := by field_simp
  have e2 : 1 / (y * Real.log y) * (Real.sqrt x * Real.log x)
      = Real.log x / (c * Real.log y) := by rw [hy]; field_simp
  have e3 : 1 / (y * Real.log y ^ 2) * (Real.sqrt x * Real.log x)
      = Real.log x / (c * Real.log y) * (1 / Real.log y) := by rw [hy]; field_simp
  have e4 : 4 / (y * Real.log y) * (Real.sqrt x * Real.log x)
      = 4 * (Real.log x / (c * Real.log y)) := by rw [hy]; field_simp
  have hcl : c * Real.log c + c / 2 * Real.log x = c * Real.log y := by rw [hlogy']; ring
  have hval : (1 / (y * Real.log y) - (1 / (x * Real.log x) + 1 / (y * Real.log y ^ 2)
      + η * (1 / (x * Real.log x) + 4 / (y * Real.log y)))) * (Real.sqrt x * Real.log x)
      = Real.log x / (c * Real.log c + c / 2 * Real.log x)
          * (1 - 1 / (Real.log c + Real.log x / 2) - 4 * η) - (1 + η) / Real.sqrt x := by
    have hsplit : (1 / (y * Real.log y) - (1 / (x * Real.log x) + 1 / (y * Real.log y ^ 2)
        + η * (1 / (x * Real.log x) + 4 / (y * Real.log y)))) * (Real.sqrt x * Real.log x)
        = 1 / (y * Real.log y) * (Real.sqrt x * Real.log x)
          - 1 / (x * Real.log x) * (Real.sqrt x * Real.log x)
          - 1 / (y * Real.log y ^ 2) * (Real.sqrt x * Real.log x)
          - η * (1 / (x * Real.log x) * (Real.sqrt x * Real.log x)
            + 4 / (y * Real.log y) * (Real.sqrt x * Real.log x)) := by ring
    rw [hsplit, e1, e2, e3, e4, hcl, ← hlogy']
    ring
  calc 2 / c - δ ≤ Real.log x / (c * Real.log c + c / 2 * Real.log x)
          * (1 - 1 / (Real.log c + Real.log x / 2) - 4 * η) - (1 + η) / Real.sqrt x := hLx.le
    _ = _ := hval.symm
    _ ≤ S * (Real.sqrt x * Real.log x) := mul_le_mul_of_nonneg_right hlow hD.le


/-- **Prime squares beyond `c√x`, from above.**  For `c ≥ 1` and `δ > 0`, eventually
`(Σ_{c√x < p ≤ x} 1/p²) √x log x ≤ 2/c + δ`. -/
theorem eventually_sum_prime_inv_sq_scaled_le {c δ : ℝ} (hc : 1 ≤ c) (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop,
      (∑ p ∈ ((Finset.Icc 0 ⌊x⌋₊).filter Nat.Prime).filter (fun p : ℕ => c * Real.sqrt x < p),
        1 / (p : ℝ) ^ 2) * (Real.sqrt x * Real.log x) ≤ 2 / c + δ := by
  have hc0 : 0 < c := by linarith
  have hlc : 0 ≤ Real.log c := Real.log_nonneg hc
  set η := c * δ / 16 with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨t₀, ht₀⟩ := eventually_atTop.mp ((tendsto_iff_norm_sub_tendsto_zero.mp
    tendsto_theta_div_self).eventually (gt_mem_nhds hη0))
  have hB := tendsto_log_div_affine_log (a := c * Real.log c) (b := c / 2) (by positivity)
    (by positivity)
  have hlogy : Tendsto (fun x : ℝ => 1 / (Real.log c + Real.log x / 2)) atTop (𝓝 0) := by
    refine tendsto_const_nhds.div_atTop ?_
    exact tendsto_atTop_add_const_left _ _ (Real.tendsto_log_atTop.atTop_div_const (by norm_num))
  have hsq : Tendsto (fun x : ℝ => (1 + η) / Real.sqrt x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop
  have h1c : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hLB := (hB.mul ((h1c.add hlogy).add_const (4 * η))).add hsq
  have hlim : 1 / (c / 2) * (1 + 0 + 4 * η) + 0 = 2 / c + δ / 2 := by
    rw [hη]; field_simp; ring
  rw [hlim] at hLB
  filter_upwards [hLB.eventually (gt_mem_nhds (show 2 / c + δ / 2 < 2 / c + δ by linarith)),
    Real.tendsto_sqrt_atTop.eventually (eventually_ge_atTop (max (max 16 (t₀ / c)) c))]
    with x hLx hsx
  have hsx16 : 16 ≤ Real.sqrt x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hsx
  have hsxc : c ≤ Real.sqrt x := le_trans (le_max_right _ _) hsx
  have hsx0 : 0 < Real.sqrt x := by linarith
  have hx0 : 0 < x := Real.sqrt_pos.mp hsx0
  have hxx : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
  set y := c * Real.sqrt x with hy
  have hy16 : 16 ≤ y := by
    calc (16 : ℝ) ≤ Real.sqrt x := hsx16
      _ ≤ c * Real.sqrt x := le_mul_of_one_le_left hsx0.le hc
  have hyt : t₀ ≤ y := by
    have : t₀ / c ≤ Real.sqrt x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hsx
    rw [div_le_iff₀ hc0] at this; rw [hy]; linarith
  have hyx : y ≤ x := by
    calc y = c * Real.sqrt x := hy
      _ ≤ Real.sqrt x * Real.sqrt x := mul_le_mul_of_nonneg_right hsxc hsx0.le
      _ = x := hxx
  have hS : ∀ t : ℝ, y ≤ t → t ≤ x → |Chebyshev.theta t - t| ≤ η * t := by
    intro t ht _
    have ht0 : 0 < t := by linarith
    have h := ht₀ t (le_trans hyt ht)
    rw [Real.norm_eq_abs, show Chebyshev.theta t / t - 1 = (Chebyshev.theta t - t) / t by
      field_simp, abs_div, abs_of_pos ht0, div_lt_iff₀ ht0] at h
    linarith
  have hb := abs_sum_prime_inv_sq_sub_le_of_relative hη0.le hS hy16 hyx
  rw [← sum_filter_prime_inv_sq_eq (by linarith : (0 : ℝ) ≤ y)] at hb
  set S := ∑ p ∈ ((Finset.Icc 0 ⌊x⌋₊).filter Nat.Prime).filter (fun p : ℕ => y < p),
    1 / (p : ℝ) ^ 2 with hSdef
  have hlx : 0 < Real.log x := Real.log_pos (by nlinarith)
  have hlogy' : Real.log y = Real.log c + Real.log x / 2 := by
    rw [hy, Real.log_mul hc0.ne' hsx0.ne', Real.log_sqrt hx0.le]
  have hly : 0 < Real.log y := by rw [hlogy']; positivity
  have hD : 0 < Real.sqrt x * Real.log x := mul_pos hsx0 hlx
  have hlow : S ≤ 1 / (y * Real.log y) + (1 / (x * Real.log x) + 1 / (y * Real.log y ^ 2)
      + η * (1 / (x * Real.log x) + 4 / (y * Real.log y))) := by
    have := (abs_le.mp hb).2; linarith
  have e1 : 1 / (x * Real.log x) * (Real.sqrt x * Real.log x) = 1 / Real.sqrt x := by
    calc 1 / (x * Real.log x) * (Real.sqrt x * Real.log x)
        = Real.sqrt x / (Real.sqrt x * Real.sqrt x) := by rw [hxx]; field_simp
      _ = 1 / Real.sqrt x := by field_simp
  have e2 : 1 / (y * Real.log y) * (Real.sqrt x * Real.log x)
      = Real.log x / (c * Real.log y) := by rw [hy]; field_simp
  have e3 : 1 / (y * Real.log y ^ 2) * (Real.sqrt x * Real.log x)
      = Real.log x / (c * Real.log y) * (1 / Real.log y) := by rw [hy]; field_simp
  have e4 : 4 / (y * Real.log y) * (Real.sqrt x * Real.log x)
      = 4 * (Real.log x / (c * Real.log y)) := by rw [hy]; field_simp
  have hcl : c * Real.log c + c / 2 * Real.log x = c * Real.log y := by rw [hlogy']; ring
  have hval : (1 / (y * Real.log y) + (1 / (x * Real.log x) + 1 / (y * Real.log y ^ 2)
      + η * (1 / (x * Real.log x) + 4 / (y * Real.log y)))) * (Real.sqrt x * Real.log x)
      = Real.log x / (c * Real.log c + c / 2 * Real.log x)
          * (1 + 1 / (Real.log c + Real.log x / 2) + 4 * η) + (1 + η) / Real.sqrt x := by
    have hsplit : (1 / (y * Real.log y) + (1 / (x * Real.log x) + 1 / (y * Real.log y ^ 2)
        + η * (1 / (x * Real.log x) + 4 / (y * Real.log y)))) * (Real.sqrt x * Real.log x)
        = 1 / (y * Real.log y) * (Real.sqrt x * Real.log x)
          + 1 / (x * Real.log x) * (Real.sqrt x * Real.log x)
          + 1 / (y * Real.log y ^ 2) * (Real.sqrt x * Real.log x)
          + η * (1 / (x * Real.log x) * (Real.sqrt x * Real.log x)
            + 4 / (y * Real.log y) * (Real.sqrt x * Real.log x)) := by ring
    rw [hsplit, e1, e2, e3, e4, hcl, ← hlogy']
    ring
  calc S * (Real.sqrt x * Real.log x)
      ≤ (1 / (y * Real.log y) + (1 / (x * Real.log x) + 1 / (y * Real.log y ^ 2)
          + η * (1 / (x * Real.log x) + 4 / (y * Real.log y)))) * (Real.sqrt x * Real.log x) :=
        mul_le_mul_of_nonneg_right hlow hD.le
    _ = _ := hval
    _ ≤ 2 / c + δ := hLx.le

end

end RHTower
