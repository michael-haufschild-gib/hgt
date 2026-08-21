import GaloisForLFunctions.RHTower.DQPTPartitionRate

/-!
# DQPT: the free-energy density and the entropy density

**Methods equation (19)** of arXiv:2511.11199 and **published Supplementary Note 3** combine the
two asymptotics of Supplementary Notes 1 and 2 into the finite-size free energy

`F₁,N(β,t) = −(1/log₂N)·ln |L_N(β,t)|`,   `|L_N(β,t)| = |S_N(s)| / Z(β,H₀)`,   `s = β + it`,

and its limit

`F₁(β,t) = ln 2` at an eta zero, `(1−β) ln 2` for `0 < β < 1` off the zeros, `0` for `β > 1`.

The associated entropy density is `𝒮 = −F₁ + β ∂F₁/∂β`, equal to `−ln 2` on the strip off the
zeros and to `0` for `β > 1` (published equation (28)).

Main results:
* `dqpt_freeEnergy_at_eta_zero`, `dqpt_freeEnergy_strip`, `dqpt_freeEnergy_right` —
  **Methods (19)** / published **(26)**;
* `dqpt_entropy_strip`, `dqpt_entropy_right` — published **(28)**.
-/

namespace RHTower.DQPT

open Complex Filter Topology Set

noncomputable section

/-- `F₁,N(β,t) = −(1/log₂N)·ln(|S_N(s)|/Z(β,H₀))`, the finite-size free-energy density. -/
def dqptFreeEnergyFinite (s : ℂ) (N : ℕ) : ℝ :=
  -Real.log (‖dqptAltPartialSum s N‖ / dqptPartition s.re N) / Real.logb 2 (N : ℝ)

theorem dqptFreeEnergyFinite_eq_sub {s : ℂ} {N : ℕ}
    (hS : dqptAltPartialSum s N ≠ 0) (hN : 1 ≤ N) :
    dqptFreeEnergyFinite s N
      = -Real.log ‖dqptAltPartialSum s N‖ / Real.logb 2 (N : ℝ)
        - -Real.log (dqptPartition s.re N) / Real.logb 2 (N : ℝ) := by
  have hZ : dqptPartition s.re N ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_dqptPartition s.re hN))
  rw [dqptFreeEnergyFinite, Real.log_div (by simpa using hS) hZ]
  ring

/-! ## The eventual nonvanishing of the partial sum -/

theorem dqpt_eventually_altPartialSum_ne_zero_of_eta_zero {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1)
    (hz : (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s = 0) :
    ∀ᶠ N : ℕ in atTop, dqptAltPartialSum s N ≠ 0 := by
  filter_upwards [dqpt_eventually_threshold s] with N hN
  have hlow := dqptAltTail_norm_lower hs hN
  have hM0 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hpos : (0 : ℝ) < 1 / 4 * ((N : ℝ) + 1) ^ (-s.re) := by positivity
  have hA : dqptAltTail s N ≠ 0 := by
    intro h
    rw [h, norm_zero] at hlow
    linarith
  intro hS
  have h := dqptEta_eq_altPartialSum_add_tail hs hs1 N
  rw [hz, hS, zero_add] at h
  have hne : ((-1 : ℂ) ^ N) ≠ 0 := by
    exact pow_ne_zero N (by norm_num)
  exact hA (by
    rcases mul_eq_zero.mp h.symm with h' | h'
    · exact absurd h' hne
    · exact h')

theorem dqpt_eventually_altPartialSum_ne_zero_of_eta_ne_zero {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1)
    (hz : (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s ≠ 0) :
    ∀ᶠ N : ℕ in atTop, dqptAltPartialSum s N ≠ 0 := by
  have hlim := (dqpt_altPartialSum_tendsto hs hs1).norm
  have hpos : (0 : ℝ) < ‖(1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s‖ := norm_pos_iff.mpr hz
  filter_upwards [hlim.eventually (eventually_gt_nhds hpos)] with N hN
  intro h
  rw [h, norm_zero] at hN
  exact absurd hN (lt_irrefl 0)

/-! ## Methods (19) / published (26) -/

/-- **At an eta zero in the open critical strip the free-energy density is `ln 2`.** -/
theorem dqpt_freeEnergy_at_eta_zero {s : ℂ} (hs : 0 < s.re) (hs1 : s.re < 1)
    (hz : (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s = 0) :
    Tendsto (fun N : ℕ => dqptFreeEnergyFinite s N) atTop (𝓝 (Real.log 2)) := by
  have hsne : s ≠ 1 := fun h => by rw [h] at hs1; simp at hs1
  have hnum := dqpt_rate_at_eta_zero hs hsne hz
  have hden := dqpt_partition_rate_lt_one hs hs1
  have hsub := hnum.sub hden
  have hval : s.re * Real.log 2 - (s.re - 1) * Real.log 2 = Real.log 2 := by ring
  rw [hval] at hsub
  refine Tendsto.congr' ?_ hsub
  filter_upwards [dqpt_eventually_altPartialSum_ne_zero_of_eta_zero hs hsne hz,
    eventually_ge_atTop 1] with N hS hN
  exact (dqptFreeEnergyFinite_eq_sub hS hN).symm

/-- **In the open critical strip off the eta zeros the free-energy density is `(1−β) ln 2`.** -/
theorem dqpt_freeEnergy_strip {s : ℂ} (hs : 0 < s.re) (hs1 : s.re < 1)
    (hz : (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s ≠ 0) :
    Tendsto (fun N : ℕ => dqptFreeEnergyFinite s N) atTop
      (𝓝 ((1 - s.re) * Real.log 2)) := by
  have hsne : s ≠ 1 := fun h => by rw [h] at hs1; simp at hs1
  have hnum := dqpt_rate_at_eta_ne_zero hs hsne hz
  have hden := dqpt_partition_rate_lt_one hs hs1
  have hsub := hnum.sub hden
  have hval : (0 : ℝ) - (s.re - 1) * Real.log 2 = (1 - s.re) * Real.log 2 := by ring
  rw [hval] at hsub
  refine Tendsto.congr' ?_ hsub
  filter_upwards [dqpt_eventually_altPartialSum_ne_zero_of_eta_ne_zero hs hsne hz,
    eventually_ge_atTop 1] with N hS hN
  exact (dqptFreeEnergyFinite_eq_sub hS hN).symm

/-- **For `β > 1` the free-energy density vanishes.** -/
theorem dqpt_freeEnergy_right {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun N : ℕ => dqptFreeEnergyFinite s N) atTop (𝓝 0) := by
  have hs0 : 0 < s.re := lt_trans zero_lt_one hs
  have hsne : s ≠ 1 := fun h => by rw [h] at hs; simp at hs
  have hzeta : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  have hfac : (1 - (2 : ℂ) ^ (1 - s)) ≠ 0 := dqpt_eta_factor_ne_zero (ne_of_gt hs)
  have hz : (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s ≠ 0 := mul_ne_zero hfac hzeta
  have hnum := dqpt_rate_at_eta_ne_zero hs0 hsne hz
  have hden := dqpt_partition_rate_gt_one hs
  have hsub := hnum.sub hden
  rw [sub_zero] at hsub
  refine Tendsto.congr' ?_ hsub
  filter_upwards [dqpt_eventually_altPartialSum_ne_zero_of_eta_ne_zero hs0 hsne hz,
    eventually_ge_atTop 1] with N hS hN
  exact (dqptFreeEnergyFinite_eq_sub hS hN).symm

/-! ## Published (27)–(28): the entropy density -/

/-- The `β`-profile of the free-energy density inside the strip, away from the eta divisor. -/
def dqptFreeEnergyProfileStrip (β : ℝ) : ℝ := (1 - β) * Real.log 2

/-- The `β`-profile of the free-energy density for `β > 1`. -/
def dqptFreeEnergyProfileRight (_β : ℝ) : ℝ := 0

theorem hasDerivAt_dqptFreeEnergyProfileStrip (β : ℝ) :
    HasDerivAt dqptFreeEnergyProfileStrip (-Real.log 2) β := by
  have h : HasDerivAt (fun b : ℝ => (1 - b) * Real.log 2) ((0 - 1) * Real.log 2) β :=
    ((hasDerivAt_const β (1 : ℝ)).sub (hasDerivAt_id β)).mul_const (Real.log 2)
  have heq : ((0 : ℝ) - 1) * Real.log 2 = -Real.log 2 := by ring
  rw [heq] at h
  exact h

theorem deriv_dqptFreeEnergyProfileStrip (β : ℝ) :
    deriv dqptFreeEnergyProfileStrip β = -Real.log 2 :=
  (hasDerivAt_dqptFreeEnergyProfileStrip β).deriv

theorem deriv_dqptFreeEnergyProfileRight (β : ℝ) :
    deriv dqptFreeEnergyProfileRight β = 0 := by
  have hconst : dqptFreeEnergyProfileRight = fun _ : ℝ => (0 : ℝ) := rfl
  rw [hconst]
  simp

/-- The thermodynamic entropy density `𝒮 = −F + β ∂F/∂β` of a `β`-profile. -/
def dqptEntropyDensity (F : ℝ → ℝ) (β : ℝ) : ℝ := -F β + β * deriv F β

/-- **Published (28), strip case.**  `𝒮(β,t) = −ln 2` for `0 < β < 1` off the eta divisor. -/
theorem dqpt_entropy_strip (β : ℝ) :
    dqptEntropyDensity dqptFreeEnergyProfileStrip β = -Real.log 2 := by
  rw [dqptEntropyDensity, deriv_dqptFreeEnergyProfileStrip, dqptFreeEnergyProfileStrip]
  ring

/-- **Published (28), `β > 1` case.**  `𝒮(β,t) = 0`. -/
theorem dqpt_entropy_right (β : ℝ) :
    dqptEntropyDensity dqptFreeEnergyProfileRight β = 0 := by
  rw [dqptEntropyDensity, deriv_dqptFreeEnergyProfileRight, dqptFreeEnergyProfileRight]
  ring

/-- The strip profile is exactly the free-energy limit of `dqpt_freeEnergy_strip`. -/
theorem dqpt_freeEnergy_strip_profile {s : ℂ} (hs : 0 < s.re) (hs1 : s.re < 1)
    (hz : (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s ≠ 0) :
    Tendsto (fun N : ℕ => dqptFreeEnergyFinite s N) atTop
      (𝓝 (dqptFreeEnergyProfileStrip s.re)) :=
  dqpt_freeEnergy_strip hs hs1 hz

/-- The right-hand profile is exactly the free-energy limit of `dqpt_freeEnergy_right`. -/
theorem dqpt_freeEnergy_right_profile {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun N : ℕ => dqptFreeEnergyFinite s N) atTop
      (𝓝 (dqptFreeEnergyProfileRight s.re)) :=
  dqpt_freeEnergy_right hs

end

end RHTower.DQPT
