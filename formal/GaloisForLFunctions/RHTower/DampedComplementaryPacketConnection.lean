import GaloisForLFunctions.RHTower.ComplementaryPacketLocalZetaTwo

/-!
# The connection equation of the damped complementary packet

With a damping `δ > 0` the divisor-clock kernel is

```text
k_{ω,δ}(t) = e^(-(1+ω+δ)t) R_ω(e^t) ,
```

and the packet at continuous clock value `h` is

```text
B_h(t) = e^(-δh) 1_{t ≥ h} k_{ω,δ}(t - h) - c_ω 1_{t < h} e^(-δt) .
```

Its two branches meet with the source-fixed **unit** jump `e^(-δh)`, because `k_{ω,δ}(0) = ω/(1+ω)`
and `c_ω = 1/(1+ω)`.

The packet connection equation

```text
(∂_h - (1+ω)) B_h = q_δ - ∑_{m ≥ 1} e^(-δh) m^(-1-δ) δ_{h + log m}
```

is a distributional statement in `t`.  Integrating it in `h` turns every atom into an absolutely
continuous contribution and gives an **exact pointwise identity**, which is what is proved here:
for `h₁ ≤ h₂` and every `t`,

```text
e^(-(1+ω)h₂) B_{h₂}(t) - e^(-(1+ω)h₁) B_{h₁}(t)
  = e^(-δt) (e^(-(1+ω)h₁) - e^(-(1+ω)h₂))/(1+ω)
    - e^(-(1+ω+δ)t) ∑_{m : h₁ ≤ t - log m < h₂} m^ω ,
```

where the atom sum is the finite step increment `packetStepSum ω (t-h₁) - packetStepSum ω (t-h₂)`
and the weight `e^(-(1+ω+δ)t) m^ω` is exactly the transported atom `e^(-δh) m^(-1-δ)` at
`h = t - log m`.  The two classical readings of the connection equation — the smooth relation
`k' = -(1+ω+δ)k - q_δ` between jumps and the jump `m^(-1-δ)` at `log m` — are proved separately.
-/

open MeasureTheory Set Filter

namespace RHTower

noncomputable section

/-! ### The damped kernel -/

/-- The damped divisor-clock kernel `k_{ω,δ}(t) = e^(-(1+ω+δ)t) R_ω(e^t)`. -/
def dampedPacketKernel (ω δ t : ℝ) : ℝ :=
  Real.exp (-(1 + ω + δ) * t) * powerSumRemainder ω (Real.exp t)

/-- At zero damping the packet kernel is the boundary kernel of the complementary packet. -/
theorem dampedPacketKernel_zero_damping (ω t : ℝ) :
    dampedPacketKernel ω 0 t = complementaryPacketKernel ω t := by
  rw [dampedPacketKernel, complementaryPacketKernel, add_zero]

/-- Closed step form of the damped kernel. -/
theorem dampedPacketKernel_eq (ω δ : ℝ) (hω : 0 ≤ ω) (t : ℝ) :
    dampedPacketKernel ω δ t
      = Real.exp (-(1 + ω + δ) * t) * packetStepSum ω t - Real.exp (-δ * t) / (1 + ω) := by
  have hne : (1 : ℝ) + ω ≠ 0 := by linarith
  have hpow : (Real.exp t) ^ (1 + ω) = Real.exp (t * (1 + ω)) := (Real.exp_mul t (1 + ω)).symm
  rw [dampedPacketKernel, powerSumRemainder, hpow, packetStepSum, mul_sub]
  congr 1
  rw [mul_div_assoc', ← Real.exp_add]
  congr 2
  ring

/-- The step profile vanishes before the clock origin. -/
theorem packetStepSum_of_neg {ω : ℝ} (hω : 0 < ω) {t : ℝ} (ht : t < 0) :
    packetStepSum ω t = 0 := by
  have hfl : ⌊Real.exp t⌋₊ = 0 := by
    refine Nat.floor_eq_zero.mpr ?_
    have h := Real.exp_lt_exp.mpr ht
    rwa [Real.exp_zero] at h
  rw [packetStepSum, hfl, zero_add, Finset.sum_range_one, Nat.cast_zero,
    Real.zero_rpow (ne_of_gt hω)]

/-- The step profile at the clock origin is one. -/
theorem packetStepSum_zero {ω : ℝ} (hω : 0 < ω) : packetStepSum ω 0 = 1 := by
  have hfl : ⌊Real.exp (0 : ℝ)⌋₊ = 1 := by
    rw [Real.exp_zero, Nat.floor_one]
  rw [packetStepSum, hfl, Finset.sum_range_succ, Finset.sum_range_one, Nat.cast_zero,
    Nat.cast_one, Real.zero_rpow (ne_of_gt hω), Real.one_rpow, zero_add]

/-- **The source-fixed value of the damped kernel at the clock origin.** -/
theorem dampedPacketKernel_zero (ω δ : ℝ) (hω : 0 < ω) :
    dampedPacketKernel ω δ 0 = ω / (1 + ω) := by
  have hne : (1 : ℝ) + ω ≠ 0 := by linarith
  rw [dampedPacketKernel_eq ω δ hω.le, packetStepSum_zero hω]
  simp only [mul_zero, Real.exp_zero, mul_one]
  field_simp
  ring

/-! ### The packet path and its unit jump -/

/-- The damped divisor-clock packet at continuous clock value `h`. -/
def dampedPacketPath (ω δ h t : ℝ) : ℝ :=
  if h ≤ t then Real.exp (-δ * h) * dampedPacketKernel ω δ (t - h)
  else -(complementaryPacketConstant ω) * Real.exp (-δ * t)

theorem dampedPacketPath_of_le (ω δ h : ℝ) {t : ℝ} (ht : h ≤ t) :
    dampedPacketPath ω δ h t = Real.exp (-δ * h) * dampedPacketKernel ω δ (t - h) := if_pos ht

theorem dampedPacketPath_of_lt (ω δ h : ℝ) {t : ℝ} (ht : t < h) :
    dampedPacketPath ω δ h t = -(complementaryPacketConstant ω) * Real.exp (-δ * t) :=
  if_neg (not_le.mpr ht)

/-- The incoming branch is continuous, so the packet has a left limit at the moving boundary. -/
theorem tendsto_dampedPacketPath_nhdsLT (ω δ h : ℝ) :
    Tendsto (dampedPacketPath ω δ h) (nhdsWithin h (Iio h))
      (nhds (-(complementaryPacketConstant ω) * Real.exp (-δ * h))) := by
  have hcont : Tendsto (fun t : ℝ => -(complementaryPacketConstant ω) * Real.exp (-δ * t))
      (nhdsWithin h (Iio h)) (nhds (-(complementaryPacketConstant ω) * Real.exp (-δ * h))) := by
    refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
    exact (continuous_const.mul (Real.continuous_exp.comp
      (continuous_const.mul continuous_id))).tendsto h
  refine hcont.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (dampedPacketPath_of_lt ω δ h ht).symm

/-- **Unit moving boundary jump.**  The two branches of the packet meet with jump `e^(-δh)`, before
any completion. -/
theorem dampedPacketPath_jump (ω δ : ℝ) (hω : 0 < ω) (h : ℝ) :
    dampedPacketPath ω δ h h - -(complementaryPacketConstant ω) * Real.exp (-δ * h)
      = Real.exp (-δ * h) := by
  have hne : (1 : ℝ) + ω ≠ 0 := by linarith
  rw [dampedPacketPath_of_le ω δ h (le_refl h), sub_self, dampedPacketKernel_zero ω δ hω,
    complementaryPacketConstant]
  field_simp
  ring

/-! ### The integrated connection equation -/

private theorem dampedPacketPath_weighted_of_le (ω δ : ℝ) (hω : 0 ≤ ω) {h t : ℝ} (ht : h ≤ t) :
    Real.exp (-(1 + ω) * h) * dampedPacketPath ω δ h t
      = Real.exp (-(1 + ω + δ) * t) * packetStepSum ω (t - h)
        - Real.exp (-(1 + ω) * h) * Real.exp (-δ * t) / (1 + ω) := by
  have hne : (1 : ℝ) + ω ≠ 0 := by linarith
  rw [dampedPacketPath_of_le ω δ h ht, dampedPacketKernel_eq ω δ hω]
  have h1 : Real.exp (-(1 + ω) * h) * Real.exp (-δ * h)
      * Real.exp (-(1 + ω + δ) * (t - h)) = Real.exp (-(1 + ω + δ) * t) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have h2 : Real.exp (-(1 + ω) * h) * Real.exp (-δ * h) * Real.exp (-δ * (t - h))
      = Real.exp (-(1 + ω) * h) * Real.exp (-δ * t) := by
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  calc Real.exp (-(1 + ω) * h) * (Real.exp (-δ * h) *
        (Real.exp (-(1 + ω + δ) * (t - h)) * packetStepSum ω (t - h)
          - Real.exp (-δ * (t - h)) / (1 + ω)))
      = (Real.exp (-(1 + ω) * h) * Real.exp (-δ * h) * Real.exp (-(1 + ω + δ) * (t - h)))
          * packetStepSum ω (t - h)
        - (Real.exp (-(1 + ω) * h) * Real.exp (-δ * h) * Real.exp (-δ * (t - h))) / (1 + ω) := by
        ring
    _ = Real.exp (-(1 + ω + δ) * t) * packetStepSum ω (t - h)
        - Real.exp (-(1 + ω) * h) * Real.exp (-δ * t) / (1 + ω) := by rw [h1, h2]

/-- **Integrated packet connection equation.**  The `h`-primitive of
`(∂_h - (1+ω)) B_h = q_δ - ∑_m e^(-δh) m^(-1-δ) δ_{h+log m}`, holding pointwise in `t` with no
distributional interpretation: the transported atoms accumulate into the exact step increment of
the power sum. -/
theorem dampedPacketPath_connection (ω δ : ℝ) (hω : 0 < ω) {h₁ h₂ : ℝ} (hh : h₁ ≤ h₂) (t : ℝ) :
    Real.exp (-(1 + ω) * h₂) * dampedPacketPath ω δ h₂ t
        - Real.exp (-(1 + ω) * h₁) * dampedPacketPath ω δ h₁ t
      = Real.exp (-δ * t) * (Real.exp (-(1 + ω) * h₁) - Real.exp (-(1 + ω) * h₂)) / (1 + ω)
        - Real.exp (-(1 + ω + δ) * t)
            * (packetStepSum ω (t - h₁) - packetStepSum ω (t - h₂)) := by
  have hne : (1 : ℝ) + ω ≠ 0 := by linarith
  by_cases ht2 : h₂ ≤ t
  · -- both branches outgoing
    have ht1 : h₁ ≤ t := le_trans hh ht2
    rw [dampedPacketPath_weighted_of_le ω δ hω.le ht2,
      dampedPacketPath_weighted_of_le ω δ hω.le ht1]
    field_simp
    ring
  · replace ht2 : t < h₂ := not_le.mp ht2
    by_cases ht1 : h₁ ≤ t
    · -- the moving boundary is crossed between `h₁` and `h₂`
      have hzero : packetStepSum ω (t - h₂) = 0 := packetStepSum_of_neg hω (by linarith)
      rw [dampedPacketPath_of_lt ω δ h₂ ht2, dampedPacketPath_weighted_of_le ω δ hω.le ht1,
        hzero, complementaryPacketConstant]
      field_simp
      ring
    · replace ht1 : t < h₁ := not_le.mp ht1
      -- both branches incoming
      have hz1 : packetStepSum ω (t - h₁) = 0 := packetStepSum_of_neg hω (by linarith)
      have hz2 : packetStepSum ω (t - h₂) = 0 := packetStepSum_of_neg hω (by linarith)
      rw [dampedPacketPath_of_lt ω δ h₂ ht2, dampedPacketPath_of_lt ω δ h₁ ht1, hz1, hz2,
        complementaryPacketConstant]
      field_simp
      ring

/-! ### The two classical readings -/

/-- **The smooth connection relation between jumps.**  Away from the shifted power-sum atoms the
damped kernel satisfies `k' = -(1+ω+δ) k - q_δ`. -/
theorem hasDerivAt_dampedPacketKernel (ω δ : ℝ) (hω : 0 ≤ ω) {m : ℕ} (hm : 1 ≤ m) {t : ℝ}
    (ht1 : Real.log (m : ℝ) < t) (ht2 : t < Real.log ((m : ℝ) + 1)) :
    HasDerivAt (dampedPacketKernel ω δ)
      (-(1 + ω + δ) * dampedPacketKernel ω δ t - Real.exp (-δ * t)) t := by
  have hne : (1 : ℝ) + ω ≠ 0 := by linarith
  set S : ℝ := packetStepSum ω t with hS
  have hlocal : ∀ s ∈ Ioo (Real.log (m : ℝ)) (Real.log ((m : ℝ) + 1)), packetStepSum ω s = S := by
    intro s hs
    have h1 : ⌊Real.exp s⌋₊ = m := floor_exp_eq hm hs.1.le hs.2
    have h2 : ⌊Real.exp t⌋₊ = m := floor_exp_eq hm ht1.le ht2
    rw [hS, packetStepSum, packetStepSum, h1, h2]
  have hmem : Ioo (Real.log (m : ℝ)) (Real.log ((m : ℝ) + 1)) ∈ nhds t :=
    Ioo_mem_nhds ht1 ht2
  have hg : HasDerivAt (fun s : ℝ =>
      Real.exp (-(1 + ω + δ) * s) * S - Real.exp (-δ * s) / (1 + ω))
      (-(1 + ω + δ) * (Real.exp (-(1 + ω + δ) * t) * S)
        + δ * Real.exp (-δ * t) / (1 + ω)) t := by
    have hlin1 : HasDerivAt (fun s : ℝ => -(1 + ω + δ) * s) (-(1 + ω + δ)) t := by
      simpa using (hasDerivAt_id t).const_mul (-(1 + ω + δ))
    have hlin2 : HasDerivAt (fun s : ℝ => -δ * s) (-δ) t := by
      simpa using (hasDerivAt_id t).const_mul (-δ)
    have h1 : HasDerivAt (fun s : ℝ => Real.exp (-(1 + ω + δ) * s))
        (-(1 + ω + δ) * Real.exp (-(1 + ω + δ) * t)) t := by
      simpa [mul_comm] using hlin1.exp
    have h2 : HasDerivAt (fun s : ℝ => Real.exp (-δ * s)) (-δ * Real.exp (-δ * t)) t := by
      simpa [mul_comm] using hlin2.exp
    have h3 := (h1.mul_const S).sub (h2.div_const (1 + ω))
    convert h3 using 1
    field_simp
    ring
  have heq : (fun s : ℝ => Real.exp (-(1 + ω + δ) * s) * S - Real.exp (-δ * s) / (1 + ω))
      =ᶠ[nhds t] dampedPacketKernel ω δ := by
    filter_upwards [hmem] with s hs
    rw [dampedPacketKernel_eq ω δ hω, hlocal s hs]
  refine (hg.congr_of_eventuallyEq heq.symm).congr_deriv ?_
  rw [dampedPacketKernel_eq ω δ hω, ← hS]
  field_simp
  ring

/-- **The shifted power-sum atom.**  The damped kernel jumps by `m^(-1-δ)` at `log m`. -/
theorem tendsto_dampedPacketKernel_nhdsLT (ω δ : ℝ) (hω : 0 ≤ ω) {m : ℕ} (hm : 2 ≤ m) :
    Tendsto (dampedPacketKernel ω δ) (nhdsWithin (Real.log (m : ℝ)) (Iio (Real.log (m : ℝ))))
      (nhds (dampedPacketKernel ω δ (Real.log (m : ℝ)) - (m : ℝ) ^ (-1 - δ))) := by
  have hne : (1 : ℝ) + ω ≠ 0 := by linarith
  have hm1 : (1 : ℝ) ≤ (m : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
  have hcastm : (((m - 1 : ℕ) : ℝ)) = (m : ℝ) - 1 := by
    have : (1 : ℕ) ≤ m := by omega
    push_cast [Nat.cast_sub this]
    ring
  have hlogm : Real.log ((m : ℝ) - 1) < Real.log (m : ℝ) :=
    Real.log_lt_log (by linarith) (by linarith)
  -- the floor of the exponential is `m` at the jump and `m - 1` just below it
  have hflAt : ⌊Real.exp (Real.log (m : ℝ))⌋₊ = m := by
    rw [Real.exp_log hmpos, Nat.floor_natCast]
  have hstepAt : packetStepSum ω (Real.log (m : ℝ))
      = (∑ i ∈ Finset.range m, (i : ℝ) ^ ω) + (m : ℝ) ^ ω := by
    rw [packetStepSum, hflAt, Finset.sum_range_succ]
  -- the incoming branch is the continuous function with step value `m - 1`
  set S : ℝ := ∑ i ∈ Finset.range m, (i : ℝ) ^ ω with hS
  have hG : Tendsto (fun s : ℝ => Real.exp (-(1 + ω + δ) * s) * S - Real.exp (-δ * s) / (1 + ω))
      (nhdsWithin (Real.log (m : ℝ)) (Iio (Real.log (m : ℝ))))
      (nhds (Real.exp (-(1 + ω + δ) * Real.log (m : ℝ)) * S
        - Real.exp (-δ * Real.log (m : ℝ)) / (1 + ω))) := by
    refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
    exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      continuous_const).sub
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).div_const (1 + ω))
      |>.tendsto _
  have hcongr : (fun s : ℝ => Real.exp (-(1 + ω + δ) * s) * S - Real.exp (-δ * s) / (1 + ω))
      =ᶠ[nhdsWithin (Real.log (m : ℝ)) (Iio (Real.log (m : ℝ)))] dampedPacketKernel ω δ := by
    have hmem : Ioi (Real.log ((m : ℝ) - 1))
        ∈ nhdsWithin (Real.log (m : ℝ)) (Iio (Real.log (m : ℝ))) :=
      nhdsWithin_le_nhds (Ioi_mem_nhds hlogm)
    filter_upwards [self_mem_nhdsWithin, hmem] with s hs1 hs2
    have hfl : ⌊Real.exp s⌋₊ = m - 1 := by
      refine floor_exp_eq (m := m - 1) (by omega) ?_ ?_
      · rw [hcastm]
        exact le_of_lt hs2
      · rw [hcastm, sub_add_cancel]
        exact hs1
    rw [dampedPacketKernel_eq ω δ hω, packetStepSum, hfl, hS,
      show m - 1 + 1 = m from by omega]
  have hlim := hG.congr' hcongr
  have hpow : Real.exp (-(1 + ω + δ) * Real.log (m : ℝ)) * (m : ℝ) ^ ω = (m : ℝ) ^ (-1 - δ) := by
    have h1 : Real.exp (-(1 + ω + δ) * Real.log (m : ℝ)) = (m : ℝ) ^ (-(1 + ω + δ)) := by
      rw [Real.rpow_def_of_pos hmpos]
      congr 1
      ring
    rw [h1, ← Real.rpow_add hmpos]
    congr 1
    ring
  have hval : Real.exp (-(1 + ω + δ) * Real.log (m : ℝ)) * S
      - Real.exp (-δ * Real.log (m : ℝ)) / (1 + ω)
      = dampedPacketKernel ω δ (Real.log (m : ℝ)) - (m : ℝ) ^ (-1 - δ) := by
    rw [dampedPacketKernel_eq ω δ hω, hstepAt, ← hpow]
    ring
  rwa [hval] at hlim

end

end RHTower
