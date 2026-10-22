import GaloisForLFunctions.RHTower.Suzuki.SuzukiCoalescingFragmentPole

/-!
# First-order rates of a coalescing characteristic

A characteristic that tends to one at rate `c` has a well-defined Cayley rate: if
`(Θ_c - 1)/c → 2w` then

`(1 - Θ_c) / (c (1 + Θ_c)) → -w`,

because the denominator tends to `2`.  Rates add across products, so the rate of the whole quotient
is the sum of the anchor's rate and the rate of the source ratio.

For the anchor chart itself the rate is explicit: `(b_c(z) - 1)/c = -2i/(z + ic) → -2i/z` on the
real axis away from the origin, which contributes the `i/z` of the limiting profile.
-/

noncomputable section

namespace RHTower

open Complex Filter Topology

/-- The Cayley rate of a characteristic that tends to one. -/
def suzukiCoalescingCayleyRate (Θ : ℝ → ℂ) (c : ℝ) : ℂ :=
  (1 - Θ c) / (c * (1 + Θ c))

/-- A characteristic with a first-order rate tends to one. -/
theorem tendsto_one_of_firstOrderRate {Θ : ℝ → ℂ} {w : ℂ}
    (h : Tendsto (fun c : ℝ => (Θ c - 1) / c) (𝓝[>] 0) (𝓝 (2 * w))) :
    Tendsto Θ (𝓝[>] 0) (𝓝 1) := by
  have hc : Tendsto (fun c : ℝ => (c : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun c : ℝ => (c : ℂ)) (𝓝 0) (𝓝 ((0 : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto 0)
    simpa using this.mono_left nhdsWithin_le_nhds
  have hprod : Tendsto (fun c : ℝ => ((Θ c - 1) / c) * (c : ℂ)) (𝓝[>] 0) (𝓝 (2 * w * 0)) :=
    h.mul hc
  rw [mul_zero] at hprod
  have hcongr : Tendsto (fun c : ℝ => Θ c - 1) (𝓝[>] 0) (𝓝 0) := by
    refine hprod.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with c hc0
    have hcne : (c : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt hc0
    field_simp
  have := hcongr.add (tendsto_const_nhds (x := (1 : ℂ)))
  simpa using this

/-- **The Cayley rate of a first-order characteristic.** -/
theorem tendsto_suzukiCoalescingCayleyRate {Θ : ℝ → ℂ} {w : ℂ}
    (h : Tendsto (fun c : ℝ => (Θ c - 1) / c) (𝓝[>] 0) (𝓝 (2 * w))) :
    Tendsto (suzukiCoalescingCayleyRate Θ) (𝓝[>] 0) (𝓝 (-w)) := by
  have hone := tendsto_one_of_firstOrderRate h
  have hden : Tendsto (fun c : ℝ => 1 + Θ c) (𝓝[>] 0) (𝓝 2) := by
    have h2 := (tendsto_const_nhds (x := (1 : ℂ))).add hone
    rw [show (1 : ℂ) + 1 = 2 by norm_num] at h2
    exact h2
  have hne : (2 : ℂ) ≠ 0 := two_ne_zero
  have hquot : Tendsto (fun c : ℝ => -((Θ c - 1) / c) / (1 + Θ c)) (𝓝[>] 0)
      (𝓝 (-(2 * w) / 2)) := (h.neg).div hden hne
  have hval : -(2 * w) / 2 = -w := by ring
  rw [hval] at hquot
  refine hquot.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with c hc0
  have hcne : (c : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hc0
  rw [suzukiCoalescingCayleyRate, ← neg_div, div_div]
  congr 1
  ring

/-- Rates add across products. -/
theorem tendsto_firstOrderRate_mul {Θ₁ Θ₂ : ℝ → ℂ} {w₁ w₂ : ℂ}
    (h₁ : Tendsto (fun c : ℝ => (Θ₁ c - 1) / c) (𝓝[>] 0) (𝓝 (2 * w₁)))
    (h₂ : Tendsto (fun c : ℝ => (Θ₂ c - 1) / c) (𝓝[>] 0) (𝓝 (2 * w₂))) :
    Tendsto (fun c : ℝ => (Θ₁ c * Θ₂ c - 1) / c) (𝓝[>] 0) (𝓝 (2 * (w₁ + w₂))) := by
  have hone₂ := tendsto_one_of_firstOrderRate h₂
  have hsum : Tendsto (fun c : ℝ => ((Θ₁ c - 1) / c) * Θ₂ c + (Θ₂ c - 1) / c)
      (𝓝[>] 0) (𝓝 (2 * w₁ * 1 + 2 * w₂)) := (h₁.mul hone₂).add h₂
  have hval : 2 * w₁ * 1 + 2 * w₂ = 2 * (w₁ + w₂) := by ring
  rw [hval] at hsum
  refine hsum.congr fun c => ?_
  by_cases hc0 : (c : ℂ) = 0
  · simp [hc0]
  · field_simp
    ring

/-- **The anchor's own first-order rate.**  On the real axis away from the origin the movable Cayley
chart has rate `-2i/z`. -/
theorem tendsto_suzukiCoalescingCayley_rate {z : ℝ} (hz : z ≠ 0) :
    Tendsto (fun c : ℝ => (suzukiCoalescingCayley c (z : ℂ) - 1) / c) (𝓝[>] 0)
      (𝓝 (2 * (-I / z))) := by
  have hzC : (z : ℂ) ≠ 0 := by exact_mod_cast hz
  have hcont : Tendsto (fun c : ℝ => -2 * I / ((z : ℂ) + (c : ℂ) * I)) (𝓝[>] 0)
      (𝓝 (-2 * I / ((z : ℂ) + ((0 : ℝ) : ℂ) * I))) := by
    have hnum : Tendsto (fun c : ℝ => ((z : ℂ) + (c : ℂ) * I)) (𝓝[>] 0)
        (𝓝 ((z : ℂ) + ((0 : ℝ) : ℂ) * I)) := by
      have : Tendsto (fun c : ℝ => ((z : ℂ) + (c : ℂ) * I)) (𝓝 0)
          (𝓝 ((z : ℂ) + ((0 : ℝ) : ℂ) * I)) := by
        exact ((Complex.continuous_ofReal.mul continuous_const).const_add _).tendsto 0
      exact this.mono_left nhdsWithin_le_nhds
    have hden : ((z : ℂ) + ((0 : ℝ) : ℂ) * I) ≠ 0 := by simpa using hzC
    exact tendsto_const_nhds.div hnum hden
  have hval : -2 * I / ((z : ℂ) + ((0 : ℝ) : ℂ) * I) = 2 * (-I / (z : ℂ)) := by
    rw [Complex.ofReal_zero, zero_mul, add_zero]
    ring
  rw [hval] at hcont
  refine hcont.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with c hc0
  have hcne : (c : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hc0
  have hB : (z : ℂ) + (c : ℂ) * I ≠ 0 := real_add_c_I_ne_zero hc0 z
  have hB' : I * (c : ℂ) + (z : ℂ) ≠ 0 := by
    intro h
    exact hB (by linear_combination h)
  rw [suzukiCoalescingCayley, div_sub_one hB, div_div]
  rw [show ((z : ℂ) - (c : ℂ) * I) - ((z : ℂ) + (c : ℂ) * I) = (c : ℂ) * (-2 * I) by ring]
  rw [mul_comm ((z : ℂ) + (c : ℂ) * I) (c : ℂ)]
  rw [mul_div_mul_left _ _ hcne]

end RHTower
