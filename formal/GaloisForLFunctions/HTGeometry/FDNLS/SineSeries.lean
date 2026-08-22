import GaloisForLFunctions.RHTower.SawtoothFourierSeries

/-!
# The two classical sine series used to check the band edges

Zhong--Malomed--Yan, arXiv:2407.12441, Section II D, equations (36) and (37).

The paper checks the two band-edge values (34) and (35) directly against the classical sums

`∑_{ℓ ≥ 1} sin(ℓ k)/ℓ = (π - k)/2`  and  `∑_{ℓ ≥ 1} (-1)^ℓ sin(ℓ k)/ℓ = -k/2`,

valid on `0 < k < 2π` and `-π < k < π` respectively (the endpoint values quoted in the paper are
one-sided limits, not values of the series: at `k = 0` every term vanishes).

The first is the sawtooth Fourier series, which the corpus already owns; the second follows from it
by the half-period shift `k ↦ k + π`, which multiplies the `ℓ`-th sine by `(-1)^ℓ`.

## Main results

* `tendsto_sum_sine_div` — **equation (36)**.
* `tendsto_sum_alternating_sine_div` — **equation (37)**.
* `sum_sine_div_at_zero` — at `k = 0` the series is identically `0`, so `(36)` genuinely fails at
  the endpoint and must be read as a limit.
-/

open Filter Topology Finset Set

namespace GaloisForLFunctions.HTGeometry.FDNLS

/-- **Equation (36).**  On `(0, 2π)` the harmonic sine series sums to the sawtooth `(π - k)/2`. -/
theorem tendsto_sum_sine_div {k : ℝ} (hk : k ∈ Ioo 0 (2 * Real.pi)) :
    Tendsto (fun N => ∑ ℓ ∈ range N, Real.sin ((ℓ : ℝ) * k) / (ℓ : ℝ)) atTop
      (𝓝 ((Real.pi - k) / 2)) := by
  have h := RHTower.tendsto_sum_sawtoothSine hk
  rwa [RHTower.sawWave_eq_of_mem_Ioo hk] at h

/-- At the left endpoint the series is identically zero, so equation (36) holds there only as a
one-sided limit. -/
theorem sum_sine_div_at_zero (N : ℕ) :
    ∑ ℓ ∈ range N, Real.sin ((ℓ : ℝ) * (0:ℝ)) / (ℓ : ℝ) = 0 := by
  simp

/-- The half-period shift multiplies the `ℓ`-th sine harmonic by `(-1)^ℓ`. -/
theorem sin_nat_mul_add_pi (ℓ : ℕ) (k : ℝ) :
    Real.sin ((ℓ : ℝ) * (k + Real.pi)) = (-1 : ℝ) ^ ℓ * Real.sin ((ℓ : ℝ) * k) := by
  have hcast : ((ℓ : ℝ)) = (((ℓ : ℤ) : ℝ)) := by push_cast; ring
  rw [mul_add, Real.sin_add, hcast, Real.sin_int_mul_pi, Real.cos_int_mul_pi]
  rw [zpow_natCast]
  ring

/-- **Equation (37).**  On `(-π, π)` the alternating harmonic sine series sums to `-k/2`. -/
theorem tendsto_sum_alternating_sine_div {k : ℝ} (hk : k ∈ Ioo (-Real.pi) Real.pi) :
    Tendsto (fun N => ∑ ℓ ∈ range N, (-1 : ℝ) ^ ℓ * Real.sin ((ℓ : ℝ) * k) / (ℓ : ℝ)) atTop
      (𝓝 (-k / 2)) := by
  have hshift : k + Real.pi ∈ Ioo 0 (2 * Real.pi) := by
    obtain ⟨h1, h2⟩ := hk
    exact ⟨by linarith, by linarith⟩
  have h := tendsto_sum_sine_div hshift
  have hval : (Real.pi - (k + Real.pi)) / 2 = -k / 2 := by ring
  rw [hval] at h
  refine h.congr fun N => ?_
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [sin_nat_mul_add_pi ℓ k]

end GaloisForLFunctions.HTGeometry.FDNLS
