import GaloisForLFunctions.HTGeometry.OscillatorMassNoEscape

/-!
# From the oscillator ladder pin to saturation of a single Hermite coordinate

The ladder pin expresses each Hermite coordinate of a rescaled profile through a defect pairing
divided by the bandwidth:

`(μ − (2m+1)) · A m = P m / c` .

If the numerators `P m` stay bounded for each fixed `m`, the bandwidth escapes and the separation
constant approaches the `n`-th rung `2n+1`, then every coordinate off that rung vanishes.  Combined
with unit total mass and a uniformly bounded oscillator energy — which forbids the mass from
drifting to high rungs — the `n`-th coordinate saturates:

`A n ² → 1` .

Only boundedness of the energy is used; the pin supplies no rate and none is needed.
-/

open Filter Topology

namespace RHTower

/-- A coordinate pinned by `(μ − lam) · A = P / c` with bounded numerator vanishes as soon as the
bandwidth escapes and the separation constant stays away from `lam`. -/
theorem tendsto_coeff_zero_of_pin
    {ι : Type*} {L : Filter ι} {A P μ c : ι → ℝ} {B lam lim0 : ℝ}
    (hpin : ∀ i, (μ i - lam) * A i = P i / c i)
    (hP : ∀ i, |P i| ≤ B)
    (hc : Tendsto c L atTop)
    (hμ : Tendsto μ L (𝓝 lim0)) (hne : lim0 ≠ lam) :
    Tendsto A L (𝓝 0) := by
  set δ : ℝ := |lim0 - lam| / 2 with hδdef
  have hδpos : 0 < δ := by
    have : 0 < |lim0 - lam| := abs_pos.2 (sub_ne_zero.2 hne)
    rw [hδdef]; linarith
  -- eventually the separation stays at distance at least `δ` from `lam`
  have hsep : ∀ᶠ i in L, δ ≤ |μ i - lam| := by
    have hball := hμ (Metric.ball_mem_nhds lim0 hδpos)
    filter_upwards [hball] with i hi
    have h1 : |μ i - lim0| < δ := by
      simpa [Real.dist_eq] using hi
    have h2 : |lim0 - lam| ≤ |lim0 - μ i| + |μ i - lam| := abs_sub_le _ _ _
    have h3 : |lim0 - μ i| = |μ i - lim0| := abs_sub_comm _ _
    rw [h3] at h2
    rw [hδdef]
    linarith
  have hcpos : ∀ᶠ i in L, (0 : ℝ) < c i := hc.eventually_gt_atTop 0
  have hbound : ∀ᶠ i in L, ‖A i‖ ≤ B / (c i * δ) := by
    filter_upwards [hsep, hcpos] with i hi hci
    have hne' : μ i - lam ≠ 0 := by
      intro h; rw [h, abs_zero] at hi; linarith
    have hA : |μ i - lam| * |A i| = |P i| / c i := by
      rw [← abs_mul, hpin i, abs_div, abs_of_pos hci]
    have hnn : 0 ≤ |A i| := abs_nonneg _
    have hstep : δ * |A i| ≤ |P i| / c i := by
      calc δ * |A i| ≤ |μ i - lam| * |A i| := by nlinarith
        _ = |P i| / c i := hA
    rw [Real.norm_eq_abs, le_div_iff₀ (by positivity)]
    calc |A i| * (c i * δ) = (δ * |A i|) * c i := by ring
      _ ≤ (|P i| / c i) * c i := by nlinarith [hci.le]
      _ = |P i| := by field_simp
      _ ≤ B := hP i
  refine squeeze_zero_norm' hbound ?_
  have hcδ : Tendsto (fun i => c i * δ) L atTop := hc.atTop_mul_const hδpos
  exact tendsto_const_nhds.div_atTop hcδ

/-- **Coordinate saturation from the ladder pin.**  Coordinates off the `n`-th rung are pinned and
vanish; unit total mass plus a uniform oscillator-energy bound stops mass from escaping to high
rungs; hence the squared `n`-th coordinate tends to one. -/
theorem tendsto_coeffSq_of_ladderPin
    {ι : Type*} {L : Filter ι} {A P : ι → ℕ → ℝ} {μ c : ι → ℝ} {B : ℕ → ℝ} {C : ℝ} (n : ℕ)
    (hpin : ∀ m, m ≠ n → ∀ i, (μ i - (2 * (m : ℝ) + 1)) * A i m = P i m / c i)
    (hP : ∀ i m, |P i m| ≤ B m)
    (hc : Tendsto c L atTop)
    (hμ : Tendsto μ L (𝓝 (2 * (n : ℝ) + 1)))
    (hE : ∀ i, Summable fun m : ℕ => (2 * (m : ℝ) + 1) * (A i m) ^ (2 : ℕ))
    (htotal : ∀ i, (∑' m : ℕ, (A i m) ^ (2 : ℕ)) = 1)
    (hC : ∀ i, (∑' m : ℕ, (2 * (m : ℝ) + 1) * (A i m) ^ (2 : ℕ)) ≤ C) :
    Tendsto (fun i => (A i n) ^ (2 : ℕ)) L (𝓝 1) := by
  refine GaloisForLFunctions.HTGeometry.tendsto_coeff_of_vanishing_of_moment_le n
    (fun i m => sq_nonneg _) hE htotal hC ?_
  intro m hm
  have hlam : (2 * (n : ℝ) + 1) ≠ (2 * (m : ℝ) + 1) := by
    intro h
    have hmn : (m : ℝ) = (n : ℝ) := by linarith
    exact hm (by exact_mod_cast hmn)
  have hzero : Tendsto (fun i => A i m) L (𝓝 0) :=
    tendsto_coeff_zero_of_pin (hpin m hm) (fun i => hP i m) hc hμ hlam
  have := hzero.pow 2
  simpa using this

/-- The absolute value of the saturating coordinate tends to one. -/
theorem tendsto_abs_coeff_of_coeffSq
    {ι : Type*} {L : Filter ι} {A : ι → ℝ}
    (h : Tendsto (fun i => (A i) ^ (2 : ℕ)) L (𝓝 1)) :
    Tendsto (fun i => |A i|) L (𝓝 1) := by
  have hsqrt : Tendsto (fun i => Real.sqrt ((A i) ^ (2 : ℕ))) L (𝓝 (Real.sqrt 1)) :=
    (Real.continuous_sqrt.tendsto 1).comp h
  simpa [Real.sqrt_sq_eq_abs] using hsqrt

end RHTower
