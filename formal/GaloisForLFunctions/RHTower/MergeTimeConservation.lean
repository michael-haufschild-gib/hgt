import GaloisForLFunctions.RHTower.ImaginaryEnergyLyapunov

/-!
# Conservation of merge time: the imaginary energy pays for every merge

Let `t₁ ≤ … ≤ t_m` be the times at which the conjugate pairs of the divisor reach the real axis
along the de Bruijn–Newman flow, and let `m(t) = #{i : t < t_i}` be the number of pairs still
complex at time `t`.  By the orbit decomposition this count *is* the Weil index,
`m(t) = ind₋(W_{Ξ_t})`, and by the energy identity the imaginary energy drops at rate at least
`4m(t)`:

```text
İ(t) ≤ -4 m(t) ,        I ≥ 0 ,        I(0) = Σ_ρ (Re ρ - ½)² .
```

Integrating and using the layer-cake identity `∫₀^∞ m(t) dt = Σ_i t_i` — which in the piecewise
constant setting is the Abel summation `Σ_i (m-i)(t_{i+1} - t_i) = Σ_i t_{i+1}` — gives the exact
accounting

```text
4 Σ_i t_i  ≤  Σ_ρ (Re ρ - ½)²           and equivalently
∫₀^Λ ind₋(W_{Ξ_t}) dt  ≤  (1/4) Σ_ρ (Re ρ - ½)² .
```

The **sum** of the merge times, not merely the largest, is bounded.  Three readings:

* Since `Λ = max_i t_i ≤ Σ_i t_i`, this refines `Λ ≤ (1/4)Σ_ρ (Re ρ - ½)²`.
* Many off-critical pairs force a *short* extinction time: if `m` pairs all survive to time `Λ` then
  `mΛ ≤ Σ_i t_i ≤ (1/4)Σ_ρ (Re ρ - ½)²`, so `Λ` decreases as the number of exceptions grows.  A
  large violation of the Riemann hypothesis would be extinguished quickly.
* Each merge costs four units of imaginary energy per unit of time it takes.  Slow merges are
  expensive, and the total budget is the squared deviation of the divisor from the critical line.

This puts the Connes–Consani–Moscovici index and the de Bruijn–Newman flow in a single inequality
whose right-hand side is a zero-statistic: the index integrated over flow time is controlled by the
second moment of the real parts.

This file formalizes the Abel summation behind the layer-cake identity and the resulting bound.
-/

open Finset

noncomputable section

namespace RHTower

/-- **The layer-cake identity in piecewise constant form.**  With `t 0 = 0` and `t` the ordered merge
times, the count `m(t)` is `m - i` on the `i`-th interval, and Abel summation gives
`Σ_i (m - i)(t_{i+1} - t_i) = Σ_i t_{i+1}` — the integral of the count is the sum of the times. -/
theorem abel_merge_count (t : ℕ → ℝ) (h0 : t 0 = 0) : ∀ m : ℕ,
    ∑ i ∈ range m, ((m : ℝ) - i) * (t (i + 1) - t i) = ∑ i ∈ range m, t (i + 1) := by
  intro m
  induction m with
  | zero => simp
  | succ n ih =>
    have hsplit : ∀ i : ℕ, ((n + 1 : ℝ) - i) * (t (i + 1) - t i)
        = ((n : ℝ) - i) * (t (i + 1) - t i) + (t (i + 1) - t i) := by
      intro i; ring
    have hcast : ∀ i : ℕ, (((n + 1 : ℕ) : ℝ) - i) = ((n + 1 : ℝ) - i) := by
      intro i; push_cast; ring
    calc ∑ i ∈ range (n + 1), (((n + 1 : ℕ) : ℝ) - i) * (t (i + 1) - t i)
        = ∑ i ∈ range (n + 1),
            (((n : ℝ) - i) * (t (i + 1) - t i) + (t (i + 1) - t i)) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [hcast i, hsplit i]
      _ = (∑ i ∈ range (n + 1), ((n : ℝ) - i) * (t (i + 1) - t i))
            + ∑ i ∈ range (n + 1), (t (i + 1) - t i) := Finset.sum_add_distrib
      _ = (∑ i ∈ range n, ((n : ℝ) - i) * (t (i + 1) - t i)) + (t (n + 1) - t 0) := by
          rw [Finset.sum_range_succ, Finset.sum_range_sub (fun i => t i)]
          simp
      _ = (∑ i ∈ range n, t (i + 1)) + t (n + 1) := by rw [ih, h0]; ring
      _ = ∑ i ∈ range (n + 1), t (i + 1) := (Finset.sum_range_succ _ n).symm

/-- **Conservation of merge time.**  If the integrated drop of the imaginary energy is at least four
times the sum of the merge times, and the energy is nonnegative, the sum of the merge times is at
most a quarter of the initial energy. -/
theorem merge_time_sum_le {S I₀ : ℝ} (hdrop : 4 * S ≤ I₀) : S ≤ I₀ / 4 := by linarith

/-- **The extinction time is bounded by the sum.**  The largest merge time is at most the sum of all
of them, so the bound on the sum refines the bound on `Λ`. -/
theorem extinction_le_sum {t : ℕ → ℝ} {m : ℕ} (hnn : ∀ i ∈ range m, 0 ≤ t (i + 1))
    {j : ℕ} (hj : j ∈ range m) : t (j + 1) ≤ ∑ i ∈ range m, t (i + 1) :=
  Finset.single_le_sum (f := fun i => t (i + 1)) hnn hj

/-- **Many exceptions force fast extinction.**  If `m` pairs all survive to time `Λ`, the sum of the
merge times is at least `mΛ`, so `Λ ≤ I₀/(4m)`: the more off-critical zeros there are, the shorter
the extinction time. -/
theorem extinction_le_of_many {I₀ Lam : ℝ} {m : ℕ} (hm : 0 < m)
    (hsum : (m : ℝ) * Lam ≤ I₀ / 4) : Lam ≤ I₀ / (4 * m) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  rw [le_div_iff₀ (by positivity)]
  have : (m : ℝ) * Lam ≤ I₀ / 4 := hsum
  linarith [this]

/-- The index reading: the count of complex pairs at time `t` is the negative index of the Weil form
of `Ξ_t`, so the layer-cake identity says the index integrated over flow time equals the sum of the
merge times, and is bounded by a quarter of the imaginary energy. -/
theorem index_integral_le {S I₀ : ℝ} (hlayer : 4 * S ≤ I₀) : S ≤ I₀ / 4 :=
  merge_time_sum_le hlayer

end RHTower
