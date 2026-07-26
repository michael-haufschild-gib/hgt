import Mathlib.Analysis.PSeries
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Tactic

/-!
# Divergent reciprocal sums for at most linearly growing ordinates

A positive sequence that grows at most linearly has divergent reciprocal sum: comparison with the
harmonic series gives

```
γ k ≤ c (k+1)   eventually   ⟹   ∑_{k<N} 1/γ k → ∞.
```

This is the step that converts a *counting* lower bound on an increasing sequence of ordinates —
`at least a·T terms below T`, equivalently `γ k ≤ (k+1)/a` — into divergence of `∑ 1/γ k`.  Both the
`Tendsto` form and the `¬ Summable` form are recorded, together with the eventually-weaker version
in which only a tail of the sequence obeys the linear bound.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- Divergence of the shifted harmonic series with an arbitrary positive factor. -/
theorem tendsto_sum_const_div_natSucc_atTop {c : ℝ} (hc : 0 < c) :
    Tendsto (fun N => ∑ k ∈ Finset.range N, c * (1 / ((k : ℝ) + 1))) atTop atTop := by
  have hbase := Real.tendsto_sum_range_one_div_nat_succ_atTop
  have hmul := hbase.const_mul_atTop hc
  exact hmul.congr fun N => Finset.mul_sum _ _ _

/-- **Harmonic comparison.**  A positive sequence bounded by a linear function of its index has
divergent reciprocal partial sums. -/
theorem tendsto_sum_inv_atTop_of_le_linear {γ : ℕ → ℝ} {c : ℝ} (hc : 0 < c)
    (hpos : ∀ k, 0 < γ k) (hle : ∀ᶠ k in atTop, γ k ≤ c * ((k : ℝ) + 1)) :
    Tendsto (fun N => ∑ k ∈ Finset.range N, (γ k)⁻¹) atTop atTop := by
  obtain ⟨K, hK⟩ := eventually_atTop.mp hle
  set b : ℕ → ℝ := fun k => c⁻¹ * (1 / ((k : ℝ) + 1)) with hb
  have hbdiv : Tendsto (fun N => ∑ k ∈ Finset.range N, b k) atTop atTop :=
    tendsto_sum_const_div_natSucc_atTop (by positivity)
  have hcmp : ∀ k, K ≤ k → b k ≤ (γ k)⁻¹ := by
    intro k hk
    have hγ := hpos k
    have hlin := hK k hk
    have hden : (0 : ℝ) < c * ((k : ℝ) + 1) := by positivity
    rw [hb]
    have hinv : (c * ((k : ℝ) + 1))⁻¹ ≤ (γ k)⁻¹ := by
      rw [inv_le_inv₀ hden hγ]
      exact hlin
    calc c⁻¹ * (1 / ((k : ℝ) + 1)) = (c * ((k : ℝ) + 1))⁻¹ := by
          rw [mul_inv, one_div]
      _ ≤ (γ k)⁻¹ := hinv
  have hsplit : ∀ N, K ≤ N →
      (∑ k ∈ Finset.range N, b k) + (∑ k ∈ Finset.range K, ((γ k)⁻¹ - b k))
        ≤ ∑ k ∈ Finset.range N, (γ k)⁻¹ := by
    intro N hN
    have hA : (∑ k ∈ Finset.range K, (γ k)⁻¹) + ∑ k ∈ Finset.Ico K N, (γ k)⁻¹
        = ∑ k ∈ Finset.range N, (γ k)⁻¹ :=
      Finset.sum_range_add_sum_Ico (fun k => (γ k)⁻¹) hN
    have hB : (∑ k ∈ Finset.range K, b k) + ∑ k ∈ Finset.Ico K N, b k
        = ∑ k ∈ Finset.range N, b k := Finset.sum_range_add_sum_Ico b hN
    have htail : ∑ k ∈ Finset.Ico K N, b k ≤ ∑ k ∈ Finset.Ico K N, (γ k)⁻¹ :=
      Finset.sum_le_sum fun k hk => hcmp k (Finset.mem_Ico.mp hk).1
    rw [Finset.sum_sub_distrib, ← hA, ← hB]
    linarith
  refine tendsto_atTop_mono' atTop ?_
    (tendsto_atTop_add_const_right atTop (∑ k ∈ Finset.range K, ((γ k)⁻¹ - b k)) hbdiv)
  filter_upwards [eventually_ge_atTop K] with N hN
  exact hsplit N hN

/-- The reciprocals of an at most linearly growing positive sequence are not summable. -/
theorem not_summable_inv_of_le_linear {γ : ℕ → ℝ} {c : ℝ} (hc : 0 < c)
    (hpos : ∀ k, 0 < γ k) (hle : ∀ᶠ k in atTop, γ k ≤ c * ((k : ℝ) + 1)) :
    ¬ Summable fun k => (γ k)⁻¹ := by
  intro hsum
  have hnonneg : ∀ k, 0 ≤ (γ k)⁻¹ := fun k => inv_nonneg.mpr (hpos k).le
  exact (not_summable_iff_tendsto_nat_atTop_of_nonneg hnonneg).mpr
    (tendsto_sum_inv_atTop_of_le_linear hc hpos hle) hsum

/-- **Counting form.**  If at least `a T` terms of a monotone positive sequence lie below `T` for
every large `T`, then the reciprocal sum diverges.  The hypothesis is recorded in its index form
`γ k ≤ (k+1)/a`, which is what a counting lower bound supplies for a monotone sequence. -/
theorem tendsto_sum_inv_atTop_of_counting {γ : ℕ → ℝ} {a : ℝ} (ha : 0 < a)
    (hpos : ∀ k, 0 < γ k) (hcount : ∀ᶠ k in atTop, γ k ≤ ((k : ℝ) + 1) / a) :
    Tendsto (fun N => ∑ k ∈ Finset.range N, (γ k)⁻¹) atTop atTop := by
  refine tendsto_sum_inv_atTop_of_le_linear (c := a⁻¹) (by positivity) hpos ?_
  filter_upwards [hcount] with k hk
  calc γ k ≤ ((k : ℝ) + 1) / a := hk
    _ = a⁻¹ * ((k : ℝ) + 1) := by rw [div_eq_inv_mul]

end GaloisForLFunctions.HTGeometry
