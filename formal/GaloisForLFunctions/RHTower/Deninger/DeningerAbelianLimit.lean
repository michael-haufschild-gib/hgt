import GaloisForLFunctions.RHTower.Deninger.DeningerAbelAverage

/-!
# The Abelian limit theorem for the Abel weight

A convergent sequence is reproduced by its Abel averages.  The weight is a probability weight, so
the tail past the convergence threshold contributes at most `ε`; the head is a finite sum whose
every term vanishes as the exponent goes to zero.

`b_n → S`  implies  `∑_n b_n w_σ(n) → S`  as  `σ ↓ 0`.

* `deningerAbelian_tendsto` : **the Abelian limit theorem.**
-/

namespace RHTower

open Filter Topology

noncomputable section

/-- A convergent real sequence is bounded in absolute value. -/
theorem deningerBounded_of_tendsto {b : ℕ → ℝ} {S : ℝ} (hb : Tendsto b atTop (𝓝 S)) :
    ∃ C : ℝ, ∀ n, |b n| ≤ C := by
  have habs : Tendsto (fun n => |b n|) atTop (𝓝 |S|) := hb.abs
  obtain ⟨C, hC⟩ := habs.bddAbove_range
  exact ⟨C, fun n => hC ⟨n, rfl⟩⟩

/-- **The Abelian limit theorem.**  The Abel averages of a convergent sequence converge to the
same limit. -/
theorem deningerAbelian_tendsto {b : ℕ → ℝ} {S : ℝ} (hb : Tendsto b atTop (𝓝 S)) :
    Tendsto (fun σ : ℝ => ∑' n : ℕ, b n * deningerAbelWeight σ n) (𝓝[>] 0) (𝓝 S) := by
  obtain ⟨C, hC⟩ := deningerBounded_of_tendsto hb
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hhalf : (0 : ℝ) < ε / 2 := by linarith
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hb (ε / 2) hhalf
  have htail : ∀ n, N ≤ n → |b n - S| ≤ ε / 2 := by
    intro n hn
    have := hN n hn
    rw [Real.dist_eq] at this
    linarith
  have hhead : Tendsto
      (fun σ : ℝ => ∑ n ∈ Finset.range N, (b n - S) * deningerAbelWeight σ n)
      (𝓝[>] 0) (𝓝 0) := by
    have hterm : ∀ n ∈ Finset.range N,
        Tendsto (fun σ : ℝ => (b n - S) * deningerAbelWeight σ n) (𝓝[>] 0) (𝓝 0) := by
      intro n _
      have := (deningerAbelWeight_tendsto_zero_within n).const_mul (b n - S)
      rwa [mul_zero] at this
    have := tendsto_finsetSum (Finset.range N) hterm
    rwa [Finset.sum_const_zero] at this
  have hheadeps := (Metric.tendsto_nhds.mp hhead) (ε / 2) hhalf
  filter_upwards [hheadeps, self_mem_nhdsWithin] with σ hσhead hσmem
  have hσ : (0 : ℝ) < σ := hσmem
  have hCS : ∀ n, |b n - S| ≤ C + |S| := by
    intro n
    calc |b n - S| ≤ |b n| + |S| := abs_sub _ _
      _ ≤ C + |S| := by linarith [hC n]
  have hsummable : Summable fun n : ℕ => (b n - S) * deningerAbelWeight σ n :=
    deningerAbelAverage_summable hCS hσ
  have hsplit : (∑' n : ℕ, (b n - S) * deningerAbelWeight σ n)
      = (∑ n ∈ Finset.range N, (b n - S) * deningerAbelWeight σ n)
        + ∑' n : ℕ, (b (n + N) - S) * deningerAbelWeight σ (n + N) :=
    (hsummable.sum_add_tsum_nat_add N).symm
  have htb := deningerAbelAverage_tail_bound hσ S (le_of_lt hhalf) htail
  have hsub := deningerAbelAverage_sub hC hσ S
  rw [Real.dist_eq, hsub, hsplit]
  have hh : |∑ n ∈ Finset.range N, (b n - S) * deningerAbelWeight σ n| < ε / 2 := by
    have := hσhead
    rwa [Real.dist_eq, sub_zero] at this
  calc |(∑ n ∈ Finset.range N, (b n - S) * deningerAbelWeight σ n)
        + ∑' n : ℕ, (b (n + N) - S) * deningerAbelWeight σ (n + N)|
      ≤ |∑ n ∈ Finset.range N, (b n - S) * deningerAbelWeight σ n|
        + |∑' n : ℕ, (b (n + N) - S) * deningerAbelWeight σ (n + N)| := abs_add_le _ _
    _ < ε / 2 + ε / 2 := by linarith
    _ = ε := by ring

end

end RHTower
