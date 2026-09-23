import GaloisForLFunctions.RHTower.FloorUnderTraceClassPerturbation

/-!
# The secular tail bound assembled from the trace

`LeakageFloorFromTrace`, `SecularTailSaturation` and `FloorUnderTraceClassPerturbation` supply the
three pieces of a `hgrow`-free route to the secular tail estimate, but they do not meet: the tail
bound of `tsum_secular_tail_le` asks for a floor at **every** index, while the trace argument
delivers one only **cofinally**, past an index produced by a Markov bound and a summable
perturbation.

This file closes that gap and assembles the chain.  A cofinal floor is enough, because the tail sum
starts past the index where the floor begins; the bound then reads

```text
∑_{j} ( ℓ_{j+M} / (d_{j+M} − μ) )²  ≤  (∑_j ℓ_{j+M}²) / (dinf − μ)² ,
```

and with `d = (1 − λ) + e` the floor is `1/4` by `exists_perturbed_leakage_floor`.  The input is a
trace bound on the free leakage plus summability of the arithmetic perturbation and Bessel
summability of the coefficients — no growth hypothesis on the amplitudes appears.
-/

namespace RHTower

/-- **Tail bound from a cofinal floor.**  The floor is only needed past the index at which the tail
begins, which is what a Markov-type argument on a trace actually produces. -/
theorem tsum_secular_tail_le_of_cofinal_floor {ℓ d : ℕ → ℝ} {μ dinf : ℝ} {M : ℕ}
    (hsat : ∀ j, M ≤ j → dinf ≤ d j) (hgap : μ < dinf)
    (hsum : Summable fun j => (ℓ j) ^ (2 : ℕ)) :
    ∑' j : ℕ, (ℓ (j + M) / (d (j + M) - μ)) ^ (2 : ℕ)
      ≤ (∑' j : ℕ, (ℓ (j + M)) ^ (2 : ℕ)) / (dinf - μ) ^ (2 : ℕ) := by
  have hd : 0 < dinf - μ := by linarith
  have hshift : Summable fun j => (ℓ (j + M)) ^ (2 : ℕ) := (summable_nat_add_iff M).mpr hsum
  have hle : ∀ j : ℕ, (ℓ (j + M) / (d (j + M) - μ)) ^ (2 : ℕ)
      ≤ (ℓ (j + M)) ^ (2 : ℕ) / (dinf - μ) ^ (2 : ℕ) := fun j =>
    sq_secular_le_of_floor (hsat (j + M) (Nat.le_add_left M j)) hgap
  have hsummable : Summable fun j : ℕ => (ℓ (j + M)) ^ (2 : ℕ) / (dinf - μ) ^ (2 : ℕ) :=
    hshift.div_const _
  refine le_trans (Summable.tsum_le_tsum hle ?_ hsummable) ?_
  · exact hsummable.of_nonneg_of_le (fun j => sq_nonneg _) hle
  · rw [← tsum_div_const]

/-- **The assembled secular tail estimate.**  From a trace bound on the free leakage, summability of
the arithmetic perturbation, and Bessel summability of the coefficients, the perturbed secular tail
is bounded past some index — with no hypothesis on the growth of the amplitudes.

This is the composition the three supporting modules were built for: `exists_perturbed_leakage_floor`
supplies the cofinal floor `1/4`, and the previous theorem consumes it. -/
theorem exists_secular_tail_bound_of_trace {ell lam e : ℕ → ℝ}
    (hnn : ∀ n, 0 ≤ lam n) (hanti : Antitone lam) {T : ℝ} (hT : 0 ≤ T)
    (htrace : ∀ n : ℕ, ∑ k ∈ Finset.range (n + 1), lam k ≤ T)
    (he : Summable e) {μ : ℝ} (hμ : μ < 1 / 4)
    (hbessel : Summable fun j => (ell j) ^ (2 : ℕ)) :
    ∃ M : ℕ,
      ∑' j : ℕ, (ell (j + M) / (((1 - lam (j + M)) + e (j + M)) - μ)) ^ (2 : ℕ)
        ≤ (∑' j : ℕ, (ell (j + M)) ^ (2 : ℕ)) / ((1 : ℝ) / 4 - μ) ^ (2 : ℕ) := by
  obtain ⟨M, hM⟩ := exists_perturbed_leakage_floor hnn hanti hT htrace he
  exact ⟨M, tsum_secular_tail_le_of_cofinal_floor
    (d := fun k => (1 - lam k) + e k) (dinf := (1 : ℝ) / 4) hM hμ hbessel⟩

/-- **The tail is small when the Bessel tail is.**  Combining with Bessel summability: the secular
tail inherits the decay of the coefficient tail, uniformly in the spectral gap.  This is the form a
source-lock comparison consumes — the tail contributes nothing in the limit. -/
theorem secular_tail_le_bessel_tail_of_trace {ell lam e : ℕ → ℝ}
    (hnn : ∀ n, 0 ≤ lam n) (hanti : Antitone lam) {T : ℝ} (hT : 0 ≤ T)
    (htrace : ∀ n : ℕ, ∑ k ∈ Finset.range (n + 1), lam k ≤ T)
    (he : Summable e) {μ : ℝ} (hμ : μ < 1 / 4)
    (hbessel : Summable fun j => (ell j) ^ (2 : ℕ)) {ε : ℝ}
    (htail : ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      (∑' j : ℕ, (ell (j + M)) ^ (2 : ℕ)) ≤ ε * ((1 : ℝ) / 4 - μ) ^ (2 : ℕ)) :
    ∃ M : ℕ,
      ∑' j : ℕ, (ell (j + M) / (((1 - lam (j + M)) + e (j + M)) - μ)) ^ (2 : ℕ) ≤ ε := by
  obtain ⟨M₀, hM₀⟩ := htail
  obtain ⟨M₁, hM₁⟩ := exists_perturbed_leakage_floor hnn hanti hT htrace he
  refine ⟨max M₀ M₁, ?_⟩
  have hgap : (0 : ℝ) < (1 : ℝ) / 4 - μ := by linarith
  have hfloor : ∀ j, max M₀ M₁ ≤ j → (1 : ℝ) / 4 ≤ (1 - lam j) + e j :=
    fun j hj => hM₁ j (le_trans (le_max_right _ _) hj)
  have hbound := tsum_secular_tail_le_of_cofinal_floor
    (d := fun k => (1 - lam k) + e k) (dinf := (1 : ℝ) / 4) hfloor hμ hbessel
  refine le_trans hbound ?_
  rw [div_le_iff₀ (by positivity)]
  exact hM₀ (max M₀ M₁) (le_max_left _ _)

end RHTower
