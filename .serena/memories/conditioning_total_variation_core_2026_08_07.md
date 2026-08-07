# Conditioning displaces a probability measure by exactly the complementary mass (2026-08-07)

Module `HTGeometry/ConditioningTotalVariation.lean`, `lake build` green (1702 jobs), axioms
`[propext, Classical.choice, Quot.sound]`, in the HTGeometry umbrella.

## Statement

For a probability measure `μ` and a measurable `B` with `μ B ≠ 0`:

- `abs_toReal_cond_sub_le` — for EVERY set `A`, measurable or not,
  `|((μ[|B]) A).toReal - (μ A).toReal| ≤ 1 - (μ B).toReal`.
- `abs_toReal_cond_sub_self` — testing `B` attains it.

So the sup defining total-variation distance is exactly `1 - μ B`. No Jordan decomposition, no TV
definition, no measurability of the test set.

## Proof shape (worth reusing)

With `b = (μ B).toReal`, `x = (μ (B ∩ A)).toReal`, `y = (μ A).toReal`:
`A ⊆ (B ∩ A) ∪ Bᶜ` gives `y ≤ x + (1 - b)`; `μ (B ∩ A) ≤ μ B` gives `x ≤ b`. Then
`x/b - y ≤ x/b - x = x(1-b)/b ≤ 1-b` and `x/b - y ≥ x - y ≥ -(1-b)`. Pure real algebra after that.

Avoid: `ENNReal.toReal_sub_of_le` plus `prob_compl_eq_one_sub` chains — messy. Use
`measure_add_measure_compl hB` and `congrArg ENNReal.toReal` to get `b + (μ Bᶜ).toReal = 1`.

## Why it was formalized

It is the abstract core of the stage-2 card
`docs/drafts/pipeline/2-fully-proven/prime-valuation-conditioning-normalization-amplification-no-go.md`
(the source-normalization no-go for the prime sieve): normalized conditional states are displaced by
the COMPLEMENTARY mass, which does not telescope, while unnormalized restrictions are displaced by
the MASS DIFFERENCE, which does. That is exactly why summability of the unnormalized defect `a_P/p`
cannot control the normalized conormal blow-up.

## Still on paper

Everything using the product measure `μ₀ = ⨂_p μ_p` on `∏_p ℕ₀` — the cylinder events `A_P` and
identities (1), (2), (3) for `ν_P` — needs an infinite product measure over the primes, which the
corpus does not have. The card remains at stage 2; only its mechanism is Lean.
