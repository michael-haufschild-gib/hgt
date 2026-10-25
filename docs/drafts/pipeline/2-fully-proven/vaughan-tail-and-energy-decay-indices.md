# Vaughan tail and empty-leg decay indices

- **ID:** vaughan-tail-and-energy-decay-indices
- **Stage:** 2-fully-proven
- **Type:** CLAIM (Lean verification pending)
- **Verification:** UNPROVED. The argument below is not a certified result until its Lean proof and transitive axiom audit pass; checked component lemmas are identified separately.
- **Source:** ../1-in-progress/q-i-selective-square-root-band.md
- **Statement:** For every fixed `ε>0`, the optimal power-saving index of `N^ε(ρ-A_N)` is `1-Θ`, where `Θ=zetaZeroAbscissa`; the square empty-leg energy has four times that index in the cutoff variable.

## Exact invariant

Let `F_ε(N)=ρ-A_N`, and let `S_ε` consist of the real numbers `η` with
`0≤η<1` for which some constant `C≥0` bounds

`|F_ε(N)|≤C N^(-ε-η)` for every `N≥1`.

The exact law is `sup S_ε=1-Θ`. It asserts a threshold, without deciding
whether a bound holds at the threshold. It would not prove that the threshold is positive.

For the normalized square empty-leg energy

`E_ε(N)=G^c_33(N²;N,N)/(N²)^(1-2ε)`,

the proved two-sided quartic comparison transfers each tail exponent `η` into energy
exponent `4η`, and conversely an energy exponent `δ` into tail exponent `δ/4`.
Thus the corresponding supremum is `4(1-Θ)` in `N`, or `2(1-Θ)` in
the horizon `T=N²`. This sharpens the existential fixed-strip equivalence.

## Dependency-closed proof

The all-positive-damping extension of finite Abel inversion proves that a tail bound of exponent `η∈(0,1)`
gives `M(N)=O(N^(1-η))`. The read compact-interval power lemma bounds
the inverse-weight increment by `(1+ε)2^ε n^ε` for every `ε≥0`; this
removes the earlier upper restriction on damping. See
[the extension proof](all-positive-vaughan-tail-power-rates.md), whose Lean check is pending.
A pointwise bound `|M(N)|≤C N^β`, `β≥0`, gives
`Σ_(k≤X)|M(k)|≤C(X+1)^(1+β)`. The read corpus theorem
`zetaZeroAbscissa_le_of_sum_norm_mertens_le` therefore gives `Θ≤β`.
Its proof uses the exact Möbius Laplace transform and the obstruction at a zeta zero;
no strip is a premise of that theorem.

The read `mobiusMertens_subpower_zetaZeroAbscissa` supplies
`|M(N)|≤C(N+1)^β` for every `β>Θ`, unconditionally. For `N≥1`, the change from
`N+1` to `N` costs at most `2^β`. These two inputs prove the upper and lower cuts:

- A tail rate gives the upper bound `η≤1-Θ`.
- For `0≤η<1-Θ`, choose `Θ<β<1-η`; the Mertens bound at `β` and the checked Abel
  tail estimate give a stronger tail exponent `1-β>η`.
- The absolute tail bound puts zero in `S_ε`. Existing bounds on `Θ` close the
  degenerate case `Θ=1` and bound both sets.

Consequently `S_ε⊆[0,1-Θ]`, and every `η∈[0,1-Θ)` belongs to `S_ε`.
If `Θ=1`, zero is the only member. Otherwise the open interval approaches its upper
endpoint, proving the supremum identity. This also proves that the index is independent
of the chosen `ε>0`.

More strongly, the full rate set is independent of positive damping, including
whether its supremum is attained. For `0<η<1`, finite Abel inversion gives the
exact implication from a tail rate to `M(N)=O(N^(1-η))`. Conversely that Mertens
bound transfers back to the exact tail exponent `η` at every positive damping;
neither direction loses an exponent. Zero belongs to every rate set. Thus the
sets agree, without deciding whether the shared endpoint belongs to them.

Define the energy-rate set with `0≤δ<4` and a uniform bound `E_ε(N)≤C N^(-δ)`.
The checked quartic inequalities and `Z>0` prove exact membership equivalence
`δ is an energy rate ↔ δ/4 is a tail rate`. The same upper/lower-cut argument gives
its supremum `4(1-Θ)`. The restrictions `η<1` and `δ<4` lose no possible better rate:
any bound beyond either endpoint could be weakened to `η∈(1/2,1)` or `δ∈(2,4)`,
contradicting `Θ≥1/2`.

Define horizon rates by the actual bound `E_ε(N)≤C(N²)^(-γ)` and `0≤γ<2`.
The identity `(N²)^(-γ)=N^(-2γ)` identifies this set with half the cutoff-energy
rate set. Its supremum is `2(1-Θ)`. Both energy-rate sets inherit the full
damping independence of the tail-rate set.

## Corollaries and limits

- Every tail rate satisfies `η≤1/2`; every energy rate in `N` satisfies `δ≤2`.
- The tail index is positive exactly when `Θ<1`.
- RH is equivalent to tail index `1/2`, energy index `2`, and horizon index `1`.
- Equivalently, RH requires all strict tail gains below `1/2`, or all strict energy
  gains below `2`. No assertion is made at either endpoint.

This is a Vaughan specialization of existing exponent laws and the proved quartic
identity. Source checks close the paper proof. Broad discovery searches were partial;
the follow-up found many general exponent laws and the existing reciprocal-tail strip
equivalence, without an exact indexed empty-leg theorem. No external novelty claim is made.
Thirty quantitative-transfer, rate-set, supremum, damping-independence, fixed-strip,
and RH targets are drafted in `/tmp/QIVaughanDecayIndexTools.lean`, uncompiled.
The draft includes unrestricted upper-rate exclusions, exact rate-set independence,
actual horizon-rate sets, and all-strict-exponent RH formulations. Three explicit
`mem_pmPronicVaughanTailPowerRates_iff_bound`,
`mem_pmPronicVaughanSquareEnergyPowerRates_iff_bound`, and
`mem_pmPronicVaughanHorizonEnergyPowerRates_iff_bound` drafts identify the formal
rate sets with all nonnegative exponents satisfying the actual bounds. Their
proofs derive the harmless upper caps from the unrestricted exclusion theorems.
`pmPronicVaughanTailPowerRates_eq_singleton_zero_of_abscissa_eq_one` formalizes
the stated degenerate-case singleton classification. These four additional
targets remain unchecked. None of these index identities gives a positive lower
bound for `1-Θ`; full Q-I remains open.
