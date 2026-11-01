# A fixed three-prime core at every p-adic resolution

- **Stage:** 3-formalized
- **Type:** THEOREM; paper proof, Lean proof, direct source check, and axiom audits complete.
- **Parent:** [principal-unit affine index](principal-unit-affine-state-index.md).

Let `p,q,r` be distinct primes, `R=ℤ[1/(pqr)]`, and

```text
H_n = {q^a r^b : a,b∈ℤ, |q^a r^b-1|_p < 1/(n+1)}.
```

For every principal resolution:

1. `log H_n` is dense in `ℝ` for every `n`.
2. Restricting `ratCorr` to `H_n` preserves both its negative index and its
   mass-zero negative index, and approximates every global correlation value.
3. On `{x↦ux+b : u∈H_n, b∈R}`, the actual `weilPadicState p c`, `c>0`,
   has index `κ(ratCorr)+1`.
4. A fixed positive oscillation of `ratCorr` persists in all `H_n`. Thus
   p-adic discontinuity already occurs on the fixed two-prime slope group;
   unrestricted denominators are not needed for the obstruction.

## Proof mechanism

Choose `k` with `p^(-k)<1/(n+1)`. The finite unit group modulo `p^k` gives
`M>0` with `q^M≡r^M≡1 mod p^k`. Thus `H_n` contains the `M`-th powers
of the two-prime group. Its logarithms are dense by the existing
`TowerCoupling.dense_range_logPos_twoPrimeUnits`, followed by multiplication
by `M`. Dense orbit-kernel restriction and nonvanishing difference multipliers
give the two index identities. Continuity in the real logarithmic variable
gives value approximation.

Choose a global correlation value different from `ratCorr(1)`, which the
existing nonzero mixed difference supplies. Approximation within half that
distance gives the uniform oscillation at every resolution.

The affine gluing witness uses only slopes in `H_n` and translations `p^(-N)`;
all lie in `R`. The proved subgroup gluing lemma needs only the powers of one
translation whose place norm exceeds one.

## Boundary

Two unrestricted primes suffice for this density mechanism. If the chosen
prime set includes `p`, imposing p-adic unit norm removes its exponent:
`ℤ[1/p]` leaves only slope `1`, and `ℤ[1/(pq)]` leaves a cyclic slope group.
This is a density boundary, not a claim that every cyclic restriction loses
spectral index. Other-prime conditions are not silently imposed.

Unbounded p-adic translations suffice for this proof; their necessity is not
established. Realizations with p-adically bounded translations require a separate
analysis of the constant spectral direction.

## Lean declarations and validation

Module: `AdelicKreinGeometry/ThreePrimesCarryTheWholeAffineState.lean`.

- `exists_twoPrimePrincipalUnit_log_near`;
- `polarIndex_ratCorr_twoPrimePrincipalUnits`;
- `negIndex_ratCorr_twoPrimePrincipalUnits`;
- `exists_twoPrimePrincipalUnit_ratCorr_near`;
- `exists_uniform_twoPrime_padic_ratCorr_oscillation`;
- `not_padic_continuous_ratCorr_twoPrimeUnits`;
- `negIndex_weilPadicState_threePrimePrincipalAffine`.

The affine proof uses `add_one_le_negIndex_glueAt_subgroup_of_translation_powers`
in `TheGluingFormulaAtEveryPlace`. Both final source checks pass. Final namespaced
transitive audits use only `propext`, `Classical.choice`, `Quot.sound`.
Umbrella import is wired; no umbrella build was run.
