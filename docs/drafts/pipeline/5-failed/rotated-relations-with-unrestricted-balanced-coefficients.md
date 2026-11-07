# Rotated relations need nonvanishing coefficients

- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Statement:** The unrestricted balanced-coefficient rotated identity admits every entire function; the usable local statement requires a nonzero coefficient at the tested zero.

## Exact issue

For any `F,q`, put `a=b=F` and `T(z)=F(qz)+F(conj(q)z)`. Then `TF=aF(q·)+bF(conj(q)·)` and `|a|=|b|`. Entire `F` gives entire coefficients. Thus this identity alone cannot constrain zeros, even when `F(0)=a(0)=b(0)=1`.

## Positive survivor

For complex `a,b,u,v`, `abs(|a||u|−|b||v|)≤|au+bv|`. Consequently balanced coefficients in a relation at a zero either both vanish or force `|u|=|v|`. Conversely equal moduli admit unit-modulus coefficients with `au+bv=0`. This gives the exact nonvanishing boundary and a quantitative error threshold for approximate relations.

The explicit normalized polynomial `F(z)=(z²−2z+2)/2`, with `a=b=F`, has a zero at `1+i`. At rotation `q=i`, one rotated value is nonzero and the other zero. Thus normalization at the origin does not repair the criterion.

The rotation factor has oriented difference
`|1−qu|²−|1−conj(q)u|²=4 Im(q) Im(u)`.
The strict direction cannot hold for both `q` and `conj(q)`.

## Scope

This refutes only the unrestricted-coefficient criterion. Nonvanishing at the tested zero is the exact local replacement. No arithmetic construction of such coefficients, infinite-product extremal theorem, or RH implication is proved here. The requested breakthrough remains open.

## Lean verification

Module: `RigidArithmeticOfCuts/RotatedRelationsNeedNonvanishingCoefficients.lean`.

- `self_coefficient_rotated_relation`: universal identity.
- `exists_normalized_entire_vacuous_rotated_relation`: normalized entire counterexample.
- `balanced_modulus_gap_le`: quantitative residual bound.
- `balanced_relation_zero_or_modulus_eq`: exact local alternative.
- `exists_unit_balanced_cancellation_iff`: converse with unit coefficients.
- `rotated_factor_norm_sq_sub`: oriented factor identity.

Direct `lake --old env lean` check passed. Axiom audits of the counterexample and four survivor laws contain only `propext`, `Classical.choice`, and `Quot.sound`. The module is imported by its programme umbrella and `MainTheorems`; umbrellas were not compiled.
