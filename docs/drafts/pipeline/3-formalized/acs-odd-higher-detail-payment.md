# Odd higher powers: joint mixed and detail payment

- **ID:** acs-odd-higher-detail-payment
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** ACS complete-cell effectivity; ArithmeticIndexDescent square-plus-odd source
- **Statement:** The original Gamma energy pays every detail-dependent contribution of all odd prime powers of exponent at least three, jointly with the full even-power source, after one fixed finite detail head and the ordinary mean are removed.

## Goal

Discharge the odd higher-power detail diagonal left outside
`SquaresAndOddHigherMixedPowersHaveUniformFiniteIndex`. Retain the literal
coarse source explicitly. This is a payment theorem for an existing unpaid
block, not a claim of full Weil positivity or closure of ACS.

## Exact target

Write `F = g + h`, where `g` is the complete-pair average and `h` its balanced
detail. Let `P_odd` be the literal prime source over odd exponents at least
three, and let `S₂` be the existing full even-power source. Prove that there
exists a fixed integer `A ≥ 1`, independent of horizon and coefficients, such
that vanishing detail coordinates below `A` implies

```
Γ(F) - S₂(F) - (P_odd(F) - P_odd(g)) + (1/2)(∫F)²
  ≥ (γ_E/2) ∫F².
```

Consequently the exact displayed form without its mean correction has
negative dimension at most `A + 1` on every finite complete-cell family.
No first-prime contribution, coarse odd contribution, actual Weil pole or
archimedean mass term is silently included in this assertion.

## Proof mechanism

1. Integer translation of a complete-pair average is orthogonal to every
   balanced target detail (`inner_shift_coarseSection_haarSection`).
2. Hence the complete odd source minus its coarse source equals the sum of
   `weight(m) * Re ⟨T_m h, F⟩`. This includes the mixed and detail diagonal
   together; their separation would introduce an unnecessary correction.
3. The original complete-profile Gamma energy pays this translated detail
   pairing with factor `1 / cellGammaWeight A`, uniformly in the integer lag.
4. The actual critical coefficients over all exponents at least three are
   summable. Restriction to odd exponents preserves the bound.
5. Choose `A` so that this charge fits inside the positive Gamma share
   retained by the full even-power estimate. Its ordinary-mean correction
   and positive Euler-constant mass floor remain unchanged.
6. On a negative subspace, the finite detail head and ordinary mean are
   injective readouts; dimension is at most `A + 1`.

## Gates

- [x] Exact original source and unpaid block identified in corpus.
- [x] Dependency-closed paper proof recorded.
- [x] Literal source identity and joint payment formalized.
- [x] Finite negative-dimension theorem formalized.
- [x] Direct `lake --old env lean` final check; umbrella import added.

## Lean declarations and validation

Module:
`GaloisForLFunctions/ArithmeticIndexDescent/OddHigherPrimePowersPayTheirWholeDetailBlock.lean`.

- `oddHigherPrimePowerSource_eq_complete_integrals` and
  `oddHigherPrimePowerSource_eq_coarse_integrals`: literal physical sources.
- `oddHigherPrimePowerSource_sub_coarse`: exact triangular identity.
- `oddHigherPrimePowerSource_sub_coarse_eq_mixed_add_detail`: identifies the
  additional pure-detail block explicitly.
- `abs_oddHigherPrimePower_detail_tail_le_gamma`: original-Gamma payment.
- `exists_oddHigherPrimePower_joint_gamma_small_tail`: uniform tail payment.
- `exists_squareOddHigherRefinement_finite_head_coercivity`: joint full-even
  and odd-detail coercivity, retaining the positive mass floor.
- `exists_uniform_squareOddHigherRefinement_negative_dimension`: uniform
  negative dimension at most `A+1` on arbitrary finite complete-cell families.

Validation: direct command exited 0 with no diagnostics:

```
lake --old env lean GaloisForLFunctions/ArithmeticIndexDescent/OddHigherPrimePowersPayTheirWholeDetailBlock.lean
```

The module is imported by `ArithmeticIndexDescent.lean`; the umbrella was not
compiled. No axiom-check command was added or run for the new module.

## Remaining ACS core

The first-prime source over all primes, the coarse odd higher source, finite
heads, coarse error, actual poles and archimedean mass still need joint
control. Uniform finite index of the complete Weil form, let alone index
zero, is not proved by this target.

## Complete paper proof [PROVED HERE]

For `p` prime and `j ≥ 0`, set `m = p^(j+3)` and
`w(p,j) = 2 log(p) / sqrt(m)`. Let `ε(p,j)` be one when `j+3` is odd and
zero otherwise. The existing critical-weight summability theorem proves
`Σ_(p,j) w(p,j) < ∞`; all these weights are nonnegative. Put
`C = Σ_(p,j) ε(p,j) w(p,j)`. In the half-line `L²` space let `T_m` be the
actual right shift by `log(m)`, a contraction. Define

```
P_odd(v) = Σ_(p,j) ε(p,j) w(p,j) Re ⟨T_m v, v⟩.
```

This series is absolutely convergent: each summand in absolute value is at
most `ε(p,j) w(p,j) ‖v‖²`. Existing representative identities identify it
with the original real-profile correlations, with no modified coefficient.

For every complete horizon `X`, write `g = coarseSection(q,X)` and
`h = haarSection(d,X)`. The exact integer-incidence identity gives
`Re ⟨T_m g,h⟩ = 0` for every `m ≥ 2`. Expanding the inner product therefore
gives, term by term,

```
Re ⟨T_m(g+h),g+h⟩ - Re ⟨T_m g,g⟩ = Re ⟨T_m h,g+h⟩.
```

Absolute convergence permits subtraction and summation, so

```
P_odd(g+h) - P_odd(g)
  = Σ_(p,j) ε(p,j) w(p,j) Re ⟨T_m h,g+h⟩.                 (1)
```

If `d(a)=0` for `a<A`, then `h` equals its high-detail projection. The
translated-detail Gamma theorem, applied at `-log(m)`, gives

```
|Re ⟨T_m h,g+h⟩| ≤ Γ(F) / cellGammaWeight(A),
```

where `F` is the original complete real profile. Thus (1) yields

```
|P_odd(g+h) - P_odd(g)| ≤ C Γ(F) / cellGammaWeight(A).    (2)
```

The full even-power theorem supplies a fixed `δ>0`, independent of `q,d,X`,
such that

```
δ Γ(F) + (γ_E/2) ∫F² ≤ Γ(F) - S₂(F) + (1/2)(∫F)².     (3)
```

Choose an integer `A > exp(C/δ)`. Then `A≥1` and
`cellGammaWeight(A) ≥ log(A) > C/δ`, so (2) is at most `δΓ(F)`.
Subtracting the signed source difference from (3) proves the exact target.
The same choice works for all horizons and all coefficients.

Finally, on any finite family of complete profiles, map coefficient vectors
to their first `A` detail coordinates and their ordinary mean. If a vector
is in this map's kernel, the target inequality and `γ_E>0` show that its
uncorrected displayed quadratic form is nonnegative. The map is therefore
injective on every strictly negative subspace, whose real dimension is at
most the target dimension `A+1`. This proves the asserted uniform bound.
All inputs are existing unconditional source theorems; no RH or index
assumption is used.

## Log

- 2026-10-28 — Corpus inspection found a triangular source identity that
  includes the omitted odd higher detail diagonal in the same Gamma payment.
  No web search, novelty checks or axiom checks requested or performed.
- 2026-10-28 — Exact source identities, joint payment and negative-dimension
  theorem passed the direct Lean check. ACS remains open; no full-form index
  bound or RH conclusion is asserted.
