# Physical-cutoff alias response joining

- **ID:** `physical-cutoff-alias-response-joining`
- **Stage:** 3-formalized
- **Type:** `[LEAN-PROVED] [BRIDGE] [NOVELTY UNVERIFIED]`
- **Source:** `critical-multiplicative-compensated-cancellation-rh.md`, `(AC17)`--`(AC23)`
- **Statement:** Complementary low and high Boolean cutoff weights, applied to the same response,
  join coordinatewise to the complete positive alias probability law.

## Exact statement

Let `S` be a finite coordinate set, `theta : S -> R` take values in a commutative ring, and let
`q,H` be natural numbers.  For `T subset S`, define

```text
L_(q,H,S)(T)
 =theta_T sum_(D subset S\T, q product(T) product(D)<=H)
    (-1)^|D| theta_D,

U_(q,H,S)(T)
 =theta_T sum_(D subset S\T, H<q product(T) product(D))
    (-1)^|D| theta_D,

W_S(T)=theta_T product_(p in S\T)(1-theta_p).
```

Then, for every `T subset S`,

```text
L_(q,H,S)(T)+U_(q,H,S)(T)=W_S(T).                     (J1)
```

Moreover

```text
sum_(T subset S)L_(q,H,S)(T)=1_(q<=H),
sum_(T subset S)U_(q,H,S)(T)=1_(H<q),
sum_(T subset S)W_S(T)=1.                              (J2)
```

For every response `R_T` in a module over `R`, bilinearity gives

```text
sum_T L_T R_T+sum_T U_T R_T=sum_T W_T R_T.             (J3)
```

If `R=real`, every `0<=theta_p<=1`, and the responses lie in a real normed space with
`||R_T||<=C`, then

```text
||sum_T W_T R_T||<=C.                                  (J4)
```

The constant is sharp for a constant response.

## Complete paper proof

For fixed `T`, the inequalities in the definitions of `L_T` and `U_T` partition the powerset of
`S\T`.  Adding the two sums therefore removes the cutoff.  Finite inclusion--exclusion gives

```text
sum_(D subset S\T)(-1)^|D|theta_D
 =product_(p in S\T)(1-theta_p),
```

which proves `(J1)`.

For the first equality in `(J2)`, expand over disjoint pairs `(T,D)` and put `M=T union D`.
For every nonempty `M`, the coefficient of `theta_M` is

```text
sum_(D subset M)(-1)^|D|=0.
```

Only `M=empty` remains, and it passes the cutoff exactly when `q<=H`.  The high-cutoff identity
follows identically or by subtracting from the complete mass one.  The last identity in `(J2)` is
the finite product expansion of `product_p(theta_p+(1-theta_p))=1`.

Equation `(J3)` follows by multiplying `(J1)` by the common response and summing.  Under the real
root-density hypotheses, every factor in `W_T` is nonnegative; the triangle inequality and `(J2)`
give `(J4)`.  A constant response realizes equality.

All sums are finite.  No analytic, asymptotic, or unproved input is used.

## Sign-failure discriminator

The theorem does not claim that `L_T` or `U_T` is positive.  If the cutoff retains exactly the
empty subset and singletons, then its inner signed sum is

```text
1-sum_(p in S)theta_p,
```

which is negative whenever the displayed sum exceeds one even if every local survival factor is
strictly positive.  This is why the joining in `(J1)`, rather than separate total variation, is
the invariant statement.

## Significance and limit

`[POSITIVE SALVAGE]` The theorem proves that physical splitting can manufacture negative Jordan
mass without changing the joined response operator.  It corrects the representation of the open
problem and applies to arbitrary finite Boolean alias systems.

`[BRIDGE]` The algebra is finite inclusion--exclusion and probability normalization; it is not
claimed as new scientific knowledge.  It does not estimate the genuine global correlation
`(AC25)`.

## Lean certificate

The exact finite theorem is formalized in
`GaloisForLFunctions/RHTower/PhysicalCutoffAliasResponseJoining.lean`:

- `truncatedAliasSum_add_highSum` proves the inner low/high partition;
- `truncatedAliasSum_rank_le_one_sign_failure` proves that a cutoff half can be negative while
  every complete local survival factor is positive;
- `physicalCutoffAliasLowWeight_add_highWeight` proves `(J1)` coordinatewise;
- `sum_physicalCutoffAliasLowWeight`, `sum_physicalCutoffAliasHighWeight`, and
  `sum_completeAliasWeight` prove `(J2)`;
- `physicalCutoffAliasResponse_join` proves `(J3)` over an arbitrary module;
- `quadraticCongruencePhysicalCutoffAliasResponse_join_norm_le` proves `(J4)` for the exact
  quadratic root densities.

The leaf module and narrow Lake target build.  The axiom audit for every declaration above reports
only `propext`, `Classical.choice`, and `Quot.sound`.

## Gates

- [x] Exact claim and hostile sign-failure test.
- [x] Dependency-closed paper proof.
- [x] Exact Lean theorem and axiom gate.
- [x] Moved to `3-formalized` after verification.
