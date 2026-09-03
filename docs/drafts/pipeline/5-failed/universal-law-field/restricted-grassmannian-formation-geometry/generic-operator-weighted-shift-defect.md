# Generic operator-weighted-shift defect

- **ID:** ULF-GOWSD-001
- **Stage:** 5-failed
- **Verdict:** exact tautology, wrong homotopy
- **Successor:** `ULF-CCRHD-001`

## Frozen proposal

Let `K` be the normalized positive trace-one prime Stokes operator and let `w_n` be the Hodge
flux.  On `ell2(Nat;H_P)`, set

```text
A_n=(I-w_n K)^(1/2),
C(e_n tensor v)=e_(n+1) tensor A_n v.
```

Then the existing separable defect satisfies the exact identity

```text
I-C*C=directSum_n w_n K.
```

## Killing mechanism

This construction is available for every positive contraction `K` and every summable scalar
sequence `w_n`; it uses no Euler, theta, Hodge, or functional-equation law beyond inserting their
already known values.

Worse, it is not the required open history.  Since `sum_n w_n=1<infinity` and `||K||<=1`, the
infinite survival product

```text
product_(j>=n)(I-w_j K)
```

has a nonzero residual on every spectral subspace where `K` has eigenvalue in `[0,1]`.  Thus the
emitted defects do not exhaust the source state.  The formula realizes `T` as a first-step defect
but destroys the exact tail law `m_n->0` that selection needs.

Replacing `w_n` by conditional hazards `w_n/m_n` restores scalar exhaustion only when prime state
is frozen; using operator hazards instead changes the exit record away from `w_n K`.  This is the
precise reason the tensor object cannot be made genuinely coupled by functional calculus alone.

## Positive survivor

History must be generated before averaging over primes.  `ULF-CCRHD-001` does this by using the
literal pair contrast `lambda` as survival probability and only then integrating its geometric
exit histories.  The resulting rational `m_n,w_n` are consequences, not inserted weights.

