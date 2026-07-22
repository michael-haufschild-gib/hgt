# Möbius antidiagonal one-prime tent law and two-prime sign wall

- **ID:** `MERTENS-PRIME-TENT-001`
- **Stage:** 2-fully-proven / needs-audit
- **Type:** THEOREM (paper)
- **Source:** `mobius-additive-frontier-research-ledger.md` · `OPEN-SOURCE-001`
- **Statement:** Removing one Euler prime gives an exact nonnegative tent kernel for every signed
  Mertens antidiagonal; removing any two primes necessarily creates a negative transfer lobe.

## Goal

Classify exactly what local Euler-factor removal can contribute to the one-sided signed Mertens
antidiagonal source

```text
U(N) = sum_(a+b=N) M(a)M(b).
```

The theorem supplies a positive one-prime representation and proves a sharp obstruction to
iterating that positivity. It does **not** prove the `N^(2+epsilon)` upper law: after this local
classification, the remaining open core is global signed cancellation among the prime-free seeds.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem, targeted `lake build` green, axiom/lint audit PASS
- [ ] 3 → 4  publication-ready: standalone theorem, proof, Lean certificate, priority audit

## Definitions

Write `mu` for the Möbius function, `M(n)=sum_(m<=n) mu(m)`, and

```text
w_N(k) = max(N-k+1,0).
```

For a prime `p`, define the `p`-free seed

```text
mu^(p)(r) = mu(r) if p does not divide r, and 0 otherwise.
```

For positive integers `r,s`, define the one-prime transfer kernel

```text
K_(p,N)(r,s)
  = w_N(r+s) - w_N(pr+s) - w_N(r+ps) + w_N(p(r+s)).       (1)
```

For nonnegative integers `A,R,S`, define the discrete tent

```text
Tent(A;R,S)
  = A - (A-R)_+ - (A-S)_+ + (A-R-S)_+.                    (2)
```

Here every truncated subtraction in (2) is taken in the nonnegative integers.

## Theorem A — one-prime tent law `[PROVED HERE]`

For every prime `p`, every `n>=0`, and every `N>=0`,

```text
M(n) = sum_(p∤r, r<=n<pr) mu(r),                           (3)

U(N) = sum_(p∤r, p∤s) mu(r)mu(s) K_(p,N)(r,s).             (4)
```

If `T=N+1`, `A=(T-r-s)_+`, `R=(p-1)r`, and `S=(p-1)s`, then

```text
K_(p,N)(r,s) = Tent(A;R,S)
             = #{(i,j): 0<=i<R, 0<=j<S, i+j=A-1}.          (5)
```

Consequently:

```text
K_(p,N)(r,s) >= 0,                                         (6)
K_(p,N)(r,s) > 0 iff r+s<=N and N+2<=p(r+s),               (7)
K_(p,N)(r,s) <= min((p-1)r,(p-1)s),                        (8)
K_(2,N)(r,s) <= K_(p,N)(r,s).                              (9)
```

Thus prime `2` gives the pointwise smallest, and hence sharpest, member of the entire positive
one-prime transfer family.

### Proof

Because `p` is prime, unique factorization gives the coefficientwise Euler-factor identity

```text
mu(n) = mu^(p)(n) - 1_(p|n) mu^(p)(n/p).                  (10)
```

Indeed, if `p∤n`, the second term vanishes. If `n=pr` with `p∤r`, multiplicativity gives
`mu(pr)=-mu(r)`; if `p^2|n`, both sides vanish. Summing (10) through `n` gives

```text
M(n) = sum_(p∤r,r<=n) mu(r) - sum_(p∤r,pr<=n) mu(r),
```

which is (3). Equivalently, coefficientwise as a formal power series,

```text
sum_(n>=0) M(n)z^n
  = sum_(p∤r) mu(r) (z^r-z^(pr))/(1-z)
  = sum_(p∤r) mu(r) sum_(a=r)^(pr-1) z^a.                 (11)
```

Squaring (11) and extracting the coefficient of `z^N` proves (4). Expanding the coefficient of
the two interval polynomials by inclusion-exclusion gives (1).

Now translate an exponent pair by `(r,s)`. The coefficient in question counts pairs

```text
(i,j),  0<=i<(p-1)r,  0<=j<(p-1)s,  i+j=N-r-s.
```

This is exactly (5), either by direct counting or by inclusion-exclusion on the two upper bounds.
Nonnegativity (6) and the upper bound (8) are immediate. Such a pair exists exactly when
`0<=N-r-s<((p-1)r+(p-1)s)`, which is (7). Finally, increasing `p` enlarges both intervals in
(11), so every coefficient of their product is nondecreasing; this proves (9). ∎

## Theorem B — universal two-prime sign wall `[PROVED HERE]`

Let `2<=p<q` (primality is not needed for the algebraic sign statement) and set

```text
Q_(p,q)(z) = (z-z^p-z^q+z^(pq))/(1-z).
```

Then `Q_(p,q)(z)^2` has a strictly negative coefficient. More precisely, with

```text
k = max(q+1,2p-1),
```

```text
[z^k] Q_(p,q)(z)^2 < 0.                                  (12)
```

For the first two primes, `[z^4]Q_(2,3)(z)^2=-2`. Therefore no simultaneous removal of two
distinct Euler primes has an entrywise nonnegative Mertens transfer kernel, even at seed pair
`r=s=1`.

### Proof

The quotient is the finite signed interval polynomial

```text
Q_(p,q)(z)
  = (z+...+z^(p-1)) - (z^q+...+z^(pq-1)).                 (13)
```

Let `P=[1,p-1]` and `R=[q,pq-1]`. In the coefficient of degree `k`, the positive-positive
convolution is absent because `k>2p-2`, and the negative-negative convolution is absent because
`k<2q`. Both inequalities follow from the definition of `k` and `p<q`. The cross convolution is
nonempty: `k-q` lies in `[1,p-1]` when `k=2p-1`, while `1` is an admissible positive exponent when
`k=q+1`. Hence the degree-`k` coefficient consists only of one or more cross terms, each occurring
twice and each carrying sign `-1`. This proves (12). Taking `(p,q,k)=(2,3,4)` leaves the two ordered
cross pairs `(1,3)` and `(3,1)`, giving `-2`. ∎

## Exact frontier consequence

Theorems A and B classify local-factor positivity:

1. one removed Euler prime always yields a nonnegative cardinality kernel;
2. prime `2` is pointwise optimal inside that class;
3. any second removed prime necessarily introduces a negative lobe;
4. therefore the desired upper law cannot come from iterating a coefficientwise-positive
   local-factor comparison.

The remaining RH-bearing obligation is to use, rather than discard, signed multi-prime
cancellation in

```text
sum_(r,s odd) mu(r)mu(s) Tent(N+1-r-s;r,s).
```

Absolute values, positive Gram completion, or monotone enlargement of the tent returns the cubic
barrier and does not prove `OPEN-SOURCE-001`.

## Novelty and literature audit

- Exact-phrase and conceptual searches found no statement of (3)--(12) as a signed-Mertens
  antidiagonal transfer classification.
- Björner's squarefree Euler-characteristic complex and later topological Mertens interpretations
  concern one-dimensional Mertens sums, not this additive antidiagonal kernel.
- Existing shifted-convolution and additive Möbius literature does not supply the global upper
  cancellation left after Theorem B.
- Negative search does not establish priority. Novelty status remains **suspended pending
  specialist, MathSciNet, and Zentralblatt review**.

## No-go closure

- **Exact killing theorem/mechanism:** Theorem B: every attempted second local Euler removal creates
  a strictly negative transfer coefficient.
- **Strongest positive survivor:** Theorem A: exact nonnegative one-prime tent representation,
  sharp support shell, and pointwise optimality of prime `2`.
- **New insight:** local Euler stripping has positivity depth exactly one. Further progress must
  control global signed prime interactions rather than add another positive local comparison.
- **Status:** dependency-closed paper proof; Lean coefficient/window connector and kernel/sign-wall
  core audited; flattened double-sum identity (4) remains paper-level; external priority audit open.

## Lean status

`formal/GaloisForLFunctions/RHTower/MobiusMertensPrimeRemovalTentLaw.lean` proves:

- Möbius coefficient removal at every prime;
- the exact prime-free interval formula for each Mertens partial sum;
- equality of the existing signed antidiagonal/RH source with the prime-window convolution;
- tent equality, nonnegativity, support, size bounds, and monotonicity;
- prime-2 pointwise minimality;
- the universal two-factor negative lobe and the exact `(2,3)` value `-2`.

Direct `lake env lean`, formal lint, standard-axiom audit, and targeted cached `lake build` pass.
The stage remains 2 until the flattened finite double-sum statement (4) itself is a named Lean
theorem and the external novelty audit closes.

## Log

- 2026-07-22 — proved one-prime tent law, shell support, prime-2 optimality, and universal
  two-prime negative lobe; moved directly to 2-fully-proven/needs-audit.
- 2026-07-22 — formalized coefficient removal, Mertens windows, RH-source connector, tent core,
  minimality, and sign wall; targeted build and axiom/lint audits passed.
