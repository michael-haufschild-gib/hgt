# Route L: complete prime-layer compensation by nearby semiprimes

- **ID:** L-ALL-PRIME-SEMIPRIME-LOCAL-MATCHING
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Lean status:** Fully formalized, unconditionally; see [l-all-prime-semiprime-local-matching-formalized.md](l-all-prime-semiprime-local-matching-formalized.md) for the theorem map (cell counts (2), (4)–(7), matching (1), two-layer pairing (3), exact derivative energy).

## Theorem

Fix a real `B>0`. For every sufficiently large integer `R`, there is an injection

```text
phi_R : {primes p : R < p <= 2R}
          -> {squarefree semiprimes m : R < m <= 2R}
```

such that `phi_R(p)=q*r` for some `q in {2,3,5}` and a prime `r>5`, and

```text
|phi_R(p)-p| <= 2R/(log R)^B.
```

Thus the pairs have their **literal** Möbius signs `mu(p)=-1` and `mu(phi_R(p))=+1`; no coefficient or prime is selected away. Put `f_x(t)=x² exp(-xt)` and

```text
||g||_delta² = Gamma(5+delta)^(-1)
  * integral_0^infinity t^(4+delta)|g(t)|² dt,
S_R(t) = sum_(R<p<=2R, p prime) (-f_p(t)+f_(phi_R(p))(t)).
```

For `0<=delta<=1`, with a constant independent of `R` and `delta`,

```text
||S_R||_delta² <<_B R^(1-delta)/(log R)^(2B+2).          (1)
```

All atoms of `S_R` occur exactly once in the full integer-cutoff Möbius source at every cutoff `N>=2R`. Consequently the *entire prime layer* in each dyadic band has an explicit, source-literal semiprime compensator with saving beyond every prescribed fixed logarithmic power. The theorem does not bound the full source: unused semiprimes and all higher-factor atoms remain.

## Proof

The corpus proves `pi(x)=Li(x)+O(x exp(-c sqrt(log x)))` for some `c>0`. Fix `B>0`, let `J=floor((log R)^B)`, and partition `(R,2R]` into `J` consecutive half-open real cells of common width `h=R/J`. For large `R`, `J>=1`, and `h<=2R/(log R)^B`. Uniformly for a cell `(u,v]` and any fixed `q in {1,2,3,5}`, its endpoints divided by `q` lie in `[R/5,2R]`. The prime-counting theorem and `log t=log R+O(1)` there give

```text
pi(v/q)-pi(u/q) = (1/q+o(1)) h/log R,              (2)
```

uniformly over **all** cells. Indeed the error from the two endpoints is `O(R exp(-c' sqrt(log R)))`, which divided by `h/log R` is `O((log R)^(B+1) exp(-c' sqrt(log R)))=o(1)`. The logarithmic-integral density contributes only relative `O(1/log R)`.

The demand in a cell is its `q=1` count, `(1+o(1))h/log R`. The supply of semiprimes `q*r` in the **same** cell, with `q=2,3,5`, is

```text
(1/2+1/3+1/5+o(1)) h/log R
  = (31/30+o(1)) h/log R.
```

For large `R`, `r>5`; unique prime factorization makes the three candidate sets disjoint and every candidate squarefree. The strict `1/30` density surplus therefore supplies a finite injection from each cell's primes to its candidate semiprimes. Combining these disjoint cell injections gives `phi_R`, and any matched pair differs by at most `h`.

The Gamma integral and `u=xt` give

```text
||partial_x f_x||_delta² = C_delta*x^(-3-delta),
C_delta = Gamma(5+delta)^(-1)
  * integral_0^infinity u^(4+delta)(2-u)² exp(-2u) du.
```

`C_delta` is continuous and bounded on `[0,1]`: for `u<=1` the power is bounded by `u^4`, for `u>=1` by `u^5`, and the exponential dominates both. The fundamental theorem of calculus in the Gamma Hilbert space then yields, for `x,y in [R,2R]`,

```text
||f_x-f_y||_delta <= C*|x-y|*R^(-(3+delta)/2).
```

The prime-counting theorem also gives `#{p in (R,2R]} << R/log R`. Apply the triangle inequality to the matched dipoles and `|phi_R(p)-p|<=h`:

```text
||S_R||_delta << (R/log R)*h*R^(-(3+delta)/2)
                 <<_B R^((1-delta)/2)/(log R)^(B+1).
```

Squaring proves (1). The construction uses the exact source coefficients and no numerical computation.

## Second-layer theorem: all primes and semiprimes compensated together

The same cells admit a *disjoint* source-literal pairing of every prime and every
squarefree semiprime in `(R,2R]` to an opposite-sign atom in that band, with
displacement at most `2R/(log R)^B`. Prime targets are semiprimes as above; each
semiprime not already used as a prime target is sent to a squarefree triprime
`q*r*s`, where `q in {2,3,5}` and `r,s>5` are distinct primes. Writing `T_R`
for the sum of these signed dipoles, the uniform energy bound is

```text
||T_R||_delta² <<_B R^(1-delta)*(log log R)²/(log R)^(2B+2),
                 0 <= delta <= 1.                         (3)
```

Here is the missing local count, including its square-root boundary. For any
cell `(u,v] subset (R,2R]` of length `h=R/floor((log R)^B)`, let `A_2(u,v)`
count squarefree semiprimes `p*r` with `p<r`. Those with `p<=sqrt u` are counted
exactly by

```text
sum_(p<=sqrt u, p prime) [pi(v/p)-pi(u/p)].              (4)
```

The strong prime-counting error, uniformly for `p<=sqrt u`, turns (4) into

```text
h * sum_(p<=sqrt u) 1/(p*log(R/p))
  + O(R*exp(-c' sqrt(log R))*log log R).                  (5)
```

Since `log(R/p)>=log R/2+O(1)`, the elementary inequality for reciprocal
logarithms and `sum_(p<=sqrt(2R)) log p/p << log R` turn the first term into
`h/log R * (sum_(p<=sqrt u)1/p+O(1))`. The corpus's prime reciprocal estimate
`RHTower.Sieve.mertensS_le` / `le_mertensS` gives
`sum_(p<=sqrt u)1/p=log log R+O(1)`, uniformly in `u`.

The omitted semiprimes have `sqrt u<p<=sqrt v`. The same prime-counting error
gives at most
`O(h/(sqrt R*log R)+sqrt R*exp(-c'' sqrt(log R)))` choices for `p`;
for each `p`, at most `h/sqrt R+1` integers `r` can satisfy `u<pr<=v`.
Their product is `O(h/log R)`, uniformly over the cells, since `h<=R` and
`h=R/(log R)^(B+o(1))`. Therefore

```text
A_2(u,v) = h/log R * (log log R+O_B(1)).                 (6)
```

For each `q in {2,3,5}`, apply (6) to `(u/q,v/q]`. Excluding semiprimes
with a factor in `{2,3,5}` removes only `O_B(h/log R)` candidates, by the
prime-counting theorem applied to the remaining prime factor. The resulting
sets of triprimes `q*r*s` are disjoint: their unique factor `<=5` is `q`.
Their total supply in one cell is

```text
(31/30) * h/log R * (log log R+O_B(1)),                (7)
```

strictly exceeding the complete semiprime demand (6) for large `R`.
First match primes to semiprimes by the preceding theorem. Then match only
the semiprimes left unused, cell by cell, to the triprime supply (7). The
targets have different factor counts, so the two matchings are disjoint;
every pair has the literal opposite Möbius signs. Finally the number of
paired sources is `O_B(R log log R/log R)`. The same Gamma derivative bound
used for (1), followed by the triangle inequality, proves (3).

This compensates the **complete first two prime-factor layers** of the
integer-cutoff source. It does not bound the full source: unused triprimes
and the bulk of higher-factor squarefree integers remain, together with
their cross-covariance.

## Remaining arithmetic producer

The two-layer pairing still does not give the bounded-return cubic energy required by [Route L's formal receiver](../l-cofinal-cubic-source-criterion.md). The full source contains the unused triprimes and higher squarefree layers; their cross-covariance with `T_R` may dominate (3). A source-exhaustive hierarchy would need a total Gamma-norm residual bounded along arbitrarily large cutoffs for positive `delta` approaching zero. Fixed low-factor layers have a `31/30` local supply surplus; the unresolved arithmetic lies in the growing bulk of prime-factor counts, where this fixed-fibre argument alone supplies no all-layer matching.
