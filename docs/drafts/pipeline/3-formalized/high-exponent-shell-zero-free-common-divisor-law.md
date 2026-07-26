# High-exponent shells have a zero-free multiplier and the full Xi divisor

- **ID:** `high-exponent-shell-zero-free-common-divisor-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper), `[RH SOURCE THEOREM]`
- **Scientific status:** `[PROVED] [PROOF VALUE ONLY] [NOVELTY NOT EVALUATED BY REQUEST]`
- **Parents:**
  - `../3-formalized/not_new_scientific_knowledge/mfree-moebius-ladder-carrier-bridge.md`
  - `mobius-incidence-clock-gini-fisher-four-unit-law.md`
  - `squarefree-fixed-current-right-half-ward-localization.md`
  - `new_scientific_knowledge/scalar-ht-persistent-clock-character-law.md`
  - `new_scientific_knowledge/charged-scalar-core-fixed-current-torsor.md`

## Statement

For `m>=1`, let

```text
a_m(n)=1_((m+1)-free)(n)-1_(m-free)(n).                 (1)
```

Thus `a_m(n)=1` exactly when the largest exponent in the prime factorization of `n` is `m`.
The supports of `a_m` and `a_k` are disjoint when `m!=k`.  On `Re s>1`, its Dirichlet series is

```text
S_m(s)=sum_(n>=1)a_m(n)n^(-s)
      =zeta(s)H_m(s),
H_m(s)=1/zeta((m+1)s)-1/zeta(ms).                       (2)
```

For every integer `m>=12`, `H_m` is holomorphic and zero-free on

```text
Re s>1/2.                                                (3)
```

Consequently, if

```text
c_infinity(s)=s(s-1)pi^(-s/2)Gamma(s/2)/2,
X_m(s)=c_infinity(s)S_m(s)=Xi(s)H_m(s),                 (4)
```

then `X_m` and `Xi` have exactly the same strict right-half divisor, with the same
multiplicities.  Equivalently,

```text
-2X_m'(s)/X_m(s)
 =-2Xi'(s)/Xi(s)-2H_m'(s)/H_m(s),                       (5)
```

and the second term in `(5)` is holomorphic on `Re s>1/2`.  Every high-exponent shell therefore
has the same strict anti-causal Hardy profile `ell_E` as the completed zeta source.

Each shell is also a positive four-unit source.  For `sigma=1+epsilon`, define

```text
P_(m,sigma)(n)=a_m(n)n^(-sigma)/S_m(sigma),
H=log n,
kappa_(m,sigma,t)=[Pi_(m,sigma),2Q_t-I].                (6)
```

Then, for every fixed `m>=12`,

```text
epsilon log n  ->  Exp(1)             in W_1,
epsilon E|H-H'| -> 1,
epsilon integral_0^infinity
  ||kappa_(m,sigma,t)||_HS^2 dt ->4.                    (7)
```

The arithmetic supports in `(6)` are pairwise disjoint across `m`, so the corresponding
incidence kernels occupy mutually orthogonal Hilbert--Schmidt blocks before any fixed-current
quotient is taken.

## Zero-free proof

The denominators in `H_m` are nonzero on `Re s>1/2`, since `Re(ms)>1` for `m>=12`.  It is therefore
enough to prove that

```text
D_m(s)=zeta(ms)-zeta((m+1)s)                             (8)
```

does not vanish there.  Write `sigma=Re s>1/2` and split off the `n=2` term:

```text
D_m(s)
 =2^(-ms)(1-2^(-s))
  +sum_(n>=3)n^(-ms)(1-n^(-s)).                         (9)
```

The leading term satisfies

```text
|2^(-ms)(1-2^(-s))|
 >=2^(-m sigma)(1-2^(-sigma)).                          (10)
```

After division by `2^(-m sigma)`, the tail is at most

```text
sum_(n>=3)(2/n)^(m sigma)(1+n^(-sigma))
 <=64 sum_(n>=3)(n^(-6)+n^(-13/2)).                     (11)
```

Here `m sigma>6`.  Since

```text
sum_(n>=3)n^(-6)
 <=3^(-6)+integral_3^infinity x^(-6)dx
 =8/3645
```

and `n^(-13/2)<=3^(-1/2)n^(-6)`, the right side of `(11)` is strictly less than

```text
64(1+1/sqrt(3))8/3645
 <4096/18225
 <1/4
 <1-1/sqrt(2)
 <1-2^(-sigma).                                         (12)
```

The tail in `(9)` is therefore strictly smaller than the leading term.  This proves `(3)` by
Rouche's elementary one-term domination, pointwise throughout the half-plane.

## Critical four-unit proof

The real number

```text
H_m(1)=1/zeta(m+1)-1/zeta(m)                             (13)
```

is positive.  Hence `(2)` has a simple pole at `s=1` with positive residue `H_m(1)`.  Uniformly
for `u` in compact subsets of `Re u>-1`,

```text
S_m(1+epsilon(1+u))/S_m(1+epsilon) ->1/(1+u).           (14)
```

This is the Laplace transform of `Exp(1)`.  Differentiating the Laurent expansion at the real
axis gives convergence of the first scaled moment to `1`; Laplace convergence plus first-moment
convergence gives `W_1` convergence.  Applying it to two independent copies yields the middle
limit in `(7)`.  The projection-commutator identity

```text
||[Pi,2Q_t-I]||_HS^2
 =8 P(H<=t)P(H>t)                                       (15)
```

and `integral P(H<=t)P(H>t)dt=E|H-H'|/2` give the last limit.

## Prime-two asymptotic and HT meaning

The same domination is uniform on every closed half-plane `Re s>=1/2+delta`.  As `m->infinity`,

```text
H_m(s)
 =2^(-ms)(1-2^(-s))(1+o_delta(1)).                      (16)
```

Thus a high shell is source-locally a large clock translation of the odd-integer zeta source,
while its completed logarithmic current retains the entire Xi divisor.  The affine translation
`2^(-ms)` becomes only the boundary constant `m log 2` after taking a logarithmic derivative and
does not alter the strict anti-causal profile.

This is a concrete fixed-current phenomenon: infinitely many disjoint positive clock sectors can
have asymptotically one-prime local geometry while carrying one common global HT divisor current.
Meromorphic continuation is therefore discontinuous in the coefficient/clock topology that makes
the shell sectors orthogonal.

## Attack on the anti-causal Ward estimate

The theorem supplies infinitely many orthogonal four-unit inputs with the same desired output
`ell_E`.  This gives a sharp anti-theatre test for a proposed Ward codifferential.

If one bounded linear row operator on the orthogonal shell sum sent every limiting shell curvature
to the same vector `ell_E`, then for `N` shells its value on their normalized sum would grow like
`sqrt(N) ell_E`; boundedness would force `ell_E=0`, hence RH.  However the identical argument
already applies to the nonzero incoming pole vector `2e^(-t/2)`.  Therefore a row operator that
collapses every shell clock to the common pole cannot be bounded unconditionally.

**Strengthened no-go.**  Artificially adjoining the shell label and then taking a scalar
codiagonal is not an RH proof.  The weighted-codiagonal dichotomy in
`not_new_scientific_knowledge/high-shell-codiagonal-closability-dichotomy.md` proves more than
unboundedness: a scalar shell row is closable exactly when its weights are square-summable, in
which case it is already bounded.  The unit-weight row which erases the common fixed-current label
is therefore nonclosable.  It cannot be repaired by declaring an unspecified closed domain.

**Positive successor.**  A viable anti-causal Ward construction must keep the arithmetic shell
label through the pole cancellation and take the fixed-current quotient only on an
operator-valued multiplication graph.  A scalar unbounded row is excluded even as a closable
operator.  Equation `(3)` guarantees that no shell-specific right-half divisor is introduced for
`m>=12`; equation `(16)` gives a prime-two-dominated cofinal family on which a uniform graph
estimate can be attacked.  Failure of such uniformity is now localized to the fixed-current
quotient, not to Gamma completion, source energy, shell orthogonality, or an auxiliary divisor.

## Proof verdict

The theorem produces an infinite, pairwise-disjoint positive test family whose completed currents
have no auxiliary strict right-half divisor.  It does not prove RH: the tempting bounded
codiagonal is already impossible for the known nonzero incoming Euler-pole vector.  The surviving
use is the prime-two-dominated cofinal test family for the single closed fixed-current graph.

## Gates

- [x] exact shell indicator and Dirichlet series
- [x] disjoint arithmetic supports
- [x] zero-free multiplier on `Re s>1/2` for every `m>=12`
- [x] exact common strict right-half divisor with `Xi`
- [x] critical `Exp(1)` clock and four-unit incidence energy
- [x] prime-two asymptotic on closed strict half-planes
- [x] bounded-codiagonal shortcut rejected using the incoming pole
- [x] scalar codiagonal strengthened from unbounded to nonclosable
- [x] proof contribution evaluated without a novelty gate
- [ ] construct a shell-label-preserving closed Ward graph
- [ ] prove a uniform relative estimate through pole cancellation
- [ ] RH
