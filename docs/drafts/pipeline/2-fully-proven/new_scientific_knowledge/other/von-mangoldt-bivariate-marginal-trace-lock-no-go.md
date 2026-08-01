# Von Mangoldt bivariate marginal trace-lock no-go

- **ID:** `von-mangoldt-bivariate-marginal-trace-lock-no-go`
- **Stage:** 2 — fully proved on paper
- **Parent:** `SR-41`; `von-mangoldt-successor-transport-inertia-law.md`
- **Type:** `[UNIVERSAL MARGINAL LAW] [SOURCE-SPECIFIC CLASS NO-GO]`
- **Scientific status:** `[PROVED] [UNCONDITIONAL] [NOVELTY UNVERIFIED] [NOT RH]`

## 1. Frontier

`SR-42` excludes positive and every fixed-index Pontryagin realization of the `SR-40` jet
current. It leaves an infinite-index bivariate prime--jet Krein completion. Standard finite
bivariate realization puts a kernel `C` on `P × J` and recovers two marginals by coordinate
partial traces:

```text
jetMarginal(C)(i,j)    = sum_p C((p,i),(p,j)),
sourceMarginal(C)(p,q) = sum_i C((p,i),(q,i)).          (1)
```

The question is whether arbitrary indefinite coupling can realize the fixed `SR-38` source
marginal together with every finite `SR-40` jet section.

## 2. Universal marginal trace lock

For every finite product kernel over any additive commutative coefficient monoid,

```text
trace(jetMarginal(C))
 = sum_i sum_p C((p,i),(p,i))
 = sum_p sum_i C((p,i),(p,i))
 = trace(sourceMarginal(C)).                            (2)
```

This is finite-sum commutation. No positivity, Hermitian symmetry, nondegeneracy, or index bound
is used. In particular, every off-diagonal mixed block is invisible to `(2)`.

## 3. Exact von Mangoldt trace flux

Write

```text
rho_M(q)
 = sum_(n=2)^(M+1) [Lambda(n)/n]
     (log(n+1)^q-log(n)^q),

R_(M,N)(i,j)=rho_M(i+j+2).                              (3)
```

For `q>0`, every summand of `rho_M(q)` is nonnegative:

```text
Lambda(n)/n >= 0,
0 <= log n < log(n+1),
log(n)^q <= log(n+1)^q.
```

If `M>0`, the `n=2` summand is strictly positive because
`Lambda(2)/2>0` and `log(2)^q<log(3)^q`. Hence

```text
rho_M(q)>0.                                             (4)
```

Taking diagonal sums in `(3)` and splitting off the last coordinate gives the exact law

```text
trace(R_(M,N+1))
 = trace(R_(M,N)) + rho_M(2N+2)
 > trace(R_(M,N)).                                      (5)
```

This is a source identity, not an estimate.

## 4. Bivariate marginal no-go

Fix any finite source type `P` and any matrix `B : Matrix P P R`. Suppose kernels `C_N` and
`C_(N+1)` satisfy

```text
jetMarginal(C_N)       = R_(M,N),
sourceMarginal(C_N)    = B,
jetMarginal(C_(N+1))   = R_(M,N+1),
sourceMarginal(C_(N+1))= B.                             (6)
```

Applying `(2)` twice gives

```text
trace(R_(M,N))=trace(B)=trace(R_(M,N+1)),
```

contradicting `(5)`. Therefore no such pair exists.

Since `B` is arbitrary, specialize it to any finite pullback

```text
B(p,q)=gammaOddJacobiPrimeCoherentResidualKernel(prime(p),prime(q)).
```

This proves exact `SR-40`/`SR-38` incompatibility for ordinary coordinate partial traces.

## 5. Scope and positive survivor

The theorem excludes more than Hilbert or fixed-index completions: it excludes arbitrary real
bivariate kernels, arbitrary negative index, and arbitrary mixed entries inside the partial-trace
class. It does not exclude a singular connector whose "compression" is not a trace-preserving
partial trace.

Any surviving `SR-41` object must therefore do at least one of the following:

1. change its source marginal with jet cutoff;
2. use a weighted/renormalized non-trace-preserving reader;
3. carry the exact flux `rho_M(2N+2)` in an explicit boundary channel.

The third option is the sharp positive survivor: the missing cyclic reader is not merely an
Euler-label decoder. It must absorb the exact strictly positive jet-opening trace flux. Mixed
blocks alone cannot pay it.

## 6. Corpus and novelty audit

Corpus search found no prior application of finite marginal trace conservation to `SR-40`,
`SR-38`, or `SR-41`. Equation `(2)` itself is elementary finite-dimensional partial-trace
algebra and is not claimed as externally novel. The source-specific strict flux `(5)`, its
composition with `(2)`, and resulting Suzuki completion-class obstruction are the provisional
scientific contribution.

## 7. Lean status

Lean proofs are implemented in:

```text
formal/GaloisForLFunctions/HTGeometry/BivariateMarginalTraceLock.lean
formal/GaloisForLFunctions/RHTower/VonMangoldtBivariateMarginalTraceLock.lean
```

Principal declarations:

```text
HTGeometry.trace_bivariateJetMarginal_eq_trace_bivariateSourceMarginal
RHTower.finiteVonMangoldtSuccessorRelativeMoment_pos
RHTower.trace_finiteVonMangoldtSuccessorPrincipalRelativeMatrix_succ
RHTower.trace_finiteVonMangoldtSuccessorPrincipalRelativeMatrix_strictMono
RHTower.not_exists_two_bivariateMarginals_finiteVonMangoldtSuccessor
RHTower.not_exists_two_bivariateMarginals_finiteVonMangoldtSuccessor_gammaOddJacobi
```
