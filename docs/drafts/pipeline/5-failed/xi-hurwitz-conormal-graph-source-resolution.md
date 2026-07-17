# Xi--Hurwitz conormal graph source resolution — retired as a separate conjecture

- **ID:** `xi-hurwitz-conormal-graph-source-resolution`
- **Stage:** 5-failed
- **Type:** RETIRED CONJECTURE / TYPING AND REDISCOVERY AUDIT
- **Scientific status:** `[RETIRED AS SEPARATE ROUTE] [POSITIVE OPERATOR REDUCTION]`
- **Live successor:**
  `../1-in-progress/mobius-incidence-curvature-gamma-sonin-pole-divisor-transfer-rh.md`
- **Stationarity audit:**
  `../2-fully-proven/not_new_scientific_knowledge/critical-logderivative-euler-safe-depoissonized-weil-stationarity.md`
- **Construction programme:**
  `../1-in-progress/euler-gamma-conormal-markov-dilation-rh.md`

## Proposed claim

The attempted successor to the failed source-matroid card was a finite completed-Beta mapping
cone whose cofinal unbounded graph would transport

```text
A(s)=4 z_s^2 XiC(z_s)
```

to the Hurwitz FE--Schwarz seam

```text
M(s)=monoScalar(1-s)-monoScalar(conj(s)).
```

The scalar version is impossible by
`../2-fully-proven/not_new_scientific_knowledge/xi-hurwitz-scalar-comparison-codimension-no-go.md`.
The proposed higher-rank version does not define a new route either.

## Exact typing failure

The finite components currently proved in the corpus do not live on one completed carrier.

1. `VonMangoldtGammaJuliaBianchiJointGram.lean` is a positive Gram on the finite prime carrier
   `EuclideanSpace C (Fin M)`.  It contains only the source-Julia Cauchy leg and the raw
   Gamma--Bianchi prime leg.
2. `VonMangoldtGammaFactorialBetaReflection.lean` is the Beta cross-pairing of the raw Euler
   source at real displacement.  It is not the completed reflection and is eventually
   indefinite after cofinal factorial normalization.
3. `CompletedPrimeGammaResolvedMomentColligation.lean` resolves the completed moment only after
   passing to a cofinal prime moment, a continuous Gamma/Bose spectral carrier, and a two-atom
   polar carrier with negative incidence.
4. The Hurwitz monodromy character belongs to the independent unit-translation lattice.  None of
   the preceding marginal Grams contains that periodic character.

Thus there is no existing finite matrix whose ordinary mapping cone has all four boundaries.
Taking their direct sum inserts zero mixed blocks by hand; choosing nonzero mixed blocks is exactly
the missing source theorem.

## Matroid-amalgamation audit

Replacing the direct sum by a matroid amalgam does not solve the problem.

- General amalgams need not exist.
- Under generalized-parallel-connection hypotheses, existence and the relative-tensor-product
  law for matroid foundations are parent mathematics.
- The corpus already records this theory in `quantum-matroid-pro-observable-field.md` and
  `wick-contracted-differential-matroid-field.md`.
- Even a canonical amalgam controls dependence and representation moduli, not the mixed
  Hermitian cross-terms or the Loewner contraction required for RH.

Therefore “source-forced mixed circuits” remains only a finite shadow of the operator coupling;
it is not an independent conjecture.

## Proof attempt against the live inequality

The strongest current source reduction fixes `a>1/2`, puts

```text
h_a(t)=Re (Xi'/Xi)(a+i t)>0,
```

and asks for the finite Cauchy--Laplace inequality

```text
2a integral_R h_a(t) integral_0^infinity
  |sum_j c_j exp(-w_j x)/(w_j-a-it)|^2 dx dt

<= integral_R h_a(t)
  |sum_j c_j/(w_j-a-it)|^2 dt.                            (1)
```

This is equivalent to RH by the proved Euler-safe Cauchy-loss theorem.

A pointwise-in-`t` proof of `(1)` is impossible.  Fix `t_0` and two distinct nodes `w_1,w_2`.
Choose

```text
c_1=w_1-a-i t_0,
c_2=-(w_2-a-i t_0).
```

At `t=t_0` the right integrand is zero, while the inner left integral is

```text
integral_0^infinity |exp(-w_1 x)-exp(-w_2 x)|^2 dx > 0.
```

Hence boundary-density positivity cannot be applied fibrewise.  The needed sign is a global
cross-frequency coupling of the prime--Gamma density.  Separate positive marginals, a Schur
product, or a matroid amalgam cannot supply it.

## De-Poissonization collapse

The Cauchy--Laplace inequality is not itself a new source producer.  The exact stationarity
theorem proves that the safe densities form one Poisson-semigroup orbit and that tail--Laplace
subtraction removes the safe offset exactly.  After this conjugation every offset gives the same
stationary completed Weil form, with prime atoms of weight

```text
-Lambda(n)/(2 sqrt(n)).
```

Thus varying `a`, increasing the smoothing, or invoking generic Laplace--Carleson admissibility
cannot create the missing sign.  Those operations change coordinates on the same RH-complete
quadratic form.  A proof must instead construct a pre-divisor source factorization of that form,
or an independently normalized source current whose nonexpansive transport implies its
positivity.

## Positive conclusion

The pointed, polarized, integral, unbounded object sought by the original programme has one exact
load-bearing clause:

> Construct before divisor insertion the completed prime--Gamma source commutator, transport it
> nonexpansively on a source-defined graph core to the Xi boundary commutator, and retain the
> stationary Weil form as its boundary energy.

The current concrete version is the Möbius incidence-curvature Gamma--Sonin pole-to-divisor
problem.  Its weighted divisor-cut commutator and pointed Fisher connection have canonical
four-unit energy; the open theorem is closed-graph divisibility of the completed Fisher numerator,
the direct completed source commutator identity, and graph-core convergence.  Analytic,
monodromy, spectral, Hermitian, and integral matroids may certify finite relations and deletion
tests, but the RH-producing datum is this metric source transport.

## Gates

- [x] scalar comparison category ruled out
- [x] finite carrier types traced exactly
- [x] missing mixed blocks identified as the theorem rather than free data
- [x] matroid-amalgamation SOTA and corpus duplication checked
- [x] pointwise boundary-density proof falsified
- [x] safe-offset contraction de-Poissonized to the stationary Weil form
- [x] positive source-commutator successor isolated
- [ ] prove the completed source commutator identity and graph-core transport
