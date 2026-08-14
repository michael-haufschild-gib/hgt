# The constrained finite-aperture radial prime charge has a universal limit

- **ID:** `constrained-prolate-full-radial-prime-charge-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Scientific status:** `[PROVED HERE] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`,
  pending independent formula-level audit
- **Parent results:** `constrained-prolate-radial-leakage-divisibility-spectrum.md`,
  `ccm-exact-radial-nonstationary-sector-bound.md`, and
  `docs/drafts/pipeline/3-formalized/not_new_scientific_knowledge/ccm/ccm-prime-shift-radial-index-separation-law.md`, and
  `ccm-exact-high-radial-first-row-bv-bound.md`
- **Statement:** The finite-aperture raw exterior von Mangoldt charge of the constrained CCM
  source, divided by its first leakage scale, converges to
  `-16/(11*pi) sum_(k>=2)(log k/k)arcsin(1/k)`.

## Setup

Let

```text
G_lambda(j,k)
 =inner(H_(lambda,j),H_(lambda,k))_(L2(ds)),

H_(lambda,k)(s)
 =sqrt(lambda*e^s)q_lambda(k*lambda*e^s),

d_1(lambda)=1-chi_4(lambda)^2.                                  (1)
```

Define the exact truncated-divisor weight and radial prime charge by

```text
a_lambda(k)=sum_(q|k; 2<=q<=lambda^2)Lambda(q),

PPrime_lambda^ap
 =-2 sum_(k>=2)a_lambda(k)sum_(j>=1)G_lambda(j,k).               (2)
```

This is the divisor-reindexed form of the prime shifts visible to the exact logarithmic aperture.
It satisfies

```text
0<=a_lambda(k)<=log k,
k<=lambda^2 -> a_lambda(k)=log k.                               (3)
```

The exact aperture theorem removes prime shifts `q>lambda^2`; it does not remove radial indices
`k=q*n>lambda^2`, because `n` remains unbounded.

## Diagonal term

The radial leakage/divisibility theorem proves

```text
G_lambda(k,k)/d_1(lambda)
 ->8/(11*pi*k)arcsin(1/k),                                      (4)

G_lambda(k,k)/d_1(lambda)<=C/k^2.                               (5)
```

Dominated convergence therefore gives

```text
-2/d_1(lambda) sum_(k>=2)a_lambda(k)G_lambda(k,k)

 ->-16/(11*pi)
    sum_(k>=2)log(k)/k*arcsin(1/k).                              (6)
```

The series converges absolutely because `arcsin(1/k)=O(1/k)`.

## Off-diagonal terms

For `j,k>=2`, `j!=k`, the exact phase-preserving exterior theorem gives

```text
sum_(k>=2)a_lambda(k)
 sum_(j>=2;j!=k)|G_lambda(j,k)|
 =O(d_1(lambda)/c),
c=2*pi*lambda^2.                                                (7)
```

For the low first row, the exact finite-index theorem gives

```text
sum_(2<=k<=lambda^2)a_lambda(k)|G_lambda(1,k)|
 =O(d_1(lambda)/sqrt(c)+d_1(lambda)*log(c)^2/c).                 (8)
```

The high radial first row is

```text
E_lambda^high
 =sum_(k>lambda^2)a_lambda(k)G_lambda(1,k).                      (8a)
```

The high-radial BV theorem proves `E_lambda^high=o(d_1)` absolutely. The finite prime-shift cutoff
alone does not prove it; the exterior phase estimate is load-bearing.

## Universal radial prime law

Combining `(6)`--`(8)` with the high-radial theorem proves

```text
lim_(lambda->infinity) PPrime_lambda^ap/d_1(lambda)
 =-16/(11*pi)
   sum_(k>=2)log(k)/k*arcsin(1/k).                               (9)
```

This is the full finite-aperture raw radial prime charge, including the infinite radial multiplier.

Equivalently, before the divisor reindexing its unsigned response constant is

```text
8/(11*pi) sum_(q>=2)Lambda(q)/q
  sum_(j>=1)arcsin(1/(q*j))/j.                                  (9a)
```

Indeed `k=q*j` turns the coefficient into
`k^(-1)sum_(q|k)Lambda(q)=log(k)/k`. Thus `(9)` is the candidate finite-aperture radial-resonance constant conjectured
independently in `ccm-radial-von-mangoldt-resonance-law.md`; that card's exact Poisson-bracket and
finite-aperture formulation remains the correct interface for the completed Weil form.

## Positive CCM consequence

The arithmetic divisibility carrier survives completion through one explicit scalar at the first
leakage scale. The finite-archimedean Gamma boundary law shows that this scalar cannot be generated
by the one-direction archimedean coefficient field: it comes from the cofinal arithmetic carrier.

The remaining closed-Weil calculation must preserve `(9)` while adding, in the same graph-domain
limit,

```text
the Poisson central correction
+ the archimedean logarithmic form
+ the interior/normalization terms required by the exact CCM operator.              (10)
```

Equation `(9)` supplies the prime term of that incidence law. It does not determine the sign of
the complete Weil form by itself.

## Novelty and significance verdict

### Novelty: provisional pass

The parent literature supplies radial PSWF asymptotics, prolate concentration, and the CCM
prime/archimedean framework separately. Formula-level searches for `arcsin(1/k) log k prolate`,
`arcsin(1/k) von Mangoldt`, and `prolate radial prime dilation arcsine spectrum` found no statement
of `(9)`. Connes--Moscovici's prolate spectral work concerns the self-adjoint prolate operator and
zeta-like ultraviolet spectra, not this leakage-normalized cofinal finite-aperture radial Gram
limit.

### Significance: provisional pass, 7/10

The theorem evaluates the cofinal finite-prime-aperture component, including its infinite radial
multiplier, and removes all off-diagonal radial uncertainty. It is not an RH criterion: the
central and archimedean terms must still be assembled in the closed Weil form and compared with
the true spectral gap.

The result remains candidate-new until an independent audit verifies the boundary normalization,
the finite-aperture Olver-envelope transfer, and the exact CCM sign convention.

## References

- T. M. Dunster, *Asymptotics of Prolate Spheroidal Wave Functions*, arXiv:1601.00699.
- A. Connes, H. Moscovici, *Prolate Spheroidal Operator and Zeta*, arXiv:2112.05500.
- A. Connes, C. Consani, H. Moscovici, *Zeta Spectral Triples*, arXiv:2511.22755.
- NIST Digital Library of Mathematical Functions, Chapter 10.

## Lean formalization status

The exact arithmetic part is formalized unconditionally.  In
`GaloisForLFunctions.RHTower.ConstrainedProlateExteriorWeil`,
`constrainedProlate_sum_vonMangoldt_divisors_ge_two` proves the divisor collapse
`sum_(q|k,q>=2) Lambda(q)=log k`; the shifted prime summands are nonnegative and summable, and
`constrainedProlatePrimeConstant` is strictly negative.  In
`GaloisForLFunctions.RHTower.ArcsineZetaDerivativeSpectrum`, the positive diagonal eigenvalues
`16 log(k) arcsin(1/k)/(11*pi*k)` are strictly positive and summable, and their total mass is exactly
the negative of `constrainedProlatePrimeConstant`.

The **double-sum Dirichlet divisor reindexing identity (9a)** is now formalized unconditionally in
`GaloisForLFunctions.RHTower.ConstrainedProlatePrimeShiftDoubleSum`.
`tsum_primeShiftDoubleSumTerm_eq_tsum_primeSeries` proves
$$\sum_{q=2}^\infty \sum_{j=1}^\infty \frac{\Lambda(q)}{q} \frac{\arcsin(1/(qj))}{j} = \sum_{n=0}^\infty \frac{\log(n+2)}{n+2} \arcsin\left(\frac{1}{n+2}\right)$$
and `primeShiftUnsignedResponseConstant_eq_half_arithmeticTrace` establishes that the unsigned response constant equals $(1/2) \operatorname{Tr}(A_\infty) = -(1/2) \mathcal{D}_{\text{prime}}$.

The *value* appearing in the diagonal limit `(4)` is now formalized in
`GaloisForLFunctions/RHTower/RadialLeakageArcsineMeasure.lean`:
`RHTower.integral_Ioi_radialLeakageDensity` proves
`integral_(Ioi k) dx/(x sqrt(x^2-1)) = arcsin(1/k)` for every `k >= 1`, and
`RHTower.radialGramDiagonal_eq_measure_slice` identifies `8 arcsin(1/k)/(11 pi k)` with the
`1/k`-scaled `k`-tail of the limiting radial leakage density.  So the right-hand side of `(4)` is
pinned to an exact measure tail rather than a quoted constant.

The exact downstream convergence bridge is now also formalized in
`GaloisForLFunctions/RHTower/RadialLeakageWeakConvergenceTransfer.lean`.
`RHTower.nuLambdaDensity_tendsto_radialGramDiagonal` derives `(4)`, with its literal `1/k` factor
and exact arcsine target, from a.e. convergence of the finite density and convergence of its total
mass.  Those two PSWF analytic inputs themselves, and the off-diagonal estimates `(7)`--`(8a)`, are
still not in Lean, so the cofinal limit `(9)` is not yet formalized.  The card remains at stage 2.

## Gates

- [x] diagonal divisibility spectrum imported
- [x] full exact nonstationary sector proved negligible
- [x] low exact finite-index first row proved negligible
- [x] diagonal and `j,k>=2` sectors summed cofinally
- [x] high truncated-divisor weighted first row proved negligible
- [x] explicit universal constant obtained
- [x] divisor collapse, positive summable diagonal spectrum, and exact scalar mass formalized
  unconditionally in Lean
- [x] double-sum Dirichlet divisor reindexing (9a) and response constant trace-shadow formalized
  unconditionally in Lean
- [x] primary formula search found no parent statement
- [x] the arcsine value in the diagonal limit `(4)` formalized in Lean as an exact measure tail
- [x] exact a.e.-density-plus-mass implication to diagonal convergence `(4)` formalized in Lean
- [ ] the diagonal convergence `(4)` itself in Lean
- [ ] independent normalization and sign audit
- [ ] combine with central correction and archimedean form
- [ ] true restricted-Weil Rayleigh comparison
