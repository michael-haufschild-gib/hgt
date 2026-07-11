# The constrained finite-aperture radial prime charge has a universal limit

- **ID:** `constrained-prolate-full-radial-prime-charge-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Scientific status:** `[PROVED HERE] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`,
  pending independent formula-level audit
- **Parent results:** `constrained-prolate-radial-leakage-divisibility-spectrum.md`,
  `ccm-exact-radial-nonstationary-sector-bound.md`, and
  `ccm-prime-shift-radial-index-separation-law.md`, and
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

## Lean decision

The formal tree has no PSWF radial asymptotics or closed prime-form interface. No Lean file is
added before independent paper-proof audit.

## Gates

- [x] diagonal divisibility spectrum imported
- [x] full exact nonstationary sector proved negligible
- [x] low exact finite-index first row proved negligible
- [x] diagonal and `j,k>=2` sectors summed cofinally
- [x] high truncated-divisor weighted first row proved negligible
- [x] explicit universal constant obtained
- [x] primary formula search found no parent statement
- [ ] independent normalization and sign audit
- [ ] combine with central correction and archimedean form
- [ ] true restricted-Weil Rayleigh comparison
