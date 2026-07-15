# Sonin full-counting reflection

- **ID:** `sonin-full-counting-reflection`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / exact physics value relation / corpus strengthening
- **Scientific status:** BRIDGE / NOT NEW SCIENTIFIC KNOWLEDGE
- **Source:**
  `formal/GaloisForLFunctions/HTGeometry/TwoProjectionHilbertSchmidtEnergy.lean`,
  `formal/GaloisForLFunctions/RHTower/SoninTimeBandHilbertSchmidt.lean`, and
  `docs/drafts/pipeline/1-in-progress/sonin-free-fermion-number-variance.md`
- **Statement:** The central Sonin prolate compression and its zero-mode-subtracted exterior
  supersymmetric partner have the same trace, every positive power trace, fluctuation spectral
  measure, and free-fermion full-counting determinant.

## Goal

Upgrade the existing quadratic Sonin number-variance identity to a complete source-specific
counting-statistics relation without introducing a numerical modular-energy regulator.  The result
uses only the actual physical/Fourier cutoff projections and their actual common-zero-mode
projection.  No zeta zero, RH hypothesis, fitted spectrum, or auxiliary physics carrier enters.

## Gates

- [x] 0 -> 1 in-progress: the operators, trace ideals, and attack are source-selected by the live
  Sonin projection pair
- [x] 1 -> 2 fully-proven: complete paper proof below; no open mathematical dependency
- [ ] 2 -> 3 formalized: requires a coordinate-free trace-class positive-domination lemma and an
  operator-side Fredholm determinant bridge; no Lean process or build has been run
- [ ] 3 -> 4 publication-ready: not a standalone novelty claim; include only as a structural
  bridge in a Sonin operator paper

## Operators

For `a>0`, orient the physical/Fourier projections as in the existing supersymmetric surface and
write

```text
A = soninAlternatingBlock(physicalForbidden(a), fourierForbidden(a)),
E = centralSoninExteriorCompression(a),
K = twoProjectionTransition(FourierProjection, PhysicalProjection).
```

Thus `A` is the interior prolate correlation operator and `E` is the complementary correlation
operator after subtracting the complete common zero-mode projection.  The current corpus proves

```text
K^* K = A-A^2,
K K^* = E-E^2,
Tr(A-A^2) = Tr(E-E^2),
||A||_HS^2 = ||E||_HS^2,
0 <= A,E,                 ||A||<1, ||E||<1,
Tr(A^(n+1)-A^(n+2)) = Tr(E^(n+1)-E^(n+2))  for every n>=0,
Tr(A)=4a^2.
```

The last trace is the already-proved Shannon time-band area law.  It is trace class because
`A=(RP)^*(RP)` with `RP` Hilbert--Schmidt.

## Proof

**[PROVED HERE]** Since `E` is positive compact with `r=||E||<1`, every eigenvalue `lambda_j(E)`
lies in `[0,r]`.  The factorization `E-E^2=K K^*` is trace class, so

```text
sum_j lambda_j(E)(1-lambda_j(E)) < infinity.
```

But `1-lambda_j(E) >= 1-r`, hence

```text
sum_j lambda_j(E)
  <= (1-r)^(-1) sum_j lambda_j(E)(1-lambda_j(E)) < infinity.
```

Therefore `E` is trace class.  This is the missing degree-one trace fact; it follows from the
already-proved strict contraction and impurity factorization, not from a new spectral hypothesis.

Because `A` and `E` are self-adjoint Hilbert--Schmidt operators,

```text
Tr(A^2)=||A||_HS^2,   Tr(E^2)=||E||_HS^2.
```

The existing Hilbert--Schmidt equality gives `Tr(A^2)=Tr(E^2)`.  Combining this with the existing
impurity-trace equality gives

```text
Tr(E)
 = Tr(E-E^2)+Tr(E^2)
 = Tr(A-A^2)+Tr(A^2)
 = Tr(A)
 = 4a^2.                                                (1)
```

For every `m>=2`, the current finite-telescoping invariant says

```text
Tr(A^2)-Tr(E^2) = Tr(A^m)-Tr(E^m).
```

Its left side is zero, so together with (1),

```text
Tr(A^m)=Tr(E^m)  for every integer m>=1.                (2)
```

Equivalently, define the finite fluctuation spectral measure of a positive strict contraction by

```text
mu_T = sum_j lambda_j(T)(1-lambda_j(T)) delta_(lambda_j(T)).
```

The all-power Witten identity gives equality of every Hausdorff moment of `mu_A` and `mu_E`:

```text
integral t^n d mu_A(t)
 = Tr(A^(n+1)-A^(n+2))
 = Tr(E^(n+1)-E^(n+2))
 = integral t^n d mu_E(t).
```

Both measures are finite and supported in `[0,1]`; determinacy of the Hausdorff moment problem
therefore gives

```text
mu_A = mu_E.                                             (3)
```

Since the weight `t(1-t)` is strictly positive on `(0,1)` and both operators have norm below one,
(3) recovers the complete nonzero spectrum with multiplicity.  Zero modes are deliberately
invisible, as required by the common-zero-mode subtraction.

Finally, for every complex counting parameter `u`, trace class gives the Fredholm determinants

```text
Chi_A(u)=det(1+uA),   Chi_E(u)=det(1+uE).
```

Their logarithmic expansions near `u=0` are

```text
log Chi_T(u) = sum_(m>=1) (-1)^(m+1) u^m Tr(T^m)/m.
```

Equation (2) makes the expansions identical.  The determinants are entire, so analytic
continuation gives

```text
det(1+uA)=det(1+uE)  for every u in C.                   (4)
```

With `u=exp(i theta)-1`, (4) is equality of the two free-fermion full-counting characteristic
functions.  The already-formalized number variance is their quadratic fluctuation coordinate.
All Renyi entropies of order `q>1` are finite and equal because their one-mode kernels are
`O(t)` at zero and the common spectrum is trace class.  Equality of the von Neumann endpoint is
conditional only on the additional logarithmic summability `sum t log(1/t)<infinity`; trace class
alone does not imply that endpoint.

## Direct corpus application

1. Exposes the previously absent exterior trace value `Tr(E)=4a^2`.
2. Promotes the live number-variance bridge from one quadratic scalar to the complete counting
   determinant.
3. Packages every current all-power Witten cancellation into one analytic value reflection.
4. Supplies a regulator-free substitute for a bounded modular Hamiltonian.  The literal operator
   `-log T` is unbounded because the compact spectrum accumulates at zero; inserting an epsilon
   would be arbitrary.
5. Leaves the RH source-norm comparison unchanged.  This is structural information about the
   Sonin projection pair, not an RH implication.

## Novelty audit

The nonzero spectral pairing is a classical consequence of the canonical two-projection
decomposition, and the correlation-operator/full-counting relation is standard free-fermion
theory.  The exact Sonin specialization, the exterior trace `4a^2`, and the bridge to the current
all-power trace surface are useful additions to this corpus, but they do not clear the NOVEL gate.
Accordingly this card is classified as a proved bridge rather than new scientific knowledge.

Primary provenance:

- P. R. Halmos, *Two Subspaces*, Transactions of the American Mathematical Society 144 (1969),
  381--389, https://doi.org/10.1090/S0002-9947-1969-0251519-5.
- I. Klich and L. Levitov, *Quantum Noise as an Entanglement Meter*, Physical Review Letters 102
  (2009), 100502, https://doi.org/10.1103/PhysRevLett.102.100502.
- I. Peschel and V. Eisler, *Free-fermion entanglement and spheroidal functions*, Journal of
  Physics A 46 (2013), 155301, https://arxiv.org/abs/1302.2239.

## Log

- 2026-07-15 -- extracted from the mquantum Peschel/SRMT catalogue as a source-specific Sonin
  transfer; paper proof completed; no mquantum execution, modification, build, test, or numerical
  computation was performed.
