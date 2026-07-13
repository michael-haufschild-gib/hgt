# Schwartz compact-multiplier diagonal factorization

- **ID:** `schwartz-compact-multiplier-diagonal-factorization`
- **Stage:** 1-in-progress
- **Type:** THEOREM / BOCHNER--SCHWARTZ INFRASTRUCTURE
- **Scientific status:** `[CONJECTURE] [OPEN CORE] [BRIDGE] [NOT AN RH PROOF]`
- **Parent:** `hedenmalm-universal-positive-form-classification.md`
- **Statement:** A jointly continuous momentum-symmetric Schwartz form factors on compactly
  supported arguments through the single product `f * conj g`.

## Goal

For a jointly continuous sesquilinear form `Q` on complex Schwartz space, assume spectral momentum
symmetry.  Prove, for compactly supported Schwartz maps `f,g` and a compactly supported smooth
cutoff `chi` equal to one near both supports,

```text
Q.fourierPullback f g = Q.fourierPullback (f * conj g) chi.       (1)
```

Equation `(1)` is the order-zero diagonal constraint needed to define a positive distribution and
then its Riesz--Markov measure.  No kernel, representation measure, or positivity of the Xi
Bezoutian may be assumed.

## Proved input

Polynomial functional calculus of spectral momentum is symmetric.  A single positive polynomial
separator proves that disjoint compact spectral supports are orthogonal.  These inputs are in
`formal/GaloisForLFunctions/SchwartzCompactPolynomialSeparation.lean`.

## Attack

1. Prove simultaneous polynomial approximation of every smooth function on a compact interval in
   all derivatives by an explicit diagonal sequence.
2. Compact support turns derivative-uniform approximation into convergence in the full Schwartz
   topology after multiplication by `f` or `chi`.
3. Pass polynomial multiplier symmetry to every compactly supported smooth real multiplier, then
   to complex multipliers by real/imaginary polarization.
4. Apply the complex multiplier identity with the multiplier `conj g` to obtain `(1)`.
5. Prove cutoff independence using disjoint-compact-support orthogonality.

## Exact open core

The missing reusable lemma is the one-dimensional `C-infinity` Weierstrass theorem in the present
toolchain:

```text
for smooth a on [A,B], there are real polynomials P_n such that
sup_[A,B] |D^k(P_n-a)| -> 0 for every fixed k.
```

The intended proof is constructive: approximate the highest derivative by ordinary Weierstrass,
then integrate the approximating polynomial while matching the lower jet at the left endpoint.

## Gates

- [x] compact spectral locality
- [x] polynomial multiplier symmetry
- [ ] all-derivative polynomial approximation
- [ ] smooth compact-multiplier symmetry
- [ ] diagonal product factorization
- [ ] positive order-zero distribution
- [ ] Riesz--Markov measure

