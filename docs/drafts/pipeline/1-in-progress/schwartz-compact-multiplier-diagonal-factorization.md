# Schwartz compact-multiplier diagonal factorization

- **ID:** `schwartz-compact-multiplier-diagonal-factorization`
- **Stage:** 1-in-progress
- **Type:** THEOREM / BOCHNER--SCHWARTZ INFRASTRUCTURE
- **Scientific status:** `[PARTIALLY FORMALIZED] [OPEN CORE] [BRIDGE] [NOT AN RH PROOF]`
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

The all-derivative Weierstrass lemma, smooth multiplier symmetry, canonical diagonal
factorization, and cutoff stability are complete.  For a nonnegative momentum-symmetric form the
stabilized local diagonal functional is now proved positive on every nonnegative compactly
supported real smooth test and satisfies an explicit local sup-norm bound. Polynomial multiples of
one fixed smooth cutoff are proved uniformly dense in each compact `C_c(R)` packet, with a common
support. The remaining bridge is the compatible limit functional and Riesz--Markov. No representing
measure may be inserted as an assumption.

## Gates

- [x] compact spectral locality
- [x] polynomial multiplier symmetry
- [x] all-derivative polynomial approximation
- [x] smooth compact-multiplier symmetry
- [x] diagonal product factorization
- [x] canonical cutoff stability
- [x] positivity on all nonnegative compact smooth tests
- [x] local order-zero sup-norm estimate
- [x] fixed-support uniform density in compact continuous packets
- [ ] positive order-zero distribution
- [ ] Riesz--Markov measure
