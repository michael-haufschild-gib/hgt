# Compact spectral diagonal positivity law

- **ID:** `compact-spectral-diagonal-positivity-law`
- **Stage:** 3-formalized
- **Type:** THEOREM / BOCHNER--SCHWARTZ BRIDGE
- **Scientific status:** `[FULLY PROVEN] [FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parent:** `../../1-in-progress/hedenmalm-universal-positive-form-classification.md`

## Theorem

Let `Q` be a jointly continuous complex sesquilinear form on Schwartz space whose physical
momentum operator is symmetric. For compactly supported spectral packets `f,g`, there is a
canonical smooth interval cutoff `chi_R` such that

```text
Q_hat(f,g)=Q_hat(f*conj(g),chi_R).
```

The value on the right is independent of every sufficiently large canonical cutoff. Hence the
compact spectral restriction of `Q_hat` factors through a stabilized local diagonal functional
`L`.

If `Q` is nonnegative, then for every compactly supported real Schwartz function `h >= 0`,

```text
Re L(h) >= 0,    Im L(h)=0.
```

The last assertion holds for the full smooth positive cone, not only for functions already
presented as modulus squares.

## Proof mechanism

1. A constructive all-derivative Weierstrass theorem approximates every smooth real multiplier on
   a compact interval by a diagonal sequence of real polynomials.
2. Compact support upgrades derivative-uniform approximation to convergence in the full Schwartz
   topology.
3. Polynomial momentum symmetry therefore extends to all smooth temperate multipliers on compact
   packets, including the complex adjoint law.
4. Multiplication by `conj(g)` gives diagonal factorization.
5. Disjoint compact spectral locality proves cutoff stability.
6. For `h >= 0`, the regularizations
   ```text
   f_epsilon(t)=chi_R(t)*sqrt(h(t)+epsilon)
   ```
   are compactly supported smooth functions and satisfy
   ```text
   |f_epsilon|^2=h+epsilon*|chi_R|^2.
   ```
   Positivity on squares and `epsilon -> 0` give positivity on `h`.
7. The nonnegative cutoff envelopes `M*chi +/- h`, with `M` the zeroth Schwartz seminorm,
   give the explicit local order-zero estimate
   ```text
   |L(h)| <= M L(chi).
   ```
8. Ordinary Weierstrass approximation followed by multiplication by the same cutoff gives a
   uniformly convergent polynomial-cutoff sequence for every compactly supported continuous real
   function, while all approximants retain one common compact support.

## Formal artifacts

- `formal/GaloisForLFunctions/HTGeometry/PolynomialSmoothApproximation.lean`
- `formal/GaloisForLFunctions/HTGeometry/SchwartzSmoothMultiplierApproximation.lean`
- `formal/GaloisForLFunctions/HTGeometry/SchwartzSmoothMultiplierSymmetry.lean`
- `formal/GaloisForLFunctions/HTGeometry/SchwartzCompactDiagonalFunctional.lean`
- `formal/GaloisForLFunctions/HTGeometry/SchwartzPositiveCompactDiagonal.lean`
- `formal/GaloisForLFunctions/HTGeometry/SchwartzCompactDiagonalOrderZero.lean`
- `formal/GaloisForLFunctions/HTGeometry/SchwartzCompactContinuousDensity.lean`

The modules contain no `sorry`, `admit`, new axioms, opaque declarations, or unsafe
declarations.

## Exact boundary

This law constructs the positive smooth-test functional locally, proves its local sup-norm
estimate, and supplies fixed-support uniform density in `C_c(R)`. The remaining classical bridge is
the compatible limit functional and Riesz--Markov representation. It does not orient the Hedenmalm
moment Bezoutian: that sign is an independent statement already equivalent to RH.
