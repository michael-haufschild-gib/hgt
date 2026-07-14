# Anchored Euler commutator Calkin norm is equivalent to the seam value defect

- **ID:** `anchored-euler-commutator-calkin-norm-equivalence`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), `[TOP-DOWN ROUTE CLASSIFICATION]`, `[VALUE RELATION]`
- **Scientific status:** `[PROVED] [POSITIVE NO-WASTE THEOREM] [NOT AN RH PROOF]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/XiPrimeSeamAnchoredCommutatorNormComparison.lean`
- **Parents:** `cofinal-first-prime-euler-compression-essential-norm-decay.md`;
  `xi-prime-seam-calkin-gram.md`
- **Statement:** The charge-scale essential norm of the anchored two-prime compressed Euler
  commutator is uniformly equivalent, with constants one and two, to the raw two-prime seam value
  difference.

## Theorem

Fix a positive Sonin aperture `a`, a complex point `rho`, and a prime `q>2`.  Write

```text
u_p = orbitwiseNatPrimeSeamCharge p rho,
C_q = firstPrimeAnchoredEulerCompressionCommutator a rho q.
```

Lean proves the two-sided estimate

```text
|u_2-u_q| <= sqrt(2q) essentialNorm(C_q) <= 2 |u_2-u_q|.       (1)
```

The proof identifies the finite orientation Gram of the packet `{2,q}` with the sum of the two
ordered seam-weighted quadratic corners.  The exact essential norm of either corner is

```text
essentialNorm(corner(2,q)) = |u_2-u_q| / sqrt(2q).             (2)
```

Finite Gram Calkin injectivity supplies the lower comparison in `(1)`.  The essential-norm
triangle inequality and `(2)` supply the upper comparison.

## Positive route classification

Equation `(1)` is a faithful-coordinate theorem.  It says that the scaled commutator norm neither
loses nor creates orientation information: it is bi-Lipschitz equivalent to the finite rational
prime-seam value defect.  Consequently

```text
sqrt(2q) essentialNorm(C_q) -> 0 along cofinal primes
```

is equivalent, up to the fixed factor two, to

```text
|u_2-u_q| -> 0 along the same primes.
```

Since the corpus already proves `u_q -> 0` throughout the open strip, either condition forces
`u_2=0`; on every Xi divisor fibre this is RH.  Thus the charge-scale Calkin target is useful as
an exact detector and quantitative coordinate, but it is not an independent source-side route for
making the common charge vanish.  A future proof must introduce information not already contained
in the two-prime value difference.

## Formalization

- `essentialNorm_add_le` adds the reusable triangle inequality to the essential-norm API.
- `anchored_orientationGram_eq_pairCalkinCorners` proves the exact two-corner decomposition.
- `essentialNorm_anchoredCommutator_le_two_mul_corner` proves the upper comparison.
- `essentialNorm_corner_le_anchoredCommutator` proves the lower comparison.
- `scaledEssentialNorm_corner_eq_seamDifference` proves the exact scale cancellation.
- `scaledEssentialNorm_anchoredCommutator_between_seamDifference` is the capstone `(1)`.

## Gates

- [x] prove the essential-norm triangle inequality
- [x] identify the anchored orientation Gram with its two ordered corners
- [x] prove both essential-norm comparisons
- [x] cancel the exact positive-Euler scale
- [x] import through the `RHTower` umbrella
- [x] refresh the generated formal indexes
- [x] narrow-build and axiom-audit the capstone

