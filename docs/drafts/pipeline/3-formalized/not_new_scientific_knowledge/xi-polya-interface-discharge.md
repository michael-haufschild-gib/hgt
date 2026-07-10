# Xi Pólya interface discharge

- **ID:** xi-polya-interface-discharge
- **Stage:** 3-formalized
- **Type:** CLASSICAL THEOREM — formalized, not new scientific knowledge
- **Source:** `XiEntireReal.lean`, `XiConvergenceExponent.lean`, `CanonicalProduct.lean`,
  `CanonicalProductGrowth.lean`, `XiCanonicalProduct.lean`, `XiHadamardFactorization.lean`,
  `XiHadamardGrowth.lean`, and `XiLaguerrePolya.lean`
- **Statement:** `[PROVED, classical]` Under the Riemann hypothesis, the real critical-line
  restriction `Xi` lies in the Laguerre--Pólya class.  Consequently a strict failure of the first
  Laguerre inequality refutes RH without an assumed `hPolya` interface.

## Goal

Replace the argument `hPolya : RiemannHypothesis → LaguerrePolya Xi` in
`LaguerreInequality.lean` by an axiom-clean theorem.  This is a one-way classical consequence of RH,
not an attempted positivity proof of RH.

## Formal mechanism

- `XiC_differentiable`, `XiC_even`, `XiC_ofReal`, and `XiC_order`.
- Square-summability of the multiplicity-weighted xi divisor.
- Locally uniform analyticity and non-accidental-zero control for genus-one canonical products over
  arbitrary index types.
- The actual Xi divisor expanded into a sigma type of exact multiplicity copies, with no chosen
  enumeration.
- The resulting canonical product has the same zero set and the same analytic order as `XiC` at
  every point.
- Filling the removable singularities of `XiC / xiCanonicalProduct` gives the entire nowhere-zero
  `xiHadamardQuotient`, with the exact identity
  `xiHadamardQuotient * xiCanonicalProduct = XiC`.
- A zero-free entire function has an entire logarithm.
- The canonical product has proximity `o(r^2)`.  The First Main Theorem transfers this to its
  reciprocal, while the unconditional order-one bound transfers it to `XiC`; hence the filled
  quotient also has proximity `o(r^2)`.
- Poisson, Borel--Caratheodory, and Cauchy estimates force every entire logarithm of the quotient to
  be affine.  Evenness kills the linear term, giving
  `XiC = (fun _ => XiC 0) * xiCanonicalProduct` unconditionally.
- Under RH, deterministic reflection-closed finite divisor products are real-split polynomials.
  A countable finite exhaustion and locally uniform convergence with two derivatives prove
  `xi_laguerrePolya_of_rh : RiemannHypothesis → LaguerrePolya Xi`.
- `laguerre_margin_neg_not_RH` now takes only the strict margin deficit and has no Pólya argument.

## Main declarations

- `xiHadamardQuotient_proximity_isLittleO_sq`
- `entire_log_affine_of_proximity_isLittleO_sq`
- `xiHadamardQuotient_constant`
- `XiC_eq_constant_mul_canonicalProduct`
- `xi_laguerrePolya_of_rh`
- `laguerre_margin_neg_not_RH`

## Gates

- [x] 0 → 1: all structural and convergence inputs identified in Lean
- [x] 1 → 2: quotient growth-to-affine, even reindexing, and real-root partial-product convergence
- [x] 2 → 3: prove the RH-to-Laguerre--Pólya provider and remove `hPolya` from the detector
- [ ] 3 → 4: axiom audit, formal lint, and documentation index
