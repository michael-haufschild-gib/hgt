# Mass-shifted Hankel flat quadrature and affine extension class

- **ID:** mass-shifted-hankel-flat-extension
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/mass-shifted-spectral-trace-route.md` · §9.3 Exact open core
- **Statement:** A minimal singular shifted-Xi Hankel face is an exact positive flat quadrature;
  its outgoing flux is the canonical affine next-moment extension coordinate and equals one
  completed prime--Gamma source jet.

## Goal

Replace the broad terminal-sign problem at a first singular shifted-Xi Hankel face by its exact,
projectively invariant source inequality. Separate information fixed by the current face from the
single unseen moment that source transport must control.

## Gates

- [x] 0 → 1  in-progress: source-pure finite-Hankel attack and Door passport identified
- [x] 1 → 2  fully-proven: dependency-closed exact algebra, quadrature, root, and source proofs
- [x] 2 → 3  formalized: unconditional Lean theorems listed below; targeted modules green
- [ ] 3 → 4  publication-ready: standalone paper and external novelty audit

## Approach

For moments `s`, let the size-`n+1` Hankel matrix be singular, its size-`n` head positive
definite, and `c` a nonzero null vector. The terminal coordinate is nonzero. Its degree-`n` null
polynomial has `n` distinct real roots. Those roots carry unique strictly positive Lagrange
weights and reproduce the moment functional on every polynomial of degree at most `2n`.

The first unseen polynomial is `X^(n+1) p`. After monic normalization, its quadrature remainder
is a scalar `R(s,[c])` depending only on the projective null line. The raw terminal flux obeys

`c_last * coupling = c_last^2 * R(s,[c])`.

Kernel orthogonality gives the stronger intrinsic identity

`R(s,[c]) = L_s(X * p^2)`.

Thus `R` is the shifted-Hankel square energy of the monic null state: the unique local Stieltjes
tangent coordinate transverse to the current unshifted Hankel face.

Changing only `s_(2n+1)` by `δ` leaves the entire current Hankel face fixed and translates
`R(s,[c])` by exactly `δ`. Hence determinant, discriminant, null roots, nodes, weights, and every
other invariant of the current face cannot determine outgoing sign.

For shifted Xi moments, `R` is simultaneously:

- the monic positive-flat-quadrature remainder;
- the Gaussian heat-resolvent boundary integral after projective normalization;
- the completed source jet divided by `c_last`;
- on the Euler ray, the archimedean jet plus Chebyshev-discrepancy jet after multiplication by
  `c_last`;
- for `0 ≤ y < 41/2`, the convergent source-only negative-binomial prime--Gamma jet after the
  same projective normalization.

Thus strict positivity is exactly

`-(c_last * discrepancyJet) < c_last * archimedeanJet`.

At a right-hand first crossing the monic remainder is nonpositive, so this projective source
dominance is impossible. Proving dominance for every admissible singular face excludes every
first crossing.

## No-go closure

- **Exact killing theorem/mechanism:** Current-face data do not determine outgoing sign:
  `exists_momentSequence_same_face_monicRemainder_eq` prescribes any real remainder while fixing
  the complete face. Direct identification with a positive Gamma-conductor Mercer residual also
  fails: `gaussianHeatPrimeDiagonalCurvature_neg` and
  `not_exists_gaussianHeatPrimeDiagonalCurvature_eq_sq_mul_gammaConductorResidual` give opposite
  diagonal signatures beyond `ξ²=t`.
- **Strongest positive survivor:** Monic remainder is exact affine extension coordinate and exact
  completed prime--Gamma source jet. Required sign is one projective source-dominance inequality,
  not positivity of arbitrary real-rooted polynomials.
- **New insight:** Singular Hankel geometry supplies roots and positive quadrature but loses the
  extension class. Arithmetic source is not decoration: it is precisely the missing affine
  coordinate. Any viable positive completion must be restricted to admissible null faces and
  retain mixed polar--Gamma and cross-prime covariance terms.
- **Status:** Generic finite-Hankel, shifted-Xi specialization, source transport, first-crossing
  obstruction, and direct Gamma-diagonal no-go are unconditional Lean. Projective source
  dominance remains open; RH is not proved.

## Lean certificate

- `GaloisForLFunctions.HTGeometry.FiniteMomentNullPolynomialRoots`
- `GaloisForLFunctions.HTGeometry.FiniteHankelBoundaryQuadrature`
- `GaloisForLFunctions.HTGeometry.FiniteHankelBoundaryExtensionClass`
- `GaloisForLFunctions.RHTower.XiShiftedHankelNullPolynomialRoots`
- `GaloisForLFunctions.RHTower.XiShiftedHankelBoundaryQuadrature`
- `GaloisForLFunctions.RHTower.XiShiftedHankelBoundaryQuadratureSource`
- `GaloisForLFunctions.RHTower.XiShiftedHankelBoundaryExtensionClass`
- `GaloisForLFunctions.RHTower.XiShiftedHankelHeatResolventBridge`
- `GaloisForLFunctions.RHTower.GammaConductorGaussianHeatDiagonalNoGo`

Key terminal theorems:

- `HTGeometry.exists_momentSequence_same_face_monicRemainder_eq`
- `HTGeometry.finiteHankelBoundaryMonicRemainder_eq_shiftedSquare`
- `RHTower.xiShiftedHankelBoundaryMonicRemainder_pos_iff_projectiveSourceDominance`
- `RHTower.xiShiftedHankelBoundaryShiftedSquare_pos_iff_projectiveSourceDominance`
- `RHTower.xiShiftedHankelFirstCrossing_shiftedSquare_nonpos`
- `RHTower.hasDerivAt_xiShiftedMomentHankelQuadratic_of_kernel_succ_shiftedSquare`
- `RHTower.xiShiftedHankelFirstCrossing_not_projectiveSourceDominance`
- `RHTower.xiShiftedHankel_terminal_mul_primeArchJet_eq_sq_mul_monicRemainder`

## Log

- 2026-08-08 — Conjecture “minimal singular face forces real-simple null roots” proved.
- 2026-08-08 — Conjecture “terminal flux is first flat-quadrature remainder” proved in stronger
  positive exactness form through degree `2n`.
- 2026-08-08 — Conjecture “current face determines outgoing sign” falsified; arbitrary affine
  extension fiber proved and formalized.
- 2026-08-08 — Conjecture “direct Gamma Mercer residual equals Gaussian heat curvature”
  falsified by exact diagonal signature mismatch; mixed completion survives.
- 2026-08-08 — Exact projective prime--Gamma source-dominance frontier formalized.
