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

The word “tangent” is now literal. Canonically Möbius-transport each quadrature node and weight by

`x ↦ x/(1+h*x)` and `ω ↦ ω/(1+h*x)`.

This finite-atomic continuation and the actual source orbit have identical first derivatives in
every visible moment coordinate. In the first unseen coordinate their velocity difference is
exactly `-(2n+1) * R`. Hence `R>0` iff completed-source velocity lies strictly below canonical
flat-atomic velocity. At a right-hand first crossing the reverse weak inequality holds.

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
  diagonal signatures beyond `ξ²=t`. Even exact mass-shift transport does not repair this:
  `atomicMobiusTransportNoGo_monicRemainder` realizes every orientation inside one fixed face and
  transport hierarchy. The stronger endpoint countermodel
  `tiedPowerEndpointOrientationNoGo` retains tied weight=node power sums, conjugation closure,
  exact `85/84` sector and `2/41` radius bounds, and complete Möbius transport, yet has opposite
  remainders on the same positive singular face.
- **Strongest positive survivor:** Monic remainder is exact affine extension coordinate and exact
  completed prime--Gamma source jet. Required sign is one projective source-dominance inequality,
  not positivity of arbitrary real-rooted polynomials.
- **New insight:** Singular Hankel geometry supplies roots and positive quadrature but loses the
  extension class. Arithmetic source is not decoration: it is precisely the missing affine
  coordinate. Even a strictly positive pre-normalized carrier does not orient it after the exact
  Gamma/factorial normalization: two positive two-atom carriers now realize opposite crossings on
  one identical singular face. Any viable positive completion must be restricted to admissible
  null faces, retain mixed polar--Gamma and cross-prime covariance terms, and orient the first
  surviving factorial-Volterra rung conditional on the complete visible null flag.
- **Status:** Generic finite-Hankel, shifted-Xi specialization, source transport, first-crossing
  obstruction, and direct Gamma-diagonal no-go are unconditional Lean. Projective source
  dominance remains open; RH is not proved.

## Lean certificate

- `GaloisForLFunctions.HTGeometry.FiniteMomentNullPolynomialRoots`
- `GaloisForLFunctions.HTGeometry.FiniteHankelBoundaryQuadrature`
- `GaloisForLFunctions.HTGeometry.FiniteHankelBoundaryExtensionClass`
- `GaloisForLFunctions.HTGeometry.TiedPowerSectorOrientationNoGo`
- `GaloisForLFunctions.HTGeometry.TiedPowerEndpointOrientationNoGo`
- `GaloisForLFunctions.HTGeometry.FactorialPositiveCarrierOrientationNoGo`
- `GaloisForLFunctions.RHTower.XiShiftedHankelNullPolynomialRoots`
- `GaloisForLFunctions.RHTower.XiShiftedHankelBoundaryQuadrature`
- `GaloisForLFunctions.RHTower.XiShiftedHankelBoundaryQuadratureSource`
- `GaloisForLFunctions.RHTower.XiShiftedHankelBoundaryExtensionClass`
- `GaloisForLFunctions.RHTower.XiShiftedHankelHeatResolventBridge`
- `GaloisForLFunctions.RHTower.GammaConductorGaussianHeatDiagonalNoGo`

Key terminal theorems:

- `HTGeometry.exists_momentSequence_same_face_monicRemainder_eq`
- `HTGeometry.finiteHankelBoundaryMonicRemainder_eq_firstUnseenMomentError`
- `HTGeometry.finiteHankelBoundaryAtomicMobiusMomentTangent_firstUnseenDefect`
- `HTGeometry.atomicMobiusTransportNoGo_monicRemainder`
- `HTGeometry.tiedPowerEndpointOrientationNoGo`
- `HTGeometry.factorialPositiveCarrierOrientationNoGo`
- `HTGeometry.finiteHankelBoundaryMonicRemainder_eq_shiftedSquare`
- `RHTower.xiShiftedHankelBoundary_sourceAtomicTangency_visible`
- `RHTower.xiShiftedHankelBoundaryMonicRemainder_pos_iff_sourceTangent_lt_atomic`
- `RHTower.xiShiftedHankelFirstCrossing_atomicTangent_le_sourceTangent`
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
- 2026-08-09 — Canonical flat-atomic Möbius continuation formalized; source/atomic visible
  tangency and first-unseen normal-defect law proved.
- 2026-08-09 — Transport-only orientation conjecture falsified twice: first by an arbitrary
  signed four-atom family, then by closed conjugation-stable tied-power sources satisfying exact
  Xi local sector and radius bounds. Global completed-source incidence is now forced.
- 2026-08-09 — Positive-carrier orientation conjecture falsified by exact positive two-atom
  factorial moment sources with one common singular face and opposite crossings. The Xi crossing
  was identified exactly as the first surviving rung after a factorial-Volterra null flag.
