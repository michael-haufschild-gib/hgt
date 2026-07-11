# Composite critical-trace to heat coefficient reader

- **ID:** theta-composite-heat-reader
- **Stage:** 5-failed / retired as RH route
- **Type:** FALSIFIED ROUTE / VALID READER INFRASTRUCTURE
- **Date:** 2026-07-10
- **Parents:** ../2-fully-proven/new/xi-theta-heat-reparametrization.md,
  ../2-fully-proven/new/xi-theta-reader-superexponential-conditioning.md
- **Statement:** The fixed-index composite reader is analytically valid, but its moving boundary is
  an exact flat translation coboundary and therefore cannot supply the nontrivial RH weld class.

## Constraint

The reader must be a compatibility condition among four fixed structures:

1. the completed cosine trace;
2. the real positive half-source;
3. the shifted heat family exp(-pi m squared)exp(-pi m squared y);
4. the balanced Perron boundary coordinate.

No new evolution parameter or free defect is allowed.

## Candidate moves

1. [BRIDGE] Use Fourier inversion to recover the positive source, then the exact map T from the
   parent theorem.
2. [PROVED PAPER] The explicit symbol is in right-half-plane H2 with exact norm, and inverse
   Paley-Wiener defines the canonical L2 heat reader.
3. [PROVED SYMBOL] The canonical quotient `sin(pi sqrt(z))/sinh(pi sqrt(z))`, normalized by its
   nonzero slope at `n squared`, gives one at the selected square and zero at every other square.
4. [FALSIFIED AS AN INDEPENDENT TERM] Its source-side representative should be paired separately
   with the reflected theta half.  Reflection is already the conjugate half of the critical cosine
   trace, while the reflected physical function is upper-supported and is not a second admissible
   lower-supported Perron source.
5. [FALSIFIED] Replace the half-plane reader by an entire moment symbol in the compactified node
   `x = exp(-pi m squared)`.
6. [PROVED BOUNDARY] The physical reader has exact boundary energy `4 sinh(pi n)^2`, hence
   normalized boundary norm `sqrt(2/pi) sinh(pi n)`.

## Attack

- The exp(pi n squared) cost is finite because n is fixed before contour depth tends to infinity.
  Uniform-in-n conditioning is not required by the existing Perron contradiction.
- `[DISCHARGED]` The nonlinear heat reparametrization changes measure by the exact identity
  `norm(Tf)^2=(1/4) integral exp(u/2)|f(u)|^2 du`. The source topology is now fixed intrinsically.
- `[DISCHARGED AT SYMBOL LEVEL]` The infinite interpolation symbol is explicit and normalized;
  no existence proposition and no finite cutoff remain.
- `[DISCHARGED AT BOUNDARY LEVEL]` Its punctured imaginary-boundary modulus, exact Cauchy profile,
  integrability, and normalized boundary energy are all proved.
- `[DISCHARGED ON PAPER]` Factoring the selected Blaschke zero gives uniform interior Hardy
  control; inverse Paley-Wiener gives a canonical L2 reader of norm
  `sqrt(2/pi) sinh(pi n)`. Lean lacks the half-plane H2/Paley-Wiener API.
- `[DISCHARGED BY REFRAMING]` The reflected half is not an independent Perron datum.  The positive
  theta source is real, its reflection has conjugate Fourier transform, and the completed critical
  trace is the real part of the positive Fourier transform.
- `[DISCHARGED]` The actual positive half is a canonical lower-supported `L2` source with threshold
  zero.  Its negative-line Perron charge tends to zero whenever `n-delta>1`, and vertical flank
  energy constructs its additive seam defect canonically.
- `[PROVED]` The compactified nodes tend to zero. The isolated-zero principle therefore forces
  every symbol holomorphic on a connected compactified domain containing zero and all nodes, and
  vanishing on all but one node, to vanish at the selected node as well. An exact reader in this
  compactified moment-symbol category is necessarily singular or nonanalytic at `x = 0`.

## Route verdict

`[FALSIFIED AS AN RH ROUTE]` The Hardy reader remains a valid coefficient functional, but the
moving boundary it transports is
`T_a P_+ - P_+ T_a`.  After inverse-translation normalization it is the exact conjugation
coboundary `T_a P_+ T_(-a)-P_+`, with an exact cocycle law and zero curvature.  Complete proof:
`../2-fully-proven/new/xi-theta-boundary-coboundary-no-go.md`.

The fixed positive source and reflected cosine datum remain valid infrastructure
(`../2-fully-proven/new/xi-theta-unit-radius-perron-source.md`).  The RH-bearing object must instead
be a static non-exact completed-theta/prime obstruction class surviving the quotient by all affine
flow coboundaries.

The direct reflected-reader calculation is now formalized in
`formal/GaloisForLFunctions/RHTower/XiThetaSquareRateReflectedAction.lean`. In the global shifted
heat coordinate the reflected profile is supported below zero, so
`thetaHeatRateSourceReaderL2_reflectedThetaAction_eq_zero` proves exact annihilation by the causal
reader. The alternative reorientation is definitionally the positive half and supplies no second
charge. See
`../3-formalized/not_new_scientific_knowledge/theta-causal-reader-reflected-action-zero.md`.

## Gates

- [x] 0 -> 1: exact atom bridge, fixed-index audit, and first functional gap identified.
- [x] Reader infrastructure: infinite symbol, exact norm, weighted Hilbert map, and direct theta
  Perron source proved.
- [x] Route falsification: reflected charge is not independent and the moving boundary is an exact
  flat translation coboundary.
- [x] Reflected action: the causal reader's direct completed-theta pairing is exactly zero in Lean.
- [ ] Any future reuse must occur only after quotienting out this affine flow defect.
