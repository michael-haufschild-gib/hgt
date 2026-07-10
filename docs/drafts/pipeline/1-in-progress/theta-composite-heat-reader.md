# Composite critical-trace to heat coefficient reader

- **ID:** theta-composite-heat-reader
- **Stage:** 1-in-progress
- **Type:** CANDIDATE / FIXED-INDEX COMPOSITE READER
- **Date:** 2026-07-10
- **Parents:** ../2-fully-proven/new/xi-theta-heat-reparametrization.md,
  ../2-fully-proven/new/xi-theta-reader-superexponential-conditioning.md
- **Statement:** For every fixed square index n, inverse logarithmic Fourier, heat
  reparametrization, exact boundary denormalization, and the square-rate Hardy reader compose to a
  coefficient functional on the completed critical trace whose Perron seam charge can be computed.

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

## Open core

[OPEN CORE] The Hardy reader remains a valid coefficient functional, but it is not the missing
Perron bridge.  The positive theta source and its reflected cosine datum are now fully accounted
for by `../2-fully-proven/new/xi-theta-unit-radius-perron-source.md`.  Construct a genuinely
non-diagonal completed coefficient extractor which retains Gamma-driven vertical decay while
exposing fixed arithmetic coefficients on the right edge.  Scalar decompletion cannot meet both
requirements.  Formalizing the half-plane H2/Paley-Wiener bridge is useful reader infrastructure,
not the carrier obstruction itself.

## Gates

- [x] 0 -> 1: exact atom bridge, fixed-index audit, and first functional gap identified.
- [ ] 1 -> 2: the infinite reader, weighted Hilbert map, and direct theta Perron source are proved.
  The reflected charge was falsified as an independent term.  The remaining requirement is the
  non-diagonal completed/raw carrier extractor.
- [ ] 2 -> 3: Lean formalization without a reader-existence Prop.
- [ ] 3 -> 4: composition into an unconditional Perron contradiction.
