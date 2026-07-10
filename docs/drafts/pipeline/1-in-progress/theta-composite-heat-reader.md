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
4. [CONJECTURE] Its source-side representative has a computable pairing with the reflected theta
   half and the third-order balanced Perron kernel.
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
- Even after coefficient extraction, the reflected-half contribution must be transported through
  the same functional. Ignoring it would repeat the exact-coherence error.
- `[PROVED]` The compactified nodes tend to zero. The isolated-zero principle therefore forces
  every symbol holomorphic on a connected compactified domain containing zero and all nodes, and
  vanishing on all but one node, to vanish at the selected node as well. An exact reader in this
  compactified moment-symbol category is necessarily singular or nonanalytic at `x = 0`.

## Open core

[OPEN CORE] Use the canonical reader from
`../2-fully-proven/new/xi-theta-square-rate-hardy-reader.md` to define the functional directly on
the completed critical cosine trace, then compute its reflected balanced-Perron charge. Formalize
the half-plane H2/Paley-Wiener bridge without an existence Prop. Any connected-domain compactified
moment symbol must carry the forced singularity at `x = 0`.

## Gates

- [x] 0 -> 1: exact atom bridge, fixed-index audit, and first functional gap identified.
- [ ] 1 -> 2: infinite reader and reflected charge proved; weighted Hilbert map is complete.
  The analytic compactified-moment alternative has been ruled out and the infinite interpolation
  symbol, exact boundary energy, and canonical L2 reader have been proved.
- [ ] 2 -> 3: Lean formalization without a reader-existence Prop.
- [ ] 3 -> 4: composition into an unconditional Perron contradiction.
