# Relation-kernel transgression route to the Riemann hypothesis

- **ID:** `riemann-relation-kernel-transgression-route`
- **Stage:** 1-in-progress
- **Type:** UNIVERSAL LAW / SOURCE-NATIVE RH ROUTE / PAPER BACKBONE
- **Status:** `[RELATION-KERNEL TRANSGRESSION LEAN-PROVED] [CALDERON--WITT CALIBRATOR LEAN-PROVED] [SOURCE AND GREEN TRANSPORT PROVED] [ARITHMETIC COMPARISON OPEN] [NOT RH]`

## Frontier

The current corpus has already constructed, without a critical-line premise:

1. a fixed Meyer Gaussian source nonzero on every multiplicity copy;
2. a literal two-line prime--Gamma Cauchy boundary whose integral is that source;
3. the unique harmonic Green primitive of the source;
4. adaptive Mobius--theta columns converging to the same primitive;
5. completed Green transport recovering the source;
6. a coefficient-faithful Calderon--Witt incidence and resolved provenance quotient;
7. the exact antidiagonal Green defect, whose universal vanishing is equivalent to RH.

Thus Hilbert realization, source existence, completion, non-erasure, and Green transport are not
the open problem.  The open problem is arithmetic annihilation of the retained antidiagonal before
codiagonal, positivity, or spectral realization erases its sign.

## Universal law

Let `pi : R -> A` be a surjective group map, `K = ker pi`, and let `c` be a normalized two-cocycle
of `A` with values in a rational vector space `M`.  Suppose the pullback of `c` to `R` is a
coboundary with primitive `b`:

```text
c(pi g, pi h) = b(gh) - b(g) - b(h).
```

Then `b|K` is a homomorphism.  If every degree-one character of `R` descends through `pi`, this
kernel character is independent of the chosen primitive.  It vanishes exactly when `c` is already
a coboundary on `A`.  For an abelian `A` and an alternating `c`, a coboundary is symmetric, hence
`b|K = 0` exactly when `c = 0`.

This is the **relation-kernel transgression law**.  A cohomologically flat free cover does not erase
a degree-two class.  It moves the class to a canonical degree-one character on the relation kernel.

## Riemann specialization

The Calderon--Witt derived cup is an actual alternating, vector-valued, nondegenerate degree-two
source class.  Baumslag rationalization supplies a free rational cover with vanishing degree-two
cohomology and degree-one descent.  Therefore its pulled-back cup has a canonical nonzero
relation-kernel transgression `tau_CW`.

The completed Green defect has one scalar horizontal coefficient `D_rho` in the same resolved
orientation direction.  The decisive open comparison is a divisor-independent chain map proving

```text
transgression(completed Green provenance at rho) = D_rho * tau_CW.
```

Literal Meyer--Poisson boundary exactness must then prove that the left side is zero.  Since
`tau_CW` is nonzero and the coefficient field has characteristic zero, `D_rho = 0`; the existing
frontier theorem then yields RH.

## Anti-circularity gates

- `tau_CW` must be defined before selecting a divisor.
- Its nonzero calibration must come from the existing cup-radical theorem, not from an off-line
  zero.
- The Green comparison must commute with differentials and Gamma/co-Poisson boundary maps.
- Boundary exactness must be proved on the literal source complex, not imposed as vanishing of the
  completed divisor class.
- No positive metric, self-adjoint operator, zero enumeration, or RH-equivalent boundedness may
  supply the first arrow.

## Exact open bridge

Construct a chain-level comparison from the Baumslag relation-kernel transgression of the
Calderon--Witt derived cup to the resolved completed-Xi Green provenance quotient, and prove:

1. coefficient factorization by the existing unsquared horizontal charge;
2. compatibility with the singular prime--Gamma Cauchy boundary;
3. annihilation of the transported class by the actual secondary Meyer--Poisson boundary;
4. independence from prime exhaustion and divisor specialization.

This bridge is the only load-bearing unproved statement in the route.  Proved source, primitive,
transport, incidence, and non-erasure theorems must not be presented as if they prove it.

## Classical-route separation

- **Hilbert--Polya:** asks for a self-adjoint realization whose spectrum contains zeros.  This
  route proves horizontal purity before any spectral realization by killing a source transgression.
- **Weil positivity:** squares or pairs the divisor charge.  This route retains the unsquared
  antidiagonal and uses a nonzero arithmetic calibrator.
- **Connes--Consani--Marcolli:** cyclic or trace consumers see codiagonal shadows.  This route stays
  in the relation kernel before cyclic trace.
- **Sonin/Calkin:** quotient and essential-spectrum methods detect completed boundary classes but
  lose factor provenance.  This route treats their classes as downstream images of one kernel
  character.
- **Deninger:** supplies the closest language--flow, Hodge weight, and Green covariance--but the
  new proof obligation is an explicit arithmetic transgression comparison, not a hypothetical
  cohomology theory or spectral determinant.

## Gates

- [x] identify completed source and Green transport as closed
- [x] identify resolved provenance as the exact retained obstruction
- [x] isolate Baumslag degree-two vanishing and degree-one descent
- [x] formalize canonical relation-kernel transgression and descent criterion
- [x] specialize to alternating Calderon--Witt cup and prove nonzero kernel calibrator
- [ ] construct singular source-to-Green comparison
- [ ] prove literal boundary annihilation after comparison
- [ ] derive RH

## Paper output

- Route paper: `docs/drafts/pipeline/4-publication-ready/riemann-relation-kernel-transgression/main.tex`
- Preview PDF: `output/pdf/riemann-relation-kernel-transgression.pdf`
- Internal claim map: `docs/drafts/pipeline/4-publication-ready/riemann-relation-kernel-transgression/FORMAL_CLAIM_MAP.md`
- Antagonist review: `docs/drafts/pipeline/4-publication-ready/riemann-relation-kernel-transgression/ANTAGONIST_REFEREE_REPORT.md`
