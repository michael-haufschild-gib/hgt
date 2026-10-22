# TG-C9.4: the literal prime-depth graph core

- **ID:** TG-C9.4-20261001-01a0
- **Stage:** completed research record; canonical card `../../../3-formalized/tg-fourier-jet-prime-graph-core.md`
- **Type:** PROVED AND FORMALIZED
- **Parents:** `tg-fourier-jet-weak-kernel.md`, `../../../5-failed/tg-fourier-jet-bounded-recovery.md`

## Exact missing arithmetic-domain theorem

For each individual prime p, prove that the literal even depth columns are a graph core
for maximal multiplication M by x² on even physical L2. In explicit terms, the closure
of the span of `(e_(p,n), M e_(p,n))` must equal the entire even multiplication graph.
Transport the result to both coordinates of the retained Fourier–jet source. Ordinary
L2 density does not establish this statement; no such implication may be assumed.

This would identify the actual finite prime-depth graph completion inside the maximal-domain
model, and allow testing its neutral recovery against the same even Schwartz vectors.
C9.3's full-carrier negative theorem must also be restricted correctly to the even carrier
before claiming a literal prime-core bounded-recovery obstruction. Odd test directions
cannot be supplied by even prime columns.

## Corpus source and paper mechanism

Documented search: `exponential depth weighted L2 graph core density`.
Actual source read: `HTGeometry/BurnolDepthCompletion.lean`, especially
`ae_eq_zero_of_integer_laplace_moments`, `burnolDepthFeature_eq_coordinate_pow`,
and the proof of `burnolDepthSpan_orthogonal`. `PrimeBurnolDepthCompletion` transports
these exact unsquared columns with nonzero Euler amplitudes; `PrimeBurnolFourierCompletion`
provides the actual even-extension normalization.

The existing moment theorem determines any L1 half-line density from all integer Laplace
samples. If a pair (u,v) annihilates every multiplication-graph column, its moments are
those of

`r exp(-ell r) [u(r)+r² v(r)]`.

This density is L1 by Cauchy–Schwarz, separately using the order-zero and order-two radial
jets. Integer-moment determinacy forces `u+r²v=0` almost everywhere, since the base column
is nonzero on the half-line. The pair then annihilates the entire maximal multiplication
graph. Close the exact graph-span using a genuine Hilbert direct-sum realization or a
continuous-dual separation argument; the default product norm is not silently a Hilbert norm.

An alternative equivalent proof uses weighted L2 with density 1+r⁴ and the same moment
argument. Choose the representation that makes all domain and topology identifications
explicit. No new analytic premise or numeric experiment is needed.

### Direct positive-resolvent construction

The same core equality has a simpler exact proof using positivity of this particular M.
Replace the source column f_n by q_n=(1+r²)f_n=f_n+M f_n. The base q_0 is in L2 by
the already admitted order-zero and order-two jets and is nonzero on the half-line.
The whole family satisfies q_n=exp(-ell r)^n q_0, up to its nonzero literal Euler amplitude.
The existing integer-Laplace moment proof therefore gives dense span of the q_n in plain L2.

Define the bounded graph parametrization

`G h = (h/(1+r²), r²h/(1+r²))`.

Both scalar multipliers are bounded by one. Exact AE multiplication gives
`G q_n=(f_n,M f_n)` and `G(f+M f)=(f,M f)` for every f in the maximal domain.
Continuity of G and density of q_n show that the graph-span closure contains the whole
maximal graph. The reverse inclusion follows from the already available closedness of
maximal real multiplication. This avoids introducing a Hilbert structure on the default
product norm or a new weighted-measure equivalence. It proves the same hard domain equality.

First formalize this on the actual half-line source, then transport with the proved even
extension and its exact multiplication covariance. The even-carrier restriction of the
bounded-recovery obstruction remains an explicit additional step.

### 2026-10-02 proof implementation checkpoint

Direct corpus search `positive multiplication resolvent graph core exponential depth dense`
returned partial results (reranking deadline), including the existing bounded multiplier
and maximal multiplication resolvent mechanisms. Source inspection confirms the required
Laplace moment theorem, literal order-two jets, and exact even-extension normalization.

The implemented half-line family is explicitly
`A_(p,n)^(-1) • (literalColumn_(p,n) + literalRadialJet_(p,n,2))`.
Its representative is the real function `(1+r²)r exp(-(n+1)log(p)r)`; no Euler amplitude
is discarded in the later transport. Orthogonality gives integer Laplace moments against
the nonvanishing weighted base. The physical graph parametrization can be written with
only one bounded multiplier: `G h=(B h,h-B h)`, `B=(1+M)^(-1)`.
This implements the same exact domain proof without a second rational multiplier.
Lean verification completed: production leaf and all three public axiom audits pass.
The canonical stage3 card records the exact statements and audit. The separate even-source
obstruction is now also proved, via exact Hermite parity and this graph-core theorem:
`../../../5-failed/tg-fourier-jet-even-bounded-recovery.md`. No full-domain restriction shortcut
is used.

## Remaining TG target

Even successful core identification and recovery classification do not construct the
Gamma–Xi comparison, Hardy-index transfer, or sub-unit source action. They settle whether
this particular retained-jet carrier preserves the actual arithmetic domain needed for
those hard producer questions. The next proof must attack this exact domain equality,
not merely restate ordinary density or choose a more convenient source family.
