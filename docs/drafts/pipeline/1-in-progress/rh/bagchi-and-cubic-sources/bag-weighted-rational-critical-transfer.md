# BAG weighted rational cubic to the compact-test boundary

- **ID:** BAG-C28.56ac, exact weighted/tested statements formalized.
- **Route:** BAG; actual rational source to the arithmetic boundary.
- **Prior contribution:** C28.56ab proves full balanced rational sums and
  dilation orthogonality. C28.56aa proves the actual arithmetic compact-test
  boundary. Neither alone identifies the frequency-weighted rational series.

## Conjecture and paper proof

For sigma>1, multiply the actual cubic coefficient Gamma_sigma(a,b) by
a^(-alpha)b^(-beta), with Re(alpha)=Re(beta)=0. Positive rational powers
have modulus one, so the COMPLETE unordered sum has exactly the balanced
absolute mass from C28.56ab. No frequency or signed sector is discarded.

The positive-rational prime-valuation equivalence identifies each character
with the finite product of prime characters. Positivity makes multiplication
and integer powers compatible with the principal complex power. Therefore
each rational summand equals the existing weighted local product, exactly.

For each finite prime set the support cutoff sum equals the existing
weightedTrace. The complete absolute sum dominates every cutoff. Tannery
and uniqueness of limits identify the full rational sum with the six-zeta
expression already proved in C28.56y. Apply the same argument to the square
energy row to identify each rational axis with its two-zeta transform.
Literal inclusion-exclusion then identifies exclusion of a=1 and b=1 with
the complete weighted arithmetic connected kernel.

The stronger tested statement is also targeted: for ANY integrable frequency
test Phi, dominate every rational summand by |Gamma_off(a,b)|*|Phi(u,v)|.
This bound is summable in the rational pair and its sum is integrable in
frequency. Series dominated convergence therefore proves an actual HasSum
of the termwise integrals, equal to the integral of the connected kernel.
For a fixed smooth compact test, C28.56aa then gives the full critical
boundary of this tested rational series. This still does not prove a
finite-height physical approximation or allow growing tests as damping moves.

## Corpus audit

Search25978: weighted cubic rational Mellin character prime support limit,
deep300, partial due to malformed local-model judging JSON. Full source
inventory65498/65498; compiler enrichment predominantly pending/source-only.
All candidate/source/proof/ingredient sections inspected. The useful returned
actual rational source is rationalCubic; unrelated cubic matrix and aperture
lemmas do not prove this transfer. Direct source inspection also uses the
audited WeightedCubicTrace, WeightedCubicContractions, RationalCubicTrace and
CubicCriticalBoundary. New mathlib power APIs are checked in a scratch probe.

## Checked weighted-series stage

Scratch15757 and production35695 passed without diagnostics. Production
ChiRamanujanWeightedRationalTrace uses lake --old env lean with explicit olean;
it is wired into RHTower. It proves the COMPLETE weighted positive-rational
cubic six-zeta sum, its exact frequency-independent absolute mass, and both
literal rational-axis two-zeta transforms. No abstract replacement coefficient
or unproved summability premise. New complex-power APIs checked in the scratch.

The second leaf, exact mask and termwise tested boundary, passed production85951
without diagnostics. Its domination uses actual |Gamma_off|*|Phi|. Both leaves
are wired. Exact statements and proof: P3 bag-weighted-rational-critical-boundary.
Lexical search43777 for
integral_tsum/summable_integral_norm returned the corpus's existing Bochner
interchange lemmas; direct source inspection supplies the stronger HasSum
dominated-convergence API. Axiom61723 passed for all27 public theorems, only
standard logical axioms. Index93281 passed with all27 API entries. Lint51208
reports15 unrelated unreachable modules, no new-leaf/proof-debt error.
Owned scratch probes cleaned after audits; source leaves and evidence logs retained.

## Hard frontier after this conjecture

Actual all-order global source derivatives are now closed in C28.56ad.
Full Schwartz critical boundary and uniform seminorm control are C28.56ae
(P1 bag-global-cubic-source-growth). Physical prime contraction matching,
noncompact/growing tests,
finite-height near-resonances and coupled damping/band limits; then growing
moments, moving cofactors and positive common-height self-return. RH unproved.
