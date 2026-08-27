# Reflected bi-heat source-normalization classification

- **ID:** RBH-SNC
- **Stage:** 3-formalized
- **Type:** CLASSIFICATION + NO-GO + EXACT RECEIVER
- **Parent:** RBH
- **Statement:** `[LEAN-PROVED] [NEW] [CLASSIFICATION] [NO-GO]` Fixed linear RBH scale reporters split exactly into reflection-even reporters, blind at every point, and nonzero reflection-odd reporters, whose equality locus is critical wall. Common nonzero normalization of actual multiplicity-leading jets cannot alter balance locus.

## Goal

Classify source normalizations capable of turning RBH reflection symmetry into top-channel balance.
Close all fixed linear scale-order and common-scalar normalization attempts without assuming divisor
location, and retain strongest oriented survivor.

## Gates

- [x] 0 → 1 in-progress: classification frozen after corpus search
- [x] 1 → 2 fully-proven: exact reflection defect and common-normalization cancellation proved
- [x] 2 → 3 formalized: direct Lean, targeted build, umbrella, axiom audit
- [ ] 3 → 4 publication-ready: external priority review

## Exact frozen claims

For fixed real weights `a,b`, define

`F_(a,b)(z) = a L(z) + b R(z)`,

where `L(z)=(Re z-1)/2` and `R(z)=-Re z/2` are exact RBH scale orders. Then

`F_(a,b)(z)-F_(a,b)(1-z) = (a-b)(Re z-1/2)`.

Hence reflection equality holds iff `a=b` or `Re z=1/2`. If `a≠b`, universal equality on Xi
divisor support is exactly RH. Separately, multiplying both actual first surviving jets by any
common `c≠0` preserves their norm-equality locus exactly.

## Complete paper proof

Reflection exchanges `L` and `R`; direct subtraction yields `(a-b)(L-R)`, while exact RBH scale
tomography gives `L-R=Re z-1/2`. Zero-product classification gives complete equality locus. For
actual top jets, multiplicativity of norm gives common positive factor `|c|`; cancellation reduces
to established coefficient-free top-jet balance, equivalent pointwise to critical-wall membership.
Existing Xi-support endpoint yields global RH equivalence for every `a≠b`.

## Hostile review and novelty verdict

- This does not produce RBH balance; asymmetric reporter equality remains exactly RH.
- Symmetric fixed weights do produce unconditional reflection equality, but are identically blind.
- Any common coefficient, multiplicity factor, Fisher residue factor, or other nonzero scalar source
  normalization cancels and cannot repair off-wall scale imbalance.
- Corpus search found exact RBH scale exchange and top-jet balance, plus reflection-even prime-mass
  blindness and squarefree Fisher multiplicity residue, but no classification of full fixed linear
  normalization class or theorem for arbitrary common normalization.
- Novelty is structural closure of this normalization class, not novelty of elementary two-variable
  algebra in isolation.

Verdict: algebraic ingredients `[REDISCOVERED]`; RBH source-normalization classification and no-go
`[NEW] [CLASSIFICATION]`, external priority provisional.

## No-go closure

- **Exact killing mechanism:** fixed linear reporter has no reflection defect beyond
  `(a-b)(Re z-1/2)`; common nonzero scaling cancels from actual jet balance.
- **Strongest positive survivor:** antisymmetric quotient is unique one-dimensional oriented
  horizontal coordinate; every `a≠b` is exact wall receiver, including arbitrary Xi multiplicity.
- **New insight:** RBH producer cannot be common/even normalization. It must create relative channel
  transport before taking norms, or supply sign/phase-sensitive cross-channel incidence.
- **Status:** dependency-closed paper proof and Lean formalization complete. Remaining RBH open core
  is source-first relative/oriented law forcing equality, not normalization choice.

## Lean formalization

- Module:
  `formal/GaloisForLFunctions/RHTower/ReflectedBiHeatSourceNormalizationClassification.lean`
- Reflection defect: `reflectedBiHeatLinearScaleReporter_reflectionDefect`
- Complete equality classification: `reflectedBiHeatLinearScaleReporter_eq_reflection_iff`
- Common-normalization cancellation:
  `reflectedBiHeatCommonNormalizedLeadingJetNorms_two_eq_iff`
- Global exact receiver:
  `riemannHypothesis_iff_reflectedBiHeatLinearScaleReporter_eq_reflection`
- Direct `lake env lean` passed.
- Targeted build
  `lake build GaloisForLFunctions.RHTower.ReflectedBiHeatSourceNormalizationClassification`
  passed (`11455/11455`).
- `#print axioms`: only `propext`, `Classical.choice`, `Quot.sound`.
- Umbrella import wired in `formal/GaloisForLFunctions/RHTower.lean`.

## Log

- 2026-08-27 — conjectured from corpus scale-order exchange, multiplicity-leading balance, and
  reflection-even source blindness.
- 2026-08-27 — classification, no-go, exact survivor, global endpoint, and Lean proof completed.
