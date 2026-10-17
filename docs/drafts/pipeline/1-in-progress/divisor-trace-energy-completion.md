# Energy completion of arbitrary divisor traces

- **ID:** divisor-trace-energy-completion
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Statement:** Identify the physical closure of arbitrary-family integer-hat
  extensions through exact component conservation laws, and construct the
  completed trace domain when the ℓ² trace inverse is unbounded.

The run-gap classification exposes a concrete missing object: nonclosed range
does not describe which physical velocities are admitted by its completion.
Work with the actual unit-cell synthesis S and active-edge graph on ℕ, whose
edge k--(k+1) is present precisely when node k+1 is in the divisor union.

Candidate classification: closure(range E_A) consists exactly of S(w), w∈ℓ²,
whose coefficient sum vanishes on every finite connected component of this
cell graph. The orthogonal complement inside the cellular space consists of
ℓ² sequences constant on each component; an infinite-component constant must
vanish. Make all components, sums and infinite-component statements explicit.
Keep the ambient physical orthogonal complement outside the cellular range.

Construct the corresponding energy-complete trace space from locally defined
cumulative sums with square-summable discrete gradient. Recover the existing
ℓ² trace space exactly in the bounded-run regime; when runs are unbounded,
produce actual completion elements that have no ℓ² trace preimage. For the
full family D=ℕ, the expected closure is the unit-cell span from index1 onward.

This would turn the nonclosed-range obstruction into a constructive continuum
domain, and prepare a domain-level comparison with the multiplicative graph.
No full SourceGraph identification, unweighted logarithmic H1 or affine-unitary
claim is justified. Dependency-closed paper proof is now in
`docs/reports/BiScaleUncertainty/DivisorTraceEnergyCompletion.md`, written before
the five Lean leaves. Formal verification remains pending; not yet counted.

Formal scope: CellPrefixHilbert, DivisorCellConstraints, DivisorGradientClosure,
DivisorEnergyCompletion, FullDivisorEnergyEscape. The last leaf constructs
finite linear ramps with exact squared physical error 1/(n+1), addressing the
producer requirement while retaining the continuum coprime-shear topic.

Verification gates:
- [x] Dependency-closed paper proof and prior corpus/primary-source audit.
- [x] CellPrefixHilbert, DivisorCellConstraints, DivisorGradientClosure: direct
  leaf checks pass with empty logs and normal compiled outputs.
- [ ] Physical completion/recovery and explicit full-family ramp leaf checks.
- [ ] Exact all-declaration axiom audit, principal signatures, umbrella/index/lint.
- [ ] Certify once as package15, update facts and memory, retain next conjecture.

Plan: identify the closure by zero cumulative sums at inactive nodes; prove
equivalence to finite-component conservation; construct the complete physical
cell domain and its cumulative traces; classify exact ℓ² recovery and produce
missing preimages in the unbounded-run case; audit every new leaf and declaration.
Key proof candidate: orthogonal residuals are constant along active edges.
Combined with zero cumulative traces, finite components force that residual to
vanish; an infinite constant tail vanishes by ℓ² decay. This can avoid assuming
an abstract spectral or domain-identification interface.

Initial lexical corpus query: `integerHat closed span range completion`,
BiScaleUncertainty filter with `--any`; all20 declarations and5 exploration
hits inspected. Existing single-grid closed-span and integer-hat identities
are useful. New run-gap draft declarations already appear in the source index
and must not be mistaken for independently certified results. No matching
component-completion classifier appeared. Lexical output supplies no semantic
coverage or compiler certification; no external novelty conclusion follows.
