# Xi Newton geometry: forcing line-centered invariant discs

Status: LIVE — source forcing unresolved.
Receiver: `RHTower.XiNewtonCriticalLine.riemannHypothesis_iff_newton_invariant_critical_discs`.
Source module: `formal/GaloisForLFunctions/RHTower/XiNewtonSchwarzPickCriticalLine.lean`.

## Objective and constraints

Derive the receiver's disc coverage for the actual completed Xi function without assuming RH,
zero localization, positivity, or another unproved source property. Corpus-only research;
no external search, novelty audit, numerical experiments, or assumed analytic inputs.
Finished results must have complete paper proofs and individual Lean audits.

## Verified source frontier

The receiver already proves:

- A holomorphic Newton self-map of a disc contains at most one zero of a nonzero entire function.
- Reflection across the critical line transports Newton orbits and zeros.
- Every isolated zero has a small invariant disc centered at that zero, including multiple zeros.
- RH is equivalent both to covering every Xi zero by a line-centered invariant disc and to
  every immediate Xi Newton basin meeting the critical line.
- An immediate basin of a zero right of the critical line stays in that half-plane.

Thus local attraction alone supplies no line-centered coverage. The missing result must force
global incidence with the line or prohibit an off-line attracting component using actual Xi data.

## Active plan

1. Search the whole Lean corpus for Newton geometry, Xi derivative control, horizontal source
   identities, zero-free continuation, and mechanisms that force incidence.
2. State exact competing conjectures and attack them against those results.
3. Extract positive structural content from each obstruction; finish its paper proof before Lean.
4. Audit new modules with `lake env lean`, build only required imports with `--old`, wire finished
   modules into RHTower, run formal lint, remove owned scratch artifacts.
5. Continue from each success or failure toward actual Xi disc coverage.

## Cycle 1: local-to-global disc enlargement

Candidate: the invariant disc supplied at an arbitrary Xi zero can be enlarged or moved until its
center reaches the critical line while preserving holomorphy and self-mapping.

Attack in progress: determine whether derivative poles, a second fixed point, or boundary escape
blocks this continuation, and identify the strongest quantitative positive theorem that survives.

Open core: an unconditional actual-Xi mechanism defeating the first obstruction to line incidence.

## Audit record

Receiver source read in full. No new mathematical theorem or RH proof claimed.
Search inventory reports broad Lean coverage but many source-only declarations; candidate
applicability must be checked by direct Lean audit.
