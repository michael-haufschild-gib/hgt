# Sharp-window convergence of the complete nodal defect

- **ID:** chmd-sharp-window-nodal-convergence
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper; Lean pending)
- **Statement:** Symmetric sharp interval restrictions converge strongly to the identity on the full maximal CHMD graph. They commute with positive part, negative part and modulus. The complete signed nodal cross-pairing, Weil energy and oneL defect therefore converge along these exact-support restrictions.

## Route and contribution

The route is complete odd theta–Doob positivity, hence RH. Reflected-prime
collar payment, the primitive half-Rayleigh bound and the oneL-defect
inequality remain open. This theorem discharges the localization premise:
every maximal state and both of its nodal lobes can be approximated in
the complete graph norm by their literal restrictions to finite windows.
There is no smoothing collar, altered lobe or missing prime tail.

## Dependency-closed paper proof

Let `C_n p` have source `1_[-n,n) p.fst`. The sharp spatial cut theorem
constructs this actual graph vector and supplies a common operator-norm
bound `||C_n|| <= M`, independent of `n`.

For a compact C2 source `v`, compact support supplies a radius `a`.
Whenever `n>a`, its interval restriction equals `v` everywhere. Source
injectivity therefore gives `C_n(compactLift v)=compactLift v`. The
literal compact C2 graph tests are dense in the full maximal graph.
Given `p` and a nearby compact test `q`,

```
||C_n p-p|| <= M ||p-q|| + ||C_n q-q|| + ||q-p||.
```

First choose `q`, then use its eventual exact fixation. This proves
`C_n p -> p` in full graph norm.

Since the interval indicator takes only values zero and one,
`C_n(posGraph p)=posGraph(C_n p)` pointwise in the source coordinate.
The same equality holds for negative part and modulus. All vectors are
already admitted; source injectivity promotes these identities to full
graph equalities. Applying the strong convergence theorem separately to
the three fixed nodal vectors proves their simultaneous convergence.
The symmetric interval indicator is reflection invariant almost
everywhere, so source injectivity also proves that each window preserves
odd parity. Endpoint values lie in a null set for the actual mass measure.

The signed pairing is the difference of the edge and source Hilbert
pairings. Thus it is jointly continuous in graph norm. The oneL moment
is a continuous source functional and the full Weil form is a continuous
quadratic form. Consequently

```
sourcePair (posGraph (C_n p)) (negGraph (C_n p))
  -> sourcePair (posGraph p) (negGraph p),
2 <(absGraph (C_n p)).fst,oneL>^2
  -> 2 <(absGraph p).fst,oneL>^2,
weilForm (C_n p) -> weilForm p.
```

The same holds for their difference, retaining precisely the unpaid
oneL-defect quantity. For every positive integer radius, the supported
maximal-domain theorem places the localized vector and its nodal lobes
in the exact aperture completion. No sign assumption enters this proof.

## Corpus inputs

- `CHMDSharpSpatialCut`: literal full-graph cuts and their uniform bound.
- `CHMDFullJumpCoreDensity.dense_compactTests`: dense actual compact C2 tests.
- `HTGeometry.StrongConvergenceDense.tendsto_of_dense_of_uniform_bound`:
  the existing epsilon argument for uniformly bounded operators.
- `CHMDBeurlingDenyNodalDecompositionAndParityBoundStateSpaces`: actual
  nodal contractions and source representatives.
- `CHMDPolarTransfer.continuous_weilForm`: continuity of the complete
  signed Weil form, including both polar coordinates.
- `CHMDSupportedApertureDomain`: exact supported maximal graph domain.

## Gates

- [x] Dependency-closed paper proof.
- [x] Lean strong convergence and exact nodal commutation.
- [x] Lean convergence of the complete signed defect.
- [ ] Candidate and actual repository leaf checks.
- [ ] Standard-axiom audit, umbrella import and scratch cleanup.

No global sign, RH conclusion or external novelty claim is asserted.

## Lean declarations and verification

Module: `GaloisForLFunctions.RHTower.CHMDSharpWindowNodalConvergence`.

- `tendsto_sharpIntervalGraph`: complete graph-norm convergence.
- `sharpIntervalGraph_fst_mem_oddSector`: exact preservation of odd parity.
- `sharpIntervalGraph_posGraph`, `sharpIntervalGraph_negGraph`,
  `sharpIntervalGraph_absGraph`: exact nodal commutation.
- `tendsto_weilForm_sharpIntervalGraph`: complete signed Weil-form limit.
- `tendsto_sourcePair_nodal_sharpIntervalGraph`: complete nodal-pairing limit.
- `tendsto_oneL_defect_sharpIntervalGraph`: convergence of the entire signed
  defect, including its squared ground-state moment.

Candidate check passed. All eight declarations above were audited with
`#print axioms`: only `propext`, `Classical.choice`, `Quot.sound` occur.
The repository leaf check and temporary-file cleanup remain pending.
