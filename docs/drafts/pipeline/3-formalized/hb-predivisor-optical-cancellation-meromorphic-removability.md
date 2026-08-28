# HB pre-divisor optical-cancellation meromorphic removability obstruction

- **ID:** HC75
- **Stage:** 3-formalized
- **Type:** THEOREM / LEAN-PROVED MEROMORPHIC REMOVABILITY CLASSIFICATION / HARD FRONTIER
- **Routes:** HB, FZZ-P, PW-B; RBH comparison
- **Source:** HC74 pre-divisor optical-cancellation profile; corpus theorem
  `MeromorphicAt.analyticAt`
- **Statement:** Any meromorphic scalar function on the open critical strip that equals the finite
  optical-cancellation profile at every strip point is automatically holomorphic there, hence
  cannot exist by HC74.

## Corpus-led conjecture

HC74 proves that the unique scalar cancellation profile is finite, continuous, horizontal, and
nonconstant throughout `0 < Re(s) < 1`, and that no holomorphic scalar function can track it there.
The next natural HB escape is meromorphic frequency dependence, motivated by Green poles and QNM
resolvents.

Lean-corpus search exposes the exact hard mechanism: `MeromorphicAt.analyticAt` upgrades a
meromorphic function to analytic at every point where it is continuous. Pointwise equality to the
explicit optical profile on the whole strip forces local equality to a continuous function, so
every alleged pole is removable. The function is therefore analytic on the entire strip, directly
contradicting HC74.

## Why this is frontier-level

This closes the first singular scalar fork left open by HC74. Meromorphic notation alone does not
save a source-global cancellation law when the law prescribes a finite value at every frequency:
all poles are forced removable. Any surviving HB/FZZ-P/PW-B completion must genuinely leave the
everywhere-finite scalar class by failing at actual strip points, developing nonisolated/branch-cut
singular structure, depending antiholomorphically, changing support domains, or becoming
operator-valued.

This does not exclude a partially defined meromorphic coefficient with genuine poles, a
divisorwise interpolant, or a Green operator whose singular support changes with frequency. It
classifies exactly why the naive meromorphic relaxation of the HC74 profile is no relaxation.

## Hostile checks

- Use `MeromorphicOn` on the open strip, not global meromorphy or rationality.
- Derive continuity locally from exact equality to the profile; never assume continuity separately.
- Prove profile continuity from its exact rational formula and strip denominator nonvanishing.
- Preserve pointwise equality on every strip point; do not strengthen a discrete Xi equality into a
  uniqueness-set claim.
- Export a positive removability theorem as well as the existential no-go.
- No numerical estimates, asymptotics, computations, added axioms, or frontier-map edits.

## Novelty boundary as of 2026-08-28

Mandatory corpus searches found `MeromorphicAt.analyticAt` and the HC74 optical profile, but no
theorem applying removable-singularity rigidity to this HB cancellation law. Bounded primary-source
audit covered Casals--Ottewill's pole/branch-cut decomposition of the Schwarzschild Green function
(arXiv:1205.6592), Green et al.'s Kerr QNM Green-function residue construction
(arXiv:2210.15935), Lestingi--Sberna--Green's all-order QNM perturbation framework with explicit
continuous-spectrum terms and divergent QNM sums (arXiv:2607.19492), and Su et al.'s Kerr
Green-function decomposition with direct, QNM, and tail sectors (arXiv:2608.17943). These sources
confirm that genuine poles and branch cuts are physically natural; no audited source states the
exact optical-profile removability classification or its resulting scalar no-go. Bounded, not
exhaustive, priority claim.

## Gates

- [x] 0 -> 1 in-progress: corpus gap, exact conjecture, hostile proof route
- [x] 1 -> 2 fully-proven: dependency-closed paper proof
- [x] 2 -> 3 formalized: closed Lean theorem, target build, axiom/lint audit, umbrella wire
- [ ] 3 -> 4 publication-ready: independent priority audit and standalone exposition

## Log

- 2026-08-28 — Opened from HC74's singular/non-holomorphic survivor. Frontier map remains read-only.
- 2026-08-28 — Corpus search identified the exact removability bridge
  `MeromorphicAt.analyticAt`: meromorphicity plus local continuity forces analyticity at each strip
  point. Bounded primary-source audit completed.
- 2026-08-28 — First conjecture survived direct Lean attack. Proved continuity of the exact rational
  cancellation profile on the open strip from positivity of both horizon shifts, promoted any
  everywhere-equal meromorphic response to `AnalyticOnNhd`, and reduced no-existence to HC74.
- 2026-08-28 — Formalized in
  `ThetaCuspHawkingPreDivisorOpticalCancellationMeromorphicRemovability.lean`. Direct
  `lake env lean` passed; target-only
  `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingPreDivisorOpticalCancellationMeromorphicRemovability`
  passed (`12139/12139`). All three exported theorem axiom audits report only `propext`,
  `Classical.choice`, and `Quot.sound`; umbrella import present. Formal lint reports no finding in
  this module and remains nonzero only for unrelated unreachable modules in the shared worktree.
