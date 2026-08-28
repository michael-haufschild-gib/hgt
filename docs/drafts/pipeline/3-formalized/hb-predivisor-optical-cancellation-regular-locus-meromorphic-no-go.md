# HB optical cancellation on the meromorphic regular locus

- **ID:** HC76
- **Stage:** 3-formalized
- **Type:** THEOREM / LEAN-PROVED GENUINE-POLE REGULARIZATION CLASSIFICATION / HARD FRONTIER
- **Routes:** HB, FZZ-P, PW-B; RBH comparison
- **Source:** HC74--HC75 pre-divisor cancellation obstruction; corpus theorem
  `MeromorphicAt.eventually_analyticAt`; punctured-neighbourhood congruence of meromorphic germs
- **Statement:** No meromorphic scalar response on the open critical strip can equal the exact
  optical-cancellation profile merely on its analytic locus; arbitrary pole values do not help,
  because canonical regularization at every pole is analytic and recovers the forbidden HC74
  profile everywhere.

## Corpus-led conjecture

HC75 excludes a meromorphic function only when equality is imposed at every point, including Lean's
arbitrary total-function values at poles. Physical Green coefficients normally impose an equation
only where the response is regular. The exact remaining question is therefore whether genuine
isolated poles can hide the nonholomorphic cancellation law.

Corpus search supplies the key stronger mechanism. `MeromorphicAt.eventually_analyticAt` says every
meromorphic germ is analytic on a punctured neighbourhood. Define the canonical analytic-locus
regularization of `f` against a continuous profile `p` by retaining `f` where it is analytic and
using `p` elsewhere. If `f = p` at every regular point, then the regularization equals `f` on every
punctured meromorphic germ, hence remains meromorphic, while it equals the continuous profile on a
whole neighbourhood. `MeromorphicAt.analyticAt` then removes every pole simultaneously.

Prove this as a general theorem for an arbitrary open set and continuous profile, then apply HC74.

## Why this is frontier-level

This attacks the genuine singular fork left by HC75, not a numerical bound. It shows that isolated
Green/QNM poles cannot rescue source-global scalar cancellation even when the physical equation is
required only at regular frequencies and pole values are wholly unconstrained. The survivor is
sharp: an HB completion must lose meromorphy itself (branch/nonisolated singularity), lose a dense
regular-locus cancellation law, change support domains, depend antiholomorphically, or become
operator-valued.

It still does not derive the complete augmented Einstein coefficient, exclude divisorwise
interpolation, or rule out branch cuts and operator-valued singular response.

## Hostile checks

- Hypothesis may constrain `f` only at points satisfying `AnalyticAt`; never prescribe pole values.
- Prove a general open-set regularization theorem, not only the final negation.
- Use punctured-neighbourhood meromorphic congruence; do not assume poles are finite/countable.
- Derive continuity of the regularized function from continuous profile equality on the open set.
- Preserve `MeromorphicOn` on the open strip; no global rationality or finite-pole premise.
- No computations, estimates, added axioms, or frontier-map edits.

## Novelty boundary as of 2026-08-28

Mandatory corpus searches found HC75, `MeromorphicAt.eventually_analyticAt`, and meromorphic-germ
punctured congruence, but no analytic-locus regularization theorem and no application to the HB
optical profile. Bounded primary-source audit covered Casals--Ottewill's Green-function pole/branch
cut decomposition (arXiv:1205.6592), Green et al.'s Kerr QNM residue construction
(arXiv:2210.15935), Lestingi--Sberna--Green's continuous-spectrum/incomplete QNM framework
(arXiv:2607.19492), and Su et al.'s Kerr direct/QNM/tail decomposition (arXiv:2608.17943). These
sources motivate genuine regular-locus equations and nonmeromorphic survivors but do not state this
exact regularization theorem or optical no-go. Bounded, not exhaustive, priority claim.

## Gates

- [x] 0 -> 1 in-progress: corpus gap, exact conjecture, hostile proof route, bounded literature audit
- [x] 1 -> 2 fully-proven: dependency-closed paper proof
- [x] 2 -> 3 formalized: closed Lean theorem, target build, axiom/lint audit, umbrella wire
- [ ] 3 -> 4 publication-ready: independent priority audit and standalone exposition

## Log

- 2026-08-28 — Opened from HC75's arbitrary-pole-value scope gap. Frontier map remains read-only.
- 2026-08-28 — Corpus-led first conjecture: canonical analytic-locus regularization should turn any
  meromorphic regular-locus solution of a continuous profile into an analytic everywhere solution.
- 2026-08-28 — First conjecture succeeded in scratch Lean. Proved the general open-set
  regularization theorem using `MeromorphicAt.eventually_analyticAt`, punctured-germ congruence,
  local continuous-profile equality, and `MeromorphicAt.analyticAt`; specialized it to contradict
  HC74 without constraining any pole value.
- 2026-08-28 — Formalized in
  `ThetaCuspHawkingPreDivisorOpticalCancellationRegularLocusMeromorphicNoGo.lean`. Direct
  `lake env lean` passed; target-only
  `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingPreDivisorOpticalCancellationRegularLocusMeromorphicNoGo`
  passed (`12140/12140`). All three exported theorem axiom audits report only `propext`,
  `Classical.choice`, and `Quot.sound`; umbrella import present. Formal lint reports no finding in
  this module and remains nonzero only for unrelated unreachable modules in the shared worktree.
