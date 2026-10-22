# HB optical cancellation local analytic-branch obstruction

- **ID:** HC77
- **Stage:** 3-formalized
- **Type:** THEOREM / LEAN-PROVED LOCAL BRANCH-DOMAIN NO-GO / HARD FRONTIER
- **Routes:** HB, FZZ-P, PW-B; RBH comparison
- **Source:** HC74--HC76 scalar cancellation profile; corpus analytic identity machinery;
  exact rational profile formula
- **Statement:** No scalar function holomorphic on any nonempty open subdomain of the critical
  strip can equal the exact optical-cancellation profile there. Thus branch cuts or nonisolated
  singular sets do not help if even one open analytic branch still obeys pointwise cancellation.

## Corpus-led conjecture

HC76 removes all isolated meromorphic poles, but a scalar Green response could retain branch cuts or
other nonmeromorphic singular sets. Such responses are nevertheless holomorphic on open branch
domains. The next exact question is local: can one analytic branch agree with the horizontal
cancellation profile on one nonempty open patch?

Corpus search supplies vertical-accumulation identity rigidity on holomorphic domains and the exact
rational HC74 profile. Construct the profile's coefficient-faithful complex rational continuation
on the full open strip. If a local holomorphic branch equals the horizontal profile, a vertical
zero sequence forces that branch to be locally constant. Horizontal points in the same ball then
force the rational continuation to be constant on a real interval; its own identity theorem makes
it constant on the full strip, contradicting the already-proved distinct quarter and half values.

## Why this is frontier-level

This attacks the nonmeromorphic branch-domain survivor, not a bound. Success would show that no
piecewise-holomorphic scalar coefficient can erase the HB radial--temporal--chiral triangle on any
open frequency region. A viable completion must therefore abandon pointwise scalar cancellation on
every analytic branch, become antiholomorphic/support-discontinuous/operator-valued, or derive a
different full augmented-source law.

This does not derive the complete augmented Einstein coefficient, exclude equality only on the Xi
divisor, or rule out genuinely distributional/operator-valued response without open scalar branch
domains.

## Hostile checks

- Domain is arbitrary nonempty open subset of the critical strip; no connectedness premise.
- Prove exact complex rational continuation and literal specialization on the real axis.
- Use a ball inside the domain for local identity; do not assume global branch connectivity.
- Prove global nonconstancy from existing exact quarter/half theorem, not numerical sampling.
- Pointwise equality is imposed only on the chosen open branch.
- No computations, estimates, added axioms, or frontier-map edits.

## Novelty boundary as of 2026-08-28

Mandatory corpus search found the global HC74 strip theorem, a different local holomorphic defect
compensator obstruction, and general analytic identity tools, but no local-branch theorem for the
exact HB optical profile and no coefficient-faithful complex continuation of it. Bounded
primary-source audit covered Casals--Ottewill's pole/branch-cut Green decomposition
(arXiv:1205.6592), Green et al.'s Kerr QNM residues (arXiv:2210.15935),
Lestingi--Sberna--Green's continuous-spectrum framework (arXiv:2607.19492), and Su et al.'s
direct/QNM/tail Kerr decomposition (arXiv:2608.17943). No audited source states this exact local
analytic-branch obstruction. Bounded, not exhaustive, priority claim.

## Gates

- [x] 0 -> 1 in-progress: corpus gap, exact conjecture, hostile proof route, bounded literature audit
- [x] 1 -> 2 fully-proven: dependency-closed paper proof
- [x] 2 -> 3 formalized: closed Lean theorem, target build, axiom/lint audit, umbrella wire
- [ ] 3 -> 4 publication-ready: independent priority audit and standalone exposition

## Log

- 2026-08-28 — Opened from HC76's branch/nonmeromorphic survivor. Frontier map remains read-only.
- 2026-08-28 — First conjecture: complexify exact profile, prove full-strip analyticity and real
  specialization, then combine local vertical and global horizontal identity theorems.
- 2026-08-28 — First conjecture succeeded in scratch Lean. Constructed exact complex rational
  continuation, proved its denominators nonzero and the continuation analytic throughout the strip,
  proved literal real specialization, and closed the arbitrary-open-domain no-go through two
  accumulation/identity arguments.
- 2026-08-28 — Formalized in
  `ThetaCuspHawkingPreDivisorOpticalCancellationLocalAnalyticBranchNoGo.lean`. Direct
  `lake env lean` passed; target-only
  `lake build GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingPreDivisorOpticalCancellationLocalAnalyticBranchNoGo`
  passed (`12141/12141`). All three exported theorem axiom audits report only `propext`,
  `Classical.choice`, and `Quot.sound`; umbrella import present. Formal lint reports no finding in
  this module and remains nonzero only for unrelated unreachable modules in the shared worktree.
