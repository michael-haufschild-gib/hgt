# LI infinite critical-amplitude Schatten boundary

- **ID:** LI-INF-AP
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md` · route LI, completed-Abel interior-current branch
- **Statement:** At critical squared mass `v = 1/4`, multiplicity-ordered positive Xi ordinates
  `gamma_n` induce exact critical-current amplitudes `gamma_n / (gamma_n^2 + 1/4)`. This sequence
  belongs to every `ell^p`, `p > 1`, but not to `ell^1`; consequently no multiplicity-ordered
  critical realization has an absolutely summable endpoint amplitude packet.

## Goal

Kill LI's last finite-packet/Bohr-almost-periodic extrapolation. Exact RH chain under attack:

`all interior currents nonzero -> RH -> every divisor copy is critical -> full current is an
infinite positive sine packet -> Bohr recurrence/sign change`.

Finite-packet sign change is already Lean-proved. Extending it requires summable amplitudes. This
card proves that required premise is false at exact critical mass, so no `ell^1` almost-periodic
extension can close LI. Surviving LI mechanism must retain zero-density continuum accumulation at
frequency zero; it cannot uniformly approximate the full current by finite critical packets.

## Gates

- [x] 0 -> 1 in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 -> 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 -> 3 formalized: Lean theorem, targeted `lake build` green, axiom audit PASS
- [ ] 3 -> 4 publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach

**[PROVED HERE]** Let `gamma_n` be corpus's generalized inverse of the multiplicity-sensitive Xi
zero count. Direct critical-line resolvent and trigonometric reduction gives exact amplitude

`a_n = gamma_n / (gamma_n^2 + 1/4)`.

All ordinates exceed one, so

`1/gamma_n <= 2 a_n <= 2/gamma_n`.

Corpus's exact trace-class RVM relocation says the actual reciprocal sequence differs absolutely
summably from its smooth RVM model. The model reciprocal is not summable, hence neither is
`1/gamma_n`; comparison proves `a` is not summable. Conversely `a_n <= 1/gamma_n`, and the ordered
Xi reciprocal operator belongs to every Schatten class above one, so `sum a_n^p` converges for
every real `p > 1`. No numerical zero data enter.

## No-go closure

- **Exact killing theorem/mechanism:**
  `not_exists_summable_liEvenCross_fullCriticalEndpointAmplitude` proves no ordered critical-copy
  realization of all positive Xi ordinates has summable endpoint amplitudes. Therefore the
  summable pure-point hypothesis needed to pass finite Bohr recurrence to the full divisor is
  false.
- **Strongest positive survivor:**
  `liEvenCrossOrderedEndpointAmplitude_schattenBoundary` proves the exact boundary: amplitudes are
  in every `ell^p`, `p > 1`, but not `ell^1`. The infinite packet is conditionally regular, not an
  uncontrolled divergent object.
- **New insight:** finite critical prefixes fail because they delete the nonuniform amplitude mass
  responsible for the Riemann--von Mangoldt `log T` divergence.
- **Status:** dependency-closed paper proof and Lean proof in
  `GaloisForLFunctions.RHTower.LiEvenCrossInfiniteCriticalAmplitudeSchattenBoundaryNoGo`.
  Targeted build PASS; axiom audit `[propext, Classical.choice, Quot.sound]`; global lint reaches
  only unrelated umbrella-unreachability failures outside this module.

## Novelty audit

Corpus search found finite-packet oscillation, sublinear-tail repair no-go, coefficient-recovering
regularization no-go, Riemann--von Mangoldt counting, and fixed-mode flux summability, but no exact
critical-amplitude `ell^1` obstruction. Primary Li-criterion and complete-monotonicity literature
audited in this campaign does not state this completed-Abel amplitude boundary.

## Log

- 2026-08-29 — created in 1-in-progress from failed `LI-INF-AP` Bohr-extension conjecture.
- 2026-08-29 — exact atom formula, sharp `ell^p/ell^1` boundary, and closed ordered-realization
  no-go formalized; moved to 3-formalized.
