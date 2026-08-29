# LI infinite critical-amplitude Schatten boundary

- **ID:** LI-INF-AP
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `rh-current-frontier-map.md` · route LI, completed-Abel interior-current branch
- **Statement:** At critical squared mass `v = 1/4`, multiplicity-ordered positive Xi ordinates
  `gamma_n` induce amplitudes `gamma_n / (gamma_n^2 + 1/4)` which are not summable, although every
  fixed-mode completed flux is summable.

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
- [ ] 1 -> 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 -> 3 formalized: Lean theorem, targeted `lake build` green, axiom audit PASS
- [ ] 3 -> 4 publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach

Let `gamma_n` be corpus's generalized inverse of the multiplicity-sensitive Xi zero count. At
`v=1/4`, critical-line trigonometric reduction gives exact amplitude

`a_n = gamma_n / (gamma_n^2 + 1/4)`.

All ordinates exceed one, so `a_n >= 1/(2 gamma_n)`. For every `n < N(T)`, generalized-inverse
duality gives `gamma_n <= T`, hence

`sum_{n < N(T)} a_n >= N(T)/(2T)`.

Riemann--von Mangoldt gives `N(T) >= T log T/(4 pi)` for all large `T`; therefore these prefix sums
are unbounded. Nonnegative summability would bound every prefix by the total sum, contradiction.
No numerical zero data enter.

## No-go closure

- **Exact killing theorem/mechanism:** pending formal proof that `a` is not summable.
- **Strongest positive survivor:** fixed-mode completed flux remains absolutely summable because
  `a_n sin(m omega_n)` has an extra vanishing frequency factor; zero-frequency continuum
  accumulation, not pure-point Bohr recurrence, is the only surviving cancellation mechanism.
- **New insight:** finite critical prefixes fail because they delete the nonuniform amplitude mass
  responsible for the Riemann--von Mangoldt `log T` divergence.
- **Status:** paper proof drafted above; Lean formalization pending.

## Novelty audit

Corpus search found finite-packet oscillation, sublinear-tail repair no-go, coefficient-recovering
regularization no-go, Riemann--von Mangoldt counting, and fixed-mode flux summability, but no exact
critical-amplitude `ell^1` obstruction. Primary Li-criterion and complete-monotonicity literature
audited in this campaign does not state this completed-Abel amplitude boundary.

## Log

- 2026-08-29 — created in 1-in-progress from failed `LI-INF-AP` Bohr-extension conjecture.
