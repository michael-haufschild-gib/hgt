# HB moving-horizon/Peierls orbit square law

- **ID:** HC67
- **Stage:** 3-formalized
- **Type:** THEOREM / LEAN-PROVED POLARIZED CAUSAL-CUT SIGN LAW / HARD FRONTIER
- **Routes:** HB, FZZ-P, RBH, PW-B
- **Source:** HC65 moving-horizon/AIME gain identity; HC66 causal optical square law; exact BM
  `++/--` Peierls polarized current and reflected unit-carrier current sum
- **Statement:** The reflected-orbit sum of the concrete unit-carrier BM Peierls polarized cut is
  exactly minus a strictly positive susceptibility times the square of the physical moving-event-
  horizon third-mass defect. Consequently its real part is strictly negative on every tilted Xi
  fibre, vanishes exactly on the critical line, and universal nonnegative orbit orientation is RH.

## Corpus-led conjecture

Fix the physical midpoint `z=1/2` of the BM radial interval and define

`P_n(q) = PeierlsCut_n(q,1/2) + PeierlsCut_n(reflect q,1/2)`.

Existing radial-current algebra gives `P_n(q)=-2(8n+5)E(q)`, where `E` is HC66's angular causal
optical density. HC65 and HC66 should imply, with explicit positive coefficients,

1. `P_n(q) = -sigma_n(q) * G_n(q)^2`, where `G_n` is signed AIME temporal gain;
2. `P_n(q) = -tau_n(q) * M(q)^2`, where `M` is moving-horizon third-mass defect;
3. `sigma_n(q)>0` and `tau_n(q)>0` unconditionally;
4. `Re P_n(q)<0` on every tilted fibre and `Re P_n(q)=0` iff critical-line incidence;
5. `(forall q, 0 <= Re P_n(q))` iff RH.

## Why this is frontier-level

Peierls skewness kills the mixed `+-` self-pairing, and corpus already proves the one-channel
mixed optical landing cannot be the causal cut of a cyclic variational theory. The correct survivor
is the polarized `++/--` current. This conjecture identifies that survivor, at exact coefficient
level, with the physical third-order moving-horizon mass-memory channel. It converts the remaining
causal-cut sign question from an unknown full nonlinear source into one explicit negative square,
while retaining the honest boundary that the abstract full-cokernel landing still needs physical
Peierls source incidence.

Because the optical density is already the shared HB/FZZ-P/PW-B/RBH Ward energy, the same orbit law
propagates to all four routes without inventing a receiver.

## Hostile checks

- Use the literal BM regular/complementary polarized current and its proved reflection sum.
- Fix `z=1/2`; do not introduce a tunable radial evaluation point.
- Derive both AIME-gain-square and moving-third-mass-square coefficients exactly.
- Prove coefficient positivity from existing nonvanishing radial/temporal factors.
- State no unconditional equality with the abstract full cokernel causal cut; its source-incidence
  premise remains open.
- Keep frontier map read-only.

## Novelty boundary as of 2026-08-28

Bounded primary-source audit covered third-order absorption-induced mode excitation
(Sberna--Bosch--East--Green--Lehner, 2022), numerical quadratic QNM coupling and horizon nonlinear
ringdown (2023--2025), third-order mass/spin drift (Zhu et al., 2024), and 2026 computations of
second-order horizon nonlinearity ratios. No audited source derives a completed-zeta Xi-fibre exact
negative-square identity between a reflected `++/--` Peierls polarized BM current and a moving-
horizon third-mass/AIME defect, or its universal RH-equivalent orientation law. Bounded, not
exhaustive, priority claim.

## Gates

- [x] 0 -> 1 in-progress: corpus gap, exact conjecture, hostile proof route, bounded literature audit
- [x] 1 -> 2 fully-proven: dependency-closed paper proof
- [x] 2 -> 3 formalized: closed Lean theorem, target build, axiom/lint audit, umbrella wire
- [ ] 3 -> 4 publication-ready: independent priority audit and standalone exposition

## Log

- 2026-08-28 — Opened after HC66 proved the one-channel optical Gram is quadratic/reflection-even
  and corpus Peierls search showed the correct cyclic survivor is the polarized `++/--` current.
- 2026-08-28 — Proved the exact reflected-orbit Peierls identity in
  `ThetaCuspHawkingMovingHorizonPeierlsOrbitSquareLaw.lean`: the orbit cut is simultaneously
  `-sigma_n(q) * G(q)^2` and `-tau_n(q) * M(q)^2`, with both susceptibilities strictly positive.
  Derived unconditional nonpositivity, strict negativity on tilted fibres, pointwise nonnegative
  orientation iff critical-line incidence, and universal nonnegative orientation iff RH.
- 2026-08-28 — Verification: direct `lake env lean` passed; target-only
  `lake build GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingMovingHorizonPeierlsOrbitSquareLaw`
  passed (`11904/11904`); all nine exported theorem axiom audits report only `propext`,
  `Classical.choice`, and `Quot.sound`; umbrella import present; formal lint reports no finding in
  this module (only pre-existing unrelated unreachable modules).
