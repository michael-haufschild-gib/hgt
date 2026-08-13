# Mass-shifted adaptive mixed terminal source contact charge (2026-08-13)

## Formal artifacts
- `formal/GaloisForLFunctions/RHTower/XiShiftedCanonicalAdmissionAdaptiveMixedSourceAllDegreeCapital.lean`
- `formal/GaloisForLFunctions/RHTower/XiShiftedCanonicalAdmissionAdaptiveMixedSourceTerminalContactCharge.lean`
- wired into `formal/GaloisForLFunctions/RHTower.lean`
- report equations 9.3.824–9.3.828
- cards:
  - `docs/drafts/pipeline/3-formalized/mass-shifted-adaptive-mixed-source-all-degree-capital.md`
  - `docs/drafts/pipeline/3-formalized/mass-shifted-adaptive-mixed-terminal-source-contact-charge.md`

## New knowledge
1. One top adaptive mixed/completed source action pays aggregate degree displacement:
   `(F_N-F_1)^2 < 2(N-1)J_N`, and on complete positive ray
   `∫(F_N-F_1)^2 ≤ 2(N-1)F_N(a)`.
2. Split all-degree reserve into retained part and source-first terminal channel
   `T_N := 2J_N-E_N-R_N^ret`.
3. Exact positive-chamber law:
   `T_N = 4(N+1) beta_(N+1) = 4(N+1) h_(N+1)/h_N`.
4. Norm-ratio/Jacobi-edge identity needs only leading solve block `H_n>0`, not next two positive extensions.
5. At strict frontier `y=tau_(n+1)`, if newborn norm has first contact order d and coefficient C>0, then
   `T_(n+1)(sqrt(y+u))/u^d -> 4(n+2)C/h_(n+1)(y)>0`.
6. Thus contact cannot hide arbitrarily in reserve: it lies uniquely in newborn terminal source channel.
7. False RH forces cofinally many such exact positive terminal-source charges; RH iff no cofinal terminal-source-charge phase. This is phase classification, not RH proof.

## Exact failed conjecture / remaining wall
Attempt to make current top source pay logarithmic newborn collapse fails at one-extra-block admission restriction. Right germ of `tau_(n+1)` gives positive `H_(n+3)`; existing degree-`n+2` effectivity/source coercivity needs `H_(n+4)`, equivalent to passing next frontier. Terminal charge itself vanishes as `u^d`, so no fixed positive capital follows. Remaining socket: source-paid normalized/logarithmic terminal-charge action using only `H_(n+3)`, or degree-proper lower bound on complete terminal-charge pulse capital.

## Verification
- direct `lake env lean` passes for both modules
- targeted `lake build` passes: all-degree capital 11819 jobs; terminal contact charge 11831 jobs
- axiom audit only `propext`, `Classical.choice`, `Quot.sound`
- no `sorry`/`admit`/`axiom`/`opaque`/`unsafe` in new modules
- no stale Lean process
- formal lint reaches new module but global lint fails on unrelated concurrent unreachable FieldOne/Sieve/Suzuki/Hedenmalm modules and one HTGeometry module
- no computations used

Novelty remains [NOVELTY UNVERIFIED].