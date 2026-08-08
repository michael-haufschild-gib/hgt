# Mass-Xi outgoing-current exact open core (2026-08-08)

New unconditional modules:
- `formal/GaloisForLFunctions/RHTower/XiMassCriticalOutgoingCurrent.lean`
- `formal/GaloisForLFunctions/RHTower/XiMassCriticalOutgoingOpenCore.lean`

Key results:
- Finite Volterra-adjoint identity moves completed critical error primitive onto `D_{1/2}F=(1/2)F-F'`.
- Infinite identity: `xiMassCompletedErrorFlux = F(0) - ∫ exp(-h/2)F(h) + xiMassCriticalOutgoingFlux`.
- Critical cofinal prime sums equal absolutely summable legal bottom Euler atomization.
- Explicit pole/zero-frequency/damped face is uniformly bounded in vertical height.
- `xiMassBottomPrimeLineBound_iff_criticalOutgoingFluxLineBound`.
- `riemannHypothesis_iff_xiMassCriticalOutgoingFluxLineBound`.

Open theorem remains unconditional uniform height bound for
`∫_0^∞ criticalMellinNormalizedChebyshevError(h) * ((1/2)F_u(h)-F'_u(h)) dh`.
Do not assume this: it is now Lean-proved equivalent to RH.

New-corpus audit:
- Hedenmalm signed boundary weld is zero-side RH equivalence, not source bound.
- `HedenmalmPinnedVolterraBoundaryDefect` rules out faithful bounded exact Volterra anticommuting metric: constant mode is killed.
- `SuzukiCarlemanStieltjesFlux` still requires literal prime-Gamma Stieltjes measure and chord-mass gap.
- Deninger bounded polarization is automatically closed/bounded and is an assumption package, not a provider.
- New prolate tunneling/turning estimates have no source map to outgoing current.
- `vonMangoldtToeplitzCountertraceRegularityNoGo` rules out ordinary bounded Toeplitz realization.

Universal interpretation: connected prime coboundary quotient, Toeplitz no-go, and pinned-Volterra no-go expose one nonlocal boundary-cohomology/constant-mode obstruction. Viable path must supply an all-prime nonlocal cofinal-flux conservation law or a rigorously closable rigged-space boundary trace.

Verification:
- `lake env lean` passes both modules.
- `lake build GaloisForLFunctions.RHTower.XiMassCriticalOutgoingOpenCore` passes.
- capstones use only `[propext, Classical.choice, Quot.sound]`.
- no forbidden declarations in new modules.
- global `formal_tools.py lint` currently fails only on unrelated concurrent unimported Band/Prolate/HTGeometry modules; both new modules are wired into `RHTower.lean` and are not listed.