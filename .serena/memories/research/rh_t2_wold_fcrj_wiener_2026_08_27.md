# RH/FCRJ research state — 2026-08-27

## User constraints
- `docs/drafts/pipeline/1-in-progress/rh-current-frontier-map.md` is read-only for this agent from now on.
- Corpus-first conjecturing: always run `scripts/formal_tools.py research "<query>"`.
- Lean: closed/unconditional, no new axioms; foreground one process; `lake env lean <file>`; only targeted `lake build <module>` at final audit; wire umbrella; no full builds.
- Persistent goal remains active until every listed route is dead or RH is formalized.

## Completed loops 60–62
- Collision tail/resolution and dipole multipole bounds formalized and targeted-audited.
- Modules:
  - `GaloisForLFunctions.RHTower.XiPhysicalPrimeEndpointPhaseCollisionTailRate`
  - `GaloisForLFunctions.RHTower.XiPhysicalPrimeEndpointDipoleMultipoleBound`
- Cards promoted to Stage 3 before later unrelated lint failures.

## Loop 63: optimized inverse-square transport energy
Module: `formal/GaloisForLFunctions/RHTower/XiPhysicalPrimeEndpointDipoleInverseSquareEnergy.lean`.
Main results:
- split: tail <= L D^2 + 4 W^2/(N+L)
- optimized: tail <= 4 W D
- scaled raw: N * sum_{n>N}|a_n|^2 <= (A^2/(4*pi^2)) * (4*N*W*D)
Uses floor(2W/D), with D=0 split.
Direct Lean and targeted build passed. Axioms: propext, Classical.choice, Quot.sound. Wired in RHTower umbrella.

## Loop 64: active aperture-width ultraviolet law
Module: `formal/GaloisForLFunctions/RHTower/XiPhysicalPrimeEndpointActiveApertureWidthEnergy.lean`.
For every active prime endpoint packet:
- chord <= (2*pi/A) * clipped interval length
- clipped length <= k-m
- D <= (2*pi/A)L <= (2*pi/A)(k-m)W
- N * raw inverse-square tail <= (2*A/pi) * N*(k-m)*W^2
Activity is essential; inactive reversed endpoints falsify the length bound.
Direct Lean, targeted build, standard-three axiom audit passed; wired.

## Loop 65: activity-localized Mertens ultraviolet law
Module: `formal/GaloisForLFunctions/RHTower/XiPhysicalPrimeEndpointActiveMertensUltravioletEnergy.lean`.
Corpus input: `mertens_first_upper` from `RHTower.CreaseBudgetPrimeMass`.
For nonempty active finite prime packet:
- W <= k + log 4
- hence N * sum_{n>N}|a_n|^2 <= (2*A/pi) * N*(k-m)*(k+log 4)^2
Empty packet handled directly.
Direct Lean, targeted build, standard-three axiom audit passed; wired.

## Pipeline/docs
- Stage-2 cards:
  - `docs/drafts/pipeline/2-fully-proven/fcrj-primewise-dipole-inverse-square-energy.md`
  - `docs/drafts/pipeline/2-fully-proven/fcrj-active-aperture-width-ultraviolet-bound.md`
  - `docs/drafts/pipeline/2-fully-proven/fcrj-active-prime-weight-mertens-ultraviolet-bound.md`
- Loop evidence appended to `docs/drafts/pipeline/1-in-progress/critical-multiplicative-compensated-cancellation-rh.md`.
- Do not edit frontier map.

## Global lint blocker
Own modules pass direct checks/builds. Global `scripts/formal_tools.py lint` currently fails because unrelated concurrent modules are unwired:
- ReflectedBiHeatSourceNormalizationClassification
- Sieve.MatomakiTeravainenBlockConvolution
- Sieve.MatomakiTeravainenFiniteIteration
- Sieve.MatomakiTeravainenFiniteIterationSource
Do not wire/change other agents' modules. Keep loops 63–65 at Stage 2 until clean global lint.

## Current loop 66
Find sharp source-retention/vanishing-width theorem or obstruction for FCRJ.
Latest corpus search found no explicit schedule. Related items:
- `rectangularMovingPrimeTent` uses aperture a=log N/2 in `CCMRectangularAutocorrelation`.
- Suzuki cofinal schedules likely separate.
- Existing limits include `tendsto_width_div_apertureLog`, `tendsto_width_div_logAperture_sq`.
Next read only targeted regions in critical route card around lines 5635–5700 and 6280–6520; inspect definitions relating FCRJ source to physical aperture.
