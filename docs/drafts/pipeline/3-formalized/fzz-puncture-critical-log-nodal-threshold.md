# FZZ puncture critical logarithmic nodal threshold

- **ID:** FZZ-P-CLNT
- **Stage:** 3-formalized
- **Type:** CLASSIFICATION + SHARP BOUNDARY + POSITIVE SURVIVOR
- **Parent:** FZZ-P-GSL
- **Statement:** `[LEAN-PROVED] [NEW] [CLASSIFICATION] [SHARP BOUNDARY] [POSITIVE SURVIVOR]` At square-root source wall, logarithmically damped FZZ germ admits a nonzero embedded `L²` mode exactly when log exponent is greater than one half.

## Goal

Resolve critical power `α=1/2` left by fractional classification. Determine whether logarithmic
damping can cross local `L²` occurrence wall and locate exact second-order threshold.

This does not prove RH and does not derive critical germ from literal FZZ dynamics.

## Gates

- [x] 0 → 1 in-progress: critical regularly-varying germ frozen after corpus search
- [x] 1 → 2 fully-proven: logarithmic change of variables, exact iff, uniqueness
- [x] 2 → 3 formalized: direct Lean, targeted build, umbrella, axiom audit
- [ ] 3 → 4 publication-ready: external priority review

## Exact frozen claim

For real `β`, define on target-centered interval `(0,1)`

`v_β(x)=x^(1/2)(1-log x)^(-β)1_(0,1)(x)`,

`f_β(x)=-x^(-1/2)(1-log x)^(-β)1_(0,1)(x)`.

A nonzero `L²` solution of `x f+v_β=0` exists iff `β>1/2`; every solution equals `f_β` almost
everywhere. Thus `β=1/2` is excluded and `β=3/4` works unconditionally.

## Complete paper proof

Away from null singleton `{0}`, equation uniquely gives `f=f_β`. Its energy density is

`x^(-1)(1-log x)^(-2β)`.

Set `x=e^(-u)`. Jacobian is `dx=e^(-u)du`, which cancels `x^(-1)=e^u`, leaving

`(1+u)^(-2β)` on `(0,∞)`.

This is integrable iff `-2β<-1`, equivalently `β>1/2`. Pointwise cancellation and nonzero state
are immediate on `(0,1)`. This proves necessity, sufficiency, uniqueness, and sharpness.

## Hostile review and priority verdict

- Result treats exact power-log family, not all slowly varying factors.
- Target-centered local equation is representative-level, not full interacting self-adjoint
  Hamiltonian or rigged spectral construction.
- Double-critical `β=1/2` diverges like harmonic tail after logarithmic chart.
- Strict log damping rescues square-root source; pure-power statement alone was incomplete.
- Any `β>1/2` works in every target chart, so local regularity remains nonselective.
- Primary Friedrichs sources audited include arXiv:math/0604277, arXiv:2004.08815,
  arXiv:1608.00468, and arXiv:1106.5782. No audited source states this exact FZZ power-log iff or
  provides Lean formalization.

Verdict: endpoint log-integrability mechanism `[REDISCOVERED]`; exact nested FZZ boundary and
unique-state route classification `[NEW] [BRIDGE]`, external priority provisional.

## No-go closure

- **Killed shortcut:** every square-root-order source is locally nonnormalizable.
- **Sharp positive survivor:** square-root node with logarithmic damping exponent `β>1/2`.
- **Sharp excluded wall:** `β≤1/2` in this power-log family.
- **New insight:** viable local FZZ interactions need not have power order greater than one half;
  critical power can survive with sufficiently strong slowly-varying damping. Correct invariant is
  square-integrability of source divided by spectral distance, not Taylor order alone.
- **Remaining core:** test literal winding-condensate source against exact weighted condition and
  derive global node set coefficient-faithfully without divisor fitting.

## Lean formalization

- Module:
  `formal/GaloisForLFunctions/RHTower/FZZCigarPunctureCriticalLogNodalThreshold.lean`
- Shifted tail infrastructure: `integrableOn_Ioi_one_add_rpow_iff`
- Exact energy law: `fzzPunctureCriticalLogEnergy_integrableOn_iff`
- Exact state `L²` law: `fzzPunctureCriticalLogFormalState_memLp_iff`
- State uniqueness: `fzzPunctureCriticalLogEigenEquation_state_unique`
- Exact occurrence law: `fzzPunctureCriticalLogPointMode_iff`
- Boundary witnesses: `not_fzzPunctureCriticalLogPointMode_at_half`,
  `fzzPunctureCriticalLogPointMode_three_quarters`
- Direct `lake env lean` passed.
- Targeted build
  `lake build GaloisForLFunctions.RHTower.FZZCigarPunctureCriticalLogNodalThreshold`
  passed (`11598/11598`).
- `#print axioms`: only `propext`, `Classical.choice`, `Quot.sound`.
- Umbrella import wired in `formal/GaloisForLFunctions/RHTower.lean`.
- Formal lint was run; it is blocked only by unrelated concurrent unwired modules
  `Sieve.MatomakiTeravainenC1PaperScale`, `Sieve.MatomakiTeravainenC1Schedule`,
  `Sieve.MatomakiTeravainenLemma23I`, `ThetaCuspFullReflectionSixthBellTransfer`,
  `ThetaCuspFullReflectionSixthGlobal`, and
  `ThetaCuspLikelihoodFourthSixthSpectralDomination`. This module is directly reachable from
  umbrella and passes direct/targeted checks.

## Log

- 2026-08-27 — conjectured from corpus fractional half-order wall and exponential Mellin head chart.
- 2026-08-27 — exact power-log threshold, unique state, excluded double-critical point, and strict
  damping witness paper-proved and formalized.
