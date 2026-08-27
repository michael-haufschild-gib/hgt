# FZZ puncture finite affine-channel classification

- **ID:** FZZ-P-AFC
- **Stage:** 3-formalized
- **Type:** CLASSIFICATION + POSITIVE SURVIVOR
- **Parent:** FZZ-P-GSL
- **Statement:** `[LEAN-PROVED] [NEW] [CLASSIFICATION] [POSITIVE SURVIVOR]` A finite affine-channel FZZ continuum equation has a nonzero embedded `L²` mode exactly when its collective on-shell source cancels and its collective transverse jet is nonzero; state is then unique almost everywhere.

## Goal

Solve finite multichannel local occurrence problem exposed by regular rank-one no-go. Determine exact
condition under which signed or complex channel mixing cancels embedded resolvent pole.

This does not prove RH and does not derive collective node from FZZ winding-condensate dynamics.

## Gates

- [x] 0 → 1 in-progress: finite affine-channel germ frozen
- [x] 1 → 2 fully-proven: exact collective factorization, necessity, sufficiency, uniqueness
- [x] 2 → 3 formalized: direct Lean, targeted build, umbrella, axiom audit
- [ ] 3 → 4 publication-ready: external priority review

## Exact frozen claim

For target energy `E`, channel `i` has amplitude `aᵢ`, on-shell value `cᵢ`, slope `dᵢ`, and form
factor

`vᵢ(x) = (cᵢ + (x-E)dᵢ) 1_(E,E+1)(x)`.

Define collective on-shell source and first transverse jet

`C = Σᵢ aᵢcᵢ`, `D = Σᵢ aᵢdᵢ`.

Every finite-channel source factors exactly as

`Σᵢ aᵢvᵢ(x) = (C + (x-E)D) 1_(E,E+1)(x)`.

There exists a nonzero `f∈L²(ℝ)` satisfying

`(x-E)f(x) + (C + (x-E)D)1_(E,E+1)(x) = 0`

almost everywhere iff `C=0` and `D≠0`. For every solution, `C=0` and

`f = -D 1_(E,E+1)`

almost everywhere. Thus state is unique modulo null sets.

## Complete paper proof

Set `g=f+D1_(E,E+1)`. Compact support gives `g∈L²`. Original equation becomes regular rank-one
equation

`(x-E)g(x)+C1_(E,E+1)(x)=0`.

The formalized inverse-square pole theorem forces `C=0` and `g=0` almost everywhere. Hence every
solution equals `-D1_(E,E+1)` almost everywhere. A nonzero solution therefore requires `D≠0`.
Conversely, if `C=0` and `D≠0`, explicit state `f=-D1_(E,E+1)` is in `L²`, satisfies equation
pointwise, and is nonzero almost everywhere on a set of positive measure.

## Hostile review and priority verdict

- Result classifies finite affine Taylor germs, not arbitrary form factors or full interacting FZZ
  Hamiltonian.
- Number of channels is arbitrary finite and coefficients are complex; cancellation is collective,
  not componentwise.
- Uniqueness is only almost everywhere, correct equivalence for `L²` states.
- Unit nodal channel produces a mode at every real `E`. Local occurrence is therefore nonselective;
  it cannot distinguish zeta ordinates.
- No spectral self-consistency, multiplicity law, global analytic continuation, or winding source
  identity is claimed.
- Friedrichs/Fermi-golden-rule pole cancellation is classical. No audited source gives this exact
  finite affine FZZ specialization, exact iff, and Lean-closed unique-state classification.

Verdict: general pole mechanism `[REDISCOVERED]`; exact FZZ affine classification and route
boundary `[NEW] [BRIDGE]`, external priority provisional.

## No-go closure

- **Killed shortcut:** finite regular channel mixing creates selective embedded modes merely by
  adding channels.
- **Strongest positive survivor:** exact collective nodal law `C(E)=0`, `D(E)≠0`, with canonical
  state `-D(E)1_(E,E+1)`.
- **New insight:** finite local channel structure reduces all occurrence information to one value
  and one transverse jet. Because a nodal unit channel realizes every energy, selectivity must be
  global and source-derived before choosing divisor points.
- **Remaining core:** derive `C(E)=0` and `D(E)≠0` coefficient-faithfully from literal FZZ/GFZZ
  dynamics at exactly Mellin divisor ordinates, then construct spectral topology and prove global
  landing without zero fitting.

## Lean formalization

- Module:
  `formal/GaloisForLFunctions/RHTower/FZZCigarPunctureAffineChannelClassification.lean`
- Factorization: `fzzPunctureAffineChannel_sum_factorization`
- Solution classification: `fzzPunctureAffineChannelEigenEquation_classification`
- Exact occurrence law: `fzzPunctureAffineChannelPointMode_iff`
- Premise-free boundary witnesses: `fzzPunctureUnitNodalAffineChannelPointMode`,
  `not_fzzPunctureUnitRegularAffineChannelPointMode`
- Direct `lake env lean` passed.
- Targeted build
  `lake build GaloisForLFunctions.RHTower.FZZCigarPunctureAffineChannelClassification`
  passed (`11555/11555`).
- `#print axioms`: only `propext`, `Classical.choice`, `Quot.sound`.
- Umbrella import wired in `formal/GaloisForLFunctions/RHTower.lean`.
- Formal lint was run; it is blocked only by unrelated concurrent unwired module
  `ThetaCuspLikelihoodFourthSixthSpectralDomination`. This module is directly reachable from
  umbrella and passes direct/targeted checks.

## Log

- 2026-08-27 — conjectured from corpus rank-one inverse-square obstruction and finite collective
  channel algebra.
- 2026-08-27 — exact iff, state uniqueness, and universal nodal counterexample paper-proved and
  formalized.
