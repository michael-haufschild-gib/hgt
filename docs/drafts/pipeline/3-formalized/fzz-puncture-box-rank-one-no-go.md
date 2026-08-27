# FZZ puncture regular rank-one occurrence no-go

- **ID:** FZZ-P-R1-NG
- **Stage:** 3-formalized
- **Type:** NO-GO + POSITIVE SURVIVOR
- **Parent:** FZZ-P-GSL
- **Statement:** `[LEAN-PROVED] [NEW] [NO-GO] [POSITIVE SURVIVOR]` A regular nonvanishing continuum form factor forces an inverse-square pole and admits no embedded FZZ `L²` point mode; a first-order form-factor node is exact sharp survivor.

## Goal

Test minimal rank-one/Friedrichs repair of standard dilation's empty point spectrum. Identify exact
regularity boundary for embedded occurrence.

This does not prove RH and does not derive nodal set from FZZ source dynamics.

## Gates

- [x] 0 → 1 in-progress: target-adapted unit-box continuum equation frozen
- [x] 1 → 2 fully-proven: inverse-square contradiction and nodal sharpness proof
- [x] 2 → 3 formalized: direct Lean, targeted build, umbrella, axiom audit; global lint blocked by unrelated concurrent module
- [ ] 3 → 4 publication-ready: external priority review

## Exact frozen claim

At arbitrary real target energy `E`, use regular form factor

`v_E(x)=1_(E,E+1)(x)`.

Any rank-one continuum eigen-equation has representative form

`(x-E)f(x)+alpha v_E(x)=0` almost everywhere, with `f∈L²`.

Then `alpha=0` and `f=0` almost everywhere. Therefore no nonzero embedded point mode exists at any
`E`, and rank-one box-mode completeness for nontrivial FZZ Mellin zeros is false unconditionally.

For nodal form factor `w_E(x)=(x-E)v_E(x)`, state `g_E=-v_E` is nonzero in `L²` and satisfies

`(x-E)g_E(x)+w_E(x)=0`

pointwise. First-order node is exact boundary exposed by obstruction.

## Complete paper proof

On `(E,E+1)`, nonzero `alpha` forces `f(x)=-alpha/(x-E)`. Thus

`|f(x)|²=|alpha|²(x-E)^(-2)`.

Since translated inverse square is not locally integrable, `f∈L²` implies `alpha=0`. Remaining
equation `(x-E)f(x)=0` and nullity of singleton `{E}` force `f=0` almost everywhere. Existence of
nontrivial zeta zero then contradicts any completeness claim using these modes.

For nodal factor, one `(x-E)` cancels resolvent denominator exactly; compactly supported unit box
state is square-integrable and nonzero because interval has positive Lebesgue measure.

## Hostile review and priority verdict

- Form factor is target-adapted, making no-go stronger than failure of one fixed untuned box.
- Result is representative-level necessary equation for rank-one eigenmode; it does not claim full
  interacting operator construction for nodal survivor.
- Nodal formal state proves local `L²` obstruction is sharp, not self-consistent coupling constant,
  multiplicity, or global FZZ dynamics.
- Fermi-golden-rule destruction of embedded modes under nonzero continuum density is classical;
  primary literature includes arXiv:0806.3992. No audited source gives exact FZZ-puncture/zeta
  specialization or its Lean-closed nodal boundary.

Verdict: general mechanism `[REDISCOVERED]`; exact FZZ route no-go and nodal survivor `[NEW]
[BRIDGE]`, external priority provisional.

## No-go closure

- **Killed route:** regular rank-one coupling nonzero at target energy.
- **Strongest positive survivor:** first-order nodal form factor cancels pole and yields explicit
  nonzero `L²` formal state.
- **New insight:** any viable regular embedded occurrence requires source-derived form-factor node
  at every target. Fitting nodes to Xi ordinates is circular; FZZ dynamics must derive collective
  nodal divisor coefficient-faithfully.
- **Remaining core:** finite/multichannel collective nodal law, self-consistency, generalized
  spectral topology, and non-zero-fed identification with `Γ(s)ζ(s)`.

## Lean formalization

- Module:
  `formal/GaloisForLFunctions/RHTower/FZZCigarPunctureBoxRankOneNoGo.lean`
- Exact classification:
  `fzzPunctureBoxRankOneEigenEquation_classification`
- Point-mode no-go: `not_FZZPunctureBoxRankOnePointMode`
- Nodal survivor: `fzzPunctureNodalBoxFormalState_memLp`,
  `fzzPunctureNodalBoxFormalState_equation`,
  `fzzPunctureNodalBoxFormalState_ne_ae_zero`
- Completeness no-go: `not_FZZPunctureBoxRankOneComplete`
- Direct `lake env lean` passed.
- Targeted build
  `lake build GaloisForLFunctions.RHTower.FZZCigarPunctureBoxRankOneNoGo`
  passed (`11554/11554`).
- `#print axioms`: only `propext`, `Classical.choice`, `Quot.sound`.
- Umbrella import wired in `formal/GaloisForLFunctions/RHTower.lean`.
- Formal lint was run but is currently blocked by unrelated concurrent unwired module
  `ThetaCuspLikelihoodFourthSixthSpectralDomination`; this module is directly reachable from
  umbrella and passes direct/targeted checks.

## Log

- 2026-08-27 — conjectured from FZZ standard-dilation no-point-spectrum and corpus inverse-square
  boundary theorem.
- 2026-08-27 — regular rank-one occurrence killed; first-order nodal survivor paper-proved and
  formalized.
