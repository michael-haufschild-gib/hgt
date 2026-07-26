# Sonin state-complete QFI multiplicative-domain universality law

- **ID:** `sonin-state-complete-qfi-multiplicative-domain-universality-law`
- **Law:** LAW518
- **Stage:** 1-in-progress
- **Type:** THEOREM (dependency-closed paper proof)
- **Register:** `[UNIVERSAL-LAW] [CORPUS-SYNTHESIS]`
- **Target:** `formal/GaloisForLFunctions/RHTower/SoninStateCompleteQFIMultiplicativeDomainUniversalityLaw.lean`

## Theorem

For every self-adjoint bounded Sonin observable `X`, the following are equivalent:

1. its complete logarithmic-clock star-Kadison defect vanishes;
2. erased pure-state QFI vanishes on every normalized physical Sonin state.

Equivalently, normalized physical states form a complete QFI test family for the self-adjoint
part of the logarithmic-scattering commutant.

## Theorem-generated derivation

Contiguous whole-corpus declaration comparison exposed four previously separate mechanisms:

- `soninLogFourierObservableTwirlStarKadisonDefect_eq_zero_iff_commutes`;
- `soninLogClock_erasedPureStateQuantumFisherValue_eq_zero_iff_observedPhysical`;
- `physicalState_soninLogFourierScattering_iff_invariantAverage_fixed`;
- `HTGeometry.orthogonalProjection_noDeparture_iff_commutes_selfAdjoint`.

The first is global and operator-valued.  The second is pointwise and state-valued.  The third
identifies physical states with the image of the Sonin invariant-sector projector.  The fourth
upgrades one-sided invariance under a self-adjoint observable to a reducing subspace.  No corpus
theorem joins them into a state-complete QFI criterion.

## Dependency-closed paper proof

Write `S` for logarithmic Fourier scattering and `P=(1+S)/2` for its invariant-sector
orthogonal projection.

If the star-Kadison defect of `X` is zero, the multiplicative-domain theorem gives `SX=XS`.
Thus `Sψ=ψ` implies `S(Xψ)=Xψ`; the pointwise QFI/physicality theorem makes erased QFI zero for
every normalized physical `ψ`.

Conversely, suppose erased QFI vanishes on every normalized physical state.  For arbitrary `v`,
put `y=Pv`.  If `y=0`, `(1-P)Xy=0`.  Otherwise normalize `ψ=y/||y||`.  Idempotence of `P` makes
`ψ` physical, so the QFI hypothesis and pointwise detector make `Xψ` physical.  Rescaling gives
`(1-P)Xy=0`.  Hence `(1-P)XP=0`.  Since `P` and `X` are self-adjoint and `P²=P`, the reducing
subspace theorem yields `PX=XP`.  Substituting `P=(1+S)/2` gives `SX=XS`; the multiplicative-domain
theorem returns zero star-Kadison defect.  No numerical computation is used.

## Strict corpus delta

Existing results detect one physical state or characterize the global operator defect.  LAW518
proves that the entire normalized physical sector is neither merely necessary nor merely
sufficient: for self-adjoint observables it is an exact state-tomographic test of global
multiplicative-domain membership.

## Gates

- [x] Whole-corpus theorem-leaf discovery
- [x] Prior corpus and failed-route audit
- [x] Dependency-closed paper proof
- [x] Lean formalization; direct `lake env lean`
- [x] Post-proof literature audit
- [ ] Axiom and umbrella audit

## Lean result

`formal/GaloisForLFunctions/RHTower/SoninStateCompleteQFIMultiplicativeDomainUniversalityLaw.lean`
proves
`soninLogFourierObservableTwirlStarKadisonDefect_eq_zero_iff_forall_physical_erasedQFI`.

Direct exact check passed without warnings:

`lake env lean GaloisForLFunctions/RHTower/SoninStateCompleteQFIMultiplicativeDomainUniversalityLaw.lean`

The module is imported by `GaloisForLFunctions/RHTower.lean`.

## Post-proof novelty audit

Performed only after dependency-closed Lean proof passed.  Searches found standard pure-state QFI
as four times generator variance, general QFI/commutator uncertainty relations, variance ordering
over all states, and general multiplicative-domain theory.  No source identified the normalized
physical sector of logarithmic Sonin scattering as a complete QFI test family for the global
star-Kadison multiplicative domain.

Relevant comparisons:

- https://arxiv.org/abs/quant-ph/0609179
- https://arxiv.org/abs/math-ph/0701062
- https://arxiv.org/abs/2303.07409

Verdict: `[NOVELTY PLAUSIBLE — SEARCH NOT EXHAUSTIVE]`.  Novelty is claimed for the exact
Sonin-scattering state-completeness/multiplicative-domain equivalence, not for pure-state QFI
variance or invariant-implies-reducing algebra separately.

## Log

- 2026-07-26 — LAW518 generated from Sonin multiplicative-domain, QFI physicality, invariant
  projection, and reducing-subspace theorems.
- 2026-07-26 — direct Lean check passed; wired into RHTower umbrella; post-proof audit plausible.
