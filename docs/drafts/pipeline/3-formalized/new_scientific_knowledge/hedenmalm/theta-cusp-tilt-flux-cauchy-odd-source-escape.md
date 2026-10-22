# Cauchy reflection-odd localization and exact CCM source escape

Status: Lean-formalized, unconditional cross-route theorem. `[CORPUS-NEW SYNTHESIS]`. Does not
prove RH.

## Conjecture loop outcome

The positive-real rank-two theorem showed that raw packet size is not the decisive rank: every
two-node linked theta/Weil packet on the exterior Euler ray is unconditionally safe. Corpus search
then exposed a superficially conflicting fact: two moving regular Cauchy poles already form a
complete RH detector. The resolved higher principle is:

```text
decisive rank = reflection-antisymmetric fiber localization,
not number of packet nodes.
```

For a non-real centered Xi divisor location `alpha`, the finite sign test supported on `alpha` and
`conj alpha` is pointwise reflection-odd. Lean now proves the exact channel law

```text
evenEnergy(sign alpha) = 0,
oddEnergy(sign alpha) = #(alpha-fiber union conj-alpha-fiber).
```

Normalized regular two-pole Cauchy packets converge in the multiplicity-exact divisor `ell^2`
carrier to this sign vector. Continuity of the two parity projections separately gives

```text
evenEnergy(F_n) -> 0,
oddEnergy(F_n)  -> N,
```

so every hypothetical off-line fiber forces eventual strict odd-energy domination on actual
holomorphic two-pole packets. RH is therefore equivalent to parity contraction on only the regular
two-Cauchy family.

## Exact source-native strengthening

The approximating poles can be chosen with unequal capped real approach rates so that, at every
stage:

- both poles lie in the full continued prime--archimedean CCM source domain;
- poles are distinct;
- neither pole is reflection-fixed;
- neither pole collides with the reflection of the other.

For this admissible sequence, the exact two-pole source formula applies and Lean proves

```text
Re(ccmTwoPoleSourceEnergy(F_n)) -> -N,
```

hence the actual continued semilocal source energy is eventually strictly negative. This names the
sharp remaining producer: an unconditional source law must exclude this cofinal
reflection-antisymmetric escape. Generic diagonal positivity, bounded central bands, and fixed
finite matrices do not control it.

## Novelty audit

Corpus search found the ingredients but not this channelwise or source-limit theorem:

- `XiWeilCauchyPoleExhaustion` proves `ell^2` convergence to fiber indicators and the abstract
  two-pole RH criterion;
- `CCMTwoPoleSourceCriterion` identifies each admissible two-pole Weil square with the continued
  source energy and proves passivity iff RH;
- `ThetaCuspTiltFluxWeilParityWeld` proves the global even-minus-odd law;
- no prior declaration computes the off-real sign vector's separate parity energies, proves their
  separate two-pole limits, or proves the exact `-N` continued-source limit.

The new synthesis closes all continuity, separation, source-domain, multiplicity, and eventual-sign
steps in Lean.

## Lean sources

`formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspTiltFluxWeilParityCauchyLocalization.lean`

Key closed declarations:

```text
xiOffRealSignTest_parityFlip
xiWeilEvenEnergy_offRealSignTest_eq_zero
xiWeilOddEnergy_offRealSignTest_eq_card
tendsto_xiWeilParityEnergies
exists_twoCauchyPacket_parity_localization
exists_twoCauchyPacket_eventually_oddEnergy_gt_evenEnergy
riemannHypothesis_iff_regularTwoCauchyParityDomination
```

`formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspTiltFluxWeilParityCauchySourceEscape.lean`

Key closed declarations:

```text
CCMAdmissibleTwoPoleSequence
exists_admissibleTwoPoleSource_parity_escape
```

Verification:

- both direct source checks passed with `lake env lean`;
- exact target builds passed for both modules; no umbrella/full build was run;
- all audited `#print axioms` reports contain only `propext`, `Classical.choice`, and
  `Quot.sound`;
- forbidden-token scan passed;
- both modules are wired into `RHTower.lean` without building the umbrella.

## Next hard conjecture

Search actual source decomposition for a coercive or monotone quantity along precisely these
unequal-rate conjugate-fiber pole trajectories. Required theorem must be independent of divisor
location data and rule out a source limit below zero. Promising corpus families are continued
Hurwitz orientation, positive-paired reduction, and multiscale Hellinger/Cauchy separation; fixed
radius diagonal criteria are insufficient unless upgraded to cofinal moving-pole control.

## Log

- 2026-08-21 — Proved pure reflection-odd fiber localization, separate parity-energy limits,
  eventual two-Cauchy parity escape, and exact admissible continued-source limit `-N`.
