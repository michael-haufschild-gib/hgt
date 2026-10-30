# Quantitative blind repair for the quarter strip

- **ID:** quantitative-blind-repair-for-the-quarter-strip
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** fourth-power-mesh-signed-saving; the twisted-arc minimum principle and prime-blind duality.
- **Statement:** Construct a blind, zero-pole replacement for a pole-free Weil test, preserving negative energy with mass cost at most `exp((1/2+ε)A)` on support `[-A,A]`.

## Exact candidate

Let `W(F)=Re(zetaZeroConfig.W F F)` and `M(F)=∫|F|²`.
For every `ε>0`, seek `Cε≥0` such that every smooth real pole-free `F`
supported in `[-A,A]`, `A≥1`, admits a finite nonnegative combination `c`
of compact Weil tests with

```
nodeVector c = 0,       nodePoleMass c = 0,
nodeArchEnergy c ≤ W(F) + M(F),
massOf c ≤ Cε exp((1/2+ε)A) M(F).
```

The intended construction uses the actual modular null witnesses and node
corrections. No existence or mass estimate for this replacement is proved.

## Why this cost matters

`twoPeriodMean_mul_massOf_le` gives
`m₂ massOf c ≤ nodeArchOnly c`, with
`m₂=(log 2/π)∫₀^{π/log 2} gammaBracket(t) dt`.
The zero-pole constraint identifies `nodeArchOnly c=nodeArchEnergy c`.
The candidate would therefore give
`W(F)≥−(1+|m₂|Cε exp((1/2+ε)A))M(F)`.
The polar ground-energy transfer
`abs_re_sub_half_le_of_ccmRestrictedWeilPolarGroundEnergy_ge_neg_exp`
then gives zero width at most `1/4+ε/2`; taking every `ε>0` gives the
required three-quarters strip. This is a proposed producer, not a proved bound.

## What the existing proofs supply

- `twistedArcMinimumPrinciple_holds` rules out a strictly positive arc-moment
  combination. Its proof uses the sign change of the lowest surviving sine
  mode and a corner derivative contradiction. It constructs a null witness;
  it does not estimate the cost of repairing an arbitrary test.
- `logNode_blind_iff_certKernelPow_vanishes` already reverses divisor transfer
  for spectral densities `Ξ^k R`, with `R` holomorphic and the stated decay.
  General blind densities need not belong to that class. Dividing by `Ξ^k`
  introduces poles that the existing transfer theorem does not control.
- `nodeLift` realizes every finite node vector; `poleFibre_nonempty` also
  fixes pole mass. Neither theorem preserves Weil energy or supplies the
  required mass bound.
- `twoPeriodMean_mul_massOf_le` uses every node `2^j`: their vanishing cosine
  moments force uniform phase modulo `2π/log 2`. Folding the increasing
  archimedean symbol then gives the mass bound. The pole constraint remains
  essential.

## First test

Analyze a correction of the actual two-bump lag tests by translated modular
null witnesses. Retain node values, both pole moments, mixed energy, and mass
in one identity. An estimate for the corrections separately is insufficient.
An abstract existential replacement chosen from an assumed negative blind
test would only repackage the missing ground-energy estimate.

## Gates

- [x] Quantifiers and existing transfer mechanisms checked in Lean source.
- [ ] Explicit arithmetic/modular repair construction.
- [ ] Dependency-closed mass and energy estimates.
- [ ] Unconditional Lean formalization and standard-axiom audit.
