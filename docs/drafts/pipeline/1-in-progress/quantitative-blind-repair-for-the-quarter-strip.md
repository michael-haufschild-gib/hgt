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
- `twistedArcMomentSum_eq_zero_of_nonneg` strengthens the sign conclusion:
  a finite twisted sum nonnegative on `[0,1/2]` vanishes there. A fixed
  clamped-kernel comparison makes any positive weighted mass force the
  corner contradiction. See [the formalized rigidity theorem](../3-formalized/twisted-arc-nonnegative-rigidity.md).
  This supplies no quantitative node, pole, or mass estimate.
- `abs_coeff_le_of_ge_on_arc` gives quantitative rigidity for ordinary
  Whittaker sums: a lower bound `−η` on the arc gives
  `|a_m|,|b_m|≤4η/K₀(2π(m+1))`. This exponentially growing inverse cost
  concerns Whittaker coefficients, not a repair of the twisted integer
  moments. No uniform source-weighted inverse estimate follows from it.
- `exists_arcCosMoment_atoms_of_density` retains the whole cosine polynomial
  `Q_v(t)=2Σ_n v_n cos(2π(n+1)t)/K₀(2π(n+1))`: if `M>0` and
  `M+Q_v≥0`, at most `N+1` positive arc atoms realize `v` with mass exactly
  `M`. Hence `exists_arcCosMoment_atoms` realizes every finite `v` with mass
  `2Σ_n |v_n|/K₀(2π(n+1))`. These are formalized ordinary Whittaker repairs;
  their arithmetic node and pole transport and source growth bound remain
  unproved.
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
- `abs_energy_nullRepair_sub_le` already gives exact positive node repair,
  with cost `Σ |v_n| atomCost(n)`. It retains both pole terms but takes
  absolute values before summing the node corrections.
- `WeilWorkExposingRayPolarLeakage` and
  `WeilWorkExposingRayCoherentCompletion` separate this cost from the optimum:
  for the same far-polar Fejér tests, independent-node repair has budget
  comparable to `X exp X`, while a joint geometric-filter correction has
  bounded energy. Its exact variance identity also forces a positive total
  energy floor (`geometric_completion_uniform_positive_floor`). Thus neither
  the independent-node cost nor the joint correction decides the candidate's
  energy-preservation requirement.
- `variance_energy_capacity` strengthens that floor: every variance
  completion built from positive mixtures of short polar seeds satisfies
  `totalArchEnergy ≥ π|F̂(t)|²/(5 log 2)` for every real `t`.
  Changing the short seeds or their translations does not remove this cost.
- The modular null family is jointly blind but has positive pole contribution:
  `tsum_shiftedGamma_pole_eq_half_mul_zero` gives exactly `w₀/2>0`.
  Its members vanish at all zeta zeros; this does not make the family
  zero-pole. The nonnegative arc measure also forces
  `0≤m_j≤4^(−j)m₀`, so setting `m₀=0` kills this whole family.
- The Klein–Gordon pair `(F/2,F')` cancels the pole exactly, but replaces
  the correlation `H` by `H/4−H''`. Values `H(log n)=0` do not control the
  second derivatives at those nodes. Forward dilation of the symmetric
  modular pole filter restores integer blindness at the cost of a Mellin
  phase; the proved positivity applies only after recentering, which loses
  the restored nodes.

## First test

Analyze a correction of the actual two-bump lag tests by translated modular
null witnesses. Retain node values, both pole moments, mixed energy, and mass
in one identity. An estimate for the corrections separately is insufficient.
The existing geometric-filter identity is a model for coupling the nodes,
but its short polar seed contributes the positive energy floor. A modular
replacement must also cancel the null family's pole contribution. Removing
its zeroth member breaks the existing joint-blindness identity. A construction
would need a coupled pole and node correction, plus quantitative division
or approximation for the actual source; none is proved.
An abstract existential replacement chosen from an assumed negative blind
test would only repackage the missing ground-energy estimate.

## Gates

- [x] Quantifiers and existing transfer mechanisms checked in Lean source.
- [ ] Explicit arithmetic/modular repair construction.
- [ ] Dependency-closed mass and energy estimates.
- [ ] Unconditional Lean formalization and standard-axiom audit.
