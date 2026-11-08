# Arithmetic poles force endpoint amplitude in every Narain average

- **ID:** W11-NE
- **Stage:** 0-backlog
- **Type:** CANDIDATE
- **Source:** [Fixed-average pole obstruction](../3-formalized/ads3-narain-average-pole-decay-boundary.md) · [Sharp exponent](ads3-narain-average-sharp-rate.md)

## Conjectures

For every positive target-height pair and every actual xi zero `ρ`, let
`α=1−Re ρ/2` and `R(y)=yA_YZ(y)+(3/π)log y−B_YZ`.
Then `R≠o(y^α)` at zero. In particular Hardy's critical-line zero should
exclude `o(y^(3/4))` for every fixed average.

A stronger amplitude target retains multiplicity. Let `m≥1` be the
zero order of xi at `ρ`, and let `a_(−m)≠0` be the leading Laurent
coefficient of the actual mean in physical variable `s` at `s=ρ/2`.
For every `0<η<|a_(−m)|/(m−1)!` and every `ε>0`, there should be
`0<y<min(ε,1)` such that

`|R(y)|>η y^α [log(1/y)]^(m−1)`.

The amplitude statement would exclude
`R(y)=O(y^α[log(1/y)]^q)` whenever `q<m−1`. In particular a multiple
zero forbids an `O(y^α)` bound at its own endpoint. Combined with the
proved strict-exponent obstruction, this predicts: an exact
`R(y)=O(y^(3/4))` rate for one fixed average forces RH **and simplicity
of every xi zero**. This implication remains unformalized; no converse
from RH and simplicity is asserted. If the endpoint bound has constant
`C`, the same amplitude law would give `|a_(−1)(ρ)|≤C` uniformly over
all zeros for this fixed mean. Thus the endpoint controls the residue
amplitudes as well as the divisor location and multiplicity.

This is an absolute-amplitude assertion. The separate Landau candidate
addresses both signs. The leading coefficient and its target-height
transformation are positive information retained by the endpoint obstruction;
[universal-profile scaling](ads3-narain-average-scaling.md) predicts their
full triangular logarithmic transformation law.

## Corpus mechanism

`RHTower.chronological_mellin_abel_boundary` in
`ChronologicalWeightedBoundary.lean` proves
`r Mellin(g)(z+r)→0` for compactly supported `g=o(y^(−1/2))`,
`Re z=1/2`, with local integrability and a global `D/y` bound.
For `β=Re ρ/2`, multiply the cutoff remainder `R(y)/y` by
`y^(β−1/2)` to match this normalization. A hypothetical endpoint
little-o bound gives both its critical decay and the required near-zero
majorant; positive-height continuity bounds the remaining compact interval.
The large-height Mellin tail is entire and disappears after multiplication
by `r`.

The existing cleared mean identity then gives a contradiction directly:
write `ξ(1+2u)=(u−p)D(u)` near `p=(ρ−1)/2`, with `D` analytic.
The Abel limit makes the cleared left side tend to zero, whereas the
actual filled numerator product at `p` is nonzero. This works for every
multiplicity, without dividing by a possibly zero first derivative.

For the stronger amplitude target, a hypothetical eventual bound by
`η y^α [log(1/y)]^(m−1)` makes the source Mellin integral converge
absolutely to the right of `Re s=β`. Its norm, multiplied by `r^m`,
is bounded asymptotically by `η(m−1)!`. The meromorphic leading-coefficient
limit instead has norm `|a_(−m)|`, a contradiction. Convergence near this
line is obtained inside that contradiction; it is not asserted for the
unrestricted actual source.

The Abel input's transitive axiom audit contains only `propext`,
`Classical.choice`, `Quot.sound`. Source normalization, the compact majorant,
cleared limit and multiplicity-sensitive Gamma bound remain unformalized.

## Gates

- [ ] 0 → 1: Abel endpoint input and actual source transport audited.
- [ ] 1 → 2: endpoint obstruction and positive amplitude theorem proved.
- [ ] 2 → 3: direct Lean checks, axiom audits and umbrella imports.
