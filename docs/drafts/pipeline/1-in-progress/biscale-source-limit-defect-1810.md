# Source compactness and the singular-energy defect

- **ID:** biscale-source-limit-defect-1810
- **Stage:** 1-in-progress
- **Type:** ANALYTIC BRIDGE; candidate exact theorem, source/API audit incomplete
- **Parent:** [field programme](biscale-field-development-1810.md), item 10

## Candidate positive theorem

Start with actual real smooth sources of unit squared mass, common support in `[-S,S]`, and a uniform bound `∫|f′|²≤B`. Impose actual logarithmic-grid conditions up to the growing cutoff and the existing source polar constraint.

The proposed conclusion is a uniformly convergent subsequence with a nonzero compact continuous source limit, all grid conditions and polar balance retained, and exact convergence of singular Lévy energies. The limit class should be compact continuous sources with an `L²` translation estimate; smoothness of the limit is not asserted from a first-derivative bound.

Mechanism: fundamental theorem of calculus and Cauchy–Schwarz give a common `1/2`-Hölder modulus for sources and a uniform bound using their zero values outside the common support. Arzelà–Ascoli gives uniform convergence. Common support turns this into strong `L²` convergence and passes normalized mass, correlations, and exponentially weighted source integrals to the limit. Each fixed grid condition eventually belongs to every source's cutoff.

The sharper integrated translation estimate `‖T_t f−f‖₂²≤Bt²` gives `0≤1−h(t)≤Bt²/2` uniformly. Since `exp(t/2)/sinh(t)≤exp(1/2)/t` on `0<t≤1`, the origin contribution is bounded by `B exp(1/2)δ²/4`. Away from zero, uniform correlation convergence and the integrable kernel tail give energy convergence. No assumed convergence hypothesis replaces the compactness argument.

## Existing exact defect to reuse

The corpus already proves the exact correlation-level defect, including subsequence extraction, in `InfiniteGridOriginConcentration.lean`. `infiniteGrid_energy_convergence_iff_uniform_origin` gives the exact uniform-origin criterion; `infiniteGrid_origin_energy_defect` and `infiniteGrid_origin_defect_iterated_limit` identify the defect; `exists_infiniteGrid_origin_defect_limit` supplies a subsequence for every bounded-energy sequence in the existing source class. Reuse these theorems. The identity to transport to the new actual source limit is

`lim_n E(f_n)−E(f) = lim_(δ↓0) lim_n ∫_(0,δ) (1−h_n(t)) exp(t/2)/sinh(t) dt`.

For each fixed `δ>0`, the complementary integral converges by uniform convergence of correlations and integrability of the kernel away from zero. Subtracting it from the convergent full energies identifies the inner limit; monotone convergence then identifies the outer limit. The uniform derivative bound annihilates this defect via the explicit quadratic origin bound.

## Required attacks and gates

- Existing `InfiniteGridStrictEnergyLoss` already refutes energy conservation from common support and strong `L²` convergence alone. Verify that its derivative energies cannot remain uniformly bounded, rather than adding an unrelated example.
- Translation of one normalized constrained source preserves its correlation, grid observations, polar product and energy while its support escapes. Construct an actual polar-balanced grid-admitted source and prove that this family has no strongly convergent normalized subsequence. This tests the role of tightness/common support.
- Verify the exact polar source definition and the exponential-integral identity before using the proposed continuity argument. Correlation convergence alone is insufficient for polar balance.
- Prove the limit regularity actually claimed; a smooth limit requires stronger bounds.
- The first source-limit query returned lower-semicontinuity and energy-domination ingredients. A subsequent incidence query exposed `InfiniteGridOriginConcentration.lean`; its full defect/convergence statements and proofs were then inspected. The missing result is source-level compactness and polar conservation from quantitative source bounds, together with a zero-defect criterion derived from those bounds.
- [ ] Exact existing source types, nonempty examples and polar identity audited.
- [ ] Dependency-closed source proof, deriving the hypotheses of the existing defect and energy-convergence theorems.
- [ ] Lean construction, actual loss/tightness witnesses, named-source/axiom audits and wiring.

No item-10 completion is claimed.
