# Failed conjecture: an invariant rational summand of actual Meyer sources

Status: disproved on paper and in Lean. Not counted as a separate contribution.

The conjecture was that the nonzero rational-function quotient of the actual
arithmetic Meyer source by its finite causal span could be lifted by a
generator-compatible section.

The stronger audited obstruction is
`deningerMeyerRationalTail_hom_source_eq_zero`: every polynomial-linear map from
that quotient into the actual source is zero. Each finite jet packet is killed
by the nonzero characteristic polynomial of its generator. Every such polynomial
is surjective on the rational quotient. Hence every packet of a proposed lift
is zero; actual observable-source injectivity forces the lift itself to vanish.
The nonzero Gaussian tail then disproves existence of a section.

The strongest positive survivor is fully proved and formalized: a nonzero
`RatFunc ℂ` module on the actual quotient, canonical actual-source division
operators D_L with matching finite left and right defects, and the actual
automorphisms `W_L(1-P_S)+P_S` with inverses `D_L+P_S`. These permit division
through arbitrary finite Xi resonances while retaining the necessary spectral
corrections. The nonzero quotient has empty algebraic spectrum.

Lean: `DeningerMeyerRationalTailNonsplitting.lean`,
`DeningerMeyerRationalTailCalculus.lean`, and
`DeningerMeyerArithmeticResonantInverses.lean`, with their audited source leaves.
Five direct leaf audits and 18 principal standard-axiom audits passed; all leaves
are wired. Global lint has unrelated concurrent umbrella omissions recorded on
the positive contribution card.

Positive contribution and full paper proof:
`../3-formalized/rh100-002-meyer-resonant-rational-calculus-2026-10-16.md`.
No positivity, continuity, or RH consequence is asserted.
