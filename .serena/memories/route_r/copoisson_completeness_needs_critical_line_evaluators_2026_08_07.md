# The co-Poisson flatness input needs critical-line evaluators, not just off-line ones

Proved unconditionally this session
(`formal/GaloisForLFunctions/RHTower/GammaCoPoissonSoninQuadrantZeta.lean`):

    riemannZeta_eq_zero_of_burnolCoPoissonAnnihilatorPoint :
      1/2 < w.re -> w.re < 1 -> 0 < b -> b < 1 ->
      BurnolCoPoissonAnnihilatorPoint w b .. -> riemannZeta w = 0

via `coPoissonIndicatorSoninCosine_mem_sourceSpace` (Burnol's explicit indicator inhabitant is a
generator) and `soninMellinEvaluation_coPoissonIndicatorSoninCosine_ne_zero_iff`.

**Consequence, and the trap it closes.**  `burnolExtendedSoninEvaluationVector` exists only for
`1/2 < Re w < 1` (and its reflected form for `0 < Re w < 1/2`): on the critical line the integral
`∫ f(t) t^{-w} dt` diverges for a constant-head `L²` vector (`t^{-1/2}` against `L²` is not `L¹` on
the tail).  So the corpus's co-Poisson annihilator characters are exactly the zeta zeros **off** the
critical line — under RH there are none.

Therefore the statement

    closure (span {evaluators at co-Poisson annihilator points}) = burnolCoPoissonQuotientSpace b

which the `gamma-copoisson-sonin-full-quotient-flatness-syzygy` card's equation `(2)` needs, is
**false under RH** in that off-line-only form, because the quotient is not trivial.  The real
missing input is two theorems:

1. **critical-line evaluators** — extend the completed-Mellin evaluation to `Re w = 1/2` by Burnol's
   Riesz/limiting construction;
2. **completeness** — the closed span of all confluent zero evaluators, on and off the line, is the
   whole `burnolCoPoissonQuotientSpace b`.

Everything else on that card is already unconditional Lean: `(1)`, `(3)`--`(7)`, `(10)`--`(12)`,
`(17)`--`(18)`, `(21)` in `GammaCoPoissonSoninQuadrantSection.lean` and
`GammaCoPoissonSoninQuadrantSyzygy.lean`.  In particular
`coPoissonQuotientCommutator_ladderKernel_offDivisor` is the exact source-error syzygy with **no**
hypothesis on `w`, and `(2)` is equivalent to its right-hand side vanishing identically — so no
finite-level rearrangement reaches `(2)`.
