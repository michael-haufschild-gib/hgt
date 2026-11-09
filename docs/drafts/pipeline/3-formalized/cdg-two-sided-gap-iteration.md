# Two-sided gap iteration without Landau

- **ID:** CDG-GAP
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/review-0911/obstacles-summary.md`, §§2.6 and 2.11.
- **Statement:** For `σ≥0` and any positive degree set `D` with gaps
  `O(x^θ)`, `θ<1`, the cubic-spline trace satisfies
  `|2 Re S(log d)|≤K d^σ` on `D` for some `K` iff `zetaZeroWidth≤σ`.

## Mathematical content

The two-sided decision step uses the Laplace-transform rate theorem directly.
It does not pass through either one-sided criterion or Landau's theorem.
At primes, exponent zero gives RH; no prime trace bound is asserted.
This supplies the report's missing sign-free decision proof, not the
collective Diophantine producer.

## Proof

**[PROVED HERE]** Write `F(u)=2 Re S(u)`. If all zeros have depth at most
`a≥0`, absolute summability of the spline coefficients with one derivative
gives `|F(t)−F(s)|≤2L(t−s)e^(at)` for `0≤s≤t`.
The degree-gap law supplies `d≤e^u` with
`u−log d≤2M e^((θ−1)u)` at every sufficiently large `u`. Consequently

`|F(u)|≤|K|e^(σu)+4LM e^((a+θ−1)u)`.

For `b=max(σ,a+θ−1)`, this is `O(e^(bu))`. A fixed compact initial interval
is absorbed into the constant by the same derivative estimate. The
continuous rate theorem gives width at most `b`. Its proof takes a Laplace
transform, continues the absolutely convergent resolvent sum along a strip
above one rightmost zero at its height, and compares its nonzero residue
with holomorphy. It needs neither a globally attained top nor a positive
density.

The unconditional strip bound starts at width `1/2`. Induction yields width
at most `max(σ,1/2−n(1−θ))`; any integer `n>1/(2(1−θ))` reaches `σ`.
Conversely, the continuous rate theorem at width `σ`, evaluated at `log d`,
gives the sampled bound. The known prime gap exponent `θ=2/3` supplies the
prime specialization. Width zero is RH by the functional equation.

## Dependencies and novelty boundary

The corpus already proves the one-sided gap law and the continuous
two-sided rate theorem. The new proof combines the improved Lipschitz law
with the latter, removing the one-sided analytic step from the sampled
receiver. No improvement of the known zero-free region follows without a
new arithmetic bound on the samples.

Lean source: `CollectiveDiophantineGeometry/TwoSidedGapIteration.lean`.
Public declarations: `twoSided_width_step`,
`zeroWidth_iff_twoSided_powGaps`, `zeroWidth_iff_twoSided_primes`,
`riemannHypothesis_iff_twoSided_primes`.

## Verification

`lake --old env lean GaloisForLFunctions/CollectiveDiophantineGeometry/TwoSidedGapIteration.lean`
passes. Each public declaration has transitive axiom set
`{propext, Classical.choice, Quot.sound}`. Programme umbrella imports the
module; no umbrella build was run.
