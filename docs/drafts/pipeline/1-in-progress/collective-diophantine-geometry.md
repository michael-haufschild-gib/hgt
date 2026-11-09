# Collective Diophantine Geometry of the Prime Logarithms

- **ID:** CDG
- **Stage:** 1-in-progress
- **Type:** RESEARCH PROGRAMME
- **Source:** `docs/reports/review-0911/obstacles-summary.md`, §2.11.
- **Goal:** Growing-dimension return counting, collective approximation tools,
  and a sign-free producer of the two-sided prime-degree crude bound.

## Required mathematical outputs

1. Return counts uniform in growing prime families; augmented lattice minima.
2. Quantitative heavy-return/large-value transfer with explicit weight and mass.
3. A breadth mechanism beyond bounded-height rounding: first quadratic-log,
   then positive-power lower bounds for logarithmic return height.
4. A sign-free decision theorem at prime degrees and an arithmetic producer
   using the functional equation centred at one half.

## Established decision mechanism

The two-sided gap iteration avoids Landau's theorem. A width bound
`a`, degree gaps `O(x^θ)`, and trace bound `O(d^σ)` give the new width
`max(σ, a+θ−1)` by Lipschitz propagation and the absolute-convergence rate
theorem. Iterating removes the initial width for every `θ<1`.
`CollectiveDiophantineGeometry/TwoSidedGapIteration.lean` proves the exact
width law and its prime specialization. All four public theorems passed
the axiom audit with only `propext`, `Classical.choice`, and `Quot.sound`.
The rate theorem uses a Laplace transform, analytic continuation and residues.
The final direct Lean check passed; the programme umbrella imports the module.
Paper proof: [CDG-GAP](../3-formalized/cdg-two-sided-gap-iteration.md).

## Open core

The corpus already has fixed-prime depth laws, bounded-height obstructions,
smooth-head moment estimates, and a positive-resonator finite-time Bohr
isometry. Repackaging those is not a new breadth estimate. No unconditional
growing-family return exclusion or RH producer has been proved here.

The existing comb estimate propagates prime precision to a smooth integer
with `k` factors at cost `k` times that precision. Its useful counting range
is past integer length comparable to the height. The unresolved collective
tool must control growing smooth supports below that range without losing
constant prime precision. This is an arithmetic counting problem, not a
missing wrapper around the existing moment estimates.

`README.md` gives the foundational draft. A return starts at `t≥1`; heaviness
must specify its weight and fraction. Exact prime-log relation lattices are
zero; successive minima concern approximation bodies in the integer lattice.
