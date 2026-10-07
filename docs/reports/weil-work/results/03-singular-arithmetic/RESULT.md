# WP03 result

**OPEN.** The bounded zeta-quotient detector is not proved.

Lean-proved bridge: for every full-cone Weil-positive λ and ε>0 there is Cε≥0
such that, simultaneously for every N∈ℕ and every t∈ℝ,

    |Σ_{n≤N} μλ(n)n^(-it)| ≤ Cε (N+1)^(1/2+ε) (2+|t|)^ε.

All inputs come from full positivity; no individual Möbius-coefficient bound
or subcritical absolute-summability premise is added. There is no exceptional
height set. The t=0 specialization gives ordinary square-root cancellation.
A cutoff of width 1/2
agrees with the sharp integer sum exactly, and fractional Mellin decay pays
the narrowing cost. This strengthens the located smooth-sum corpus statement.

The ordinary reciprocal Dirichlet series converges at every s with Re s>1/2
and equals the same literal holomorphic reciprocal G. At s=1 its ordinary
harmonic sum is zero. These consequences are formalized in the same leaf:
`WeilWorkSingularArithmeticSharpReciprocal.lean`.

The targeted `lake build --old +GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticSharpReciprocal`
passed. The final direct `lake env lean` leaf audit passed with no diagnostics.
All five declarations use only `propext`, `Classical.choice`, `Quot.sound`.
The leaf is wired into RHTower. Latest formal lint reports seven unrelated
unwired modules; it reports no failure for this leaf.

The quotient bridge is now formalized: for every ε>0 there is Cε≥0 with

    |Σ_{n≤N} qλ(n)| ≤ Cε (N+1)^(1/2+ε),   qλ = 1*μλ.

Its ordinary Dirichlet series converges throughout Re s>1/2. The actual
weighted zeta norm, with weight (2+|t|)^(-1-η), is integrable for every η>0
on σ∈[1/2,3], σ≠1. This supplies the quotient's fractional Mellin mass;
polynomial strip growth separately supplies the contour shift. Pole removal
uses the existing entire zeta numerator and reciprocal primitive. All inputs
are derived from full positivity and unconditional corpus theorems.

The three new leaves are `WeilWorkSingularArithmeticWeightedZeta.lean`,
`WeilWorkSingularArithmeticMellinMass.lean`, and
`WeilWorkSingularArithmeticQuotient.lean`. Their targeted `--old` builds passed.
The quotient import makes all three reachable from RHTower. All three direct
final audits passed without diagnostics. The nine-public-declaration axiom
audit passed; every declaration uses only `propext`, `Classical.choice`, and
`Quot.sound`. Latest formal lint reports nine unrelated unwired modules and
none of these leaves.

These are classical analytic bridges, not claimed significant novelty. They do
not bound the actual quotient ζG uniformly in height.

Both coefficient sequences now also have Lean-checked square mass:

    Σ_{1≤n≤N}|μλ(n)|² ≤ Cε(N+1)^(1+ε),
    Σ_{1≤n≤N}|qλ(n)|² ≤ Dε(N+1)^(1+ε).

The reciprocal estimate follows by integrating the finite all-twist polynomial
over a time interval proportional to N and applying the sharp mean-value lower
bound. Divisor Cauchy–Schwarz and an exact summatory swap give the quotient
estimate. No infinite-series mean limit or exceptional-height removal is
asserted. The new `WeilWorkSingularArithmeticSquareMass.lean` leaf passed its
targeted `--old` build and final direct `lake env lean` audit with no diagnostics.
It is wired into RHTower. Both public declarations passed the axiom audit with
only `propext`, `Classical.choice`, and `Quot.sound`.

The open detector requires uniform twisted quotient control. The precise
sufficient bound and why ordinary cancellation does not supply it are recorded
in PROOF.md. The research goal remains active and unsolved.
