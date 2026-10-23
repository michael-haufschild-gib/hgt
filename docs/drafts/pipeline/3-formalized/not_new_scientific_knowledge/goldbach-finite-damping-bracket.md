# Finite damping bounds and positive compensation for Goldbach

- **ID:** goldbach-finite-damping-bracket
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean); BRIDGE, no scientific novelty claim
- **Parent:** [damping reflection and arithmetic parity](goldbach-damping-reflection-parity.md)
- **Source:** the actual RH divisor response, with squarefree and odd-sector projections

## Exact unconditional statements

Use the existing source and target weights:

    o_ε(k)=1_(μ(k)=−1) ∏_(p|k) 2sinh(ε log p/2),
    O_N(ε)=Σ_(k+l=N) o_ε(k)o_ε(l),
    G(N)=Σ_(p+q=N; p,q prime) log p log q,
    L_N(ε)=(16O_N(ε)−O_N(2ε))/(12ε²),
    Q_N(ε)=O_N(4ε)−20O_N(2ε)+64O_N(ε).

For every natural target N and every real damping ε, Lean proves

    16O_N(ε)−O_N(2ε) ≤12ε²G(N),
    L_N(ε)≤G(N),
    ε²G(N)≤O_N(ε),
    Q_N(ε)≥0,
    L_N(ε)−L_N(2ε)=Q_N(ε)/(48ε²),
    L_N(2ε)≤L_N(ε).

It also proves L_N(ε)→G(N) as ε→0 through nonzero real damping.
Real division makes L_N(0)=0; every finite assertion includes that case.
For positive damping, the first two readings give a lower and upper
approximation to G(N). No analytic premise is present in these statements.

## Closed paper proof

The [parent extraction proof](../../2-fully-proven/goldbach-odd-damping-extraction-minorant.md)
contains the full argument. Its finite dependencies are as follows.

1. The odd source is nonnegative at nonnegative damping. Its supported
   endpoints are squarefree with an odd number of prime factors. Either
   both endpoints are prime, their product contribution vanishes, or
   their joint doubling multiplier D is at least sixteen.
2. For x≥0, 3sinh x≤x(cosh x+2): differentiate the difference and use the
   corpus theorem `HTGeometry.two_cosh_sub_two_le_self_mul_sinh`.
   For A,B≥1, `(A+2)(B+2)(4−AB)≤27`, by expansion in A−1 and B−1.
   Together these prove the prime-pair minorant; the composite-pair
   defect is nonpositive. Summation gives the lower bound.
3. The inequality sinh x≥x proves the prime-pair majorant. All other
   summands are nonnegative. Evenness extends both bounds to real damping.
4. At the next scale let E be the joint multiplier. Each elementary
   multiplier A≥2 becomes A²−2≥A, so E≥D. For a composite pair D≥16,
   `D(E−20)+64≥(D−16)(D−4)≥0`. For a prime pair there are exactly two
   factors A,B≥2. With D=AB, one has
   `E≥D²/2−4` and `D(E−20)+64≥(D−4)²(D+8)/2≥0`.
   Multiplication by the nonnegative source pair and summation prove Q≥0.
5. The exact increment is algebra. The previous tangent limit gives
   the punctured convergence. Thus nonzero damping can be successively
   halved to increase the minorant toward G(N).

## Lean and verification

Module: [RiemannHypothesisBridge.lean](../../../../../formal/GaloisForLFunctions/goldbach/RiemannHypothesisBridge.lean).
Its existing umbrella import remains in place; no umbrella was built.

The eight audited closures are:

- `oddDampedExtractionMinorant_le`
- `tendsto_oddDampedExtractionMinorant`
- `primePairWeight_mul_sq_le_oddDampedReflectionOverlap`
- `oddDampedRefinementGain_nonneg`
- `oddDampedExtractionMinorant_sub_two_mul`
- `oddDampedExtractionMinorant_two_mul_le`
- `primePair_iff_positive_oddDampedDyadicDefect`
- `goldbach_iff_positive_oddDampedDyadicDefect`

Direct check from `formal/`:

    lake --old env lean GaloisForLFunctions/goldbach/RiemannHypothesisBridge.lean

Exit 0, no warnings. All eight closures use only `propext`,
`Classical.choice`, `Quot.sound`. Log:
`/tmp/hgt-goldbach-finite-damping-audit.log`. Audit directives removed;
proof bodies unchanged. No added premise, proof hole, or raised option.
The existing prime-pair equivalence now uses the minorant directly,
removing its duplicated factor-count argument.
Declaration indexes regenerated. Owned diff checks and source-discipline
checks pass; scratch searches removed and all owned commands terminated.
No new umbrella or repository-wide build is claimed.

## Remaining arithmetic obligation

Prove L_(2(n+2))(ε)>0 for some positive ε at every natural n. Neither
the nonnegative refinement gain nor convergence establishes that sign.
The results supply a finite compensation law in the RH source language;
they do not prove Goldbach, RH, or an equivalence between the conjectures.

No new scientific knowledge beyond the elementary extraction mechanism
is claimed. Continuous monotonicity and the fourth-order error are still
paper results. The next research step remains an actual arithmetic lower
bound or the signed covariance estimate, rather than further extraction
identities.
