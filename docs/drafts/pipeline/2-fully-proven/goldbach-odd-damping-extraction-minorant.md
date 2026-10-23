# A two-scale minorant for the Goldbach coefficient

- **ID:** goldbach-odd-damping-extraction-minorant
- **Stage:** 2-fully-proven
- **Type:** BRIDGE; elementary coefficient extraction, no scientific novelty claimed
- **Parent:** [damping reflection and parity](../3-formalized/not_new_scientific_knowledge/goldbach-damping-reflection-parity.md)
- **Lean status:** the source, tangent and finite sign certificate are checked in `goldbach/RiemannHypothesisBridge.lean`; the quantitative minorant below is paper-only.

## Objects

Let a_ε(k) be the squarefree, unit-removed RH divisor response. Set

    b_ε(k)=exp(ε log k/2)a_ε(k),
    o_ε(k)=(b_ε(k)−b_{−ε}(k))/2,
    O_N(ε)=Σ_{k+l=N}o_ε(k)o_ε(l),
    G(N)=Σ_{p+q=N; p,q prime}log p log q.

All sums at fixed N are finite. Damping reversal gives b_{−ε}(k)=μ(k)b_ε(k).
Therefore o_ε(k) is zero unless μ(k)=−1, and otherwise

    o_ε(k)=∏_{p|k}2sinh(ε log p/2).

Every retained integer is squarefree and greater than one, and has an odd
number of prime factors.

## Exact theorem

For each N there are nonnegative real coefficients c_j, j≥1, such that

    O_N(ε)=Σ_{j≥1}c_j ε^(2j),       c_1=G(N),

with absolute convergence for every real ε. For ε≠0 define

    L_N(ε)=(16O_N(ε)−O_N(2ε))/(12ε²).

Then

    L_N(ε)=G(N)−Σ_{j≥3}((4^j−16)/12)c_j ε^(2j−2) ≤ G(N).

In particular L_N(ε)→G(N) as ε→0, with error O_N(ε⁴), and L_N is
nonincreasing on positive damping. Also

    O_N(ε)=ε²G(N)+O_N(ε⁴).

These are unconditional statements about the actual source. They do not
assert L_N is positive at any specified target or damping.

## Dependency-closed proof

For p prime, log p>0, and the everywhere convergent series is

    2sinh(ε log p/2)
      =Σ_{r≥0}(log p)^(2r+1) ε^(2r+1)/(2^(2r)(2r+1)!).

Every coefficient is positive. Multiplying finitely many such series is
valid by absolute convergence. An odd number of factors gives only odd
degrees, beginning at the number of factors. Each reflected product
therefore has only even degrees, beginning at two or above. The finite
sum over the antidiagonal retains nonnegative coefficients and absolute
convergence. Degree two requires exactly one prime factor at both
endpoints. Squarefreeness identifies those endpoints with actual primes,
whose linear coefficients are log p and log q. Hence c_1=G(N).

Substitution of 2ε multiplies degree 2j by 4^j. In 16O_N(ε)−O_N(2ε),
degree two has multiplier 12, degree four vanishes, and all remaining
multipliers are negative. Absolute convergence at 2ε justifies the
subtraction and gives the exact displayed series for L_N. Its error has
nonnegative coefficients at even degrees at least four. Thus it is
nonnegative at every real ε, increases with ε>0, and is O_N(ε⁴) at zero.
The expansion for O_N follows from the same series.

## Finite proof of the minorant and majorant

The inequality itself admits a proof without infinite series. For x≥0,
the function g(x)=x(cosh x+2)−3sinh x vanishes at zero and has derivative
x sinh x+2−2cosh x≥0. The latter bound is already proved in
`HTGeometry.two_cosh_sub_two_le_self_mul_sinh`. Thus

    3sinh x ≤ x(cosh x+2).

For A,B≥1, expansion in a=A−1 and b=B−1 gives

    27−(A+2)(B+2)(4−AB)
      =3a²+3b²+12ab+4a²b+4ab²+a²b² ≥0.

If cosh x cosh y≥4, the next inequality has nonpositive left side.
Otherwise multiply the two sinh bounds by the nonnegative factor
4−cosh x cosh y and apply the polynomial identity. In both cases,

    sinh x sinh y(4−cosh x cosh y) ≤3xy.

For a prime pair p,q, put x=ε log p/2 and y=ε log q/2. The doubling
formula then proves that its contribution to 16O_N(ε)−O_N(2ε) is at
most 12ε² log p log q. For every supported nonprime pair, at least four
distinct prime factors occur across the two endpoints. Each factor
multiplies by 2cosh(ε log p/2)≥2 under doubling, so that pair's defect
is nonpositive. Unsupported pairs contribute zero. Summing proves

    16O_N(ε)−O_N(2ε) ≤12ε²G(N).

Also sinh x≥x for x≥0. Thus every prime pair contributes at least
ε²log p log q to O_N(ε), and all remaining terms are nonnegative:

    ε²G(N) ≤O_N(ε).

Both statements hold for every real ε: the overlap and ε² are even.
With real division's zero convention, L_N(0)=0≤G(N), so the minorant
inequality also has an unconditional statement at zero. This finite
proof certifies the inequalities; the series proof above separately
establishes monotonicity and the fourth-order error.

## Positive compensation across three scales

There is also a finite, termwise proof of dyadic monotonicity. Define

    Q_N(ε)=O_N(4ε)−20O_N(2ε)+64O_N(ε).

For a supported pair write P=o_ε(k)o_ε(l), D for its joint doubling
multiplier at ε, and E for that multiplier at 2ε. Its contribution to Q
is P[D(E−20)+64]. At nonnegative damping P≥0. Each elementary multiplier
A=2cosh x is at least 2 and becomes A²−2≥A under doubling, hence E≥D.

If one endpoint is composite, D≥16, and

    D(E−20)+64 ≥(D−16)(D−4) ≥0.

For a prime pair there are exactly two factors A,B≥2. Then D=AB≥4 and

    E−(D²/2−4)=(A²−4)(B²−4)/2 ≥0,
    D(E−20)+64 ≥(D−4)²(D+8)/2 ≥0.

Unsupported pairs vanish. Summing, and then using evenness, proves
Q_N(ε)≥0 for every real ε. Direct algebra gives the exact increment

    L_N(ε)−L_N(2ε)=Q_N(ε)/(48ε²) ≥0.

At zero both sides are zero under real division's zero convention.
Thus halving damping produces an increasing sequence of minorants
converging to G(N). This is a positive compensation law for the actual
source. It supplies neither a positive starting value nor a positive
limit at a target where that sign has not been proved.

## Relation to the open arithmetic task

For every target, existence of positive L_N at some positive damping is
equivalent to existence of a prime pair: positivity gives G(N)>0 by the
minorant, and G(N)>0 gives positive L_N near zero by convergence.

This supplies a decreasing minorant where O_N(ε)/ε² supplies an increasing
majorant. It extracts the first coefficient without assuming its sign.
The all-even positivity of this minorant remains unproved. No uniform
lower bound, damping scale, or horizon-limit interchange is asserted.

## Audit

- Finite Euler-product and hyperbolic identities audited against the local corpus.
- This is standard two-scale Richardson extraction on the identified source.
- Paper proof closed; quantitative Lean theorem not yet supplied.
- No computational experiment and no additional analytic premise.
