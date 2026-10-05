# BAG complete Schwartz critical boundary

- **ID:** BAG-C28.56ae.
- **Route:** BAG actual rational cubic -> physical cubic transfer.
- **Status:** Formalized; all four production leaf and all 33 public axiom audits passed.
- **Predecessors:** C28.56aa compact boundary, ab complete rational source,
  ac weighted rational/tested identity, ad actual all-order global growth.

## Exact new statement

For EVERY complex Schwartz test Phi on R^2, the complete unordered
positive-rational cubic, with BOTH literal rational axes excluded, has the
critical boundary

    lim_(epsilon -> 0+) tsum_a rationalCubicTest Phi (1+epsilon) a
      = cubicSchwartzBoundaryValue Phi.

No compact support, reflection symmetry, source-growth estimate, arithmetic
identity or convergence assumption is a premise. The source is the literal
six-zeta/Euler source already identified with the complete rational series.

Let F_sigma(u,v)=A_sigma(u,v)Phi(u,v) and
G_sigma(u,v)=(A_sigma(u,v)-T_sigma(u))Phi(u,v). Write

    Q_axis = [G(u,v)+G(-u,v)]/u^2,
    Q_mixed = [F(u,v)-F(-u,v)-F(u,-v)+F(-u,-v)]/(u*v),

with totalized zero values on their denominator axes. At sigma=1 the action is

    (1/2) integral_R2 Q_axis(Phi)
    + (1/2) integral_R2 Q_axis(Phi swap)
    - pi^2 Phi(0,0)
    - (1/2) integral_R2 Q_mixed(Phi)
    + integral_R2 Phi.

All quotient integrals are proved integrable. The factors one half undo the
two-reflection axis average and the coefficient -2 times the four-reflection
mixed average. Thus every original signed quadrant is retained.

## Dependency-closed proof

Define S_(k,n) as the supremum of the finite family of standard Schwartz
seminorms with weight <=k and derivative order <=n. Actual ad source bounds,
local Leibniz, and linear frequency pullback prove, uniformly sigma in[1,2],

    (1+|u|+|v|)^k * norm(D^n testedSource)
      <= C(k,n) * S_(k+54+9*n,n)(Phi)

for BOTH F and G, including all joint damping derivatives. One seminorm
S_(k+54+9*N,N) controls every n<=N.

For k=4,N=2, actual G vanishes at u=0. Its even reflected numerator has
quadratic cancellation along the SHORT u-segment at FIXED v. This preserves
decay in the transverse frequency. For Q_mixed, split four regions: two small
coordinates use rectangular second derivatives; exactly one small coordinate
uses first derivatives on its short segment at fixed large coordinate; two
large coordinates use direct source decay. Exact evenness extends these
estimates to the whole plane. Consequently BOTH quotients are bounded by

    C*S_(76,2)(Phi) / ((1+u^2)*(1+v^2)).

The integrable Cauchy product density supplies global DCT while retaining the
actual moving source. Damping factors lie between zero and one and tend to
one off the axes. Original unreflected kernels are separately proved
integrable at each positive nearby damping before splitting reflection sums.
Measure-preserving reflections give their exact full-plane averages.

The intersection uses joint two-frequency scaling. Uniform Schwartz control
bounds actual A*Phi globally; the product Cauchy density has mass pi^2 and
A_1(0,0)=1. Hence the literal signed intersection mass is -pi^2 Phi(0,0).
Combine both finite parts, this mass, product PV and ordinary test integral.
Finally rationalCubicTest_hasSum, applied to Schwartz integrability, identifies
the complete tested rational series at EVERY positive damping. No exchange
of a finite-prime integral net is used.

## Corpus grounding and failures learned from

Deep searches79976/9492 found Schwartz seminorm and DCT machinery but no
actual-source noncompact boundary. Search84339 returned a partial result
after a reranker disconnect; its Connes one-dimensional quotient source
supports short-segment cancellation, not the missing two-dimensional
transverse decay. Coverage and compiler freshness are recorded in the log.
The current proof builds that missing argument.

Failures during Lean checking were elaboration problems, not mathematical
counterexamples. Explicit function types and scalar calculations avoid
unfolding the actual zeta source, stuck product topologies, and conversion
goals between equivalent order instances. No heartbeat/recursion-limit changes.

## Production leaves and audits

- ChiRamanujanSchwartzSourceDecay: finite-seminorm control of actual sources.
- ChiRamanujanSchwartzIntersectionMass: full noncompact intersection mass.
- ChiRamanujanSchwartzQuotientBounds: uniform full-plane domination.
- ChiRamanujanSchwartzCriticalBoundary: DCT, original-kernel integrability,
  reflection identities and complete rational critical boundary.

Each leaf passed foreground `lake --old env lean <leaf> -o <olean>`:
SourceDecay session23588, IntersectionMass70465, QuotientBounds68160,
CriticalBoundary30640, all exit0 with clean logs. The final theorem is
`tendsto_schwartz_rationalCubicTest_criticalBoundary`.

All 33 public declarations passed the /tmp `#print axioms` audit25246;
only propext, Classical.choice and Quot.sound occur. All four leaves are
imported exactly once by RHTower.lean; no umbrella/full build was run.
Index82447 passed; every public declaration appears in LEAN_API.md.
Lint10429 reported 40 unrelated errors (38 unreachable modules and two
sorry occurrences in LiEvenCrossActualClockDampedCutoffEscape); no error
names a new Schwartz leaf. Repository-wide lint therefore did not pass.
Production, axiom, index and lint logs remain under
`/tmp/bag-schwartz-*-01a0.log`. No added axioms, proof debt, computation,
heartbeat raises, or subagents in these proofs.

## Remaining hard BAG problem

This closes the fixed Schwartz-test arithmetic boundary. It does not identify
arithmetic axes a=1,b=1 with physical diagonals p=r,q=r, establish a growing
physical-test/coupled damping-height limit, exchange the finite-prime integral
net, or control complete finite-height near-resonances. Growing signed moments,
moving cofactors and positive common-height self-return remain open. RH is
neither proved nor falsified by this result.
