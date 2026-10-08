# Arbitrary periodic phase — candidate L2

Status: OPEN; no Lean theorem. Parent: general AP conjecture L.
Verdict: SURVIVES PRELIMINARY ATTACK for the actual source; proof not complete.
Scientific novelty remains provisional.

## Exact candidate

For every hW : WeilPositiveFull lam, put
C(x)=quantizationResidualCumulative hW x and W(x)=exp(2πi C(x)).
Write R for (lam(n)=Λ(n) for all n≥2) together with RH.

For every real r>1, a representation

    W(x)=Σ_{k∈ℤ} p_k exp(2ik(log r)x),  x>0,
    Σ |p_k| r^{|k|}<∞

forces R. The final source-only formulation is R or absence of all such
representations. L1 proves the integer r≥2 subcase; it does not produce a
representation from hW. The alternative competing possibility is a full-positive
source with a genuinely rational-ratio periodic phase that is not rigid.

The first unresolved case is r=u/v with coprime integers u>v>1. The original
q-chain used an integer base, and that arithmetic restriction is substantive.
[OPEN CORE]: extract a source invariant that excludes positive mean winding for
these two-direction divisibility resonances. Integer-height coefficient equations
alone must be audited before they are used for this purpose.

## Why the old proof does not automatically extend

For r=u/v, a resonance at m is n=m(v/u)^k. Positive k needs powers of u dividing
m; negative k needs powers of v dividing m. Rows at m=u^l v^j are finite sections
with k between −j and l, unlike L1's infinite one-sided q-chain. No noninteger
reflected radial residue may be set to zero without an additive-twist theorem.

The actual continuity argument already proved in CumulativeContinuity should
extend once the represented symbol is constructed: subunit local residual mass
prevents integer jumps of the cumulative lift. The unpaid step is arithmetic
control of winding, not generic logarithm existence.

## Symbolic attack and positive survivor

A warning model for the *abstract integer resonance equations*, not a claimed
Weil-positive source, is as follows. Take coprime u>v>1, r=u/v, and choose

    v^(-1/2) < α < v/u  (possible when u²<v³).

Set P(z)=(z−α)/(1−αz), whose Laurent coefficients are p_0=−α,
p_k=(1−α²)α^(k−1) for k≥1, and p_k=0 for k<0. Put
b=√r/α and c=α√r. Define a(n) by the ordinary Dirichlet series

    Σ a(n)n^(−s)=ζ(s) (1−c u^(−s))/(1−b u^(−s)).

Equivalently, set a(0)=0 and a(n)=Σ_{u^j|n} d_j for n≥1, where d_0=1 and
 d_j=(b−c)b^(j−1) for j≥1. Then a(1)=1. Along u-divisibility chains the
formal generating identity P(√r t) A(t)=p_0/(1−t) gives every integer
resonance row is p_0, despite P having positive winding. The inequalities
αr<1 and b<√u give both the weighted phase moment and the full critical
coefficient-energy bound. ONE-SIDED-RATIONAL.md now contains the complete symbolic
paper audit. The model is not a Lean-certified counterexample and is not a
full-positive source: its nonzero deviation/n is absolutely summable, contradicting
the corpus absolute-convergence rigidity theorem if full positivity were imposed.
No claim is made at the excluded equality b=√u.

This tests an attempted reduction of L2, not L2 itself. The full hW and the
identity with its actual canonical phase remain indispensable. If this attack
survives, the next proof must use source information lost by the integer radial
projection. Do not retire L2 or claim failure of spectral quantization from it.

The strongest positive survivor is L2+: one-sided rational phase rigidity, via
exact valuation classification and numerator-power logarithmic support. Its
paper proof and five final Lean leaf audits are complete in ONE-SIDED-RATIONAL.md;
all twenty declarations passed the standard-axiom audit.
This does not settle two-sided L2 or produce a periodic representation from hW.

Cycle 18 closes two-sided rational phases for sources with finite negative
harmonic mass, including all nonnegative sources: L2h in BILATERAL-RATIONAL.md.
Two new leaves passed clean final direct audits and are wired. The actual source
has a(n)=1 wherever u∤n and v∤n, hence λ(q)=Λ(q) at every prime q>u. The endpoint
deficit receiver then gives rigidity unless Σ max(−λ(n),0)/n diverges. This
avoids finite-block invertibility. General signed L2 remains open.


Cycle 19 proves L3p: a nonrigid source's periodic base must have a rational
positive power. Thus bases r>1 whose every positive power is irrational are
excluded. This does not replace r by a rational number inside the phase:
projecting onto the arithmetic harmonics need not preserve unit modulus.
General rational-power bases, signed bilateral L2 and P18 remain open.
ARITHMETIC-SPECTRUM.md contains the dependency-closed paper proof; the new
ArithmeticSpectrum leaf passed a clean direct audit.
