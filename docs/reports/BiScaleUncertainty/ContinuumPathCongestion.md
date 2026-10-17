# Infinite-edge logarithmic path congestion

## Measure and state construction

An edge e=(h,u) has endpoints u and u+h. Set a(e)=min(u,u+h),
b(e)=max(u,u+h), and R(e)=exp(b(e))−exp(a(e)). Thus R≥0 and all endpoint
maps are continuous, including h=0 and reversed edges.

Construct κ from arbitrary nonnegative densities: a density on the forward-lag
half-plane (h>0) plus
a countable sum of pushforwards of weighted Lebesgue measure by u↦(h_n,u).
Each weighted measure is s-finite, as is its pushforward, sum, and countable
mixture. This proves the measure condition needed for Tonelli. It is not valid
to silently apply Tonelli to an unrestricted measure on an uncountable space.
The construction includes continuous lag densities and countably many arithmetic
lag lines. No particular arithmetic kernel or global mass estimate is assumed.
The formal constructor accepts nonnegative weight functions through
`Measure.withDensity`. Integral decompositions retain those weighted measures;
expansion into a raw density integrand would additionally require measurable weights.

Let q be an actual real L2 physical velocity, F(t)=∫₀ᵗq, and f(x)=F(exp x).
The preceding Sobolev package proves local absolute continuity and
f'(x)=exp x q(exp x) almost everywhere. Define the nonnegative measurable density
H(x)=exp x q(exp x)², which agrees almost everywhere with exp(−x)|f'(x)|².
It is integrable on every compact logarithmic interval.

## Exact local and global identities

Define P(e,y)=R(e)1_(a(e),b(e)](y). The set of (e,y) with a(e)<y≤b(e)
is Borel, so P and P(e,y)H(y) are jointly measurable. For every edge, set

    J(e)=|f(u+h)−f(u)|²,
    B(e)=∫ P(e,y)H(y)dy = R(e)∫_(exp a(e))^(exp b(e))q(t)²dt.

Local trace Cauchy–Schwarz gives J≤B. Each local value is finite; for R>0,

    B(e)−J(e)=R(e)∫_(exp a(e))^(exp b(e))
                         (q(t)−(F(exp b(e))−F(exp a(e)))/R(e))²dt.

When R=0, both J and B vanish. Define S=B−J≥0 pointwise. The primitive F
is continuous, hence J is measurable; B is measurable by parameter integration,
and so is S. Using nonnegative extended integrals throughout, Tonelli gives

    K(y)=∫ P(e,y)dκ(e),
    ∫ K(y)H(y)dy = ∫ B(e)dκ(e) = ∫ J(e)dκ(e)+∫ S(e)dκ(e).    (1)

No integrability premise is needed and infinite totals are allowed. This is an
addition identity; it never subtracts two infinite global energies. Replacing
H by the actual derivative density is justified by its almost-everywhere equality
under Lebesgue measure, even when K is infinite.

Consequently the infinite-edge jump energy is at most the congested additive
Dirichlet energy. At each edge, the elementary real identity

    J=(|f(u+h)|−|f(u)|)²
        +4(f⁺(u+h)f⁻(u)+f⁻(u+h)f⁺(u))

also bounds four times the integrated opposite-sign nodal pairing by the same
congested energy. Arbitrary additive constants can be retained in the nodal state.

## Parent theory and precise boundary

The classical comparison-of-Dirichlet-forms method replaces each jump by a path
and records the load on each path segment; see Diaconis–Saloff-Coste,
*Comparison Theorems for Reversible Markov Chains*, and
[Aldous–Fill, §8.1](https://www.stat.berkeley.edu/~aldous/RWG/Book_Ralph/Ch8.S1.html).
This package adapts that principle to continuum logarithmic paths, actual rough
Sobolev primitives, mixed diffuse/countable-line measures, and an exact extended
slack identity. No novelty claim for the classical comparison principle.

Equation (1) is not yet a finite graph-domain theorem. A finite scalar bound needs
control of K; scaling κ alone rules out a universal scalar independent of κ.
The concrete arithmetic/archimedean kernel remains a later obligation.

The corpus search found the existing diffuse-plus-countable-line edge measure
and its s-finiteness proof; the new construction follows that geometry without
importing application-specific modules. A second deep search, excluding those
applications, found general kernel integration machinery but no applicable
continuum path-congestion theorem. Both searches completed without errors or
partial results; semantic coverage was unmeasured and snapshots lagged the index.

Status: certified contribution 3/100. Both direct Lean leaves pass without
diagnostics; all 34 public theorems and 3 constructed measure instances pass
axiom audit with only standard Lean axioms. Imports and indexes are updated.
Global lint reports six unrelated concurrent missing imports; exact evidence is
in `ContinuumCoprimeShear-FACTS.md`.
