# Bounded chronological arithmetic repair — working knowledge

**Frozen target [R], OPEN.** Construct real a_(k,N), one fixed bound C independent
of k,N, and full L²(0,∞) convergence e^(−t)+Σ_(k≤N)a_(k,N)h(kt)→0,
where h(t)=1/t−1/(e^t−1). Derive everything without RH. The target has not changed.
[Classical RH interface](chronological-rh-recovery-interface.md).

**Verified:** fourteen individual Lean leaf builds; 167 public declarations audited,
only propext/Classical.choice/Quot.sound. All thirteen umbrella imports wired.
Current authoritative lint passes with existing file-size warnings. [Proofs and certificate](../3-formalized/chronological-arithmetic-repair-boundary.md).

## What works

**[C, proved] Universal error floor.** One G>0 works for every coefficient
budget C≥0, every N and every vector with |a_k|≤C:
||r_N||₂≥G/[4 sqrt(log(1+8(1+CN)/G))]. If ||r_N||₂≤η, then
G(exp((G/(4η))²)−1)≤8(1+CN). The proof uses the invariant Mellin value Γ(ρ)
at a critical zero and a three-region integral estimate. Hardy supplies a zero
unconditionally. Fixed budgets exclude persistent power-rate decay in N,
but permit [R]. No numerical ordinate or RH assumption enters Lean.
[Exact proof and consequences](../3-formalized/chronological-heat-error-floor.md).

**[BRIDGE] Nonlinear response repair.** Put q=e^(−t) and
 g=2h(2t)−h(t)=q/(1+q). The recurrence P₀=0, P_(m+1)=g(1+P_m) has
q−P_m=qg^m and squared L² error ≤4^(−m)/2. Lean proves the actual integral
and its limit. Products of responses are used; this is not [R].

**Exact arithmetic cost.** For a zero-constant formal series F, its unique
Lambert inverse is μ*coeff(F). Every power g^r, r≥2, has inverse coefficient
of absolute value binomial(p−1,r−1) at every sufficiently large prime p.
Lean excludes bounded real Lambert representations. Formal-series impossibility
alone says nothing about L² closure.

**Positive residue: sharp boundary.** P_m=q−q^(m+1)/(1+q)^m. Its exact inverse
A_(k,m) agrees with μ(k) through m, equals μ(m+1)−1 at m+1, and equals
μ(m+2)+m at m+2 for m≥2. Thus |A_(m+2,m)|≥m−1. If a truncation through N
has bound B and m>B+1, then N≤m+1: it is exactly a Möbius prefix, with at
most one final correction −1. All these statements are formalized.

## Independently frozen candidate [A]: damped infinite depth

For 0≤ε≤1/2 define

F_ε(q)=q/(1+εq),
b_(n,ε)=Σ_(d|n) μ(n/d)(−ε)^(d−1).

Candidate arrays are b_(n,ε_N), n≤N, with ε_N→0. **[A] is now disproved.**
Their full L² convergence is equivalent to raw Möbius convergence [B], and
the direct heat obstruction [F] below rules out raw convergence unconditionally.

**[BRIDGE, proved in Lean]** F_ε is the damped fixed point
F=g(1+(1−ε)F). Its formal Lambert inverse is exactly b, and
|b_(n,ε)|≤1/(1−ε)≤2 for every n. Also q−F_ε=εq²/(1+εq), with full squared
L² error ≤ε²/4. Thus infinite depth removes the finite-product coefficient
obstruction. This does not justify exchanging arithmetic truncation and limits.

**Exact finite remainder, proved in Lean.** Let
R_N(t)=e^(−t)+Σ_(k≤N)μ(k)h(kt), and let D_(N,ε) be [R]'s residual with b.
Then

D_(N,ε)(t)=e^(−t)−Σ_(d≤N)(−ε)^(d−1)e^(−dt)
+Σ_(d≤N)(−ε)^(d−1)R_floor(N/d)(dt).

The exponential part is controlled by a finite geometric sum. The last sum
contains R_N itself with coefficient one. No ε_N→0 in the stated range can
make this finite remainder tend to zero in full L².

## Attacks, limits, and next hard question

- Exact cancellation in chronological degree forces μ. Its bound |μ|≤1 does
  not control error concentrating at t→0.
- Fake proof: rapid nonlinear recovery → bounded arithmetic linearization →
  finite L² recovery. Finite powers fail the middle step. Damped infinite depth
  repairs that step, but [F] now disproves the final implication for [A].
- Reversing [A] gave exact full L² equivalence to raw convergence. The direct
  positive-Abel transfer now closes raw nonconvergence without inverse smoothing.
- [F]'s obstruction is arithmetic coherence across cutoffs. It does not extend
  to arbitrary bounded arrays; those may add a correction of persistent L² size.
- Unrestricted density via analytic dilation pairing/Blaschke uniqueness is
  another possible [BRIDGE], not yet dependency-closed or formalized. It supplies
  no coefficient budget and does not prove [R].

No numerical result enters Lean. No new RH proof or novelty/priority claim.

## Frozen test [B], proved: full L² convergence equivalence

Every schedule 0≤ε_N≤1/2 tending to zero has damped convergence iff raw
convergence. If strict earlier raw norms are ≤C, then
||D_(N,ε)−R_N||₂≤2ε(1+C); only indices N/d<N occur. Volterra induction
supplies raw boundedness from damped convergence, then the discrepancy vanishes.
`ChronologicalDampingRigidity.chronologicalDampedHeat_converges_iff_raw`
proves this for the actual half-line norm, without assuming raw boundedness.

## Frozen [F], proved: raw heat obstruction and positive survivor

Raw Möbius heat errors cannot tend to zero in full L². Average the dyadic Fermi
response to get K(r)=∫₀¹g(ru)du. The weights exp(−r)/K(r) are positive,
decreasing and at most two. Abel summation turns any raw tail bound δ into
sqrt(t)|Σμ(k)exp(−kt)|≤6δ+(6+M)sqrt(t). Raw convergence would kill the critical
Möbius–Laplace profile, contradicting the corpus's closed critical-zero theorem.
This also excludes every vanishing geometric-damping schedule [A].

**Positive survivor, Lean complete:** one c>0 works for every successful
arithmetic array: ||r_N(a)−R_N||₂≥c at arbitrarily large N. Genuine repair must
supply a correction of nonvanishing full norm; coordinatewise rigidity [E]
and localization of that correction to a growing tail remain open.
[Direct proof and certificate](../3-formalized/chronological-raw-heat-obstruction.md).

## Arithmetic averaging and the current construction gap

**[G], OPEN:** μ(k)k^(−ε_N) with ε_N≥0 tending to zero. The exact positive
Abel decomposition retains exp(−ε_N log N)R_N and earlier raw prefixes.
**[BRIDGE G0], Lean complete:** ε_N log N→0 cannot succeed. More generally,
positive decreasing row weights whose terminal value tends to one have
exactly the raw convergence condition. The proof obtains raw boundedness by
Volterra induction. Every successful power schedule must have a cofinally
positive ε_N log N floor. This is not an eventual floor or a refutation of [G].
[Exact theorem, positive survivors and certificate](../3-formalized/chronological-arithmetic-averaging-scale.md).

**[BRIDGES Q/Q+], Lean complete:** S_N=Σa_(k,N)/k→0 for every successful
bounded array. Uniformly in cutoff, for T≥1,
|S_N|≤(T+1)(||r_N||₂+(1+4C)exp(−T)). Adjusting a_(1,N) by −S_N removes
the charge exactly and changes the residual by −S_N h. For every η>0 one
obtains exact zero charge with budget C+η and the same convergence, choosing
finitely many initial rows zero. This does not preserve exact C or a frozen
Möbius prefix. [Proof and certificate](../3-formalized/chronological-harmonic-charge.md).

Runpod positive averages reach 1.01503e−9 at N=8192. Freezing the first half
of the coefficients increases the positive-average error to 5.93328e−6;
its quadrature primal/dual values nearly coincide. Releasing monotonicity
while preserving Möbius signs gives 1.29339e−8; the full unit box gives
6.05440e−9 with the same 4096 frozen coefficients. The predeclared
sign-preserving ≤1e−8 prediction was not attained, nor refuted by a certified
lower bound. Independent quadrature and high-precision checks agree.
[Current source investigation and report](chronological-escaping-averages.md).

Earlier N=4096 C=1 fits reached 3.51e−10 with 16 frozen coefficients and
8.71e−10 with 1024 frozen. Peaks near logarithmic frequency 14.1 arose without
zero inputs; these remain finite diagnostics. [Earlier report](../2-fully-proven/computations/chronological-fixed-prefix-2026-09-06/REPORT.md).

**Unclosed source estimate:** construct bounded arrays with vanishing full
norm; positive cutoff distributions remain a more restrictive open option. Fixed-rank feasibility gives no uniform bound
linking rank and cutoff. Cancelling finitely many scalar zero phases fails to
control moving L² profiles, whose Mellin dependence is N^(ρ−s) on an entire
line. A dual proof must rule out a uniformly positive separating L² test;
compact-test identities alone do not extend without the required norm control.
[Compact current attack card](chronological-arithmetic-averaging.md).

## Current boundary-moment attack

**Two new paper proofs, Lean pending.** A fixed smooth finite-dimensional
tail space cannot repair an exact proportional Möbius prefix, even with
unbounded tail coefficients: exact discrete annihilators force a forbidden
weighted Möbius critical limit. The positive invariant is the nonzero distance
of a critical heat profile from that tail space; a uniform observation
inequality gives a cofinal full-norm floor.

**[BRIDGE K-growing-jet]:** PNT and a finite Gram construction do supply
unit-bounded arrays with an exact half-prefix, zero charge and an increasing
number of matched odd derivatives. They converge in L²([δ,∞)) for every
δ>0. Their full L² norm is still uncontrolled. The missing estimate must
link growing moment order, inverse Gram cost and the approaching-zero
remainder. Fixed-order feasibility alone does not provide that link.

Runpod tested 27 exact-moment candidates. Best unit-budget norms at
N=512,2048,8192: 4.05e−6, 1.28e−6, 5.20e−7. More moments can worsen
full error and exceed the coefficient budget; near-zero Taylor accuracy
does not control the rest of the boundary layer.
[Compact proof/experiment map](chronological-boundary-moment-repair.md).

**[BRIDGE K-window], paper proved:** every zero-charge unit row with an exact
half-prefix has ||r_N||_(L²([log(N)/N,∞)))≤8/log(N), N≥4. For the growing-jet
source, [R] therefore reduces exactly to N⁻¹∫₀^(log N)|r_N(u/N)|²du→0.
That growing interval cannot be replaced by a fixed compact interval.

**New Lean component:** the actual weighted source Σμ(n)w(nt) has an
absolutely convergent Mellin transform M(w)/ζ on Re s>1, with measurable,
finite-cutoff and local-integrability properties for compact bounded weights.
[Certificate](../3-formalized/chronological-weighted-mellin.md).
The actual weighted critical-zero obstruction is also audited, including its
Abel boundary limit, pole-removed continuation and positive cofinal source
height. [Boundary certificate](../3-formalized/chronological-weighted-boundary.md).
The full fixed-tail obstruction and growing-jet construction remain paper-only.
