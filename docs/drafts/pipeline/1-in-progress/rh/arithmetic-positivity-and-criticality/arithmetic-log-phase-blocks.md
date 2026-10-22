# Complete logarithmic phase blocks

- **Stage:** 1-in-progress
- **Type:** CONJECTURES, separate from EDQ-CELL-PHASE R
- **RH dependency:** a whole-tail sign below the proposed height threshold would only control the size of the exceptional head. An independent constraint at the unit term of every zero would still be required.

## Frozen statements

Use the literal source and Bernoulli polynomial from [the successor-phase card](../../arithmetic-successor-phase-threshold.md). Let `s=sigma+i*t`, `u=conjugate(s)`, `sigma>0`, `t>0`, integer `n>=1`, and `t<2*pi*n`. Put

`a_k=n*exp(2*pi*k/t)` and `T_u(x)=integral_(x..infinity) b(y)*y^(-u-2) dy`.

Define the complete-turn contribution and its prefix by

`B_k=Im[n^(-s)*(T_u(a_k)-T_u(a_(k+1)))]`,

`P_K=Im[n^(-s)*(T_u(n)-T_u(a_K))]`.

**B1 [BRIDGE]:** every `B_k<=0`, for every natural `k`.

**B2 [BRIDGE], independently frozen:** every `P_K<=0`, for every natural `K`.

B1 implies B2. Either statement, together with the already established decay of the tail, would imply `Im(g_s(n))<=0`. Strict negativity in R would require an additional argument; nonpositive finite prefixes alone do not establish it. These statements are not claims at arbitrary heights or at all zeta zeros.

## Source of the changed grouping

`ArithmeticSuccessorCellPhase` proves alternating signs on arbitrarily late integer cells at one exact fixed height. That obstruction leaves cancellation across cells unresolved. The corpus search for periodic primitives and phase cancellation led to `HTGeometry.LogTrigPowerPrimitives`: exact primitives of powers times sine or cosine of a logarithm. Grouping by complete logarithmic turns makes the oscillatory factor return to its initial phase while retaining the actual periodic quadratic. The pairing `x -> exp(pi/t)*x` reverses the sine but changes `b(x)`; its sign cannot be assumed.

## Frozen numerical attack

Run only on the authorized Runpod. Test `sigma in {0.05,0.5,2,8}`, `n in {1,4,16,64}`, and `t/(2*pi*n) in {0.3,0.7,0.95,0.9999}`. Test up to eight complete turns, reducing the count when `log(a_K/n)>20`. Retain every block and prefix, not only violations. Use arbitrary precision growing with endpoint size and real part. Verify selected signs at higher precision and, where feasible, independently by finite-cell integration. Numerical signs are exploratory evidence, never Lean premises.

For a real cutoff `x`, let `m=floor(x)` and `q=m+1`. The exact cell primitive is

`F_m(x)=[x^(1-u)/(1-u)+(2*m+1)*x^(-u)/u-m*(m+1)*x^(-u-1)/(u+1)]/2`.

Then `T_u(x)=T_u(q)+F_m(q)-F_m(x)`, where

`T_u(q)=[-zeta(u,q+1)-q^(1-u)/(1-u)-q^(-u)/2]/[u*(u+1)]`.

Differentiate the displayed primitive on each integer cell to check the formula. Keep endpoint terms; resetting the anchor at each turn would change the conjecture.

## Open obligations

B1 is refuted by the literal-source theorem described below; its frozen quantifiers remain unchanged. Prove or refute B2. Retain R unchanged and use the exact source-scaling survivor to study cumulative cancellation. A counterexample to this grouping would not disprove R or RH. No literature novelty is asserted.

## Independent positive survivor L [BRIDGE]

The first scan suggests B1 fails while B2 survives. The following distinct constant-speed statement was frozen before its proof:

For `0<lambda<2*pi`, integer `K>=0`, `A=2*pi*K/lambda`, and `r=fract(A)`,

`integral_(0..A) b(y)*sin(lambda*y) dy`

`= r*(1-r)/(2*lambda) - sin(r*lambda/2)*sin((1-r)*lambda/2)/(lambda^2*sin(lambda/2)) <= 0`.

Equality holds exactly when `r=0`. This is the unweighted constant-speed model, not B2. The source's logarithmic phase and its power weight have not been replaced in B2 or R.

Paper derivation: integrate twice on each integer cell. The continuous quadratic contributes the final value `-b(A)/lambda`; its slope drops by one at each interior integer, contributing `sum_(j=1..floor(A)) sin(lambda*j)/lambda^2`. The final sine and the integral of the sine vanish because `lambda*A=2*pi*K`. A finite sine sum gives the displayed product. For `x=lambda/2`, strict negativity for `0<r<1` reduces to

`sin(r*x)*sin((1-r)*x) > x*r*(1-r)*sin(x)`.

For each `0<y<pi`, `sin(y)-y*cos(y)>0`, because its derivative is `y*sin(y)>0` and its value at zero is zero. Multiply this inequality at `r*x` and `(1-r)*x` by the respective positive complementary sine and weight; add, then use the sine addition identity. Endpoint cases are exact zeros. The full finite integral identity, all turn numbers, and exact equality classification are now proved in `ArithmeticLinearPhasePrefix`; the proof is not limited to the final trigonometric inequality.

The source-scaling theorem transfers every fixed strict negative case of L to an eventual strict negative logarithmic prefix as the cutoff and height grow proportionally. The [proved first-variation identity](../../../3-formalized/arithmetic-clock-first-variation.md) now covers the exact integer coincidences too: the leading value is zero, but the exact first-order coefficient is strictly negative. Thus every fixed positive complete endpoint is covered. B2 still needs control over every turn number at one finite cutoff, including changing fractional endpoints close to integer coincidence. Neither of the present pointwise asymptotic theorems is uniform in the turn count.

**L+ [BRIDGE], independently frozen after L's proof:** for `0<lambda<2*pi` and every real `A>=0`, the constant-speed prefix `integral_(0..A) b(y)*sin(lambda*y) dy` is nonpositive, even if A is not a complete-turn endpoint. In the first half of each turn the prefix decreases, because `b<=0` and `sin>=0`; in the second half it increases, because both factors are nonpositive. Its maximum on that turn is therefore at one of the two complete-turn endpoints already controlled by L. This exposes a sign-preserving primitive for a constant-speed model. It does not prove that a nonlinear change of phase preserves the sign.

## Independently frozen clock test C [BRIDGE]

**C:** for integer `n>=1`, `0<t<2*pi*n`, and every `V>=0`,

`integral_(0..V) b(n*exp(v))*sin(t*v) dv <= 0`.

This drops the exponential damping in phase coordinates as a separately named, stronger conjecture. If true, integration by parts against `exp(-(sigma+1)*v)` would imply the nonpositive weighted prefixes needed by B2 for `sigma>-1`. It does not change B2's definition. For a first attack, test complete-turn endpoints with `sigma=-1` in the finite x-integral; no infinite-tail formula at that real part is required. Failure would identify the damping as essential to this proposed proof, rather than refute B2.

The additional numerical attack uses finite polynomial-power primitives directly, with `sigma in {-1,-0.5,0,0.001,0.5,8}`, `n in {1,16,256,4096}`, `t/(2*pi*n) in {0.25,0.5,0.75,0.99,0.9999}`, and first through eighth complete turns. Retain the distinction between in-domain B2 tests and the out-of-domain clock test.

## Established results and exact open cut

The main Runpod scan found 43 positive complete turns among 504 tested turns, in 21 of 64 parameter triples. Every tested prefix was negative. A separate boundary scan found 882 negative prefixes, including 147 undamped-clock tests at `sigma=-1`. Twelve selected cases were independently checked by integer-split quadrature at 150 digits; method differences were below `9e-144`. The [report](../../../2-fully-proven/computations/arithmetic-log-phase-blocks/REPORT.md) retains all data and numerical limitations. The separate module `ArithmeticLogarithmicPhaseScaling` now formally refutes the literal logarithmic B1, independently of these numerical results. At height `t=(4*pi/3)*N`, its second actual fixed-anchor turn is positive for arbitrarily large integer N, still with `t<2*pi*N`. The proof transfers the positive model segment by an exact source change of variables and dominated convergence, including the complex phase anchor. B2 and C remain conjectures. See [the actual-source certificate](../../../3-formalized/arithmetic-logarithmic-phase-scaling.md) and [the closed no-go with its positive survivor](../../../5-failed/arithmetic-logarithmic-block-sign.md).

L and L+ are fully proved in Lean, including their source integral identities and complete equality classification. Lean also proves that the second constant-speed turn at `lambda=4*pi/3`, over `[3/2,3]`, is positive. The [formal certificate](../../../3-formalized/arithmetic-linear-phase-prefix.md) and [closed model no-go](../../../5-failed/arithmetic-linear-block-sign.md) delimit this result.

**Conditional paper implication, not a proved producer:** C would give strict negativity of the complete weighted tail for every `sigma>-1`. Write `H(V)=integral_(0..V)b(n*exp(v))*sin(t*v) dv`. If C holds, `H<=0`; it is strictly negative on a small initial interval because the quadratic and sine have strict opposite signs there. Also `|H(V)|<=V/8`. For `a=sigma+1>0`, integration by parts gives

`integral_(0..infinity) exp(-a*v)*H'(v) dv = a*integral_(0..infinity)exp(-a*v)*H(v) dv < 0`.

The boundary term vanishes by the displayed linear bound. Multiplying by the positive factor `n^(-2*sigma-1)` recovers `Im(g_s(n))`. Thus the undamped clock inequality is a concrete candidate sufficient for R, and even predicts a larger real-part range. Its proof is missing. The finite constant-speed law does not supply it: the map `x=n*exp(v)` changes the spacing of every arithmetic cell.

The independent [quartic remainder theorem](../../../3-formalized/edq-quartic-remainder-phase-cutoff.md) gives a full-tail negative phase on the explicit region `0<sigma<=1`, `t>=1`, `n^2>=t^3`. It does not establish B2 or C, or the proposed linear threshold, and retains the exceptional head.

**RH remains open even if C is proved.** Its condition `t<2*pi*n` reaches cutoffs beyond the height-dependent head. At a zero, the required sign is the unit quantity `Im(g_s(1))=t*(2*sigma-1)/(2*|conjugate(s)*(1-conjugate(s))|^2)`. No new arithmetic identity forces that unit sign. Neither finite-prefix regrouping nor the proposed tail estimate justifies discarding the head. No radical new RH architecture or literature novelty was established.
