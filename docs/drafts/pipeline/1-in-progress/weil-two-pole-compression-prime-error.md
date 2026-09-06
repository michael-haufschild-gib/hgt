# Actual two-pole compression: exact RH criterion and open arithmetic sign

- **Stage:** 1-in-progress
- **Closed chain:** actual prime–Gamma pole matrix → uniform boundary and diagonal bounds → logarithmic Chebyshev primitive at square-root scale → bounded actual unit-Riesz resolvent → mathlib RH. Smooth-source positivity and form-core density prove the converse.
- **Current open core:** prove `|C(a)|≤A(a)` for every positive aperture. This is exactly RH; it is not an available positivity lemma.
- **Formal packages:** [matrix and integrated error](../3-formalized/weil-two-pole-matrix-and-integrated-prime-error.md); [uniform bounds and exact RH criterion](../3-formalized/weil-fixed-exponential-pole-rh-criterion.md).

## Exact criterion
Let `p_±=1_[-a,a]exp(±x/2)`, `A=Q(p_+)`, and `C=Re Q(p_+,p_-)` for the actual full Weil form. Then

`Q(c p_+ + d p_-)=(A+C)|c+d|²/2+(A-C)|c-d|²/2`.

RH is equivalent to `∀ a>0, |C(a)|≤A(a)`, equivalently nonnegativity of both literal parity poles. False RH forces one of these actual test vectors to have negative full Weil energy at some aperture. These vectors are not constrained ground vectors.

Set `N=2sinh(a)`, `M=2a`, `X=exp(2a)`, `kappa=-EulerGamma-log(2pi)`, `B_j=integral_[-a,a] exp(jx)B(a-x,a+x) dx`, and `E_M(t)=sum_{2≤n≤floor(exp t)}Lambda(n)/n-t`. Every prime power remains in

`T(a)=sum_{2≤n≤floor X}Lambda(n)(1+1/n)(2a-log n)`.

The exact arithmetic entries are

`A=kappa N-exp(a)+(1-2a)exp(-a)+B_1-2exp(a)E_M(2a)+2exp(-a)psi(X)`,

`C=kappa M+2a²+N²+B_0-T(a)`.

`riemannHypothesis_iff_primeGammaPoleInequality` expands the criterion into exactly these expressions. No matrix, boundary, or arithmetic sign is dropped.

## Uniform admitted estimates
Define `K_B=2log 2+pi+1`, `K_A=|kappa|+K_B+4+2(log 4+5)+2(log 4+4)`, and `K_D=K_A+K_B+2(|kappa|+log 4+5)+1`. For every positive aperture, unconditionally,

`0≤B_0≤K_B`, `0≤B_1≤exp(a)B_0≤K_B exp(a)`, `|A|≤K_A exp(a)`.

For `P(T)=integral_0^T [exp(t)-psi(exp(t))]dt`, the physical deficit is exactly `D(a)=P(2a)`. The cross entry satisfies

`C=D+kappa M+exp(-2a)-1+B_0-R`, `R=integral_[-a,a]E_M(a+x)dx`,

`|R|≤(log 4+5)M`.

Consequently all-aperture compression positivity gives `|P(T)|≤K_D exp(T/2)` on `T≥0`. RH is also exactly the existence of some uniform constant in this primitive bound, without logarithmic loss.

## Closed analytic transfer
The corpus's unit-Riesz ray integral satisfies

`J(T)=-exp(T/2)P(T)+(1/2)integral_0^T exp(t/2)P(t)dt`.

Absolute continuity of `P` justifies integration by parts across the prime-counting jumps. A bound `|P(T)|≤B exp(T/2)` gives `|J(T)|≤(3/2)B exp(T)`. The exact identity `J(T)=exp(T)C_res(T)+2/3` gives `|C_res(T)|≤(3/2)B+2/3`, which lands in the existing actual unit-Riesz RH criterion. No analytic continuation obligation remains in this handoff.

## Conjecture → proof / fail → pivot
1. Generic ground-variance equality is sharp in the Hermitian swap model and does not exclude a zero constrained floor. The positive survivor is the actual source-gap bound.
2. Inspecting its pole energy exposes the exact matrix: self entries reduce to arithmetic cumulatives; cross entries retain the moving prime tent. Gamma and pole terms cancel the diagonal's linear-radius main term. All identities are formal.
3. The scalar inequality `x log x≥x-1`, applied at `1±u`, bounds each boundary logarithm by the corpus's admitted screw-tail half moment. Its exact half-line integral yields the uniform boundary bound; Mertens and Chebyshev then bound the diagonal. All are formal for every positive aperture.
4. The hypothesized fixed-exponential completeness is proved in both directions through the primitive/resolvent handoff and smooth-core density. The source sign remains the mathematical problem.

5. A positive odd prime contribution near entry does not stay positive. The actual transport matrix has a unique half-log sign cutoff `H(a)∈(a/3,a/2)`. Every genuine prime power reverses its Weil contribution at two increasing apertures. The positive survivor is the exact decomposition into nonnegative old losses and recent gains, retaining the Gamma–pole balance. All three leaves and this classification are formal; [proof](../3-formalized/weil-odd-prime-cutoff.md), [closed shortcut](../5-failed/weil-odd-prime-permanent-entry-sign.md).

## Exact odd-prime budget

For each aperture there is a unique `H(a)∈(a/3,a/2)` satisfying `sinh(a-H)=(a-H)cosh(H)`. Put `h_n=log(n)/2` and

`w_n=8 Lambda(n) exp(-h_n)[sinh(a-h_n)-(a-h_n)cosh(h_n)]`.

Among visible prime powers, `w_n>0` below the cutoff and `w_n<0` above it before entry. Define `O=sum_{h_n≤H}w_n` and `R=sum_{H<h_n≤a}(-w_n)`, with the original finite prime range. Both are nonnegative. With `N=2sinh(a)`, `M=2a`,

`G_odd=2[kappa(N-M)-exp(a)+(2a+1)exp(-a)+2a²+B_1-B_0-(N-M)²]`,

`Q(p_+-p_-)=G_odd+R-O`.

Thus the exact odd comparison is `O≤G_odd+R`. The negative odd pole square and every prime power remain present. This partition supplies no aggregate sign; the even comparison also remains open.

## Closed interval and prime-power checkpoint comparisons

The boundary primitives and the actual chamber differential system are formal. If `a≤b`, `a≥2`, and `floor(exp(2a))=floor(exp(2b))`, nonnegative actual odd energies at `a,b` force strictly positive energy at every intermediate radius. Nonnegativity on the whole closed interval is exactly equivalent to nonnegativity at those two endpoints. The proof establishes `E_ch''-E_ch<0` for the complete odd source, retaining Gamma, pole and all prime terms. [Proof and audit](../3-formalized/weil-pole-prime-chamber-comparison.md).

The next changed-cutoff endpoint is now included: if `exp(2b)≤floor(exp(2a))+1`, the same endpoint criterion and strict interior positivity hold. At equality the entering diagonal atom and cross tent vanish exactly, so the actual matrix equals its incoming chamber value. For any starting radius `a≥2`, odd nonnegativity on the whole tail is exactly its value at `a` and its values at every subsequent integer entry `log(n)/2`. Any negative tail value forces a negative starting value or a negative integer-entry value. [Entry cancellation, discrete criterion and audit](../3-formalized/weil-pole-prime-entry-comparison.md).

The support reduction to genuine prime powers is also closed. The frozen matrix is its exact smooth Gamma–polar part minus finite Mangoldt atoms; zero-Mangoldt integers leave both entire frozen functions unchanged. The interval comparison therefore holds across any prime-power-free open gap, including both endpoints, with no bound on its length. For every `a≥2`, the whole odd tail is nonnegative exactly when its starting value and every subsequent genuine prime-power entry value are nonnegative. Any negative tail witness forces a negative value in that set.

The exact RH criterion now retains all even inequalities, the odd range `0<a≤2`, and only genuine prime-power entry signs above two. The new odd/even energy corrections vanish at entry `b=log(n)/2` and have opposite slopes `4Lambda(n)(1-exp(-b))²` and `-4Lambda(n)(1+exp(-b))²`. These are entry responses, not permanent signs for older terms. [Prime-power gap proof, criterion and parity slopes](../3-formalized/weil-pole-prime-power-gaps.md).

## Exact entry–loss balance and opposite late-gap shapes

For `b_n=log(n)/2`, `t_n=a-b_n`, let `J_odd=4Lambda(n)(1-exp(-b_n))²` and `J_even=4Lambda(n)(1+exp(-b_n))²`. The exact corrections are `J_odd t_n-V_n` and `-J_even t_n-V_n`, where `V_n=8Lambda(n)exp(-b_n)(sinh(t_n)-t_n)`. The remainder is exactly its hyperbolic Green integral and is positive for every positive elapsed aperture of a genuine prime power.

Sum all visible terms to obtain nonnegative budgets `B_odd=sum J_odd t_n`, `B_even=sum J_even t_n`, and `V=sum V_n`. With the exact smooth Gamma–polar parts, `E_odd=2(A_sm-C_sm)+B_odd-V` and `E_even=2(A_sm+C_sm)-B_even-V`. The shared loss is strictly positive after `log(2)/2`; entry-tangent totals alone give upper bounds. The source comparison is exactly `V≤2(A_sm-C_sm)+B_odd` and `B_even+V≤2(A_sm+C_sm)`.

The admitted diagonal bound proves a fixed threshold `R_0=max(2,log(K_A+17))`. Above it, ordinary odd curvature is negative and even curvature positive between active entries. On each entire closed prime-power gap above this threshold, the actual odd profile is strictly concave and even profile strictly convex. There is one unique actual even-energy minimum, whose sign decides that whole gap; if interior it has zero derivative in the exact incoming expression. This supplies an even checkpoint with a different location rule from the odd endpoints. [Closed paper proof and Lean audit](../3-formalized/weil-pole-entry-age-balance.md).

## Live conjecturing obligations
1. Find arithmetic control coupling the explicit tent cross entry to its diagonal. In odd parity this is the exact comparison `O≤G_odd+R` between the classified prime budgets and Gamma–pole balance. Separate absolute estimates prove the correct scale but not `|C|≤A`.
2. Test a proposed comparison on both parity energies, retaining the full boundary mass and every prime power. Any failure must yield its strongest positive survivor before a shortcut is retired.
3. Relate a successful source comparison to the selected-ground inequality `4|F(u)|²≤(mu-lambda)[2(A+rC)-2lambda(N+rM)]` when useful; the fixed-pole criterion can also close RH directly.
4. Prove arithmetic control of actual odd values at genuine prime-power entries above radius two and actual even minimum values on prime-power gaps above `R_0`. Full boundary handoff, support reduction, ordinary parity curvature and existence/uniqueness of the even minimum are closed. Remaining bounded-radius ranges also need proof.
5. Use the exact common-loss balance to test a proposed arithmetic estimate: it must control `V≤2(A_sm-C_sm)+B_odd` and `B_even+V≤2(A_sm+C_sm)`. Positive entry slopes and separate nonnegativity of the three budgets do not supply either comparison.

The original constrained-ground route remains open and is not retired. No numerical computation, additional axiom, or oracle supplies these results.
