# Actual pole entry balance, opposite curvature, and unique even minima

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Lean:** `CCMRestrictedWeilPrimeAgeBalance`, `CCMRestrictedWeilPoleEntryAgeSource`, `CCMRestrictedWeilPoleParityCurvature`, `CCMRestrictedWeilPoleGapShape`; 26 public theorems and 11 definitions, all wired into `RHTower`.
- **Closed results:** exact common loss beyond both entry tangents; full arithmetic–Gamma balances in both parities; eventual ordinary odd concavity and even convexity; a unique actual even-energy minimum on every sufficiently late closed prime-power gap.
- **RH chain:** full prime–Gamma pole positivity → integrated Chebyshev square-root bound → bounded critical resolvent → mathlib RH. Actual source signs remain open.

## Corpus-driven conjecture → proof → pivot

1. **Conjecture:** propagate the known entry slopes through the actual finite prime sums. **Exact correction:** expanding the corpus's literal diagonal and cross atoms exposes the same post-entry loss in both parities. Entry tangents alone overestimate the actual arithmetic response.
2. **Conjecture:** this loss has an exact positive Green representation. **Proved:** `sinh(t)-t=integral_0^t sinh(t-u)u du`, nonnegative for `t≥0` and strictly positive for `t>0`. Each genuine prime power therefore has positive accumulated loss at every later radius.
3. **Conjecture:** the common loss survives unchanged in the complete source. **Proved:** finite summation gives both identities below, with the exact Gamma–polar terms retained. The resulting sign problem is a coupled comparison of three nonnegative arithmetic budgets with two specified smooth source terms.
4. **Conjecture:** the admitted `|A|≤K_A exp(a)` bound upgrades the shifted odd differential inequality to ordinary curvature control. **Proved:** beyond `R_0=max(2,log(K_A+17))`, ordinary odd curvature is negative and even curvature positive at every matching-cutoff radius.
5. **Conjecture:** this yields a useful even-gap checkpoint. **Proved:** both actual matrix entries equal their incoming expressions on the entire closed prime-power gap. Strict convexity gives a unique actual even minimum. Its value decides nonnegativity on the gap; if interior, it is stationary. **Remaining step:** prove these minimum values and the genuine odd prime-power checkpoint values nonnegative from the actual arithmetic source.

The Green calculation follows the corpus's hyperbolic variation-of-parameters mechanism (`HTGeometry.HyperbolicSourceRange`) but is proved directly for the identified atom. `SourceHorizontalWoldEulerGreenAnomaly` concerns an inverse-Euler series and supplies no missing source sign here. No operator or positivity theorem from that different profile is assumed to apply.

## Exact atom balance

Write `b=log(n)/2`, `t=s-b`, and `lambda=Lambda(n)`. The already identified atoms subtracted from the matrix are

`d_n(s)=2lambda(exp(s)/n-exp(-s))`,

`c_n(s)=lambda(1+1/n)(2s-log(n))`.

Define the positive tangent magnitudes

`J_odd(n)=4lambda(1-exp(-b))²`,

`J_even(n)=4lambda(1+exp(-b))²`,

and the common loss

`V_n(s)=8lambda exp(-b)[sinh(t)-t]`.

For every integer `n≥2` and real `s`, the exact identities are

`2(-d_n+c_n)=J_odd(n)t-V_n(s)`,

`2(-d_n-c_n)=-J_even(n)t-V_n(s)`.

**Proof.** Since `exp(2b)=n`, `1/n=exp(-b)²` and `exp(s)/n-exp(-s)=2exp(-b)sinh(s-b)`. Substitute these into the atoms and expand the two squares. No asymptotic truncation occurs.

The kernel `K(t)=sinh(t)-t` satisfies `K(t)≥0` for `t≥0` and `K(t)>0 iff t>0`. Its Green identity follows by differentiating `-u cosh(t-u)-sinh(t-u)` with respect to `u`, giving `u sinh(t-u)`, and applying the fundamental theorem of calculus. The odd atom equivalently has the exact balance

`2(-d_n+c_n)=J_odd(n)sinh(t)-4lambda(1+1/n)K(t)`.

The actual response therefore contains a negative continuous forcing term in addition to its positive odd entry impulse.

## Full source and nonnegative budgets

Sum over the original visible range `2≤n≤floor(exp(2a))`. Let

`B_odd(a)=sum J_odd(n)(a-log(n)/2)`,

`B_even(a)=sum J_even(n)(a-log(n)/2)`,

`V(a)=sum V_n(a)`.

All three sums are nonnegative. Visibility gives nonnegative elapsed aperture; Mangoldt weights and both squared tangent factors are nonnegative. Moreover, `V(a)>0` whenever `a>log(2)/2`, using the literal prime two as one positive summand.

Let `A_sm,C_sm` denote the exact Gamma–polar terms from the finite-atom matrix presentation. The full actual energies satisfy

`E_odd(a)=2(A_sm(a)-C_sm(a))+B_odd(a)-V(a)`,

`E_even(a)=2(A_sm(a)+C_sm(a))-B_even(a)-V(a)`.

Thus simultaneous parity nonnegativity is exactly

`B_even+V≤2(A_sm+C_sm)` and `V≤2(A_sm-C_sm)+B_odd`.

The same positive loss appears in both inequalities. Omitting it gives an upper bound for energy, strictly so after the first prime entry; it does not give a lower bound that proves positivity. This statement does not assert that an actual RH test has negative energy.

## Eventual ordinary curvature

Let `K_A=ccmWeilPoleUniformDiagonalBound`, already proved positive with `|A(a)|≤K_A exp(a)` for every positive aperture. Set

`F_A(s)=16cosh(s)-4exp(-s)-4exp(-s)(1+exp(4s))/(exp(4s)-1)`,

`F_C(s)=8cosh(2s)+4-4/(exp(2s)-1)`.

For `s≥2`, the exact fractions give

`0≤F_A(s)≤16exp(s)`, `F_C(s)≥4exp(2s)`.

Indeed, `exp(4s)≥9` bounds its ratio by two; `exp(-s)≤1`, `cosh(s)≥1`, and `cosh(s)≤exp(s)` control the diagonal forcing. The other fraction is at most four, and the exponential form of `cosh(2s)` supplies the lower cross bound.

The ordinary parity equations are

`E_odd,ch''=2(A_ch+F_A-F_C)`,

`E_even,ch''=2(A_ch+F_A+F_C)`.

When the frozen cutoff matches the actual radius and `s≥R_0=max(2,log(K_A+17))`, the admitted diagonal bound implies

`E_odd,ch''≤2[(K_A+16)exp(s)-4exp(2s)]<0`,

`E_even,ch''≥2[-K_A exp(s)+4exp(2s)]>0`.

All constants are exact expressions; no numerical estimate of the threshold is used.

## Closed gaps and the even minimum

If `a≤b` and there is no genuine prime-power entry in `(a,b)`, every newly visible interior atom has zero Mangoldt weight. At the right endpoint, any nonzero new atom is exactly at entry and has zero value. Both actual matrix entries therefore agree with the incoming expressions throughout `[a,b]`, including both boundaries. This extends the prior odd-source equality to the full matrix and even source.

For `a≥R_0`, the incoming odd profile is strictly concave and the even profile strictly convex on `[a,b]`. The proof transfers the ordinary second-derivative signs through the exact equality of frozen functions at interior radii; continuity supplies the closed endpoints. These shape statements are confined to each gap, not asserted globally across nonzero entry-slope jumps.

Compactness gives an even minimum. Strict convexity proves that precisely one actual aperture in the gap minimizes the even source. Testing nonnegativity at that aperture is equivalent to testing the entire gap. If the minimizer is in `(a,b)`, the derivative of its exact incoming even expression vanishes there; the minimum may also occur at a boundary.

## Verification

- Foreground `lake env lean` passed for `/tmp/hgt-pole-age-balance.3YaALh/AtomBalance.lean`, `SourceBalance.lean`, `Curvature.lean`, and `GapShape.lean`.
- All four named leaf builds passed with `lake --old --log-level=error build GaloisForLFunctions.RHTower.<leaf>`. No full or umbrella build.
- `lake env lean /tmp/hgt-pole-age-balance.3YaALh/Axioms.lean` audited all 37 public declarations: exactly `[propext, Classical.choice, Quot.sound]`. No added axiom or computation oracle.
- `python3 scripts/formal_tools.py lint` passed with existing large-file warnings; `git diff --check` passed. The research index was refreshed and the new actual even-minimum declarations retrieved. Process inspection found no Lean or Lake process.
- No numerical experiment, external computation, background build, subagent, or commit.

## Current frontier

The exact accumulated arithmetic loss and late-gap shapes are closed. The open source inequalities are the coupled entry/age budgets, the genuine odd prime-power checkpoint signs, and the unique even-gap minimum signs. The remaining bounded-radius ranges also require proof. No value positivity or unconditional RH conclusion is supplied by the shape or balance identities. See the [current source-sign card](../1-in-progress/weil-two-pole-compression-prime-error.md).
