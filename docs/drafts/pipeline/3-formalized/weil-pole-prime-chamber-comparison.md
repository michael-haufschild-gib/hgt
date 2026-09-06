# Actual odd-pole positivity within a fixed prime cutoff

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Lean:** `CCMRestrictedWeilPoleBoundaryPrimitives`, `CCMRestrictedWeilPoleBoundaryDifferential`, `CCMRestrictedWeilPolePrimeChamber`, `CCMRestrictedWeilOddPrimeChamberComparison`; 22 public theorems and eight definitions, wired into `RHTower`.
- **Closed result:** at radii at least two, nonnegative actual odd energies at two endpoints with the same integer prime cutoff force strictly positive actual odd energy at every intermediate radius.
- **RH chain:** all-aperture full prime–Gamma pole sign → square-root integrated Chebyshev error → bounded actual unit-Riesz resolvent → mathlib RH. The endpoint signs and complete all-aperture sign remain open.

## Corpus-driven conjecturing loop

1. **Candidate:** reuse the corpus's prime-entry localization of odd first failure. **Scope failure:** `XiShiftedHardEdgeOddFirstFailurePrimePowerJump` uses a fixed state and a density constant inside each integer-cutoff chamber. The present exponential poles move with aperture, and their old prime contributions vary inside a chamber. That theorem does not directly supply their sign.
2. **Conjecture:** the logarithmic Gamma boundary masses have fixed-lower-endpoint primitive representations and explicit second derivatives. **Proved:** the admitted screw-tail half moment handles integrability at zero; reflection and translation identify the primitives; the fundamental theorem of calculus applies only at the positive upper endpoint.
3. **Conjecture:** freezing the arithmetic cutoff leaves a simple differential system for the actual pole matrix. **Proved:** the two prime cumulatives become constants, the complete prime tent becomes affine, and the diagonal and cross entries have the equations below.
4. **Conjecture:** the odd shifted forcing is negative at all apertures at least two. **Proved:** retain the prime tent with its nonnegative sign, the full Gamma terms and the pole square; elementary admitted bounds give strict negativity. A minimum principle then gives genuine propagation of full-source positivity inside the chamber.

The calculus mechanisms are standard. The local-extremum argument follows the corpus's `SuzukiInteriorExcursionSpectralTurningPoint.suzukiSecondDeriv_nonpos_of_isLocalMax`, with the minimum orientation. The new identified differential system and interval comparison concern the actual moving arithmetic source, not an arbitrary positive model.

## Boundary identities and differential laws

Put `L(t)=-log(1-exp(-t))`. The actual cross and self boundary masses are

`B_0(a)=integral_0^(2a) L(t)dt`,

`B_1(a)=(exp(a)/2)integral_0^(2a) exp(-t)L(2t)dt + exp(-a)integral_0^(2a) exp(t)[L(t)-L(2t)/2]dt`.

**Admission and identification.** The existing bound by the screw-tail half moment makes `L(2t)` integrable at zero; scaling gives integrability of `L(t)`. The exact boundary formula is

`B(R,S)=(1/2)L(2R)+L(S)-(1/2)L(2S)`.

The two doubled logarithmic primitives cancel in the unweighted aperture integral. Multiplying by `exp(x)` and translating each endpoint gives the two weighted primitives. No differentiation or continuity at the singular lower endpoint is assumed.

For every `a>0`, the real-variable primitive extensions satisfy

`B_0'=2L(2a)`, `B_0''=-4/(exp(2a)-1)`,

`B_1''-B_1=-4exp(-a)(1+exp(4a))/(exp(4a)-1)`.

The weighted first derivative retains both endpoint contributions before the exact second-order cancellation. All equalities to the actual physical boundary masses are formal.

## Exact prime-chamber system

Fix an actual aperture `a_0` and its integer cutoff `N=floor(exp(2a_0))`. Define the chamber expressions by retaining the actual reciprocal-Mangoldt and Chebyshev cumulatives at `a_0`, retaining the Gamma primitive dependence on the variable radius, and continuing the prime tent affinely:

`T_ch(s)=T(a_0)+2(s-a_0)sum_{2≤n≤N}Lambda(n)(1+1/n)`.

At every positive `s` with `floor(exp(2s))=N`, the chamber expressions equal the actual full Weil entries `A(s),C(s)` and actual odd energy `E(s)=Q(p_+-p_-)=2(A-C)`. This identification is explicit, including all prime powers.

Put

`F_A(s)=16cosh(s)-4exp(-s)-4exp(-s)(1+exp(4s))/(exp(4s)-1)`,

`F_C(s)=8cosh(2s)+4-4/(exp(2s)-1)`.

Throughout the positive real domain of each chamber expression,

`A_ch''-A_ch=F_A`, `C_ch''=F_C`,

`E_ch''-E_ch=2[F_A-F_C+C_ch]`.

The prime dependence in the shifted odd equation survives through the actual cross entry. It is not discarded by the differential calculation.

## Signed forcing and interval propagation

At a matching-cutoff radius `s≥2`, the formal theorem gives

`E_ch''(s)-E_ch(s)<0`.

**Complete sign proof.** The admitted boundary estimate gives `B_0≤2log2+pi+1≤7`. Also `kappa=-EulerGamma-log(2pi)<0`, and the complete tent is nonnegative, so its exact cross formula gives

`C≤2s²+4sinh(s)²+7`.

The exponential bound gives `4/(exp(2s)-1)≤1`. All subtracted Gamma fractions in `F_A` are nonnegative. Write `c=cosh(s)`. The hyperbolic identities and `sinh(s/2)≥s/2` give `s²≤2(c-1)` and hence `c≥3`. The shifted forcing is bounded above by

`2[20c-12c²+4]<0`.

This proves the sign for the actual source, without an RH premise or numerical experiment.

**Minimum principle.** A continuous real function on a closed interval with `f''-f<0` in its interior and nonnegative endpoint values cannot have a negative interior minimum: the second derivative at that minimum would be both nonnegative and smaller than the negative function value. Having proved nonnegativity throughout, an interior zero gives the same contradiction. Thus it is strictly positive in the interior.

Consequently, for positive radii `a≤b` with `a≥2` and equal integer cutoff,

`[E(c)≥0 for every c∈[a,b]]  iff  [E(a)≥0 and E(b)≥0]`.

When `a<c<b`, the endpoint signs force `E(c)>0`. These are `ccmWeilOddPole_nonneg_interval_iff_endpoints` and `ccmWeilOddPole_pos_between_same_cutoff` for the actual full source.

## Verification

- Foreground scratch checks passed with `lake env lean /tmp/hgt-pole-chamber.mNv6O2/Primitives.lean`, then `Differential.lean`, `Chamber.lean`, and `Comparison.lean`.
- All four named leaf audits passed with `lake --old --log-level=error build GaloisForLFunctions.RHTower.<leaf>`. No full or umbrella build.
- `lake env lean /tmp/hgt-pole-chamber.mNv6O2/Axioms.lean` audited all 30 public declarations: exactly `[propext, Classical.choice, Quot.sound]`, no added axiom or oracle.
- `python3 scripts/formal_tools.py lint` passed with existing large-file warnings; `git diff --check` passed. Process inspection found no remaining Lean or Lake process. The research index was refreshed.
- No numerical experiments, external computation, background builds, or commits.

## Current frontier

The theorem in this package assumes equal integer cutoffs at its two endpoints. The [entry comparison package](weil-pole-prime-entry-comparison.md) closes the separate handoff through the zero-energy entering atom and reduces all odd inequalities above radius two to the starting value and later integer-entry values. None of these results proves the required endpoint signs. The even sign and the remaining small-radius range also remain open.

The all-aperture arithmetic inequality remains open in [the current source-sign card](../1-in-progress/weil-two-pole-compression-prime-error.md). The [permanent prime-entry sign shortcut](../5-failed/weil-odd-prime-permanent-entry-sign.md) remains rejected, with this full-source propagation law strengthening its positive replacement.
