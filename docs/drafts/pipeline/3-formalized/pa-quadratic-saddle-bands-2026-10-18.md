# PA: populated positive saddle bands at quadratic order

- **ID:** PA-QUADRATIC-SADDLE-BANDS-20261018
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** PA route; `PrimeArchHausdorffFixedOrderLargeShiftPositivity.lean`, `HausdorffCDDPhaseKernel.lean`, `XiZeroCountRVMRemainder.lean`.
- **Statement:** One fixed-width band of actual Xi atoms retains at least half its absolute mass, strictly positively, for every order and every shift above a common quadratic threshold.

## Exact theorem and significance

There exist `H >= 1` and a positive natural `A` such that, for every `k,r` with
`A*(k+1)^2 <= r`, putting `T = sqrt(r/(k+1))` and
`F(q) = x_q^(k+1)*(1-x_q)^r`,

`0 < (1/2)*sum_(T<|Im rho_q|<=T+H) |F(q)| <= sum_(T<|Im rho_q|<=T+H) Re F(q)`.

The band is nonempty without RH. The complete radius-one prime--archimedean
Hausdorff difference is exactly this band sum plus its absolutely convergent
complement. A negative complete difference therefore forces the complement
below minus half the band's absolute mass.

The hard local obstruction removed is the separate absolute-phase budget.
That budget requires height proportional to order and hence cubic shifts.
Keeping the signed cancellation controls a populated fixed-width band once
height squared is proportional to order, hence at quadratic shifts. Neither
simple zeros nor a hypothesis on their horizontal positions is assumed.

This proves positivity of a source subpacket. Full-source positivity and RH
remain open. Radius is `1`; the endpoint-calibrated full-array conjecture in
`../1-in-progress/pa-growing-order-phase-cancellation-2026-10-18.md` is not closed.

## Complete paper proof [PROVED HERE]

1. For arbitrary real `tau,sigma` and natural `n,r`, define
   `B=|n*tau-r*sigma|+(n*|tau|^3+r*|sigma|^3)/3`.
   The exact unreduced phase of `(1+i*tau)^n*(1-i*sigma)^r` is
   `theta=n*atan(tau)-r*atan(sigma)`. The existing cubic arctangent estimate
   gives `|theta|<=B`. Polar factorization and `cos(theta)>=1-theta^2/2`
   give real part at least `(1-B^2/2)` times modulus. Thus `B<=1` retains half
   the modulus, even if the two separate absolute phases are large.
2. For an actual Xi copy write `u=|Im rho|`, `v=1/2-Re rho`, and
   `lambda=Re x=(u^2-v^2)/(u^2+v^2)^2`. Corpus geometry gives
   `u^2>=41/2`, `v^2<1/4`, and `|Im x|/lambda<=2/u`.
   It also implies `1/(u^2+1)<=lambda<=1/u^2`: the lower comparison, after
   clearing denominators, is
   `u^2*(1-3v^2)-v^2-v^4>=u^2/4-5/16>0`.
   Therefore `a=lambda/(1-lambda)` satisfies
   `1/u^2<=a<=1/(u^2-1)` and `0<lambda<1`.
3. Suppose `H>=1`, `T>=max(4,H)`, `T<=u<=T+H`, and `r=n*T^2`.
   Those slope bounds give `0<=a<=1`, `r*a<=2n`, and
   `|n-r*a|<=4nH/T`. For the two sides use respectively
   `n-r*a<=n*(u^2-T^2)/u^2<=3nH/T` and
   `r*a-n<=n/(T^2-1)<=nH/T`.
4. Put `tau=Im x/lambda` and `sigma=a*tau`. Then `|tau|<=2/T` and
   `n+r*a^3<=3n`, so the signed phase budget is at most
   `8nH/T^2+8n/T^3`. If `32nH<=T^2`, the two terms are at most `1/4`
   and `1/16`; hence `B<=5/16<1`. Multiplication by the positive real scale
   `lambda^n*(1-lambda)^r` proves half-modulus retention for every atom in
   the band. These atoms are nonzero since both `x` and `1-x` have nonzero
   real parts of the required signs.
5. For population use the unconditional corpus estimate
   `|N(t)-M(t)|<=C log t`, where
   `M(t)=t/(2*pi)*log(t/(2*pi*e))+7/8`.
   Choose `H=16*pi*(C+1)`. For sufficiently large `t>=max(H,4,(2*pi*e)^2)`,
   monotonicity of logarithm gives
   `M(t+H)-M(t)>=H/(4*pi)*log t`, while the two remainder terms total at
   most `3C log t`. Hence `N(t+H)-N(t)>0`. The exact symmetric mass/count
   identity makes the copy band nonempty. This uses no RH-dependent
   short-window theorem.
6. Let `S` exceed that counting threshold, `H`, and `4`, and set
   `A=ceil(S^2+32H+1)`. For `n=k+1` and `r>=A*n^2`,
   `T=sqrt(r/n)` satisfies `T>=S` and `T^2>=32nH`. Apply steps 4 and 5,
   sum the pointwise half-modulus bounds, and use nonemptiness for strict
   positivity. Absolute convergence of the actual Hausdorff atom series
   gives the exact prime-source decomposition and the complementary
   deficit statement.

## Formal implementation

- `BiScaleUncertainty/CompensatedHausdorffPhase.lean`: exact signed phase, cubic remainder, global real-part lower bound.
- `BiScaleUncertainty/HausdorffSaddleScale.lean`: slope localization and the `5/16` phase budget at quadratic scale.
- `RHTower/PrimeArchQuadraticSaddleBands.lean`: actual Xi geometry, unconditional band population, all-order quadratic band theorem, exact source decomposition, complementary deficit.

Main theorem: `RHTower.exists_quadratic_positive_primeArchHausdorff_saddle_bands`.
Source residual theorem: `RHTower.exists_quadratic_primeArchHausdorff_complement_deficit`.

## Verification

- [x] Dependency-closed paper proof before Lean implementation.
- [x] All three canonical leaf checks: `lake --old env lean <leaf> -j1`; exit 0, empty logs.
- [x] All three leaves wired into their relevant umbrellas; no umbrella build.
- [x] `scripts/formal_tools.py lint`: exit 0, existing large-file warnings only.
- [x] Lexical index finds all three `signedPowerPhaseBudget` declarations.
- [x] All 19 public declarations audited in `/tmp`; exactly `[propext, Classical.choice, Quot.sound]`, no added axioms.
- [x] Three capstone/source types checked; actual positivity theorem has no RH or analytic producer premise.
- [x] API probes pass; source hashes unchanged after canonical audits.

Audit artifacts: `/tmp/hgt-pa-{phase,scale,source,axioms,lint}.log`,
`/tmp/hgt-pa-audit-manifest.json`, `/tmp/hgt-pa-source-sha256.txt`.

## Next mathematical target

Control the complementary signed sum from the arithmetic source. The positive
band alone can coexist with an off-line divisor and is not an RH proof.
Keep that conjecture open while rotating to another route family on the next
research pass.

## Log

- 2026-10-18 — Rotated JAS to PA. Paper component proved; three canonical Lean leaves, all 19 public axiom audits, API probes, source hashes, and repository lint pass. Full-array positivity and RH remain open.
