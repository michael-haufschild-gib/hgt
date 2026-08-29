# JAS Gamma--theta reflection-prefix conditioning wall

- **ID:** JAS-GTRPCW
- **Stage:** 5-failed
- **Type:** THEOREM (Lean) / construction-class no-go
- **Source:** corpus search over `JointAncestryGammaThetaSeparateNormalizationWall`, `JointAncestryGammaThetaDivisorGaugeTrivialization`, `CirclePoissonProductSingularity`, `InfiniteProductNearOne`, `InfiniteProductNonvanishing`, and `XiCTaylorThetaTailCompletedValuationReflection`
- **Status labels:** `[PROVED HERE] [PROVED IN LEAN] [CORPUS-NOVEL NO-GO] [POSITIVE SURVIVOR FORMALIZED] [TARGETED EXTERNAL NO-MATCH] [GLOBAL NOVELTY UNVERIFIED]`

## Result

Let

`P_x(N) = ∏_{n<N} jasGammaThetaLocalRenormalizedFourthFactor x p_n`

for the corpus prime enumeration. For `x>0`, Lean proves

`P_x(N) → 0  ↔  x ≤ 1/2`.

For `0<x<1`, define uniform reflection-prefix comparability by requiring one `c>0` that bounds both

`‖P_x(N)/P_{1-x}(N)‖` and `‖P_{1-x}(N)/P_x(N)‖`

from below for every `N`. Lean proves the sharp classification

`JASGammaThetaReflectionPrefixesUniformlyComparable x ↔ x = 1/2`.

In particular, specialization to `x=1/4` proves unconditionally that the literal diagonal Gamma transport cannot be uniformly conditioned throughout the open strip.

## Paper proof

The preceding module proves the exact local identity `F_x(p)=1-D_x(p)`, strict `0<F_x(p)<1`, and

`Summable D_x ↔ 1/2 < x`.

If `x≤1/2`, the nonnegative defect sum diverges. The finite product estimate

`∏(1-D_n) ≤ exp(-∑D_n)`

forces `P_x(N)→0`. If `x>1/2`, absolute summability of `D_x` gives an infinite product and the corpus nonvanishing theorem for absolutely summable perturbations of one shows its limit is nonzero. Reflection swaps the two regimes unless `x=1/2`; hence one of the two prefix ratios tends to zero. At the fixed point the two prefix products agree exactly. This proves the classification and open-strip counterexample with no hypothesis about Xi zeros.

## Exact route consequence

The killed claim is: the divisor-independent diagonal gauge extracted from synchronized-lcm Gamma weights can provide uniformly conditioned forward/reflected transport across the strip. It cannot.

Full RH chain served by the survivor:

1. synchronized-lcm Gamma gauge gives the exact local factors `F_x(p)`;
2. this theorem eliminates all reflection transport using their diagonal prefix ratios;
3. surviving producer must be genuinely non-diagonal and infinite-support, matching the open datum isolated by `XiCTaylorThetaTailCompletedValuationReflection`;
4. such a producer must preserve prime-Haar prefix Cauchy status between `x` and `1-x`;
5. `xiPrimePoissonHaarPrefixReflectionCauchyCoherent_iff` then forces `Re ρ=1/2` for every Xi divisor;
6. `everyXiPrimePoissonHaarPrefixReflectionCauchyCoherent_iff_riemannHypothesis` closes RH.

This theorem is not RH. It kills a whole diagonal construction class and narrows JAS to non-diagonal infinite-support polarization.

## No-go closure

- **Exact killing theorem/mechanism:** `not_forall_openStrip_jasGammaThetaReflectionPrefixesUniformlyComparable`; square-order prime defect makes one reflected prefix collapse while the other has nonzero limit.
- **Strongest positive survivor:** `tendsto_jasGammaThetaLocalRenormalizedFourthPrefix_zero_iff` and `jasGammaThetaReflectionPrefixesUniformlyComparable_iff` give the sharp product wall and unique conditioned reflection fixed point.
- **New insight:** relative normalization does not rescue separate completion. Gamma sewing cancels first order locally, but its residual quadratic defect makes any diagonal reflected condition number collapse off the critical line. Only non-diagonal infinite-support polarization remains.
- **Lean module:** `GaloisForLFunctions.RHTower.JointAncestryGammaThetaReflectionPrefixConditioningWall`.

## Lean audit

- Direct check: `lake env lean GaloisForLFunctions/RHTower/JointAncestryGammaThetaReflectionPrefixConditioningWall.lean` — PASS.
- Exact leaf: `lake build GaloisForLFunctions.RHTower.JointAncestryGammaThetaReflectionPrefixConditioningWall` — PASS (`12201/12201`).
- Axioms for sharp wall, comparability classification, and open-strip no-go: `[propext, Classical.choice, Quot.sound]` only.
- Umbrella: imported by `GaloisForLFunctions.RHTower`.
- Formal lint: no module-specific forbidden declaration; repository lint still reports pre-existing unrelated reachability errors and large-file warnings.

## Novelty audit

Exact corpus searches returned no prior declaration of this prefix-product or two-sided reflection-conditioning law. Targeted external searches through 2026-08-29 found related but non-matching work:

- Connes--Consani, [The Scaling Hamiltonian](https://arxiv.org/abs/1910.14368): semi-local operator framework and limits of a proposed positivity argument.
- Connes--Consani, [Weil positivity and Trace formula, the archimedean place](https://arxiv.org/abs/2006.13771): archimedean Weil positivity and semi-local program.
- Gonek, [Finite Euler products and the Riemann Hypothesis](https://arxiv.org/abs/0704.3448): RH-conditional approximation by short Euler products, not this factor or conditioning wall.
- Lie--Sullivan, [Quasi-invariance of countable products of Cauchy measures under non-unitary dilations](https://arxiv.org/abs/1611.10289): Kakutani square-summability classification, not the synchronized-lcm Gamma factor.

No exact external match was found. This is a targeted audit, not proof of global literature novelty.

## Log

- 2026-08-29 — conjecture originated from named corpus results and frozen with explicit JAS→RH chain.
- 2026-08-29 — paper proof closed, formalized in Lean, exact leaf audited, and diagonal relative-gauge subroute retired.
