# T2 adaptive cubic energy and supercritical no-go

- **ID:** T2-ACE-NOGO
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md` · T2 ordered-prime shell defect
- **Statement:** Natural Wold square energy at `1/2 < t < 3/2` forces the endpoint residual
  rate `N^(-2t/3)`; consequently `WoldNatResidualSquareEnergy t` is false for every
  `t > 3/4`.

## Goal

Kill the entire supercritical T2 square-energy branch and discharge its strongest positive
survivor:

`E(t) → endpoint natural rate 2t/3 → ordered prime-log rate 2t/3`.

For `t>3/4`, this crosses the corpus's unconditional half-density obstruction. For
`1/2<t<3/4`, it strictly improves the previous fixed-square-root-window transfer
`c<t-1/4` to the endpoint `c=2t/3`, reducing the remaining T2 producer burden.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorem, targeted `lake build` green, axiom audit PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Corpus basis and conjectures

Write

`R N = xiHeatCassiniWoldNatResidualLogDiscrepancy N`

and

`E(t) := Summable (fun N => N^(2t-1) |R N|^2)`.

Mandatory corpus search found:

- `woldNatResidual_log_persistence`, the source-specific one-sided logarithmic modulus;
- `WoldNatResidualSquareEnergy`, the literal weighted Hilbert energy;
- exact natural/ordered prime transport through
  `xiHeatCassiniOrderedWoldPartialMass_eq_natWeightSum` and `xiMassNthPrimeLogHeight`;
- `not_eventually_xiHeatCassiniOrderedWoldResidualLogDiscrepancy_exp_rate_of_half_lt`, the
  unconditional half-density obstruction;
- no adaptive power window, no `2t/3` transfer, and no supercritical energy no-go.

Conjecture T2-ACE-A (adaptive endpoint transfer): if `1/2<t<3/2` and `E(t)`, then

`∃ B>0, ∀ᶠ N, |R N| ≤ B N^(-2t/3)`.

Conjecture T2-ACE-B (closed supercritical classification):

`∀ t, 3/4<t → ¬E(t)`.

## Paper proof [PROVED HERE]

Set `a=1-2t/3` and use the integer radius `H_N=⌈N^a⌉`. The constraints
`1/2<t<3/2` give `0<a<1`, hence eventually `1≤H_N≤N/2`.

On the sign-appropriate interval `[N,N+H_N]` or `[N-H_N,N]`, logarithmic persistence
gives

`|R N| ≤ mean |R n| + 2H_N/N`.

Every index in either interval is at least `N/2`. Since `2t-1>0`, finite
Cauchy--Schwarz and total energy `Q` give

`mean |R n| ≤ sqrt(2^(2t-1) Q) N^(-(2t-1+a)/2)`.

The defining balance `a=1-2t/3` makes `(2t-1+a)/2=2t/3`; the drift has the same
exponent because `a-1=-2t/3`. This proves T2-ACE-A at the endpoint, not merely below it.

For arbitrary `t>3/4`, lower the radius to some `u` with `3/4<u<1` by monotonicity of
the nonnegative weighted energy. T2-ACE-A gives rate `2u/3>1/2`. Evaluating the natural
bound at `nthPrimeSubtype N` and simplifying produces the forbidden ordered exponential
rate, proving T2-ACE-B.

More explicitly, put

`Q = ∑ n, n^(2t-1)|R n|²`.

Both sign-selected windows have cardinality `H_N+1 ≥ N^a`, and every member `n` obeys
`N≤2n`. Therefore

`N^(2t-1) ∑window |R n|² ≤ 2^(2t-1) Q`.

Finite Cauchy--Schwarz gives

`mean_window |R n| ≤ sqrt(2^(2t-1)Q) N^(-(2t-1+a)/2)`.

Logarithmic persistence gives the pointwise estimate after adding `2H_N/N`. Since
`H_N≤N^a+1≤2N^a` eventually and

`(2t-1+a)/2 = 2t/3 = 1-a`,

we obtain the dependency-closed endpoint bound

`|R N| ≤ (sqrt(2^(2t-1)Q)+4) N^(-2t/3)`.

Energy monotonicity follows termwise from `u≤t` and `N≥1`; the zero index vanishes because
both weights have positive exponent. For `t>3/4`, choose
`u=(3/4+min(t,1))/2`. Then `3/4<u<1`, `E(t)→E(u)`, and the endpoint transfer supplies
an ordered rate `2u/3>1/2`. The corpus theorem
`not_eventually_xiHeatCassiniOrderedWoldResidualLogDiscrepancy_exp_rate_of_half_lt`
contradicts it. No premise remains.

## Hostile tests

- Fixed square-root windows cannot prove this: their additive drift is exactly `N^(-1/2)`.
- The adaptive exponent is forced by balancing Cauchy cost and logarithmic drift; changing it
  worsens one of the two terms.
- `t<3/2` is needed only for a sublinear window. Arbitrary supercritical `t` is handled by
  downward energy monotonicity to `u<1`.
- The result does not infer a producer from RH or from a pointwise estimate; direction is only
  energy to decay.
- The no-go conclusion is premise-free after quantifying `t`; it does not assume a zeta zero or RH.
- At `t=3/4`, endpoint rate is exactly `1/2`; the strict half-density obstruction does not kill
  this boundary, so no endpoint overclaim is made.

## Novelty audit (2026-08-30)

Internal exact-statement search was negative. Closest corpus theorem uses a fixed square-root
window and loses one quarter-power. Closest square-energy parent theory concerns Chebyshev sharp
prime windows and square-aperture positive excess, not the natural Wold residual or this adaptive
cubic balance.

External targeted search checked current Mertens-error literature, including Broadbent--Fiori--
Kadiri--Ng--Wilk's August 2026 explicit Mertens bounds and Bhattacharya--Martin--Simpson's 2025
weighted-prime error correlations. Those works study explicit pointwise bounds, zero formulas,
or limiting distributions; neither states weighted discrete square-energy implication T2-ACE-A
nor supercritical classification T2-ACE-B. The `2/3` interpolation balance is structurally related
to classical one-dimensional Gagliardo--Nirenberg interpolation, but its exact weighted Wold
endpoint and RH-route obstruction were not found.

- https://arxiv.org/abs/2608.01498
- https://arxiv.org/abs/2507.13504

Novelty status: **plausibly new; exact-statement corpus and literature search negative as of
2026-08-30**.

## No-go closure

- **Exact killing theorem/mechanism:** T2-ACE-B excludes every square-energy radius strictly
  above `3/4` by adaptive cubic persistence plus the closed half-density obstruction.
- **Strongest positive survivor:** T2-ACE-A, the endpoint `2t/3` energy-to-pointwise transfer.
- **New insight:** The former `1/4` loss was a fixed-window artifact. Source persistence and
  Hilbert energy balance cubically, with forced window exponent `1-2t/3`.
- **Status:** paper proof dependency-closed; exact survivor and killing theorem formalized in Lean.

## Lean certificate

- Module:
  `GaloisForLFunctions.RHTower.XiHeatCassiniWoldNaturalAdaptiveCubicEnergyNoGo`
- Endpoint survivor:
  `exists_woldNatResidual_power_rate_twoThirds_of_squareEnergy`
- Downward energy law:
  `woldNatResidualSquareEnergy_mono`
- Closed killing theorem:
  `not_woldNatResidualSquareEnergy_of_threeQuarter_lt`
- Direct `lake env lean` source check: PASS.
- Targeted module build: PASS.
- Axioms: `[propext, Classical.choice, Quot.sound]` only.
- Umbrella: imported by `GaloisForLFunctions.RHTower`.
- Global lint: module reachable and clean; repository lint remains red only on unrelated concurrent
  unreachable modules.

## Log

- 2026-08-30 — created directly in 1-in-progress after corpus audit, exact RH-chain freeze,
  hostile testing, and current-literature audit.
- 2026-08-30 — T2-ACE-A and T2-ACE-B proved on paper; exact cubic exponent retained after
  hostile endpoint testing.
- 2026-08-30 — exact survivor and unconditional supercritical no-go formalized, wired, directly
  checked, targeted-build audited, and axiom-audited.
