# T2 natural square-energy three-quarter transfer

- **ID:** T2-NSE-3Q
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md` · T2 ordered-prime shell defect
- **Statement:** For the genuine centered natural Wold residual `R N`, summability of
  `N^(2t-1) |R N|^2` forces every power rate `c < t - 1/4`; cofinal such energies for
  `1/4 < t < 3/4` force RH.

## Goal

Close T2's two receiver burdens in one source-specific theorem:

`literal Wold natural square-energy spectrum below 3/4`
`→ strict-half natural Wold power spectrum`
`→ zero Chebyshev width`
`→ RH`.

This does not assume a zero, terminal decay, or RH. It leaves exactly one producer: prove the
cofinal weighted square energies from the unsplit Wold current.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorem
  `riemannHypothesis_of_woldNatResidualSquareEnergy_cofinal_threeQuarter`, targeted
  `lake build` green, axiom audit PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Corpus basis and exact conjectures

Write

`R N = xiHeatCassiniWoldNatResidualLogDiscrepancy N`

and

`E(t) := Summable (fun N => (N : ℝ)^(2*t-1) * |R N|^2)`.

Corpus inputs, found with `scripts/formal_tools.py research`, are:

- `woldNatResidual_right_sqrt_persistence` and
  `woldNatResidual_left_sqrt_persistence`: a spike at `N` persists across one half of the
  `N ± sqrt N` window, with error `O(N^(-1/2))`.
- `woldNatResidualPowerSpectrum_iff_sqrtMeanSpectrum`: bounded critical-window local `L¹`
  means recover the full pointwise power spectrum.
- `riemannHypothesis_iff_woldNatResidualPowerSpectrum_zero` and
  `riemannHypothesis_iff_woldNatResidualAllStrictHalfPowerRate`: all strict half-rates are RH.
- `not_eventually_xiHeatCassiniOrderedWoldResidualLogDiscrepancy_exp_rate_of_half_lt`:
  no genuine Wold residual can cross the half-density rate.

Conjecture T2-NSE-3Q-A (single-radius transfer): if `1/4 < t ≤ 3/4` and `E(t)`, then
`WoldNatResidualPowerSpectrum (3/4 - t)`. Equivalently, every `0 < c < t - 1/4`
has an eventual bound `|R N| ≤ C N^(-c)`.

Conjecture T2-NSE-3Q-B (cofinal capstone):

`(∀ t, 1/4 < t → t < 3/4 → E(t)) → RiemannHypothesis`.

## Paper proof [PROVED HERE]

Let `Q = ∑ N, N^(2t-1)|R N|²`, which is finite and nonnegative. For the exact corpus
window `W_N = [N-sqrt N,N+sqrt N]`, `|W_N|=2 sqrt N+1`. For `N≥4` and `n∈W_N`,
`n≥1` and

`sqrt n ≤ 2 |W_N|`.

Fix `0<c<t-1/4` and put `d=2c-(2t-1)`. Then `d<1/2`; since `n≥1`, monotonicity in
the exponent gives

`n^d ≤ n^(1/2) = sqrt n ≤ 2 |W_N|`.

Consequently

`n^(2c)|R n|² = n^(2t-1)n^d|R n|²`
`≤ 2 |W_N| n^(2t-1)|R n|²`.

Summing on `W_N` and bounding the finite nonnegative energy sum by `Q` gives

`∑_(n∈W_N) n^(2c)|R n|² ≤ 2 |W_N| Q`.

Finite Cauchy--Schwarz now gives

`mean_window(n^c |R n|)`
`≤ |W_N|^(-1/2) * (2 |W_N| Q)^(1/2) = sqrt(2Q)`.

Thus the critical-window weighted `L¹` mean is eventually bounded. The dependency-closed corpus
theorem `woldNatResidualPowerSpectrum_of_sqrtMeanSpectrum` converts this into
`WoldNatResidualPowerSpectrum (3/4-t)`, proving T2-NSE-3Q-A.

For T2-NSE-3Q-B, fix any `0<c<1/2` and choose `t=(c+1)/2`. Then
`1/4<t<3/4` and `c<t-1/4`; T2-NSE-3Q-A supplies the required rate. Hence every strict
half-rate holds, and `riemannHypothesis_iff_woldNatResidualPowerSpectrum_zero` gives RH.

Every step uses an existing closed Lean theorem or elementary finite inequalities. No analytic
or asymptotic premise remains.

## Hostile tests

- A single energy at `t < 3/4` cannot reach RH: it controls only rates below `t-1/4`.
- Polynomial prime-log graph smoothness corresponds to no positive power `t`; it cannot be
  silently promoted to this premise.
- Dropping Wold square-root persistence restores the generic `1/2` point-evaluation loss.
- Endpoint `t=3/4` is not needed; only the cofinal strict spectrum is used.
- The positive and negative persistence halves must both be retained; one-sided sign control is
  insufficient.
- Initial values `N=0,1,2,3` are finite-prefix noise and may not enter an asymptotic exponent
  argument.

## Novelty audit (2026-08-30)

Internal research returned the persistence and RH receiver theorems above, but no weighted global
square-energy transfer, no `1/4` loss theorem, and no `3/4` ceiling for this Wold residual.

External targeted search found nearby but different results: Zhao proves RH criteria from the sign
of first integrals of classical Mertens errors, Bhattacharya--Martin--Simpson study correlations and
limiting logarithmic distributions of weighted prime-counting errors, and Brent--Platt--Trudgian
study mean square of the prime-number-theorem error. None states this discrete weighted `ℓ²`
transfer, uses Wold square-root persistence, or identifies the `3/4` ceiling.

- https://arxiv.org/html/2411.18903v2
- https://arxiv.org/abs/2507.13504
- https://arxiv.org/abs/2008.06140

Novelty status: **plausibly new; exact-statement search negative as of 2026-08-30**.

## Rejected strengthening and pivot

The initial supercritical claim `t>3/4 → ¬E(t)` was removed after hostile proof testing. The
fixed square-root persistence law has an additive `N^(-1/2)` drift, so it cannot by itself
promote any mean estimate to a pointwise exponent above `1/2`. This does not affect the proved
strict-subhalf transfer. A possible separate survivor uses an adaptive window of length `N^a`;
balancing averaging against logarithmic drift predicts the sharper rate `c<2t/3`, but that is not
used or claimed here.

## New insight

Source persistence recovers one quarter-power from global Hilbert energy, moving T2's sufficient
cofinal radius from the generic graph threshold `1` to `3/4`. The two former receiver burdens—
terminal control and height-cofinal zero-width transfer—are now one explicit literal-source energy
producer.

## Lean certificate

- Module:
  `GaloisForLFunctions.RHTower.XiHeatCassiniWoldNaturalSquareEnergyThreeQuarter`
- Single-radius mean transfer:
  `woldNatResidualSqrtMeanSpectrum_of_squareEnergy`
- Single-radius pointwise transfer:
  `woldNatResidualPowerSpectrum_of_squareEnergy`
- T2 capstone:
  `riemannHypothesis_of_woldNatResidualSquareEnergy_cofinal_threeQuarter`
- Direct source check: PASS.
- Targeted module build: PASS.
- Axioms: `[propext, Classical.choice, Quot.sound]` only.
- Umbrella: imported by `GaloisForLFunctions.RHTower`.
- Global lint: new module is reachable and clean; repository lint remains red only on unrelated
  concurrently present unreachable modules.

## Log

- 2026-08-30 — created directly in 1-in-progress after corpus and literature audit.
- 2026-08-30 — T2-NSE-3Q-A/B proved on paper; supercritical overclaim rejected after hostile test.
- 2026-08-30 — exact theorem formalized, wired, targeted build and axiom audit passed.
