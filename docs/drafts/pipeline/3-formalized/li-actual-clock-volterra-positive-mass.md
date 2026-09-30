# Actual clock response: Volterra identity and divergent positive mass

- **ID:** LI-CURRENT-VOLTERRA
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean); generic structural survivor, significance unverified
- **Parent:** [actual-current scaling route](../1-in-progress/li-actual-current-small-mass-sinc-scaling.md)
- **Statement:** Complete-source clock response has divergent positive-part mass and is positive at arbitrarily large clocks, without RH or a reciprocal-moment sign premise.

## Exact source theorem

Write `R_j=thetaCuspRawEvenMoment j`, `C_j=R_j/R_0>0`, `M_j=normalizedPrimeArchMoment j`. Already formal clock series is `S(w)=Σ_j(-1)^j(16w)^jM_j/(2j+1)!`. Set

`B(t)=Σ_j C_j t^(2j)/[(2j)!]²`,
`F(t)=t S(t²/16)=Σ_j(-1)^jM_j t^(2j+1)/(2j+1)!`.

For every `t≥0`, `∫_0^t F(s)B(t−s)ds=tB'(t)`. For `t>0`,

`∫_0^t max(F(s),0)ds ≥ tB'(t)/B(t) → +∞` as `t→+∞`.

Exact substitution gives `∫_0^t max(F(s),0)ds=8∫_0^(t²/16)max(S(w),0)dw`. Hence positive-part clock mass diverges and `∀W_0 ∃w>W_0, S(w)>0`. This gives no everywhere-positive sign, negative witness, uniform finite-current sign, zero-exclusion producer or RH conclusion.

The already formal clock limit also transfers each positive `S(w)`, `w>0`, to an actual-current corridor: `C_n(w/(n+1)²)>0` for all sufficiently large natural `n`. Therefore such corridors exist beyond every clock threshold. Paper proof: the positive masses tend to zero, clock is identically `w`, and the normalized current tends to the strictly positive `S(w)`; its denominator is positive. This is an eventual sign along prescribed shrinking masses, not all-mode positivity at a single mass.

## Dependency-closed paper proof

1. Existing scalar recurrence `303R_(j+1)≤(32j+17)R_j` gives `C_j≤(32/303)^j j!` by induction. Since `(2j)!≥j!`, `B` terms on `|t|≤T` are bounded by `[(32/303)T²]^j/j!`. Derivative terms have the same factorial envelope with a polynomial factor. Existing `|M_j|≤A150^(−j)` supplies compact-uniform absolute convergence of `F` and derivatives. All raw moments are strictly positive; no degrees are omitted.
2. Put `f_j=(-1)^jC_j/(2j)!`. Exact source germ identity `XiC'+zGXiC=0`, divided by `R_0`, gives `Σ_(j+k=n)M_j f_k=−2(n+1)f_(n+1)`.
3. Compact absolute convergence permits multiplication and termwise integration. Beta integral is `∫_0^t s^(2j+1)(t−s)^(2k)ds=(2j+1)!(2k)!t^(2j+2k+2)/(2j+2k+2)!`. For `r≥1`, convolution coefficient at `t^(2r)` is `Σ_(j+k=r−1)(−1)^jM_jC_k/(2k)!`, divided by `(2r)!`. Multiply recurrence by `(-1)^(r−1)` to get `2r C_r/[(2r)!]²`, exactly coefficient of `tB'(t)`. Both vanish at zero.
4. Positive coefficients give `0<B(t−s)≤B(t)` for `0≤s≤t`. Therefore `F(s)B(t−s)≤max(F(s),0)B(t)`. Integrate and divide by `B(t)>0`.
5. Put `b_j=C_j/[(2j)!]²>0` and `H_K(t)=Σ_(j<K)b_jt^(2j)`. Since `B(t)≥b_Kt^(2K)`, each term of `H_K/B` tends to zero. Weighted-degree identity gives `tB'(t)≥2K(B−H_K)`. Arbitrary `K` proves `tB'/B→+∞`.
6. On `s≥0`, `max(F(s),0)=s max(S(s²/16),0)`. Substitute `w=s²/16`, `s ds=8dw`. If `S≤0` on any tail, its positive-part integral would be bounded by a finite compact prefix, contradiction.

## Dependency audit and significance

- `PrimeArchThetaScoreMomentRecurrence.lean:124`: all-`j` scalar recurrence. Polynomial-square test `P(y)=y^j` accesses only index `2j` and is not this dependency.
- `XiCTaylorThetaTailMomentLogConvex.lean:16`: strict raw moment positivity.
- `PrimeArchThetaAllOrderCumulant.lean:92`: actual all-order central recurrence.
- `LiEvenCrossActualCurrentClockSeries.lean`: literal source clock and absolute convergence.
- Two independent read-only audits agree on full convergence, beta normalization, weighted-degree divergence and factor eight. Root spot-checked scalar recurrence and central identity.
- Generic factorial transformation and positive-kernel comparison are the mechanism. No world-novelty or significant new RH mechanism claim. This is exact positive salvage from the generic inverse-convolution sign obstruction.
- Prior corpus retrieval has pending/stale compiler metadata; no absence claim. Narrower calibrated-floor/source-resolvent search still running.

## Open arithmetic core

Positive `B,B'` do not imply pointwise `F≥0`; differentiated inverse Volterra resolvent alternates signs generically. [Calibrated Gaussian–Hermite obstruction](../2-fully-proven/li-mass-calibrated-score-floor-obstruction.md) now matches literal actual `R_0` and full prescribed polynomial floor on paper while retaining a negative cumulant determinant. Actual theta lattice, full moment sequence and source membership remain unmatched. Theta pointwise-sign route remains in progress. Literal Volterra, positive-mass and cofinal-corridor theorems on this card are Lean-closed; the separate countermodel construction is paper-only.

## Final formal closure

Seven leaves are wired into `RHTower.lean`: `LiEvenCrossActualCurrentClockRegularity`, `LiClockVolterraPositiveMass`, `LiEvenCrossActualClockBorelSource`, `LiEvenCrossActualClockBorelGrowth`, `LiEvenCrossActualClockCumulantConvolution`, `LiEvenCrossActualClockVolterra`, and `LiEvenCrossActualClockPositiveMass`.

Literal source capstones in `LiEvenCrossActualClockPositiveMass.lean`:

- `liEvenCrossActualClock_logDegree_le_clockPositiveMass`: exact derivative-ratio bound with multiplier eight.
- `liEvenCrossActualClockResponse_positiveMass_tendsto` and `liEvenCrossActualCurrentClockSeries_positiveMass_tendsto`: response and clock positive-part mass tend to infinity.
- `liEvenCrossActualCurrentClockSeries_positive_cofinally`: positive clock value beyond every real threshold.
- `liEvenCrossSquareMassAdjacentCurrent_eventually_pos_of_clockSeries_pos`: exact shrinking-mass corridor at each positive clock value.
- `liEvenCrossSquareMassAdjacentCurrent_positiveCorridors_cofinally`: unconditional actual positive corridors beyond every clock threshold.

Every named `lake build --old` and final exact `lake env lean <leaf>` passed. All 56 public declarations across these leaves passed foundation-only axiom audits. Root capstone named build passed 12,573 jobs, leaf 97 seconds; final direct output is empty. Root evidence: `/tmp/hgt-li-actual-clock-positive-mass-{build,axioms,final}.log`. Earlier source/growth and generic logs are recorded below; pole leaves' exact terminal build/direct/axiom outcomes are tool-transcript evidence, with scratch `/tmp/li_pole_audit_actual_clock_axioms.lean`. Root inspected their finite recurrence, beta integration, complete Cauchy-product domination and source normalization, and the source capstone axiom audit checks their dependencies transitively.

Latest whole-tree lint before these additions remains red on 13 unrelated external unreachable modules. All seven leaves are wired; index/lint refresh follows completion of the separate envelope work. This is targeted formal closure, not a clean global gate claim. No proof debt, added RH premise, numerical experiment or heartbeat override.

## Formal plan

1. Actual `B` series: compact summability, positivity/monotonicity, weighted-degree ratio divergence; actual clock continuity from its local factorial envelope.
2. Exact source coefficient recurrence and complete-source convolution identity.
3. Positive-part bound, clock substitution, divergent mass and cofinal-positive capstone.
4. Named leaf builds, final exact leaf checks, `/tmp` axiom audits, umbrella wiring, index/lint. Preserve unrelated external failures.

## Log

- 2026-09-29 — Candidate recorded in parent before hard work. Independent audits closed paper proof; formal plan recorded before implementation. RH and global source sign remain open.
- 2026-09-30 — Disjoint Lean work started: actual Borel source/growth; exact cumulant convolution/Volterra identity; generic positive-part comparison/substitution; root actual-clock continuity and source capstone. Latest narrower search returned partial retrieval with inventory complete but predominantly pending/stale compiler metadata; generic resolvent and unrelated Borel hits supply no producer or absence claim.
- 2026-09-30 — `LiClockVolterraPositiveMass.lean` closes all seven generic integral/cofinal/substitution APIs; `LiEvenCrossActualCurrentClockRegularity.lean` closes literal clock continuity and local uniform factorial envelope. Both named `--old` builds and final exact checks passed; all nine public axiom audits returned only foundations. Root read the complete generic proof, factor-eight substitution and axiom output, then wired both leaves. Actual-source convolution/growth/capstone remain pending, so card remains stage two.
- 2026-09-30 — Actual Borel source and growth leaves are final: both named `--old` builds and exact direct audits passed without own diagnostics; all 32 public APIs use only foundations (`/tmp/hgt-li-borel-source.yc03VC/`). Root inspected actual normalization, factorial induction, derivative identity, exact finite-prefix inequality and ratio-divergence proof, read all axiom output, and wired both leaves. Complete source convolution and literal positive-mass capstone remain pending.
- 2026-09-30 — Exact full-source Volterra leaves passed named builds, final exact checks and nine axiom audits. Root literal positive-mass/cofinal-current leaf passed named build, six foundation-only axiom audits and final exact check with empty output. Wired all seven leaves and moved this card to stage three. RH and pointwise arithmetic source sign remain open.
