# Fixed minorant separation from one origin moment

Status: [PAPER PROVED; LEAN VERIFIED]
Date: 2026-10-09
Source policy: our Lean corpus only; no web or external papers.

## Claim and plan

Strengthen fixed-probe separation: any strict coefficient minorant with finite
deficit moment at the origin has one fixed negative probe in every late panel.
No coefficient nonnegativity, failed-positivity premise, or convergence at the
selected nonzero shift is needed. Nonnegative strict minorants discharge the
origin-moment premise automatically.

1. Prove truncated potential sums are always finite, for arbitrary coefficients.
   Expose the unconditional real-shift identity and the zero-side limit.
2. Extract a fixed atom from the subcritical integer-log kernel-sum budget.
3. Prove persistent separation using only the origin moment and that atom.
4. Specialize to nonnegative strict minorants with no summability premise.
5. Compile affected leaves, audit every new/changed public result, wire/index,
   run authoritative lint, promote this card, clean owned scratch.

## Dependency-closed paper proof

Let K be the Riemann autocorrelation, K0=K(0)>0. The corpus proves
`sum_{2<=n<=N} K(log n) <= (23/50) K0` for every N.

First, arbitrary truncated potential terms have finite support. If
`n>floor(exp(2|L|+|y|))`, then log n exceeds 2|L|+|y|, so both
`|y+log n|` and `|y-log n|` exceed 2L. Both truncated kernels vanish.
Thus no coefficient or convergence premise is needed for truncated summability
or for the exact fixed-probe identity already proved conditionally in the corpus.

For any nonnegative v vanishing below 2 with some v(q)>0, put
`D=sum_n v(n) K(log n)`. There exists m>=2 with `v(m)K0>2D`.
Indeed, otherwise v(n)K0<=2D for all n>=2. The q inequality forces D>0.
Multiply these inequalities by K(log n), sum over finite ranges, and apply
the kernel budget. Passing to tsum yields `D K0 <= (23/25) D K0`, impossible.
This atom-selection statement itself needs no summability premise: the assumed
pointwise bound provides the finite-sum bound used in the contradiction.

Now let lam<=vonMangoldt on n>=2, v=-weilDeviation(lam), and assume only that
sum v(n)K(log n) converges. Strictness supplies v(q)>0. Select m as above and
set g=v(m)K0-2D>0. For every cutoff L, the truncated nonnegative paired potential
T_L satisfies `T_L(0)<=2D` and `T_L(log m)>=v(m)K_L(0)`.
The unconditional probe identity therefore bounds the actual probe by

`zeroSide(L,m)+4D-2v(m)K_L(0)`.

The zero side tends to zero and K_L(0)->K0, so this upper bound tends to -2g.
Eventually the same fixed probe is <=-g. Increase the integer cutoff to include
m in every expanding panel. No convergence of T_L(log m) is used.

For nonnegative minorants, excess is zero. The corpus's nonnegative-coefficient
convergence theorem gives convergence of the origin potential. Evenness of K
identifies its terms as -2v(n)K(log n), discharging the sole moment premise.

## Corpus audit and boundaries

The local OR search returned 446 declarations across 193 modules and located
the existing moving-probe separation and the recent fixed-witness theorem that
assumes failure of positivity. The truncated-potential search returned four
declarations across three modules; the returned generic truncated summability
arguments impose unnecessary untruncated convergence/control premises.
The finite-support argument is already used inside the older minorant proof.

Inspected the exact kernel budget and the finite-support/atom comparison in
`WeilFullConeMinorantRigidity.lean`. No external novelty claim. This does not
settle fixed-probe separation when the origin deficit moment diverges, nor
general mixed-sign rigidity. No numerical experiments, axioms, or heartbeat
increases.

The exact local query `minorant origin moment` returned no indexed hits. This
is a corpus-local dependency/duplication audit, not an exhaustive semantic or
external novelty claim.

## Exact new insight

The integer-log kernel mass is strictly below half the origin kernel value.
Consequently a nonzero deficit cannot have every atom dominated by twice its
origin moment. This selects a fixed probe without first assuming failure of
any positivity predicate. Finite origin moment is then enough to control its
positive contribution; the negative contribution needs only the selected atom.
Convergence at that probe, or at any other nonzero shift, is unnecessary.

Truncated potential convergence is completely discharged for arbitrary real
coefficients: these sums have finite support. Their exact real-shift probe
identity is therefore unconditional.

## Lean artifacts and validation

Updated `formal/GaloisForLFunctions/RHTower/WeilLogShiftExcessControl.lean`:

- `summable_truncated_potential_term`: arbitrary coefficients, cutoff, and shift.
- `logShift_probe_potential_identity`: unconditional identity, replacing the
  former private identity with convergence arguments.
- `tendsto_logShift_zeroSide`: unconditional fixed-probe zero-side limit.
- The existing `tendsto_logShift_probe_of_summable_potential` retains its
  signature and uses these stronger ingredients. The obsolete private
  truncated-summability helper was removed.

New `formal/GaloisForLFunctions/RHTower/WeilLogShiftFixedMinorant.lean`:

- `exists_deficit_exceeds_twice_origin_moment`
- `exists_fixed_logShift_minorant_separation_of_summable_origin`
- `exists_fixed_logShift_separation_of_nonneg_strict_minorant`

Both final leaves passed `lake --old env lean <leaf> -o <local olean>` with
default heartbeats and no diagnostics. All seven new/changed public theorem
axiom audits passed with exactly `[propext, Classical.choice, Quot.sound]`.
Exported signatures confirm that truncated summability and the identity are
unconditional, atom selection has no summability premise, and the separator
requires only the stated origin moment. Initial local elaboration/indentation
issues were fixed without changing the paper proof or statements.

The new module is wired into `RHTower.lean`. Index refresh and all seven API-row
checks passed. Authoritative global lint passed (exit 0, `formal lint passed`).
Scoped source/umbrella/card whitespace checks passed. All owned jobs exited;
all eleven owned scratch files were removed and their absence verified. Both
exported Lean artifacts are present and newer than their final sources.

## Remaining frontier

Probe and cutoff may depend on lam. The older separation theorem's cutoff
uniform across coefficient sequences with a prescribed deficit remains a
distinct result; this increment supplies a fixed probe for each sequence.

The origin-moment premise remains in the general signed-minorant theorem and
is used explicitly to bound the positive truncated contribution. A zero
totalized moment on a divergent series cannot replace it. Fixed-probe
separation for divergent origin moment and general mixed-sign rigidity remain
open here.
