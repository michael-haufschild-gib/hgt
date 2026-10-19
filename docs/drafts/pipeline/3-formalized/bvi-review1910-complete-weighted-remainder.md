# Complete weighted Bézout–valuation remainder

- **ID:** bvi-review1910-weighted-remainder
- **Stage:** 3-formalized
- **Type:** BRIDGE
- **Source:** `docs/reports/review-1910/astra.md`, §6, B1–B4.
- **Statement:** The complete pronic receiver has an exact five-component Vaughan Gram expansion; existing source cancellation gives a uniform-cutoff logarithmic signed bound, whose majorant is nonsummable below half damping. The active-boundary energy correction is absolutely summable.

## Goal

Produce an unconditional arithmetic estimate that improves the complete receiver
`pmBezoutInteriorPronicEnergy`, with an explicit parameter range. Boundedness at
one positive damping below one half is an intermediate target; cofinally small
positive dampings are required by the existing RH receiver. Neither is assumed.

## Requirements and proof plan

- [x] B1: Exact weighted decomposition from the receiver into the existing
  Möbius Vaughan dictionary; retain every cross term and boundary contribution.
- [x] B2: Source-specific signed estimate in a stated range, with coefficient
  norms and all cutoff dependence; compare to the unsigned baseline.
- [x] B3: Insert the estimate into the complete pronic budget and determine
  summability. No claim from leading-log cancellation alone.
- [x] B4: Audit exactly what unsigned observations determine; any obstruction
  must name its observation class and a useful replacement hypothesis.
- [x] Dependency-closed paper proof and internal/external parent-theory audit.
- [x] Unconditional Lean capstones, leaf source checks, axiom audit, umbrella
  wiring, corpus readback, formal lint execution and owned-scratch cleanup.

## Verification

Direct `lake env lean` audit of the actual leaf passed without warnings or
errors, emitting its `.olean` and `.ilean`. All 17 public declarations have
exactly the standard axiom set `propext`, `Classical.choice`, `Quot.sound`.
The BVI umbrella imports the leaf; regenerated indexes and lexical corpus
readback contain all 17 public declarations. Owned scratch sources and
probes were removed; no owned Lean/build process remains.

Repository-wide `scripts/formal_tools.py lint` was run. Its only errors at
this audit were concurrent modules missing from the ArithmeticCriticalityTheory
umbrella: `ShiftedGroundStateKernelBounds` and
`ShiftedGroundStatePotentialBounds`. No lint error names this leaf. The
global lint gate is therefore not reported as passing.

## Verified starting distinctions

The existing endpoint is damping at least one half. The interior gradient
conservation identity cancels the original energy from both sides. Uniform
renormalized interior remainders therefore do not independently bound that
energy. The exact source is the centered damped divisor prefix, not a raw
Möbius coefficient or a finite-cutoff Ramanujan surrogate.

## Open core

An unconditional signed saving with summable losses for the full receiver has
not been proved. Current work starts with its exact arithmetic kernel and the
applicability ranges of existing estimates.

## Formal interface

The implementation is
[`CompletePronicVaughanCalibration.lean`](../../../../formal/GaloisForLFunctions/BezoutValuationIncidence/CompletePronicVaughanCalibration.lean).
Algebraic identities allow arbitrary real damping and natural cutoffs. Analytic
capstones take damping in `Set.Ioo 0 (1/2)`; none assumes a cancellation or
energy estimate.

- `pmInteriorPronicEnergy_eq_vaughanGram`: all 25 ordered Gram entries.
- `pmPronicVaughanMixedRemainder_logarithmic_bound`: full signed remainder,
  uniform in both cutoffs, with the exact finite initial energy retained.
- `not_summable_pmPronicLogMajorant`: the resulting upper-bound series fails
  the complete summability test throughout the stated damping range.
- `pmPronicVaughan_flip_energy_gap`: exact mixed observation lost by
  diagonal-only data; companion theorems preserve diagonals and identify the
  sign-modified source.
- `summable_pmInteriorPronicEnergy_difference` and
  `pmInteriorPronicEnergy_sub_source_uniformly_bounded`: the active boundary
  contributes an absolutely summable correction to the energy density.

## Exact decomposition and paper proof

Write `rho = Re(1/zeta(1+epsilon))`, `S(n)` for the existing active
sawtooth component, and

`F_n(f) = sum_{1 <= d <= n} f(d) d^(-epsilon) floor(n/d)`.

For arbitrary natural cutoffs U,V, put

1. `v0(n) = F_n(mu_U)`;
2. `v1(n) = F_n(mu_V)`;
3. `v2(n) = -F_n(zeta * mu_U * mu_V)`;
4. `v3(n) = F_n((mu-mu_U) * (1-zeta*mu_V))`;
5. `v4(n) = -n*rho - (S(n+1)-S(n))`.

Then `I_epsilon(n) = sum_i v_i(n)` exactly. Proof: interchange the finite
divisor sum to count multiples, apply the already-proved two-cutoff Möbius
identity pointwise, and subtract the literal density and active difference.
The convolution at d is over `a*b=d`; its Type-II term is supported on
`a>U,b>V` when V is positive. No coprimality condition is discarded or
introduced. The floor endpoint depends on n throughout.

For implementation, the two short sums end at `min U n` and `min V n`.
The negative rectangle is
`sum_{a<=min U n,b<=min V n} mu(a)mu(b) sum_{k<=n/(ab)} w(n,abk)`;
the positive rectangle uses `min U n<a<=n,min V n<b<=n` instead, where
`w(n,d)=d^(-epsilon)*floor(n/d)`. This is the existing
`sum_moebius_weight_eq_rectangular_with_tail` specialized to the actual
receiver weight. In particular `mu(a)mu(b)` is retained as written: replacing
it by `mu(ab)` without coprimality would change the identity.

Coefficient accounting: each Möbius leg has absolute value at most one,
and its squared coefficient norm on a finite set A is exactly
`sum_{a in A} mu(a)^2 <= #A`. For d>=1, the moving weight is nonnegative,
vanishes for d>n, and is at most `n*d^(-1-epsilon)`. If the both-large
rectangle is regrouped into the existing Type-II short coefficient, its
norm budget is the existing `B^2*(L-V)_+` when `L<=(B+1)*V`, or the
all-horizon divisor-moment budget outside that range. None of these unsigned
norm bounds alone supplies the signed Gram estimate below. The cutoff-free
constants in that estimate come from full harmonic Möbius cancellation.

Consequently, with
`G_ij(T)=sum_{1<=n<=T} v_i(n)*v_j(n)/(n*(n+1))`,

`E_epsilon(T)=sum_i G_ii(T)+sum_i sum_{j != i} G_ij(T)`.

This is finite distributivity, so there is no exchange of infinite sums,
uncontrolled remainder or omitted principal/cross term. There is no
logarithmic counterterm in this direct receiver expansion; using the
martingale representation instead would require retaining its compensated
harmonic terms.

### Signed calibration and summability test

The existing source theorem
`RHTower.pmPowerDampedDivisorRemainder_eventually_log_four` gives, for
`0<epsilon<1/2`, eventually

`|A_epsilon(n)| <= 1 + C_epsilon*n^(1-epsilon)/(log n)^4`.

It uses the actual harmonic Möbius cancellation theorem, not an assumed
coefficient norm. Since `|S(n+1)-S(n)|<=1/2`,

`I_epsilon(n)^2 <= 9/2 + 2*C_epsilon^2*n^(2*(1-epsilon))/(log n)^8`.

The finitely many exceptions contribute a fixed nonnegative constant. Thus
the complete receiver has an upper bound by a constant plus a constant times
the partial sums of

`b_epsilon(n) = (n^(1-epsilon)/(log n)^4)^2/(n*(n+1))`, for n>=2.

For every `epsilon<1/2`, this majorant diverges. Indeed, put
`delta=1-2*epsilon>0`. Eventually `(log n)^8<=n^delta`, and
`n*(n+1)<=2*n^2`; hence `b_epsilon(n)>=1/(2*n)`.
Harmonic comparison proves failure of this *majorant* to close the budget,
not divergence of the actual arithmetic energy.

Combining the two exact statements gives a signed estimate for the mixed
remainder, uniform in U,V:

`Mixed(U,V,N+L) <= E_epsilon(N)+9/2 +
  2*C_epsilon^2*sum_{N<n<=N+L} b_epsilon(n) - sum_i G_ii(N+L)`.

Here N,C depend on epsilon only. This is an actual-source estimate with the
complete diagonal subtraction, not an estimate obtained by replacing all
mixed entries by absolute values. Its analytic strength remains that of the
existing source theorem, and the preceding comparison shows why it does not
give bounded energy below one half.

The matching unsigned comparison is obtained from the exact fractional-part
series: split at d=n, use `0<=fract(n/d)<1` on the head and
`fract(n/d)=n/d` on the tail. Integral comparison gives
`|A_epsilon(n)| <= 1 + (1/(1-epsilon)+1/epsilon)*n^(1-epsilon)`
for `0<epsilon<1`. Its squared pronic majorant has order `n^(-2*epsilon)`.
Thus the signed source estimate saves eight logarithmic powers in the same
receiver. The review's `M*invSum(M)^3` bound concerns an undamped truncated
sieve coefficient energy; it is not numerically interchangeable with this
centered damped primitive. Its coefficient norms can enter a future
Type-II estimate, but do not by themselves provide this signed saving.

### Finite active-boundary energy correction

For `0<epsilon<1/2`, the difference between the interior energy and the
centered-source energy is bounded uniformly in the horizon. This strengthens
the existing factor-two comparison without assuming either energy bounded.
Set `D(n)=S(n+1)-S(n)`, so `A(n)=I(n)+D(n)` and `|D(n)|<=1/2`.
Then

`|I(n)^2-A(n)^2| <= 2*|I(n)|*|D(n)|+D(n)^2 <= |I(n)|+1/4`.

The source calibration gives, eventually, `|I(n)|<=3/2+C*n^(1-epsilon)`:
the logarithmic denominator is eventually at least one. As
`n*(n+1)>=n^2`, the absolute energy difference at n is bounded by

`(7/4)/n^2 + C*n^(-1-epsilon)`.

Both comparison series converge. The original signed difference is therefore
absolutely summable, and every finite-horizon difference is bounded by its
total absolute sum. This proves that this particular boundary correction is
harmless. It does not prove any Type-I/II mixed term separately summable.
Parent-theory verdict: `BRIDGE`, from a bounded perturbation and the existing
sublinear source estimate; no new arithmetic cancellation is claimed.

### Observation audit

The five diagonal block energies do not determine the signed mixed sum.
The complete weighted Gram matrix does determine it by the displayed
identity. No pair of arithmetic models sharing the latter and differing in
this energy is possible. This algebra is not a universal sieve-parity
obstruction. The replacement input is an upper bound on the actual mixed
sum relative to the actual diagonal sum, uniform in T at the chosen damping.

A concrete sufficient target is the following dyadic signed estimate.
Let `Gamma_ik(j)` be the same Gram entry restricted to
`2^j<=n<2^(j+1)`. Find `C_epsilon<infinity` and `eta>0` such that

`sum_i sum_{k!=i} Gamma_ik(j) <= -sum_i Gamma_ii(j) +
  C_epsilon/(j+1)^(1+eta)`.

The residual dyadic budgets then sum by the p-series test. This is an
unproved replacement target, not a premise used by any Lean theorem here.
The present pointwise calibration supplies only
`O_epsilon(2^(j*(1-2*epsilon))/(j+1)^8)` per large dyadic block, which
explains the remaining power gap despite its logarithmic improvement.

More precisely, negate a single component k. Every diagonal entry stays
unchanged, whereas the total energy changes by
`4*(sum_j G_kj-G_kk)`. Indeed the new total source is `I-2*v_k`, and
`I^2-(I-2*v_k)^2=4*v_k*(I-v_k)` pointwise. This identifies the missing
signed observation exactly. The sign-modified decomposition is an algebraic
observation test, not another Möbius source or a countermodel satisfying all
arithmetic hypotheses.

### Parent-theory verdict

`BRIDGE`: finite Vaughan transport and transfer of existing harmonic Möbius
cancellation, not a new cancellation theorem. Green–Tao, *Quadratic
uniformity of the Möbius function*, Lemma 4.1, supplies the classical
Type-I/II parent (https://aif.centre-mersenne.org/item/10.5802/aif.2401.pdf).
Matomäki–Radziwiłł–Tao, *An averaged form of Chowla's conjecture*, controls
averaged shifts; its statement does not directly control the moving floor
kernels and all mixed components above
(https://arxiv.org/html/1503.05121v3). Neither comparison establishes novelty
or a sub-half-damping budget. The next producer must improve the power or
estimate the coupled signed Gram sum without taking absolute values first.
