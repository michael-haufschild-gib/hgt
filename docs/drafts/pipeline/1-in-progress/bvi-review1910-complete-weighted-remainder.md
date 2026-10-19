# Complete weighted Bézout–valuation remainder

- **ID:** bvi-review1910-weighted-remainder
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** `docs/reports/review-1910/astra.md`, §6, B1–B4.
- **Statement:** Derive and estimate the literal signed remainder in the damped interior pronic energy, preserving all moving cutoffs, density terms and cross terms.

## Goal

Produce an unconditional arithmetic estimate that improves the complete receiver
`pmBezoutInteriorPronicEnergy`, with an explicit parameter range. Boundedness at
one positive damping below one half is an intermediate target; cofinally small
positive dampings are required by the existing RH receiver. Neither is assumed.

## Requirements and proof plan

- [ ] B1: Exact weighted decomposition from the receiver into the existing
  Möbius Vaughan dictionary; retain every cross term and boundary contribution.
- [ ] B2: Source-specific signed estimate in a stated range, with coefficient
  norms and all cutoff dependence; compare to the unsigned baseline.
- [ ] B3: Insert the estimate into the complete pronic budget and determine
  summability. No claim from leading-log cancellation alone.
- [ ] B4: Audit exactly what unsigned observations determine; any obstruction
  must name its observation class and a useful replacement hypothesis.
- [ ] Dependency-closed paper proof and internal/external parent-theory audit.
- [ ] Unconditional Lean capstones, leaf source checks, axiom audit, umbrella
  wiring, corpus readback, formal lint and owned-scratch cleanup.

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

## Exact candidate and paper proof

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
`delta=(1-2*epsilon)/2>0`. Eventually `(log n)^8<=n^delta`, and
`n*(n+1)<=2*n^2`; hence
`b_epsilon(n)>=(1/2)*n^(-epsilon-1/2)`. The comparison power has exponent
greater than -1. This proves failure of this *majorant* to close the budget,
not divergence of the actual arithmetic energy.

### Observation audit

The five diagonal block energies do not determine the signed mixed sum.
The complete weighted Gram matrix does determine it by the displayed
identity. No pair of arithmetic models sharing the latter and differing in
this energy is possible. This algebra is not a universal sieve-parity
obstruction. The replacement input is an upper bound on the actual mixed
sum relative to the actual diagonal sum, uniform in T at the chosen damping.

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
