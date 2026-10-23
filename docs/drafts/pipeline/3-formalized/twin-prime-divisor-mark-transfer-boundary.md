# Exact transfer boundary for proper-divisor marks

- **ID:** twin-prime-divisor-mark-transfer-boundary
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `../1-in-progress/twin-prime-unconditional-programme-2026-10-23.md`
- **Statement:** On a finite weighted set of primes, every proper-divisor mark of the shift has a squared approximation error containing the full twin-prime mass; the signed Möbius residual splits exactly into that negative mass and a composite residual.

## Route under attack

Try to transfer cancellation with nonempty small-prime divisor marks to the
prime values of `p+2`, by making the marks approximate one more accurately.
The precise proposed extension is that the same marks approximate one on the
prime-valued part of the shift. This is false: their restriction there is
identically zero. This does **not** disprove unrestricted shifted-prime
cancellation or the published preprint's own conclusion.

The broader claim that an unrestricted `o(π(x))` cancellation estimate alone
proves twin-prime infinitude has no established implication here. We do not
claim a logical independence theorem about the actual primes.

## Definitions

Let `S` be any finite set of primes and let `w(p) ≥ 0`. For an arbitrary real
coefficient function `c(n,d)`, put

`D(n) = {d : d | n, 1 < d < n}`,

`A_c(n) = Σ_{d∈D(n)} c(n,d)`.

Define `T = Σ_{p∈S, p+2 prime} w(p)` and

`E_c = Σ_{p∈S} w(p)(1-A_c(p+2))²`.

For any real function `a` on natural numbers, define

`R(a) = Σ_{p∈S} w(p) μ(p+2)(1-a(p+2))`,

`C(a) = Σ_{p∈S, p+2 not prime} w(p) μ(p+2)(1-a(p+2))`.

## Dependency-closed paper proof [PROVED HERE]

1. A prime has no divisor strictly between one and itself. Hence
   `A_c(q)=0` for every prime `q`, for every coefficient function `c`.
2. Partition `S` according to primality of `p+2`. On its prime part the
   squared factor `(1-A_c(p+2))²` equals one. Thus

   `E_c = T + Σ_{p∈S, p+2 not prime} w(p)(1-A_c(p+2))²`.

   Every remaining summand is nonnegative, so `T ≤ E_c`. Equality holds
   exactly when every positive-weight composite shift has mark one.
3. For a prime `q`, `μ(q)=-1`. The same partition gives

   `R(A_c) = C(A_c) - T`, equivalently `T = C(A_c)-R(A_c)`.

   This identity retains the arithmetic sign that an absolute error bound
   discards. With `a=0`, it specializes to unrestricted shifted Möbius
   sum = composite shifted Möbius sum minus twin mass.
4. The bound in step 2 is sharp over all proper-divisor coefficient functions.
   Define `c*(n,d)=1/|D(n)|` with real division (zero denominator gives zero).
   If `n≥2` is composite, its definition supplies a divisor `1<d<n`, so
   `|D(n)|>0` and `A_{c*}(n)=1`. If `n` is prime, the mark is zero by step 1.
   Since `p+2≥4`, the error of this coefficient function is exactly `T`.
   No assertion of primality distribution enters this construction.

Dependencies: elementary prime/divisor characterization, finite sum
partition, nonnegativity of squares, and the prime value of the Möbius
function. No asymptotic assertion or unproved analytic estimate is used.

## Internal and external novelty audit

- Internal search: `prime divisibility masks mean square approximation
  vanishes prime pairs`. Inspected
  `RHTower.WeilSingularArithmetic.primeMaskVariance_decomposition` in
  `QuasiRHCalibratedPrimeMasks.lean`: a related completed-square identity for
  coprimality covariance, not this shifted-prime identity.
- [Lü–Wang–Wu, §2.3 and §5.3](https://arxiv.org/html/2610.20242v1): each
  auxiliary weight requires divisibility by primes in specified small
  intervals. Such a weight vanishes on a larger prime. Their limit keeps
  the number of weights fixed before sending the counting scale to infinity.
  No lower bound for twin primes is stated there.
- [Polymath8b, §8](https://arxiv.org/html/1407.4897v4#S8): arithmetic sign
  information and sieve-observation limitations are established prior ideas.
- Verdict for the proposed transfer: **FALSE** on the prime-valued stratum.
  Verdict for the survivor's novelty: **REDISCOVERED** finite orthogonal
  decomposition applied to arithmetic support. No new scientific theorem
  or progress on infinitude is claimed.

## No-go closure

- **Killing mechanism:** every mark is zero on every prime shift.
- **Strongest positive survivor:** exact energy decomposition, equality
  classification and attainable minimum `T`; signed identity
  `T=C(A_c)-R(A_c)` identifies the missing signed estimate.
- **New insight for this route:** better approximation supplies upper
  control of twin mass. A lower bound requires a positive signed surplus,
  not merely a smaller norm error. The elementary principle itself is known.
- **Lean status:** formalized in
  `formal/GaloisForLFunctions/twin-prime/DivisorMarkTransfer.lean`:
  `TwinPrime.divisorMarkError_eq`,
  `TwinPrime.divisorMarkError_eq_twinMass_iff`,
  `TwinPrime.exists_divisorMark_minimum`, and
  `TwinPrime.twinMass_eq_signed_residual_difference`.
  Leaf audit passed with
  `lake --old env lean GaloisForLFunctions/twin-prime/DivisorMarkTransfer.lean`.
  Printed axioms for the three capstones are exactly `propext`,
  `Classical.choice`, and `Quot.sound`. No added analytic premises or axioms.
  All parameters are finite prime sets, nonnegative weights, and arbitrary
  real coefficient functions. Own umbrella: `twin-prime/Main.lean`.

## Next conjecture, without importing a premise into Lean

For the actual prime-weighted dyadic window, seek a direct lower bound on
the composite residual minus the total residual. By the identity above,
merely postulating this surplus would restate the desired prime-pair bound.
Verdict for that postulate alone: **CIRCULAR**. The next admissible route must
prove a signed arithmetic estimate on an independently expanded divisor
sum, with its full residue dependence retained.

## Log

- 2026-10-23 — Exact finite proof completed before Lean. Identified transfer
  failure; strongest positive survivor specified. Main twin-prime goal open.
- 2026-10-23 — Exact survivor, equality classification, and sharpness passed
  Lean and axiom audits. This closes the finite transfer audit only.
