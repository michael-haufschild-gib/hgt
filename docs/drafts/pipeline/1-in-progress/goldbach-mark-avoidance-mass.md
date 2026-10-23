# Mass missed by subpower auxiliary marks

- **ID:** goldbach-mark-avoidance-mass
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** [Varying-shift audit](goldbach-varying-shift-source-audit.md).
- **Statement:** Determine the exact mass on which every permitted auxiliary
  mark vanishes, and audit the attainable approximation precision.

## Exact candidate and scope

Fix `0<α<β<1`, put `L=log T`, and let `P_T` be the product of the primes
`exp(L^α)<ℓ≤exp(L^β)` which do not divide the positive even target `T`.
Define the weighted prime count

`V(T)=Σ_{p<T, p prime} (log p) 1_{gcd(T−p,P_T)=1}`.

**Candidate M1:** `V(T)~T L^(α−β)`, uniformly as even `T→∞`.
This is expected to be a routine consequence of classical sieve inputs,
not new scientific knowledge. The paper derivation below is under audit;
no Lean theorem or novel analytic claim is recorded as complete.

For the inspected source's encompassing range, `α=0.1`, `β=0.2`.
An approximation made only from nonempty divisor marks using these primes
vanishes on the set counted by `V(T)`. If `M(T−p)` is any such
approximation, then, exactly,

`Σ_{p<T} (log p)|1−M(T−p)|² ≥ V(T)`.

The same support lower bound holds for absolute error. This tests an
absolute-norm method of removing marks; it does not disprove signed
cancellation or a transfer using the sign of the residual.

## Finite positive survivor

On any finite measured set, let `Z` be the subset where every allowed
mark vanishes. Among **all** functions vanishing on `Z`, the minimum
of `Σ w|1−f|²`, with `w≥0`, is exactly `Σ_Z w`, attained by
`f=1` off `Z` and `f=0` on `Z`. The error decomposes as

`Σ w|1−f|² = Σ_Z w + Σ_{outside Z} w|1−f|²`.

When marks are allowed arbitrary coefficients on their available
divisors, the minimizer is represented by assigning each available
divisor the reciprocal of their number. Thus the support bound is
sharp in that class. This is ordinary orthogonal projection, not a
novel positive theorem. The positive arithmetic survivor sought in M1
is the explicit prime-plus-band-avoiding count, including its scale.

The local `twin-prime/DivisorMarkTransfer.lean` was read: it proves the
analogous exact minimum when the support consists of **all proper
divisors**, with the missed set being prime shifts. It does not state
M1 or this varying-band prime asymptotic. No conditional analytic
interface will be added to fill that gap.

## Paper derivation to audit

The inputs are classical Mertens and Bombieri–Vinogradov. The latter's
uniform reduced-class statement is recorded in
[Kedlaya, Theorem 17.1](https://kskedlaya.org/ant/chap-bombieri.html);
Mertens' product asymptotic is stated in
[Lichtman–Martin–Pomerance, §4](https://math.dartmouth.edu/~carlp/proc14569.pdf).
Their proofs are not replaced by the newer conditional parity sources.

1. **Euler product.** On reduced residue classes modulo `P_T`, avoidance
   of `T` modulo each pool prime has exact density
   `δ_T=∏_{ℓ|P_T}(1−1/(ℓ−1))`.
   The ratio of each factor to `1−1/ℓ` is
   `1−1/(ℓ−1)²`. The product of these ratios tends to one because
   the lower endpoint tends to infinity. Mertens therefore gives
   `δ_T~L^(α−β)` before puncturing. Removing primes dividing `T`
   changes its logarithm by
   `O(log T·exp(−L^α))=o(1)`, uniformly in `T`.

2. **Finite inclusion–exclusion.** Let `R` be an even integer comparable
   to `C log L`, with `C` fixed sufficiently large. The even and odd
   Bonferroni truncations bound the avoidance indicator above and below.
   Their divisors have at most `R+1` factors and hence size at most
   `D=exp((R+1)L^β)=T^o(1)`. Each divisor coefficient is `+1` or `−1`.

3. **Prime progression errors.** Every divisor `d` retained in a
   truncation is coprime to `T`; divisibility of `T−p` selects the
   reduced class `T (mod d)`. Since `D=T^o(1)`, classical
   Bombieri–Vinogradov bounds the sum of errors by `O_A(T L^(−A))`
   for each fixed `A`. Replacing von Mangoldt by the prime logarithm
   costs at most `O(D sqrt(T) L²)=T^(1/2+o(1))`, which is negligible.
   The endpoint `p<T` can be implemented at `T−1`, changing the main
   length only by one; this does not change the asymptotic.

4. **Euler-product tails.** Put `W=Σ_{ℓ|P_T}1/(ℓ−1)`.
   Mertens gives `W=(β−α)log L+O(1)`. The degree-`r` elementary
   symmetric sum is at most `W^r/r!`. For `R=C log L` with `C`
   sufficiently large in terms of `A`, the tail beyond `R` is
   `O_A(L^(−A))`, by the ratio bound on successive terms and
   `r!≥(r/e)^r`. Thus both truncations have main term
   `T δ_T+O_A(T L^(−A))`.

Taking `A>β−α` would prove M1. All constants can depend on the fixed
band exponents and requested precision, but not on `T`.

## Consequence and remaining work

If M1's derivation and dependencies pass audit, every such approximation
has squared error at least `(1+o(1))T L^(α−β)` on the prime measure.
At `α=0.1,β=0.2`, this is much larger than `T/L`, the expected
scale with one prime logarithm for two-prime representations. Enlarging
the class of marked functions to all functions supported off the
avoidance set does not improve this minimum.

The corresponding signed residual is a separate problem. The support
floor forces an analysis of that residual; it does not force its sign.
A successful prime-detecting argument must supply that signed input,
or use a different family whose support includes the relevant primes.

- Paper status: candidate derivation recorded; hostile audit and exact
  local input inspection pending.
- Lean status: M1 and its analytic dependencies not formalized for this
  chain. Generic finite minimum has an existing related certificate,
  but is not being presented as the desired arithmetic theorem.
  Corpus search exposed `RHTower.tendsto_primeRecipSum_sub_logLog`
  in `RHTower/MertensSecondPrimeRecipSum.lean`; its complete final
  statement and proof were read. It has no analytic assumption binder.
  Its import closure has not been recompiled or audited in this batch.
  All 65 lexical `Bombieri` hits were paged; no checked prime
  Bombieri–Vinogradov capstone was found among them. This is a search
  result, not proof of repository-wide absence.
- Novelty status: classical sieve corollary expected; no scientific
  advance claimed.
- No-go closure: **not complete**. Keep route active until the positive
  arithmetic survivor and its exact Lean status are resolved.

## Log

- 2026-10-23 — Identified the full mark-avoidance support, derived its
  candidate uniform prime asymptotic, and separated signed residual
  control from absolute approximation.
