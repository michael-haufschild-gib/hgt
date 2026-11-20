# Exact top-band collapse at prime centers, cofactor slice self-duality, and the eight-ninths prime-center shell criterion

- **ID:** elt-top-prime-band-and-reflected-shell-barrier
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** `docs/reports/review-1911/todo.md` #12 · `formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/`
- **Statement:** At every prime center `p` and cutoff `3 ≤ Q ≤ 2p`, the `V = 1` primitive cofactor projection collapses identically to `remainingPrimitivePrimePrice p Q 1 = unrestrictedLargePrimePrice p Q` and `primitiveProjectedFactorial p 1 = completeMidpointFactorial p - (log 4 - log 3)` (hence `ordinaryPrimeBandPrice b b p = unrestrictedLargePrimePrice p (min (2p) ⌊(4p)^b⌋₊) - completeMidpointFactorial p + (log 4 - log 3)` for `b ≥ 1 / 2`, `p ≥ 3`); `unrestrictedLargePrimePrice n Q` decomposes into cofactor slices `v ∈ [2, 4n]` whose short slices (`v Q ≤ 2n`) equal `θ(⌊4n/v⌋) - 2θ(⌊3n/v⌋) + θ(⌊2n/v⌋)` (`= -primeMidpointPrice m` when `n = mv`); and `Θ_ζ ≤ 5 / 6` holds if and only if `unrestrictedLargePrimePrice p ⌊p^{8/9}⌋₊ - reflectedDensity · p ≤ C p^t` across prime centers `p` for every `t ∈ (5/6, 1)`.

## Goal
Prove the exact algebraic collapse of the top ordinary-prime band `a = b` (`V = 1`) at prime centers with zero divisor/proper-power remainder, exhibit the exact Chebyshev-`θ` cofactor-slice self-duality of `unrestrictedLargePrimePrice`, and establish the prime-center `p^{8/9}` reflected-shell equivalence for `Θ_ζ ≤ 5 / 6`.

## Gates
- [x] 0 → 1  in-progress: exact `SquareConductors` interfaces (`ordinaryPrimeBandPrice`, `remainingPrimitivePrimePrice`, `unrestrictedLargePrimePrice`, `reflectedPrimeShellExponent`) isolated
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean module `SquareConductors/TheTopPrimeBandAndReflectedShellBarrier.lean`, `lake --old env lean` green, standard axioms only

## Paper Proof (`[PROVED HERE]`)

1. **Exact `V = 1` (`a = b`) algebraic collapse at prime centers.**
   - For any `n > 0`, `midpointFloorWeight n n = 4 - 2 · 3 + 2 = 0` and `divisibleCofactorFactorial n n = log(4!) - 2 log(3!) + log(2!) = log 24 - 2 log 6 + log 2 = log 4 - log 3`.
   - For `n > 0` and `Q ≥ 3`, `(Icc 1 (4n/n)).filter (Q < · ∧ Prime · ∧ · ∤ n)` is empty because `4n/n = 4` and `4` is composite; hence `divisibleCofactorPrimePrice n Q n = 0`.
   - When `p` is prime, `p.divisors = {1, p}` (`1 ≠ p`). Thus `primitiveProjectedFactorial p 1 = divisibleCofactorFactorial p 1 - divisibleCofactorFactorial p p = completeMidpointFactorial p - (log 4 - log 3)`.
   - Likewise, for prime `p` and `3 ≤ Q ≤ 2p`, `primitive_prime_cofactor_projection` at `V = 1` gives `(∑_{v ∈ (0, 4p], gcd(p,v)=1} truncMoebiusDivisorSum 1 v · primitiveOrdinaryCofactorRow p Q v) = divisibleCofactorPrimePrice p Q 1 - divisibleCofactorPrimePrice p Q p = divisibleCofactorPrimePrice p Q 1`. Splitting the left-hand side at `v = 1` via `prime_cofactor_unit_price` yields `remainingPrimitivePrimePrice p Q 1 - primeMidpointPrice p`. On the right-hand side, for prime `q`, `q ∣ p ↔ q = p`, and at `q = p` the factor `midpointFloorWeight p p = 0` vanishes, so dropping `q ∤ p` leaves the sum unchanged; splitting `(Q, 4p]` at `2p` gives `unrestrictedLargePrimePrice p Q - primeMidpointPrice p`. Canceling `-primeMidpointPrice p` proves `remainingPrimitivePrimePrice p Q 1 = unrestrictedLargePrimePrice p Q`.
   - For `1 / 2 ≤ b` and prime `p ≥ 3`, `(4p)^{b - b} = 1` gives `V = 1`, while `4p ≥ 12 > 9` gives `(4p)^b ≥ √(4p) ≥ 3`, so `3 ≤ min (2p) ⌊(4p)^b⌋₊ ≤ 2p` and `ordinaryPrimeBandPrice b b p` collapses identically.

2. **Exact cofactor-slice decomposition and Chebyshev-`θ` self-duality.**
   - For `q ≥ 1` and `T ≤ 4n`, `⌊T / q⌋ = ∑_{v=1}^{4n} 1_{q v ≤ T}`. Substituting `T = 4n, 3n, 2n` into `unrestrictedLargePrimePrice n Q` and swapping sums expresses `unrestrictedLargePrimePrice n Q = ∑_{v=1}^{4n} cofactorThetaSlice n Q v`.
   - At `v = 1`, every `q ∈ (Q, 2n]` satisfies `q ≤ 2n ≤ 3n ≤ 4n`, so `1 - 2 + 1 = 0` and `cofactorThetaSlice n Q 1 = 0`.
   - Whenever `v ≥ 2` and `v Q ≤ 2n`, we have `Q ≤ ⌊2n/v⌋ ≤ ⌊3n/v⌋ ≤ ⌊4n/v⌋ ≤ 2n`, so `q v ≤ k n ↔ q ≤ ⌊k n / v⌋` lies entirely inside `(Q, 2n]` on the differences `(⌊2n/v⌋, ⌊3n/v⌋]` and `(⌊3n/v⌋, ⌊4n/v⌋]`, yielding `cofactorThetaSlice n Q v = θ(⌊4n/v⌋) - 2θ(⌊3n/v⌋) + θ(⌊2n/v⌋)`. When `n = mv`, this equals `-primeMidpointPrice m`.

3. **Prime-center `p^{8/9}` reflected-shell criterion for `Θ_ζ ≤ 5 / 6`.**
   - Combining `prime_centers_iff_eleven_thirds` with `prime_midpoint_iff_eleven_thirds` and `prime_midpoint_upper_spectrum_iff` equates `Θ_ζ ≤ 5 / 6` to `∀ t ∈ (5/6, 1), ∃ C, ∀ p prime, primeMidpointPrice p ≤ C p^t`.
   - By `large_prime_shell_linear_center` at `b = 5 / 6` and `reflected_prime_shell_at_five_sixths` (`reflectedPrimeShellExponent (5 / 6) = 8 / 9`), `|unrestrictedLargePrimePrice p ⌊p^{8/9}⌋₊ - reflectedDensity · p - primeMidpointPrice p| ≤ A p^t` for every `t > 5 / 6` and every prime `p`, yielding the two-way equivalence.

## Log
- 2026-11-20 — complete paper proof recorded in `2-fully-proven`.
