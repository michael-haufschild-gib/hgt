# Wirsing bound and asymptotic for prime-set flip twins

- **ID:** rit-wirsing-flip
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Programme:** RenormalizedIntersectionTheory (open topic 3: twins whose flipped and unflipped primes both have divergent reciprocal sums)
- **Statement:** Let `ω` be completely multiplicative with `|ω| ≤ 1` and prime mean
  `Σ_{p≤n} ω(p) log p/p = β log n + O(1)`, and `L(N) = Σ_{n≤N} ω(n)/n`. Then
  (a) `|L(N)| ≪ (log N)^{b−1}` for every `b ≥ 1`, `b > |1 + β|`;
  (b) `L(N) = C (log N)^β + O(1)` for `0 < β ≤ 1`.
  For the flip `ω_P` of a prime set of relative logarithmic density `κ`
  (`|Σ_{p∈P,p≤n} log p/p − κ log n| ≤ C`), `β = 1 − 2κ`: `L(N) = C(log N)^{1−2κ} + O(1)` for `κ < 1/2`,
  `L` bounded for `κ > 1/2`, and for `κ > 1/4` `L(N)² = o(log N)`, so `HodgeSeparates ω_P`.
  The primes `≡ r (mod q)`, `r` a unit, have `κ = 1/φ(q)`; for `φ(q) < 4` the twin is separated
  (primes `≡ 1` and `≡ 3 mod 4`).

## Proof
1. **Exact identities.** `M(N) = Σ_{n≤N} (ω(n)/n) log(N/n)`: `Σ ω(n) log n/n = L(N) log N − M(N)`,
   `M(N+1) = M(N) + L(N) log((N+1)/N)`.
2. **Chebyshev identity** (`RHTower.Sieve.sum_mul_log_eq_vonMangoldt`, `f(n) = ω(n)/n`):
   `Σ ω(n) log n/n = Σ_{d≤N} Λ(d) ω(d)/d · L(⌊N/d⌋)`.
3. **Non-prime `d`**: `Σ_{d non-prime} Λ(d)/d ≤ 2(log 4 + 4) + 8 + mertensTail` (two Mertens forms),
   and `|L| ≤ 1 + log N`: cost `O(1 + log N)`.
4. **Prime `d`, Abel summation**: with `g(i) = a(i+1) − β(log(i+1) − log i)`, partial sums of `g` are
   the prime mean minus `β log n`, bounded by `C`; the total variation of `k ↦ L(⌊N/k⌋)` is at most
   `H_N`. So the prime part is `β Σ_k (log k − log(k−1)) L(⌊N/k⌋) + O(C(1 + H_N))`.
5. **Divisor swap**: `Σ_k (log k − log(k−1)) L(⌊N/k⌋) = Σ_m (ω(m)/m) log⌊N/m⌋`, within `2` of `M(N)`
   (`log(N/m) − log⌊N/m⌋ ≤ 2m/N`).
6. **Equation**: `|L(N) log N − (1+β) M(N)| ≤ K(1 + log N)`.
7. **Bound**: for `N ≥ 3`, `log N ≥ 1`; `A (log N)^b` with `A(b − |a|) ≥ 2K` is a supersolution:
   `(log N + δ)^b ≥ (log N)^b + bδ(log N)^{b−1}` (Bernoulli).
8. **Asymptotic** (`1 < a = 1 + β ≤ 2`): `U = M/(log N)^a`, `σ = δ/log N ∈ [0,1]`,
   `q = (1+σ)^a ∈ [1 + aσ, 1 + aσ + σ²]` (Bernoulli; concave Bernoulli for `(1+σ)^{a−1}`):
   `U(N+1) = U(N)(1+aσ)/q + Eσ/((log N)^a q)`; the forcing is `≤ K/(a−1)·ΔT`, the drift
   `≤ |U| σ² ≤ 4|U|/(a−1)·ΔT`, `T = (log N)^{1−a}`, by `(a−1)δ ℓ'^{−a} ≤ ℓ^{1−a} − ℓ'^{1−a}` (concave
   Bernoulli) and `ℓ'^a ≤ 4ℓ²`. Hence `U` bounded, `U ± G T` monotone, `c = inf (U + G T)`,
   `|U − c| ≤ G T`, and `|L − a c (log N)^{a−1}| ≤ aG + K`.
9. **Flips**: prime mean `= Σ_p log p/p − 2 Σ_{p∈P} log p/p`; Mertens gives `β = 1 − 2κ`;
   `0 ≤ κ ≤ 1` from the density hypothesis; for `κ > 1/4` pick `b < 3/2`, `b > 2 − 2κ`, so
   `L²/log N ≤ A²(log N)^{2b−3} → 0`.
10. **Residue classes**: `RenormalizedArithmeticPotentialTheory.exists_abs_classMertensSum_sub_le`,
    minus the proper prime powers (`O(1)`).

## Gates
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized: `RenormalizedIntersectionTheory/TheWirsingBoundForFlipTwins.lean`,
  `RenormalizedIntersectionTheory/TheResidueClassTwinsAreSeparated.lean`

## Open
- `κ ≤ 1/4`: `L = C(log N)^{1−2κ} + O(1)` is not `o(√log N)` unless `C = 0`; identify `C` with the
  Euler-product constant and compute the margin.
- `κ = 1/2` (`β = 0`): only `L ≪ (log N)^ε` is proved.
