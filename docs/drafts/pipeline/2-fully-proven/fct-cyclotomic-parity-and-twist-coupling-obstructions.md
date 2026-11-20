# Cyclotomic Gauss-monomial parity, reflection-Hölder duality gap, planted dispersion saturation, and twist-coupling obstructions

- **ID:** fct-cyclotomic-parity-and-twist-coupling-obstructions
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** `docs/reports/review-1911/todo.md` #12 · `formal/GaloisForLFunctions/FamilyContinuationTheory/`
- **Statement:** For `n > 0` with `6 ∣ n`, `gcd(gcd(n/3, n/2), n) = n / 6`, so cubic and quadratic Gauss sums span unit character index modulo `n` iff `n = 6` (blocking `n = 12`), and among all even `n > 3` and prime cover orders `p₀ ≤ 3` dividing `n`, `gcd(gcd(n/p₀, n/2), n) = 1 ↔ (p₀, n) = (3, 6)`; the $L^{2r}$ Hölder-Poisson dual length `2rU - a` satisfies `2rU - a < a ↔ rU < a` (exceeding `a` by `≥ 2(1 - a)` for all `r ≥ 1, U ≥ 1, a < 1`); planted conjugate characters saturate multilinear character dispersion sums at `(∏_r |S_r|)^2`; and coherent twist averaging obeys `‖∑_{v ∈ V} λ_v‖^2 ≤ |V| ∑_{v ∈ V} ‖λ_v‖^2` while shifting `lx ↦ lx + ν` (`ν ≥ 0, n > 0`) raises `lowBoundaryGenOrder` by at least `ν / (2n)`.

## Goal
Formalize the four structural obstructions governing higher-order cyclotomic covers, $L^{2r}$ Hölder-reflection moments, arbitrary-weight multilinear character dispersion, and coherent twist-averaging couplings in `FamilyContinuationTheory`.

## Gates
- [x] 0 → 1  in-progress: exact interfaces in `FamilyContinuationTheory/TheBudgetInTheTwistExponent.lean` verified
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean module `CyclotomicParityAndTwistCouplingObstructions.lean`, `lake --old env lean` green, standard axioms only

## Paper Proof (`[PROVED HERE]`)

1. **Cyclotomic Gauss-monomial index conservation and uniqueness of `(p₀, n) = (3, 6)`.**
   - Write `n = 6m` (`m ≥ 1`). Then `n / 3 = 2m`, `n / 2 = 3m`, `gcd(2m, 3m) = gcd(2, 3) · m = m`, and `gcd(m, 6m) = m = n / 6`.
   - If `a(n/3) + b(n/2) ≡ 1 (mod n)` with `n = 6m`, then `m ∣ 6m` and `m ∣ 2am + 3bm`, so `m ∣ 1`, forcing `m = 1` (`n = 6`); conversely `(-1)·2 + 1·3 = 1` at `n = 6`. In particular `4a + 6b ≡ 1 (mod 12)` has no integer solution.
   - Let `p₀ ≤ 3` be prime (`p₀ ∈ {2, 3}`), `n > 3` even, and `p₀ ∣ n`. If `p₀ = 2`, `gcd(gcd(n/2, n/2), n) = n / 2 ≥ 2 ≠ 1`. If `p₀ = 3`, then `6 ∣ n` and `gcd = n / 6 = 1 ↔ n = 6`.

2. **$L^{2r}$ Hölder vs. Voronoi/Poisson reflection duality gap.**
   - By linear arithmetic, `2rU - a < a ↔ rU < a`. For `r ≥ 1`, `U ≥ 1`, and `a < 1`, `rU ≥ 1 > a` and `(2rU - a) - a = 2(rU - a) ≥ 2(1 - a) > 0`.

3. **Planted conjugate-character saturation of multilinear character dispersion.**
   - Given finite sets `S_0, …, S_{k-1}`, a finite index set `B` with `u₀ ∈ B`, and unit-modulus factors `‖χ(u₀, r, x)‖ = 1` on `S_r`, define `w(r, x) = \overline{χ(u₀, r, x)}`. Then `‖w(r, x)‖ = 1` and `w(r, x) χ(u₀, r, x) = 1` on `S_r`, so the `u₀`-term of `∑_{u ∈ B} ‖∑_{x ∈ ∏ S_r} ∏_r w(r, x_r) χ(u, r, x_r)‖^2` equals `(∏_r |S_r|)^2`, lower-bounding the full sum over `B` by nonnegativity.

4. **Twist-coupling Cauchy–Schwarz ceiling and low-side `lx`-shift penalty.**
   - By Cauchy–Schwarz (`Finset.sum_mul_sq_le_sq_mul_sq`), `‖∑_{v ∈ V} λ_v‖^2 ≤ (∑_{v ∈ V} ‖λ_v‖)^2 ≤ |V| ∑_{v ∈ V} ‖λ_v‖^2`, and for `Z ≥ 1, 0 ≤ ν ≤ U`, `Z^{ν/2} ≤ Z^{U/2}`.
   - For `n > 0` and `ν ≥ 0`, `max 0 (ly - lx - ν) ≥ max 0 (ly - lx) - ν` and `max 0 (lx + ν + ly + ℓ - 1) ≥ max 0 (lx + ly + ℓ - 1)`, so
     $$\operatorname{lowBoundaryGenOrder}(n, lx + \nu, ly, \ell) - \operatorname{lowBoundaryGenOrder}(n, lx, ly, \ell) \ge \frac{\nu - \nu/2}{n} = \frac{\nu}{2n}.$$

## Log
- 2026-11-20 — complete paper proof recorded in `2-fully-proven`.
