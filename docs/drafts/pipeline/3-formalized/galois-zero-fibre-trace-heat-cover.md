# The trace of a fibre of the heat cover

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Questions:** review-1211 §2.19 Q5 (the sign part of the monodromy; single-valued
  invariants of the cover); link of tier 3 to the coefficient fields of tier 1.

`H_τ(z) = ∫ Φ(x) e^{τx²} e^{izx} dx`, `c(τ) = H_τ(0)`.

## Theorems

1. `H_τ(z) = Σ_k (−1)^k c^{(k)}(τ) z^{2k}/(2k)!` for all complex `τ`, `z`.
2. For every `τ` there is `C` with `|H_τ(z)| ≤ exp(C(1+|z|)log(2+|z|))` for all `z`.
3. For an even entire `f` with `f(0) ≠ 0` and the bound of 2, the zeros `a_q` with
   multiplicity satisfy `Σ_q a_q^{−2} = −f''(0)/f(0)`.
4. If `c(τ) ≠ 0` then `Σ_q z_q^{−2} = c'(τ)/c(τ)`, the sum over the zeros of `H_τ` with
   multiplicity.
5. If `g` is analytic at `τ₀` with a zero of order `k`, then `(τ − τ₀) g'(τ)/g(τ) → k`.
6. At a centre time `τ₀` where `2k` zeros collide at the centre,
   `(τ − τ₀) Σ_q z_q(τ)^{−2} → k` as `τ → τ₀`.

## Proof

1. Taylor series of the entire function `H_τ` at `0`. The odd derivatives vanish (`H_τ` is
   even) and `H_τ^{(2k)}(0) = (−1)^k c^{(k)}(τ)` by the heat equation.
2. `Φ(x) ≤ A exp(−B e^{b|x|} + c x²)`. With `T = c + |τ|` and `κ = B b⁴/48`:
   `T x² ≤ κ x⁴ + T²/(4κ) ≤ (B/2) e^{b|x|} + T²/(4κ)`, so
   `|Φ(x) e^{τx²}| ≤ M e^{−(B/2) e^{b|x|}}`. For `y, u ≥ 0`:
   `y u ≤ (B/4) e^{bu} + M₁ (1+y) log(2+y)` (if `bu/2 ≤ log(E₀(2+y))` bound `u`; otherwise
   `e^{bu} ≥ E₀ (2+y) · bu/2`). With `y = |Im z|` the integrand is at most
   `M e^{M₁(1+|z|)log(2+|z|)} e^{−(B/4)e^{b|x|}}`, and the last factor is below a Gaussian.
3. `f'/f(z) = Σ_q −z/(a_q(a_q − z))` off the zeros (corpus, genus-one product). Divide by
   `z`. As `z → 0` the left side tends to `f''(0)/f(0)` because `f'(0) = 0`; the right side
   tends to `−Σ a_q^{−2}` by dominated convergence, with `|a_q(a_q − z)|^{−1} ≤ 2|a_q|^{−2}`
   for `|z|` below half the distance from `0` to the zeros.
4. 2 and 3 for `f = H_τ`, and `H_τ''(0) = −c'(τ)`.
5. `g = (τ − τ₀)^k φ` with `φ(τ₀) ≠ 0`; `(τ − τ₀) g'/g = k + (τ − τ₀) φ'/φ`.
6. A collision of order `2k` at the centre is a zero of order `k` of `c`; `c ≠ 0` near `τ₀`
   off `τ₀`; apply 4 and 5.

## Formalization

`GaloisTheoryOfZeros/TheTraceOfAFibreOfTheHeatCover.lean`: `hasSum_complexHeat_jets`,
`exists_norm_complexWeight_le`, `exists_norm_complexHeat_le`,
`hasSum_inv_sq_zeroCopyPoint_of_even`, `hasSum_inv_sq_zeros_complexHeat`,
`tendsto_sub_mul_logDeriv`, `tendsto_sub_mul_tsum_inv_sq_zeros`. Input:
`RHTower.logDeriv_eq_tsum_of_even`.

Checked with `lake --old env lean`; umbrella import wired.
