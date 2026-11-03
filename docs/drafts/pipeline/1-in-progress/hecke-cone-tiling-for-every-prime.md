# The Hecke cones of determinant n tile the quadrant

- **ID:** R0311-25-2b
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper)
- **Source:** review-0311 §2.5.2 (source Hecke operators for every prime; A15)
- **Statement:** For `n ≥ 1`, `X_n = {[[a,b],[c,d]] ∈ M₂(ℕ) : ad − bc = n, a > c, d > b}` and
  `v = (x, y) ∈ ℕ²`, `x ≥ 1`:
  `#{(M, m, k) : M ∈ X_n, m ≥ 1, k ≥ 0, v = m(a,b) + k(c,d)} = Σ_{e | gcd(n,x,y)} e`.
  For a prime `p`: `1 + p·[p | x ∧ p | y]`. Consequently the Barnes boundary periods satisfy
  `Σ_{M ∈ X_p} P_w(aα+bγ, aβ+bδ) = P_w(a, b) + p P_w(pa, pb)` and the source Hecke operator
  `T_{p,s}f(a) = Σ_{M∈X_p} (γa+δ)^{−2s} f((αa+β)/(γa+δ))` has eigenvalue `1 + p^{1−2s}` on the
  Barnes period (absolute chamber `Re 2s > 2`).

## Proof

Write `u₁ = (a,b)`, `u₂ = (c,d)`; an `X_n`-basis of the lattice `L = ℤu₁ + ℤu₂` (index `n`). The cone of
`(u₁,u₂)` is `{m u₁ + k u₂ : m ≥ 1, k ≥ 0}`.

1. **Uniqueness.** Let `(u₁,u₂)`, `(u₁',u₂')` be `X_n`-bases of the same `L`, `u₁' = αu₁ + βu₂`,
   `u₂' = γu₁ + δu₂`, `αδ − βγ = 1`, and `v` in both cones: `m = m'α + k'γ ≥ 1`, `k = m'β + k'δ ≥ 0`,
   `m' = δm − γk ≥ 1`, `k' = αk − βm ≥ 0`. With `P = α − γ`, `R = β − δ` the conditions `c' < a'`,
   `d' > b'` read `Pa + Rc > 0`, `Pb + Rd < 0`; with `a > c ≥ 0`, `d > b ≥ 0` this forces `P ≥ 1`,
   `R ≤ −1`. The inverse change of basis gives `γ + δ ≥ 1`, `α + β ≥ 1`. Case analysis on the signs of
   `β, γ` (using `αδ − βγ = 1`, `k' ≥ 0`, `k ≥ 0`) leaves only `α = δ = 1`, `β = γ = 0`.
2. **Existence (the chain).** Start with `u₁ = (n', 0)` (generator of `L` on the axis) and the Hermite
   vector `u₂ = (j, g)`, `0 ≤ j < n'`, `n'g = n`: an `X_n`-basis. While `c ≥ 1`, the successor
   `(u₂, t u₂ − u₁)`, `t = ⌈a/c⌉ ≥ 2`, is an `X_n`-basis of `L` (`0 ≤ tc − a < c`, `(t−1)d > b`); `c`
   strictly decreases. Writing `v = m u₁ + k u₂` (`k ≥ 0` at the start), if `m ≤ 0` pass to the
   successor: `v = (mt + k)u₂ + (−m)(tu₂ − u₁)`, keeping the second coefficient `≥ 0`; at the last basis
   `u₂ = (0, d)` and `m = x/a ≥ 1`.
3. **Count.** Hence each index-`n` sublattice containing `v` carries exactly one `X_n`-cone through
   `v`, and the number of such sublattices is `Σ_{e | gcd(n,v)} e` (`p + 1` lines of `𝔽_p²` for prime
   `n = p`; one through `v ≢ 0`).

Numerics (scratch `tiling.py`, `tiling5.py`): verified for `n ≤ 12`, `x, y < 30`.

## Gates
- [x] 0 → 1  statement and proof sketch
- [ ] 1 → 2  complete paper proof
- [ ] 2 → 3  Lean
