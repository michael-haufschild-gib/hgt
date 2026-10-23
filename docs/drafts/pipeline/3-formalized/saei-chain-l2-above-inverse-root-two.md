# The centred damping chain is Hilbert–Schmidt above damping 1/√2

- **ID:** saei-chain-l2-root-two
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** SAEI README §9 topic 4 (the centred chain on `ℓ²`)
- **Statement:** For `η > 1/√2` the centred damping chain `C_η` (state `n+1` at index `n`) has
  `Σ_{n,k} C(n,k)² < ∞`; hence `Σ_{n<T} (C_η b)(n)² ≤ M_η Σ b_k²` on finitely supported `b`.

## Goal
Lower the unconditional `ℓ²` range of the chain from `η > 1` (`centeredOperator_l2_le`, size of a
bounded source) to `η > 1/√2`, using only the sign-blind bound `|P_η(q)| ≤ C q^{1−η}` and the
trivial short-interval bound `|Σ_{I}(c − ρ)| ≤ |I|`. Below `1/√2` the obstruction is exactly the
short-interval discrepancy of `c_η(m) = Σ_{d|m} μ(d) d^{−η}` on intervals of length `N/K²` at height
`N/K`. Source-pure: only the literal coefficients; no zeros.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea
- [x] 1 → 2  fully-proven: complete paper proof below, `[PROVED HERE]`
- [x] 2 → 3  formalized: `centeredOperator_l2_le_of_inverseRootTwo` in
  `SignedArithmeticEnergyIncidence/TheChainIsHilbertSchmidtAboveInverseRootTwo.lean` (with
  `FloorJumpsAboveTheSquareRootAreSparse`), checked with `lake --old env lean`
- [ ] 3 → 4  n/a

## Approach — paper proof [PROVED HERE]
Notation: `N = n+1`, `K = k+1`, `q_K = ⌊N/K⌋`, `s_K = q_K − N/K ∈ (−1,0]`, `J = q_K − q_{K+1} ≥ 0`,
`A(q) = Σ_{m≤q} c(m)` with `0 ≤ c ≤ 1`, `ρ = 1/ζ(1+η) ∈ (0,1)`, `P(q) = A(q) − ρq`, `0 < η < 1`.

1. **Kernel identity** (as in `abs_centeredRow_le`):
   `C = (K/N)[(K^{−η} − (K+1)^{−η})(P(q_K) + ρ s_K) + (K+1)^{−η}((P(q_K) − P(q_{K+1})) + ρ(s_K − s_{K+1}))]`.
2. **Bounds.** `|P(q)| ≤ C₁ q^{1−η}` (floor form: head `≤ Σ_{d≤q} d^{−η} ≤ q^{1−η}/(1−η)`, tail
   `q Σ_{d>q} d^{−1−η} ≤ q^{1−η}/η`); `0 ≤ K^{−η} − (K+1)^{−η} ≤ η K^{−1−η}`;
   `|P(q_K) − P(q_{K+1})| ≤ min(J, 2C₁ q_K^{1−η})`; `|s_K − s_{K+1}| = |J − N/(K(K+1))| < 1`.
   Hence `|C| ≤ T1 + T2 + T3 + T4` with
   `T1 = ηC₁ N^{−η} K^{−1}`, `T2 = ηρ K^{−η}/N`, `T3 = (K^{1−η}/N) min(J, 2C₁ q_K^{1−η})`,
   `T4 = ρ (K^{1−η}/N) |J − N/(K(K+1))|`.
3. **Sums.** `Σ T1² ≤ η²C₁² ζ(2η) ζ(2)` and `Σ T2² ≤ η²ρ² ζ(2) ζ(2η)`, finite for `η > ½`.
   Region `K² ≤ N`: `T4 ≤ ρK^{1−η}/N`, and `Σ_{K ≤ √N} K^{2−2η} ≤ N^{(3−2η)/2}`, so
   `Σ_N N^{−(1+2η)/2} < ∞`. For `T3` there `J ≤ 2N/K²` and `q_K ≤ N/K`; with
   `min(x,y) ≤ x^λ y^{1−λ}`, `T3 ≲ N^{−η(1−λ)} K^{−λ(1+η)}`, square-summable when
   `2λ(1+η) > 1` and `2η(1−λ) > 1`; such `λ` exists iff `1/(2(1+η)) + 1/(2η) < 1` iff `η² > ½`.
   Region `K² > N`: `J ≤ 1`, and `J = 1` determines `K` from `m = q_K` (`K` is the largest index
   with `⌊N/K⌋ = m`, and `m < √N`); so `Σ_{K²>N, J=1} K^{2−2η} ≤ N^{2−2η} Σ_{m<√N} m^{2η−2} ≲
   N^{(3−2η)/2}`, giving `Σ_N N^{−(1+2η)/2} < ∞`; the part `N/(K(K+1)) ≤ N/K²` of `T4` gives
   `Σ_K K^{−2−2η} #{N < K²} ≤ ζ(2η)`.
4. **Operator bound.** Cauchy–Schwarz on each row of a finitely supported `b`, as in
   `centeredOperator_l2_le`.

The only place where `η > 1/√2` enters is `T3` on `K² ≤ N`: the short-interval sums of `c − ρ`.

## Log
- 2026-10-23 — created in 1-in-progress with the paper proof.
- 2026-10-23 — formalized; moved to 3-formalized.
