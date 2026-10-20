# WP4: single-modulus bilinear dispersion on the pronic Gram

- **ID:** bvi-wp4-single-modulus-dispersion-2026-10-20
- **Stage:** 1-in-progress
- **Type:** CANDIDATE (contribution loop, goal 100)
- **Source:** `docs/reports/work-packages.md` WP4; BVI README §5 research topic 1
- **Statement:** bound `Σ_{p∼P} Σ_{q∼Q} a_p b_q 𝒢^{ec}(p,q)` at one modulus with exponent `θ > 1`,
  or prove which input classes cannot, with the replacement hypothesis.

## Units used by this card

- Window `M ∼ X` of the pronic measure; moduli `∼ P`. Exponent `θ = 2 log P / log X`.
  Large sieve is diagonal-quality at `X ≥ P²` (θ ≤ 1); the pronic mass of the prime block
  sits at `X ∼ P` (θ = 2, the receiver).
- Diagonal scale of a prime packet: `D(a) = Σ_p p a_p²` (`𝒢^{ec}(p,p) ≍ p`).
- Trivial (Cauchy–Schwarz) loss: `|S|`, the number of moduli.

## Significance criteria (WP4)

1. θ > 1 for a stated coefficient class. 2. Interior rate > 7/24 with all terms.
3. Type-II input at one modulus with exact loss. 4. No-go for a named class + replacement.
Not significant: reciprocity error, window constants, horizons, large-sieve factor two, ε ≥ 1/2.

## Ledger of contributions

(count = number of entries marked DONE; Lean module named on each)

- **C1 DONE (criterion 4).** `BVI/BrownianBridgeLawOfThePrimeBlockAndCodimensionNoGo`.
  First-jump window: `V(n) = L − nA + C(n)`, `C(n)=Σ_{p≤n}a_p p`, for `n < 2 min S`; for `S⊆(P,2P]`,
  `A=L=0`: window energy `= Σ a_p a_q (min(p,q) − pq/(2P+2))` (Brownian bridge) `≤ 𝒢^{ec}`-form.
  No-go: any `J` linear side conditions admit `a≠0`, `A=L=0`, with
  `Q^{ec}(a) ≥ (k²−1)/(24(2P+1)) Σ p a_p²`, `(J+3)k ≤ |S|`. Named class: Type-II ℓ² inputs with
  `J` side conditions; loss `≳ |S|/((J+3)² log P)` vs trivial `≲ 3|S|`. Replacement: square-root
  size of the summatory jump function `C` on the block (θ = 2 window).
- **C2 DONE (criterion 4).** `BVI/CoherentPrimeBlocksAndTheTypeIIWindowNoGo`.
  `k` primes in `[p₀,p₀+ℓ]`, unit jumps: on clean regions `j(p₀+ℓ) ≤ n < (j+1)p₀` the packet is
  exactly affine `L + kj − ns`; on `[J₀p₀, 2J₀p₀)`, `4J₀ℓ ≤ p₀`: window energy `≥ (k/2304)·k Σ_W w`
  (window diagonal bound). Pigeonhole: every `S⊆(P,2P]` has such a block with
  `k ≥ |S|/((P−1)/(ℓ+1)+1)`. Large-sieve loss `P²/X` attained at every window below `P²`:
  no Type-II input reaches any θ > 1. Replacement: square-root cancellation of the jump measure
  `Σ_{p∈I} a_p p` on intervals of length `P²/X`.

## Queue

- C1 first-jump window: Brownian-bridge law and codimension no-go.
- Hyperbola (summatory) form of the truncated pronic Gram: dilated min kernels.
- Type-II exact loss: trivial `|S|` vs block lower bound; Type-I ⟺ short-interval PNT.
- Bézout ray reduction of window covariances; Chowla-type replacement hypothesis.

## Log
- 2026-10-20 — created
