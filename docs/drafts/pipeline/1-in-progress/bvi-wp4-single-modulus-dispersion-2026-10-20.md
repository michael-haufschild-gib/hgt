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

## Queue

- C1 first-jump window: Brownian-bridge law and codimension no-go.
- Hyperbola (summatory) form of the truncated pronic Gram: dilated min kernels.
- Type-II exact loss: trivial `|S|` vs block lower bound; Type-I ⟺ short-interval PNT.
- Bézout ray reduction of window covariances; Chowla-type replacement hypothesis.

## Log
- 2026-10-20 — created
