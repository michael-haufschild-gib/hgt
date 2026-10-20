# THIM WP5 loop: the parity pair (goal: 100 significant contributions)

- **ID:** thim-wp5-parity-1020
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) per contribution; CONJECTURE for open items
- **Source:** docs/reports/work-packages.md §WP5; THIM README §5 research topic 1 (mechanism 5)
- **Statement:** Construct two weights with identical divisor-sum, Ramanujan and pronic Gram data and
  opposite trans-horizon energy growth, or prove no such pair exists and name the additive observable
  that separates them.

## Contract (from WP5)
A contribution counts when it (1) constructs a pair with both proofs, or (2) proves impossibility with
the separating observable and its exact loss, or (3) bounds the complete signed trans-horizon energy at
one fixed `ε < 1/2` with all terms retained, or (4) bounds the odd-sector low-prime diagonal potential
independently and moves the aperture unit in WP1/WP3; AND (5) names the step `k ↦ k+1`, `N ↦ N+1` or
`k ↦ pk` where the arithmetic of `ℕ` enters. Not counted: small-horizon thresholds, Buchstab band signs,
second-order crossover terms, schedule classifications.

## Precise data notions used
For a weight `c` with absolutely convergent Ramanujan coefficients `w_c(e) = Σ_{e|d} c(d)/d`:
- **Ramanujan data:** the amplitude spectrum `|w_c(e)|`.
- **Divisor-sum data:** the complete-period (Haar) translation statistics of the divisor-sum signal
  `c * 1`: mean `w_c(1)` and lag covariances `Σ_e c_e(h) w_c(e)²` at every additive lag `h`.
- **Pronic Gram data:** the pronic Gram kernel `𝒢(e₁,e₂)` with the weighted entries
  `|w(e₁) w(e₂) 𝒢(e₁,e₂)|`, in particular every mode mass `w(e)² 𝒢(e,e)`.
These are exactly the data invariant under the **parity involution** `w ↦ λ·w` on moduli (for
squarefree support `λ(e) = μ(e)`): translation statistics are diagonal in the Selberg coordinates, so
they see `w(e)²` only. Signed Ramanujan coefficients pin an admissible weight (Möbius inversion over
multiples), so with signed data no pair exists trivially; the parity is the real content.
- **Trans-horizon energy:** the pronic receiver energy `E_T(c) = Σ_{n≤T} A_c(n)²/(n(n+1))`,
  `A_c(n) = Σ_{j≤n} ((c*1)(j) − w_c(1))` (equivalent up to `×2 + 1/2` to the interior energy).

## Conjecture queue
1. Parity twin `c'_ε` of `c_ε = μ(d)d^{-ε}`: Ramanujan coefficients `|w_ε(e)|`, nonnegative row,
   `c'_ε(d) ≥ κ_ε μ²(d) d^{-ε}`; `E_T(c'_ε) → ∞` for `ε ≤ 1/2`; with the corpus bound
   `exists_pmPowerDampedDivisorDiscreteEnergy_budget_of_half_le` this is the pair at `ε = 1/2`.
2. Exact loss: `E(λw) − E(w) = 4 X` with `X` the cross-parity pronic pairing; at `ε < 1/2` the receiver
   bound ⇔ `X_T = E⁺_T/2 + O(1)` against `E⁺_T ≍ T^{1−2ε}`.
3. Separating observable for the twin: dilation correlations `k ↦ pk` (edges `e | pe` flip sign).
4. Horizon-escape pair: sharp Möbius rows vs smooth rows with the same pointwise limits.

## Contribution ledger (append-only)

## Log
- 2026-10-20 — card created; README §5 and WP5 read; corpus searched (no parity-pair work; BVI
  `pmPronicVaughan_flip_energy_gap` is the generic polarization algebra only).
