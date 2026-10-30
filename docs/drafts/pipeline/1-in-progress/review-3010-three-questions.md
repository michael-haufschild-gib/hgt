# The three questions of review 3010 (overlap window, Adams producer, flip resolution)

- **ID:** R3010-Q123
- **Stage:** 1-in-progress
- **Type:** CONJECTURE (loop)
- **Source:** ../../../reports/review-3010/obstacles-summary.md §2.3
- **Statement:** Answer Q1 (location of the RH transition in the overlap window), Q2 (Adams operations as a Stepanov producer), Q3 (overlap needed to resolve a gauge point from `0`), with Lean proofs.

## Goal
Full answers with unconditional Lean theorems. Estimates, criteria and no-gos are not answers.

## Gates
- [x] 0 → 1  in-progress
- [ ] 1 → 2  fully-proven
- [ ] 2 → 3  formalized

## Approach

### Q3 — exact resolution law (answered for every twist at finite square-root distance)
Objects: `W(c,N)` complete Weil matrix of a profile `φ` without real Fourier zeros at width
`c/N`; a real twist `λ` of `Λ` with defect `d_λ(k) = (Λ(k) − λ(k))/√k`, `D(λ) = Σ_k |d_λ(k)| < ∞`;
normalized Ramanujan modes `e_m`; packets `y = Σ_{m∈T} β_m e_m`.

Theorem (Lean, `RenormalizedArithmeticPotentialTheory`):
1. Packet limit: the twisted complete form of the packet tends to
   `E_λ(c;T,β) = Σ_m β_m² E_m(c) + 2 Σ_k d_λ(k) k^{-1/2} M(y·y(k·))`
   (`tendsto_twisted_packet`; twist part `tendsto_twistedGap_packet`, independent of `c`).
2. Dichotomy at fixed `c`: `λ_λ(c) = inf_{Σβ²=1} E_λ(c;T,β)`; `λ_λ(c) > 0` ⇒ the twisted complete
   matrix is eventually positive definite; `λ_λ(c) < 0` ⇒ eventually negative on an atomic test
   (`eventually_posDef_of_resolutionBottom_pos`, `exists_eventually_neg_of_resolutionBottom_neg`).
   Mechanism: reserve + finite Ramanujan approximation give `W ≥ T` off a finite packet span
   (`exists_finite_orthogonal_gap`), then a 2×2 Schur estimate (`posDef_add_of_packets`).
3. `λ_λ` is antitone in `c`, and strictly negative past its first nonpositive value
   (`resolutionBottom_neg_of_lt`; uses strict decrease of each `E_m` and finiteness of conductor
   sublevels).
4. Exact threshold `c_0(λ) = sup{c : λ_λ(c) > 0}`: if `λ` is seen at some overlap, then
   `0 < c_0(λ) < ∞`, positive definite below, negative above (`resolutionThreshold_spec`).
5. Flips: `D(ω_p) ≤ 4 log p/√p`, flip energy `4 log p Σ_j p^{-(2j+1)} M(y·y(p^{2j+1}·))`, every
   flip seen, `c_0(ω_p)` exact and `→ ∞` (`primeFlip_resolutionThreshold_spec`,
   `le_primeFlip_resolutionThreshold`); finite flip sets via the product trial `Π_{p∈S} F_p`
   (`finiteFlip_resolutionThreshold_spec`).
6. Resolution–distance law: `E(c) ≤ 2D(λ)` for every `c > c_0(λ)`
   (`completedShellEnergy_le_distance_of_resolutionThreshold_lt`); tilted spline:
   `C₀ √p ≤ 8 log p · max(c,1)^7` above `c_0(ω_p)`.

Not covered: twists at infinite distance (twin tails, the Liouville point, vertical shifts); for
them the twist is not a bounded perturbation of the packet operator.

### Q1 — structural notes
- Low zeros (`|γ| ≲ N/c`) enter Ramanujan modes only through the boundary term `N^ρ/ρ` of the
  partial sums of `Σ c_m(n) n^{-s}`: contribution `β_1² · c·Σ_ρ 1/(ρ(1−ρ)) / log N`, the same with or
  without RH. Fixed-`c` positivity is RH-blind for this reason.
- The margin `E(c)` is the dual-sum (approximate functional equation) energy of zeros at height
  `≳ 2πN/c`.
- Off-line zeros can only be seen by synthesized wide tests; their energy is `c·(Q(h)/‖h‖² + κ log N ε_φ(c)²)`
  with `ε_φ` the synthesis (aliasing) error. Expected transition: `log N · ε_φ(c)² ≍ 1`, not
  `E(c) log N ≍ 1`.

### Q2 — open

## Log
- 2026-10-30 — created; Q3 law derived on paper and formalized (five modules in
  `RenormalizedArithmeticPotentialTheory`, see Q3).
