# Cross-programme contributions to the eighteen research programmes

- **ID:** cross-programme-250-2026-10-25
- **Stage:** 1-in-progress
- **Type:** RESEARCH PROGRAMME
- **Source:** user `/goal` of 2026-10-25 (eighteen programme READMEs, frontier map).
- **Statement:** 250 significant unconditional Lean contributions: answers to programme open
  questions, missing tools, cross-programme theorems, or frontier arithmetic problems.

## Gates
- [x] 0 → 1  frontier map and READMEs surveyed; counting rule fixed (log: `logs/cross-programme-250-2026-10-25.md`)
- [ ] per contribution: paper proof → Lean (`lake --old env lean`, clean axioms) → umbrella wiring

## Active conjecture

C1 (SSA §7.5): the lag-two floor is exactly `1/4`; every odd shift has floor exactly `1/3`,
attained by the conductor-two twin `(−1)^{v₂(n)}`.
Proof: three signs `f(n), f(n+1), f(n+2)` have at least one agreeing pair, so odd positions pay
`1 − a(n) − a(n+1)`; even positions give `L₁/2`; the two lower bounds sum to `H/2`.

C2 (SSA §7.4): every zero-defect sign has `f(2) = −1` (the `f(2) = 1` branch dies at `n = 25`);
`(−1)^{v₂(n)}` is a zero-defect sign that is not a conductor-three twin.
Open conjecture C2′: the zero-defect signs are exactly `(−1)^{v₂}` and the two conductor-three
twins (verified numerically: only these three patterns on primes `≤ 13` extend to `n ≤ 400`).

C3 (BVI §7.7, THIM §7.3): closed form of the cofinal Möbius slope
`κ = ρ Σ_j S(j) log(1+1/j)`:

    κ = (ρ/2π) ∫_ℝ H(t) / |t ζ(1+it)|² dt,   H(t) = Σ_δ μ(δ) w(δ)² |B_δ(it)|²
      = (ρ/2π) ∫_ℝ |B(it)|² ∏_p (1 − |p+1−p^{−it}|^{−2}) dt / |t ζ(1+it)|²,

`w = μ/σ`, `B_δ(s) = Σ_n b_δ(n) n^{−s}`, `b_δ(n) = n^{−1} ∏_{p|n, p∤δ} (p+1)^{−1}` (absolutely
convergent on `Re s ≥ 0`), `B = B_1`. Numerically `≈ 0.4408` (corpus value `0.4407`).
Paper proof: (1) `S(⌊e^u⌋) = Σ_δ μ(δ)w(δ)² g_δ(u − log δ)²`, `g_δ(v) = T_δ(⌊e^v⌋)` (coprimality
sieve); integrate and translate: `κ = ρ Σ_δ μ(δ)w(δ)² ‖g_δ‖₂²`, absolutely by
`|T_δ(Y)| ≤ Cδ^{1/4}(1+log Y)^{−2}`. (2) `∫ g_δ e^{−sv} = L(c_δ,s)/s` (`Re s > 0`,
`c_δ = 1_{(·,δ)=1} w`); `L(c_δ,s) ζ(1+s) = B_δ(s)`; dominated convergence at `σ ↓ 0` and
`ζ(1+it) ≠ 0` give `ĝ_δ(t) = B_δ(it)/(it ζ(1+it))`; Plancherel. (3) swap `Σ_δ`, `∫`.
(4) `B_δ = B/∏_{p|δ}(1 − p^{−s}/(p+1))`, Euler product in `δ`.

## Log
- 2026-10-25 — created; C1, C2 paper proofs complete.
- 2026-10-25 — C1 formalized (#1). C2 formalized (not counted). C3 formalized (#2).
