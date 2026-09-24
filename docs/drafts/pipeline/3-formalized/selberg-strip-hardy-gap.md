# Selberg strip gap with vertical Hardy energy

- **ID:** SELBERG-STRIP-HARDY
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Lean corpus `SelbergMaassStripGap.level_scaled_eigenvalue_bound` (λ ≥ 3π²/(2w²), w = N+1), 2026-09-24.
- **Statement:** For every nonzero Maass cusp eigenform on Γ(w) with eigenvalue λ, and α = π√3/w, one has 2λ ≥ α(1+α). In particular no exceptional eigenvalue exists for Γ(w), w ≤ 14.

## Goal
The corpus strip argument uses only horizontal (Wirtinger) energy and gives order 1/w². Retaining the
vertical energy through a ground-state (Hardy) inequality in the height variable changes the order to 1/w.

## Paper proof
Notation: κ = 2π/w, Y₀ = √3/2 (strip floor), α = κY₀, h(y) = α/y − κ (so h(Y₀) = 0, h ≤ 0 on [Y₀,∞)).
For each deck component g and height y > 0 let M, J, H, V be the period-normalized slice mass,
flux Re⟨∂_y g, g⟩, horizontal energy ‖∂_x g‖² and vertical energy ‖∂_y g‖². M' = 2J (corpus).

1. Horizontal: zero constant term (corpus, sub-quarter) and Parseval give H ≥ κ²M.
2. Vertical: 0 ≤ ‖∂_y g − h g‖² = V − 2hJ + h²M, so V ≥ hM' − h²M.
3. Sum over the deck, S = ΣM (unit-strip trace mass), G = Σ(H+V) (unit-strip gradient):
   G ≥ (κ² − h²)S + hS' = (hS)' + W S, with W = κ² − h² − h' = α(1−α)/y² + 2ακ/y.
   For y ≥ Y₀, y²W ≥ α(1−α) + 2ακY₀ = α(1+α).
4. Integrate on [Y₀,R]: h(R)S(R) ≤ ∫(G − WS), so α(1+α)∫_{Y₀}^R S/y² ≤ ∫G + κS(R).
   Cusp decay S(R) → 0; R → ∞ gives α(1+α)·M_strip ≤ E_strip.
5. Corpus comparison: M_cell ≤ M_strip, E_strip ≤ 2E_cell = 2λM_cell, M_cell > 0. Hence α(1+α) ≤ 2λ.
6. w ≤ 14: α ≥ π√3/14 > 0.3884, α(1+α) > 0.539 > 1/2, so λ > 1/4 · 1.07 — contradiction with λ < 1/4.

## Literature position
Roelcke's horizontal argument (λ₁(SL₂ℤ) > 3π²/2) and Huxley's small-level verification (N < 19, 1985)
precede this. The consequence for levels ≤ 14 is therefore not new. The mechanism (ground-state Hardy
energy giving order 1/w rather than 1/w² for the cusp-width bound) was not found in the literature
screened; novelty is unconfirmed.

## Log
- 2026-09-24 — created; paper proof complete; Lean module `SelbergMaassStripHardyGap` started.
- 2026-09-24 — Lean closed: `formal/GaloisForLFunctions/RHTower/SelbergMaassStripHardyGap.lean`.
  `hardy_eigenvalue_bound` (α(1+α) ≤ 2λ, α = (2π/(N+1))·√3/2) and
  `level_le_fourteen_no_exceptional` (no exceptional Maass cusp form on Γ(n), n ≤ 14; the corpus previously
  reached 7). `lake build ... --old` green; `#print axioms`: propext, Classical.choice, Quot.sound.
  Wired into `RHTower.lean` after `SelbergMaassStripGap`. Global lint fails only on another agent's
  in-progress module (`ThetaCuspHawkingBMPWCrossClockActualError`).
- Numerical note: only π > 3 is used; the bound α ≥ 0.37 gives α(1+α) > 0.507 > 1/2.
- 2026-09-24 — Cycle 2, Lean closed: `formal/GaloisForLFunctions/RHTower/SelbergMaassModalHardyLaw.lean`.
  `modal_hardy` (per Fourier mode n of each deck component: t_n(1+t_n)·M_{q,n} ≤ E_{q,n}, with
  t_n = (2π|n|/(N+1))·√3/2), `modal_hardy_law` (Σ t_n(1+t_n)M ≤ 2λ ΣM), `strip_mass_eq_modal` (Tonelli),
  and `low_mode_dominance`: an exceptional form has Σ (t_n(1+t_n) − 1/2)·M_{q,n} < 0, so its strip mass
  sits mostly in modes |n| ≲ 0.0673(N+1). Build green; axioms propext/choice/Quot.sound.

## No-go closure: strip-energy methods at large level (paper, 2026-09-24)
- **Killing mechanism.** Take a Γ₀(p) newform, p prime; at cusp 0 (width p) the deck modes carry the
  coefficients λ(n) at frequency n/p. With exact modes c_n = ρ(n)√y K_ν(2πny/p), the mode strip mass is
  |ρ(n)|²·B_ν(n/p), B_ν(x) = ∫_{√3/2}^∞ K_ν(2πxy)² dy/y. If the coefficients obey the Rankin–Selberg mean
  (|λ(n)|² ≈ 1 on average at scale p), then Σ_n (w(n/p) − 2λ)M_n ≈ p·c·Φ_ν with
  Φ_ν = ∫_0^∞ (w(x) − 2λ)B_ν(x)dx = (1/(2π·√3/2))·(A₁/2 + A₂/3 − 2λA₀), A_k = ∫_0^∞ u^k K_ν(u)² du:
  A₀ = π²/(4 cos πν), A₁ = πν/(2 sin πν), A₂ = π²λ/(8 cos πν). Hence
  A₁/2 + A₂/3 − 2λA₀ = πν/(4 sin πν) − (11/24)π²λ/cos πν < 0 on all of 0 ≤ ν < 1/2 (−0.88 at ν = 0).
  Without the strip/cell factor 2: A₁/2 + A₂/3 − λA₀ = −0.26 at ν = 0, still negative. The width-1 cusp
  contributes O(|ρ(1)|²), which is p times smaller. So the modal Hardy law is satisfied by the expected
  coefficient distribution at every exceptional λ. No arithmetic input about coefficient distribution can
  turn strip-energy balances (Hardy or exact Bessel, which is an identity) into an exclusion at large level.
- **Strongest positive survivor.** The unconditional Lean theorems above: λ ≥ α(1+α)/2 with α = π√3/(N+1)
  (order 1/N, Selberg for levels ≤ 14), and exact low-mode dominance. They are sharp for the method: the only
  slack is at small level, where the discreteness of n/p and the width-1 cusps matter.
- **New insight.** The corpus's cusp-energy programme (conjecturing-loop cycles 1–55 and this card) is
  structurally capped at bounded level. A uniform exclusion must use an identity that sees arithmetic
  beyond the second moment of the coefficients: a trace formula (Kloosterman/Kuznetsov or Selberg), or
  L-function nonvanishing at forced zeros.
- **Status.** Paper computation of the Bessel moments (standard Mellin formula for ∫ u^{μ−1}K_ν(u)² du).
  No Lean formalization: mathlib has no Macdonald functions. Not a proof about actual forms, only about
  what the method can certify.
