# The Window Tower of Spec ℤ (WTZ) — programme card

- **ID:** WTZ
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) programme
- **Source:** docs/reports/review-0211/obstacles-summary.md §2.7 (theory of the window tower)
- **Statement:** develop the tower `A ↦ W_A`: window algebra, transitions and control, Tate pieces
  vs Weil's form, lattice, growth, symmetries, selection.

## Goal
Answer the §2.7 questions by Lean theorems; build the tools. Folder
`formal/GaloisForLFunctions/WindowTowerOfSpecZ/`, umbrella `WindowTowerOfSpecZ.lean`, README there.
CWS (`CohomologyOfWindowsOfSpecZ`) is owned by another agent: import, never edit.

## Lean modules [L]
TheWindowDirichletAlgebra, TheTowerOfSmallExtensions, TheWindowFormIsTheDerivativeOfTheJordanCounts,
TheTateFlowOnTheWindowAlgebra, TheAtomicLatticeOfAWindow, TheExactPoleCapacityOfAWindow,
TheSymmetriesOfTheTower, TheTwistsOfTheTower, WeilsWindowFormIsASignedCount,
TheTransferAcrossAStage, TheExitChargePaysEveryNewFold, TheEulerFactorizationOfAWindow,
TheEndProfileOfAWindow, ShortWindowsArePaidByTheirExitCharge, TheArakelovBundleOfAWindow.

## Status
- Window algebra = Dirichlet ring truncated at `⌊e^A⌋` (`ker_windowRep`); nesting; `ZMZ⁻¹ = M − ρ(Λ)`;
  `Q = Ω‖H‖² + J − 2⟨ρ(Λ)H,H⟩ + pole`.
- Control: small extensions, socle law, sharp Loewy length, cotangent = primes, inverse limit.
- Tate: `J_0 = 1`, `∂J|₀ = Λ`, `J_{β+1} = φ#ℙ^β`, `Q = Ωτ(0) − 2τ′(0) + J + pole`; first prime coefficient
  `#ℙ^{k−1}(𝔽₂)`; cocycle, commutator form, Hensel tower; flips fail and `ζ(s)ζ(s−ε)` passes Tate positivity.
- Atomic lattice = regular representation; arithmetic = multiplication by `Λ`; pole = values at `s=0,1`.
- Exact pole capacity `2sinh(A/2) − A`; sharp floor `≤ −Ω(0) + (4A+1)e^{A/2}`.
- Adams lifts = dilations up to Tate twist `(e−1)/2`; Serre duality = Rosati involution.
- Character twists carry Tate families: `L(s,χ)` has Tate pieces `χφ#ℙ^β`, non-Tate piece `χΛ`; near
  dimension zero Tate positivity at primes ⇔ weight sign (Markov, soft).
- Signed count: `Λ(n) = Σ p_j J_j(n)` for `P` interpolating `log` on `1..N`; `Q = Ω‖H‖² + J + pole − 2Σ p_jτ(j)`.
- Stage transfer: `Q = Q_N + w(fold − end mass)`; composite stages free; collar exit charge
  `Ω(ε)∫_{collars}H² ≤ J_∞` with `Ω(ε) ≥ log 3 > 2/e ≥ w_n` on every stage: every new fold is paid.
- Euler factorization of the window zeta operator (factored indicators, `e_p(1−δ_p) = 1`).
- End profile: `∫(Ω(−u)+Ω(A+u))H² ≤ J_∞`; `Q ≥ ∫V_A H² + pole`, `V_A = Ω_Γ + φ(d₋) + φ(d₊)`;
  windows of length `≤ 1/12` positive by the exit charge alone.
- Arakelov bundle `⊕_{m≤e^A}𝒪(½log m)`: RR `Nd + ½log N!`, slope `≤ A/2`.

## Open (README §7)
Positivity surviving the derivative at dimension zero; positivity across a small extension;
stage-resolved analytic control (AOT aperture transport); window capacity; exponent vs zero width.

## Log
- 2026-11-02 — created; fifteen modules formalized; README written.
