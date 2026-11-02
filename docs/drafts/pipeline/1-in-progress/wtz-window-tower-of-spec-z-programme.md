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

## Conjecture loop (ledger)
| # | Conjecture | Test | Status |
|---|---|---|---|
| C1 | On the atomic lattice `|⟨ρ(Λ)ιg,ιg⟩| ≤ ½(Σ_{d≤N}Λ(d)/d + log N)‖ιg‖²` (Mertens size, not `ψ_{1/2}`) | numerics: λ_max ≈ ½ Mertens (N ≤ 3000) | **[L]** `TheAtomicLatticeSeesTheMertensSum` |
| C1' | sharper: λ_max ≤ ½ log N | numerics N ≤ 3000 (ratio → ½ from above vs Mertens; `≤ ½ log N` holds) | open (needs Mertens `Σ Λ/d ≤ log N`) |
| C2 | stage multiplicativity: `v(f*g) = v(f)v(g)`, leading coeff multiplies; exact nilpotency order | paper | **[L]** `TheValuationAndTheUnitsOfTheTower` |
| C3 | Wiener's lemma: `ρ_A(f)` unit ⇔ `f(1) ≠ 0`; spectrum `{f(1)}` | paper | **[L]** same module |
| C4 | tangent principle `J_k(n) ≥ [n=1] + kΛ(n)` (k ≥ 0) ⇒ nonneg tests: `⟨ρΛH,H⟩ ≤ (τ(k) − ‖H‖²)/k` | paper | **[L]** `TheTangentPrincipleOfTheTateFamily` |
| N0 | numeric window model (sine basis, Lévy symbol from ω): μ(0.3)=0.225, μ(0.6)=0.0086, μ(0.8)=2e−4, ≈0 beyond 1 | harness `weilwin.py` | tool; precision ~1e−3 |
| C5 | archimedean index `ι_Γ(A)` = #neg squares of `Ω_Γ + J_∞` on the window: `0` below `A₁ ≈ 0.215`, `1` on `(A₁, A₂ ≈ 0.762)`, then `≈ 2A` (Weyl, symbol zero `ξ₀ ≈ 2π`) | numerics `archindex.py` | observed; second (odd) direction appears after `log 2` |
| C5' | pointwise-in-`J` mechanisms cannot pass `A₁ ≈ 0.215` (true ground energy of `Ω_Γ + J_∞` crosses 0); Picone parabola weight reaches ≈ 0.20, exit potential 0.18 | numerics `picone.py` | learned: beyond `A₁` the pole is indispensable |
| C6 | `m^k + I_N = {f : f(n)=0 for n ≤ N, Ω(n) < k}`; `gr_k` has basis the `k`-almost primes ≤ N (Hilbert function = Landau `π_k(N)`) | paper | **[L]** `TheHilbertFunctionOfTheTower` |
| C7 | socle of `D_N` = span `δ_n`, `N/2 < n ≤ N` (type `⌈N/2⌉`); Gorenstein ⇔ `N ≤ 2` (window `< log 3`) | paper | **[L]** same module |
| C8 | parity at the first prime: on `[log 2, log 3)` the fold `T₂` raises the σ-odd sector and lowers the σ-even sector; pole does the opposite | numerics `parity.py` (odd min −0.013→+0.030 at A=0.76) | observed |

