# Review-0311 §2.5: breakthrough questions below RH

- **ID:** R0311-25
- **Stage:** 1-in-progress
- **Type:** CONJECTURE (loop)
- **Source:** `docs/reports/review-0311/obstacles-summary.md` §2.5.1–2.5.4
- **Statement:** Give a definite, Lean-formalized answer to each of the four §2.5 questions.

## Questions

| # | Question | Owner folder | Status |
|---|---|---|---|
| 2.5.1 | Two-collar recursion: `S^N_ε`, its evolution law, closed collar coupling at stages 1, 2 | `CanonicalSystemOfTheWindowTower/` | open |
| 2.5.2 | Hecke-equivariant completion: exact Weil = Krein identity with Hecke ↔ `T_p − Id` | `RenormalizedIntersectionTheory/MayerScattering/` (other agent active on F2 synthesis) | open |
| 2.5.3 | Log-free unit-window occupancy `D_win` | `RHTower/WD/` | open |
| 2.5.4 | Growing conductors at the critical curve, then `M(N) → N` | `ArithmeticHodgeTheoryOfDegenerations/` | open |

## 2.5.1 — mathematical core

Stage `n = N+1`, `ℓ = log n`, `w = Λ(n)/√n`, `ε < log((n+1)/n)`, `A = ℓ+ε`; collars
`L = [−A,−ℓ]`, `R = [−ε,0]`, interior `I = [−ℓ,−ε]`; collar coordinate `t ∈ [0,ε]`, the fold is the
identity `J` in collar coordinates.

1. **Ordered coupling.** For `f` supported left of `g`, Weil's complete form satisfies
   `Q(f+g) = Q(f)+Q(g)+2∫∫f(u)g(v)κ(v−u) − 2Σ_n w_n∫f(u)g(u+log n)` with
   `κ(x) = 2cosh(x/2) − ω(x) = e^{x/2} − e^{−x/2}/(e^{2x}−1) = e^{x/2} − Σ_{k≥1}e^{−(2k+½)x}`:
   the trivial divisor of `ζ` (pole `s=1` with `+`, trivial zeros `s=−2k` with `−`); the Gamma pole
   `s=0` cancels against the pole term.
2. **Gluing.** `Q(x_L+y+x_R) = Q(x_L+y)+Q(y+x_R)−Q(y)+2κ(x_L,x_R)−2w⟨x_L,x_R⟩`, the three `Q`'s
   on windows of length `ℓ` (previous level).
3. **Transmission.** Across an interval the archimedean datum transmits only the moments at the
   trivial divisor; folds `n ≤ N` add delays (shift couplings). Exact Bellman/Kalman update of the
   past information form on the mode space = the Riccati law; a prime power adds an impulse.
4. **Disk law.** Stage positivity ⟺ previous window positive and `|C(x_L,x_R) − w⟨x_L,x_R⟩|² ≤
   S_L(x_L)S_R(x_R)`: the fold lies in the Carathéodory disk centred at the frozen coupling with
   radii the one-end complements of the previous window.

Numerics (stage 1, piecewise-constant, scratch `collar.py`): frozen coupling has two dominant
singular values (`≈0.50, 0.48` at `ε=0.069`), the rest `< 10⁻⁶`; on constants it is `≈ w`
(`0.488` vs `0.490`); frozen Schur parameter norm `1.8 → 39`, full `0.33 → 0.92` for
`ε = 0.07 → 0.25`.

## Ledger

| # | Conjecture | Result |
|---|---|---|

## Log
- 2026-11-03 — created
