# Review-0311 §2.5: breakthrough questions below RH

- **ID:** R0311-25
- **Stage:** 1-in-progress
- **Type:** CONJECTURE (loop)
- **Source:** `docs/reports/review-0311/obstacles-summary.md` §2.5.1–2.5.4
- **Statement:** Give a definite, Lean-formalized answer to each of the four §2.5 questions.

## Questions

| # | Question | Owner folder | Status |
|---|---|---|---|
| 2.5.1 | Two-collar recursion: `S^N_ε`, its evolution law, closed collar coupling at stages 1, 2 | `CanonicalSystemOfTheWindowTower/` | answered, Lean: `3-formalized/r0311-two-collar-recursion.md` |
| 2.5.2 | Hecke-equivariant completion: exact Weil = Krein identity with Hecke ↔ `T_p − Id` | `RenormalizedIntersectionTheory/MayerScattering/` | answer written; modules compiling |
| 2.5.3 | Log-free unit-window occupancy `D_win` | `RHTower/WD/` | open |
| 2.5.4 | Growing conductors at the critical curve, then `M(N) → N` | `ArithmeticHodgeTheoryOfDegenerations/` | open |

## 2.5.2 — answer

- **Completion** `𝒦 = ℓ²(upper resonances)`, Krein form `[x, y] = Σ_s x_s conj(y_{s♯})`; PM's core space
  embeds densely and isometrically for the Krein forms; window map `𝓦_A H = (√m_{2s} Φ_H(s, 1))_s`,
  bounded `‖𝓦_A H‖² ≤ 20e^A T ‖H‖²_{W^{2,1}}`; `Q(H) = 2 Re[𝓦H, 𝓦H]` exactly; reflection is the
  twisted conjugate Krein reflection (`TheHeckeEquivariantCompletion`).
- **Every prime.** Hecke cones `X_p = {ad − bc = p, 0 ≤ c < a, 0 ≤ b < d}` tile the quadrant: each
  vector in one cone, `p`-divisible vectors in `p + 1` (`TheHeckeConesTileTheQuadrant`). Hence
  `Σ_{X_p} P_w(M(a,b)) = P_w(a,b) + pP_w(pa,pb)` and `T_{p,w/2}P_w(·,1) = (1 + p^{1−w})P_w(·,1)`
  for `Re w > 2` (`TheBarnesPeriodIsAHeckeEigenfunctionForEveryPrime`). The Eisenstein period
  `E_w` is holomorphic in `w` on `{Re w > 0} ∖ {1, 2}` at every `a > 0` (three-term propagation from the
  Mayer disc) and equals `P_w(·,1)` for `Re w > 2`; the identity theorem on this connected set gives
  `T_{p,s}ψ_s = (1 + p^{1−2s})ψ_s` on the strip and at every resonance
  (`TheEisensteinPeriodIsAHeckeEigenfunctionForEveryPrime`). So `T_p − Id` acts by `p^{1−2s}`, the
  Mellin multiplier of `F_pH = √p H(· + log p)`: `T_pΦ_H − Φ_H = Φ_{F_pH}` and
  `𝓦(F_pH)_s ψ_s = 𝓦(H)_s (T_p − Id)ψ_s` (`TheSourceHeckeOperatorsAreMellinTranslations`).

## 2.5.4 — working notes

Exact conductor law (AHD `ram_layer_sharp`): the conductor-`m` window has second order
`(log N/∫φ²) Σ_{de=m} μ(d) 𝒜_N(c/e)`; the count `7φ(m)J(m)/K` is its limit when every `c/e → ∞`.
The quiet region of the Ramanujan block ends at `|τ| ≍ N/m`, the spline band at `|τ| ≍ N/c`: the two
meet at `m ≍ c`. Candidate answer: count form uniform exactly for `m = o(c_N)`; beyond, the exact
alias law with the scaling function `R(c/m)`.

## 2.5.3 — working notes

`D_win` ⟺ thin-Planck-shadow windows are `o(V)` (corpus): the total shadow measure of deep zeros is
`≤ Ce^{−rA}V/A` unconditionally, so `D_win` fails only through windows holding few, spread-out deep
zeros. Every deep zero is detected only on its own `1/log V` neighbourhood; a unit window holds
`log V` such cells.

## Ledger

| # | Conjecture | Result |
|---|---|---|
| 1 | Source Hecke for general `p` from a rational kernel identity as at `p = 2` | replaced: the number of cones grows with `p`; the cone count (tiling) is the uniform mechanism |
| 2 | Continue the general-`p` eigenvalue in `a` from a segment as at `p = 2, 3` | replaced: branch arguments leave the Mayer disc for `p ≥ 5`; continuation in `w` at every `a > 0` instead |
| 3 | `D_win` from Selberg's density `N(½ + A/log V, 2V) ≪ e^{−A/4}V log V` | fails by one `log V`: consistent with an `e^{−cA}` fraction of zeros deep and one per window |
| 4 | `D_win` from Littlewood's lemma on each Burnol window at `σ₁ = ½ + A/(2 log V)` | the linear and quadratic Taylor terms of `log ζM` have window averages `O(e^{−cA/2}/log V)` (signal `A/log V` wins), but the cubic remainder `∫|ζM − 1|³` has no cancellation and is `e^{−cA}` per window: loses `log V` |
| 5 | `D_win` from a Laguerre-inequality violation at a deep pair | the pair gives `2/δ² = 2log²V/A²`, the real zeros `≍ log²V`: no violation for large `A` |
| 6 | Sup-norm zero detection by `ζM ≈ 1` on unit windows | the mollified residual has `≍ log V` independent values per window; its maximum is `≍ e^{−Aθ}√(log log V)` → ∞ for fixed `A` |

