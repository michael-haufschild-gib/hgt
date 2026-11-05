# Critical Hardy theory of the window cone (CHT)

- **ID:** cht
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean), programme
- **Source:** docs/reports/review-0511/obstacles-summary.md §2.7.1
- **Statement:** Structure of the nested cones `𝒜(c)`: effective uniqueness, margin law, edge profile, datum classification.

## Goal
Exact finite-level theory of the window cone. A receiver: no sign for ζ is claimed. Lean folder
`formal/GaloisForLFunctions/CriticalHardyTheoryOfTheWindowCone/`, foundational README there.

## Gates
- [x] 0 → 1  in-progress
- [ ] 1 → 2  fully-proven
- [ ] 2 → 3  formalized

## Approach

Work list, in order (paper proofs below; each must be followed by Lean).

**W1 Cone calculus.** Same-level box from two-site tests; closed convex finite-dim; qualitative collapse
`∀n ∀ε ∃c₀ ∀c≥c₀ ∀λ∈𝒜(c), |λ(n)−Λ(n)|<ε` from box compactness + `eq_vonMangoldt_of_weilPositiveFull`.

**W2 Finite-window duality.** No level shift: on a fixed window finitely many weights act, two-site tests give a
compact box in every coordinate with `log n < 2c`, so Farkas + finite intersection property give
`(∃λ, W_λ ≥ m‖·‖² on window) ⇔ ∀ blind finite family, ΣαH(f) ≥ mΣα‖f‖²`.

**W3 Margin ceiling.** Truncate twisted-arc family `F_j` (`F̂_j = ΞQ_j`), weights `w_j = 4√2·4^j m_j/(2j)!`,
`m_j ≤ 4^{−j}`. Bound `F_j` on `Re s = σ` by `Γ(σ/2+j)`: `|F_j(x)| ≲ Y^j e^{−Y}`, `Y = πe^{2x}`; `Σ_j w_j F_j(x)²
≲ poly(Y)e^{−Y}`. Then for all λ: `m Σw_j‖F_j^c‖² ≤ Σ w_j Re W_ζ(F_j^c) + box·tail`. Output: `λ*(c) ≤ K e^{−κ e^{2c}}`.
Negative side: `F_j(−x)` has `Q_j(−z) = ∏(k+½−s/2)`, bound by `|s/2+j|^j`.

**W4 Polarization.** For λ∈𝒜(c): `|W_λ(F^c, g)|² ≤ W_λ(F^c)W_λ(g)`; subtract `W_Λ`: theta-smoothed reading
`S_δ(x) = Σ_n δ_n n^{−1/2}(Φ(x−log n)+Φ(x+log n))` doubly exponentially small on the window.

**W5 Datum.** `Ω_q = Ω + log q`. No pole, `log q ≥ log π − ψ(¼)`: symbol ≥ 0, 0∈cone, ball in cone. Pole weight
β < 1, or conductor q < 1: cone empties at a finite window for ALL weights. Conductor-criticality.

**W6 Edge profile on a window.** Solutions of the window equation: `κ₊u` continuous at the edge,
`u(x)√log(1/x) → h(0)`.

**W7 Single-atom dual measures.** (Quantified arc minimum principle.) Reading of `Σ_m d(m)𝓕h(mn)` at `log n` is
supported on divisors of `n₀` when `𝓕h(N) = tδ_{N,n₀}`. If a positive arc measure has that moment vector then
`±t·(λ−Λ)(n₀)n₀^{−1/2} ≲ tail(c)`: explicit `ε(n,c)`. Case `G(½) ≤ 0` quantifies: `ψ ≥ −Ct`, first mode missing,
`|sin 2πmx| ≤ m sin 2πx` give `|a_m| ≲ m e^{2πm} t`. Case `G(½) > 0`: open.

## No-go closure (mandatory when falsified)
- **Exact killing theorem/mechanism:** —
- **Strongest positive survivor:** —
- **New insight:** —
- **Status:** —

## Log
- 2026-11-05 — created; README draft written.
