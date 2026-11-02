# The Window Tower of Spec ℤ (WTZ) — programme card

- **ID:** WTZ
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) programme
- **Source:** docs/reports/review-0211/obstacles-summary.md §2.7 (theory of the window tower)
- **Statement:** develop the tower `A ↦ W_A`: window algebra, transitions and control, Tate pieces
  vs Weil's form, growth law in `A`, end profile, lattice, selection.

## Goal
Answer the §2.7 questions by Lean theorems; build the tools. Folder
`formal/GaloisForLFunctions/WindowTowerOfSpecZ/`, umbrella `WindowTowerOfSpecZ.lean`, README there.
Seed programme CWS (`CohomologyOfWindowsOfSpecZ`) is owned by another agent: import, never edit.

## Planned modules
1. TheWindowDirichletAlgebra — window shifts, `ρ_A` ring hom, faithfulness mod `I_N`, nesting,
   position commutator, Tate twist, Weil's window form `Ω‖H‖² + J − 2⟨ρ(Λ)H,H⟩ + pole`.
2. TheTowerOfSmallExtensions — truncation ideals, socle law, Loewy length, cotangent = primes.
3. TheWindowFormIsTheDerivativeOfTheJordanCounts — `d/dk J_k(m)|₀ = Λ(m)`; Weil's arithmetic term
   is `−2 d/dk ⟨ρ(J_k)H,H⟩|₀`; `J_{β+1} = φ·#ℙ^β`.
4. TheGrowthLawOfTheWindowTower — centred pole plane, capacity `2sinh(A/2) − A`, window negativity,
   exponent `∈ [zero width, ½]`, RH ⇔ subexponential.
5. TheEndProfileOfAWindow — archimedean exit identity, `V_A = Ω(0) + φ(−u) + φ(A+u)`.
6. TheAtomicLatticeOfAWindow — atoms carry the regular representation of `D_N`.
7. Selection along the tower.

## Paper notes
- Right shift `T_t H(u) = 1_{u≤0}H(u−t)`: `T_sT_t = T_{s+t}` (s ≥ 0) for all `H`; `T_t = 0` on
  `F_A` for `t > A`; `[T_t, M] = −tT_t`; `e^{−kM}T_te^{kM} = e^{−kt}T_t`.
- `⟨T_{log n}H,H⟩ = ∫H(u)H(u+log n)` on `F_A`; Markov form collapses to `Ω‖H‖² + J − 2Σw_n⟨T H,H⟩`.
- Jordan: `J_k = μ * id^k`, `∂_k J_k(m)|₀ = (log * μ)(m) = Λ(m)`.
- Pole: `2Ĥ(0)Ĥ(1)` translation invariant; centred sinh `s_A(u) = 2sinh((u+A/2)/2)`,
  `‖s_A‖²_{W} = 4sinh(A/2) − 2A`.
- End profile numerics (scratch): `V_A(centre) < 0` from `A ≈ 0.18`; `φ(t) < 0` from `t ≈ 1.11`.

## Log
- 2026-11-02 — created; README draft written.
