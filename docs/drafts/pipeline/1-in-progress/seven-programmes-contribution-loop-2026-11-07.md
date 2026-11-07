# Seven-programme contribution loop (PTT, TAPO, ZCG, RAC, AAD, AGT, ASH)

- **ID:** spcl-2611
- **Stage:** 1-in-progress
- **Type:** CONJECTURE loop
- **Source:** user goal 2026-11-07; `docs/reports/review-0711/{obstacles-summary,walls-ledger}.md`; the seven READMEs
- **Statement:** conjecture → prove/formalize or refute → learn, aiming at significant contributions (open questions,
  missing tools, walls, insights). Working log: `logs/seven-programmes-contribution-loop-2026-11-07.md`.

## Goal
Each accepted contribution is an unconditional Lean theorem that answers or sharpens a stated open question of one of
the seven programmes, supplies a listed missing tool, or exposes a structural law of the field.

## Gates
- [x] 0 → 1  in-progress
- [ ] per conjecture: paper proof here, Lean module, audit

## Peer ownership (do not duplicate)
- TAPO is under active edit by another session (VK one-line bound, resonator mean, smooth-prime mean squares).
- AAD extremal-measure atoms, APD integer-norm one-offs, CHT, ThetaCuspSections, SumProductArithmeticOfTheLogarithm:
  other sessions.

## Conjectures

| # | Programme | Statement | Status |
|---|---|---|---|
| C1 | AGT Q1 | Doubling law `F_x F_{x+ℓ} = F_{2x}(2s)`; order-two twin pairs: `Θ ≤ 2 max θ_μ`, so `max ≥ 1/4` | formalized |
| C2 | AGT | Constant source: `max(θ_1(x), θ_1(x+ℓ)) ≥ 1/2` at order-two points; real Dirichlet twins have `θ_1 ≥ 1/2` | formalized |
| C3 | PTT §9.8 | A.e. order-two fibre and its antipode both have natural boundary `Re s = ½`; their product is `ζ(2s)` | formalized |

## Log
- 2026-11-07 — created; C1–C3 formalized and wired (AGT, PTT umbrellas); loop paused by the user.
