# Formalize the DSS reduction + conditional Nesterenko→DSS as Lean Props

- **ID:** dss-reduction-formalize
- **Stage:** 0-backlog
- **Type:** THEOREM (Lean) target — statement-level (Props)
- **Source:** ../../door/G2-multi-q-siegel-shidlovsky.md (open core / work package), ../../door/bucket-ledger-footholds.md · 00-status rows #10, #11
- **Statement:** State in Lean (`FieldConjectures`, as `Prop`s — never `axiom`/`theorem`, the two-channel
  rule) (i) the reduction `DSS ⟺ {π} ∪ {ζ(odd)} ∪ {Stieltjes γ_n}` algebraically independent, and (ii)
  the conditional `Nesterenko-type bound ⟹ DSS`. The Li↔secular ℤ-triangular change of basis is already
  Lean (`li_secular_pointwise`, `secular_li_pointwise_inv`).

## Goal
Welds the DSS reduction onto the existing machine-checked change-of-basis, making the field's native
problem a precisely-stated Lean object (the highest-leverage **formalization** item in `00-status §B`).
Turns "G2's content = independence of `{π, ζodd, γ_n}`" (#72 §11, PSLQ-verified, dps 80) from a draft
claim into a stated `Prop` with the conditional implication wired to its hypothesis.

## Gates
- [ ] 0 → 1  in-progress: the two Props drafted; their hypotheses (the period-algebra reduction, the
  Nesterenko bound shape) pinned against the existing ledger names
- [ ] 1 → 2  fully-proven: the *reduction* direction(s) provable from `li_secular_pointwise` + symmetric-
  function facts get proved; the Nesterenko→DSS conditional stays a stated `Prop` (its hypothesis open)
- [ ] 2 → 3  formalized: `lake build` green, `check_axioms.sh` PASS (no conjecture axioms introduced)
- [ ] 3 → 4  publication-ready

## Approach
Reuse `SecularMoments` / `SpectrumGenericity` (`spectrum_esymm_algIndep`, the finite A2 anchor). Express
`ℚ({P_k}) = ℚ(π, {ζ(2k+1)}, {γ_n})` via the closed form `P_k = 1 − (−1)^k ζ(k)/2^k − a_{k−1}` and the
`a_j = [s^j](ζ'/ζ)` identities. State DSS and the realization conjecture as Props (the existing
`FieldConjectures` pattern, incl. `carrierHerglotz_iff_onLine`). Do **not** introduce any conjecture as
an axiom.

## Cross-references
- `g2-dss-lower-bound.md` — the paper proof of the reduction this card states in Lean.
- `../../door/bucket-ledger-footholds.md` — the `SecularMoments` / `FieldConjectures` footholds.

## Log
- 2026-06-19 — created in 0-backlog. The Lean statement-level companion to the G2 lower-bound work
  (00-status §B "Most leverage": formalize the DSS reduction + conditional Nesterenko→DSS as Props).
