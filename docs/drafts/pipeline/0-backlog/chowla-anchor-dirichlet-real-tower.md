# The Chowla anchor: the seam-sign bit of the Dirichlet family reads Siegel parity

- **ID:** chowla-anchor-dirichlet-real-tower
- **Stage:** 0-backlog
- **Type:** CONJECTURE (arithmetic anchor law) + THEOREM (Lean, transfer bricks)
- **Source:** successor of seam-sign-pinning (§Closure, rng-drawn); the dissolution theorems of
  `EquivariantRootDissolution.lean` are generic in the carrier — this card feeds them the first
  carrier whose anchor bit is not a theorem.
- **Statement:** For a real primitive Dirichlet character χ, the seam-sign anchor bit of the
  Real (Schwarz-equivariant) root tower of Λ(s,χ) at the central anchor equals sign L(½,χ), and
  equals the parity of the total multiplicity of real zeros in (½,1); regional dissolution of the
  equivariant theory for Λ_χ ⟺ that parity is even. Family-wide dissolution = central
  nonnegativity (GRH-implied, Chowla-adjacent, open).

## Goal
For ξ the anchor bit is a theorem (`xi_pos_on_real_anchor`, η-positivity) and the seam-sign
theory dissolves regionally into the plain Kummer ladder. One carrier over, the same bit is an
open arithmetic quantity. What proving the transfer gives: the equivariant-root machinery becomes
an arithmetic instrument — the first place in the program where the seam-sign obstruction is
*not* discharged for free and instead detects the Siegel-zero sector.

Known inputs, [SEARCH] register: real primitive χ has root number +1, so Λ(1−s,χ) = Λ(s,χ) and Λ
is real on the real axis (real coefficients) — Λ_χ is an FE+Schwarz member; L(σ,χ) ≠ 0 for
σ ≥ 1, and Λ → +∞ on the real axis, so every sign flip of Λ on (½,∞) happens at a real zero in
(½,1). The sign-transport skeleton is unconditional; only the VALUE of the bit is open.

`[CONJECTURE]` the anchor law: sign L(½,χ) = (−1)^{Σ ord of real zeros in (½,1)}, and the
equivariant surplus of the Real tower of Λ_χ over the plain tower on central symmetric windows is
exactly this one bit — the Siegel parity. `[OPEN CORE]` whether the bit is + for every real
primitive χ (central nonnegativity); any structural constraint the weld/ledger machinery puts on
it beyond GRH-transfer is the moonshot.

## Gates
- [ ] 0 → 1  in-progress: well-posed; mathlib Dirichlet completed-L API surveyed on THIS
      toolchain (verify names in /tmp scratch — do not trust recalled names)
- [ ] 1 → 2  fully-proven: anchor law on paper (real-axis sign transport = real-segment analogue
      of `xi_line_sign_iff_even_cumulative_order`)
- [ ] 2 → 3  formalized: FESchwarz instance for Λ_χ (real primitive χ); anchor-law bricks;
      dissolution instance `lambda_chi_equivariant_root_iff` with the sign clause LEFT OPEN as
      the arithmetic interface
- [ ] 3 → 4  publication-ready

## Approach
1. Instantiate the generic dissolution: `exists_equivariant_root_iff_anchor_pos` and
   `exists_equivariant_root_iff_orders_dvd` need only `FESchwarz Λ_χ` and anchor data — no new
   obstruction theory.
2. Real-axis sign transport: re-run the `CreaseHolonomy` peel along the real segment (½,1] from
   the positivity anchor σ ≥ 1 down to ½; conclusion = the anchor law.
3. The interface theorem: dissolution for Λ_χ on central windows ⟺ 0 < Λ(½,χ) — the sign clause
   as an explicit `Prop` hypothesis, the card's arithmetic socket.
4. Then the science: what does the crease ledger of Λ_χ along the critical line say about the
   real-segment ledger? The two ledgers share the anchor — a constraint tying line parity to
   Siegel parity would be new.

## Log
- 2026-07-11 — created in 0-backlog from seam-sign-pinning §Closure (rng pick: chowla-anchor).
