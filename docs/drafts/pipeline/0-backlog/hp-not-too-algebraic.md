# The Hilbert–Pólya operator "can't be too algebraic" (B18)

- **ID:** hp-not-too-algebraic
- **Stage:** 0-backlog
- **Type:** CANDIDATE (directional)
- **Priority:** FUTURE
- **Source:** ../../door/bucket-new-sibling-conjectures.md (#85 B18), ../../door/G5-unitarity-gatekeeper.md · 00-status row #108
- **Statement:** A self-adjoint operator `H` with spectrum `{γ_n}` **"cannot be too algebraic"** — naive
  Hilbert–Pólya constructions fail **precisely because** they would force `{γ_n}` to be algebraic,
  contradicting DSS. This is **why candidate G5's operator is hard: the two faces fight** (A1 wants a
  concrete self-adjoint operator; A2 forbids its spectrum from being algebraic).

## Goal
A **structural obstruction** explaining the difficulty of the G5 operator
(`weil-positivity-operator.md`, `carrier-herglotz-rh.md`): it converts the empirical "no HP operator has
ever been found" into a **theorem-shaped constraint** — any HP operator must be transcendental-spectrum
in a strong sense, ruling out the algebraic constructions people keep trying. Couples A1
(operator-construction) to A2 (transcendence) as a *no-go* with a precise boundary.

## Door passport
- **Door-3:** the constraint is on the **difference-transcendence degree** of the spectrum (a native
  invariant): "too algebraic" = low difference-trdeg ⟹ ¬DSS.
- **Door-2:** "algebraic spectrum contradicts DSS" uses DSS (native) essentially — the obstruction is
  native to the extent DSS is; the bound on *how* algebraic an HP operator can be is the new content.

## Gates
- [ ] 0 → 1  in-progress: "too algebraic" given a precise meaning (an algebraicity measure on the
  spectrum); the implication "too algebraic ⟹ `{γ_n}` algebraic ⟹ ¬DSS" stated
- [ ] 1 → 2  fully-proven: the no-go proved (a quantitative bound on the algebraicity any HP operator can have)
- [ ] 2 → 3  formalized
- [ ] 3 → 4  publication-ready

## Approach
Formalize the chain "operator too algebraic ⟹ spectrum algebraic ⟹ contradicts DSS"; quantify
"too algebraic" so the no-go has a boundary (the maximum algebraicity compatible with DSS). This
sharpens why the operator approaches (`weil-positivity-operator.md`) are hard and where they must be
transcendental.

## Cross-references
- `weil-positivity-operator.md`, `carrier-herglotz-rh.md` — the G5 operator this constrains.
- `g2-dss-lower-bound.md` — DSS is the input that forbids algebraic spectra.

## Log
- 2026-06-19 — created in 0-backlog. HP "can't be too algebraic" (B18, directional): the structural
  obstruction (the two faces fight) explaining why the G5 operator is hard.
