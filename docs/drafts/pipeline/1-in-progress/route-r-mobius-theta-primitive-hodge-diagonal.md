# Route R Möbius--theta primitive/Hodge diagonal

- **ID:** ROUTE-R-MPART-HODGE-DIAGONAL
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** rh-current-frontier-map.md · Route R
- **Statement:** The literal `mPart` source atom at label `p^(e+1)` is the valuation-depth `e`
  primitive half-density atom; after source-derived primitive promotion its two reflected Hodge
  orientations have coefficients `p^(±a(e+1))`.

## Goal

Construct first non-arbitrary common grading between physical Möbius--theta coefficient source and
global secondary Gamma/Hodge graph. This is necessary infrastructure for conservative resolved
graph descent: inverse-zeta exponent `e+1` must become valuation depth `e` because `mPart (e+1)` is
supported on `(e+1)`-st powers, not because two independent indices were identified by hand.

This theorem does not by itself imply graph admission or RH. Remaining open core is completed,
label-preserving graph convergence of the full source chain and faithfulness on the global relative
admission quotient.

## Gates

- [x] 0 → 1  in-progress: literal source atom located; canonical grade identification; exact proof
  plan through `term_mPart_pow`, prime Möbius value, half-density cancellation, and existing
  primitive/Hodge modular rate
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem, targeted module build green, formal lint PASS
- [ ] 3 → 4  publication-ready: standalone paper theorem and Lean certificate

## Approach

For `m=e+1`, inspect the actual direct integer-labelled summand of the internally promoted physical
source at base label `p`. Exact power reindexing places it at `p^m` in `mPart m`; its Möbius
coefficient is `-1`, its physical scalar is `-p^(-m/2)`, and its translation is `-m log p`.
The primitive promotion gauge `p^(m/2)` cancels exactly. The surviving translation depth equals the
existing Gamma/Hodge cell rate at `(p,e)`, so modular reflection produces reciprocal coefficients
`p^(±am)`. Prove all identities without divisor selection, then expose the exact balanced-capacity
classification inherited by the literal source diagonal.

## No-go closure (mandatory when falsified)

- **Exact killing theorem/mechanism:** Not falsified.
- **Strongest positive survivor:** Pending.
- **New insight:** `mPart` exponent and Hodge valuation depth have a canonical prime-power diagonal.
- **Status:** Paper/Lean proof in progress.

## Log

- 2026-08-02 — created in 1-in-progress after updated resolved-descent and admission-loss audit.
