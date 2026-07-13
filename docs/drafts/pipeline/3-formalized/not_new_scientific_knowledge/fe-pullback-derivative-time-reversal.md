# FE pullback derivative time reversal

- **ID:** fe-pullback-derivative-time-reversal
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Priority:** FOUNDATIONAL
- **Source:** split from `../2-fully-proven/completed-connection-category.md` section 3
- **Statement:** Pullback by the functional-equation involution `sigma(s)=1-s` conjugates the complex
  derivative to its negative: `sigma^* d/ds sigma^* = -d/ds` on functions differentiable at `s`.

## Goal
This banks the exact archimedean time-reversal algebra behind the completed connection card's PT statement.
It does not formalize the completed connection category, prime-lane parity, Hilbert-Polya operators,
unitary holonomy, PT-unbroken spectral theory, or RH.

## Paper Proof
Let `iota(s)=1-s` and define pullback by

`iota^* f = f o iota`.

Since `iota` is an involution, `(iota^*)^2 = id`. The derivative of `iota` is `-1`. If `f` is differentiable
at `iota(s)`, the chain rule gives

`d/ds (f(iota(s))) = f'(iota(s)) * iota'(s) = -f'(iota(s))`.

Evaluating at `iota(s)` and using `iota(iota(s))=s` gives

`d/ds (f(iota(s))) |_{s=iota(s0)} = -f'(s0)`.

Equivalently,

`iota^* (d/ds) iota^* f = -d/ds f`.

## Gates
- [x] 0 -> 1  in-progress: derivative time-reversal extracted from the completed connection PT card.
- [x] 1 -> 2  fully-proven: paper proof above by involutivity and the chain rule.
- [x] 2 -> 3  formalized: Lean definitions/theorems `fePullback`, `fePullback_involutive`,
  `hasDerivAt_sigma`, `hasDerivAt_fePullback`, `deriv_fePullback_eq_neg`,
  `deriv_fePullback_at_sigma_eq_neg`, and `fePullback_deriv_fePullback_eq_neg_deriv` in
  `formal/GaloisForLFunctions/HTGeometry/PTInvolution.lean`; scratch `#check`/`#print axioms`, `lake build`, and
  `scripts/check_axioms.sh` pass.
- [ ] 3 -> 4  publication-ready: cite as the formal certificate for the FE time-reversal half of the
  completed PT-involution.

## Log
- 2026-06-19 - Leaner split this exact derivative-conjugation theorem from
  `completed-connection-category` section 3. The parent card remains in `2-fully-proven` because the
  completed connection category, prime-lane parity packaging, global PT holonomy, spectral theory, and RH
  are not fully Lean-formalized.
