# FE constraint critical-line fixed locus

- **ID:** fe-constraint-critical-line-fixed-locus
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) - grade **BRIDGE**
- **Priority:** FOUNDATIONAL
- **Source:** split from `../2-fully-proven/constraint-not-flow-theorem.md` section 3.
- **Statement:** The functional-equation map `sigma(s)=1-s` has order two, and the conjugate FE constraint
  `sigmaConj(s)=1-conj(s)` fixes exactly the critical line `Re(s)=1/2`.

## Goal

This banks the exact finite complex-arithmetic core of the "constraint, not flow" card: the FE symmetry is an
order-two constraint, and its conjugate fixed locus is the critical line. It does not formalize the infinite
torus spectral theorem, Hilbert-Polya scope, orthogonality meta-theorem, DSS, Connes' spectral realization, or
any positivity/RH claim.

## Paper Proof

For the FE involution, `sigma(s)=1-s`, so `sigma(sigma(s))=1-(1-s)=s`.

For the conjugate constraint, `sigmaConj(s)=1-conj(s)`. If `sigmaConj(s)=s`, then comparing real parts gives
`1-Re(s)=Re(s)`, hence `Re(s)=1/2`; comparing imaginary parts is automatic since
`Im(1-conj(s))=Im(s)`. Conversely, if `Re(s)=1/2`, then real and imaginary parts of `1-conj(s)` agree with
those of `s`, so `sigmaConj(s)=s`.

## Gates

- [x] 0 -> 1  in-progress: exact FE-constraint fixed-locus core extracted from the broader structural card.
- [x] 1 -> 2  fully-proven: paper proof above by elementary complex arithmetic.
- [x] 2 -> 3  formalized: Lean theorems `sigma_involutive`, `sigmaConj_involutive`, and
  `sigmaConj_fixed_iff_critical` in `formal/GaloisForLFunctions/Core.lean` and
  `formal/GaloisForLFunctions/SigmaOrbit.lean`; names checked by scratch file; `#print axioms` uses only the
  allowed standard subset `[propext, Classical.choice, Quot.sound]`; `lake build` green; `check_axioms.sh`
  PASS.
- [ ] 3 -> 4  publication-ready: include as the FE-constraint lemma in the Hilbert-Polya re-posed note.

## Door Passport

Door-2 strips this to elementary complex arithmetic for the map `s |-> 1-s` and conjugation, so it is BRIDGE.
Its value is as the Lean-certified fixed-locus anchor for the broader constraint-not-flow theorem.

## Log

- 2026-06-19 - Leaner split this exact FE fixed-locus lemma from `constraint-not-flow-theorem`. The parent card
  remains in `2-fully-proven` because the infinite flow, orthogonality, DSS, and Connes/Hilbert-Polya scope are
  not fully Lean-formalized.
