# CC gauge-trivialization identity

- **ID:** cc-gauge-trivialization-identity
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Priority:** FOUNDATIONAL
- **Source:** split from `../2-fully-proven/multiplier-dichotomy-theorem.md` case (I)
- **Statement:** If a rank-one multiplier is constant up to coboundary, `a=c*sigma(g)/g`, then gauging by `1/g` changes the multiplier to the constant `c`; the analytic model `g(z) exp(z*lambda)` satisfies the expected local first-order ODE where `g(z) != 0`.

## Goal
This banks the elementary formal core of the constant-up-to-coboundary case. It does not formalize the global shift equation, Picard-Vessiot classification, degree-at-infinity obstruction, or the imported hypertranscendence converse.

## Paper Proof
For the gauge identity, write `a=c sigma(g) g^{-1}` and choose `h=g^{-1}`. The transformed multiplier is
`a sigma(h) h^{-1} = c sigma(g) g^{-1} sigma(g^{-1}) (g^{-1})^{-1} = c`, using `sigma(g^{-1})=sigma(g)^{-1}`.

For the local ODE, let `f(z)=g(z) exp(z lambda)`. The product rule gives
`f'(z)=g'(z) exp(z lambda)+g(z) exp(z lambda) lambda`. If `g(z) != 0`, this is
`(g'(z)/g(z)+lambda) f(z)`.

## Gates
- [x] 0 -> 1  in-progress: exact CC gauge and local ODE identities extracted from multiplier dichotomy case (I).
- [x] 1 -> 2  fully-proven: paper proof above, using group cancellation and the product rule.
- [x] 2 -> 3  formalized: Lean theorems `ccGaugeMultiplier_eq_const` and `hasDerivAt_mul_exp_const_ode` in `formal/GaloisForLFunctions/MultiplierDichotomy.lean`; names checked by scratch file; `lake build` green; `check_axioms.sh` PASS.
- [ ] 3 -> 4  publication-ready: include as the formal certificate for multiplier dichotomy case (I).

## Log
- 2026-06-19 — Leaner split this exact CC case-I core from `multiplier-dichotomy-theorem`. The parent card remains in `2-fully-proven` because its global shift solution, degree-at-infinity obstruction, and imported hypertranscendence converse are not fully Lean-formalized.

