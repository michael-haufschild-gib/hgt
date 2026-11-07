# Discrete Hardy phase recurrence cannot represent zeta zeros

- **Stage:** 5-failed
- **Mechanism:** use unitary coefficient phases on `ℓ²` to transport a finite exceptional zeta eigenspace.
- **Obstruction:** shifted zeta convolution has domain `{0}` for `ε≤1/2`. For `ε>1/2`, bounded Dirichlet point evaluations see only zeta arguments with real part greater than `1`.
- **Positive survivor:** exact transition from trivial to dense domain at `ε=1/2`; finite coordinate sequences belong on the dense side.
- **Paper and Lean:** complete; `ArithmeticInnerFunctionTheory.closure_shiftedZetaDomain` and `shiftedZetaDomain_nontrivial_iff`, in `TheDirichletHardyDomainOfZeta.lean`. [Proof and audit](../3-formalized/dirichlet-hardy-zeta-domain-threshold.md).
- **Scope:** this excludes the proposed multiplier model, not an actual finite exceptional zero layer. AAL remains undecided.
