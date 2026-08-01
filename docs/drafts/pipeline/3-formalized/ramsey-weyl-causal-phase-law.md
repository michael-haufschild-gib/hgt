# Ramsey--Weyl causal phase law

- **ID:** `ramsey-weyl-causal-phase-law`
- **Stage:** 3-formalized
- **Type:** THEOREM / QUANTUM CLOCKS / CAUSAL PROPAGATOR / NONPERTURBATIVE MEASUREMENT
- **Paper proof:**
  `../2-fully-proven/new_scientific_knowledge/other/ramsey-weyl-causal-phase-law.md`
- **Lean:** `formal/GaloisForLFunctions/HTGeometry/ContinuumChronometricGravity.lean`
- **Status:** unconditional algebraic and phase-germ core.

## Formalized theorem

Lean proves:

1. an abstract causal Weyl system with alternating real bilinear pairing and the half-phase product
   law has the exact full order phase and scaled group commutator;
2. opposite smearings give two-sided operator inverses;
3. four Ramsey quadratures jointly recover two arbitrary complex ordered expectations;
4. a central order phase passes exactly through every complex-linear state functional;
5. continuity and value one at zero give the required local nonvanishing denominator;
6. when the reverse-order expectation is nonzero, its ordered ratio is exactly the phase;
7. for
   \[
     \Omega_E(t)=\exp(-itE),
   \]
   the complex derivative at zero is \(-iE\), hence
   \[
     E=i\Omega_E'(0).
   \]

The last theorem removes the fixed-phase \(2\pi\) ambiguity using the calibrated phase germ rather
than a logarithm branch.

## Unconditional declarations

- `chronometricRamseyOrderQuadratures`
- `chronometricRamseyOrderQuadratures_injective`
- `CausalWeylSystem.operator_mul_swap`
- `CausalWeylSystem.operator_smul_mul_swap`
- `CausalWeylSystem.operator_mul_neg`
- `CausalWeylSystem.operator_neg_mul`
- `CausalWeylSystem.operator_smul_groupCommutator`
- `orderedExpectation_eq_phase_mul_reverse`
- `orderedExpectation_ratio_eq_phase`
- `eventually_ne_zero_of_continuousAt_eq_one`
- `causalOrderPhase`
- `hasDerivAt_causalOrderPhase_zero`
- `causalPairing_eq_I_mul_deriv_orderPhase_zero`

## Exact boundary

Lean proves the exact abstract causal-Weyl/Ramsey theorem.  It does not instantiate the abstraction
with a concrete globally hyperbolic field theory, construct controlled local Weyl pulses, prove
detector backreaction control, or perform retarded-support splitting.  Those remain physical and
analytic obligations outside the paper theorem.
