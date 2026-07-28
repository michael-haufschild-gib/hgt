# Ramsey--Weyl causal phase law

- **ID:** `ramsey-weyl-causal-phase-law`
- **Stage:** 3-formalized
- **Type:** THEOREM / QUANTUM CLOCKS / CAUSAL PROPAGATOR / NONPERTURBATIVE MEASUREMENT
- **Paper proof:**
  `../2-fully-proven/new_scientific_knowledge/ramsey-weyl-causal-phase-law.md`
- **Lean:** `formal/GaloisForLFunctions/HTGeometry/ContinuumChronometricGravity.lean`
- **Status:** unconditional algebraic and phase-germ core.

## Formalized theorem

Lean proves:

1. four Ramsey quadratures jointly recover two arbitrary complex ordered expectations;
2. a central order phase passes exactly through every complex-linear state functional;
3. when the reverse-order expectation is nonzero, their quotient is exactly the phase;
4. explicit right inverses turn the central reordering law into a group-commutator phase;
5. for
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
- `orderedExpectation_eq_phase_mul_reverse`
- `orderedExpectation_ratio_eq_phase`
- `centralOrderPhase_groupCommutator`
- `causalOrderPhase`
- `hasDerivAt_causalOrderPhase_zero`
- `causalPairing_eq_I_mul_deriv_orderPhase_zero`

## Exact boundary

Lean does not instantiate the central phase with a relativistic Weyl algebra, construct controlled
local Weyl pulses, prove detector backreaction control, or perform globally hyperbolic retarded
support splitting. Those remain physical and analytic obligations.

