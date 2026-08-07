# Sonin principal-relative trace splitting and unique finite part — formalized

- **ID:** `sonin-principal-relative-trace-splitting`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Scientific status:** `[LEAN-PROVED] [CORPUS-NEW WELD] [NOVELTY UNVERIFIED] [NOT RH]`
- **Paper proof:**
  `../../2-fully-proven/new_scientific_knowledge/sonin/sonin-principal-relative-trace-splitting.md`
- **Status:** unconditional; no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe`

## Lean modules

- `formal/GaloisForLFunctions/RHTower/SoninPrincipalRelativeIdeal.lean`
- `formal/GaloisForLFunctions/RHTower/TraceClassCyclicity.lean`
- `formal/GaloisForLFunctions/RHTower/TraceClassOperatorTrace.lean`
- `formal/GaloisForLFunctions/RHTower/SoninPrincipalRelativeTraceSplitting.lean`
- `formal/GaloisForLFunctions/RHTower/SoninFinitePartUniqueness.lean`

## Formal theorem chain

1. `SoninPrincipalRelativePresentation` and `toOperator` are the presentation map `Φ_p(A,K)=S_A+K`
   of `(1)`; `toOperator_zero`, `toOperator_add`, `toOperator_smul` make it linear.
2. `IsSoninPrincipalRelativeIdeal.memSchattenClass_one` is item 2: every exact relative correction
   is Schatten-1.
3. `traceClassRoot`, `traceClassRoot_isHilbertSchmidt` and `MemSchattenClass.one_isTraceClass`
   are the factorization `(6)` of a Schatten-1 operator into two Hilbert–Schmidt factors;
   `MemSchattenClass.one_opTrace_comp_comm` is the cyclicity `(7)`, with
   `opTrace_add_of_memSchattenClass_one` and `opTrace_smul` giving linearity of the ordinary trace
   on the ideal — item 3.
4. `SoninPrincipalRelativePresentation.toOperator_injective` is the directness `(8)`–`(9)`, resting
   on `finitePrimeSoninPrincipalShellCombination_not_mem_relativeIdeal_of_ne_zero`: on an injective
   prime list no nonzero principal shell combination lies in the relative ideal.
5. `principalTrace`, `finitePart`, and `finitePart_eq_of_toOperator_eq` define the signed finite
   part `(3)` and show it depends only on the represented operator; `finitePart_add`,
   `finitePart_smul`, `finitePart_neg` give its linearity.
6. `soninPrincipalRelativeRange` makes the presented operators a submodule of the bounded
   operators, `shell_mem_soninPrincipalRelativeRange` and `relative_mem_soninPrincipalRelativeRange`
   place both normalizations inside it, and `soninFinitePartₗ` descends the finite part to a linear
   functional on it with `soninFinitePartₗ_shell` and `soninFinitePartₗ_relative` as the two
   normalizations `(2)` — item 4, existence half.
7. `soninPrincipalRelativeRange_eq_shell_add_relative`,
   `eq_soninFinitePartₗ_of_normalizations`, `existsUnique_soninFinitePart` and
   `apply_toOperator_eq_finitePart` are item 4's **uniqueness** half: exactly one linear functional
   on that subspace carries the two normalizations.
8. `finitePrimeSoninQuadraticCorner_principalRelativeEq_shellCombination` is `(10)`, so
   `ofQuadraticCorner` and `toOperator_ofQuadraticCorner` place the actual finite prime Gram
   combination inside the presented subspace.
9. `finitePart_ofQuadraticCorner`, `soninFinitePrimeAnomaly` and
   `finitePart_ofQuadraticCorner_eq_anomaly` are `(4)`–`(5)`: the finite part of the Gram
   combination is the logarithmic orbital trace plus the exact residual anomaly, whose linearity in
   the coefficient matrix is `soninFinitePrimeAnomaly_zero`, `_add`, `_smul`.

## Meaning

The exact principal shell and the exact relative ideal form a direct sum on every finite injective
prime Sonin Gram system, and the ordinary trace on the residual determines the *unique* signed
extension of the principal logarithmic trace.  The exact finite-place anomaly is therefore a single
linear functional of the coefficient matrix, with no regulator, quotient representative, positivity
hypothesis, RH hypothesis, or zero datum entering.

## Scope

This closes construction, representative independence and uniqueness on every finite prime
subsystem.  It is not a cofinal statement: the sibling aperture card proves that every strict
aperture pair has a genuine prime whose restriction defect leaves this class.

## Verification

- `lake env lean` passes on all five modules;
- `#print axioms` on all 50 declarations named by the paper card returns only `propext`,
  `Classical.choice`, and `Quot.sound`;
- all four modules are imported by `GaloisForLFunctions.RHTower`.

## Remaining frontier

The Burnol-completed coercivity question, constrained but not settled: the bare aperture channel is
unbounded below (`not_exists_lower_bound_soninAperturePacketCurvature_re_opTrace`) and any working
completion must be unbounded above along the unit-weight packet family
(`not_bddAbove_of_lower_bound_completion`).
