# Corpus facts

Evidence: **source** means Lean statement and proof inspected; **programme** means a corpus README claim awaiting its cited proof. Neither label asserts a fresh compilation or transitive axiom audit. Interpretations belong in the final report.

## F01. Zeta zeros remove a probe obstruction

**Source.** For `0 < ε < 1/2`, put `ρ = 1 − ε + it` and `c(d) = d^(−ε) cos(t log d)`. Its repairing ideal in the critical Wiener algebra has a nonempty Bohr hull exactly when `ζ(ρ) ≠ 0`. When `ζ(ρ) ≠ 0`, that hull consists precisely of the two prime-coordinate characters attached to `ρ` and its conjugate.

The proof separates any third character using `(δ_p − a)(δ_q − b)`, a finite kernel vanishing on the prescribed pair. The final nonemptiness equivalence uses the existing receiver-payment criterion; the ideal calculation itself supplies no nonvanishing estimate for ζ.

Declarations: `mem_paidIdeal_oscillating_iff`, `mem_obstructionHull_oscillating_iff`, `obstructionHull_oscillating_nonempty_iff` in [TheZerosOfZetaAreWhereTheObstructionVanishes.lean](../../../formal/GaloisForLFunctions/ArithmeticOrientationTheory/TheZerosOfZetaAreWhereTheObstructionVanishes.lean).

## F02. Several different boundaries share the number one half

**Programme; direct proofs pending.** THIM distinguishes sign-blind payment, which requires damping **strictly greater** than `1/2`, from horizon-limit commutation, which holds **at and above** `1/2`. Below `1/2`, a paid infinite source need not have uniformly paid truncated rows. Relevant statements: `receiverBounded_amplitudeInvariant_iff`, `horizonLimit_commutes_with_receiver_iff` ([THIM](../../../formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/README.md)).

ACCE distinguishes the finite-horizon zero-damping limit from uniform admission: every fixed horizon has a bounded limit at damping zero; the obstruction can lie in a moving interior bump. `tendsto_dampedMobiusEnergy_nhdsGT_zero`, `riemannHypothesis_of_no_interior_bump` ([ACCE](../../../formal/GaloisForLFunctions/ArithmeticContinuationAndCriticalEnergy/README.md)).

## F03. The stated criticality obstruction permits losses

**Programme; direct proofs pending.** ACT's null sequences exclude subtracting a Hardy weight, reducing a prime rate or removing a fraction of the variance. Its README explicitly distinguishes these from negative floors: an aperture-uniform loss suffices for RH, while an exponential loss measures a strip. It also restricts the positive folded-supersolution obstruction to a specified decaying profile class ([ACT](../../../formal/GaloisForLFunctions/ArithmeticCriticalityTheory/README.md), mechanisms 4 and 9, traps).

## F04. A large positive norm can coexist with a small adverse pairing

**Programme; direct proofs pending.** The raw prime-comb energy is asymptotic to `4 exp(2r)` on normalized slow profiles; its first-power adverse charge is `o(exp r)` on the same family. The surviving operator is a translation on slow profiles and a resolvent on fixed profiles. The norm majorant discards the geometry of the particular pairing ([ArithmeticCompensationTheory](../../../formal/GaloisForLFunctions/ArithmeticCompensationTheory/README.md), mechanisms 1–12).

## F05. The scaling surface is a paired vector space

**Programme; direct definitions pending.** ACS explicitly defines its scaling surface as a vector space with a pairing, not a scheme. Its finite-field golden datum satisfies integral counts, functional equation, Witt integrality and Adams structure while having one negative square. Consequently those named structures, in the stated model class, do not supply effectivity ([ACS](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/README.md), introduction and mechanisms 1–3).

## F06. Weil and integer-successor affine states are incompatible

**Source.** If a positive-definite function `φ` on `Aff(ℚ)` restricts on positive dilations to Weil's spline correlation, then `φ(translation b)` is one constant `α` for **every nonzero rational** `b`, with `0 ≤ α ≤ Re φ(1)`. This excludes a translation restriction `1_ℤ`, which distinguishes nonzero integers from nonintegral rationals.

Proof mechanism: existence of this extension implies RH; the resulting dilation correlation has a summable atomic archimedean spectrum; atomic spectral blindness forces constant nonzero-translation values. The conclusion is a conditional classification, not an independent construction of the positive extension. The full affine extension carries only one interval-valued parameter per spectral atom.

Stronger spectral statement: a positive affine state with integer successor has zero spectral mass on the entire archimedean Kronecker line. The proof uses rational ratios `(N+1+b)/(N+1+a)` tending to 1 in the real topology but with reduced numerator–denominator product growing quadratically. The Hecke bound forces their coefficients to zero; normalized finite Gram averages bound Kronecker-line mass by `φ(1)/M` for every `M`.

Declarations: `weil_successor_blind` ([source](../../../formal/GaloisForLFunctions/ArithmeticPositiveDuality/WeilsCorrelationCarriesNoSuccessor.lean)); `weil_extension_classification` ([source](../../../formal/GaloisForLFunctions/ArithmeticPositiveDuality/TheExtensionsOfWeilsCorrelationAreIndexedByTheZeros.lean)); `integer_successor_kronecker_null` ([source](../../../formal/GaloisForLFunctions/ArithmeticPositiveDuality/TheIntegerSuccessorForcesAKroneckerNullDilationSpectrum.lean)).
