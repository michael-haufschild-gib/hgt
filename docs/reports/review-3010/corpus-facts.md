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

## F07. Counting precision and complete tower positivity impose different requirements

**Source.** At any prime tower, index zero for every compact smooth test is equivalent to RH **and exact equality of every coefficient** `λ(n) = Λ(n)` for `n ≥ 2`. In contrast, `Count(Λ + 1/n)` is equivalent to RH, although that perturbed source never has tower index zero. The counting endpoint tolerates the square-root class; complete tower positivity does not.

`deciding_input_necessary_properties` assumes a predicate implies `Count` for every source. Its conclusions exclude specified twins and perturbation stability. They do not classify every possible proof method. `errorLaw_cannot_decide` concerns arbitrary weights sharing an error law; exact arithmetic restrictions are additional information.

Sources: [TowerPositivityIsPrecisionExact.lean](../../../formal/GaloisForLFunctions/ArithmeticOfSquareRootPrecision/TowerPositivityIsPrecisionExact.lean), [TheDecidingInputTheorem.lean](../../../formal/GaloisForLFunctions/ArithmeticOfSquareRootPrecision/TheDecidingInputTheorem.lean).

## F08. Holomorphic rigidity has explicit quantifiers

**Source.** An entire weight calibrated to `|F(x)|²` at every real point is uniquely `F·F#`. A holomorphic linear carrier vanishing on every critical-line configuration also vanishes on the stipulated reflected configurations; the sesquilinear version requires separate holomorphy and universal critical-configuration vanishing. The approximate statement fixes positive boundary bounds and obtains a depth at which quartet response falls below a prescribed quantum. These statements do not quantify over arbitrary nonlinear source constructions or singular currents.

Sources: `eq_weilWeight_of_calibrated` in [TheExplicitImageIsTheWeilForm.lean](../../../formal/GaloisForLFunctions/HilbertianExplicitFormulas/TheExplicitImageIsTheWeilForm.lean); `linearCarrier_eq_zero`, `sesquilinearCarrier_eq_zero`, `exists_depth_without_quantum` in [HolomorphicCarriersCannotBeQuantized.lean](../../../formal/GaloisForLFunctions/RHTower/HolomorphicCarriersCannotBeQuantized.lean).

## F09. Shell cancellation gives a positive coprimality formula

**Source.** For a nonzero real `C²` profile supported in `[0,1]`, positive overlap `c` and conductor `m`, the shell-completed energy is a sum of nonnegative Fourier tails over positive integers coprime to `m`. The proof interchanges a finite divisor sum with convergent one-conductor tails; Möbius cancellation becomes the coprimality indicator. This proves nonnegativity for every conductor and overlap. For each fixed conductor, the energy tends to zero as overlap tends to infinity. Realization on actual finite Weil matrices is a separate assertion.

Declarations: `hasSum_completedConductorEnergy`, `completedConductorEnergy_nonneg`, `tendsto_completedConductorEnergy_atTop` in [TheShellsRepayEveryConductor.lean](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheShellsRepayEveryConductor.lean).

## F10. Defect-only confinement really requires exponentially large conductors

**Source.** Unit-normalized actual Ramanujan horizon vectors converge to orthogonal conductor coordinates and have limiting prime energy `γ + log m + tameDifferent(m)`. At `m = 2^k` this is exactly `γ + (k+1) log 2`. A row estimate bounds their pole defect by this energy plus `log 4 + 4 + ε`. Consequently any fixed conductor cutoff below `2^k` misses unit vectors of defect only linear in `k`. The obstruction concerns **all bounded-defect vectors**, not just negative directions of the complete signed form.

Declarations: `eventually_exists_unit_vector_escaping_conductors`, `ramanujanAdjunctionEnergy_two_pow`, `not_eventually_defect_coordinate_capture_below_binary_cutoff` in [PrimeDefectConfinementMustRetainLowEnergyConductors.lean](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/PrimeDefectConfinementMustRetainLowEnergyConductors.lean).

## F11. Exact nonlinear coordinates need not preserve the required positive cone

**Source.** For the first theta atom, the invertible clock `u = arsinh(t/√q)` changes the reflected pair exactly into `C exp(−4t²)(B−24t²)`. Its signed moments are an adjacent-Gamma mixture. At every nonnegative source center, all clocked signed Hankel heads are positive definite, while some physical signed head fails positive semidefiniteness at that same center. Exact recovery of the source by inverse substitution therefore supplies no positivity transport by itself.

Declarations: `firstAtomGaussianClockProfile_eq`, `firstAtomGaussianClockProfile_pullback`, `firstAtomGaussianClock_positive_pullback_fails` in [HyperbolicClock.lean](../../../formal/GaloisForLFunctions/CompletedArithmeticForms/HyperbolicClock.lean).

## F12. A congruence preserves complete mixed-rank error

**Source.** The monic Hermite change of coordinates is surjective and transports the entire quadratic comparison with the Gaussian head. Gaussian contraction pays the first atom; a weighted entry estimate pays the infinite theta remainder with a linear dimension cost. The resulting bound for the **literal complete native** moment matrix is `|vᵀ(H−G)v| ≤ C(N)/q · vᵀGv`, with quadratic rank numerator, provided `q ≥ 16(N+2)²`. This includes every signed coefficient direction. Its scale condition grows with rank.

Declarations: `relativeFormError_of_hermiteCongruence`, `nativeHermiteTail_relative_error_le`, `nativeBalancedFullHead_quadratic_rank_error_le` in [NativeQuadraticRank.lean](../../../formal/GaloisForLFunctions/CompletedArithmeticForms/NativeQuadraticRank.lean).

## F13. Combining sources can create an exact positive reserve

**Source.** When both preceding Hankel heads are positive definite, the successor Schur complement of their sum equals the sum of their successor complements **plus** a nonnegative variance. This variance measures disagreement of their minimizing coefficient vectors in their respective head norms. It vanishes exactly when the minimizers coincide. Positivity of the preceding heads is essential to the stated theorem; it is not an all-rank theta positivity proof.

Declarations: `successorSchur_add_eq`, `successorMixtureVariance_nonneg`, `successorMixtureVariance_eq_zero_iff` in [SuccessorMixture.lean](../../../formal/GaloisForLFunctions/CompletedArithmeticForms/SuccessorMixture.lean).
