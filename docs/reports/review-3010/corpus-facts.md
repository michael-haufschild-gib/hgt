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

**Source.** The raw prime-comb energy and cross-prime aggregate are both asymptotic to `4 exp(2r)` on a normalized smooth odd slow family. Its first-power charge divided by comb mass tends to zero. More generally this normalized charge tends to the original profile's autocorrelation at displacement 2, which is zero for support in `[-1,1]`. The normalized comb itself converges in square norm to translation by 2. Thus a sharp large norm does not imply a large adverse pairing with the original source.

Declarations: `tendsto_combCharge_rescaledTest_div_combMass_zero`, `exists_odd_smooth_family_sharp_comb_rate` in [ThePrimeCombIsATranslation.lean](../../../formal/GaloisForLFunctions/ArithmeticCompensationTheory/ThePrimeCombIsATranslation.lean). The fixed-profile resolvent description remains README-level evidence here.

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

## F14. Every fixed overlap is already positive on the full actual matrix

**Source.** For the tilted unit spline and every fixed `c > 0`, all eigenvalues of the complete Weil matrix eventually exceed a positive floor. The floor and starting horizon may depend on `c`. This covers every coefficient vector, not merely a selected packet. The proof combines actual conductor quasimodes, a complete defect reserve and a common positive conductor floor. It does not supply a horizon uniform in growing `c`.

Declarations: `tendsto_completeWeilMatrix_completedConductor_residual_norm`, `exists_tiltedUnitSpline_completeWeil_eigenvalue_floor`, `eventually_tiltedUnitSpline_weilQuad_atomicTest_nonneg` in [TheCompleteWeilFormIsPositiveAtEveryFixedOverlap.lean](../../../formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/TheCompleteWeilFormIsPositiveAtEveryFixedOverlap.lean).

## F15. Two gap readings select where one maximal gap does not

**Source.** Within the family of finite prime flips, the original gap at least `2 log 2` together with the dyadically toggled gap at least the untwisted dyadic-response gap holds exactly for the empty flip set. Proof: the first inequality excludes flipping 2; any remaining flip strictly decreases the second gap, whose secular root lies below the maximal plateau. The theorem concerns this specified family and two exact lower bounds.

Declarations: `finiteFlip_two_gap_selection` in [OneDyadicProbeSelectsTheFinitePrimeSource.lean](../../../formal/GaloisForLFunctions/ArithmeticCountingPositivity/OneDyadicProbeSelectsTheFinitePrimeSource.lean); `exists_maximal_flip_with_almost_unchanged_dyadic_gap` in [ConductorMassBoundsGapLossAndProbePrecision.lean](../../../formal/GaloisForLFunctions/ArithmeticCountingPositivity/ConductorMassBoundsGapLossAndProbePrecision.lean). The latter proof uses the conductor-mass perturbation bound and arbitrarily large primes: every fixed positive response tolerance admits a nontrivial maximal-gap flip.

## F16. Missing mass is classified on actual spectral sublevels

**Source.** For every prime pattern and every regular energy threshold, the entire actual bounded prime spectral sublevel has limiting squared constraint mass equal to the finite sum of its counted conductor masses. Distinct limiting energies give injectivity; exact eigenvalue counts show that the selected lines exhaust the sublevel. Euler density zero is equivalent to mass vanishing on **every** bounded energy window. This is stronger than vanishing on each selected line separately.

Declarations: `tendsto_primeSetBoundedSpectralMass`, `primeSet_bounded_spectral_mass_vanishes_iff` in [PrimeCountsDetermineEveryBoundedSpectralMass.lean](../../../formal/GaloisForLFunctions/ArithmeticCountingPositivity/PrimeCountsDetermineEveryBoundedSpectralMass.lean).

## F17. Nonlinear arithmetic readings recover depth-sensitive traces

**Source.** Prescribed finite theta prefixes recover the actual multiplicity-weighted collided metric and all normalized depth moments uniformly over tests with `sourceTestSize ≤ 1`, motion `|τ| ≤ n/2` and combined aperture `a+j|L| ≤ 2 log(n+1)`. After division by `4^j`, the error is bounded by `sourceTestSize² · [B/(n+1)² + O(log(n+4)/n)]`. The reading is positive. Its construction passes through regularized source curvature, Green testing and a summable divisor tail; no RH or zero-separation premise occurs in the capstone. This is approximation of a trace, not an upper bound for its depth defect.

Declarations: `exists_polynomialThetaSource_aperture_logarithmic_bound`, `polynomialThetaSource_uniform_test_aperture_moments` in [PolynomialThetaMetric.lean](../../../formal/GaloisForLFunctions/ConjugateDiagonalGeometry/PolynomialThetaMetric.lean).

## F18. Actual heat dynamics retain nonreal-count dissipation through collisions

**Source.** For admissible nonnegative unit-window cutoffs at large height `X`, and `0 ≤ a ≤ b ≤ 1/8` with `b log X ≤ 1`, actual localized vertical energy satisfies

`E_w(b) − E_w(a) + 2∫ₐᵇ N_w ≤ (2M+2V+4W) C log X · ∫ₐᵇ E_outer`.

Here `N_w` is the full multiplicity-weighted nonreal count. Continuous truncated counts and bounded convergence carry the estimate through collisions. A corresponding upper-right-slope bound holds at time zero as well. The right side is still a nearby energy flux, not a proved extinction estimate.

Declarations: `exists_uniform_heatLocalizedVerticalEnergy_evolution`, `exists_uniform_heatLocalizedVerticalEnergy_right_slope` in [HeatLocalizedEnergyDissipation.lean](../../../formal/GaloisForLFunctions/RHTower/Heat/HeatLocalizedEnergyDissipation.lean). Capstone proofs and the initial zero-velocity reduction were inspected; intermediate local drift estimates were not all reread.

## F19. A payment domain and its closure have different information

**Source.** At the critical single-prime coefficient model, payment is square summability of inclusive partial sums in `ℓ¹`. Its closure is only the zero-total-evaluation hyperplane. Every continuous functional annihilating the payment domain is a scalar multiple of total evaluation. Separately, for an actual source, its paid ideal is exactly the input image of its complete cofactor graph, with a unique square-summable output for each paid input. Thus the graph records output energy absent from the input's closure description.

Declarations: `criticalCoefficientDomain_topologicalClosure`, `criticalCoefficientDomain_continuous_annihilator` in [CriticalCoefficientDomain.lean](../../../formal/GaloisForLFunctions/BiarithmeticGeometry/CriticalCoefficientDomain.lean); `paidIdeal_iff_existsUnique_cofactorGraph` in [PaidGraphIdentification.lean](../../../formal/GaloisForLFunctions/BiarithmeticGeometry/PaidGraphIdentification.lean).

The graph input image is closed **iff** its output norm is uniformly bounded by its input norm: `isClosed_range_cofactorGraphInput_iff` in [CofactorGraphClosedness.lean](../../../formal/GaloisForLFunctions/BiarithmeticGeometry/CofactorGraphClosedness.lean). Choosing a closure cannot supply that bound.

## F20. Positive self-duality forces lattice support by saturation

**Source.** A locally finite positive measure with no mass in `(-1,1) \ {0}` is self-dual against integer translates of the tent exactly when it is a constant multiple of the integer Dirac comb. At the unshifted tent, the gap uses the entire available integral at the origin; the remaining nonnegative sinc-square integral is zero. Its zero set forces integer support. Translated identities then force equal atom masses. Both positivity and the exact identity concern the **same measure**.

Declaration: `tentSelfDual_iff_eq_smul_diracComb` in [PositiveSelfDualMeasuresWithAGapAreDiracCombs.lean](../../../formal/GaloisForLFunctions/ArithmeticPositiveDuality/PositiveSelfDualMeasuresWithAGapAreDiracCombs.lean).

## F21. Growing-overlap positivity has two separate restrictions

**Source.** Along `c_N = (log N)^α`, `0 < α < 1/40`, every **fixed finite** distinct conductor family is eventually positive for all its coefficients. Both residual and Gram discrepancy are paid relative to a vanishing conductor floor. The RH-equivalent full-space theorem instead permits `c_N = 2(log N)^α` with `α > 1/4`. Removing fixed-family dependence and improving the admissible growth range are separate missing steps in this comparison.

Declarations: `eventually_tiltedWeil_growing_packet_pos` in [WeilGrowingPackets.lean](../../../formal/GaloisForLFunctions/CompletedArithmeticForms/WeilGrowingPackets.lean); `riemannHypothesis_iff_tiltedUnitSpline_completeWeil_nonneg_log` in [LogarithmicOverlapOfTheCompleteWeilMatrixIsTheRiemannHypothesis.lean](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/LogarithmicOverlapOfTheCompleteWeilMatrixIsTheRiemannHypothesis.lean).

## F22. The exponent sixteen belongs to a particular signed-form estimate

**Source.** The actual complete form satisfies `W ≥ a c^(−7) D − C c^9 ‖x‖²` once `N ≥ H c^8`. Hence a unit vector with `W ≤ 0` has `D ≤ C' c^16`. The proof pays the non-ratio form and the pole moments separately in absolute value, each with a defect fraction proportional to `c^(−7)` and mass cost proportional to `c²` divided by that fraction. These are upper estimates, not a lower obstruction at exponent sixteen. F10 is the separate genuine obstruction to compressing **all** bounded-defect vectors.

Declarations: `tiltedUnitSpline_complete_defect_reserve_explicit`, `exists_negative_completeWeil_poleDefect_polynomial_bound` in [TheCompleteWeilReserveHasPolynomialOverlapCost.lean](../../../formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/TheCompleteWeilReserveHasPolynomialOverlapCost.lean).

## F23. Complete prefix inversion already has a uniform mixed cost

**Source.** For the plateau profile, beyond one prefix horizon, simultaneously for all ambient horizons and overlaps satisfying `c M ≤ N`, the actual prefix inverse obeys `0 ≤ bᵀA⁻¹b ≤ 20‖b‖²`. The complete Schur form is exactly `yᵀCy − (By)ᵀA⁻¹(By)` and lies between `yᵀCy − 20‖By‖²` and `yᵀCy`. Here `B` retains the complete prime, Gamma and polar mixed block. A separate tilted-spline theorem controls every inverse direction by finitely many conductor readings at fixed overlap; its finite family and horizon depend on overlap and tolerance.

Declarations: `eventually_plateauPrefix_inverse_quadratic_le`, `eventually_plateauPrefixSchur_quadratic_payment` in [WeilPrefixPayment.lean](../../../formal/GaloisForLFunctions/CompletedArithmeticForms/WeilPrefixPayment.lean); `exists_tiltedWeil_inverse_finite_reading_tail` in [WeilGreenTail.lean](../../../formal/GaloisForLFunctions/CompletedArithmeticForms/WeilGreenTail.lean).

## F24. A nonzero compatible carrier can annihilate its actual source

**Source.** Every finite simultaneous Sonin/Euler carrier is nonzero, but the complete cleared Euler source current vanishes on it. On the original Sonin carrier, the current's kernel is exactly an enlarged Fourier gap. The corresponding boundary quotient has a bounded spectral chart recovering the actual source's Fourier band; prime-insertion transitions become Fourier restrictions in these charts. Thus the compatible carrier alone omits source boundary data that the quotient chart retains.

Declarations: `ccmFiniteEulerSourceCurrent_sonin_kernel_iff`, `ccmEulerSimultaneousProjection_ne_zero`, `ccmFiniteEulerSourceCurrent_mul_simultaneousProjection` in [CCMEulerMovingCarrierRadical.lean](../../../formal/GaloisForLFunctions/RHTower/CCM/CCMEulerMovingCarrierRadical.lean); `ccmEulerBoundarySpectralEquiv_source`, `ccmEulerBoundaryTransition_spectral` in [CCMEulerBoundarySpectralChart.lean](../../../formal/GaloisForLFunctions/RHTower/CCM/CCMEulerBoundarySpectralChart.lean).

## F25. The receiver survives as a difference below the forcing scale

**Source.** For the actual Möbius source at fixed subcritical damping, receiver energy divided by inversion-forcing energy tends to zero. No common scalar normalization keeps forcing bounded and receiver uniformly nonzero. Nevertheless, the exact squared Gram distance between forcing and cofactor equals receiver energy; divided by receiver energy it is identically one at every positive horizon. The forcing-normalized Gram determinant tends to zero. The first ratio uses the actual source's zero-free-region estimate; the exact distance identity by itself gives no upper bound on receiver energy.

Declarations: `tendsto_receiver_div_forcingEnergy_zero`, `no_common_scalar_normalization` in [ForcingScaleSeparation.lean](../../../formal/GaloisForLFunctions/ArithmeticDefectRigidity/ForcingScaleSeparation.lean); `tendsto_forcingGramDefect_div_forcingEnergy_sq_zero`, `gram_distance_div_receiverEnergy_eq_one` in [TheReceiverIsTheGramTangent.lean](../../../formal/GaloisForLFunctions/ArithmeticDefectRigidity/TheReceiverIsTheGramTangent.lean).

Adding fixed covariance coordinates does not repair this automatically. After subtracting the forcing power, every escaping fixed signed Gram table is `sign(b) sign(c) K(j,k)`, with signs `(1,−1,0)` for receiver, residual and paid forcing. Its vectors already belong to the original cofactor Hilbert module: `ActualCofactorLimit.admits_or_signedCofactorGram_tendsto` in [TheSignedCofactorGramHasNoExtraCoordinates.lean](../../../formal/GaloisForLFunctions/ArithmeticDefectRigidity/TheSignedCofactorGramHasNoExtraCoordinates.lean).
