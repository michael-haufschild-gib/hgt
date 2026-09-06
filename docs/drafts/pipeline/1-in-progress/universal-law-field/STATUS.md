# Universal-law corpus facts

Updated: 2026-09-06

Scope: compressed facts and logically forced design constraints extracted from audited positive theorems, negative no-gos, frontier branches, and RH endpoints. No active conjectures or work log.

## RH: route-independent research constraints

- **Must exclude even one off-line zero.** A density estimate allowing a sparse exceptional set, however small, is not yet RH. The missing step is elimination of the exceptions, not another interpretation of the proportion.
- **Must prove that a classification covers every zero.** Different classes may have different proofs of critical-line membership. The classes need independent definitions, exhaustive coverage, and a proved line conclusion for each class. A partition of primes or of arithmetic coefficients does not itself partition the zeros; any such connection requires proof, including the terms involving several groups. A class-specific contradiction at hypothetical off-line zeros remains a legitimate target.
- **Cannot obtain selection from reflection alone.** Reflection pairs opposite horizontal displacements; it does not identify each zero with its reflected partner. Symmetry-compatible countermodels still have off-line zeros. Evidence: F06, F14.
- **Must retain the information the conclusion needs.** A transformation that forgets real parts, multiplicities, or signs must recover them by a proved identity before it can constrain those data. A self-adjoint operator listing zero ordinates does not locate the original complex zeros. Evidence: F10, F13, F664.
- **Cannot bound the raw even theta moments by one geometric sequence.** For the positive theta density representing Xi, `m_n=2∫₀∞x^(2n)Φ(x)dx` has `m_(n+1)/m_n→∞`. Every distant interval contributes a positive lower bound with arbitrarily large geometric base. A model with bounded moment ratios therefore needs a proved transformation before its moments can represent these raw source moments. Evidence: `RHTower.tendsto_thetaCuspRawEvenMoment_ratio_atTop` in `ThetaRawGramGrowthObstruction`.
- **Must derive the decisive property for the fixed arithmetic object.** Positivity, boundedness, recurrence, or regularity taken as an RH-equivalent input is an endpoint, not a source proof. Fitting a new positive model separately to each hypothetical zero does not exclude any zero. Evidence: F01, F04, F19.
- **Cannot spend positivity as an upper bound.** A positive quadratic form can be arbitrarily large. An energy argument needs an independently proved arithmetic ceiling and must account for signed cross terms and any energy moved into an unobserved component. Evidence: HARD LOCK P, F15.
- **Cannot bound a second moment from positive mass and a fixed first moment alone.** Even probability measures supported on `[3,infinity)` with fixed mean `16/5` have arbitrarily large second moments. Any source argument that needs such a bound must retain additional information. Evidence: the unconditional real-parameter two-atom theorem `RHTower.c5MomentEscape_exists_fixedMean_unboundedSecond` in `ThetaCuspC5SpectralMomentTransport`. This is a precise insufficiency result, not a prohibition on positivity in an RH proof.
- **Must justify the actual limiting operation.** Control at each fixed cutoff need not control a cutoff moving with the zero, height, or deformation. A proof using such a limit must control that joint dependence and the retained tail. Evidence: F08, F11, F17.
- **Must retain the exceptional initial terms after proving a uniform tail sign.** A sign proved for every index `n` with `n²≥t³` leaves the earlier indices uncontrolled at height `t`. In particular, for `t>1` it gives no sign at `n=1`; reconstructing that unit term from a convergent arithmetic family does not remove the missing comparison. The literal normalized power-sum remainder now has exactly such an unconditional negative-tail bound throughout `0<Re(s)≤1`, `t=Im(s)≥1`. Evidence: `normalizedWeightedRemainder_im_neg_of_height_cube` in `RHTower.ArithmeticRemainderPhaseCutoff`; its unit reconstruction is `normalizedWeightedRemainder_one_eq_boundary` in `ArithmeticPrimeSievePhase`.
- **Cannot discard infinite-dimensional charge using finite-dimensional cyclicity.** The trace of a commutator can be nonzero when only the commutator, not its separate products, is trace class. Every trace rearrangement needs its own ideal hypotheses. For the specific cubic `(R-P)^3-(R-Q)^3-(Q-P)^3` of orthogonal projections, a complete eigenbasis of `P+Q+R` forces zero trace; this does not settle the remaining spectral sector. Evidence: `CubicAggregateSpectralCurrent.opTrace_cubicAssociator_eq_zero_of_aggregate_eigenbasis` (declaration namespace `RHTower`).
- **Must account for boundary charge after compression.** For three source projections `A,B,C`, put `S=A+B+C` and `K=[A,B]+[B,C]+[C,A]`. Under trace-class commutators with an orthogonal cutoff `E`, source commutation `[S,K]=0` allows genuine rounded compressed projections whose combined cubic is trace class and satisfies `2 Tr(cubic)=Tr(S[E,K])`. A zero-charge argument of this form must annihilate the boundary pairing; establishing source commutation supplies admission, not that final vanishing step. Evidence: `RHTower.exists_rounded_cubic_with_boundary_trace` in `CubicBoundaryChargeTransport`.
- **Cannot rule out ordinary cubic charge from trace-class admission alone.** There exist three genuine orthogonal projections with trace-class `C=(R-P)^3-(R-Q)^3-(Q-P)^3` and `Tr C=3√3/(2π)≠0`, obtained from smooth matrix-valued Hardy sources. Cancellation proved for commuting projections, separately admitted products, or a complete aggregate eigenbasis cannot exclude this noncommuting infinite-dimensional mechanism. A proof using it must still derive the required charge and its arithmetic identification; the example alone does not locate zeta zeros. Evidence: `RHTower.exists_projections_with_nonzero_cubic_trace` and `RHTower.not_cubic_trace_conservation_of_combined_nuclearity` in `CubicBoundaryNonzeroCharge`.
- **Cannot infer universal charge normalization from the smallest carrier.** Three-column flat projection sources have planar area curvature; the two-channel spectral relation already fails for rational-entry three-dimensional projections. Evidence: `cyclicSource_trace_curvature`, `cyclicFlatCounterProjection_casimir` and `cyclicFlatCounterProjection_current_ne_zero` in `RHTower.CubicCirculantSourceCurrent`.
- **Must distinguish faithful charge realization from arithmetic selection.** One fixed construction, applied to literal completed zeta along a smooth rectangle, retains its values before compression and gives genuine orthogonal projections with ordinary cubic trace exactly the enclosed zero count, including multiplicity. Neither the count nor a selected zero enters the source definition. This realizes the arithmetic charge; it does not force that charge to vanish around off-critical zeros. Recovery is pointwise, not a bounded inverse after compression. Evidence: `RHTower.exists_faithful_arithmetic_rectangle_cubic` in `CubicArithmeticRectangleSource`.
- **Must keep impossibility claims within their proved premises.** Failure of one positive, linear, continuous, or spectral construction does not forbid all such RH proofs. No theorem here requires every solution to be nonlinear, singular, nonclassical, or absent from literature.
- **Must control approximation error after summing over the full spectrum.** Fixed polynomial probes can each have finite trace while their traces increase to infinite root mass. For nonnegative roots at most one, the proved finite-prefix error is `2K/(n+2)` and the remaining tail is charged by `n/2` times square energy. Approximate moment matching also pays the absolute coefficients of the chosen polynomial; small errors at each fixed degree alone do not bound that growing weighted error. Evidence: `finite_rootPrefix_le_certificate_add_resolution`, `certificate_le_rootPrefix_add_energyTail`, and `rootMomentCertificate_le_rootBudget_add_error` in `GaloisForLFunctions.HTGeometry.PolynomialRootBudget`. This is an approximation constraint, not an arithmetic positivity theorem.

- **Must distinguish strict test positivity from a uniform positive floor.** At a first zero of the constrained ground energy, if such an aperture exists, every nonzero smooth interior test is strictly positive, while its normalized energies approach zero and the completed space contains a nonzero null vector. Smooth density does not make that null vector a smooth test, and invertibility of a differential test parametrization does not supply a uniform bound. This is a proved conditional boundary description, not evidence that such an aperture exists. Evidence: `RHTower.polarMultiplier_firstZero_no_uniform_positive_floor` and `RHTower.riemannHypothesis_or_polar_firstZero_core_boundary` in `CCMRestrictedWeilPolarMultiplierCriterion`.

- **Must rule out the unique possible transition to negative Weil energy.** For tests whose two exponential moments vanish, the least normalized Weil energy strictly decreases as their allowed support interval grows. The proved alternatives are a positive floor at every finite radius, equivalent to RH, or exactly one zero radius with positive floors below and negative floors above. This classification does not select its positive branch. Evidence: `RHTower.strictAnti_ccmRestrictedWeilPolarGroundEnergy`, `RHTower.riemannHypothesis_iff_polarGroundEnergy_pos`, and `RHTower.riemannHypothesis_or_unique_polarGroundZero` in `CCMRestrictedWeilPolarStrictDomain`.

- **Must determine constraint forces from the actual source.** A minimum taken over tests with two vanishing exponential moments satisfies the full Weil operator equation with two uniquely determined pole-forcing terms. Reflection reduces them to one even or odd profile. Its scalar is exactly the boundary–arithmetic source moment divided by a strictly positive pole Gram entry. This determination retains actual operator-domain membership; it does not set the scalar to zero or select the ground's source moment. Evidence: `RHTower.polarSingleForcing_coefficient_eq_source_div` and `RHTower.exists_polarGround_boundarySource_forcing` in `CCMRestrictedWeilPolarGroundSourceMoment`.

- **Cannot discard constraint forcing through invariance or parity.** At every finite positive support radius, the actual Weil operator sends an exponential pole profile outside the entire span of the two pole profiles. The surviving source moment takes every complex value separately on even and odd functions with both exponential moments zero. On their sum, the original and reflected source moments can be prescribed independently. Endpoint divergence establishes this despite the exact arithmetic cancellations. A comparison based on these constrained moments must use the selected ground's additional variational properties; parity alone supplies neither zero coupling nor a universal linear sign. Evidence: `RHTower.ccmRestrictedWeilOperator_polarPlus_ne_forcing` in `CCMRestrictedWeilPolarSourceNonvanishing`; `RHTower.exists_polarParity_boundarySource_eq` and `RHTower.polarConstrained_jointBoundarySource_surjective` in `CCMRestrictedWeilPolarParitySourceCoupling`.

- **Cannot exclude zero constrained energy from a nonzero constraint force alone.** A minimizing test with vanishing exponential moments has an exact full-operator residual whose squared size is the source moment squared divided by a positive Gram factor. Its variational bound compares that force with the gap to the unrestricted minimum and the full shifted pole energy. Nonzero forcing requires a strictly lower unrestricted minimum; it does not force the constrained minimum positive. A proved Hermitian two-coordinate example has zero constrained minimum and nonzero forcing while satisfying the shifted positivity bound. An RH argument using this comparison must supply additional arithmetic control. Evidence: `RHTower.polarSingleForcing_residual_norm_sq`, `RHTower.polarGround_source_gap_bound`, and `RHTower.zeroGround_nonzeroSource_shiftedPositive_model` in `CCMRestrictedWeilPolarGroundVariance`.

- **Must control the integrated prime-counting error at square-root scale.** Let `psi(X)` sum `log p` over prime powers `p^k≤X`. RH is exactly the existence of a finite constant `K≥0` such that `|integral_0^T [exp(t)-psi(exp(t))]dt|≤K exp(T/2)` for every `T≥0`. No additional logarithmic factor is required for this primitive. Absolutely continuous integration by parts transfers this bound to a bounded completed Chebyshev resolvent and its actual zeta continuation. Evidence: `RHTower.riemannHypothesis_iff_logChebyshevDeficitPrimitive_bound` and `RHTower.unitRieszChebyshevRayIntegral_eq_deficitPrimitive` in `CCMRestrictedWeilPoleCompressionRHCriterion`.

- **Must retain mixed arithmetic correlations when testing positivity.** A compactly supported exponential and its reflection have equal full Weil self energies `A`, but positivity of every complex combination requires the separate comparison `|C|≤A` for their cross energy `C`. That cross energy contains the integral of the difference between exponential growth and the actual weighted prime-power counting function. Its reciprocal-prime correction is bounded linearly in support radius, its Gamma boundary mass is uniformly bounded, and its diagonal has a uniform exponential bound. The all-radius comparison `|C|≤A` is exactly RH; separate diagonal estimates leave this mixed arithmetic sign to prove. Evidence: `RHTower.ccmWeilPoleCompression_nonneg_iff`, `RHTower.ccmWeilPoleCross_eq_integratedError`, and `RHTower.abs_integratedChebyshevDeficit_sub_weilPoleCross_le` in `CCMRestrictedWeilPoleCompression` and `CCMRestrictedWeilPoleIntegratedPrimeError`.
- **Cannot propagate positivity from the signs of newly entering prime terms.** In the actual test `1_[-a,a](exp(x/2)-exp(-x/2))`, every fixed prime power contributes positively at one support radius and negatively at a larger radius. Positive arithmetic weights do not prevent this reversal. An all-radius comparison must retain older losses, recent gains, and the full Gamma and pole terms. Evidence: `ccmOddPole_primePower_contribution_changes_sign` and `ccmWeilOddPole_eq_prime_budgets` in `CCMRestrictedWeilOddPrimeBudget`. The replacement must compare the full moving energy: above radius two, nonnegative endpoints force strictly positive interior values across any gap containing no prime-power entry. New atoms vanish at entry and zero-Mangoldt integers have no effect. All odd energies on a tail are nonnegative exactly when the starting energy and every later genuine prime-power entry energy are nonnegative; any negative tail value forces a negative value in that set. Those signs still require arithmetic control (`ccmWeilOddPole_nonneg_tail_iff_primePower_entries`, `ccmWeilOddPole_negative_tail_iff_primePower_entry`).

- **Must distinguish parity in the response to a new prime term.** For the actual exponential-cutoff odd and even tests, the new prime-power energy corrections both vanish at entry `b=log(n)/2`. Their slopes are respectively `4Lambda(n)(1-exp(-b))²>0` and `-4Lambda(n)(1+exp(-b))²<0`. These exact entry responses have opposite signs, while each older odd contribution can later reverse its sign. Evidence: `hasDerivAt_ccmWeilOddPole_entry_atom`, `hasDerivAt_ccmWeilEvenPole_entry_atom`, and the strict-sign classifications in `CCMRestrictedWeilPoleEntrySlopes`.

- **Must retain the loss accumulated after a prime term enters.** In both actual exponential-cutoff parity tests, a prime-power contribution equals its entry slope times elapsed aperture minus the same strictly positive later loss. The loss is proportional to `sinh(t)-t=integral_0^t sinh(t-u)u du`. Summing entry tangents alone therefore overestimates both complete energies; it cannot serve as a lower bound for positivity. The exact source balance retains this common loss and both Gamma–polar terms (`ccmWeilOddPole_eq_entry_age_balance`, `ccmWeilEvenPole_eq_entry_age_balance`).

- **Must distinguish endpoint control from minimum control in opposite parity.** Beyond a fixed explicit support radius, the full odd exponential-test energy is strictly concave and the even energy strictly convex between consecutive prime-power entries. The even energy has one unique actual minimum on each closed gap, possibly at a boundary; its sign decides the whole gap, and an interior minimum is stationary. These shape laws provide no minimum-value sign (`ccmWeilPole_primePower_gap_strict_shape`, `exists_unique_ccmWeilEvenPole_gap_minimum`).

- **Must distinguish locating an extremum from proving its value nonnegative.** For the actual compact exponential even tests of RH, stationarity at support radius `a≥2` forces `|X-psi(X)|≤K sqrt(X)` at `X=exp(2a)`, for one explicit constant; `psi` is the weighted prime-power counting function. This includes interior minima between consecutive prime-power entries. Their energy still retains a weighted logarithmic prime sum and needs a separate lower comparison. The location estimate neither gives its sign nor bounds prime error at arbitrary radii (`abs_prime_error_le_at_ccmWeilEvenPole_gap_minimum`, `ccmWeilEvenPole_nonneg_iff_logMoment`).

- **Cannot recover every arithmetic value from positive weights and two mass totals.** On the prime powers 2,3,4, all nonnegative weights with sum six and reciprocal-weighted sum two are `(2t,6(1-t),4t)`, `0≤t≤1`. Their weighted logarithmic moment ranges from `8log 3` to `13log 2`, despite identical mass data and identical derivatives of the associated cross response. The actual RH test must retain this additional moment or prove a comparison controlling it. These auxiliary weights are not the literal Mangoldt coefficients (`ccmWeilThreeAtom_mass_classification`, `ccmWeilThreeAtomCross_range_iff`).


- **Cannot assign a fixed sign to an individual prime contribution from the two pole constraints.** Even with `∫exp(x/2)f(x)dx=∫exp(-x/2)f(x)dx=0`, nonzero form-domain tests realize both signs of an outer-shell prime translation. Its optimal contraction constant is exactly one after removing the prime weight; no smaller constant follows from those constraints alone. The resulting literal prime norm bound is `21(exp(a)+exp(a/2))`, but combined arithmetic–Gamma positivity remains a separate obligation. Evidence: `RHTower.exists_polarConstrained_outerShell_eigenvectors`, `RHTower.polarConstrained_outerShell_bound_iff`, and `RHTower.norm_ccmFinitePrimeOperator_le_twoScaleExp` in `CCMRestrictedWeilPrimeOuterShell`.

- **Must test compatibility before combining sharp estimates.** For two distinct prime shifts lying between the radius and diameter of a bounded support interval, a nonzero test with both exponential moments zero can preserve both individual norms. Yet every positive weighted sum of those restricted shifts has norm strictly below the sum of the separate bounds: their output directions cannot align at the maxima. Repeated products move support out of the interval and give an explicit quantitative gap. Evidence: `RHTower.exists_polarConstrained_common_outerShift_norm`, `RHTower.ccmOuterShiftPair_opNorm_sq_bound`, and `RHTower.ccmOuterShiftPair_norm_lt_sum` in `CCMRestrictedWeilPrimeInterference`.

- **Must combine the exact arithmetic and boundary terms before estimating constraint forces.** In the full Weil action on an exponential profile restricted to a finite interval, the radius, spatial ramp, and exponential main contributions cancel exactly. Pairing against a function with both exponential moments zero leaves only the logarithmic boundary term minus the genuine Chebyshev and reciprocal-prime errors. The reciprocal-prime error is uniformly bounded, but neither that bound nor positivity of the boundary term determines the pairing against a sign-changing function. Evidence: `RHTower.ccmRestrictedWeilOperator_polarPlus_coeFn` and `RHTower.inner_polarWeil_on_constrained_eq_boundaryArithmetic_integral` in `CCMRestrictedWeilPolarSourceCancellation`; `RHTower.abs_ccmReciprocalMangoldtError_le` in `CCMRestrictedWeilPrimePolarArithmeticAction`.

- **Must retain boundary contributions created by restricting support.** Applying the actual Gamma operator to an exponential profile cut off at two endpoints produces a linear bulk term, a fixed constant, and two strictly positive logarithmic boundary tails. The complete integral is evaluated through an integrable core. Its equality to the physical operator is proved by absolute integrability against compact interior tests, Fubini, and smooth-test separation of locally integrable coefficients. Existing operator-domain membership supplies the global L² representative; no extra endpoint regularity is required. Evidence: `RHTower.ccmPolarGammaImage_coeFn` in `CCMRestrictedWeilGammaPolarAction`, supported by `CCMRestrictedWeilGammaMixedJump` and `CCMRestrictedWeilGammaPolarAbsoluteBound`.

- **Cannot reject a Weil test solely because its cutoff has a jump.** Every real exponential restricted to a finite interval belongs to the actual unrestricted Weil operator domain. Its Fourier transform retains both endpoint terms, yet multiplication by the exact Gamma weight still gives an L² function. The full operator value is proved by representing its complete form pairing and adding the literal prime and pole terms; boundary discontinuity alone is therefore no domain obstruction. Evidence: `RHTower.memLp_ccmFormWeight_mul_fourier_polarVector` in `CCMRestrictedWeilPolarFourierRegularity`, and `RHTower.ccmPolarApertureVector_mem_weilOperator_domain`, `RHTower.ccmRestrictedWeilOperator_polar_apply` in `CCMRestrictedWeilPolarOperatorDomain`.

- **Cannot judge an omitted arithmetic tail solely by its small mass before an oscillatory transform.** For the actual theta density `Phi` defining completed zeta, let `P_N` contain its first `N≥1` integer shells and write `C_f(t)=integral_0^infinity f(x)cos(tx)dx`. Lean proves `t² C_(P_N)(t)→−P_N'(0)<0` and `t² C_(Phi−P_N)(t)→P_N'(0)>0`, while `t² C_(Phi)(t)→0`. Thus the infinite tail supplies the entire opposite leading term at every fixed cutoff. This is a constraint on source approximation, not a proof of Hankel positivity or of RH. Evidence: `tendsto_thetaFiniteShellCosine_mul_sq`, `tendsto_thetaFullCosine_mul_sq_zero`, and `tendsto_thetaShellRemainderCosine_mul_sq` in `RHTower.ThetaFiniteShellFourierBoundary`.

## Hard facts

F01 — Receiver abundance. Corpus has many exact RH equivalences: positivity, flatness, finite action, recurrence descent, formation properness, source-dagger descent, boundary absence. They are readouts, not independent evidence or producers.

HARD LOCK P — Positivity alone does not supply the missing arithmetic inequality. All-test Weil positivity is RH-equivalent; generic finite Gram/CP/KMS constructions are nonselective; the stated positive Green--Stokes split exceeds its Euler budget. These no-gos retain their exact premises. An independently proved quantitative bound for the literal arithmetic source remains a possible producer: being positive, quadratic, or contractive is not itself a mathematical disqualification. In particular, Gamma--Hankel PSD supplies a lower covariance floor, not the missing upper ceiling (`MobiusLaplaceGammaHankelWall`: `finiteMobiusGammaHankelOffDiagonalCovariance_lower_floor`).

F02 — Finite local exactness is nonselective. Arbitrary finite packets, jets, multiplicities, indices, Grams, KMS systems, homology, determinants, and recoveries coexist with off-line charge.

F03 — Must distinguish identities between functions from relations at one point. Differential independence excludes nonzero polynomial identities in the functions and their derivatives over the stated coefficient field; it does not exclude a common zero. For a finite family analytic at `a` and differentially independent over a coefficient field containing `C(s)`, multiplying every function by `s-a` preserves that independence and makes every value at `a` zero. Thus independence of arithmetic function families cannot by itself retire a proposed relation forced only at a zeta zero. The finite-family gauge law is Lean-proved as `HTGeometry.differentialIndependent_mulBase_iff`; an actual zeta-dilation application is `AdjacentDilation.adjacentDilationGauge_differentialIndependent_over_zeta`. Any proposed relation at a zero still needs its own arithmetic proof.

F04 — Source/receiver firewall. A construction can land exactly on Xi data while its final continuity, sign, descent, properness, or bound is still literally RH.

F05 — Large fused subcorpus has one signed current `a(s) = 2 Re(s) - 1`, with functional-equation reflection sending `a` to `-a`.

Gamma-six residue, Möbius prime-normal growth, Green codiagonal, Wold/Fisher response, affine Xi
residue, and several Hellinger/Kakutani readers recover `a`, `a²`, or its support.

F06 — Functional equation transports; it does not select. Common recovery lifts FE without information or formation-capital loss. FE-symmetric entire positive countermodels can have off-line zeros.

F07 — Faithful recovery conserves obstruction. Split/injective recovery preserves information, Hellinger affinity, formation capital, and completion boundary. Strict improvement requires erasure.

F07a — Cannot count copied labels as independently formed data. Diagonal copying preserves every coordinate marginal but equals the independent `d`-fold product (`d>=2`) only for a Dirac packet, even for normalized signed real weights. For two finite probability packets, one common stochastic map produces both independent products iff the packets are identical or have disjoint supports (`finiteDiagonalPower_marginal`, `finiteDiagonalPower_eq_independentPower_iff_dirac`, `finiteFormationClone_exists_iff`, Lean). Matching marginals or faithful split recovery does not supply that common replicator; an arithmetic cloning argument must construct it rather than assume it.

F08 — Formation and completion do not commute. Off-line current appears as completion boundary, Roos `lim¹`, and physical transport. Boundary absence is RH-equivalent; finite formation never sees class.

F09 — Bounded presentation changes are genuine gauges. Mutually bounded dictionaries preserve saturation and completion boundary. Ordinary naturality across bounded gauges cannot kill off-line class.

F10 — Quotients erase typed data differently. Positive squares erase sign/phase; reduced quotients erase nilpotent tangents; scalar fusion erases homology; compact observation erases lifted history.

F10a — Must distinguish global phase choice from relative-phase information. On an infinite locally finite connected graph, Boolean edge coherences modulo finite defects determine vertex phases modulo finite changes and one global flip iff every finite-edge-boundary cut has a finite side; products of two infinite connected graphs satisfy this condition (`CoherenceTailQuotient.coherenceTailMap_injective_iff_finiteBoundaryOneEnded`, `CoherenceEndReconstruction.finiteBoundaryOneEnded_boxProd`; declaration namespace `HTGeometry`). Finite-boundary cuts modulo finite sets are exactly the clopen end-space ring, preserving symmetric-difference addition and intersection multiplication (`CoherenceEndClopen.finiteBoundaryBooleanRingQuotientEquivClopens`). These are topology/reconstruction laws, not an identification with arithmetic sum/product or an RH selector.

F11 — Observer recurrence and source return differ. Compact observer can recur while source lift escapes linearly. Faithful recurrence descent is an RH receiver.

F12 — Hypertranscendence supplies independent directions and noncompactness, not vanishing. Unbounded rank/depth is necessary for several completion births and insufficient for selection.

F13 — Provenance and multiplicity survive only in typed landings. Prime labels, valuation depth, Xi multiplicity, reflection orientation, and ancestry cannot be replaced by total mass or norm.

F14 — External polarization can retain what internal multiplication erases. Reflected pairing cancels signed current and doubles unsigned escape; higher arity alone does not select.

F15 — Escape is conserved as capacity in proved models. Visible cancellation moves exact energy to hidden ports. Any proposed annihilation needs a closed accounting identity.

F16 — Quantization detects; it does not prohibit. Integer, rank, and `π`-scaled residues encode multiplicity but do not imply absence.

F16a — Must distinguish arbitrary finite depth from a finite source cutoff. For a holomorphic function nonzero somewhere on a connected open domain, existence of a holomorphic `2^k`-th root on that entire domain for every `k` already forces nonvanishing: a positive finite zero order cannot be divisible by every `2^k`. No compatibility between roots or limiting estimate is needed; on a simply connected domain a coherent tower follows. The unproved arithmetic input would be the global finite-depth roots, not their coherence (`RHTower.CoherentTower.nonvanishing_of_exists_roots_all_two_powers_preconnected`, `coherentTower_iff_exists_roots_all_two_powers_preconnected`; declaration namespace `RHTower`).

F16b — Cannot infer integral vanishing from all modular observations without excluding invisible divisible components. Adjoining a nonzero rational vector space to an abelian group preserves its mod-`m` quotient data and torsion subgroup, and every homomorphism to a direct sum of finite groups kills that added space. Finite generation supplies additional information: non-torsion then gives a surjective map to the integers (`HTGeometry.DivisibilityFirewall.divisibility_firewall`, `exists_int_surjection_of_not_isTorsion`; declaration namespace `HTGeometry`).

F16c — Must derive invertibility on the actual obstruction space when using finite phase transport to force integer vanishing; a phase relation alone is insufficient. On a coefficient space of positive dimension `d`, a clock with entries `1,z,…,z^(d−1)` and a shift with closing-edge weight `h` obey `CS=zSC` exactly when `h=0` or `z^d=1`. The zero-edge shift always works but is singular. For a primitive `2^k`-th root, an invertible pair exists exactly when `2^k` divides `d`; the converse constructs that pair without further source information. For the corpus's actual off-critical zero-multiplicity spaces, existence at cofinally many depths is exactly RH. This does not prohibit an arithmetic construction of invertible transport; it identifies what that construction must prove. Evidence: `dyadicBoundaryCompletedJetWeyl_iff_zero_or_dvd`, `boundaryCompletedJetShift_zero_det`, `semDyadicWeylModel_nonempty_iff_pow_dvd_holeCount`, `riemannHypothesis_iff_cofinal_semDyadicWeylModels` (namespace `RHTower`, Lean).

F17 — Cofinal order is law data. Fixed cutoffs, convergent scalar prefixes, compact subsequences, and local positivity do not control moving heads, apertures, domains, or retained infinite tails.

F18 — No-go survivors are systematic: completion boundary, connecting rank, nilpotent tangent, signed orientation, hidden capacity, quantized residue, unbounded domain, or singular comparison. Calling all of them curvature loses information.

F19 — Adaptive laws absorb displacement. Every horizontal grade admits fitted covariant/positive systems. Only descent to one fixed law detects neutrality; that descent is usually RH-equivalent.

F20 — Algebraic relation and executed relation differ. Additive source cancellation can acquire an exact nonlinear character, determinant, square, or completion defect.

F20a — Must distinguish forcing a shape from selecting its calibration. For any real normed vector space `E`, the maps `F : ℕ → E` obeying `F(mn)=m•F(n)+n•F(m)` and one uniform bound `‖F(m+n)−F(m)−F(n)‖≤C(m+n)` are exactly `F(n)=n log(n)•v`, with arbitrary `v∈E`. No completeness or finite dimension is required. These precise addition/product laws remove independent prime-by-prime choices but leave the calibration vector, including complex phase, unrestricted; they supply neither an arithmetic bound nor RH. Evidence: `HTGeometry.controlledArithmeticLeibniz_iff_logModel` in `ArithmeticControlledLeibniz`.

F20b — Must distinguish an allowed tangent from a controlled nonlinear lift. If `f(mn)=m•f(n)+n•f(m)` and `g(mn)=m•g(n)+n•g(m)+B(f(m),f(n))` for a real bilinear `B` between normed spaces, the discrepancy between multiplication and repeated addition obeys exactly `q^(-k)•[g(m q^k)−m•g(q^k)]=g(m)+(k/q)•B(f(m),f(q))` for every positive integer `q`. The unnormalized discrepancy is the finite sum of the individual additive carries; its normalized increment reconstructs the entire bilinear interaction. For each fixed `(m,q)`, bounded returns at arbitrarily large `k` are equivalent to zero interaction; bounds and return schedules may depend on that pair. Thus a uniform linear additive-defect bound suffices, but is not required. Zero interactions admit `g=0`; with multiplication in a reduced real normed algebra, all-pair returns force `f=0`. No integrality, completeness, finite dimension, or bound on `f` is needed. These laws do not construct a Xi-linked deformation or prove its returns. Evidence: `arithmetic_second_order_primitive_iff` in `ArithmeticSecondOrderObstruction`; `arithmeticPowerResponse_eq_affine`, `arithmeticInteraction_eq_response_increment`, `arithmeticSecondOrder_cofinalReturns_iff_tangent_zero` in `ArithmeticInteractionScaleLaw` (namespace `HTGeometry`, Lean).

F20c — Must test exact deformation beyond first order. In any reduced real normed algebra, a multiplicative formal family `P(n,T)` with constant coefficient `n` is identically `n` if each positive even coefficient has an additive defect bounded by `C_k(m+n)`; constants may depend on order, and no convergence in `T` is assumed. The coefficient at twice the first potentially nonzero degree supplies F20b's obstruction. Thus neither rationality nor a first-order bound is the missing requirement in this class. This theorem does not construct a deformation from a Xi zero or prove the arithmetic coefficient bounds. Evidence: `HTGeometry.arithmetic_formalDeformation_iff_constant` in `ArithmeticSecondOrderObstruction`.

F20d — Cannot infer a complex location constraint from all prime-carry identities and preservation of integers alone. The single family `δ_p(z)=(z−z^p)/p` satisfies the nonlinear addition/product carry rules for every prime on all of `ℂ`, maps integers to integers, and reconstructs `z^p+pδ_p(z)=z`. An infinite family of these exact arithmetic identities is therefore still nonselective; this does not exclude additional conditions on an integral completion. Evidence: `HTGeometry.IntegerPrimeCarry.all_prime_carry_laws_on_complex_plane` in `IntegerPrimeCarryComplexExtension`.

F20e — Must distinguish an infinite nonlinear history from its vanishing. In a complete real normed algebra with `‖1‖=1`, bounded real coefficient sums and a vanishing algebra-valued weight with summable successive differences force the chronological exponential product to converge to an invertible limit, without commutation between times (`ordered_exponential_converges_to_unit` in `HTGeometry/NoncommutativeAbelDevelopment`, Lean). Literal integer-deletion coefficients `1−p·1_(p divides n)`, `p≥1`, weighted by `n^(−s)`, satisfy these conditions for every `Re s>0` after any continuous real-linear map into that algebra; their limits respect continuous algebra homomorphisms (`eulerDeletionDevelopment_converges_to_unit`, `map_eulerDeletionDevelopmentLimit`). This constructs each separate exponential history without zero input; no identification with the raw discrete quasi-shuffle lift, cross-modulus coherence, identity limit, or critical-line selection is proved.

F20f — Must distinguish control of every interaction depth from a relation between arithmetic histories. For each fixed modulus `p≥1` and `Re s>1/2`, the literal jumps `(1−p·1_(p divides n))n^(−s)` generate one operator-norm convergent history on bounded functions of all finite words, retaining every strict iterated word in their real/imaginary parts. A single cutoff controls all word lengths simultaneously; phase encoding is injective and its two letter actions do not commute (`ArithmeticWordHistory.all_word_lengths_uniform`, `phaseLetters_injective`, `letters_do_not_commute` in `EulerDeletionWordHistory`, Lean). This uses the actual discrete factors `1+L(jump)`, not replacement by exponentials. A zeta zero closes its first level (`zeta_zero_closes_first_level`); no higher-level vanishing or cross-modulus selection law is proved. F20h gives the exact scalar boundary for growing moduli. In this construction, merely adding arbitrarily high interaction orders is no longer a missing existence theorem.

F20g — Must preserve movement of the source argument when transferring an arithmetic law. Literal integer carries `c_n(x)=floor(nx)−n floor(x)` have zero-or-one additive defects and `0≤c_n(x)≤n`, but obey `c_(mn)(x)=c_m(nx)+m c_n(x)`. The untwisted rule `c_(mn)=m c_n+n c_m` holds for all integer inputs iff `x` is an integer, when every carry is zero. Their quadratic lift retains the transported argument and weight `m²`; their exact phase family `exp(i t c_n(x))` has norm one at every scale. Thus this bounded-carry construction cannot supply a nonzero instance of F20b by freezing its argument or using bounded phase as a bound on the unwrapped response. This does not exclude transport-aware laws or identify `x` with a Xi parameter. Evidence: `carry_add_defect`, `carry_bounds`, `untwisted_leibniz_iff_integer`, `second_mul`, `phase_mul`, `norm_phase` in `IntegerCarryTransport` (namespace `HTGeometry.IntegerCarryTransport`, Lean).

F20h — Cannot replace convergence for each integer modulus by one ordinary cutoff controlling all moduli in `0<Re s≤1`. For the literal prefixes `P_q(s,N)=sum_(1≤n≤N) (1−(q+1)·1_(q+1 divides n))n^(−s)`, uniform Cauchy tails over `q≤A(N)` exist exactly when `A(N)(N+1)^(−Re s)→0`, for every natural-valued budget `A`, without a monotonicity assumption. A deletion within the next block forces the matching lower bound; periodic Abel summation supplies the upper bound. The criterion holds independently of whether zeta vanishes and supplies no relation between completed histories. Evidence: `DeletionModulusBoundary.uniformTails_iff_budget_decay_critical` and `not_all_moduli_uniform` in `EulerDeletionGrowingModulus` (Lean); [proof and scope](../../3-formalized/not_new_scientific_knowledge/euler-deletion-growing-modulus-boundary.md).

F20i — Must recompute a quotient at a vanishing scalar before using a description obtained by dividing that scalar away. Over any commutative ring R, the two-coordinate boundary generated by `(-c,cq)` and `(cq,-cq)` has quotient `R/(c) × R/(cq(q−1))`. At `c=0` its boundary is zero and both coordinates survive for every q. Therefore setting `c=ζ(ρ)=0` cannot select q through nonvanishing of this quotient. The conclusion concerns this literal construction; it is not a restriction on all homological approaches to RH. Evidence: `quotientEquiv`, `quotientZeroEquiv`, and `field_finrank_classification` in `DerivedSelectionGeometry.SourceScalarBoundary` (Lean); [proof and scope](../../3-formalized/not_new_scientific_knowledge/cyclic-source-nonunit-scalar-audit.md).

F20i-a — Must retain a nonzero coefficient before pairing with a testing vector that vanishes. No nonlinear, discontinuous, nonreciprocal, or parameter-dependent choice of the other vector can recover it through an ordinary bilinear pairing. For the corpus's literal source probes, the entire attainable scalar range is exactly the profiles vanishing at critical zeros; every such profile already has a weighted linear skew realization, with weights fixed away from critical zeros and free on them. This restricts that source readout, not all nonlinear or distributional approaches to RH. Evidence: `exists_hbXiPeierlsSourceProbeProfile_iff`, `hbXiPeierlsArbitraryResponseProfile_has_weightedSkewRealization`, `hbXiPeierlsSourceProbeProfile_weighted_eq_iff`, and the unconditional full-AIME/first-live-jet exclusions in `ThetaCuspHawkingBMSourceProbeRangeClassification` (namespace `RHTower`, Lean).

F20j — Cannot infer uniform geometric coefficient control from formal invertibility of the literal arithmetic series. The series `F_s(z)=sum_(n≥1) (-1)^(n−1)n^(−s)z^n` has a two-sided formal compositional inverse for every complex s. Its third coefficient defect is `a3−a2²=3^(−s)−4^(−s)`, whose maximum over all imaginary parts at fixed real part sigma is exactly `3^(−sigma)+4^(−sigma)`. This maximum crosses one at a unique real cutoff strictly between 1/2 and 1, so the unit coefficient ceiling already fails at some points strictly right of the critical line. Formal inversion supplies no such ceiling and no zeta zero-location restriction. Evidence: `formalSeries_subst_inverse`, `formalInverse_subst_series`, `horizontal_unit_bound_iff`, and `exists_strict_half_strip_violation` in `AlternatingInverseCoefficientBoundary` (Lean); [proof and limits](../alternating-source-inverse-branch-intake.md).

F21 — Execution/observation is lax in two independent places. Source histories can fail to splice; a later noninjective observer can create an additional false splice.

F22 — Grammar is graded and reflexive. Repairing one failure can generate next legal failure context. Finite or set-level reflexivity has not generated arithmetic cofinal selection.

F23 — Compact recurrence converts drift to carry. Nonzero character forces cofinal linear carry traffic; recurrence alone does not bound traffic.

F24 — Finite source recovery can be injective while cofinal map collapses. Faithful normal recovery can have singular/full vertical fibre. Regular observers are not enough.

F25 — Exact mass transport closes quantity but leaves ordered incidence current. Conservation of mass is weaker than cancellation of signed node-cell transport.

F26 — Routes are not equivalent gauges. Singular transitions can enlarge admission exactly by killing obstruction classes; injective transitions preserve admission. Any universal field must retain first-loss data rather than declare all route carriers isomorphic.

F27 — Generic failure-to-test, obstruction-promotion, and diagonal grammar-genesis mechanisms are already formalized. They generate new laws and unbounded primitive degrees, but do not by themselves turn a literal arithmetic source defect into a vanishing theorem.

F28 — Additive horizontal information already has a literal group-theoretic form. Gamma-six source atoms live in an infinite cyclic group algebra; physical evaluation is an exponential character with parameter `(2 Re(s)-1) log 6`. Its descent through the source boundary holds exactly at neutral grade.

F29 — Nonabelian perfect source algebra exists in corpus. Steinberg and elementary groups in rank at least three are perfect; every root generator is a chained commutator. Their kernel is the formal `K₂` carrier. This machinery has not been coupled to horizontal Xi formation.

F30 — Perfectification cannot mean scalar trace erasure. Ordinary trace kills split-leg commutators at every grade while graded corner traces recover positive off-centre curvature. Therefore a valid nonabelian fusion must transgress lost `H₁` current into a retained central/ `K₂` class and then control that class; merely calling current a commutator is false progress.

F31 — The EWQ/Gamma fusion is already exact. The two-gauge interaction quotient is one-dimensional; the normalized Euler--Wick packet spans it; opposite Gamma-six characters land in exactly that class with coefficient `curvature/8`. Its radical is exactly `a=0`.

F32 — Hypertranscendental decoration makes the full Laurent quadratic ghost independent of both analytic marginals, so its descent is exactly `a=0`. This proves non-absorption, not annihilation; global descent remains exactly RH.

F33 — Actual arithmetic has a degree-lowering operation. A depth-dependent cubic polynomial in the Kummer derivation sends an honest Steinberg cell in augmentation order two to its oriented normal edge in order one. Kummer regulator reads the nonzero lost order exactly.

F34 — That oriented edge is not a Steinberg/Milnor boundary and its multiplier `K₁` cycle is not a Hochschild degree-two boundary. The two-sided Gamma-six normal has the same non-membership. Thus a literal `H₁ -> K₂` perfectification contradicts the source algebra.

F35 — Formation order already has an integral spectrum. On `I^r/I^(r+1)`, formation number acts by integer `r`, reflection acts by `(-1)^r`, and closed period `p` leaves first-grade residue `p`. The positive Rees completion has compact formation resolvent, but no Xi occurrence theorem.

F36 — Existing source-normal equicontinuity, bounded formation work, and global properness predicates select `a=0` exactly. None is known unconditionally on the Xi source; assuming one is only another RH receiver.

F37 — Literal completed Weyl/Clifford action is impossible: its orbit of the Xi sector runs through three auxiliary completed `L` sectors, so kernel invariance requires four simultaneous zeros. A surviving scale action must live before completed Fourier-sector diagonalization.

F38 — Source algebra already has integral Frobenius/Adams structure: prime-packet units identify with multiplicative automorphisms of the algebraic prime fibre, and arithmetic Frobenius is literal `p`-power. What is absent is a zero-independent prime--Gamma/Xi comparison making horizontal physical character an algebraic weight of this action.

F39 — Formation-scale quantization is not a new mechanism. The scalar HT clock programme already proves polynomial multiplicative characters are monomials and develops the common Möbius clock toward integral weights. Its open source/clock realization is the same semantic bridge that the quantization proposal would have renamed.

F40 — Reduced rational-Witt descent loses orientation. At the cyclotomic Gamma-six denominator, forward and reciprocal residues coincide, their odd difference is zero, and Frobenius-fixed residue retains only parity. Ramified top-conormal stages restore a coefficient-faithful oriented grade, but the corpus explicitly does not prove that completed Xi/Gamma intrinsically supplies that grade.

F41 — Infinitesimal rigidity is already a receiver. Off-line Xi placement gives a faithful dual-number arc and a formally ramified transverse image; formal unramifiedness of that image is equivalent to critical-line placement. Declaring the tangent direction illegal is circular.

F42 — Complete positivity cannot be the higher law. The physical two-leg first-jet landing is complex and orientation-sensitive; replacing it by `L* (.) L` makes a CP channel while deleting global phase and the reflection-odd second-Cartier class.

F43 — Formal-group structure explains but does not select. Corpus already proves the multiplicative law `F(X,Y)=X+Y+XY`, its logarithmic linearization, the exact inverse relation between forward and reflected defects, and the resulting positive curvature for every horizontal grade.

F44 — Ordinary reciprocity conserves displacement. Product formula balances a nonzero archimedean logarithm against finite valuations for every real exponent. Torsion Brauer data cannot faithfully receive continuous horizontal charge.

F45 — The source has ingredients of a cyclotomic law but not the law. It has a genuine nonzero K1-style unit cycle `u_p^-1 tensor u_p` in Hochschild-one homology, detected by Kummer and Stokes regulators, exact rational-Witt Frobenius/Verschiebung operations, and a strict Xi-resolved landing. Corpus does not yet construct an algebraic `K_1` lift whose Dennis trace is this cycle. THH/TC and cyclotomic trace occur only as parent machinery in one programme; no number-field cyclotomic realization or archimedean Gamma comparison is constructed.

F46 — Gamma/EWQ curvature is the product of two first-order comparison defects. For `q = exp(a)`, set `D+ = q-1`, `D- = q^-1-1`. Corpus proves

`D+ + D- = -(D+ D-) = 2(cosh(a)-1)`

and identifies this scalar, modulo the two marginals, with the unique EWQ interaction class. This is exactly the algebraic shape of a second cross-effect of a failed equalizer.

F47 — Plain cyclotomic equalization fails its own collision test. Gamma cover composition at `p=2,3` is coherent for every grade; finite rational-Witt orbit traces are Frobenius fixed while the signed orientation is erased. A coefficient-faithful `TC^- -> TP -> Gamma` comparison would have to restore precisely the existing scale-zero/rational-Cartier producer. Standard p-typical `TC` does not make that restoration automatic.

F48 — Stabilization/additivity also erases the needed defect. Corpus proves the physical degree-one product trace does not descend through ordinary Hochschild boundaries. A localizing or 1-excisive invariant can kill the nonlinear cross-effect, but cannot then recover Gamma/EWQ curvature coefficient-faithfully.

F49 — Every Xi divisor has a canonical transverse algebra map from dual numbers into the summable Hadamard corona. Its image is scalar on the line and is an embedded dual-number algebra off the line. FE reflection acts on the framed arc by `eps -> -eps`; forgetting the frame makes direct and reflected image algebras identical at every grade.

F50 — Corpus already contains the relevant formation Hopf source. The packet generator `t` is group-like. The monoid bialgebra `k[t]` has no antipode; its Laurent group completion `k[t,t^-1]` is a Hopf algebra with `S(t)=t^-1`. This is the exact algebraic shape needed to combine formation, splitting, and FE reflection.

F51 — Existing common recovery proves action-level naturality only: FE lifts through formation and is information-neutral. Corpus search found no theorem saying the Xi occurrence kernel is stable under packet splitting/comultiplication. This distinction is the new frontier.

F52 — Formation-congruence leakage is already formalized. `RouteRExternalTensorMonodromy` proves group-like formation equals primitive formation plus external tensor curvature, curvature survives exactly off wall, diagonal multiplication erases it, and source equality of the two formations is the unproved RH-strength operation. A coideal-kernel formulation is the same endpoint.

F53 — Every current drift/recurrence model is generated on cyclic, abelian, amenable, or freely fitted symmetry. Those symmetries admit unbounded one-cocycles. Existing scale--Mautner theory shows pure-point recurrence erases formation and compact-resolvent same-fibre dilation is impossible, but cross-fibre histories still escape.

F54 — Corpus has unused higher-rank source grammar: rank-three Steinberg and elementary groups, perfectness, finite generation over finitely generated rings, torus words `h(u)`, exact torus conjugation weights, Weyl inversion, and explicit central `K_2` relation defects.

F55 — Corpus has no Kazhdan property-(T), fixed-point-(FH), or higher-rank affine-cocycle realization. It also proves the Gamma-six oriented normal is not Steinberg/Milnor incidence, so a valid higher-rank law must extend its action as cocycle data rather than falsely making it a Steinberg boundary.

F56 — Kazhdan extension is dead. Physical half-density transport is nonunitary, the Gamma normal lies outside the Steinberg ideal, and extending a cyclic current to a rigid group is unconstrained law insertion. Property (T) would only kill a cocycle after the RH-strength extension existed.

F57 — Path coherence is dead. The Gamma cover composes coherently at every grade, including off-line grades. FE-compatible parallel transport does not imply criticality.

F58 — Compact/filtration lowering is already generic corpus infrastructure. The source-normal depth-lowering admission and compact aggregate needed at Xi fibres are RH-equivalent endpoints; renaming them properness or quasinilpotence adds no mechanism.

F59 — Raw cubic source channel is not summable; only a renormalized correction is. Therefore no global trace law may silently assign nuclearity to every source-generated interaction.

F60 — Linear source-reversal defect is mixed-cobar exact even off line, while its quadratic mate curvature survives. Exactification moves information to higher interaction order; it does not annihilate it.

F61 — Gamma-six forward/reflected defects form an odd visible law `D(a)` with `D(a)^2 = -K(a) I`, `K(a) >= 0`, and `K(a)=0 <-> a=0`. For `a != 0` this curved law has an explicit contracting homotopy. Thus ordinary cohomology/Hodge contraction accepts exactly the wrong sector.

F62 — Bare `L_infinity`, Maurer--Cartan, Cartan contraction, Gauss--Codazzi, cofinal filtration, and obstruction-degree lowering already exist in Lean. Rephrasing corpus in any of these languages is not a conjecture.

F63 — A flat total block law can hide nonzero observed curvature as a product of two complementary couplings. Existing Gauss--Codazzi proves this abstractly. Hence `total law squares to zero` alone does not select; it permits curvature leakage.

F64 — Completion phantom, source tail, divisor current, and nearby-cycle defect carry the same off-line Noether charge. This classifies survival after completion; it does not force vanishing.

F65 — Cross-route fusion is not the missing theorem. Corpus already proves that one signed source-history defect is exactly normalized compact-theta Green flux, inverse-Cayley Gamma-frame skew, logarithmic duality--dagger curvature, shell-transfer entropy, and multiplicity-weighted affine Xi residue (`XiHistoryThetaGammaAmbidexterityTransgression`, `XiSourceHistoryResidueTransgression`, `XiDualityDaggerHistoryTransgression`).

F66 — The fused defect has explicit exchange rates. If `a = 2 Re(s)-1`, its coordinates include `a`, `m a`, `log(p) a`, `exp(±log(p)a)`, a quadratic formation cost proportional to `a²`, and a positive entropy-production coordinate. These are nonlinear presentations of one anomaly, not independent constraints on it.

F67 — Existing positive proofs mostly reconstruct or conserve the anomaly. Existing no-gos mostly show that hiding it forces payment in rank, conditioning, sign variation, singular domain, interaction order, provenance loss, or open history. The corpus therefore distinguishes an intrinsic signed anomaly from the multi-resource debt created by attempts to suppress it.

F68 — Resource currencies cannot yet be collapsed to one scalar. Exact lower bounds are proved in different categories, and corpus has no universal exchange theorem converting rank growth, condition-number growth, noncompact Calkin class, negative capacity, sign variation, singularity, and horizon escape into one another.

F69 — A cost is evidence only when fixed before choosing a repair. Every repair selector is the unique minimizer of a manufactured positive cost (`ConstitutiveRepairTorsorSelectorNoGo`), so an optimized correction proves nothing unless both cost and admissible class are source-generated.

F70 — Algebraic existence and executable control are different layers. A two-prime Bezout identity can exist while every bounded synthesis fails (`HedenmalmTwoPrimeBezoutGrowthNoGo`); exact finite formation does not imply a bounded, continuous, or cofinal execution.

F71 — Almost-everywhere topology is too coarse for divisor semantics. An isolated resonance can be
changed pointwise without changing its `L²` class, while Hardy/RKHS or distributional structure
retains it (`ThetaCuspHawkingGlobalL2ShellBlindnessNoGo`, `L2PointSamplingNoGo`).

F72 — Even complete local shape is nonselective. All-order local Bernstein sign, every prescribed
finite jet, and every finite critical prefix can coexist with a later wrong sign; the Li survivor
requires an essentially infinite, nonuniform tail cancellation.

F73 — Two-axis and second-order coherence are already receivers. Grade--phase nodal purity, its BV
master equation, and coherent second-order descent of a fixed all-prime source complex are each
proved equivalent to RH (`XiNodalDefectSuperselection`). Adding dimensions or saying “mixed
curvature” does not supply selection.

F74 — Audit baseline is explicit. At the 2026-09-01 13:55 frontier cutoff, 561 named `NoGo` Lean
files, 73 declarations then classified as explicit positive survivors across 67 files, 232 certified
universal-law capstone rows, every frontier branch/open core/boundary, and all 1,917 reconciled
endpoint obligations were checked at statement level. The 13:55–15:22 frontier delta and its
immediate endpoint audit are compressed in `F89`–`F108`; mutable file/text counts are not
mathematical claims.

F75 — Positive results split into three logically different classes. Transport/reconstruction laws
identify or conserve data unconditionally; selection laws prove neutrality from a global premise;
positive survivors quantify what remains or what a repair must pay after a no-go.

F76 — Unconditional transport is abundant and nonselective. Exact recovery, FE lift, reflection, Hodge realization, Hilbert/Gram reconstruction, Noether conservation, transgression, and four-organ fusion preserve or re-express the defect but do not force it to vanish.

F77 — Every audited abstract selector has the same logical shape: fixed law plus bounded work, compact/proper admission, exact exchange, no-loss descent, integrable potential, or closed history forces neutrality. At actual Xi fibres, supplying that global premise is an endpoint or is already proved RH-equivalent.

F78 — Positive survivors have a common direction: a failed finite/regular repair does not leave nothing. It leaves a pointed residue, relative class, mixed charge, nonzero conormal jet, rank or capacity floor, reciprocal-growth bound, sign-indefinite form, divergent synthesis, or cofinal current.

F79 — Generic universal-law machinery is saturated in corpus. It already contains strictification, central promotion, higher transgression, `L_infinity`/MC, finite and nonabelian Livsic theory, properness, compactification, interaction spectra, Hodge carriers, phase quotients, recurrent/open histories, and higher-arity formation. Recasting RH in one of these mechanisms is not progress.

F80 — The main logical fracture is source execution versus semantic observation. Finite source rules may terminate while completion is nonconfluent; algebraic relations may be exact while bounded execution fails; observer relations may close by splicing distinct source histories; and completion may create a class with no finite witness.

F81 — “Shadow” has a precise audit meaning: any faithful image, nonlinear coordinate, positive square, quotient, completion class, residue, or cost generated from the same source defect. A shadow is not a new independent reason for vanishing. A theorem about literal source execution that rules out the defect before Xi-zero specialization would not be a shadow; corpus presently has no such theorem.

F82 — Physical source landing is no longer an open identification. The prime-normal integer-labelled Möbius–theta source equals the `mPart` source in `L²`; Plancherel lands it in `ζ(m(1/2+it))⁻¹ XiC(t)` almost everywhere; and its complete exponent codiagonal is absolutely summable in `L²` (`MobiusThetaPhysicalSourceToXiLanding`). This controls the real Plancherel boundary, not complex point evaluation at a divisor.

F83 — Compact prime-packet exactness and analytic graph completion are genuinely different. Literal finite packets are dense in the Gamma-six graph completion, while explicit averaging packets vanish in ambient `ℓ²` and retain unit graph trace; the singular vertical boundary is therefore produced by actual source sequences, not by missing inverse-limit infrastructure (`DeningerGammaSixCofinalSingularGraphSoninTransport`).

F84 — Barrelled closed-graph selection is a terminal receiver. A completed barrelled source with pointwise-bounded readouts kills horizontal grade by Banach–Steinhaus, but existence of the Xi-labelled certificate and of its global producer is already equivalent to critical-line placement and RH (`PrimeDepthBVWoldBarrelledSourceTerminalNoGo`).

F85 — The finite renormalized cubic Euler–Gamma budget does not continuously dominate the off-centre Hellinger sector. The cubic/Hellinger self-charge is discontinuous at the critical boundary, and the remaining completed-source order law is RH-equivalent (`XiWardCubicLogMomentHellingerCauchySeparator`, `FrankensteinWoldCubicJuliaOrbitBudget`).

F86 — Möbius, von Mangoldt, theta/Gamma, and finite face/Koszul descriptions are already one exact source calculus. Lean proves `μ * log = Λ`, contraction of the Dirichlet Maurer–Cartan form to the literal von Mangoldt current, Witt ghost/exterior Newton generation, complete Möbius–theta Fourier–Laplace landing on its honest domain, and finite prime-face alternating augmentation (`MobiusLogDivisorParaproduct`, `DirichletMaurerCartanMellinOrbitLaw`, `WittFormationMechanics`, `MobiusThetaComplexSourceToXiLanding`, `PrimeDilationTropicalBoundaryTomography`). It also has `Λ * μ = -μ log` and its absolutely convergent dilation law `sum_m Λ(m) f_h(mx) = -sum_n μ(n)log(n) H_h(nx)` for `h in DeningerExpSchwartz, x>0` (`deningerMobius_connection`). Recasting that identity as feedback supplies no estimate by itself. Algebraic fusion is closed; cofinal cancellation or complex occurrence control is not.
F86a — It already has nonlinear visible addition `sum_(a,b>=1,gcd(a,b)=1) Φ(ax)Φ(by)=Φ(x+y)` for `x,y>0`, `Φ(x)=sum_n μ(n)e^(-nx)` (`visibleCoprimeMobiusLaplaceSum_eq_add`, Lean). Raw coprimality matrices have unbounded negative inertia (`finiteMobiusCoprimeMatrixComplex_negativeInertia_unbounded`); the pairing cannot be assumed positive. Its continued Mellin kernel `ζ(s)ζ(t)invζ(s+t)` has mixed order-`(m,m)` jet at `(ρ,conj ρ)` equal to `|ζ^(m)(ρ)|² invζ(2 Re ρ)`, where `m` is exact Xi multiplicity and `invζ(1)=0`; this jet vanishes iff `Re ρ=1/2` (`visibleCoprimeZetaMixedJet_eq`, `visibleCoprimeZetaMixedJet_eq_zero_iff`). These certificates classify the jet, not force its vanishing.

F87 — Finite prime zero localization is already exact in two different normalizations. A literal finite Euler functional equation forces every local parameter to satisfy `a_p² = p` and every zero to have real part `1/2` (`FiniteSquarefreeEulerFunctionalEquation`). In centered Lee–Yang coordinates, the physical factor `p⁻¹ᐟ²` shifts the unit wall to `Im z = 1/2`; moving that factor into a ferromagnetic two-spin interaction restores centered finite zero localization, whereas direct reciprocal Euler pairing is Lee–Yang only at unit weight (`PrimeEulerLeeYangAmplitudeNoGo`, `PrimeEulerFerromagneticInteraction`, `EulerReciprocalLeeYangNoGo`). None of these finite theorems identifies a cofinal limit with completed Xi.

F88 — Direct prime-Ising thermodynamic reconstruction of Xi is ruled out. Unbalanced finite trees have a nonzero oriented central logarithmic-derivative floor; scalar centering does not remove it; even or Schwarz-real zero-free normalizers cannot absorb it; and no sequence of balanced finite prime-labelled ferromagnetic trees—with arbitrary labels, couplings, topology, and size—converges locally uniformly to unit-pointed XiC (`PrimeIsingTreeCentralMassFloorLaw`, `PrimeIsingTreeBalancedCentering`, `PrimeIsingTreeFixedModalClosureNoGo`). Finite Lee–Yang zero localization and completed analytic shape are independent obligations.

F89 — Cofinal contour scheduling has no asymptotic selection freedom. Every admissible cofinal corrected-prime rectangle schedule converges to the same complete physical Weil energy, and any two schedules differ by a term tending to zero. Nevertheless asymptotic nonnegativity along one, some, or all such schedules is exactly RH; under failure of RH every schedule has an eventually uniformly negative physical sample (`XiPhysicalPrimeApertureThetaAbelEnergyPrimeCofinalScheduleInvariance`).

F90 — The full error-syndrome packaging already exists. One off-line Xi divisor fibre carries a simultaneous source-defined completion-defect syndrome collecting independently constructed route shadows exactly when its horizontal grade is nonzero; global syndrome-freedom is exactly RH (`XiCompletionDefectSyndrome`, `XiInternalTransverseCompletionSyndrome`). The syndrome classifies a global logical sector but supplies no source law excluding it.

F91 — Secondary energy and self-intersection are already exact shadows. Corpus has nonnegative secondary Floquet/Green energies and positive finite Hodge self-pairings; its canonical reflection self-intersection charge is exactly squared off-line divisor order, is even and monotone by height, and vanishes globally exactly under RH (`DeningerSecondaryFloquetEnergy`, `DeningerMeyerSecondaryPoissonRegulator`, `XiReflectionSelfIntersectionCharge`). Ordinary adelic product reciprocity remains blind to every real horizontal exponent.

F92 — Prime–theta mixed covariance is already exact but quotient-blind. Normalized integer translation has a flat rank-one covariant source inverse on every integrable source vector. At each Xi divisor copy, both reflected orientations have the same nonzero integer-anomaly forcing with the same label, yet that forcing lies in every retained Xi conormal kernel. Equality of the two translated source modes is equivalent to horizontal vanishing, so common forcing and flatness do not produce the equality (`FrankensteinThetaPrimeTranslationCommonForcing`).

F93 — Complete reflected-Hankel positivity is not a real-zero law. The positive real entire source `cosh(z) + cosh(2z)` has nonnegative reflected polynomial-square moment form at every real centre and strictly positive rank-three signed Hankel determinant, yet it vanishes at `i*pi/3` (`TCDCompleteReflectedHankelRealRootednessNoGo`). Thus even all-order positive reflected moments do not determine complex divisor orientation.

F94 — A finite literal Ramaré packet cannot be source-faithfully centred. Vanishing on one nondegenerate interval uniquely forces the finite counterterm to negate every source coefficient and vanish off source. Every nonempty literal scalar packet, and its actual bilinear form, has strictly positive squared-norm energy on every such interval (`RouteERamareSourceFaithfulFiniteCenteringNoGo`).

F95 — Quadratic divisor charge is incompatible with either one-sided compact-open semicontinuity. Upper-semicontinuous lower-faithful Wold-charge descent exists exactly under RH; in the opposite direction, two simple off-line roots converge locally uniformly to one double root while exact charge jumps from `4` to `8`, excluding lower-semicontinuous exact reporting. Scalar multiplicity weights stable under collision are exactly linear (`XiHeatCassiniWoldOrbitChargeUpperSemicontinuousNoGo`, `XiHeatCassiniWoldOrbitChargeLowerSemicontinuousCollisionNoGo`).

F96 — Hilbert compensation has an intrinsic hard-edge graph-energy divergence independent of rank or metric regularity. The exact pre-divisor HB susceptibility is at least `x^-2` on `(0,1/2)` and is not integrable. No two Hilbert-valued legs realizing even its diagonal can both have finite square energy; if one feature leg has finite energy, every exact metric-image leg has infinite energy, with no boundedness, closability, self-adjointness, or domain relation assumed (`ThetaCuspHawkingPreDivisorFiniteEnergyInfiniteRankGramNoGo`, `ThetaCuspHawkingPreDivisorFiniteGraphEnergyMetricNoGo`).

F97 — Hypertranscendence is forced by infinite spectrum in one exact source class. A one-sided periodic heat orbit with algebraic Fourier amplitudes, convergent for every complex time and place, has finite support whenever its time-zero spatial fibre is differentially algebraic. Everywhere backward-entire heat evolution also forces super-Gaussian coefficients and sublogarithmic central index (`ArithmeticHeatFiniteSpectrum`, `SuperGaussianCentralIndex`).

F98 — Autonomous composition can hide one primitive state exactly. For an autonomous first-order outer factor, the complete composite-jet field adds only one transcendence degree over the inner derivative-shadow field. On the same Gaussian primitive, replacing `exp(w)` by the nonautonomous `w exp(w)` restores the compressed state and raises differential rank from three to four (`CompositionRelativeVisibility`, `NonautonomousCapGaussian`).

F99 — Paired irregular unitarity is strictly weaker than constituentwise purity. A formal type and its Hermitian dual have unit-norm determinant at every source scale for every type. At any one nonzero scale, unit norm of each constituent is equivalent to vanishing real type; on Xi copies this is exactly critical-line placement (`XiDualConjugateIrregularPurity`).

F100 — Smooth completion can hide two exact relative characters. The raw Stokes current and its polar countercurrent complete to a wall-continuous codiagonal while their difference tends to `8m`, with exact Xi multiplicity `m`. At second order, Laurent ghost and cyclic anomaly have zero codiagonal for every Xi divisor, while their relative Ward character vanishes exactly on the critical line (`XiResolvedStokesWardCharacter`).

F101 — A nonzero all-orders-flat boundary charge is genuinely nonanalytic in augmentation scale. For analytic germs, flatness beyond every Rees grade is equivalent to local zero. The actual positive-charge reflected prime–Wold gauge is nonzero and all-orders flat, hence cannot be the boundary sampling of a holomorphic augmentation germ (`ReesAnalyticQuasianalyticity`).

F102 — Nested source formation performs a legal cancellation that external centering cannot. Subtracting two nested literal Ramaré aperture forms cancels all scalar mass already present at the smaller aperture. The exact remainder consists only of polarization against newly activated integers, the activation-seam norm, and old-minus-new normalized incidence energy; the integrated physical off-diagonal obeys the same identity (`RouteERamareNestedApertureScalarLocalization`).

F103 — Literal nonabelian depth data can survive completion exactly. In the actual Q8 quadratic source, the central involution is detected by the coefficient-faithful character as `-1`, occupies lower ramification levels zero through two, disappears at level three, and has the same break after adic completion and local-CFT comparison (`DeningerQ8ActualQuadraticSourceHigherRamification`). This is a source-depth/orientation fragment, not a completed-Xi occurrence law.

F104 — A pole-clearing gauge is exactly invisible to the relevant rectangle boundary functional when its zero lies outside the rectangle. Multiplying a detector by that gauge changes neither the weighted Littlewood boundary charge nor its height growth; detector, mollifier, and horizontal boundary terms remain (`LittlewoodPoleGaugeCancellation`, `LevinsonMollifiedEdges`).

F105 — Refinement conserves rather than annihilates defect in the abstract corpus. Binary fusion splits total defect into local block defects plus defect between block resultants; fine formation energy is coarse endpoint energy plus centred fluctuation energy. The nested Ramaré law is a literal arithmetic instance with activation seam and incidence-energy variation (`NormingFaceFusion`, `SourceFormationHarmonicMechanics`, `RouteERamareNestedApertureScalarLocalization`).

F106 — A zeta zero removes one base observation, not the lifted hierarchy. In the strict right half of the critical strip, the heat–aperture echo ladder has nonzero source coefficients and every positive-depth value is nonzero; `zeta(s)=0` is exactly disappearance of rung zero. Even and odd subsequences separately obey closed rising-factorial laws from their initial rungs (`HeatApertureEchoParity`).

F107 — FE and Schwarz comparison already gives a complete one-coordinate orientation detector. For every prime, the heat–aperture coefficient difference is the canonical prime seam up to an explicit nonzero factor; equality at one prime is equivalent to `Re(s)=1/2`, and checking all primes adds nothing beyond prime two. Equality of the actual degree-one Euler local fluxes and equality of the actual Euler-point tangents have the same zero locus. Pointwise existence of a radially calibrated dagger-confluent repair is likewise equivalent to `Re(s)=1/2` (`HeatAperturePrimeSeamReflection`, `ConstitutiveDaggerConfluence`).

F108 — Monotone Schrödinger dynamics does not orient rank-three reflected Hankel curvature. The positive even entire profile `exp(-z²-z⁴/6)` satisfies `f''=Vf`, has `V(0)<0`, and has strictly increasing `V` on the positive ray, yet its central signed rank-three determinant is `-87040` (`TCDMonotoneSchrodingerD1NoGo`). Thus the proved monotonicity of the actual theta Schrödinger potential cannot by itself settle the remaining TCD sign.

F109 — Formation, source-generated execution, completion genealogy, operation descent, history, properness, and intervention grammar are already explicit universal-law programmes with exact calibrations. Their selection gates all retain an unproved literal-source premise. Naming one of those mechanisms again does not change the logical frontier.

F110 — Audited operations fall into three anomaly-support classes. Faithful recovery, gauge, and functional-equation transport retain horizontal grade; positive, scalar, and recurrent observers forget part of it; admissible Gamma-cell multiplication can introduce arbitrary off-line divisor without violating the ambient structural laws. Corpus search found no literal pre-divisor operation that both restricts which horizontal grades occur in the Xi divisor and is proved before occurrence specialization.

F111 — Base-preserving does not mean support-preserving. In `Set/A`, the base-preserving maps `f(a,*)=(a,a)` and `g(a,*)=(a,0)` have equalizer supported exactly at `a=0`. Products, split recoveries, and fibrewise surjections preserve inhabited support, but equalizers and compatibility loci can select a fibre. The unresolved issue is source generation of the relation, not whether its maps are vertical.

F112 — “Endogenous compatibility” is not a restriction unless its generation grammar is fixed. `SourceCoherentInterventionSynchronization` already packages source response equalizers and proves zero selection from triviality plus compatibility. Conversely, `ConstitutiveEndogenousCompatibility` proves that one state-indexed test can realize every transition system, naturally under relabelling. Thus an unconstrained source-indexed relation can hide the desired conclusion verbatim.

F113 — Finitary-versus-cofinal birth and compact escape are already closed mechanics, not a new field pivot. Finite words, even from arbitrarily many monotone extensive finitary formations, retain finite ancestry and cannot realize the concrete cofinal-birth closure. The corpus already retired bare compact-counterwitness escape after identifying formation depth as its diverging resource (`ConstitutiveFinitaryFormation`; `ULF-GTM-FAILED-2`).

F114 — Passing from one zero to the whole divisor does not cross the frontier. Corpus already has complete Xi-divisor tomography, global all-zero energy criteria, and the canonical proposition `XiSourceForcedHorizontalVanishing`; its entropy, Gamma/co-Poisson, Gaussian-Wronskian, and RH forms are proved equivalent. The missing assertion remains global source-forced vanishing itself.

F115 — Source scale escape is already an exact horizontal-grade coordinate. Every nonzero grade has unbounded nonlinear prime-clock work, while bounded work is equivalent pointwise and globally to critical placement and RH (`SourceHorizontalWoldPrimeClockProfile`). Scale covariance therefore supplies a sharp receiver/properness endpoint but not the unconditional boundedness producer.

F116 — Geometry of incompatible cofinal directions is already present. Formation/completion exchange defects, noncommuting sequential observer-time limits, mixed prime/depth filters, and `InterfinityGeometry` model stable primitives, death regions, and source-marked exactness. The source-marked Lawson topology is proved to join loss of exactness with acquisition of stable primitives (`SourceMarkedInterfinityBridge`). This explains order-of-limits shadows but does not annihilate their literal arithmetic class.

F117 — Additive/multiplicative half-density unitarity is already an exact selector interface. Normalized dilation becomes additive translation, the prime/Gamma source character has modulus one exactly at neutral horizontal grade, and fixed Gamma boundary is equivalent to Meyer-character unitarity on retained Xi copies. Existing ax+b, dilation/translation, and semilocal spectral constructions do not prove that Xi occurrence must enter this unitary sector.

F118 — Must keep the model and its quantifiers fixed when applying a counterexample.
Continuous positive prime and counting densities can share a rational zeta function with a
nonreal zero at `2/3+i`, while one fixed counting function has an explicit quadratic logarithmic
remainder, hence error smaller than every positive power of `x` (`BeurlingLogarithmicCounting`).
The older arbitrary-zero construction chooses a different model for each error exponent and
formalizes no counting bound (`BeurlingRegularIntegersOffLineZeros`). Neither construction asserts
a discrete prime sequence or a functional equation. These examples test criteria sharing their
full hypotheses; they do not force every RH proof to use exact integer occurrence or distributivity.

F119 — Integral multiplicativity plus a nonvanishing strip completion factor still does not select. `GammaFECell` contains zeta, is closed under convolution by an integral multiplicative finite Dirichlet polynomial, and thereby contains `zeta*dzo` with a simple off-line zero. Exact coefficients `a_n = 1` distinguish zeta from that cell, but this coefficient identity names the literal source; it does not constrain the divisor.

F120 — Additive and multiplicative readings separate at a Xi zero. Euler--Maclaurin additive data contains a nonempty local zero certificate while every pinned finite-prime source map, finite Euler atlas divisor, and multiplicative sigma jet is trivial there (`additive_carrier_multiplicative_source_mismatch_positive`). Those finite multiplicative local data do not reconstruct this additive zero certificate. The theorem does not require every RH proof to use a particular joint-operation architecture.

F121 — Multiplicative ancestry first becomes visible in interaction order. A pure prime tone has
zero cubic moment, while the multiplicatively forced prime-square harmonic gives a strictly
positive cubic resonance; a full nonnegative prime-power tower retains this positivity
(`ThirdMomentResonance`). But positivity does not descend to the marginal interaction quotient,
which is unconditionally indefinite (`eulerWickReplicaCenteredInteraction_not_kreinNonneg`).

F122 — Static source relations do not feel horizontal Gibbs grade. Positive source reweightings
preserve the complete cofinite Gram radical and coefficient-independence matroid at every
temperature; only free energy and tropical support radius change (`SourceMarkedGibbsSplitting`).

F123 — Source-labelled rank and inertia have no positive energy quantum. For every packet size and
every `epsilon > 0`, one shared reservoir realizes a nondegenerate prime-labelled form of inertia
`(m-1,1,0)` (or its reflected reverse), trace zero, recoverable nonzero coefficients, and Frobenius
square below `epsilon^2` (`SourceHorizontalSharedReservoirAmplification`).

F124 — Integer topological charge is not a finite source resource. Matrix tensor amplification
multiplies determinant `K₁` charge by arbitrary positive dimension, while balanced reflection can
erase signed Fredholm index independently of escape multiplicity (`PrimeAFMatrixOperatorKOneDirectLimit`,
`HedenmalmThetaKakutaniBalancedIndexNoGo`).

F125 — Finite well-founded execution does not imply global selection. Every finite formation
rulebook can terminate while remaining nonconfluent; adjoining each missing join changes executable
paths but leaves generated semantic equivalence stationary (`ConstitutiveCriticalCompletionMechanics`).

F126 — Literal arithmetic carries distinct additive-successor and Dirichlet-convolution structures.
Horizontal logarithmic weight is an exact derivation of Dirichlet convolution and is invariant under
radial gauge, while Euler--Maclaurin occurrence can be nontrivial when every finite multiplicative
source jet is trivial (`DirichletMaurerCartanMellinOrbitLaw`, `IdentitySectorRadialBlindness`,
`NoGoPositiveFormulations`).

F127 — The additive/multiplicative interaction is not a direct sum. The actual von Mangoldt
successor Gram has strict negative adjacent Hankel curvature at every order; adding any ordinary
Hankel Gamma/Bianchi boundary cannot make a Hankel target. A viable completion requires forced
non-Hankel cross terms (`VonMangoldtAdditiveLogJetHankelCurvature`).

F128 — The resolved joint `(prime, depth)` source/co-source cross-pair is an exact unsquared
von Mangoldt Laplace channel and lands in the Xi relative resolvent after polar/Gamma completion.
At balanced reflection its literal coefficient cross-term is not absolutely summable, so scalar
analytic continuation is essential rather than an optional Hilbert completion
(`EulerPrimitiveJointDepthKreinXiLanding`).

F129 — Balanced-wall nonsummability is horizontal-grade blind. For every real split parameter
`a`, the literal source/co-source cross-term at reflected parameters `a,-a` is nonsummable, while
the Krein pairing and its completed scalar landing depend only on the codiagonal combination
`w + conj(v)` (`EulerPrimitiveJointDepthKreinXiLanding`).

F130 — Prime-depth BV--Wold scalar curvature is a forgetting defect, not curvature of the full
source transport. Restoring the two endpoint clock characters gives an explicit triangular frame
`G_i` with transport `G_i⁻¹G_j`, exact composition, and `D₁D₀ = 0` for every horizontal grade.

F131 — Integral centered monodromy is an exact RH endpoint, not a proved source law. The actual
centered log character descends iff its grade is integral, hence iff its grade is zero in the open
critical strip; the corpus supplies no unconditional descent premise.

F132 — Differential-character lattice periods are conditional on a character, boundary formula,
closed cycle, and discrete-lattice small-chain law. They do not turn an arbitrary nonzero scalar
triangle defect into an integral period.

F133 — Reflection-Tate cohomology detects fixed support but does not generate it. Free reflection
orbits are norms/boundaries, fixed orbits retain mod-two charge, and a charge lattice admits a
conservative Tate reporter iff every charge is already supported on the fixed locus. Existence of a
conservative Xi conormal landing is exactly RH (`IntegralOrbitTateExtension`,
`ReflectionTateConservativeClassification`).

F134 — Formation work is an exact receiver of mismatch, not a proved source budget. Independent
depth multiplies the three-slot exchange defect linearly, bounded work is equivalent to equality of
the compared laws, and global Xi formation-work properness is exactly RH
(`ConstitutiveExchangeableFormationSelection`, `XiFormationStratificationLaw`).

F135 — Common diagonal symmetry of positive-integer additive atom fusion and
multiplicative/Dirichlet atom fusion is trivial. The full common-gauge type is a singleton; this is
now paper-proved and Lean-certified (`TwoProductDiagonalGaugeRigidity`).

F136 — Real radial weights `n ↦ n^a` preserve multiplicative atom fusion at every grade but preserve
ordinary additive atom fusion iff `a = 0`. Literal Xi/Mellin formation supplies the first action,
not an unconditional theorem that it is an automorphism of the second.

F137 — Complete source response already generates a canonical context quotient, and every reachable
context-observable branched realization is uniquely equivalent to it. Sequential Hankel and
positive GNS minimal realizations and unique marked intertwiners are also Lean-certified
(`ConstitutiveContextResponseGeometry`, `MarkedWordRealization`, `MarkedCyclicRigidity`).

F138 — Minimal realization and generated intertwiners are presentation theorems, not response
selection. A functional-equation involution can fix observer and recovery kernel, exchange legs,
and act nontrivially on a nonzero formation charge (`TernaryFormationDualityHodge`).

F139 — Ambient exterior non-linearity does not imply absence of a canonical determinant line. For
every injective finite-rank formation `F`, `⋀^d(range F)` is one-dimensional and embeds injectively
in `⋀^d(target F)` (`RangeDeterminantFormation`).

F140 — Top exterior formation factors exactly through the range determinant line: source
determinant line is canonically equivalent to `⋀^d(range F)`, followed by faithful ambient
inclusion (`RangeDeterminantFormation`).

F141 — For every independent frame, canonical range generator is nonzero, spans range determinant
line, maps exactly to ambient Pluecker vector, and embedded carrier equals its ambient Pluecker
span (`RangeDeterminantFormation`).

F142 — Gram determinant is squared norm of included Pluecker vector and is invariant under
orientation reversal; it is a positive phase/orientation quotient of range determinant carrier,
not carrier itself (`ComplexGramPlucker`, `CCMEvansDeterminantLine`,
`RangeDeterminantFormation`).

F143 — Exact nonnegative action ledger plus cofinal source-potential recurrence already forces
transverse collision charge zero, and corresponding Xi landing already closes RH. Missing theorem
is literal source production of ledger/landing, not recurrence algebra (`CausalCollisionRecurrenceLaw`,
`XiCausalCollisionRecurrenceLaw`).

F144 — Source gauge change acts on top exterior formation by determinant character. Hence frame
coordinates are gauges of range determinant line, while line and embedded Pluecker span are
presentation-independent (`RangeDeterminantFormation`).

F145 — Literal Xi determinant-central holonomy defect is already a critical-line classifier, not a
global vanishing theorem. Exceptional two-sheet reflection coefficient is a gauge coboundary; its
surviving selector is mixed with Wold transport (`ArithmeticXiStokesCentralRankPort`,
`DeningerExponentGammaSixShellTransportRigidity`).

F146 — One-rank injective refinement creates a type-level determinant gap. At old degree `d`, old
top wedge injects as a one-dimensional image inside a `(d+1)`-dimensional target; at new degree
`d+1`, old exterior source has rank zero and new target is a line, so induced map is not surjective
(`RankJumpDeterminantCreation`).

F147 — Exterior powers commute with injective direct limits only degreewise at fixed `n`; this does
not transport moving determinant degrees `finrank(stage)` across strict rank growth
(`ExteriorPowerDirectLimit`, `RankJumpDeterminantCreation`).

F148 — Actual depth-12 normalized finite-abscissa source channels are linearly independent over the
full zeta differential field. Their finite complex spans have exact rank `n`, grow strictly at
every tick, and never stabilize (`LiteralSourceDeterminantRankTower`).

F149 — Every actual source tick creates a canonical pointed one-dimensional quotient: the new
literal channel has nonzero quotient class and spans the complete increment. Each finite stage and
each increment has one-dimensional determinant, while moving top exterior transport from old stage
is not surjective (`LiteralSourceDeterminantRankTower`).

F150 — Generic rank-changing determinant/interchange carriers are established mathematics:
determinant torsors/gerbes for Tate objects, 2-gerbes for 2-Tate spaces, and higher determinant
commutators already exist. Corpus determinant/index no-gos show these carriers classify anomaly but
do not force literal source trivialization (`ULF-MDIS-FAILED-1`).

F151 — Functional-equation inversion acts on the marked execution of one actual source increment
by exact multiplier `-z^-(2m+1)`. Across `n` consecutive increments beginning at `M`, multiplier is
`(-1)^n z^-n(2M+n)`; actual depth-12 prime-edge executions obey same product law
(`LiteralSourceReflectionDeterminantCocycle`).

F152 — Source rank growth amplifies fixed horizontal radial drift quadratically: accumulated
reflection multiplier has norm `norm(z)^-n(2M+n)`. For every nonempty block it has unit norm iff
`norm(z)=1`; at prime-radial character `p^nu`, this is iff `nu=0`
(`LiteralSourceReflectionDeterminantCocycle`).

F153 — FE involutivity does not trivialize accumulated determinant distortion. It pairs cocycle with
its inverse for every grade. Information-neutral common recovery likewise preserves separation,
while bilateral summability/properness is already a critical-line endpoint
(`ULF-FEIDS-FAILED-1`, `ConstitutiveFunctionalEquationPacketLift`,
`PrimeEdgeObserverFormationHodge`).

F154 — Literal rank normalization `(z^-1)^m e_m(z)` makes every nonzero-character source edge
exactly `1-z`, independent of rank. Reflection multiplier becomes constant `-z^-1`, and an `n`-edge
block accumulates only its `n`th power (`LiteralSourceReflectionRankGaugeLinearization`).

F155 — Raw quadratic reflection multiplier is exact rank-frame coboundary:
`z^m[-(z^-1)^(2m+1)]z^m=-z^-1`, with exact finite-block product identity. Quadratic rate is not
gauge-invariant; residual unit-norm classifier `norm(z)=1` survives (`ULF-QRDS-FAIL-1`).

## Logical consequences of audited facts

Each `CANNOT`/`MUST` line is a necessary consequence of cited corpus results. This section contains
no candidate mechanism, active conjecture, or research direction.

### It cannot be this

CANNOT-01 — It cannot be functional equation plus entireness plus positive `Lambda`, because an
explicit system has all three and prescribed off-line zeros (`EntireFunctionalEquationOffLine`,
`LambdaPositiveFunctionalEquationOffLine`).

CANNOT-02 — It cannot be any fixed finite packet, aperture, moment list, jet order, determinant, or
Gram test, because complete finite data admit off-line extensions (`FiniteHankelBoundaryExtensionClass`,
`CompletedResponseBoundedJetFiltrationNoGo`).

CANNOT-03 — It cannot be positivity alone, including reflection positivity, Hermitian positivity,
KMS passivity, Markov positivity, or positive carrier order, because each occurs with wrong or
undetermined wall orientation (`FactorialPositiveCarrierOrientationNoGo`, HB/RBH no-gos).

CANNOT-04 — It cannot be a norm, square, energy, absolute value, phase quotient, or projective
class alone, because these retain size while erasing the reflection-odd sign that distinguishes
the wall (`PhaseCancellationAffineCurvature`, EWQ scalarization no-gos).

CANNOT-05 — It cannot be FE pairing, involution, path coherence, or conjugacy alone, because those
transport off-line data without identifying the paired points (`EntireFunctionalEquationOffLine`,
Gamma-cover composition laws).

CANNOT-06 — It cannot be common recovery, invertible re-encoding, gauge transport, or naturality,
because exact recovery preserves all distinguishing information (`ConstitutiveAsymptoticLawCore`,
`ConstitutiveFunctionalEquationPacketLift`).

CANNOT-07 — It cannot be recurrence, periodicity, finite-state stationarity, or closed observation,
because recurrent quotients coexist with linearly escaping lifted history (`ConstitutiveTimeReversalLikelihoodCocycle`,
`WeightedHistoryCompletionBoundaryLaw`).

CANNOT-08 — It cannot be self-adjointness, unitarity, spectral realization, or Hilbertization alone,
because arbitrary real spectra have self-adjoint realizations and faithful unitary realization can
erase or reject source translation (`CountableSpectralHamiltonianRealization`,
`ConstitutiveUnitaryJordanFormationFracture`).

CANNOT-09 — It cannot relocate a weak-Schatten-one source to the ordered reciprocal-ordinate Xi operator by bounded left/right mixing plus a trace-class correction (`RoutePPrimitiveGammaJuliaLogWeakTraceMixingNoGo`). The target is outside weak Schatten-one. This excludes that ideal-preserving transport class, not compact operators, Fredholm determinants, Sobolev methods, or every source completion; F663 gives two additional concrete source-budget exclusions.

CANNOT-10 — It cannot be boundedness, contractivity, dissipativity, or nonexpansivity alone,
because these either hold off line or have the passive polarity opposite to required source sign
(HB dissipative-response and source-nonexpansive no-gos).

CANNOT-11 — It cannot be ordinary cohomological exactness, Hodge contraction, Cartan contraction,
or derived contractibility, because the off-line curved Gamma suspension is explicitly
contractible (`SourceHorizontalGammaSixCurvedSuspensionHodgeTrace`, scalar Cartier wall).

CANNOT-12 — It cannot be total square-zero/flatness alone, because a flat block law can hide visible
curvature in complementary coupling products (`NomologicalGaussCodazzi`).

CANNOT-13 — It cannot be bare `L_infinity`, Maurer--Cartan, Gauss--Codazzi, filtration, or degree
lowering language, because those mechanisms are already formalized and do not restrict which
corrections exist (`SplitLInfinityObserverExtension`, `ConstitutiveCohomologicalDegreeLowering`).

CANNOT-14 — It cannot be a single scalar polynomial law combining route invariants, because
descent, conservativity, and properness ranks vary independently (`NomologicalThreeOrganIndependenceLaw`).

CANNOT-15 — It cannot be diagonal, marginal, one-leg, rank-one, or source-independent mixing,
because orientation lives in off-diagonal interaction and arbitrary diagonal responses are
nonselective (EWQ replica scalarization, HB arbitrary-response no-gos).

CANNOT-16 — It cannot be fixed linear normalization, common scalar counterterm, parity
symmetrization, or holomorphic unitization, because exact coefficient-faithful source reservoirs
still have wrong jet or polarity (`SourceHorizontalHolomorphic*Cofinal*NoGo`).

CANNOT-17 — It cannot be local, jointly holomorphic complex-bilinear, finite-exponential-type,
finite-variation, or polynomially tempered response, because these classes are explicitly closed
off (`FZZSchwarzschildPhysicalResponseFiniteTypeNoGo`, FZZ/HB reflection no-gos).

CANNOT-18 — It cannot be regular compact-open or upper-semicontinuous descent, because escaping
off-line bubbles converge to the same visible limit while retaining quantized charge
(`XiHeatCassiniWoldOrbitCharge*NoGo`).

CANNOT-19 — It cannot be finite-stage exactness or stagewise exhaustion, because every finite
history can be exact while a nonzero completion phantom survives (`RouteRCompletionPhantomNoether`,
`EulerCutoffTailRoosStagewiseExhaustionNoGo`).

CANNOT-20 — It cannot be an arbitrary adaptive/endogenous compatibility law, because one endogenous
test can realize every transition system (`ConstitutiveEndogenousCompatibility`).

CANNOT-21 — It cannot be unrestricted cross-prime coupling or determinant fitting, because additive
cross-prime matrices are dense in every normalized even entire target and therefore cannot select
RH (SC additive two-port universality in frontier map).

CANNOT-22 — It cannot be perfectification, commutator killing, or declaration that Gamma normal is
a Steinberg boundary, because its Kummer regulator is nonzero and it lies outside Steinberg ideal
(`deningerGammaSixOrientedEscape_not_mem_steinbergIdeal`).

CANNOT-23 — It cannot be hypertranscendence alone, because freedom/noncompactness creates directions
but no relation that kills their off-line charge (HT freedom laws plus positivity/orientation
no-gos).

CANNOT-24 — It cannot be a global no-phantom, source-normal landing, cofinal boundedness, positive
kernel, selector, or semistability premise already proved equivalent to RH (`endpoints.md`).

CANNOT-25 — It cannot fit a representation, metric, response, gauge, or correction separately at
each Xi zero, because arbitrary target realization is nonselective and merely reads divisor data
(HB arbitrary-incidence/response and source-independent Krein no-gos).

CANNOT-26 — It cannot be cross-route fusion or exact transgression alone, because history, theta
flux, Gamma skew, dagger curvature, entropy, and affine residue are already exact coordinates of
one defect for every horizontal grade (`XiHistoryThetaGammaAmbidexterityTransgression`).

CANNOT-27 — It cannot be a two-axis node, mixed master equation, or second-order coherence law,
because the grade--phase versions are already proved exactly RH-equivalent
(`XiNodalDefectSuperselection`).

CANNOT-28 — It cannot be least action, minimum energy, or canonical optimization unless objective
is fixed independently of repair, because every selector is uniquely optimal for a manufactured
positive cost (`ConstitutiveRepairTorsorSelectorNoGo`).

CANNOT-29 — It cannot work only modulo almost-everywhere equality or global `L²`, because isolated
divisor shells are invisible there (`ThetaCuspHawkingGlobalL2ShellBlindnessNoGo`,
`L2PointSamplingNoGo`).

CANNOT-30 — It cannot infer analytic execution from algebraic generation, because exact two-prime
Bezout generation coexists with absence of uniformly bounded synthesis
(`HedenmalmTwoPrimeBezoutGrowthNoGo`).

CANNOT-31 — It cannot be any all-order local shape rule, because a complete local Bernstein tower
and arbitrary finite critical prefixes coexist with later global sign failure
(`LiEvenCrossLocalBernsteinShapeNoGo`, finite-prefix oscillation no-go).

CANNOT-32 — It cannot be singularity, non-Fock realization, reflection unitarity, or finite source
energy alone, because all coexist with arbitrary positive even divisor density
(`FZZParitySingularWeightedHilbertDensityNoGo`).

CANNOT-33 — It cannot choose phase from divisor amplitude, because an amplitude-following unit
gauge makes off-line cocycles positive real (`BMRadiativeSourceFEUnitPhaseRealificationNoGo`).

CANNOT-34 — It cannot assume every conservative repair system has a scalar progress functional:
collective repairs cross a sharp threshold where a positive closed circulation exists and every
strict scalar progress certificate fails (`ConstitutiveCollectiveRepairThreshold`).

CANNOT-35 — It cannot be another abstract universal-law formalism detached from arithmetic:
strictification, promotion, higher coherence, reconstruction, properness, recurrence, positivity,
and interaction spectra already have certified unconditional capstones (`_LEAN-CERTIFICATION.md`).

CANNOT-36 — It cannot identify the compact prime-packet inverse limit with the analytic graph
completion or infer boundary-freeness from compactness: explicit literal source packets converge
to a nonzero vertical graph boundary while disappearing in ambient `ℓ²`.

CANNOT-37 — It cannot infer complex divisor control from the exact real-axis Möbius–theta `L²`
landing. Almost-everywhere Plancherel equality and absolute `L²` codiagonal summability do not make
off-axis point evaluation continuous.

CANNOT-38 — It cannot be another faithful conversion among Möbius inversion, von Mangoldt
logarithmic differentiation, theta/Gamma Mellin transport, Witt ghosts, or finite Čech/Koszul
faces. Those conversions are already exact and retain rather than annihilate the cofinal
obstruction.

CANNOT-39 — It cannot be finite Lee–Yang localization or a finite Euler functional equation.
Both already place finite zeros on the centered wall after their respective coefficient
normalizations; the absent statement is a source-derived cofinal completed-Xi comparison.

CANNOT-40 — It cannot obtain that comparison as a locally uniform limit of finite prime-labelled
ferromagnetic Ising trees, even after scalar centering or balancing. The unbalanced, centered,
even/Schwarz-real normalized, and fully balanced tree families are already excluded by exact
first-jet and modal-rank no-gos.

CANNOT-41 — It cannot be fairness, cofinal schedule independence, contour choice, or reordering
alone. Corrected literal prime-contour schedules already have one schedule-independent limit both
under RH and under failure of RH; only the sign of that common limit is selective, and that sign is
RH-equivalent.

CANNOT-42 — It cannot be an error-correction or syndrome reinterpretation by itself. The complete
multi-route syndrome and its logical-sector classification are already exact; asserting its global
absence, infinite distance, or universal correctability merely restates an RH-equivalent endpoint
unless derived from an independent pre-divisor source law.

CANNOT-43 — It cannot be a secondary-height or self-intersection slogan whose global zero identity
is postulated. Positive local Hodge energies and quantized global reflection charge already exist;
the missing theorem is exactly an independent arithmetic reason that total off-line charge is below
its first nonzero quantum—or zero—and that assertion closes RH.

CANNOT-44 — It cannot be additive–multiplicative covariance, a flat prime-translation connection,
common reflected forcing, or annihilation by all retained divisor characters alone. Those laws
already hold while the two reflected source responses remain distinct off line; demanding their
equality is itself the RH-selective endpoint.

CANNOT-45 — It cannot infer real-rootedness from positivity of every reflected Hankel square plus
strict finite Hankel rank: an explicit positive real entire source satisfies all those conditions
and has a nonreal zero.

CANNOT-46 — It cannot remove an unavoidable finite scalar packet by a finite source-faithful
counterterm. Exact interval cancellation forces coefficientwise deletion of the source itself.

CANNOT-47 — It cannot make exact quadratic divisor charge continuous by weakening compact-open
descent to either upper or lower semicontinuity. Escape breaks the upper direction and multiplicity
collision breaks the lower direction.

CANNOT-48 — It cannot use finite-graph-energy pointwise Hilbert compensation, even with infinite
rank and an arbitrary unbounded, nonclosable, non-self-adjoint, or partially defined metric action.
The literal pre-divisor susceptibility forces inverse-square hard-edge energy divergence in at
least one leg.

CANNOT-49 — It cannot place an infinite algebraic heat spectrum inside an everywhere-entire,
differentially algebraic periodic fibre. In that class the spectrum is forced finite.

CANNOT-50 — It cannot infer full lifted state from an autonomous composite shadow. Exact
transcendence-degree accounting shows that autonomy can compress the primitive coordinate.

CANNOT-51 — It cannot use global determinant unitarity or paired Hermitian-dual purity. Pairing
makes these identities hold at every horizontal grade while constituentwise purity remains
selective.

CANNOT-52 — It cannot infer annihilation from completed smoothness or zero total anomaly. Exact
relative multiplicity and Ward characters survive in the resolved antidiagonal.

CANNOT-53 — It cannot absorb a nonzero all-orders-flat source charge into an analytic Taylor/Rees
germ. Quasianalyticity forces every such analytic germ locally zero.

CANNOT-54 — It cannot obtain global orientation or height growth from a removable pole-clearing
gauge. The exact boundary functional cancels that gauge on every rectangle avoiding its zero.

CANNOT-55 — It cannot be refinement conservation, relative seam transgression, or telescoping
alone. Those laws already classify where cancelled mass moves but impose no source bound or
vanishing on the new seam.

CANNOT-56 — It cannot interpret a zeta zero as total source extinction, vacuum, or death of an
entire recursive tower. The literal heat–aperture lift keeps every strict rung nonzero when its
zeroth observed rung vanishes.

CANNOT-57 — It cannot postulate FE–Schwarz lift uniqueness, branch confluence, one-prime matching,
all-prime matching, Euler-flux matching, or Euler-tangent matching at a zero. Each is already a
faithful coordinate of horizontal grade, hence an RH-selective receiver rather than a source law.

CANNOT-58 — It cannot derive the required reflected-Hankel orientation from positivity of an entire
source, a negative central Schrödinger potential, and monotonicity of that potential. Those data
admit an explicit negative rank-three determinant.

CANNOT-59 — It cannot be another formation, execution, completion, history, properness, or operation-
descent vocabulary whose only theorems preserve, forget, or repackage the already-realized anomaly.
Those mechanism classes and their conditional selectors are already present.

CANNOT-60 — It cannot use base-preservation or verticality alone as a no-selection criterion.
Vertical equalizers can have support only at neutral grade.

CANNOT-61 — It cannot call a compatibility law source-generated merely because it depends on source
state. An unconstrained state-indexed test can encode any desired transition relation.

CANNOT-62 — It cannot be bare logical noncompactness, cofinal birth, counterwitness escape, global
divisor tomography, or source scale properness. Each already exists in exact form and terminates at
an unproved literal-source vanishing or boundedness statement equivalent to RH.

CANNOT-63 — It cannot be a renaming of noncommuting limits as Interfinity geometry or of the
critical half-density as semiring/ax+b unitarity. Both mechanisms and their exact selector
interfaces already exist; the occurrence-to-unitary or source-exactness theorem remains open.

CANNOT-64 — It cannot be simple pole order, entire order one, positive generalized primes, or any
power-scale regularity of generalized integer counting. Explicit off-line systems satisfy each of
these separately, and the Beurling system satisfies simple-pole plus arbitrarily sharp counting
regularity simultaneously.

CANNOT-65 — It cannot be integral multiplicative coefficients plus a freely varying nonvanishing
Gamma factor and functional equation. That class is convolution-mobile and carries simple
off-line charge.

CANNOT-66 — It cannot infer a positive selector from joint interaction merely because the source
or a replica is positive. Passing to the interaction quotient can create an indefinite form.

CANNOT-67 — It cannot select neutral grade from static standard-integer additive/multiplicative
coherence, coefficient relations, or KMS compatibility. Power characters carry every real grade
through the exact formation diamonds, and source relation matroids are Gibbs-temperature blind.

CANNOT-68 — It cannot obtain a contradiction by representing one anomaly in many routes, tensor
replicas, or source labels. Rank and integer charge can be amplified algebraically, while labelled
indefinite rank can cost arbitrarily small norm; no unconditional finite literal-source budget has
been proved.

CANNOT-69 — It cannot be termination, acyclicity, or semantic completion of finite source rules.
Well-founded finite execution coexists with persistent nonconfluence, and conservative addition of
missing joins can reveal new failures without narrowing the semantic model class.

CANNOT-70 — It cannot identify ordinary integer addition with Dirichlet convolution and then use
initial-semiring or vanishing-cotangent rigidity. Horizontal grade is a genuine derivation of the
Dirichlet algebra; forcing it to descend to the initial semiring discards the analytic source
interaction and inserts the desired vanishing as an unsupported quotient.

CANNOT-71 — It cannot select neutral grade from existence, divergence, or canonical scalar
renormalization of the balanced source/co-source cross-term. The divergence occurs at every
horizontal split, and codiagonal contraction forgets the relative grade before continuation.

CANNOT-72 — It cannot quantize the unnormalized BV--Wold triangle curvature as a lattice period.
The full clock-retaining transport is pure gauge and flat at every grade; demanding centered-log
descent or a differential-character lift inserts the missing RH-equivalent premise.

CANNOT-73 — It cannot select the critical line by assuming a conservative reflection-Tate charge.
Conservativity is exactly fixed-locus support, and existence of a conservative Xi landing is an RH
restatement rather than a pre-divisor source law.

CANNOT-74 — It cannot infer bounded or proper cofinal formation work from finite generation, local
exchange identities, or information-neutral functional-equation lifting. Nonzero local mismatch
accumulates linearly, and the required global boundedness is already equivalent to neutrality.

CANNOT-75 — It cannot force neutral grade by declaring the Mellin radial action to be a common
automorphism of additive and Dirichlet packet fusion. Common-gauge rigidity is true, but the
additive-automorphism lift is not generated by Xi source formation and would insert the conclusion.

CANNOT-76 — It cannot select a response from existence or uniqueness of its minimal realization,
canonical context quotient, or generated marked intertwiner. Those constructions exist for every
complete response, including functional-equation-symmetric responses with nonzero hidden charge.

CANNOT-77 — It cannot infer “no determinant line” from dimension greater than one of ambient
exterior target. Formation's actual range canonically supplies a one-dimensional determinant line
whose faithful image is exactly Pluecker line.

CANNOT-78 — It cannot recover determinant-line orientation or holonomy from Gram positivity. Norm
squared identifies all unit phases and survives sign reversal of source frame.

CANNOT-79 — It cannot obtain selection by renaming horizontal defect as nonnegative dissipated
action and assuming a recurrent source potential. That is existing conditional Xi recurrence
endpoint, not source production.

CANNOT-80 — It cannot obtain selection from ordinary holonomy of one globally framed finite range
determinant line. Finite gauge changes produce determinant characters/coboundaries, while existing
Xi determinant holonomy is already only a wall classifier.

CANNOT-81 — It cannot treat determinant lines of rank-growing stages as an ordinary directed system
under exterior powers of stage inclusions. Same-degree maps preserve old wedge; new top-degree map
has zero old source and misses new determinant line.

CANNOT-82 — It cannot obtain selection by replacing determinant line with determinant gerbe,
2-gerbe, higher commutator, or bifiltered determinant interchange alone. Those generic carriers
already encode higher anomalies, while internal reflected determinant/index laws remain
nonselective.

CANNOT-83 — It cannot infer unit determinant transport from FE involutivity, common recovery, or
information neutrality. Reflected source cocycles are inverse-paired at every grade, and bilateral
properness is itself a selector premise.

CANNOT-84 — It cannot use quadratic growth of raw marked-edge reflection multipliers as invariant
conditioning or curvature. Source-visible rank gauge linearizes it exactly; any bound in raw frame
requires an independently proved source-fixed gauge prohibition.

### It must do or have this

MUST-01 — It must be defined on pre-divisor source data and specialize at Xi occurrences only after
its law is proved.

MUST-02 — It must distinguish fixed arithmetic source occurrence from generic spectral or scalar
occurrence, because generic occurrence is universal (`FZZCigarPunctureTemperedScalarOccurrenceNoGo`).

MUST-03 — It must retain reflection-odd orientation, not reconstruct it from positive or projective
data after quotienting.

MUST-04 — It must retain analytic multiplicity and prime/depth labels, because marginal
multiplicities and source marking survive the no-gos.

MUST-05 — It must act before smoothing, averaging, scalarization, completion, or phase quotient,
because those operations preserve, export, or erase the needed sign.

MUST-06 — It must be cofinal and whole-history, because every fixed finite depth/window/observer is
nonselective.

MUST-07 — It must permit genuinely infinite-rank, noncompact, singular, non-Fock, distributional,
or multivalued behavior, because the audited regular finite/bounded/Hilbert comparison classes are
closed while these classes remain unexcluded.

MUST-08 — It must contain at least two directed legs and a mixed interaction, because one-leg and
diagonal laws cannot carry the required orientation.

MUST-09 — It must control higher interaction order, because linear source-reversal defect is exact
off line while quadratic curvature survives (`DeningerFailureNerveMixedDaggerCoboundary`).

MUST-10 — It must state where obstruction goes under every legal transformation: faithful maps
conserve it, lossy maps expose a kernel, and completions export it as horizon charge.

MUST-11 — It must constrain hidden complementary couplings, because otherwise they can cancel any
visible curvature inside a flat total law.

MUST-12 — It must classify all source-generated corrections by an exhaustive normal form, because
one unclassified correction makes every claimed selection theorem conditional.

MUST-13 — It must derive admissibility from source grammar rather than add compactness, positivity,
normality, source-faithfulness, or properness as a new premise.

MUST-14 — It must couple prime, archimedean/Gamma, FE orientation, depth, and completion history in
one law, because each isolated organ has explicit off-line models.

MUST-15 — It must use the existing joint conservation/transgression web as input; reproducing it,
mapping its terms, or proving another shared zero locus is not a new result.

MUST-16 — It must predict an exact quantitative theorem outside the already-proved transgression
web before any RH consequence is trusted.

MUST-17 — It must survive generalized-prime and freely fitted off-line countermodels by using a
rigidity special to the literal arithmetic source, not to Xi-labelled targets.

MUST-18 — It must turn noncompactness into a constraint on possible laws, not claim that
noncompactness itself forces vanishing.

MUST-19 — It must explain why local exactness is abundant while global selection fails: obstruction
is raised in interaction degree or exported to cofinal history rather than destroyed.

MUST-20 — It must prove that every allowed off-line cancellation loses required source data or
leaves a nonzero conserved charge; naming that dichotomy is not enough.

MUST-21 — It must force `K(a)=0` without assuming any statement already equivalent to `a=0`; only
then may existing `K(a)=0 <-> a=0` close RH.

MUST-22 — It must identify whether each ingredient is unconditional transport, conditional
selection, or a positive survivor; moving a theorem between those logical classes is forbidden.

MUST-23 — Any cost, norm, phase reference, topology, or admissible class it uses must be fixed by
literal source data before choosing a repair or Xi divisor.

MUST-24 — Its topology must retain isolated occurrence, multiplicity, orientation, and provenance;
an `L²` or almost-everywhere quotient is insufficient.

MUST-25 — It must distinguish algebraic formation from executable formation and prove any needed
boundedness, convergence, or completion statement rather than infer it from a formal relation.

MUST-26 — It must retain joint prime/depth or grade/phase incidence rather than separate scalar
marginals (`BifilteredScalarizationNoGo`).

MUST-27 — Any local-to-global step must contain an essential infinite nonuniform tail mechanism;
finite prefixes, fixed jets, and finite moment towers cannot supply it.

MUST-28 — It must distinguish intrinsic signed anomaly from repair debt and account separately for
rank, conditioning, variation, singularity/domain, interaction order, provenance loss, and history
escape until exact exchange laws between them are proved.

MUST-29 — If it invokes bounded work, compactness, properness, exact exchange, integrable potential,
or closed history, it must prove that property unconditionally for the pre-divisor arithmetic
source; importing it at Xi fibres is an RH endpoint.

MUST-30 — Its decisive implication must be a theorem about literal source execution, not another
faithful coordinate of horizontal grade and not a condition attached separately to each zero.

MUST-31 — Any passage from the proved physical Möbius–theta landing to complex divisor occurrence
must construct an occurrence-sensitive source topology and prove the required execution map in
that topology; importing barrelledness, pointwise boundedness, or closed graph is terminal.

MUST-32 — It must add a source-proved constraint on the cofinal joint execution of the existing
Möbius–von-Mangoldt–theta/Gamma calculus; another identity, transform, resolution, or homology
model of that calculus is not selection leverage.

MUST-33 — Any scalar charge passed through collision or completion must be linearized before the
passage, or its nonlinear collision defect must remain as source-marked noncompact boundary data.

MUST-34 — If it uses an everywhere-entire periodic heat carrier with algebraic amplitudes, its
infinite arithmetic spectrum requires a hypertranscendental spatial fibre or departure from that
carrier class.

MUST-35 — Any phase quotient, determinant, completion, or codiagonal observation must retain the
resolved constituents and their relative character; the total object alone is provably blind.

MUST-36 — Its decisive source theorem must restrict the anomaly fibres arithmetically realizable by
Xi occurrence. Explaining the internal geometry of every fibre, or transporting an occurrence
within its existing fibre, cannot be the selection step.

MUST-37 — If selection is expressed by an equalizer, fixed locus, compatibility locus, or vanishing
locus, the source must generate both compared responses and the obligation relating them before
Xi occurrence specialization; defining the locus after reading horizontal grade is an endpoint.

MUST-38 — A claimed source law needs a fixed occurrence-independent signature and uniform
derivation rule. State-indexed predicates, chosen equalizers, and arbitrary compatibility oracles
are logically capable of storing RH rather than proving it.

MUST-39 — A higher theory must distinguish information-conservative re-expression from a theorem
that narrows the literal source model class. Route equivalence, full-divisor aggregation, cofinal
completion, and properness can expose the exact missing proposition without supplying new evidence
for it.

MUST-40 — A claimed proof advance must identify the exact previously unproved statement it
establishes and its place in the proposed chain. New terminology, an equivalent formulation, or a
new realization alone does not establish that statement. A speculative architecture may precede
such a theorem, but must identify its missing links.

MUST-41 — Must check that the same countermodel satisfies every hypothesis before excluding a
proposed proof mechanism. A continuous example does not eliminate methods requiring discrete
ordinary integers. Matching selected asymptotic estimates does not establish that exact integer
occurrence or addition–multiplication distributivity is mandatory for all RH proofs.

MUST-42 — A proposal claiming new information from combined arithmetic operations must exhibit
what their joint use adds. Separate marginal identities do not by themselves prove a joint
constraint. Existing finite-prime blindness and higher-interaction examples do not establish that
every possible RH proof must use an additive-successor/prime-power history invariant.

MUST-43 — Any decisive capacity must be nonhomogeneous under source-respecting rescaling, invariant
under presentation by routes or replicas, and impossible to manufacture by matrix amplification or
erase by balanced reflection. Its finite total budget must be proved from literal source formation,
not assumed at the Xi divisor.

MUST-44 — A proposal using interaction between additive and multiplicative constructions must
prove the claimed interaction law for its actual arithmetic objects. Compatibility of separate
models, marginal positivity, or a formal direct sum cannot substitute for that law. This is a
requirement on such proposals, not a universal prescription for RH proof architecture.

MUST-45 — A cross-effect selector must retain the two oriented legs and at least one asymmetric
third incidence before codiagonal pairing. Any law depending only on the paired sum, total trace,
or balanced divergence is radial-gauge blind.

MUST-46 — Selection must distinguish existence of the always-flat resolved source transport from
existence of a canonical source-compatible reduction of that transport. Any reduction, splitting,
integral structure, or descent used here must be generated before choosing a Xi divisor and must
not be equivalent by definition to neutral horizontal grade.

MUST-47 — Any quotient charge used for selection must prove from literal source formation why the
source marker cannot become a norm, boundary, or free-orbit export; conservative reconstruction
cannot be assumed.

MUST-48 — Any formation selector must derive a cofinal non-escape or work bound from the literal
pre-divisor source. Finite rule count, termination, local conservation, and stepwise
information-neutrality do not imply that global bound.

MUST-49 — A two-operation selector must construct from literal source execution the same action on
both operations. Classifying the intersection of their symmetry groups is useful only after this
occurrence theorem; membership in the intersection cannot be imposed as compatibility.

MUST-50 — It must constrain which complete responses literal arithmetic can generate, not merely
reconstruct a chosen response or prove equivalence of its presentations. Realization minimality is
downstream of response admission.

MUST-51 — A route-independent formation geometry must transport canonical determinant line of
actual source-generated range; ambient scalarizations, Gram norms, and chosen frame coordinates are
only gauges or quotients.

MUST-52 — A determinant-line RH architecture must identify existing source-forced horizontal
charge with cofinal formation holonomy and prove from literal pre-divisor execution that source
completion trivializes that holonomy. Choosing a trivialization or assuming flatness inserts the
selection conclusion.

MUST-53 — If recurrence is used, literal source formation must construct exact nonnegative ledger,
its cofinal recurrence, and Xi landing before divisor specialization; recurrence rigidity itself is
already solved.

MUST-54 — Any determinant obstruction with selection force must survive absence of one global
finite gauge: cofinal or singular gluing, rank-changing relative determinant transport, or failure
of global nonvanishing section. Source must prove its trivialization rather than assume it.

MUST-55 — A rank-growing formation theory must attach canonical quotient determinant increment to
every strict source refinement and prove fusion/cocycle laws for accumulated increments; chosen
complements or frame orientations are not source-native.

MUST-56 — To identify hypertranscendence with determinant noncompactness, it must prove actual
literal source tower has unbounded independent rank and that its quotient determinant history
cannot stabilize or escape into a forgotten boundary. Rank-jump algebra alone is insufficient.

MUST-57 — Since actual source rank growth and canonical quotient increments are now proved, any
determinant-history selector must construct source/reflection transport on those literal quotient
generators, identify its accumulated class with existing horizontal Xi charge, and prove
pre-divisor source completion trivializes it. Generic gerbe existence is insufficient.

MUST-58 — Marked source reflection transport has exact quadratic distortion only in raw rank frame.
Any resulting architecture must first prove that frame source-canonical against all legal rank
gauges; otherwise subquadratic conditioning is coordinate-dependent and cannot select.

MUST-59 — Decisive formation invariant must survive every source-legal rank gauge, or prove from
literal pre-divisor arithmetic why gauge fails to extend across a second formation operation.
One-leg determinant growth and reflection character alone are insufficient; mixed cross-effect is
required before Xi specialization.

F156 — Natural-rank trivializer `(z^-1)^m` is restriction of bilateral sewing history
`g_z(e)=z^(-e)`. It algebraically trivializes every nonzero literal-source character, but is
polynomially moderate exactly when `|z|=1`.

F157 — Same bilateral history trivializes actual depth-12 marked source execution, while character
inversion acts by rank reversal `g_(z^-1)(e)=g_z(-e)`. For half-density character
`p^(1/2-s)`, admissibility is exactly `Re s=1/2`.

CANNOT-85 — It cannot use ordinary algebraic coboundary class of source reflection as selector:
class vanishes for every nonzero character, including off-line ones. Obstruction survives only
after source-admissible gauges are fixed.

MUST-60 — Higher theory must specify admissible gauge sheaf/bornology before Xi occurrence and
prove literal formation places canonical rank primitive in it. Post-divisor moderation or a gauge
class chosen from horizontal grade is RH restatement.

F158 — On directed ranks, actual marked formation `F_z(m)=z^m(1-z)` is moderate iff `|z|<=1`,
while exact recovery `R_z(m)=z^(-m)` is moderate iff `1<=|z|`; their pointwise product is constant
`1-z`. Joint formation/recovery moderation is therefore exactly `|z|=1`.

F159 — Same joint law holds for actual depth-12 marked source channels. At half-density character
`p^(1/2-s)`, joint directed properness is exactly `Re s=1/2`; bilateral completion is not needed.

CANNOT-86 — It cannot treat exact or information-neutral recovery as topological admissibility.
Recovery may preserve every datum while carrying exponential rank cost opposite to formation.

MUST-61 — A source proof may target one occurrence-independent bornology making actual formation
and its canonical recovery jointly polynomially controlled. Separate zero-dependent norms, or
continuity of only one leg, leave an entire off-line chamber.

F160 — Finite Laurent packets `C[Z]` with coefficient `ell^1` form a coefficient-native Hopf
envelope for directed formation and inverse recovery. Actual edges satisfy the exact algebra law
`T^(-m) * (T^m - T^(m+1)) = 1 - T`, independent of rank.

F161 — Evaluation characters of this bilateral Wiener source are bounded exactly on the unit
circle. Half-density evaluation `T |-> p^(1/2-s)` is bounded exactly when `Re(s)=1/2`.

CANNOT-87 — It cannot use algebraic Hopf extension alone as selector: evaluation extends
algebraically for every nonzero character. Selection requires boundedness in one source-fixed
coefficient norm, not an annular or zero-dependent weight.

MUST-62 — Higher theory must derive an occurrence-independent bounded Xi packet evaluation on a
coefficient-native Laurent completion before divisor specialization. Choosing the completion from
the target horizontal grade is circular.

F162 — Bilateral Wiener boundedness, fixed-star positivity, integral Cartier recovery, compact
recurrence descent, and two-sided bounded orbit are already equivalent neutral-grade receivers.
They expose one modular character in different completions; none supplies its arithmetic producer.

CANNOT-88 — It cannot obtain new selection by combining functional-equation inversion with a
Wiener/C-star completion, positive representation, closed-loop holonomy, or two-sided power
boundedness. Corpus already proves each rigidity implication; asserting Xi admission is RH-equivalent.

MUST-63 — Must derive every summation, continuity, positivity, boundedness, or passage-to-limit
claim needed by the chosen proof, with its hypotheses satisfied by ordinary zeta. Countermodels
for broader source classes do not require every new mechanism to use a prescribed integer
execution, a particular pair of operations, or a fixed order of analytic completion.

F163 — Categorical-dimension/integrality and singular multivalued-correspondence pivots are already
represented. Integral centered monodromy is a wall receiver; closed relations can become fully
vertical or source-nonselective, and relation excess alone does not orient the Xi occurrence.

CANNOT-89 — It cannot infer neutral grade by declaring the horizontal character a finite-set
dimension, semiring character, additive automorphism, or correspondence representation. Existence
of that lift is the missing occurrence theorem; regular and multivalued versions already terminate.

MUST-64 — A distributive-source mechanism must construct its mixed action from literal coefficient
execution itself and prove a new unconditional restriction on realizable response laws. Merely
requiring the multiplicative character to respect addition stores the desired neutrality.

F164 — Horizontal grade is the rapidity of reciprocal reflected transport. The corpus's `tanh`,
`sech`, `artanh`, `sinh`, and `cosh-1` laws are velocity, visibility, additive rapidity, oriented
current, and boost energy of the same rank-two hyperbolic block; they are not separate mechanisms.

F165 — The cofinal theta Green boundary has fixed mixed inertia `(1,1)`, while finite Krein--Langer
forms assign one negative square to each off-line pair. Thus the RH-bearing invariant is not raw
positivity or raw inertia but excess/relative negative index above the universal hyperbolic block.

CANNOT-90 — It cannot polarize away the fixed negative theta boundary mode. Actual stage boundaries
remain uniformly separated from both positive and negative cones cofinally; the mixed block is
vacuum geometry, not an off-line defect.

MUST-65 — Required producer is source-native relative-index properness: define the vacuum-subtracted
index before divisor specialization, prove literal finite stages have zero excess, and prove no
negative-index birth or escape under arithmetic completion. An exact identification of its limit
with Krein--Langer off-line-pair count would then close RH.

F166 — Vacuum-subtracted Krein index is not continuous in compact-open or all-jet compact-open
topology. Explicit analytic families retain any prescribed extra negative-square count while
converging locally uniformly, with every derivative, to a lower-index limit.

CANNOT-91 — It cannot prove RH by ordinary relative-index conservation or a norm-continuous exact
index. Negative directions can migrate to infinite height; lower index lies in the closure of every
higher finite index stratum.

F167 — The escaped index is already reconstructed as one singular principal class by Gamma-six
boundary jets, prime-normal double-log energy, adaptive Green codiagonal zeros, and reflected
Kakutani flux. Global zero escape class/properness is equivalent to RH.

CANNOT-92 — It cannot advance by adjoining one boundary point, tail mass, or ``index at infinity''.
Corpus already has that receiver and its four-organ reconstruction; vanishing remains the producer.

F168 — Multiple compact gauges do not block escape: any two compact reporters on an
infinite-dimensional Hilbert source share an orthonormal null sequence. Noncompactness or positive
essential norm alone also fails because a noncompact reporter may have infinite-dimensional kernel.

CANNOT-93 — It cannot obtain properness by stacking finitely many compact completions or by adding
an arbitrary noncompact boundary channel. Required invariant is essential coverage, not visibility.

F169 — Literal critical Stokes formation has source winding `-1`; completed prime--Gamma flow is
joined to it by a zero-avoiding homotopy on the real chamber and has the same Fredholm winding.
Separately, the unilateral-shift law identifies recurrent boundary observation, open defect history,
defect rank, and Toeplitz boundary index.

F170 — Fixed Fredholm winding does not constrain Krein negative squares. Arbitrary finite negative
spectator blocks may be added without changing essential Toeplitz index. Existing arithmetic-prime
Fredholm operator is selected from integer grade, not constructed coefficient-faithfully from the
full literal source.

CANNOT-94 — It cannot equate source winding with off-line count without a completeness theorem.
That equality is false for a source shift direct-summed with invisible finite Krein spectators.

MUST-66 — Completion-index route requires arithmetic asymptotic completeness: construct one
pre-divisor, coefficient-faithful source wave operator; prove its quotient/scattering class is the
fixed source winding; prove its cokernel is exhausted by the universal theta vacuum line plus the
Xi Krein negative space. Then index `-1 = -(1 + k)` forces off-line count `k=0`. Until this operator
and exhaustion law are explicit, ``arithmetic Levinson'' is a research question, not a conjecture.

F171 — Literal all-prime pre-divisor source already has one exact Witt/Pontryagin defect: on every
left fibre its rigged form has exactly one negative square modulo the coefficient radical, while
reflection negates the form and gives one positive square on the right. A canonical two-prime time
axis and real-linear fundamental symmetry polarize it unconditionally.

F172 — Right source fibres also contain finite prime restrictions with arbitrarily large negative
index. Hence absolute source index one cannot bound Xi off-line index: only a one-sided relative
polarization/completion index could connect the left source vacuum to right-divisor defects.

CANNOT-95 — It cannot identify the universal `(1,1)` Green block with a globally index-one source
space and conclude RH by index monotonicity. Reflection reverses source orientation, and the
opposite source chamber already has unbounded negative index.

F173 — Honest finite theta source operators converge in norm and their determinants converge
compact-open to normalized Xi, but every exact metric-adjoint repair escapes canonical theta
polarization. Generic hyperbolic doubling preserves all source traces yet only Schwarz-doubles the
divisor; chiral selection restores the original zeros rather than moving them to the line.

CANNOT-96 — It cannot use generic Krein self-adjointization, metric rescaling, or projective
polarization as completion selector. These exist for every finite source matrix and preserve
nonreal divisor data exactly.

MUST-67 — The precise candidate invariant is relative completion index: index of the Fredholm pair
between source-selected and divisor/Hardy polarizations, vacuum-normalized by the fixed rank-two
Green cell. To close RH it must be constructed coefficient-faithfully before Xi specialization,
proved proper/no-escape, and identified with Krein--Langer off-line count. Absolute inertia is the
wrong invariant.

F174 — Multiplicity is no longer an obstruction to a completion index. The corpus has a complete
confluent Cauchy basis for each finite Hardy negative model and exact multiplicity-aware
Krein--Langer counts. Repeated zeros contribute independent jet channels rather than repeated value
features.

F175 — One boundary channel does not imply index one. Scalar generalized-Schur functions have
arbitrary finite negative-square count, and one scalar scattering channel can have arbitrary
winding/bound-state number. The one-dimensional Gamma-six singular boundary likewise records
off-wall charge but collapses all Xi labels onto scalar multiples of one boundary vector.

CANNOT-97 — It cannot derive RH from dimension of the universal completion boundary or uniqueness
of the fixed `(1,1)` Green cell. Boundary-channel rank and bound-state/Krein index are independent;
the missing datum is degree/asymptotic completeness, not channel dimension.

F176 — The corpus separately has (i) a literal one-prime Hardy Fredholm cycle of index `-1`, stable
under compact completion, (ii) a one-line arithmetic formation boundary detecting every off-line Xi
copy, and (iii) a multiplicity-exact Xi negative Hardy space. No theorem identifies these three as
the source index, boundary channel, and complete bound-state space of one operator. The prime cycle
is not coefficient-faithful for the full all-prime source.

CANNOT-98 — It cannot set source winding equal to vacuum plus off-line multiplicity by analogy.
Without a coefficient-faithful wave operator and cokernel-exhaustion theorem, invisible finite
Krein spectators may change Xi inertia without changing the essential Toeplitz index.

F177 — Generalized boundary triples, Fredholm-Lagrangian/Maslov theory, real spectral flow, and
topological Levinson theorems already supply abstract index-transgression technology. They do not
construct the arithmetic source operator or prove its completeness. Using them alone is a
literature-level repackaging.

F178 — The affine semigroup `N ⋊ N^×` has several natural operator-algebraic boundary quotients
(additive, multiplicative, and full/Cuntz). Therefore “the source completion” is not canonical from
the semigroup presentation alone.

CANNOT-99 — It cannot choose an ax+b/Cuntz/Toeplitz boundary quotient and call its index the
arithmetic selector. A valid completion must be singled out by a universal property forced by exact
integer occurrence and must exclude the known off-line countermodels before divisor specialization.

MUST-68 — Surviving completion-index mechanism is an arithmetic Levinson exact sequence. Construct
one pre-divisor, coefficient-faithful all-prime wave operator from coupled successor--dilation
execution; prove its source index is the single vacuum index; prove its completed cokernel is
exhausted, with multiplicity, by the vacuum channel plus the Xi confluent negative Hardy space; and
prove no channel escapes. Then `-1 = -(1 + k)` forces the off-line multiplicity `k=0`.

MUST-69 — Exact residue-class occurrence must select the completion and collapse the separate
per-prime Fredholm defects to one global source class. Direct sum gives infinite index; arbitrary
quotient is circular. The required theorem is a mixed additive--multiplicative completion law, not
static compatibility of the two operations.

F179 — The completed theta source determinant is already exact: one fixed Hilbert--Schmidt source
inverse `B` satisfies `det₂(I+zB)=XiC(z)/XiC(0)` globally, and analytic zero order equals the
algebraic multiplicity of the corresponding generalized source eigenspace.

F180 — Vacuum index cancels divisor defects. For injective `S`,
`0 -> coker A -> coker(SA) -> coker S -> 0` and `ker(SA)=ker A`. Hence a one-defect shift composed
with `A_z=I+zB` has kernel rank `g_z`, cokernel rank `1+g_z`, and index `-1` for every `z`, including
every Xi zero. Paper proof: `vacuum-index-cancellation-determinant-torsion.md`.

CANNOT-100 — It cannot force RH from a fixed numerical Fredholm index plus cokernel exhaustion.
Every Xi mode contributes a matched kernel--cokernel pair; assuming injectivity of the completed
wave operator is exactly assuming determinant nonvanishing.

F181 — Determinant lines/family index, Hodge purity, complete positivity, equivariant character
indices, and deficiency-`(1,1)` self-adjoint extensions all retain or orient the same defect, but
the corpus already shows their selective clause is RH-equivalent or admits arbitrary off-line
models. They are family-level readers, not source producers.

MUST-70 — A viable completion index must live before pointwise group completion: analytic root
complex, determinant-section torsion, or an equivalent effective family defect. It must derive
from literal source formation a support/properness theorem excluding off-real torsion; merely
equipping the Xi pencil with a Real, Hodge, Krein, Maslov, or determinant-line structure is static.

F182 — Squier/polygraphic completion, Novikov--Sikorav homology, BNS support, Roos `lim^1`, and
affine-semigroup boundary quotients are completion readers. Corpus already realizes the actual
off-wall class in derived completion and makes its universal vanishing RH-equivalent; these
theories do not construct the missing arithmetic occurrence or select a unique completion.

CANNOT-101 — It cannot preserve and multiply the primewise residue-cell torsions
`tau_n(z)=(1-z^n)/(1-z)` through a nested entire completion. For unbounded `n`, one persistent root
`exp(2*pi*i/n)` per stage accumulates at `1`; every locally uniform entire limit is identically zero.
Scalar or zero-free entire normalization cannot remove this divisor.

F183 — Nonzero analytic completion forces a counterdivisor. On any fixed disc around `1`, local
cyclotomic torsion contributes at least one positive divisor degree per sufficiently large stage.
If the completed holomorphic functions converge to a nonzero limit, divisor additivity and the
argument principle force the meromorphic interaction factor's local divisor degree to tend to
`-infinity` at least linearly. Paper proof: `cofinal-cyclotomic-torsion-collapse-and-counterdivisor-law.md`.

MUST-71 — Global arithmetic torsion must be nonadditive across prime-local completion indices. A
viable source law must construct, before Xi specialization, the mixed addition--multiplication
counterchannel that cancels the cofinal cyclotomic divisor while retaining a locally finite entire
secondary torsion. Choosing a meromorphic denominator after reading the target divisor is circular.

F184 — Functional equation, Gamma factor, and completed-zeta polar plane do not determine primitive
completion index. Multiplication by a normalized symmetric off-line quartet preserves all three
and the exact polar part while adding two off-line hyperbolic planes.

CANNOT-102 — It cannot recover off-line index from completed boundary data alone. Any selector
using only functional equation, Gamma factor, residues, or the fixed pole hyperbolic plane accepts
the normalized quartet twist.

F185 — The same quartet twist is not an absolutely convergent Dirichlet series on `Re s = 2`: its
quartic vertical growth contradicts boundedness of every absolutely convergent integer Dirichlet
series there. Exact integer occurrence excludes this countermodel; boundary symmetry does not.

F186 — A nonnegative generalized-prime logarithmic Euler perturbation can create a genuinely new
zero only at or left of its convergence abscissa. Landau's boundary singularity concerns the
logarithmic perturbation; it need not be a singularity of its exponential. For `t>0` and natural
`m`, `exp(-m*log(1/t))=t^m`, which extends analytically through zero. Must prove the precise
boundary growth before excluding such an extension: an `exp(-c/t)` upper bound beats every
positive polynomial lower bound, but logarithmic divergence alone does not. A factor's
nonvanishing inside its convergence region supplies no general bound on the error in counting
the modified integers. The exact finite-order obstruction is
`ThinDeletion.exp_neg_div_lt_pow`; the boundary and application scopes are audited in
[the thin-deletion card](../thin-random-deletion-beurling-alpha-beta.md). This relative statement
imposes no condition on zeros already belonging to zeta.

F187 — Literal integer addition independently carries continuation through the critical strip.
The centered sawtooth/Bernoulli-`B₂` identity continues zeta to `Re s > -1`, away from its sole pole
at `1`, and recovers `zeta(0)=-1/2`; no Euler-product continuation is used.

F188 — Pointwise source-horizontal rigged Krein geometry is trivial inside each open half-strip:
all fibres are related by tame diagonal congruence, and opposite chambers by anti-congruence. Any
invariant of one fibre's topological Krein-isomorphism class is chamber-constant and cannot select
the wall; fixed coordinates or cross-fibre history are indispensable.

F189 — Every finite trace-free skew-adjoint additive determinant stage has nonnegative real central
second jet. Even variable-rank stages cannot converge compact-open to normalized Xi, whose central
second jet is negative. Finite additive unitary landing has the wrong local orientation.

F190 — Every normalized `L1` probability-density clock is Rajchman. Hence all corpus Gamma,
logistic, harmonic, Wigner--Smith, Julia-jump, theta-tail, Suzuki/Cauchy, Meixner, Laplace,
triangular, uniform-difference, and normalized radial clocks erase every nonzero prime-log
character, including countable coordinatewise families.

CANNOT-103 — It cannot use absolutely continuous positive timing or averaging as the selector.
Such clocks quotient away precisely the nonzero horizontal character; they are phase readers after
selection, not occurrence producers.

F191 — Marked FZZ replica response is an incidence invariant, not a marginal charge invariant.
Fixed-support separated Quillen normalization cancels, and every same-winding marked response is
zero; the exact first response is supported only on the opposite-winding cross-block.

MUST-72 — A surviving completion producer must retain cross-orientation incidence before positive
averaging or phase quotient: support must move, opposite sectors must interact, or the completion
law must be nonseparable. Marginal, same-orientation, and fixed-support data erase the anomaly.

F192 — Reduced sigma--delta Bessel PPV component and no-new-constants infrastructure is closed, but
the final Galois scaling contradiction still requires comparison-basis independence. It is not yet
an unconditional hypertranscendence producer for RH.

CANNOT-104 — It cannot infer bounded occurrence evaluation from scalar analytic continuation. The
corpus has no theorem welding the literal rank tower or centered additive continuation to the exact
theta determinant as a bounded representation; inserting that boundedness is RH in disguise.

MUST-73 — Construct from exact integer occurrence one joint closed completion in which centered
additive continuation and canonical multiplicative formation/recovery act on the same source graph,
then prove Xi occurrence evaluations automatically bounded before divisor specialization. F161
would then force every prime character `p^(1/2-s)` to have modulus one, hence `Re s=1/2`.

F193 — Additive Haar uniqueness fixes each local dilation modulus, but global adelic unimodularity
does not fix horizontal grade: the product formula remains `1` after every real power. Therefore
local Haar scaling and global product-formula cancellation tolerate the full radial family.

CANNOT-105 — It cannot select grade by Haar uniqueness, adelic unitarity, or scalar product formula.
Those laws permit arbitrary redistribution of one real modular exponent between places.

MUST-74 — Any local--global producer must detect nonseparable cross-place or cross-orientation
incidence, not the scalar sum/product of local moduli. Its neutralization must fail for a real-power
twist even though ordinary reciprocity and the adelic product formula still hold.

F194 — Lean certifies a new completion-index dichotomy. Neutral twisted Möbius recovery is the
divisor delta; every positive twist has strictly positive Euler-product fibres and boundary index
`1/zeta(1+a)` strictly between `0` and `1`, hence outside the integral divisor lattice.

F195 — Lean certifies meromorphic completion-current quantization. Every nonzero meromorphic germ
has integer cofinal current `(1-z)(-z W'/W)`; therefore no such germ can realize the positive-grade
fractional index. Module: `HTGeometry/TwistedMobiusWittCompletion.lean`.

CANNOT-106 — Fractional index alone is still a receiver if `a`, the radial current, or the
meromorphic germ is supplied after reading a zero. It cannot select RH until exact integer
occurrence constructs the twisted current and completion before divisor specialization.

MUST-75 — Prove two source laws: twisted divisor coefficients have Cesàro/Abel boundary current
`1/zeta(1+a)`, and a genuine coefficient-one Xi occurrence lifts that same current to a nonzero
single-valued meromorphic germ. Their conjunction with F195 forces `a=0`.

F196 — The twisted Möbius coefficient in F194 is not a new source law. It is exactly the existing
Suzuki/Wold activation factor `activationFactor a`; Lean already proves its Euler product and
Dirichlet series `zeta(s)/zeta(s+a)` for every `a >= 0`. Suzuki summatory-error modules already use
the reciprocal-zeta density. New content of F194--F195 is only meromorphic-current quantization.

CANNOT-107 — It cannot identify an arithmetic mean or Abel boundary density with local divisor
order without an independently derived occurrence-to-germ theorem. Positive activation is a valid
exact coefficient stream, while its ordinary Witt completion may have a nonmeromorphic boundary;
that is compatible source behavior, not a contradiction.

FAIL-28 — Twisted Möbius--Witt fractional index fails as RH producer. The required lift from Xi
occurrence to a single-valued meromorphic germ has no source justification and would prohibit a
known exact Suzuki/Wold family. Formal arithmetic and quantization theorems survive as a sharp
boundary classification; MUST-75 is retired as selection programme.

F197 — Fresh interaction audit: information absent from marginals survives in crossed sectors.
The balanced quantum switch's odd branch is exactly a half-commutator and vanishes exactly when
the two statewise orders commute; FZZ same-winding and neutral-conjugate responses vanish, while
opposite winding survives and modulus weighting recovers the radial label. Kinematic support alone
is radial-blind.

F198 — Finite memory cannot absorb the source obstruction. Lean constructs positive finite-bath
memory kernels and exact Volterra solutions, yet Gamma/digamma/zeta/Xi remain
constant-coefficient differentially transcendental after adjoining any finite bath. The missing
direction is not a finite hidden-variable or finite-memory correction.

F199 — Fixed-domain bounded repair cannot cure cofinal escape. Even an unbounded ambient Suzuki
observer with one fixed common graph domain, weak boundedness, and fixed Hilbert--Schmidt
ingress/egress contributes only a bounded trace correction against the cofinally negative Ward
defect. Any surviving repair must change domain/bornology cofinally or retain an unbounded
interaction channel.

F200 — The corpus already has route-independent reconstruction and stratification. Gamma-six
boundary jets, Möbius double-log energy, adaptive Green codiagonal, and Kakutani/Hellinger read one
reflection-even principal escape class; independent formation work, central holonomy, properness,
and escape index have the same zero stratum. These classify RH but do not produce that stratum.

F201 — Properness is gauge-dependent. Constant codiagonal recovery is closable in the base
`ell^2` gauge only at coefficient zero, but the `(n+1)` formation-graph load followed by bounded
inverse-grade recovery realizes every coefficient. Thus a completion can hide nonzero anomaly by
moving unbounded scale from recovery into formation.

F202 — Informative completion requires genuinely cofinal topology, but topology alone is
underdetermined. Product topology makes finite-coordinate freedom dense and exact recovery
vertical; conormal refinement is strictly finer but remembers only the projective conormal line;
provenance topology is either discrete or lets cofinal singleton atoms converge to zero and loses
their coefficient.

CANNOT-108 — It cannot infer selection from boundedness, closability, compactness, or properness
in a chosen completion. A one-way unbounded load can regularize exactly the nonzero codiagonal that
the base gauge rejects.

MUST-76 — A source-admissible completion must be two-sided: formation and information-neutral
recovery must both extend boundedly on the same completed source. Otherwise regularization merely
exports anomaly into an unbounded change of gauge.

F203 — Lean proves the route-independent bounded-factorization law: every algebraic response that
factors through bounded formation and bounded recovery is sequentially closable in the original
source topology. Hence every certified failure of `IsSequentiallyClosableBetween` is exactly an
obstruction to a common two-sided bounded completion, independent of the route's scalar language.

F204 — Specialization to the constant cofinal codiagonal forces its coefficient to zero through
every complex normed intermediate space. The ULF-TAFM-29 graph rescue therefore works only by an
unbounded formation load; bounded recovery did not remove anomaly, it transferred anomaly into
ingress.

CANNOT-109 — It cannot call a topology or graph norm information-neutral when only recovery is
bounded. One-way boundedness permits arbitrary anomaly regularization and makes properness a gauge
artifact.

MUST-77 — Derive from pre-divisor Xi occurrence one common completion with bounded formation and
bounded recovery of the already fused codiagonal response. F203 then forces closability, F201
forces the horizontal coefficient to zero, and existing global stratification yields RH. This
bounded source factorization—not another zero-index equivalence—is the remaining producer law.

F205 — Functional-equation parity does not identify one class as both even and odd. The actual Xi
conormal current is reflection-odd and unconditionally nonzero; the four-organ principal escape
class is its unsigned support/energy, reflection-even, and reflection doubles rather than cancels
it. Corpus already proves oddness of the conservative Green codiagonal iff RH.

CANNOT-110 — It cannot kill the fused escape class by the characteristic-zero slogan “even and
odd implies zero.” Odd orientation and even escape live in different graded pieces; identifying
them is precisely the missing selection assertion.

FAIL-29 — Reflection-parity torsion shortcut retired after corpus audit. Correct survivor: any
mechanism must retain the odd orientation through completion while controlling its even quadratic
escape, not equate the two.

F206 — Lean proves bounded-coboundary invariance: adding any bounded response of the completed
source leaves `IsSequentiallyClosableBetween` unchanged. Nonclosability is therefore not a value
but a completion-obstruction class modulo bounded corrections.

CANNOT-111 — It cannot identify routes merely because their scalar readers have the same zero
locus or asymptotic coefficient. Equality of obstruction classes requires an explicit comparison
whose route difference factors boundedly through the common source completion.

MUST-78 — Upgrade the existing transgression web to bounded-coboundary comparisons between route
responses. Then Gamma, Möbius, Green, Hellinger, trace, and recurrence become gauges of one
completion-obstruction class; any one bounded two-sided source factorization kills the class in
all organs. This is the next route-independent theorem, before further RH specialization.

F207 — F192 is superseded. Lean now proves comparison-basis independence over the full Bessel PPV
ring and closes the scaling contradiction: modified-Bessel order, reflected intensity, and the
calibrated extremal physical scan are unconditionally hypertranscendental. Passing to a reduced or
minimal component cannot manufacture a constant-field relation.

F208 — The actual causal-depth Gamma pre-Gram feature is nuclear and Schatten-one. Pairing it with
any uniformly operator-bounded moving response gives only a sublinear Ward correction, with no
rank hypothesis.

CANNOT-112 — It cannot evade fixed-source trace no-gos by increasing response rank. Rank-free
trace-class duality already kills every uniformly bounded response. A survivor must be unbounded,
domain-changing, cutoff-moving/non-trace-class, or alter source incidence before trace pairing.

F209 — Tensor formation changes duality type. The n-fold epsilon dual squares to `(-1)^n`: even
arity has real involutive polarizations; odd arity carries a complex structure. Its local epsilon
bit is exactly the existing Euler--Wick binary gauge sign.

CANNOT-113 — It cannot model every functional-equation or duality lift by one ungraded involution.
Formation can change the square from `+1` to `-1`; a universal lift must retain degree parity and
its forced phase correction.

F210 — Literal Q8 arithmetic data supplies a genuine source-generated global orientation. Its
proved local Artin epsilon factors at `2,5,41` are `+1,-1,+1`, and their global product is `-1`.
Thus arithmetic phase production exists in the corpus; zeta's obstruction is not absence of local
epsilon-factor technology.

MUST-79 — A universal source law must explain which coefficient-faithful local incidence survives
neutralization and completion. Scalar product formulas, marginal moduli, and positive averaging are
insufficient: Q8 shows orientation is carried by the local representation/incidence data, while
F191 and F197 show neutral or same-sector projection erases it.

F211 — Closed-relation language already gives an exact Xi dichotomy. On the critical line the
half-density Xi graph has zero vertical fibre; off line every closed relation retaining the full
algebraic graph has the whole scalar target as vertical fibre. Thus off-line occurrence is maximal
multivaluedness, not a missing notion of generalized graph.

CANNOT-114 — It cannot advance by replacing operators with linear relations or by naming anomaly
the vertical part of a graph. That construction already classifies the critical line; requiring a
single-valued closed source realization is the same occurrence/admission gate.

F212 — Rational-Hurwitz refinement already has the exact nonlinear source law. At every modulus
`n`, squaring the modulus sends normalized reflection energy `E` to `4 E (1+E)`; the excess over
linear refinement is the nonnegative square `4 E^2`. Vanishing of this excess at any nontrivial
modulus on every Xi fibre is equivalent to RH and to vanishing of the existing Hurwitz orientation
energy.

CANNOT-115 — It cannot obtain selection from residue branching, martingale energy, finite Fourier
Plancherel, or Chinese-remainder refinement by assuming linear or norm-conserving refinement. The
literal finite Hurwitz source proves the nonlinear hyperbolic law; deleting its square term is
already the RH assertion.

F213 — Two independent graded structures already coexist. The theta source-positive polynomial
flow contains an exact `sl2` triple with `H=[E,F]`; the actual Xi conormal current has a faithful
square-zero parity suspension, and functional-equation oddness becomes a commuting involution after
the parity correction. Positive Hodge suspension retains the nonzero multiplicity current at every
Xi zero rather than killing it.

CANNOT-116 — It cannot force neutral grade by putting reflected weights `+a,-a` in opposite parity
and invoking supertrace cyclicity. Ordinary `sl2` uses the commutator `EF-FE`, for which reflected
ordinary traces cancel; graded supertrace cancels the odd supercommutator `EF+FE`, not that `sl2`
commutator. Parity relabelling therefore creates no contradiction.

MUST-80 — Any graded algebraic selector must construct, from literal pre-divisor execution, an odd
source operation whose genuine supercommutator retains the signed horizontal grade. It cannot use
the existing ordinary `sl2` bracket, and it cannot replace signed grade by `J*J` or another positive
square, which is reflection-even and nonzero at critical Xi occurrences.

F214 — Cartan contraction, actual Xi square-zero conormal charge, theta one-chain socle, and global
normalized root-current sewing all exist separately. The missing source contraction is already
RH-complete; global sewing recovers local currents only through unbounded inverse denominators.

CANNOT-117 — It cannot posit `{d,iota}=a id` on the actual occurrence complex. Nonzero characters
are generically Cartan-contractible, while constructing that identity on the source-selected Xi
complex is the selection assertion.

F215 — Local matrix-factorization and curved-Hodge support is RH-blind. On-line and off-line simple
zeros have the same node category; nonzero Gamma-curvature sectors are contractible, and ordinary
Hodge cohomology accepts the wrong sector.

CANNOT-118 — It cannot select by local singularity category, matrix factorization, or curvature
supertrace. These retain local type while forgetting source placement and finite-part transport.

F216 — Twisted Möbius recovery has a certified fractional boundary current, but no source theorem
identifies it with an Xi meromorphic current. Relative divisor cancellation also leaves a nonzero
exponential finite-part torsion.

MUST-81 — Any completion-index comparison must first construct one source-normalized observable
on both completions and control its finite part; equality of divisor order or zero locus is too
weak.

F217 — Conic properness, Lorentz compact reduction, APS balance, and bounded two-sided formation
all select neutral grade once assumed. Actual Xi occurrence is not yet proved to carry any of
these source structures; changing vocabulary does not supply them.

CANNOT-119 — It cannot advance by renaming the RH endpoint conicity, compact reduction, bordism,
microsupport, or properness. The source must generate the relevant structure before specialization.

F218 — The corpus already proves `not RH` iff an actual finite source Lorentz plane exists. It also
identifies rational-Hurwitz refinement with a Lorentz boost: rapidities add, Krein form and
determinant are conserved, and seam energy is `sinh(u)^2`.

F219 — The exact nonlinear Hurwitz law `E(n^2)=4E(n)(1+E(n))` is the double-rapidity identity
`sinh(2u)^2=4 sinh(u)^2(1+sinh(u)^2)`. Likelihood contrast, visibility, fused defect, Hodge sign,
and reciprocal Gamma holonomy are matrix coefficients or positive quotients of the same boost.

F220 — The prime-log weld is dense and noncyclic. Therefore a nonzero horizontal grade sends
literal prime formation to a dense noncompact one-parameter boost subgroup, not a discrete clock.

F221 — Lean audit found no common-lattice version of this law. Existing integral Big-Witt descent
requires the two light-cone eigenvalues themselves to be integers and is exactly RH-equivalent;
central, equimodular, and fitted finite-rank enrichments are already killed.

F222 — Paper theorem ULF-DALR-01: if `2 cosh(a x)` is integral for every prime-log weld rate `x`,
then `a=0`. Hence a dense Lorentz weld preserving one fixed rank-two integral lattice is trivial.
One-prime Pell boosts survive; common dense arithmetic descent kills them.

MUST-82 — Construct from literal pre-divisor formation one prime-independent integral lattice in
the existing oriented rank-two conormal plane, with every prime acting by its certified Lorentz
boost. This is weaker than integral eigenvalues, stronger than separate fitted lattices, and would
force every Xi horizontal grade to zero by F222.

CANNOT-120 — It cannot use a separately chosen lattice or basis for each prime, an infinite-rank
lattice, or a frame chosen after reading a zero. The rigidity comes from one finite-rank arithmetic
object carrying the full dense prime action.

F223 — Lean proves the full common-frame classification. A single invertible rank-two real frame
intertwining every prime-weld Lorentz boost with an integer matrix exists iff horizontal grade is
zero. Module: `RHTower/DenseArithmeticLorentzLatticeRigidity.lean`.

F224 — Existing source integrality does not yet supply F223's frame. Rational-Hurwitz values are
coefficient-one residue sums, but the Lorentz plane appears only after scalar normalization;
literal prime-formation charge has unbounded rank and its coarse scalar cokernel is trivial.

F225 — Theta/Burnol gives a nonzero two-prime quotient vector without multiplicative transport.
Big-Witt Frobenius changes arithmetic base at fixed Xi fibre and its reporter records the label,
not conormal-vector transport. Neither is a common lattice action.

F226 — Integral Tate residue separates fixed from free reflection orbits, but prime holonomy is not
proved to preserve that divisor lattice. Orbit integrality and formation integrality are distinct.

CANNOT-121 — It cannot infer a common rank-two arithmetic frame from integer coefficients, a
two-prime nonzero vector, same-fibre Frobenius base change, or integral divisor multiplicity.
None proves a prime-stable monoidal quotient retaining orientation.

MUST-83 — The exact producer is a canonical rank-two monoidal quotient of the growing integer
formation lattice, prime-stable before scalar normalization and faithful to the signed conormal
current. A chosen rank-two compression is invalid; the quotient must prove its discarded kernel is
horizontal-blind.

F227 — The Lorentz boost is the paired prime response only after removal of its common vertical
phase and critical scalar. Integralizing the full character would also force zero ordinate and is
false for actual critical-line zeros.

MUST-84 — Integral descent must occur on a source-canonical projective orientation quotient, with
determinant/volume trivialization recovering the unimodular radial boost. A phase chosen after
reading the divisor is not source data.

F228 — Corpus already has a one-prime irrational-rotation `K₀` integer-trace collision whose source
projective module is missing. Projective-module language alone therefore repeats a known endpoint;
new content of F223 is only dense all-prime common-frame rigidity.

CANNOT-122 — It cannot claim victory from integral Lorentz rigidity without constructing the
phase-projective determinant quotient. That construction, not trace arithmetic, is the producer.

F229 — Fresh Lean audit: integer-genus FZZ samples do not determine a replica tangent. Sine-null
entire deformations fix every nonnegative integer sample while prescribing an arbitrary tangent at
genus zero, and Schwarz reality still permits every real tangent.

F230 — Literal worldsheet genus has the opposite obstruction: every continuous map into `Nat` is
locally constant, so it cannot produce a nonzero first replica tangent. Analytic interpolation is
therefore arbitrary while literal continuous genus motion is zero.

CANNOT-123 — It cannot use an ordinary real/complex tangent as a source derivative for discrete
formation. Integer samples underdetermine it, and a continuous literal discrete history kills it.
Source differentiation must be an insertion/successor/incidence operation before analytic readout.

F231 — Fresh Lean audit: an `ell`-fold prime-supported multiplicative formation has product fibres
of cardinality at most `ell!`; its convolution coefficients and total coefficient energy incur the
same factorial loss. Unique factorization leaves only permutation histories, not `ell^ell`
arbitrary histories.

F232 — Fresh Lean audit: every fixed logarithmic source jet of the causal-depth Gamma pre-Gram
feature remains nuclear/Schatten-one, so every uniformly bounded response gives only a sublinear
Ward correction. Exact two-leg source-normal deattenuation instead produces multiplier `p` and the
physical source leaves the Hilbert graph domain.

CANNOT-124 — It cannot repair the common obstruction by taking more finite log jets, increasing
bounded response rank, or applying the exact two-leg inverse inside the same Hilbert domain. The
first two remain smoothing; the last exports the anomaly into domain failure.

F233 — Fresh Lean audit: common retarded/advanced orientation corrections and even point-supported
hard-edge charges cannot tune the nonlinear Hawking causal cut. Unit-normalized moving-horizon
AIME response also cancels its own candidate counterterm.

CANNOT-125 — It cannot manufacture the missing signed source term from a common causal correction,
an even local hard-edge renormalization, or unit moving-boundary normalization. Required incidence
must remain asymmetric and source-visible before those quotients.

F234 — Paper theorem ULF-SKJS-1: for `c=(X-1)(Y-1)` and Euler--Kummer clock
`D=A X∂X+B Y∂Y` over a field with `2AB≠0`, the ideal `(c,Dc,D²c)` is the unit ideal. Hence every
Kummer-stable ideal containing one positive complementary Steinberg cell is the whole actual
rational multiplicative group algebra.

CANNOT-126 — It cannot impose complementarity in a proper static quotient on which the logarithmic
Kummer clock descends. Second normal-jet saturation collapses that quotient to zero.

F235 — The positive survivor of F234 is a surjective three-term normal-jet resolution at every
cell. Local homology/cokernel contains no obstruction; only provenance, compatibility, and uniform
boundedness of its right splittings can carry global information.

F236 — Big-Witt/p-derivation language alone does not change F235. Corpus Frobenius acts vertically
at fixed completed-Xi spectral coordinate, Teichmuller atoms are arithmetic-delta constants, and
horizontal relabelling is not fibre transport.

CANNOT-127 — It cannot call a delta-ring, lambda-ring, arithmetic jet, or coherent Frobenius lift
the missing mechanism without a non-Teichmuller moving-relation class and a source-native bounded
horizontal transport.

MUST-85 — Any surviving moving-relation mechanism must retain relations and their normal jets in a
pro-system rather than quotient by them, and must construct compatible two-sided bounded splittings
from literal successor--prime--Gamma formation before Xi specialization. If it does, existing
bounded-factorization and codiagonal rigidity force horizontal grade zero; if its split norms
diverge, it is another completion no-go.

F237 — Paper theorem ULF-SKSB-1: every right inverse of the actual depth-`m` Steinberg second-jet
resolution has coefficient norm at least
`1/(2 |log x_m log y_m|)`. Since `x_m=1/(1+(2/3)^m)` and
`y_m=(2/3)^m/(1+(2/3)^m)`, this lower bound diverges exponentially up to a linear factor.

CANNOT-128 — It cannot assemble bounded global recovery from diagonal/cellwise Kummer-jet
splittings. Every local complex is exact, but every possible splitting is cofinally ill-conditioned.

F238 — Existing formation-Laplacian theory makes the survivor exact: a new cross-cell channel must
intercept every adaptive null sequence and give a uniform lower frame bound on the quotient by the
common mode. Any channel bounded by the old diagonal energy leaves closed-range failure unchanged.

F239 — The existing coherent Big-Witt cross-pair compensator does not supply F238. Complete
right-leg fibres have zero one-leg trace and their closure stays in its closed kernel; a punctured
fibre recovers the missing coefficient but is an incomplete, noncanonically selected incidence.

CANNOT-129 — It cannot repair the split blowup by saying “couple all cells” or “use the Big-Witt
off-diagonal compensator.” Full coherent coupling cancels the signal; selecting a puncture without
a source law inserts the answer.

MUST-86 — The live higher mechanism must generate a canonical asymmetric cross-cell incidence
before coherent summation, while retaining exact reconstruction of the discarded complement. Its
interaction Hessian must have a uniform quotient spectral gap; otherwise F237 and the prime-log
gapless theorem force unbounded recovery.

F240 — Corpus correction to F239: canonical punctures already exist. Genuine normalized Big-Witt
rows are constructed for prime two and for every fixed left prime; their ambient packets tend to
zero while all graph lifts converge to the same vertical one-leg generator and retain unit trace.

F241 — The rooted collision is completely classified in Lean. An arbitrary prime-labelled finite
reporter descends through the scalar singular graph iff its prime coefficients are constant. The
Wold--Jordan profile is only `A/p`; descent iff `A=0`, and the Xi endpoint is the pullback of this
free-scalar fact.

CANNOT-130 — It cannot solve the coherent-fibre problem by pointing, rooting, or selecting a
fixed-left row. The literal source already does all three, and the result is the sharp
nonclosability/RH-equivalent receiver rather than a producer.

F242 — Retaining the root label as an independent boundary coordinate would prevent the collision
but also admit the reciprocal profile for arbitrary `A`. Scalar forgetting is selective but loses
provenance; full label retention is conservative but nonselective.

CANNOT-131 — It cannot choose between a scalar completion and a direct-sum labelled completion and
call that choice the higher mechanism. The first inserts equality of labels; the second removes the
selection constraint. A source law must govern the identifications between labels.

F243 — The obvious transition law is already formalized. Literal Big-Witt atoms `1/(pq)` generate
exactly the complete-prime Dirichlet energy `sum |a_p-a_q|^2/(pq)`; bounded finite-window energy is
equivalent to a constant prime potential and, for the actual Xi seam, equivalent to RH. Its missing
input remains a pre-divisor source upper bound.

CANNOT-132 — It cannot rename the existing prime-seam energy as groupoid curvature, interaction
action, or completion holonomy. Without a new source conservation law that bounds it, this is the
same RH-equivalent receiver.

MUST-87 — A surviving completion law must be conservative on rooted provenance, yet impose a
source-generated constraint on transition arrows before Xi specialization. It must produce—not
assume—the boundedness, vanishing, integrality, or compactness that makes the already-formalized
transition receiver selective.

F244 — Pair-groupoid language is also already exhausted. Exact bidescent conserves horizontal
defect under vertical coboundaries but cannot kill it without an independent anchor; any
nonnegative additive cost on reversible histories is identically zero. Directed irreversible
history can carry cost, but direction alone supplies no selector.

CANNOT-133 — It cannot relabel the existing prime-seam cocycle as a groupoid action, or use a
reversible nonnegative path cost. The former still needs the source upper bound; the latter
vanishes by reversibility.

F245 — Paper theorem ULF-ICTR-1: for `0<=b<1`, the unnormalized paired trace
`T_b(n)=n^(1+b)+n^(1-b)` is integral for every natural scale `n` iff `b=0`. For `0<b<1`, its second
integer difference is eventually positive and tends to zero, contradicting integrality. The paired
determinant is exactly `n^2` at every positive scale.

F246 — F245 fuses four previously separate facts: functional-equation/Schwarz orientation pairing,
literal all-natural-number formation, finite factorial multiplication histories, and real-power
finite-difference asymptotics. Its new move is to retain the common scale `n` erased by every
determinant-one/Lorentz normalization.

CANNOT-134 — It cannot normalize first and then ask for a lattice, or retain only prime-scale
traces. The exact selector uses the unnormalized integral trace at every natural formation size;
discarding the common factor or the composite scales removes the discrete-curvature contradiction.

MUST-88 — Construct before Xi specialization a multiplicative integral or virtual-integral
rank-two formation correspondence `M_n` whose functional-equation involution exchanges the two
orientations, whose determinant line is `n^2`, and whose complex character eigenvalues are
`n^(2 Re s)` and `n^(2-2 Re s)`. Its integral categorical trace plus F245 forces grade zero and
closes RH through the existing exact grade equivalence.

MUST-89 — The realization must be signed/virtual/Krein-capable: corpus genuine-positive Artin/Wick
no-gos prohibit assuming a genuine positive finite representation. Integral provenance must come
from finite formation histories, not from a zero-labelled lattice selected after complexification.

F247 — Hostile realization audit killed the finite-rank form of MUST-88. Scalar extension of one
integral matrix cannot make its characteristic polynomial depend on a spectral character; allowing
character-valued entries makes the source trace character-valued, not integral.

CANNOT-135 — It cannot place `n^(2 Re s),n^(2-2 Re s)` in a finite integral matrix independent of
`s`, or choose an `s`-dependent integral lattice. The first is impossible; the second is the old
descent receiver.

F248 — Exact hyperbolic formation ledger: for even/odd weights `E=n exp(u)`, `O=n exp(-u)`,
`Tr=2n cosh u`, `STr=2n sinh u`, `EO=n²`, `STr/Tr=tanh u`, `2n/Tr=sech u`, and
`Tr²-STr²=4n²`. Mixed inertia, Hodge sign, positivity, contrast, visibility, and rapidity are exact
readouts of one parity-graded ledger, not analogies.

F249 — Corpus Frobenius--Verschiebung relation supplies a possible source origin. `F_nV_n=n`; on a
character with `F_n=n^sigma`, the dual weight is `V_n=n^(1-sigma)`. The even/odd squared doublet has
weights `n^(2sigma),n^(2-2sigma)` and fixed determinant `n²`.

F250 — ULF-ICTR-1 now also proves all-scale integral supertrace rigidity: for `0<=b<1`,
`n^(1+b)-n^(1-b)` is integral for every natural `n` iff `b=0`. Lean proves trace, supertrace,
determinant, Minkowski conservation, tanh contrast, and inverse-cosh visibility in one module.

CANNOT-136 — It cannot use raw finite rank, raw infinite trace, or fixed finite log jets. The source
must be an integral pro/super object, and integrality must reach the analytic character through a
proved relative Fredholm/Lefschetz completion comparison.

MUST-90 — Build finite integral formation-history complexes with chain maps `F_n,V_n`, prove
`F_nV_n=n` and multiplication functoriality, place `F_n²` in even and `V_n²` in odd parity, then
compute the finite Lefschetz-supertrace transition law. Stabilization or a source-canonical relative
integer must be proved before any Xi character.

MUST-91 — Prove completion-index invariance: the stabilized integral Lefschetz supertrace equals
the analytic relative supertrace after the common Gamma-six recovery completion. Applying a strip
character then gives the all-scale integers in F250, forces grade zero, and closes RH. Failure of
this equality must be classified as the route-independent completion anomaly.

F251 — Raw finite Frobenius--Verschiebung stages are now classified on paper and in Lean. If
Frobenius is a finite permutation `F` and `V=qF⁻¹`, then
`STr(F²,V²)=(1-q²)#Fix(F²)`. The trace is integral but depends only on finite orbit structure and
degree; it contains no analytic grade.

CANNOT-137 — It cannot identify `q^(1+a)-q^(1-a)` with a raw finite Witt/permutation Lefschetz
trace. Finite stages supply integral provenance, not rapidity. Normalizing or inserting character
weights at finite level changes the source and assumes the desired character.

F252 — Every already-specialized finite prime Koszul fibre in the open strip is contractible.
Taking `lim` or algebraic `lim¹` of its zero cohomology tower remains zero. Zeros therefore cannot
be ordinary derived-limit cohomology of specialized finite fibres.

F253 — Ordinary scalar derived Cartier base change is also exhausted: its two-term fibre is
contractible at every nonneutral character and survives only at neutral character. It is a sharp
wall receiver, not an off-line anomaly carrier.

CANNOT-138 — It cannot be ordinary algebraic Tor, ordinary scalar derived base change, or ordinary
`lim¹` applied after spectral specialization. All three erase the off-line class by exact
contractibility.

F254 — Provenance-continuous completion of eventually exact stages cannot create homology. Yet the
corpus identifies every off-line horizontal class with a completion-born boundary and with a
nonzero Roos class. Hence any genuine off-line carrier certifies failure of provenance-continuous,
uniformly controlled exactness during completion.

F255 — Today's Gamma/Suzuki audit locates that failure sharply. Actual causal Gamma feature is
Schatten-one; every fixed log jet and every admitted subexponential functional calculus remains
Schatten-one; bounded responses are sublinear; additive logarithmic singular residue is invariant
under the feature; exact two-leg deattenuation instead exits the Hilbert graph by prime-harmonic
divergence.

CANNOT-139 — It cannot live inside bounded/nuclear functional calculus, be detected by an additive
singular trace modulo trace class, or use the physical inverse on the same Hilbert graph. The live
class lies at a nonclosed/unbounded completion boundary and must retain its source domain defect.

F256 — Hawking/Peierls no-gos impose parity on that boundary. Common retarded/advanced corrections
cancel exactly; an order-one hard-edge distribution contributes only its orientation-odd
derivative-delta charge; finite-exponential-variation causal Laplace spectra cannot realize the
pre-divisor susceptibility. The survivor is odd, singular, and not finite variation.

F257 — FZZ no-gos impose source differentiation. Literal integer genus has zero continuous
tangent; integer-genus entire samples admit arbitrary replica tangents; adaptive BRST occurrence,
nonzero Gamma normalization, and radial visibility still do not imply passivity. The needed
derivative must be a source insertion/incidence operator, not analytic interpolation of discrete
samples.

F258 — Prime-amplifier proofs expose the usable integral source grammar: multiplication histories
quotient to prime multisets; ordered fibres have size at most `ell!`; distinct products obey a
stars-and-bars bound; powered coefficients are literal fibre cardinalities; exact coefficient
energy controls block support. This supplies integral symmetric/divided-power formation stages,
but F251 proves their raw traces are grade-blind.

CANNOT-140 — It cannot rename the existing coefficient-fed Roos or shell base-change reader as
the producer. Those classes are explicitly evaluated on centered rate and already have the
critical-line zero radical. New content must construct the comparison from the integral formation
system before supplying a spectral occurrence.

MUST-92 — Replace MUST-90's raw trace stabilization by the source-native comparison square
`complete-then-specialize -> specialize-then-complete` for the actual integral formation complex.
Its cone must be formed in a controlled topological/pro category where cofinally unbounded
contracting homotopies are not equivalences. Ordinary derived categories are excluded by F252--F254.

MUST-93 — Lift `F_n,V_n` and functional-equation parity to this comparison cone and prove a global
properness theorem: at every Xi occurrence the cone has a finite perfect integral boundary class,
its analytic eigenweights are `n^(2 Re s),n^(2-2 Re s)`, and its integral index equals their
supertrace for every natural `n`. F250 then forces `2 Re s-1=0` and closes RH.

F259 — The specialization--completion square already exists concretely in the Meyer half-density
bridge. Strong source embeds injectively into `L²` and intertwines the prime Koszul operator. Off
line the completed `L²` operator is a unit, but its inverse cannot preserve the strong source
image. Thus horizontal escape is literally `complete then invert ≠ invert in source`.

F260 — The arithmetic leg is also complete: packet units are equivalent to compatible
automorphisms of all actual away-prime cyclotomic towers, and diagonal packet Frobenius acts by the
literal prime-power map at every finite stage. This is a faithful profinite/integral history, not a
fitted scalar reporter.

F261 — One completion topology is impossible. Maximum-grade provenance norm retains every cofinal
private shell but makes the transverse quotient discrete. Dyadic summable provenance norm is
non-discrete but sends nonzero cofinal private shells to zero, and no uniform bound compares the
first norm to the second.

CANNOT-141 — It cannot seek one Banach/Hilbert/provenance norm that is simultaneously analytic,
non-discrete, and uniformly faithful to unbounded source labels. Lean proves the two canonical
requirements are singularly incompatible.

F262 — The needed carrier is therefore intrinsically bi-complete: arithmetic/profinite topology
retains labels and integrality; analytic/Hilbert topology supplies spectral completion but loses
cofinal provenance. Their partially defined comparison graph, not either completion alone, is
where source escape lives. Existing Gelfand-triple code already supplies the correct three-space
shape but assumes the RH-strength source-eigenclass lifting interface.

MUST-94 — Refine MUST-92 to a two-topology comparison. Construct from the same algebraic formation
complex both its profinite provenance completion and Gamma/Meyer Hilbert completion. Treat identity
between them as a closed relation/Gelfand pairing, form its specialization--inversion defect, and
prove packet Frobenius--Verschiebung equivariance. Do not force a continuous map between singular
topologies.

MUST-95 — Immediate source-specific gate: generalize the Meyer prime Koszul comparison to a
pre-divisor complex parameter, define the quotient measuring failure of the completed inverse to
preserve strong source image, and identify its anti-invariant part with the existing Roos class.
Then prove this defect has a finite perfect integral packet lattice; its FV supertrace plus F250
closes RH.

F263 — First half of MUST-95 is now paper-proved and Lean-formalized. For every `s in C` and prime
`p`, Meyer half-density realization intertwines source and Hilbert prime Koszul coordinates before
divisor specialization. If `R` is strong-source range and `D_s` the Hilbert coordinate, then
`R <= D_s⁻¹(R)` and the canonical completion escape is `E_s=D_s⁻¹(R)/R`, realized inside `H/R`.

F264 — Exact transgression law: whenever `D_s` is bijective, `E_s=0` iff `D_s⁻¹` preserves
strong-source range iff the source Koszul coordinate is surjective. Thus a static invertible
completion square does not manufacture a second obstruction; it transports the source cokernel
into an inverse-domain quotient.

F265 — At every Xi divisor and every prime, off-line placement forces `E_rho != 0`; conversely
`E_rho=0` forces critical-line placement. This closes the comparison carrier and RH implication,
but supplies no vanishing producer.

CANNOT-142 — It cannot stop at the Meyer escape quotient, source-cokernel equivalence, or another
static comparison square. Those are now exact receivers. Any claimed completion mechanism that
forces `E_rho=0` by assuming source-preserving inversion or source surjectivity is circular.

F266 — Existing complete-arithmetic-to-Meyer comparison no-go is stronger than a topology slogan.
Every uniformly first-order-regular comparison sends normalized actual Xi traces to zero along a
cofinal divisor sequence. A concrete fixed comparison stays nonzero at every finite stage yet
still converges to zero. Hence source information can survive pointwise while its amplitude is
erased asymptotically.

F267 — Existing arithmetic formation-completion boundary is literally centered grade times one
fixed singular vector, and its Roos/physical identifications are coefficient-fed. Likewise the
integral bidirectional Big-Witt lift is defined by demanding an integral ghost equal the Gamma
weight, and its existence is already equivalent to grade zero. Neither is the source producer.

CANNOT-143 — It cannot demand uniform nonerasure, prescribe an integral ghost after spectral
evaluation, or call `a` times a fixed completion vector arithmetic generation. The first is ruled
out by F266; the latter two insert the selector.

F268 — Loss-order/Rees reinterpretation is not new source structure. Corpus already defines Xi
relative-completion slope as `Re rho-1/2`, proves functional-equation sign reversal, and identifies
semistability with critical-line placement, closability, and zero theta flux. Gamma--Rees and
prime/depth normalized-log modules already recover the same scalar through positive comparison
factors.

CANNOT-144 — It cannot define a new filtration slope from Xi trace decay, normalized anomaly,
conormal norm, or the existing relative-completion coordinate. Those are divisor-fed receivers;
asserting that an independent source filtration has that slope is the missing comparison, not a
proof. `ULF-FVCS-L2S` is retired.

F269 — Fresh audit of today's Lean additions gives a strict producer/receiver split. Source-native
finite Frobenius--Verschiebung traces are integral but grade-blind; source-native twisted Möbius
completion produces a positive fractional nonmeromorphic boundary at every positive twist;
off-line Meyer completion escape is provably nonzero. By contrast, grade-zero conclusions require
an integral descent, common lattice, bounded two-sided factorization, or escape vanishing that the
source has not produced.

F270 — `ULF-PD2SG-1` is dependency-closed and Lean-certified. Let `p` be prime, `XY=p^2`, and
`1<Y<=X<p^2`. If the first two odd power sums `X-Y` and `X^2-Y^2` are integers, then `X=Y=p`.
Thus for `0<=b<1`, integrality of only the two prime-power supertraces at depths one and two forces
`b=0`; all-scale integrality and dense all-prime descent are unnecessary.

F271 — Both sharpness directions are explicit. Composite determinant `36` admits `(X,Y)=(9,4)`
with integral first two supertraces. At prime determinant `9`, the roots of `z^2-7z+9` are unequal,
lie in the open reciprocal strip, and have integral even traces at every power by the recurrence
`T_(r+2)=7T_(r+1)-9T_r`. Primality and odd parity are separately load-bearing.

MUST-96 — Replace all-scale/common-lattice descent by two-superghost descent. Construct before
divisor specialization one integral parity-graded object at one prime whose analytic realization
has reciprocal determinant `p^2` and odd ghosts `p^(1+a)-p^(1-a)` and
`p^(2+2a)-p^(2-2a)`. Big-Witt Frobenius already transports ghost two to ghost one. F270 then forces
`a=0`; the only missing producer is source/Gamma supertrace naturality for this one object.

F272 — The existing full integral Laurent producer has a sharper one-prime selector. Its one-copy
quadratic ghost at prime two is `Q_2(a)=-2(cosh(a log 2)-1)`, and `|a|<1` forces
`-1/2<Q_2(a)<=0`. Hence `Q_2(a)` is integral iff `a=0`. This is paper-proved and Lean-certified,
including the exact pointwise Xi equivalence.

F273 — Total multiplicity destroys the selector: for every `m>=3`, some nonzero strip grade has
`m Q_2(a)=-1`. Multiplicity must be resolved by the intrinsic local divisor filtration
`m_rho^j/m_rho^(j+1)`, whose layers are one-dimensional, not by dividing a total index or choosing
a root projector.

F274 — Direct character-to-Euler-index transgression is rejected. Laurent ghost evaluation is a
varying analytic torsion/determinant, while ordinary Euler index is integer and locally constant.
Equating them without an integral endomorphism is an unmotivated type jump; `ULF-DCIT-1` is retired.

CANNOT-145 — It cannot use ordinary equivariant `K`-theory, a continuous Fredholm family, total
divisor multiplicity, positivity, ghost erasure, or an asserted equality between analytic torsion
and Euler index. Each either retains nonintegral character values, loses the selector, or is already
an RH-equivalent receiver.

F275 — Corpus already contains the correct higher-rank carrier. Bare functional-equation
reflection `R` and Gamma-transported reflection `R_a` are involutions; their framed difference
`C_a=R_a-R` is the curved suspension, and `det C_a=2(cosh a-1)` is exactly negative Laurent
quadratic ghost. Unframed traces and determinants are blind; relative framing retains anomaly.

F276 — `ULF-DRRIF-1` is dependency-closed and Lean-certified. If the dyadic relative reflection
`C_(a log 2)` has integer coordinates in one complex rank-two frame and `|a|<1`, its determinant is
an integer in `[0,1/2)`, hence zero and `a=0`. Frame existence at every Xi support point is exactly
RH. This replaces dense all-prime common-lattice descent by one prime and one framed matrix.

F277 — `ULF-IRRCF-1` is dependency-closed and Lean-certified. The universal integral matrix
`C_T=[[0,T-1],[T^-1-1,0]]` satisfies `C_T^2=kappa I` and `det C_T=-kappa`; Gamma evaluation sends it
exactly to the curved suspension `R_a-R` and sends its determinant to positive paired curvature.
Integral Laurent formation, functional-equation reflection, and Gamma curvature are therefore
three realizations of one source Clifford law, not analogous route outputs.

MUST-97 — Remaining global theorem only: fuse the constructed integral complex `C_T` with the
existing canonical Xi jet associated-grade functor, and prove dyadic Gamma realization lands each
one-dimensional layer in a finite free `Z`-lattice. Then `ULF-DRRIF-1` forces every support grade
to zero and closes RH. Any construction that chooses a zero, assumes integral landing, or uses
total multiplicity merely restates this gate.

F278 — Today's singular-cohomology theorem changes locality. Every finite restriction of the
reflection-odd all-prime co-shift profile is an `ell^2` boundary, while its full cofinal class is
zero exactly at neutral grade. The obstruction cannot occur at any finite stage.

F279 — Today's infinite Suzuki Gamma kernel theorem proves the complementary fact: the full
moment feature and its positive trace-class energy are faithful on all arithmetic source
coordinates and lose exactly the auxiliary feature sector. Infinite completion can retain all
source data even though every fixed log jet, bounded graph observer, and rational singular-residue
circuit is coefficient-blind.

F280 — Copywise dyadic integral/compact reduction is not the producer. Corpus already constructs a
unique coefficient-faithful relative Gamma local system, flat off line as well as on line, whose
positive compact real-form reduction exists exactly at neutral grade. `ULF-DRRLC-1` is retired as
a producer programme; `ULF-DRRIF-1` survives only as its exact terminal selector.

CANNOT-146 — It cannot be finite-packet exactness, fixed jets, bounded or rational completion,
pointwise phase recurrence, generic passivity, a fitted integral frame, or ordinary square-zero
totalization. Today's positive/no-go audit makes each blind, nonselective, or already RH-equivalent.

MUST-98 — Move one categorical level up: realize `C_T` as the paired naturality defect of cofinal
Tate completion. At stage `m`, flat-minus-scaled defect is `(1-u) beta_m` on the newly born top
coordinate; reciprocal clocks reconstruct `-C_T`, so `C_T^2=kappa I` is completion curvature.
Then seek zero-independent integral strictness of the assembled top-coordinate action; only that
global law may invoke the dyadic selector.

F281 — `ULF-CRRCF-1` is dependency-closed and Lean-certified. At every Tate stage, canonical top
readout of reciprocal flat-minus-scaled naturality defects reconstructs the full Gamma relative
reflection matrix. Its square is scalar curvature, its determinant is paired positive curvature,
and that determinant equals evaluation of the universal integral Laurent determinant. The
quadratic ghost is therefore literally a cofinal completion anomaly, not a static analogy.

MUST-99 — Assemble this reciprocal-clock operator over the existing arithmetic cofinal Tate direct
sum over `Z[T,T^-1]`, before Xi specialization. Prove actual Xi completion preserves its canonical
integral top-coordinate module. Copywise compact reduction, source/physical reader agreement, or
post-evaluation integrality does not count; each is already a wall receiver.

F282 — `ULF-ICTRRA-1` is dependency-closed and Lean-certified. Finite Tate shift, zero-extension,
and top-boundary mechanics now exist over `Z[T,T^-1]`. Flat-versus-`T` and
flat-versus-`T^-1` defects reconstruct `C_T` at every stage; their direct-sum operator over all
stages satisfies `D_T^2=kappa id`. The zero-independent integral curved Tate object is built.

MUST-100 — Prove one global Gamma base-change square intertwining `D_T` with stagewise physical
curved suspension, then fuse that square with the existing Xi jet associated-grade comparison.
Only remaining conjectural content may be preservation of canonical integral top-coordinate
module under actual Xi completion; per-fibre integrality is forbidden.

F283 — `ULF-ICTGBC-1` is dependency-closed and Lean-certified. Coefficientwise Gamma base change
globally intertwines the integral cofinal Tate operator `D_T` with physical `D_a`; moreover
`D_a^2=-K(a) id`. Source construction, cofinal assembly, and Gamma physicalization are one exact
base-change system. None is the missing selector.

MUST-101 — Fuse `D_T` with the existing global Xi jet associated grade and identify its canonical
top-coordinate module before proposing another producer. After that unconditional comparison, the
only admissible new source law is global integral strictness under actual Xi completion. Copywise
reader agreement or fitted lattices remain forbidden wall receivers.

F284 — Completion audit: actual Xi vertical class is completion-born iff the pre-divisor Roos
`lim^1` class is nonzero iff strict physical image is nonzero iff compact recurrence descent fails.
Ordinary derived scalar base change contracts off neutrality; finite associated grade forgets the
splitting torsor. Neither can carry the anomaly.

F285 — `ULF-ICTFPI-1` is dependency-closed and Lean-certified. Literal finite Meyer--Tate Xi
landings are boundaries and converge in Hilbert graph norm to the physical landing for every Xi
grade. Their fixed-source exactness states converge in provenance topology iff the evaluated
integral determinant vanishes. The Laurent ghost is the obstruction index to formation properness,
not a static detector.

CANNOT-147 — It cannot be ordinary vector/norm convergence, finite associated-grade preservation,
ordinary Tor/base change, or boundary-of-boundary killing. Norm convergence holds off line;
associated grade forgets splitting; scalar derived fibres contract; Stokes killing erases ghost and
compensating curvature together.

MUST-102 — Prove zero-independent source-marked provenance continuity of the literal Meyer--Tate
formation system. Equivalently, actual arithmetic formation must preserve its fixed boundary
witness through singular completion. This is the sole remaining producer; assuming it pointwise is
RH-equivalent.

F286 — Fresh code review correction: `SourceMarkedExFlag` retains source vector and open survival
truth values, not a boundary primitive. At an exact physical state every survival neighborhood is
absent, so the positive convergence direction of `ULF-ICTFPI-1` is vacuous. The theorem is a valid
obstruction equivalence, not a formation-properness producer.

F287 — Corpus already has the stronger mechanism. A compatible family of stage quotient classes
lifts to coherent representatives iff its boundary mismatch is a Roos coboundary; failure is the
canonical `lim^1` class. Stable-image/Mittag--Leffler towers kill every such obstruction by producing
coherent corrections. This tracks proofs of exactness, not Boolean exactness.

CANNOT-148 — It cannot be blanket Mittag--Leffler stability of the existing fixed-tail tower.
Its bond prepends zero, misses every nonzero head, and its reaches strictly lose successive head
coordinates. The ambient tower is designed to carry nonzero `lim^1`; only the distinguished
arithmetic primitive, or a different source tower mapping faithfully to it, may be coherent.

MUST-103 — Replace flag convergence by proof-carrying completion: construct one zero-independent
arithmetic tower of actual boundary primitives and a coefficient-faithful comparison sending its
coherence obstruction to the Xi Roos class. Prove coherence from a source law before divisor
specialization. Pointwise existence of primitives, Boolean exactness, or universal stability of the
target tail tower does not count.

F288 — `ULF-ICTCPI-1` is dependency-closed and Lean-certified. The literal pre-divisor summable
primitive fibre is always subsingleton; its only possible point is the negative arithmetic-tail
history. It is inhabited iff the Roos class, integral determinant index, and Xi formation anomaly
vanish. Universal inhabitation is RH.

F289 — Higher mechanism identified: completion must retain compatible null-homotopies, not only
objects or exactness truth values. Primitive choices form fibres under kernel gauge; transition
mismatch is the cocycle, `lim^1` its holonomy, and `det C_T` its evaluated obstruction index. Here
kernel rigidity collapses each fibre to empty-or-singleton, so no gauge choice can hide failure.

CANNOT-149 — It cannot be “find some better primitive after completion.” Concrete Roos rigidity
already fixes the only possible primitive coefficient-for-coefficient. Remaining freedom is solely
whether this literal history belongs to the arithmetic summability/properness class.

MUST-104 — Find a zero-independent law forcing the literal negative-tail history into the source
completion class. Candidate law must act before Xi specialization and imply summability/properness;
post-divisor closability, bounded work, integral framing, or survival continuity are equivalent
receivers, not derivations.

F290 — Fresh cross-organ theorem: an Xi coherent primitive exists iff orthogonal theta-shell
recovery is sequentially closable. Any exact factorization of that recovery through bounded ingress
and bounded egress on one normed completion constructs the unique primitive. Thus Roos `lim^1`
holonomy and shell graph nonclosability are the same completion failure, not parallel endpoints.

F291 — Today's integral Tate, Gamma base-change, proof-carrying completion, and shell-replica code
now gives one exact anatomy. `C_T` is the zero-independent cofinal naturality defect; Gamma
evaluation is its Lorentzian physical gauge; `det C_T` is its scalar index; the Roos class is failure
to complete finite null-homotopies; infinite shell replication turns the same failure into a
graph-null sequence with nonzero lifted Ward response. Compact recurrence is the quotient-side
closed phase.

CANNOT-150 — It cannot kill the Roos class by reflection oddness or strict functional-equation
involutivity. Reflection swaps the two off-line fibres and sends `alpha` to `-alpha`; this action
squares to identity for every `alpha`. Concluding `alpha=-alpha` would identify the fibres and
reinsert the missing selection premise. Scalar FE/Schwarz projective residues are gauge-trivial.

FAIL-37 — Adjoint-differential shortcut retired. A dense closable scalar reporter already has a
bounded full-domain extension, while the replicated shell codiagonal is explicitly nonclosable.
Calling recovery an adjointable differential cannot generate closability; source must first build
the common two-sided correspondence.

F292 — Literal shell formation fixes a non-arbitrary completion datum: counting trace equals the
canonical `ell^2` GNS norm and successor formation preserves both. Shell sectors are disjoint and
arbitrarily finite differentially independent while carrying the same divisor and anomaly. A
summable probability weighting is not equivalent: it breaks successor invariance and can hide a
nonzero constant response.

MUST-105 — Test `ULF-SSND-1`: construct before divisor specialization one normal stationary
formation/recovery correspondence on the shell counting-trace GNS completion, and prove its core
recovery is exactly the pre-divisor quadratic Ward response on proof witnesses. Normal two-sided
transport gives bounded factorization; F290 then supplies every coherent primitive and closes RH.
Markov/Fisher data processing without the literal response comparison does not count.

F293 — Fresh review of today's completion code: the cofinal Laurent/Tate modules are finite
stagewise algebra. Their gains, shift maps, direct sums, Gamma base change, determinant identities,
and coefficient reconstructions do not define a Tate topology or prove strictness/properness of an
arithmetic completion. Source-marked convergence is imposed by survival predicates; its positive
physical direction is vacuous at an exact state.

F294 — The coherent-primitive theorem is exact and stronger than the flag topology: the primitive
fibre is subsingleton and is inhabited iff the Roos class, integral completion index, Xi anomaly,
and shell closability obstruction vanish. It classifies the missing history uniquely but does not
put that history in the source completion.

FAIL-38 — `ULF-SSND-1` retired. Normality governs bounded observables, not the singular/unbounded
Ward response. Adding trace-nonincreasing `L2` boundedness plus exact core recovery assumes the
existing bounded-factorization endpoint; positive physical realization conflicts with certified
non-Bessel strip behaviour. Counting trace still proves the survivor: any nonzero off-line exact
recovery must be singular, domain-changing, or noncyclic.

F295 — Today's prime co-shift and Gamma-six relation no-gos remove two more fake sewing laws.
Natural boundaries cannot selectively absorb the reflection-odd anomaly without also killing both
source eigenprofiles, while relation covariance plus any nonvertical descended reader already
forces equality of scalar characters. The former is too indiscriminate; the latter hides selection
in descent.

F296 — Suzuki/Hilbert--Brown/CCM/FZZ review gives one common exclusion envelope. Trace-class
source features plus uniformly bounded, domain-preserving, cyclic recovery remain sublinear;
bounded generalized inverses, finite circuits, moving projections, fixed graph norms, ordinary
log residues, and regular vacuum linearisations cannot supply the linear Ward load. Unframed
unitary invariants and balanced antiunitary amplitudes erase orientation. A successful lift must
change domain/sheet/support or use a source-generated noncyclic renormalised history; merely
postulating such singularity is not a mechanism.

CANNOT-151 — It cannot be positivity, complete reflected Hankel positivity at every order,
exponential type, and functional-equation symmetry alone. The certified uniform-distribution TCD
countermodel has all these properties and still has nonreal zeros.

F297 — Today's sieve code contains a genuine source law rather than a receiver: unique
factorisation identifies coefficients of a powered prime amplifier with unordered prime
multisets; fibre multiplicity is integral and bounded sharply by `ell!`; coefficient support and
squared energy obey exact counting inequalities. Commutative observation forgets order but retains
its multiplicity as positive arithmetic mass.

F298 — The shifted-Euler Taylor stratification already formalises the associated source geometry:
neutral-shift vanishing order is `omega(n)`, the first derivative is exactly `2 Lambda(n)`, the
leading derivative is `2^omega omega!` times the product of prime logs, and reflection cancels even
jets while doubling odd jets. Prime polar mechanics already reconstructs parity, valuation depth,
squarefree locus, and the Möbius boundary phase. Normal-crossing, ordered-history, and parity-depth
reinterpretations are therefore established shadows, not new selectors.

F299 — Functional-equation packet lifting through the common recovery kernel is observer-level
information-neutral: it discards and regenerates latent history. Prime-Poisson superselection,
Shale summability, Fock recurrence, and finite-cutoff non-Cauchy laws are already exact RH
receivers. They show that a source sewing unitary can exist only on the critical line, but none
produces that sewing from the scalar functional equation.

CANNOT-152 — Minimal KSGNS/Stinespring uniqueness cannot by itself generate the missing lift. The
corpus already proves canonical pointed-unitary uniqueness for a supplied CP map and minimal
presentation. Scalar equality of one functional-equation reporter does not imply equality of CP
maps on a generating operator system; assuming a shared CP action or its intertwiner merely
supplies the missing event, target, and passage.

FAIL-39 — Normal-crossing completion, ordered confluence, Shale/Fock sector separation, and minimal
dilation uniqueness retired as standalone higher mechanisms. Each is already formalised and exact;
their conjunction still lacks the same source-generated weld. Combining receivers does not make a
producer.

MUST-106 — Next admissible mechanism must prove an intervention-tomography theorem before divisor
specialisation: one arithmetic source law generates a shared action/channel, the full family of
route interventions is complete on a generating system, and functional-equation equality for that
family forces equality of the entire action. Only then may canonical dilation uniqueness produce
history sewing and prime-Poisson/Shale superselection force horizontal grade zero. A scalar
reporter, supplied CP map, chosen operator system, or assumed completeness does not count.

F300 — Fresh tomography audit retires MUST-106 as stated. Complete process tomography in the
corpus is only a finite span theorem. One-clock CCM tomography reconstructs the complete Xi divisor,
yet its fibre still admits arbitrary pointed Stone recurrence. More decisively, an explicit ternary
model fixes the observer and recovery kernel, implements the functional-equation involution, and
acts nontrivially on a nonzero rank-one formation charge.

CANNOT-153 — It cannot generate source sewing from a complete family of passive interventions. If
the family omits hidden formation charge, the ternary countermodel survives; if it includes that
charge, scalar functional-equation equality gives no equality on the added interventions. The
shared action remains an extra premise.

FAIL-40 — Intervention tomography retired. Existing complete response quotients, minimal
realizations, divisor tomography, and the FE-fixed hidden-charge countermodel already give its
strongest forms and exact failure.

F301 — Nomenclature correction: the horizontal Euler--Wold ``Jordan producer'' takes the Xi copy
and its grade as input. It preserves the selected fibre and proves exact orbit budgets; it does not
restrict which grades occur. It is a connector/receiver, not a source producer.

F302 — Two involutions must remain distinct. Functional-equation reflection `rho |-> 1-rho` has no
fixed Xi zero copy, including on the line; Hermitian reflection `rho |-> 1-conj(rho)` fixes exactly
the critical line. Their mixed source jet is `2 a gamma`, equivalently the imaginary part of the
Xi-squared node, but even completion erases it. Confusing the involutions inserts selection.

F303 — Toeplitz/Hopf/C-star/Shilov completion is already exact. The unilateral source bialgebra
lacks an antipode, the boundary quotient kills its rank-one defect and yields the bilateral Laurent
action, and compact boundary representation/admission is already RH-equivalent.

CANNOT-154 — It cannot call the C-star envelope, Shilov boundary, or boundary representation the
missing mechanism. Those constructions classify the quotient after the boundary ideal is supplied;
proving the actual Xi landing factors through that quotient is precisely the open admission theorem.

FAIL-41 — Boundary-envelope reinterpretation retired after direct Lean audit.

F304 — Formation charge is already the symmetric distributivity quotient
`U inter (W+Z) / ((U inter W)+(U inter Z))`; its dual, Hodge carrier, serial erasure/generation law,
and completion-born realization are formalized. Central/distributive language does not add a
producer: automorphisms transport nonzero charge, and singular completion creates exactly the
off-line class.

FAIL-42 — Central-support/distributive-completion reinterpretation retired. It restates proved
formation homology and the existing completion boundary.

F305 — Tensor polarization already amplifies one indefinite Lorentz block: negative index grows at
every tensor depth, and a uniform finite target budget forces positivity. One off-line Xi atom has
the predicted half-rank negative tensor sector. The missing map is a form-preserving embedding of
all formed sectors into one fixed-aperture arithmetic target; assuming it is the old completeness
gate.

F306 — Ordinary nuclearity does not kill the completion class. Nuclear maps extend to completions
and projective tensor products preserve Deninger nuclearity, while the actual fixed-tail tower is
not Mittag--Leffler. Today's Suzuki theorem is sharper: every fixed log jet remains nuclear and any
uniformly bounded response stays sublinear. Thus nuclear/solid vocabulary without a new source
transition law cannot force the unique Roos primitive.

FAIL-43 — Tensor-amplification, nuclear-exactness, and projective/metaplectic-coherence shortcuts
retired. Tensor amplification lacks the fixed-target embedding; nuclearity lacks stable images;
scalar FE/Schwarz projective data gauge-trivializes, while genuine nonsplit FE extensions exist at
every grade.

F307 — Literal arithmetic has a faithful profinite leg: packet units are exactly compatible
automorphisms of all away-prime cyclotomic towers, their topology is compact and totally
disconnected, and Frobenius is literal prime-power action. A connected Lorentz flow cannot descend
nontrivially into this automorphism group. This is a real fracture, but F262 already locates it:
profinite provenance and Hilbert/Gamma completion are singular topologies joined only by a partial
comparison relation.

CANNOT-155 — It cannot infer RH from connected-versus-profinite topology alone. Claiming that the
analytic Xi flow descends through the profinite action supplies the missing bi-completion comparison;
local Haar modulus or global adelic unimodularity is nonselective for the same reason.

F308 — Formation-depth execution has an exact category profile. With the corpus gauge
`G(x)=|sum x_n|+2 sum n|x_n|`, its domain is a separable Banach space compactly and densely
embedded as a proper sigma-compact `F_sigma` meagre subspace of the observer `ell^2` completion.
Any Hilbert-null sequence whose codiagonal tends to a nonzero value must escape every bounded
`G`-set. This is proved on paper in `ULF-FDBE-1` from the Lean compact-sublevel, exhaustion, and
bounded-recovery laws.

F309 — Countably many compact route gauges cannot cover an infinite-dimensional observer space.
For compact linear maps `T_m : E_m -> H`, every image is a countable union of nowhere-dense compact
sets, so `H \ union_m range(T_m)` is dense residual. Adding finitely, countably, or recursively
enumerably many compact/nuclear route completions cannot supply global admission.

CANNOT-156 — It cannot use Baire measurability, Pettis automatic continuity, or Borel graph
regularity to force grade zero on the existing source domain. Those theorems require a nonmeagre
ambient subgroup or its equivalent; the literal executable core is dense meagre `F_sigma`, while
its codiagonal is continuous only in the strictly finer formation norm.

FAIL-44 — Baire automatic-continuity selection retired. Positive survivor: nonzero horizontal
response is exactly certified by unbounded formation-depth escape, and every countable compact
route atlas misses a residual set. Any source mechanism must create one essential noncompact
coverage operation rather than add another local compact gauge.

F310 — The completed Deninger Green/incidence bridge is already norm-faithful and dense at the Xi
completion. Its algebraic source range is nevertheless exactly the finite-jet range, dense and
nonclosed; the reflected-Gaussian horizon is nonzero on every divisor copy and lies in
`closure(range) \ range`, both before and after incidence/provenance transport. Completing the
source metric therefore admits the missing infinite history at every horizontal grade.

CANNOT-157 — It cannot close RH by calling common recovery isometric, completing its dense range,
or invoking completeness plus density. The completed receiver faithfully transports the same
singular horizon; it neither annihilates nor orients its horizontal coefficient. Surjectivity after
completion is admission, not selection.

FAIL-45 — Complete-metric/isometric dense-landing fusion retired. It confuses closing the
finite-jet source with proving that arithmetic formation lands in a grade-zero subspace.

F311 — The literal theta/Gamma-six shell operator has a strict ideal wall, not a soft norm
estimate. Every nonblind finite shell is coefficient-faithful and weak trace class at every
horizontal grade, but ordinary trace class exactly at grade zero; universal trace-class admission
over Xi support is RH. Its full corrected source differs from this principal operator by an
unconditionally trace-class remainder, so the obstruction is the principal completion class.

F312 — Prime formation is faithfully compact but intrinsically nonproper: its range is nonclosed,
it has no positive lower frame bound, and adjoining any compact boundary reporter leaves a common
orthonormal escape. Any reporter restoring a joint lower bound is necessarily noncompact and
cannot factor boundedly through the prime sampler. Isometric change of gauge preserves this wall.

CANNOT-158 — It cannot infer anything about Xi support from the residual complement of countably
many compact route ranges. A meagre countable atlas can still contain every member of the
countable Xi divisor set. Baire proves observer incompleteness, not divisor exclusion.

F313 — The universal Laurent source contains two involutions, bare reflection `R` and transported
reflection `R_T`, with products `R R_T=diag(T^-1,T)` and `R_T R=diag(T,T^-1)`. Their commutator is
`diag(T^-1-T,T-T^-1)`; they commute exactly when `T^2=1`, and under the positive Gamma character
`T=e^a` exactly when `a=0`. The curved differential `R_T-R` squares to the quadratic Laurent ghost.

CANNOT-159 — It cannot impose commutative descent of bare and transported reflection as an
innocent coherence law. Their failure to commute is already the pre-divisor anomaly; demanding
commutation or an integral physical frame is a sharp grade-zero receiver unless literal source
formation independently supplies that descent.

F314 — Today's integral-rigidity modules separate genuine arithmetic from inserted integrality.
Finite permutation Frobenius--Verschiebung traces see only fixed-point counts and degree defect,
not rapidity. Conversely, two odd integral superghosts at prime-square determinant, all-scale
integral conformal trace, one common dense prime-weld integral Lorentz frame, or one dyadic
integral relative-reflection frame each force grade zero. Every latter condition is an external
landing hypothesis, not a consequence of the integral Laurent source.

CANNOT-160 — It cannot obtain selection from “the source is integral.” Laurent coefficients are
integral before specialization, while evaluation `T -> e^a` is real-valued. A numerical index,
integral trace, or integral matrix after physical evaluation requires a separate strict landing
theorem; that theorem already carries the selection content.

F315 — The Meyer half-density comparison makes completion escape pre-divisor and exact. The strong
source range is contained in the analytic inverse domain; when the Hilbert Koszul coordinate is
invertible, the quotient vanishes exactly when its inverse preserves strong-source provenance.
At an off-line Xi fibre this quotient is nonzero. Dense Hilbert realization therefore does not
repair the source-range fracture.

F316 — Critical completion quantizes the continuous horizontal rapidity. The unique Route-R Roos
primitive is the literal negative tail; its class vanishes exactly for summable coefficients. At
the moving first-trace wall every `t>0` represents `-h`, every `t<0` represents `+h`, and `t=0`
represents `0`, where the prime-harmonic class `h` is nonzero. Magnitude disappears; only causal
orientation survives modulo summable work.

CANNOT-161 — It cannot select by making the horizontal grade small, continuously deforming it, or
summing the signed functional-equation pair. Completion has already collapsed every nonzero
magnitude to the same two oriented classes, and reflection cancels `h+(-h)` automatically. A
surviving law must detect the quadratic pairing or forbid the oriented history itself.

F317 — Square-zero totalization is nonselective. Any composable pair of linear maps can be enlarged
to an injective genuine complex while retaining its original curvature on the compensating
summand. The source also contains an explicit all-cross Big-Witt compensator whose second ghost
cancels the full physical diagonal at every grade. Algebraic exactness can always relocate the
anomaly.

CANNOT-162 — It cannot close RH by demanding `d^2=0`, BRST closure, or existence of some
null-homotopy. Those conditions admit universal stabilizations and the literal nonlocal
compensator. A valid completion must restrict admissible compensators by source provenance,
effectivity, or formation cost and prove that restriction before divisor specialization.

F318 — The actual strict-preclosure prime edge has a source-native ideal filtration: its all-prime
correction is Hilbert--Schmidt but not trace class, its harmonic coordinate differs from `1/p` by
an `ell^1` term, and its twist by `p^t` is summable exactly for `t<0`. Reflected ideal phases agree
exactly at `t=0`. This is a pre-divisor orientation wall on literal prime data.

F319 — Information-neutral functional-equation packet lifting does not identify the reflected
completion sectors. Common recovery preserves KL information, measure class, and mutual
singularity; off-wall prime-Poisson sectors remain disjoint and admit no nonzero closed
source-linear sewing. Thus information neutrality transports the anomaly faithfully rather than
annihilating it.

FAIL-46 — Information-neutrality/trace-ideal shortcut retired. The available lift acts on observer
laws and preserves off-wall superselection; it does not supply the missing same-source closed
correspondence in the prime completion topology.

F320 — Regularized-determinant holonomy also fails as a linear selector. The forced `S_2\S_1`
source has a genuine `det_2` anomaly, but its fully labelled functional-equation reflection double
has product one at every grade. The nonzero information survives only in higher interaction
ghosts: complete all-cross cancellation kills the quadratic ghost while the determinant retains a
strict negative quartic and, integrally, an infinite ghost tail.

FAIL-47 — Scalar or projective determinant-holonomy selection retired. Reflection Cartier
trivialization is unconditional. Any live mechanism must control effectivity or admissibility of
the whole interaction-level completion, not the signed scalar cocycle.

F321 — Actual cofinal theta Green boundaries do not approach a positive form. They retain one
fixed positive and one fixed negative direction with limiting values `+1/6` and `-1/6`, uniformly
away from either semidefinite cone. Reflection-balanced Toeplitz models likewise have zero signed
index and determinant one while retaining unsigned defect energy `2n`. Mixed inertia is persistent
carrier structure; signed cancellation is not absence of formation.

CANNOT-163 — It cannot polarize away the fixed negative direction, use signature/index zero, or
use determinant one as a vacuum law. Hyperbolic pairs are invisible after signed/group-completed
decategorification. A selector must prove both effective defect sectors empty, not merely equal.

F322 — Critical completion is an exact occupation quantizer. For every nonzero grade `t`, Route-R
external tensor curvature is the same universal class `h tensor h`; its `(p,q)` representative is
exactly the Big-Witt physical atom `1/(pq)`. The class detects zero versus nonzero grade but erases
every nonzero rapidity magnitude.

F323 — Literal Gamma-six paired boundary cost does not share that collapse: it is
`2(cosh(t)-1)` and strictly separates positive rapidities. No function on external completion
curvature can reconstruct this cost; grades `1` and `2` already have equal curvature and unequal
cost. Lean: `RHTower.RouteRCompletionQuantumCostSeparation`.

F324 — The two levels are jointly complete. The marked profile `(oriented completion class,
Gamma-six paired cost)` is injective: orientation selects the sign ray, strict hyperbolic cost
recovers magnitude, and class zero isolates neutral grade. Neither coordinate is sufficient alone.

FAIL-48 — Unmarked external completion curvature retired as the universal object. It is the correct
effective occupation shadow and Big-Witt kernel, but it cannot carry formation distance, properness,
or noncompact history.

MUST-107 — Surviving higher mechanism must be two-level and source-generated: an effective
reflection-even occupation class before signed cancellation, plus a proper marked history/cost
before phase completion. RH closure requires proving actual Xi formation can recur in the completed
observer only with bounded marked history; assuming fibrewise bounded work is already an RH
receiver.

F325 — The corpus already contains the proposed marked-action closure. Literal pre-divisor Wold
polar work has a quartic proper lower bound and bounded scale-orbit work iff grade zero. Literal
Suzuki completed-source observer-jet action implies RH, and its strongest global linear bound is
equivalent to RH. Abstract completion kernel-pair non-descent and transverse repair are also already
formalized.

FAIL-49 — “Add a non-descending cost mark, then assume closed Xi histories have bounded action”
retired as higher mechanism. The mark is mathematically necessary and jointly reconstructive, but
the boundedness clause is the existing RH-complete endpoint, not its producer.

CANNOT-164 — It cannot move the unknown from vanishing defect to bounded action, descent,
saturation, or faithful comparison and call that a mechanism. Each is already an exact receiver in
the corpus. Next law must generate source-history admissibility from stricter source formation
semantics and charge every compensator automatically.

F326 — Cyclotomic-density continuation is already closed as a no-go. Finite source stages carry
literal Frobenius actions, but any entire completion retaining one new cyclotomic divisor at each
cofinal stage is identically zero; a nonzero limit needs linearly growing negative counterdivisor
degree. Finite cyclotomic compatibility does not produce a coherent completion primitive.

FAIL-50 — “Finite torsion fibres vanish, hence one holomorphic obstruction family vanishes by the
identity theorem” retired. The corpus proves exactly this collapse and shows the missing datum is
the source-generated counterdivisor/primitive compatibility, not analytic continuation.

F327 — Compact-versus-split and periodic-versus-positive completion are already exact receivers.
The reciprocal-character field has compact and split real forms with different admission domains;
prime `5` has a literal period-two depth clock whose canonical Gamma-six bistochastic completion
returns exactly iff grade is zero. Intertwining that clock with physical completion is RH-bearing.

FAIL-51 — Cyclotomic rotation/Lorentz boost intersection and locally-finite-to-positive quotient
selection retired as mechanisms. Their rigidity is valid, but the required coefficient-faithful
intertwiner is the already isolated source-completion producer.

F328 — Every off-line conjugate pair contributes one exact hyperbolic plane: positive and negative
inertias both increase by one. Entire functional-equation and Beurling countermodels also realize
these planes. Lorentzian/Krein geometry is therefore the correct universal carrier of off-line
occupation, but functional equation, entire continuation, and small perturbation do not exclude it.

F329 — Stable hermitian decategorification is too coarse. Over the quadratically closed complex
source, nondegenerate quadratic forms and their Grothendieck--Witt completion retain only rank;
Witt cancellation, signed index, determinant one, and zero signature all erase effective metabolic
pairs. Rapidity and Gamma cost require an unstable, source-marked metric refinement.

CANNOT-165 — It cannot identify the new mechanism with Lorentzian geometry, modular flow,
Grothendieck--Witt theory, or a positive polarization alone. Each already explains a shadow, while
explicit off-line countermodels satisfy the same carrier laws.

F330 — Higher Schatten/cyclic repair is also present. The anomaly is Hilbert--Schmidt but not trace
class; products of two Hilbert--Schmidt operators are trace class; source cyclic cocycles annihilate
literal Hochschild boundaries; the quartic hyperbolic amplitude lands coefficient-faithfully in
the physical degree-six boundary. Physical cyclic descent is nevertheless exactly RH.

FAIL-52 — “Move one trace degree higher” retired as producer. Higher cyclicity supplies the correct
interaction reader but not the source-to-physical descent that would annihilate its nonzero
effective amplitude.

F331 — The surviving common interpretation is effective metabolic birth under completion. Finite
exact source stages have no defect object; singular completion may create a balanced hyperbolic
pair that is zero in every group-completed shadow but nonzero as an effective object, with external
occupation recording birth and Gamma cost recording its size.

MUST-108 — A genuine higher law must prove, before Xi specialization, that literal arithmetic
formation completion cannot create effective metabolic pairs from compatible finite proof
witnesses. It must retain object-level effectivity, primitive provenance, and nonlinear cost;
proving only vanishing after group completion, cyclic pairing, phase quotient, or bounded action
does not discharge this gate.

F332 — Compact inverse-limit repair is obstructed at tower level. The finite Euler/cyclotomic
source tower has surjective bonds, while every fixed-tail Roos bond misses a nonzero head; no
levelwise-surjective natural comparison can connect them. The canonical oriented conductor
regulator exists only by retaining the horizontal holonomy and therefore preserves, rather than
exactifies, the Roos class.

FAIL-53 — “Use finite-stage compactness or a surjective profinite tower to manufacture the global
primitive” retired. Any live source comparison must be relative/mapping-cone valued and
non-surjective; ordinary compact descent necessarily erases the completion anomaly it must control.

MUST-109 — The no-metabolic-birth theorem of MUST-108 must be proved on the relative comparison
between arithmetic/profinite formation and analytic tail completion. It cannot be a functor on
either completion separately: the anomaly is exactly their noncommuting comparison.

F333 — Today's fusion modules identify the actual Xi boundary without interpretation slack.
Arithmetic formation meets the analytic vertical boundary only at neutral grade; completion birth,
nonzero Roos class, strict physical transport, and failure of compact recurrence descent are the
same pointwise event. The integral cofinal Tate index and its unique coherent primitive classify
that event but do not prevent it.

F334 — Endogenous grammar birth is already constructed. The corpus has exact rule, sequential,
and analytic examples where completion creates a new executable law, proves completion birth needs
unbounded formation depth, and source-generates the next minimal challenge. “Effective metabolic
birth” is therefore an interpretation of the Xi event, not a new production law.

FAIL-54 — Grammar birth or a bare no-metabolic-birth axiom retired as the higher mechanism. The
former is already present; the latter names the desired conclusion unless arithmetic admissibility
of proof histories is independently generated.

F335 — Exterior/Hodge and curved-differential interpretations are already exact. The source has an
alternating degree-one cup, positive cup-star reader, and a completed odd operator with
`D^2=-K(a)I`; off centre that curved complex is contractible, and supertrace, matrix-factorization,
local-singularity, and ordinary derived-base-change shadows are blind to selection.

FAIL-55 — Odd exteriorization, curved DG/Clifford completion, and matrix factorization retired as
producers. They correctly encode the paired Gamma curvature but do not constrain which analytic
characters occur.

F336 — The rational-adelic multiplier already supplies more than a K1 analogy: every prime gives a
genuine nonzero `HH1` unit cycle, a coefficient-faithful corrected Bruhat cycle, Kummer period
`log p`, a nonerasing Xi cap, and exact Gamma-orientation parity. Ordinary dagger reverses the
source class and cancels the physical sign. No actual algebraic-K1/cyclotomic-trace/TC realization
or archimedean Gamma regulator comparison is constructed.

CANNOT-166 — It cannot invoke standard K-theory/THH/TC additivity as the missing selector. The
required anomaly is a nonlinear reflection cross-effect; ordinary additive stabilization and
reduced cyclotomic traces erase its orientation. A viable cyclotomic law would have to construct,
not assume, a coefficient-faithful integral two-orientation Gamma regulator.

F337 — Self-amplification is also classified. Tensor powers of one indefinite packet have
unbounded negative index, but selection requires injective form-preserving realization in one
fixed finite-negative-budget target. For the actual Route-R completion quantum, canonical diagonal
multiplication back to the corona kills the external curvature because the wall tangent is
square-zero.

FAIL-56 — “The anomaly replicates and must fit back into its rank-two boundary” retired. Corpus
supplies replication but refutes the canonical curvature-preserving fold; supplying another fixed
target embedding is the existing tensor-admission endpoint.

F338 — The strongest surviving interpretation is proof-history descent. Finite semantic completion
can identify two executable repairs while a radially calibrated analytic potential assigns them
opposite values. Three-slot proof erasure, dagger confluence, equality of those provenances, and
neutral horizontal grade are exactly equivalent for the canonical half-density potential. This
explains the unique Roos primitive as a failed completed null-homotopy, not a new object class.

F339 — Exchangeability cannot manufacture that descent. Three-slot deletion exposes exactly the
square of the two provenance laws; common recovery preserves its Jeffreys information, and
independent depth makes the work additive. Bounded work or thinning consistency forces neutrality,
but the literal arithmetic source-to-singular-face naturality square remains unproved.

CANNOT-167 — It cannot assume proof irrelevance, dagger confluence, three-slot exchangeability,
thinning consistency, or bounded proof work after analytic completion. Each is already a sharp RH
receiver. The missing law must construct one pre-divisor arithmetic quotient on which finite proof
equivalence remains valid after singular completion and whose recovery retains the prime-harmonic
principal class.

MUST-110 — Any surviving proof-history mechanism must exhibit a zero-independent arithmetic
presentation, its native semantic equivalence, and a singular completion functor that descends the
canonical orientation potential through that equivalence. It must prove descent from source
formation rules, not from Xi fibres; existing three-slot and coherent-primitive theorems then force
every support grade to zero.

F340 — Frobenius--Verschiebung reciprocity is not spherical-trace equality. The source relation is
`V_n=n F_n^-1`; `V_n` is a degree-scaled adjoint, not the ordinary categorical dual whose trace is
automatically equal to that of `F_n`. Making the normalized analytic action unitary or identifying
the scaled adjoint with a fixed dual is precisely the existing purity/polarization endpoint.

FAIL-57 — Ambidextrous categorical dimension retired as producer. It correctly repackages the
even/odd hyperbolic ledger, but the equality that would force the two reciprocal weights together
is the missing Hodge/purity law.

F341 — `ULF-CIT-13` proves a new exact three-organ fusion. If `E(a)` is the three-slot exchange
defect of reflected logistic proof histories and `K(a)` is Gamma-six paired boundary cost, then

`K(a) * (1 - 2 E(a)) = 8 E(a)`, with `1 - 2 E(a) > 0`.

Hence `K(a)=8 E(a)/(1-2 E(a))`: Gamma cost and proof distinguishability reconstruct each other
exactly, not only at their common zero.

F342 — External completion curvature is the occupation quotient of the same proof-exchange law.
It vanishes exactly when `E(a)` vanishes, while every nonzero grade maps to the same prime-harmonic
external class. Thus proof exchange retains bounded distinguishability, Gamma retains its nonlinear
odds cost, and external completion retains only presence. Lean:
`RHTower.CompletionProofExchangeCostFusion`.

MUST-111 — Higher mechanism is now narrowed to proof-history descent, not another cost or
curvature. It must prove `E=0` from one literal pre-divisor arithmetic face/semantic law in the
singular constant-plus-`ell^1` quotient. Once that source law exists, F341 transfers the vanishing
to Gamma cost and F342 to completion occupation; existing global support theorems close RH.

F343 — Curvature is already a nonzero pre-divisor source element. Over
`Z[T,T^-1]`, the integral reflection operator satisfies
`D_T^2 = (T-1)(T^-1-1) I`; Gamma evaluation gives the physical curved suspension exactly. At every
finite cofinal Tate stage, the top coordinate of the naturality defect reconstructs that full
physical suspension. Completion exposes and quantizes source curvature; it does not create it.

CANNOT-168 — It cannot explain the obstruction as curvature, anomaly, or proof history born only
at infinite completion. Those are valid observer descriptions, but today’s integral/cofinal
theorems locate their antecedent at the Laurent source and at every finite cofinal stage.

F344 — Co-shift covariance gives a sharp source obstruction. The reflection-odd singular class is
zero exactly on the line, but off line any two-co-shift-invariant boundary containing the reflected
difference contains both eigenprofiles separately because their co-shift eigenvalues differ.

FAIL-58 — Generic source-natural proof-history/face descent retired. The live three-slot card can
survive only through a construction that explicitly breaks or replaces co-shift covariance while
retaining the forward singular mode; a faithful co-shift-natural quotient cannot do the job.

F345 — All-prime Laurent evaluation is faithful: a Laurent polynomial vanishing at every physical
unit-clock determinant `-p` is zero. No nonzero finite prime-local Laurent relation annihilates all
physical prime-Gamma determinants.

CANNOT-169 — It cannot force selection by one finite algebraic identity evaluated prime by prime.
Any producer must use genuinely infinite/cross-prime or singular structure before scalarization,
and must retain information absent from the faithful Laurent evaluations.

F346 — `ULF-CIT-13` is an exact bridge, not a producer. Its quantities reduce to
`E(a)=tanh(a/2)^2/2` and `K(a)=4 sinh(a/2)^2`, so `K=8E/(1-2E)` is the standard bounded-contrast to
hyperbolic-odds change of coordinate. Its new corpus value is the exact identification of three
readers; it does not narrow the pre-divisor source model class.

FAIL-59 — Phantom maps, `lim^1`, proof-history loss, and S-complete/GIT quotient language retired
as the higher mechanism. They supply established parent theories for finite-stage invisibility or
orbit closure, but neither prevents the nonneutral source curvature nor forces the Xi support to
its neutral fibre.

F347 — The “integral cofinal formation index” is Gamma evaluation of an integral Laurent
determinant; its physical value is complex/real analytic, not automatically an integer-valued
Fredholm index. Integrality or an integral frame selects the line only when independently produced,
so it remains an RH receiver.

F348 — The coherent completion primitive is unique when it exists and is literally the negative
tail. Its existence, source-marked convergence, shell closability, compact recurrence, index zero,
and RH are equivalent receivers. Constructing it by generic completion exactness would assume the
endpoint.

MUST-112 — Replace “make universal curvature vanish” by a transverse-support law. A viable source
mechanism must allow the nonzero universal Laurent curvature and nonzero internal Xi jets, yet
derive from literal pre-divisor arithmetic formation that the Xi conormal/support module is
annihilated by that curvature. Specialization then forces `T=1`, hence horizontal grade zero and RH.

MUST-113 — Such a law must be zero-independent, infinite/cross-prime or singular, conservative on
the internal Xi class, and incompatible with arbitrary compensators. It must explain why co-shift
covariance is legitimately broken or replaced. Defining the module over `Z[T,T^-1]/(curvature)`,
postulating a null-homotopy, or assuming support on the neutral fibre is circular.

F349 — Must distinguish differential-algebraic independence from freedom to choose arithmetic layers independently. Literal prime-residue formation is bigraded by valuation depth and interaction support: finite rectangles are jointly differentially independent, each support sector is relatively hypertranscendental over its complement, fusion adds depth and unions support, and overlap lowers breadth.
For tail-complete finite residue profiles, fusing with the fixed depth-zero source-unit carrier determines the entire next layer, although that layer is relatively hypertranscendental over the complete preceding differential field. The canonical minimal derivation- and carrier-fusion-closed field containing depth zero already exists and contains every layer (`PrimeValuationFusionCompletionLaw`). For actual pairwise-coprime unit residues its finite depth-`d` rectangles have exact rank `d * product_i phi(q_i)`. This is closure of upper-end meromorphic germs, not a norm estimate or an admissibility theorem for completed Xi; it creates unbounded depth without collapsing the grading.

F350 — The corrected completed-Xi `+2` shift is hypertranscendental over the field generated by
the genuine coordinate and every prime-zeta valuation layer. No finite or bounded-order transport
through the complete scalar valuation tower generates the actual Xi shift.

F351 — Bare rank is not conserved by the universal hyperbolic double: affine orientation,
integral recurrence lattice, and differential-transcendence rank can all change. Any rank/index
comparison must be source-marked and induced by an actual morphism.

FAIL-60 — “Equate differential law-birth rank with Krein negative index” retired. Exact finite
Kolchin ranks and exact one-negative-direction Xi blocks exist, but no source morphism identifies
them; numerical equality would repeat the forbidden bare-rank argument.

F352 — The squarefree Euler--Wick interaction quotient is one-dimensional. Its genuine packet
spans that line; Gamma-six curvature lands on the same class with coefficient `K(a)/8`, and the FE
replica construction realizes the same class as one split-signature/Krein direction.

FAIL-61 — Adding “one interaction direction” to “one Krein direction” is double counting. Corpus
bridges identify them as two readers of one reflection charge, so no finite negative-index budget
is exceeded.

F353 — Source-horizontal Stokes flatness is automatic after tuning the differential to holonomy
`exp(a)`. Untwisting to the fixed Deninger differential is possible exactly at `a=0`; global fixed
untwisting is RH. Flatness relative to a moving connection is therefore not a selector.

FAIL-62 — One-dimensional holonomy, FE inversion, or covariant Stokes closure retired as
producers. Scalar FE gluing is gauge-trivial, and the source row--column loop already fixes the
normalized interaction for every grade; demanding fixed-frame triviality is the RH endpoint.

F354 — Common recovery is information-neutral but not holonomy-neutral. It preserves
measure-class equivalence and singularity, while recovered packets can carry arbitrary additive
or nonabelian cocycles. Exact vertical bidescent likewise preserves arbitrary horizontal
holonomy unless an independent anchor is supplied.

FAIL-63 — Recovery uniqueness, minimality, or information neutrality alone cannot kill the
horizontal anomaly. They reconstruct whatever cocycle the source carries.

F355 — The actual nonzero Xi leading conormal is closed in a determinant-one resolved
prime/depth frame for every horizontal grade. The triangular frame retains reciprocal Wold--Gamma
clock ratios and uses its off-diagonal BV mass as an exact compensator. Forgetting those diagonal
clocks recovers scalar curvature; scalar closure on the same conormal is exactly RH.

CANNOT-170 — It cannot combine `D^2=curvature` with resolved closedness and infer curvature
annihilation. The resolved complex already supplies an unconditional off-line compensator. A live
law must first prove that this compensator is inadmissible under independently generated source
structure.

F356 — Relative to the neutral resolved frame, the entire grade deformation is the faithful
unipotent shear
`(z1,z2) -> (z1 + a * normalizedPotential(i) * z2, z2)`.
It fixes the horizontal subobject and vertical quotient, hence is invisible on the associated
graded, but moves the distinguished source splitting. Every finite prime/depth cell detects `a`;
for fixed prime the shear tends to identity with depth.

F357 — Two independently labelled world observables have scalar common commutant; after adjoining
an arbitrary discrete clock, every equivariant refactorization preserving both is clock-only.
Adding labelled clock projectors and shifts reduces it further to one clock-origin translation
times one scalar, without a cardinality restriction on the clock.

CANNOT-171 — Relative hypertranscendence forbids differential-rational synthesis across support
sectors but does not forbid an external direct-sum shear. Likewise, commutant rigidity cannot be
applied until its two observables are constructed from the literal arithmetic source and proved
preserved. Merely naming horizontal/vertical coordinates as physical labels would assume the
desired fixed splitting.

MUST-114 — The sharp next gate is source-generated splitting rigidity. Construct two
zero-independent, pre-divisor observables on the prime/depth--Xi extension whose common commutant
is block diagonal, and prove formation/recovery preserves them. Then the grade-relative unipotent
gauge of F356 must be identity; positivity of its literal potential forces `a=0` on every Xi copy,
and the existing support theorem closes RH. Without the source construction and preservation
proof, this is only an exact reduction, not a producer.

F358 — Source-marked exactness/provenance topologies are generated by survival/death tests. Their
convergence theorems say endpoint exactness is eventually preserved because that is how the
topology was defined; they do not independently force exactness of the arithmetic completion.

FAIL-64 — Weyl--parabolic self-opposition retired in its naive form. Actual Xi reflection sends
`a` to `-a` inside the same triangular resolved-frame family; no source theorem swaps its two
axes. Adding that swap assumes a second flag, and the ternary-formation countermodel already has
an involution fixing the observer, exchanging legs, and acting by `-1` on a nonzero charge.

F359 — Pre-divisor Meyer--Koszul completion escape is the exact failure of inverse-closedness.
When the Hilbert Koszul operator is invertible, escape vanishes iff its inverse preserves strong
source provenance, equivalently iff the strong source coordinate is surjective. Every off-line Xi
copy has nonzero escape at every prime.

CANNOT-172 — It cannot postulate spectral invariance, holomorphic-functional-calculus closure, or
bilateral resolvent preservation as the higher law. On the literal Meyer source each is already
the RH-strength inverse-preservation endpoint; an independent source construction is required.

F360 — Arithmetic discreteness is selective only when one common frame survives formation. Two
odd power sums of a positive reciprocal pair with determinant `p^2` force the neutral pair; an
all-scale integral conformal trace forces zero grade; and a fixed rank-two integral lattice for
the dense prime-log Lorentz action forces zero rapidity. Finite permutation
Frobenius--Verschiebung traces instead see only fixed-point counts and degree.

CANNOT-173 — It cannot infer an integral completion index from integral finite source stages.
Individual integer shadows and finite permutation traces are blind; the missing datum is one
source-produced lattice/frame carried unchanged through the analytic completion.

F361 — Local spectral scalarization destroys orientation before any asymptotic issue. The actual
matched CCM chiral matrix at reporter `r` is special-orthogonally conjugate to that at `-r`, so
its characteristic relation and full unframed unitary orbit are reflection-blind. The external
source shear frame still recovers `r` exactly.

F362 — FZZ gives an exact history/quotient split. The balanced external-Gamma amplitude recurs to
`1` at arbitrarily large nonzero momentum, while its unwrapped phase is strictly increasing and
its Ward delay has a unique vacuum minimum. Normalized replica differentiation cancels every
replica-independent external factor, and admissible cubic phase gauges change the delay without
changing the normalized Ward profile.

F363 — The causal-depth Gamma source is faithful but every regular Hilbert/trace completion is too
smoothing. Its infinite feature has exactly the declared feature-sector kernel, yet fixed log
jets, subexponential functional calculus, bounded generalized inverses, projection cutoffs, and
arbitrary biunitary motion remain trace class/Hilbert--Schmidt and give only sublinear Ward work.
The canonical two-leg inverse gain leaves the Hilbert graph domain by prime-harmonic divergence.

F364 — The new Kloosterman modules expose a source-polarization law. Keeping ordinary physical
residue coefficients on both legs retains a signed cross-modulus kernel and an exact Hermitian
Gram interaction. Fourier-completing both legs collapses the same carrier to inverse-residue
correlation. Equal-modulus complete correlations are elementary Ramanujan coefficients; the only
cancellation-bearing part is incomplete and cross-modulus.

MUST-115 — Any higher completion law must be genuinely polarized: retain one arithmetic/provenance
leg while completing the other, and prove an exact reconstruction law before diagonal
scalarization. Symmetric two-leg completion, local spectra, fixed Hilbert graphs, or endpoint-made
topologies erase the anomaly. To close RH, the mixed pre-divisor interaction must source-generate
either the common lattice of F360 or a uniform cross-cell quotient gap; existing integral-frame,
bounded-splitting, and bilateral-moderation theorems then force `a=0` on every Xi support copy.

F365 — Ordinary completion idempotence is grade-blind. The actual Gamma-six transported
reflection carrier is an idempotent rank-one oblique projection for every horizontal grade;
functional-equation conjugation sends its adjoint from fibre `a` to fibre `-a`. Same-fibre
self-adjointness occurs exactly at `a=0`, but doubling the reflected fibres makes every grade
self-adjoint.

CANNOT-174 — It cannot use idempotence, monadic localization, cross-fibre dagger compatibility,
or doubled self-adjointness as selection. Same-fibre dagger is already the RH endpoint unless a
literal source law constructs it independently.

F366 — Logarithmic one-port accumulation does not force the grade to vanish. On maximal logarithmic
graph domains, inverse-log multipliers give explicit bounded upper-shear splittings on `ℓq` and
`c0`. Finite-cell detectability plus convergence of each shear to the identity therefore does not
create a global obstruction by itself.

FAIL-65 — Idempotent/dagger completion and accumulated one-port shear retired. Both repackage
known grade-dependent carriers without excluding their explicit off-line models.

F367 — Derived selection geometry already computes the universal wall torsion. Its source
orientation line is `R/(q-1)`, its physical two-leg incompatibility module is
`(R/(q-1))²`, its `Ext`/`Tor` and Fitting support lie on `q=1`, and local ambidexterity curvature
generates the same wall ideal. Arithmetic pullback has a nontrivial fibre exactly when
`Re ρ = 1/2`.

CANNOT-175 — A wall-supported derived, matrix-factorization, Fitting, or curvature object cannot
select its own support. Its internal identities become zero or vacuous off the wall; demanding a
nonzero fibre at every Xi divisor point is exactly RH, not a producer.

F368 — Proof irrelevance identifies proofs, not structured formation witnesses. Corpus proof
erasure is already equivalent to vanishing affine residue. The coherent-primitive fibre is a
subsingleton, but it is inhabited exactly when the completion/Roos/properness index vanishes.
Uniqueness therefore cannot manufacture existence.

FAIL-66 — Proof identity, confluence, and subsingleton completion retired as automatic producers.
They erase presentations only after the same obstruction has vanished.

F369 — Fresh audit reverses the viable selection shape. The corpus has independently nonzero
pre-divisor source classes and separately has objects supported only on the neutral wall. What is
missing is neither another obstruction nor another wall object, but a coefficient-faithful
*survival transport*: a source theorem forcing one nonzero arithmetic class to land nontrivially
in a wall-supported completion.

MUST-116 — Any survival transport must be constructed before divisor specialization, be inhabited
by an arithmetic theorem independent of RH, and preserve nonzeroness under formation/recovery.
Then target support forces `q=1`, hence `a=0`, on every Xi copy. It cannot infer survival from the
wall object itself, replace existence by uniqueness, or hide the conclusion in same-fibre dagger,
positivity, moderation, or properness.

## 2026-09-02 — ULF-SLC-001 (share-ledger ceiling / Kuznetsov producer): holomorphic half closed in Lean
Card moved to `1-in-progress/universal-law-field/ulf-share-ledger-ceiling-kuznetsov-producer.md`.
Lean-closed this session (all in `HTGeometry`, wired, axiom-clean): the level-one holomorphic
Poincaré series `P_m` as cusp forms; `𝒟` as a measure-theoretic fundamental domain for `PSL₂(ℤ)`;
the strip unfolding; `⟨f, P_m⟩ = 2(4πm)^{1−k}Γ(k−1)·conj(a_f(m))`; the Petersson inner-product
space of cusp forms (positive definite, finite dimensional); the Fourier coefficients of `P_m`
through Kloosterman sums and `J_{k−1}`; and `petersson_formula_levelOne`.
Open and decisive for the card: the spectral (Maass/Eisenstein) Kuznetsov formula, whose
continuous spectrum carries `|ζ(1+2it)|^{−2}` — the only place ζ's zeros enter the ledger. No
foundation for it exists in mathlib or the corpus.
## 2026-09-02 — ULF-SLC-001 retired: the automorphic producer is a dead end for RH (paper proof)
Verdict written into the card (now `5-failed/ulf-share-ledger-ceiling-kuznetsov-producer.md`):
Petersson and Kuznetsov contain ζ only on `Re s = 1` (zero-blind); the Selberg trace formula's
ζ-zero side is the Poisson-smoothed scattering density `Σ_ρ K_ρ` with peak `(1/2π)(1/β+1/(1−β))`
and floor `(1/2π)/(1+(2r−γ)²)`, so the only created positivity (`Σ_j h(t_j) ≥ 0`) yields a Class II
ledger capped at the de la Vallée Poussin width `c/log γ` (Ceiling C2); the zeros are poles of the
scattering matrix, outside every `L²` Parseval identity (structural). Route E does not need
Kuznetsov (Huxley replaces it). Survivors: C1–C4 and the level-one Petersson formula, both in Lean
(`3-formalized/petersson-formula-level-one-lean.md`). The Selberg-ledger ceiling is certified in
Lean as `RHTower/SelbergLedgerCeiling.lean`: target-file check and independent axiom audit pass;
all seven ceiling theorems use only `propext`, `Classical.choice`, and `Quot.sound`.
F370 — `GL(2)` automorphic spectral theory separates created positivity from ζ-zero data.
Petersson contains no ζ; Kuznetsov contains only `|ζ(1+2ir)|⁻²` on zero-free `Re s=1`; Selberg
places zeros in the non-`L²` scattering density, where nonnegative tests see each zero through a
pair of Poisson kernels.
F371 — The Selberg positive ledger has an exact crowding ceiling. A target zero has weight at most
`(||h||₁/(2π))(1/(1-β₀)+1/β₀)`, while every zero within height two contributes at least
`(2/(29π))||h||₁`; exclusion requires `1-β₀ < 1/((4/29)|Z|-2)`. Local zero density therefore
restricts the method to de la Vallée Poussin width.
CANNOT-176 — It cannot obtain RH by tuning a nonnegative Selberg test, widening/narrowing its
window, adding Petersson/Kuznetsov/DI/Stadlmann estimates, or placing scattering poles in an
`L²` Parseval space. Sign changes remove the only created positivity; the poles are not `L²`.
FAIL-67 — Automorphic created positivity as a ζ-zero selector retired. Positive survivors are the
level-one Petersson identity and exact Selberg peak/floor/width ceiling, all Lean-certified.
F372 — Faithful wall torsion cannot be the universal object. Over `R=k[q,q⁻¹]`, the wall element
`q-1` annihilates the source and two-leg incompatibility modules, whose annihilator is exactly the
wall ideal; a faithful `R`-module cannot have that nonzero annihilator. After arithmetic pullback,
faithfulness plus wall annihilation is equivalent to requiring every Xi fibre to lie on the wall.
FAIL-68 — Global faithful-torsion survival retired. Universal form is algebraically impossible;
divisor-fibre form is an RH-equivalent receiver. Positive survivor: selection needs a source law
that changes the coefficient category or produces descent before wall specialization.
F373 — Ordinary `K₀`/Morita quantization is also grade-blind. Morita equivalence preserves the
integral class of the actual rank-one oblique projection, which remains idempotent at every grade.
The corpus irrational-rotation `K₀` collision kills a supplied Chern charge, and bidirectional
Big-Witt integrality kills a supplied Gamma grade, but constructing either supplied integral class
on every Xi fibre is exactly the unresolved source interface/RH endpoint.
CANNOT-177 — It cannot assert that the real boost `p^a` scales an integral `K₀` class. `K₀` has
only integer scalar action, while the physical boost acts on representatives/weighted traces; an
integral lift of that real scaling is precisely what must be proved. Morita recovery alone keeps
the class fixed and sees no grade.
FAIL-69 — `K₀`, Chern trace, or Big-Witt rapidity quantization retired as automatic producers.
Positive survivor: any discrete selector must derive its integral structure from a source operation
whose preservation law still retains the oriented boost, not from completion equivalence itself.
F374 — Compact observation and positive energy do not control lifted history. Finite-support
restricted histories are dense, proper, and nonclosed in the full product; every fixed finite
observer eventually stabilizes while support cost is unbounded. Universally, any periodic observer
history admits a positive compact-resolvent lift with graph action tending to infinity and no
convergent subsequence.
CANNOT-178 — It cannot infer source recurrence, bounded formation work, or completion properness
from compact observer recurrence, GNS positivity, compact resolvent, or compact action sublevels.
Those structures admit exact escaping hidden lifts independently of arithmetic grade.
F375 — Perfect-complex decategorification is systematically extension-blind. Euler/`K₀`, every
power supertrace, every power superdeterminant, and positive squared modulus all factor through
cohomology; explicit countermodels preserve those shadows while changing polarity, extension law,
cost, or flat holonomy. The integer-doubling tower has zero ordinary inverse limit but nonzero
`lim¹`, so completion history can survive simultaneous shadow cancellation.
CANNOT-179 — It cannot use exactness, cohomology, five-shadow agreement, or finite unitary
recurrence to prohibit completion-born anomaly. A live invariant must retain controlled
null-homotopies/extension data before passage to cohomology or group completion.
F376 — Native observer descent is exact but constitutively neutral. Coimage/effectivity and
serial/parallel descent hold at Set level, yet one fixed observer with positive vertical kernel
coexists with positive-definite, degenerate, and Lorentzian forms; identical observer data can also
carry different costs or differential-algebraic status. Positive differential observers can have
arbitrarily large covariance rank and infinite hidden GNS dimension.
CANNOT-180 — It cannot derive neutral inertia, finite hidden rank, or a unique constitutive law
from observer effectivity, positivity on the vertical kernel, or jet covariance alone. Selection
must constrain how hidden extension data are formed, not merely how they descend.
F377 — The completed pseudodifferential valuation-lattice carrier and its standard apartment now
exist unconditionally, but differential coefficient automorphisms fix that apartment pointwise.
The current differential variational building records valuation coweights while forgetting the
coefficient-side anomaly it was meant to select.
CANNOT-181 — It cannot call the existing building the higher mechanism. Any useful building law
needs a second source-generated, completion-sensitive apartment/flag and a proved relative
displacement or intersection theorem; the canonical apartment alone is blind.
F378 — The two literal rational-adelic endpoints are a covariant flag, not a preserved frame.
Class-space action fixes `ε₀` and rescales nonunital `ε₁` by the inverse positive radial character;
the reduced cyclic source is `ker ε₀ ∩ ker ε₁`, so both endpoint values vanish there. The Kummer
one-cocycle retains prime logarithmic weight, but is a detector and supplies no second invariant
splitting.
FAIL-70 — Two-endpoint common-commutant selection retired. On the full source the endpoint pair
records the dilation instead of excluding it; on the reduced source it is zero and nonseparating.
MUST-117 — Surviving information type is a controlled nonsplit comparison: a formation
null-homotopy/extension together with its support or propagation cost. Any candidate must derive
uniform control from literal pre-divisor arithmetic operations, map its obstruction faithfully to
the Xi completion class, and prove that off-line effective metabolic birth requires loss of that
control. Merely postulating bounded work, a second frame, or extension splitting is an existing
RH-equivalent receiver.
F379 — Ordinary reciprocity is signed and first-order. The rational Arakelov product formula
cancels finite logarithmic trace against the archimedean boundary, and reciprocal Gamma
characters have determinant one at every grade. The same reflected pair has positive residual
`2(cosh a-1)`, equivalently the square of the reciprocal-gain mismatch, with radical exactly
`a=0`.
CANNOT-182 — It cannot use an additive product formula, determinant torsor, tame-symbol sum, or
ordinary group-valued reciprocity as selector. Group completion cancels opposite orientations at
every grade; the RH-bearing datum is the effective nonlinear residual left after that cancellation.
F380 — Functional-equation packet lifting is involutive and information-neutral only on the image
of common-kernel formation: it applies the observer involution, discards hidden history, and
regenerates that history. Exact countermodels keep observer and recovery kernel fixed while the
nonzero formation charge changes sign. Thus quotient-level reversibility is compatible with a
nontrivial lifted defect.
CANNOT-183 — It cannot infer full-source reversibility, zero index, or neutral grade from
functional-equation involutivity, KL/Jeffreys isometry, or common recovery. Those laws certify an
observer quotient, not an inverse on unreduced history.
F381 — The monoid/Hopf-envelope model identifies the quotient mechanism exactly. A unilateral
shift represents the irreversible source monoid but cannot extend to its Laurent/Hopf group
completion; the obstruction is one rank-one defect. Any quotient killing that defect makes the
shift invertible and gives a unique Hopf-envelope extension. Separately, injective post-completion
cannot erase an earlier cokernel: its dimension adds the new outer cokernel.
FAIL-71 — Automatic reciprocity/Hopf-extension selection retired. It explains how completed
observers hide an effective defect, but asserting extension before quotient is the missing
properness/exactness theorem, not its proof.
F382 — Algebraic cross-route fusion cannot create a missing rank-one differential law. A nonzero
algebraic eigenvector over a tensor-fraction extension specializes and descends to one factor;
three-face multiplicative identities force logarithmic derivatives into one-coordinate algebraic
closures. Auxiliary algebraic route factors therefore add presentation, not a new producer.
CANNOT-184 — It cannot seek the universal mechanism in an algebraic tensor product, finite
extension, or multiplicative three-face weld. A live fusion must depend essentially on controlled
completion, chronology, or nonalgebraic topology and must fail under specialization to each route
factor.
F383 — Proof exchange, Gamma completion cost, and external completion occupation are one scalar
state in three coordinates. Gamma curvature is the odds transform of the three-slot exchange
defect, the visibility complement is strictly positive, and all three vanish exactly at `a=0`.
This is exact joint reconstruction, not a source law making the state vanish.
F384 — Effective arithmetic anomalies propagate rather than localize. Centered all-cross
Big-Witt formation kills ghosts one through three but leaves a quartic determinant product; a
nonzero integral first ghost forces nonzero ghosts at every sufficiently large prime; persistent
cofinal cyclotomic zeros in a locally uniformly convergent holomorphic family force its limit to
vanish identically. These form a possible propagation-to-collapse chain only if one literal
source map preserves the same nonzero class through all three steps.
F385 — Signed nonlocal completion can still short the effective diagonal: the complete all-cross
Big-Witt source has zero ghost because its off-diagonal compensator is exactly the negative of the
physical diagonal, unconditionally. In contrast, finite and summable nonnegative cooriented Gamma
packets cannot short any nonzero grade.
MUST-118 — A viable higher law must derive, from source chronology/provenance rather than imposed
positivity, why reverse/off-diagonal compensators are inadmissible while the diagonal anomaly
survives. One concrete closure architecture is: actual integral anomaly -> forced infinite prime
tail -> persistent cyclotomic formation zeros -> normalized nonzero holomorphic limit
contradiction. Every arrow, especially integrality and persistent-zero transport, must be
pre-divisor, coefficient-faithful, and independently proved; without them this is only a diagram.
F386 — The integral propagation-to-collapse diagram fails at its first physical arrow. The
normalized Gamma-six Big-Witt second ghost is `-1/3`, so no integral source scalar-extends to it.
Unconditional integral Cartier sources exist, but a coefficient-faithful physical reporter exists
exactly on the critical line; likewise the bidirectional physical Big-Witt lift exists at grade
`t` iff `t=0`, and on every Xi divisor iff RH.
CANNOT-185 — It cannot invoke integral ghost propagation, cyclotomic persistence, or integer-index
rigidity until a new pre-divisor map makes the actual horizontal anomaly integral. Existing
physical integrality statements already contain the critical-line conclusion.
FAIL-72 — Integral-tail-to-cyclotomic-collapse retired as a producer. Its propagation and collapse
arrows are valid positive survivors; its required physical integral landing is RH-strength.
F387 — Modular geometry is an exact interpretation but not a new producer. The grade is the
Radon--Nikodym character `p^(-2|t|)`, recovered from the signed Krein current only by the singular
multiplier `p`, which does not preserve the fixed `ell^1` source ideal. A nonerasing equivariant
descent into a norm-conservative target forces `t=0`; type-III covariant traces cannot be invariant
and nonzero, while normalized measured indices erase finite and density-zero off-line sectors.
Source/Gamma naturality and modular-centralizer rigidity are already pointwise wall conditions and
globally equivalent to RH.
CANNOT-186 — It cannot obtain selection from Maharam extension, cocycle superrigidity, a finite or
semifinite trace, KMS passivity, or centralizer language alone. Superrigidity leaves the prime-log
homomorphism, type III removes absolute count, and supplying a nonerasing conservative descent is
the unresolved arithmetic theorem.
FAIL-73 — Modular-flow/centralizer trivialization retired as an automatic producer. Positive
survivor: all route readers are charts of one modular completion class, and every viable selection
law must choose its representation/completion from arithmetic rather than assume traciality.
F388 — The Lorentzian reversal has an exact Bogoliubov form already in the corpus. The positive
residual is partner occupation; all-prime Hellinger/Kakutani polarization is its square; repeating
the beta block along the natural overtone ladder gives finite Shale mass linear in cutoff and
infinite mass off wall. Regular/common-Fock implementability and common-Fock Cauchy convergence are
pointwise equivalent to neutral grade and globally equivalent to RH. Finite cutoffs remain valid,
and nonregular or incomplete-tensor sectors escape.
CANNOT-187 — It cannot infer RH from Bogoliubov conservation, Shale--Stinespring, Kakutani
singularity, finite-cutoff vacua, or orthogonality catastrophe. Those classify disjoint sectors;
they do not prove that the arithmetic source occupies the regular sector.
FAIL-74 — Fock implementability as the completion index retired as a producer. It is another exact
gauge of the already known derived completion class.
MUST-119 — The missing law is not another detector of nonzero grade. It must prove, from a literal
pre-divisor arithmetic operation, that the physical completion belongs to a uniquely forced
normal/regular folium or equivalent controlled history class. Any axiom of regularity, finite
trace, conservative descent, source naturality, centralizer rigidity, or vanishing `lim^1` merely
restates an existing RH endpoint.
F389 — Today's critical-block code isolates a genuinely source-side selection mechanism. A block
normalization containing the canonical sheet receives a continuous lift from the actual source
chart. If that normalization is formally étale and the source contains closed histories projecting
to both marked torus meridians, connected-cover monodromy forces its observation fibre to be a
singleton. This is cycle-complete formation: source histories generate the observer fundamental
group, so no nontrivial connected completion cover can remain between source and observer.
CANNOT-188 — Source-chart finiteness, integrality, path connectedness, properness, or the existence
of the lift does not supply cycle completeness. The Lean endgame still assumes formal étaleness of
the block normalization and two closed source loops with the exact generator classes. Treating
either premise as automatic merely renames the unramifiedness and sheet-selection gaps.
MUST-120 — A topological higher law must derive, from literal pre-divisor arithmetic, both formal
purity of the admissible completion and surjectivity of source histories onto observer cycles. To
close RH it must additionally realize every nonzero horizontal grade as nontrivial monodromy of
such an admissible lifted completion; cycle completeness would then force that monodromy to be
trivial, hence `exp(a)=1`, `a=0`, and `Re rho=1/2`. Without the grade-to-cover bridge this is a
source-model restriction, not an RH proof.
F390 — Higher-rank prime dynamics separates history fluctuation from horizontal grade but does not
select the grade. On two independent prime clocks the grade is already the homomorphism
`(m,n) ↦ a (m log p + n log q)`. Cocycle-superrigidity conclusions reduce a cocycle to a
homomorphism modulo a coboundary, so this exact anomaly survives their conclusion. Measure
rigidity for toral/solenoidal actions additionally assumes positive or high entropy and
hyperbolicity and classifies invariant measures; it supplies no vanishing law for the surviving
real homomorphism.
CANNOT-189 — It cannot infer neutral grade from a `×p,×q` action, a natural-extension solenoid,
higher-rank recurrence, entropy rigidity, or cocycle superrigidity. A valid selector still needs a
literal source relation annihilating the homomorphism part; assuming compact range, finite image,
unitarity, or zero periods is the existing descent/admission endpoint.
FAIL-75 — Higher-rank dynamical rigidity retired as an automatic producer. Positive survivor:
higher-rank formation can canonically isolate the invariant homomorphism carrying horizontal grade
from coboundary-valued completion history, so future laws must act on that quotient rather than on
gauge fluctuations.
## 2026-09-02 — individuation law frozen (card `0-backlog/zero-individuation-law-two-completion-producer.md`, ULF-IND-001)
F379 — Every share ledger `Σ_ρ φ(ρ)` over an FE- and conjugation-stable zero set is even in the
per-pair displacement `δ = β − ½`; first-order sensitivity exists only through half-plane cuts,
alignment singularities, or amplification. Combined with ceilings C1–C4 and the Selberg ledger
theorem, every fixed-kernel positivity certificate resolves off-line zeros only to the
archimedean density `ν(t) = (1/2π) log(t/2π)`; the `log t` of every ceiling is the Γ-phase
derivative. Zeros enter `GL(2)` spectral identities only as poles of `ξ(2s−1)/ξ(2s)`, outside
every `L²` Parseval identity.
CANNOT-182 — It cannot observe an individual nontrivial zero through any unconditional
arithmetic identity: every identity is a functional of the pair-even smoothed zero density.
Hence no card of the form "prove `Φ(source) ≥ 0` for one fixed functional `Φ`" can be a
producer.
MUST-118 — A producer must be nonlinear in the zero measure, oriented only through the
archimedean phase, an identity uniform in amplification, and crowd-cancelling. The one classical
object of that shape is the convex Littlewood mean `M_T(σ) = (1/2π)∫ log|ζ(σ+it)|dt`, whose kinks
are individual real parts. The frozen producer conjecture is the two-completion comparison: the
multiplicative (partial Euler product) and additive (Hadamard) completions have vertical
log-means differing only by the Γ-phase density on `½ < σ < 1`, with the mean provable by a
pair-even second-moment argument and individuation supplied by convexity. Bricks B1–B5 in the
card; B5 is not to be attacked before B1–B4 and a corpus search of RG, T1, D2.
F391 — Literal archimedean-only selection is false. The Gamma/functional-equation cell is closed
under a positive reciprocal quartic that plants an explicit nonreal off-line strip zero while
preserving real-strip zero-freeness, integral multiplicativity, and the completed functional
equation (`GammaCellNonrealMobility`). Gamma supplies no nontrivial divisor because it is
nonvanishing on the relevant right half-plane.
F392 — The global theta source contains irreducible diffuse information at infinity. Its positive
archimedean measure gives zero mass to the prime-power logarithms; sampling defect equals full theta
mass, reflection completion doubles the defect, and normalized defect remains one. On every
sampling gap its functional cannot factor through the samples even by arbitrary nonlinear
postprocessing (`SeamArchimedeanSamplingQuotient`, `ArchimedeanSamplingDefect`).
F393 — Prime and archimedean organs have an exact load/capacity split. The archimedean form is
uniformly definite with lower constant `4-3 log 2-pi/2`, and Weil positivity is exactly domination
of the prime operator by this form. Actual Suzuki walls are positive atomic prime mass minus
positive continuous screw mass; cofinal raw-prime contours differ from full Weil energy by one
explicit centered archimedean square (`ArchimedeanPairingDefinite`,
`SuzukiWardAtomicContinuousLightWeld`,
`XiPhysicalPrimeApertureThetaAbelEnergyPrimeCanonicalVanishingLimit`).
CANNOT-190 — It cannot call RH a theorem of the isolated Gamma factor, functional equation, or
archimedean positivity. Nor can it directly reconstruct the diffuse seam from prime samples or
dominate it as a raw measure: the channels are sampling-disjoint, and Gamma/FE cells admit
off-line mobility. Direct Hilbert--Schmidt welding is already impossible.
MUST-121 — The viable archimedean reversal is global: finite places set atomic loading/vertical
frequencies, while the full integer-theta completion supplies polarization and the horizontal
unitary axis. A producer must derive a coefficient-faithful nonlocal atomic--diffuse admission law
from literal integer formation, before divisor specialization, coupling additive Fourier
self-duality to multiplicative Euler completion. Imposed domination, Weil positivity,
self-adjointness, or completion regularity is the RH endpoint, not its source.
FAIL-76 — “Gamma alone forces the critical line” retired. Positive survivor: zeros can be treated
as resonances of failure to admit atomic Euler formation into the global archimedean theta
polarization. The exact admission mechanism remains open; no RH gate is discharged.
## 2026-09-02 — ULF-IND-001 producer refuted; survivors formalized
F380 — Lean: convergence of the Möbius Dirichlet series at one point forces `ζ ≠ 0` on the open
half-plane to its right, so the abscissa of convergence of `∑ μ(n) n^{−s}` is at least the real
part of every zero (`RHTower.riemannZeta_ne_zero_of_moebius_convergesAt`,
`re_le_abscissaOfConv_moebiusShift`). Lean: every pair ledger `φ(½+δ+iγ) + φ(½−δ+iγ)` is even in
`δ` with vanishing derivative at `0` for every `φ`; the Lagarias–Suzuki constant term never
vanishes at a half-zero of `Λ` in `Re s < ½` (`GaloisForLFunctions.RHTower.ZeroLedgerPairParity`).
CANNOT-183 — It cannot run a two-completion comparison with two unconditional sides: inside the
strip the prime series diverges everywhere and the convergent Möbius series is already the
zero-free statement. The mean-value level of the smooth Littlewood identity gives `N(σ,T) = o(T)`
only; detecting one zero needs window means of `log|ζ|` to precision `1/T₀`, and pair-even
second moments give `T₀^{−c}`.
FAIL-71 — ULF-IND-001's producer (Euler-vs-Hadamard Littlewood-mean comparison) retired. The
individuation diagnosis (parity, crowd, Landau blindness, poles-not-eigenvalues) stands and is
now three-quarters Lean-certified. MUST-118 withdrawn.
MUST-119 — Any comparison of completions must treat the multiplicative side as a regularized
family whose regularization budget is computed explicitly; unconditional convergence of that side
is the conclusion (F380). This is the budget branch of the regularization trilemma, so a
surviving candidate must exhibit a budget that is *not* the divergent positive mass — otherwise
it is W1.
## 2026-09-02 — literal Euler/theta contractivity decided (ULF-EHC-001)
F394 — On additive log/Fourier half-density `L²`, the exact finite Euler operator
`E_S = prod_(p in S)(I-p^(-1/2)tau_(-log p))` has norm
`prod_(p in S)(1+p^(-1/2))`. Multiplicative independence of primes supplies the simultaneous
maximally expansive phase by Kronecker; reciprocal-prime divergence makes these norms cofinally
unbounded. No raw bounded or contractive Euler operator completion exists on this carrier.
F395 — Literal formation and critical-axis selection are different laws. Finite Euler action is
coefficient-exact on the even-Schwartz theta source; joint formation/recovery moderation is exactly
the unitary half-density axis; absence of a completion-born arithmetic boundary is exactly RH.
None of these makes joint admission automatic.
CANNOT-191 — It cannot mean raw Euler-product contractivity on full theta half-density `L²`, nor
can scalar norm-normalization be the selector: raw norms diverge, while normalization makes every
finite stage contractive independently of horizontal grade.
MUST-122 — Any surviving automatic-admissibility theorem must be a pre-divisor relative graph/form
identity. It must couple forward formation, reflected recovery, and archimedean subtraction so the
cofinal expansive prime phase becomes an exact boundary term; asserting boundedness, bilateral
moderation, boundary freedom, or Weil domination merely states the RH endpoint.
FAIL-77 — “Literal Euler completion acts contractively in theta polarization” retired in its raw
operator meaning. Positive survivor: exact cofinal norm growth identifies the missing object as a
relative completion index/cancellation law, not an Euler operator on one Hilbert completion.
F396 — Lean closes ULF-EHC-001: literal half-density Euler cutoff norm is exactly
`prod_(p<=N)(1+p^(-1/2))`, tends to infinity, is not uniformly bounded, and has neither strong nor
weak bounded-operator completion (`LiteralEulerHalfDensityContractionNoGo`). Axioms are only
`propext`, `Classical.choice`, `Quot.sound`.
F397 — Euler formation is automatically isometric only after the polarization is allowed to move.
For each prime, multiplication by the inverse local factor is a unitary from the archimedean fiber
to the Euler-weighted semilocal fiber, and the Hardy--Titchmarsh square commutes exactly. This holds
for every prime before any divisor and therefore explains admission but cannot select RH
(`HardyTitchmarshSemilocalSquare`).
CANNOT-192 — Replacing one fixed theta Hilbert space by the natural Euler-weighted Hilbert bundle
does not finish the mechanism. Its finite-site log metric is additive, but even after removing the
linear prime shell its central prime-square mode is `-1/p`, so the global absolute metric diverges.
Neither fixed-fiber contraction nor unrenormalized moving-fiber unitarity can be the selector
(`SoninSemilocalMetricLog`).
MUST-123 — “Automatic admissibility” can now mean only canonical extension of the moving
semilocal polarization through the all-place theta completion after a source-forced relative
subtraction. The required theorem must derive that subtraction from literal integer/Poisson
self-duality, preserve unsquared Euler coefficients, and prove the residual completion boundary is
zero. By `ArithmeticFormationCompletionBoundaryFusion`, universal residual-boundary vanishing then
forces every Xi occurrence to have neutral grade and closes RH.
## 2026-09-02 — anchor law frozen (card `0-backlog/anchor-law-inner-band.md`, ULF-ANC-001)
F381 — Every unconditional zero-free statement is the reach of an anchor (an unconditional
nonvanishing value) against the archimedean crowd: Euler product (`Re s > 1`), pole (de la Vallée
Poussin, Vinogradov–Korobov, Littlewood's `(log log t)/log t` saturation under Lindelöf), Bochner
positivity of `Φ` (real axis), Maass–Selberg (Lagarias–Suzuki approximants), mollifiers
(proportion `1 − c/θ`, `c ≈ 1/3` against Levinson `0.3474` and Conrey `0.4088`), Waldspurger
squares (central twists of GL(2)). The one anchor on the line is the on-line zero set: the first
Laguerre inequality of `Ξ` at `t = γ` forces every off-line pair to have `δ ≥ c/log γ`
(identity `Ξ'² − ΞΞ'' = Ξ² Σ_z (t − z)^{−2}`), the dual of the pole's band.
CANNOT-184 — It cannot obtain an interior zero-free set of positive measure from growth or
positivity: the pole's reach saturates at `(log log t)/log t` and interior multiplicative anchors
are the conclusion (F380).
MUST-120 — Any surviving mechanism must either manufacture an anchor of unbounded length
(the mollifier route, capped at `1 − c/θ` for finite `θ`) or anchor on the line itself. The
first line-anchored target is the unconditional first Laguerre inequality of `Ξ` at every `t`
(inner band `c/log γ`); it fails for every de Bruijn–Newman deformation `Ξ_s`, `s < 0`, so no
kernel-positivity proof exists and a proof must use the arithmetic at `s = 0`.
## 2026-09-02 — scalar completion retired; full scale-history law proved (ULF-PSH-001/2)
F398 — Literal valuation/Poisson fusion already preserves the unsquared Euler coefficients and
reconstructs the scalar completed current `−a ξ′(a)/ξ(a)` for `a>1`; moving head–tail transgression
already has zero scalar trace unconditionally. Scalar subtraction/residual vanishing is therefore
not the missing selector (`XiAperturePoissonEulerLogDerivCompletion`,
`EulerPrimitiveCommonTestBoundaryTransgression`).
CANNOT-193 — It cannot be a same-fibre scalar or bounded local metric counterterm. The orbital
response `m log p` is nonzero modulo bounded responses, the central prime-square shell is `−1/p`,
and positive Hilbert mass cannot cancel the positive principal shell (`SoninSemilocalMetricLog`,
`ConnesSemilocalOrbitalSourceClass`).
F399 — Full Poisson aperture history canonically normalizes every positive orbital clock:
`ψ_t(a)=2t√a e^(−ta)`, `||ψ_t||²=1`, and
`<ψ_t,ψ_u>=4tu/(t+u)²=sech²((log t−log u)/2)`, with equality to one iff `t=u`.
Thus literal integer/Poisson formation forces the missing off-diagonal cross-aperture kernel
(`PoissonScaleHistoryFrame`, ULF-PSH-001; Lean proved).
F400 — For `t=m log p`, the scale-history lift absorbs the unbounded orbital clock while leaving
the external unsquared Euler amplitude `p^(−m/2)/m` untouched. Its remaining global obstruction is
exactly the principal `m=1` harmonic shell, consistent with the forced `6/p` diagonal gain anomaly;
higher modes/remainder are summable.
FAIL-78 — “Canonical scalar metric-anomaly subtraction plus vanishing scalar residual” retired as
RH mechanism: both effects already occur without RH. The signed-subtraction survivor was tested
next and also failed (FAIL-79).
MUST-124 — Withdrawn: fixed principal-shell cancellation has wrong selection polarity.
## 2026-09-02 — ULF-ANC-001 inner-band target retired; survivors formalized
F382 — Lean: `ΞC'² − ΞC·ΞC'' = ΞC² ∑_q (z − a_q)⁻²` off the divisor (termwise differentiation of the
corpus's Mittag-Leffler expansion), the exact pair term `−2/δ²` at a real point, and the inner
band as an implication (`RHTower.XiLaguerreZeroSumIdentity`). Lean: a positive, even,
log-concave kernel whose Fourier transform violates the first Laguerre inequality
(`HTGeometry.LaguerreKernelCounterexample`).
CANNOT-185 — It cannot anchor on the line: the first Laguerre inequality of `Ξ` at `γ` is
equivalent to a pointwise lower bound on the on-line inverse-square zero sum near `γ`, which no
unconditional input supplies (proportions and all-zero gap bounds only). Kernel positivity,
evenness and log-concavity do not imply the inequality (F382), so no theta-kernel argument can.
FAIL-72 — ULF-ANC-001's inner-band target retired. The anchor-law diagnosis stands.
MUST-121 — Any surviving anchor must be neither convergence of a multiplicative series in the
strip (F380) nor the on-line zero configuration itself (CANNOT-185); manufactured anchors are
capped at `1 − c/θ`. A candidate must name an unconditional nonvanishing datum of a third kind
before any reach argument is attempted.
## 2026-09-02 — principal subtraction refuted; anomaly reclassified (ULF-PSH-002/3)
F401 — In log-aperture coordinate, every Poisson clock history is a translate of one universal
mother: `e^(x/2) ψ_t(e^x)=F(x+log t)`, `F(x)=2e^x e^(−e^x)`. Thus noncompactness is literal
translation escape and the `sech²` kernel is stationary autocorrelation
(`PoissonScaleHistoryFrame`; Lean proved).
CANNOT-194 — It cannot subtract the fixed principal `[1/p]` class, even in a signed completion
and even modulo arbitrary `ell¹` remainder. Exact trichotomy: coefficient `0` admits only neutral
grade; coefficient `−1` admits only nonneutral grade; every other fixed coefficient admits none.
The actual source counterterm `−1/p+2/p²` realizes the wrong phase
(`HedenmalmThetaPrincipalCountertermPolarityNoGo`, `HedenmalmThetaPrincipalClassTrichotomy`).
F402 — The harmonic anomaly is an oriented nonzero square-zero class modulo `ell¹`; reflection
negates it, cofinal prime shift fixes it, and every reduced-ring receiver kills it. Neutral/tail
limits do not commute: depth-first gives `±1`, grade-first gives `0`. It is a first-order
completion-end class, not removable scalar error (`RouteRSummableHadamardConstitutiveCoronaEmbedding`,
`RouteRFirstWallNeutralTailNoncommutation`).
FAIL-79 — ULF-PSH-002 “theta–Poisson principal-shell subtraction” refuted. Positive survivor:
transgress bulk harmonic density to an oriented nonreduced end class and prove source-global end
properness without subtracting the class (ULF-PSH-003).
MUST-125 — Build a pre-divisor, coefficient-faithful nonreduced translation-corona formation. It
must retain the oriented square-zero harmonic symbol, realize its clocks by the ULF-PSH-001 mother
orbit, split arithmetic mass into Haar bulk plus bounded-primitive discrepancy, and derive global
end properness from theta/Poisson source laws. Reduced positivity, fixed counterterms, or bare
functional-equation fibre identification are forbidden. Vanishing of the retained class then
forces neutral grade and closes RH.
## 2026-09-02 — integrality anchor law frozen (card `0-backlog/integrality-anchor-law.md`, ULF-INT-001)
F383 — All four retired routes bounded a real-valued quantity to force an integer (a zero count)
to vanish, with slack of order `log t` per integer. Every theorem that locates zeros (Hadamard–de
la Vallée Poussin, Weil, Deligne, Lee–Yang, Kaczorowski–Perelli degree `< 2`, the corpus's prime
Ising-tree Lee–Yang) contains one integrality anchor — a discrete invariant squeezed between an
archimedean bound and its gap `1` — and is capped exactly where that squeeze has slack `≥ 1`.
CANNOT-186 — It cannot force a zero count to zero with a real-valued inequality valid on a
continuous class containing `ζ`: such classes contain members with any off-line configuration at
the crowd's resolution, so the slack is `≥ log t` per integer (equality for pole-anchored
arguments; mollifiers change the constant only).
MUST-122 — A producer card must name, before any inequality: a discrete invariant `I`; why one
off-line quartet forces `I ≥ 1`; an archimedean bound `s(k)` with amplification parameter `k`;
and `s(k) → 0`. Real-valued inequality cards without (i)–(iv) are closed by CANNOT-186.
## 2026-09-02 — ULF-INT-001 closed as a route; the law stands as constraint
F384 — Lean: the Mertens sum is the Möbius sum over odd integers of `(x/2, x]`; it is the
alternating face count of the squarefree knapsack complex `{S ⊆ primes : ∏S ≤ x}`; every such top
window contains an odd prime; affine rescalings preserve relative displacement
(`RHTower.MertensOddWindowKnapsack`).
CANNOT-187 — It cannot amplify: no finite product of affine rescalings of `ζ` changes the
displacement of a zero relative to its strip, convolution powers keep the abscissa, and the
knapsack complex's Betti numbers (odd squarefree integers of the top window by `ω`) do not
cancel — only the parity of `ω` does. Every discrete invariant surveyed (window counts,
indices, Toeplitz indices, `ζ`-algebra, knapsack topology, Iwasawa invariants, Kloosterman
integrality, CM averages) fails (i)–(iv) of MUST-122.
FAIL-73 — ULF-INT-001's route content retired. The audit table and MUST-122 stand.
MUST-123 — The only discrete structure satisfying MUST-122 is a local-eigenvalue realisation of
the global zeros with a non-affine amplification, i.e. an F₁-point with a Deligne-type tensor
structure. The integrality anchor law and the F₁ open core are the same requirement; no other
producer shape remains open in the corpus.
## 2026-09-02 — formation-end tangent law proved; automatic Xi admission retired (ULF-FTG-001/2)
F403 — Prime-harmonic formation has an exact logarithmic-end tangent.  For
`mu_{a,L}=sum_{log log p>L} p^(-1-a) delta_(log log p-L)`, positive grade has vanishing total mass,
neutral grade converges to Haar measure with uniform whole-half-line cumulative discrepancy, and
negative grade has infinite mass in every fixed end window.  This is an unconditional consequence
of Mertens' second theorem.
F404 — The tangent lifts to the literal Poisson translation frame while retaining unsquared Euler
amplitudes in synthesis.  At neutral grade the frame operators converge in operator norm to a
nonzero Haar operator; at positive grade they vanish in trace norm; at negative grade local norms
diverge.  Every prime-power depth `m>=2` is trace-class residual and vanishes at the end, so full
Euler formation has the same tangent as its principal layer (ULF-FTG-001; paper proved, Lean open).
F405 — The `log log p` clock is not a second unrelated source coordinate: it is the logarithmic
blow-up of theta's `2 log p` translation end.  Poisson scale history therefore describes normal
geometry at theta infinity, not the literal theta translation orbit itself.
CANNOT-195 — Functional equation cannot supply bilateral tangent admission.  It swaps grades but
does not prove source-to-Xi continuity; ordinary Hilbert graph closure is top and canonical
half-density Xi descent is RH-equivalent.  Assuming landing would restate RH (ULF-FTG-002).
FAIL-80 — “Functional equation automatically admits both reflected Euler tangents” retired.
Positive survivor: simultaneous finite nonzero reflected tangent is classified exactly by neutral
grade once an independent source-to-Xi landing theorem is supplied.
MUST-126 — Construct a pre-divisor cofinal transition functor from finite literal theta/Euler
transports to the nonreduced formation-tangent completion, then prove actual Xi compact-open
completion factors through it in both orientations.  Proof may use finite-stage Poisson boundary
annihilation and the new Haar-frame estimate, but not a zero/divisor or any RH-equivalent global
continuity premise.  This factorization—not anomaly subtraction—is the surviving selection edge.
## 2026-09-02 — direct subunit anchor narrowed to one `J`-trace theorem (ULF-DSA-002)
F406 — Direct subunit shape is realized without amplification.  Every strict-right copy has the
unsigned integer `thetaKakutaniEscapeMultiplicity = 1`; signed reflection index cancels.
F407 — Exact Lean fusion:
`B_Euler < (115/108) * thetaKakutaniEscapeMultiplicity <= E_Loewner` for every strict-right copy
(`DirectSubunitEscapeCapacityFusion`).
F408 — Completion provenance is not open.  Literal unsquared joint-depth Euler Krein coefficient
lands in the polar/Gamma completed Xi resolvent; positive-shift arithmetic covariance equals the
reflection-Loewner kernel; opposite-radial signed-source residues recover the cubic residue Gram.
F409 — Universal anomaly is not a guessed scalar subtraction.  Boundary translation has a
negative two-node determinant, and the unshifted residual is exactly rank-one credit minus a
positive Hardy debt.  Completion must remain `J`-contractive until this debt is globally shorted.
F410 — Bilateral orientation compresses the Hardy debt to one shared rank-one ghost, but
source/Gamma-natural descent of that ghost to one prime-independent scalar is already equivalent
to neutral grade/RH.  Viable shorting must retain the prime-indexed ghost section until after the
source/environment Schur operation.
CANNOT-196 — It cannot be completed-SEM winding, Rajchman decay, finite Kakutani values `< 1`, or
integral Laurent evaluation: each is receiver-blind, tends to the unit wall, or lacks integrality
at physical evaluation.
CANNOT-197 — It cannot be fixed scalar mixing, positive Hadamard boundary translation, or bare
Loewner domination.  The first two are disproved; the last is RH-equivalent.
CANNOT-198 — It cannot describe “source-to-completion transport” as missing.  That transport is
proved.  Missing edge is a global pre-divisor trace inequality for its quadratic signed current.
CANNOT-199 — It cannot supply the W-H212 shared ghost as anomaly counterterm before shorting;
source-natural existence of exactly that scalar is a terminal RH receiver.
MUST-127 — Keep P-G206's full prime-resolved exterior environment, sew it to P-G194's
matrix-complete Burnol channels, and identify only its completed quotient with W-H212's rank-one
Hardy ghost.  Before residues or prime-independent descent, prove the resulting `J`-Schur trace is
at most P-G175's primitive collision budget.  After residues this must yield
`E_Loewner <= B_Euler`, closing RH against F407.  No selected zero, divisor premise, supplied shared
ghost, target capacity, or amplification may enter.  Exact card:
`direct-subunit-anchor/tropicalized-defect-capacity-anchor.md`.
## 2026-09-02 — arithmetic symplectic descent frozen (card `0-backlog/arithmetic-symplectic-descent.md`, ULF-SYMP-001)
F385 — Audit of the discrete doors: reflection torsion, Galois dichotomy, Lee–Yang trees, Baker
independence and pair parity are fixed-point invariants of the reflection group and are blind at
free orbits by theorem; the multiplicity ladder is the only door whose invariant (symplectic
self-adjointness, `even_finrank_maxGenEigenspace`) acts at every eigenvalue, which is why RH was
localizable there to one construction: an alternating form from Euler data, self-adjoint for the
divisor operator off the line, with line-supported anomaly.
MUST-124 — The alternating form must be the Hilbert/Steinberg-symbol form on `ℚ^×/ℚ^{×2}`
(Lagrangian by quadratic reciprocity, `μ₂` the sign at `∞`), transported to the window model over
quadratic twists; the decisive test is self-adjointness of the divisor operator on one finite EM
split (T2). A failure there closes the card with a finite witness.
## 2026-09-02 — ULF-SYMP-001 refuted; Kramers sharpened
F386 — Lean: on a space with a cyclic vector every `K`-self-adjoint bilinear form is symmetric,
so no symplectic self-adjoint structure exists on a cyclic space; a symplectically self-adjoint
endomorphism has no cyclic vector (Jordan blocks double). Doubling any block with a nondegenerate
symmetric invariant form gives a symplectic realization for free. `{±1}`-valued skew pairings
are symmetric (`HTGeometry.CyclicNoSymplecticSelfAdjoint`).
CANNOT-188 — It cannot obtain the ladder's symplectic structure from any form on the canonical
cyclic divisor model, nor from any family pairing (twists, reflection, FE doubling) — the former
is impossible, the latter blind — nor from quadratic symbols (symmetric); tame symbols with
non-real characters are alternating but have no global reciprocity (`K₂(ℚ)` has none beyond `μ₂`).
FAIL-74 — ULF-SYMP-001 retired. The ladder's open core is sharpened, not closed: the required
structure is a canonical decomposition of the local divisor into two isomorphic halves from Euler
data, i.e. a square root of the local factor.
MUST-125 — Any candidate for the ladder must exhibit two isomorphic copies of the local divisor
produced from Euler data by a non-linear (non-family) construction; linear constructions are
blind by F386.
## 2026-09-02 — multiplicity ladder gate 7: twin rigidity
F387 — Lean: every twin factorization of ξ on `Re s > ½` is `(g v, g/v)` for an analytic square
root `g` and an analytic unit `v`; conversely every such pair is a twin
(`RHTower.TwinRigidity`). The twin set is empty or a torsor over the diagonal twin.
CANNOT-189 — It cannot gain leverage from non-diagonal twins, metaplectic even/odd channels, or
Maass–Selberg Gram balance: each yields ξ as a product of two factors only in the dressed form
`g v · g/v`, i.e. only after a square root exists. No motive has an L-function with half of ζ's
divisor (`L(M ⊕ N) = L(M)L(N)` and `𝟙` is simple).
MUST-126 — The ladder's open core is irreducible: an analytic half-divisor of ξ on `Re s > ½`
constructed from arithmetic by a non-linear, non-family, non-motivic mechanism. The only
arithmetic candidates in view, the Selberg–Delange powers `ζ^θ`, have continuation past the zero
field equivalent to the rung.
## 2026-09-02 — direct-subunit shorting audit
F411 — P-G206/P-G207 already close short-before-descent. The prime-resolved Julia environment
forms a rank-one block `[[|c|²,c],[conj(c),1]]` with zero Schur short, and this exact block survives
Gamma/polar completion and multiplicity-copy descent at every Xi support, including off-line
support.
F412 — Zero Schur short has no capacity content. The same rank-one block has zero short for
arbitrarily large `c`, so neither `J`-shorting nor its completion transport can imply a bound on
the visible positive corner.
CANNOT-200 — It cannot treat global `J`-shorting as the missing producer. Shorting and descent are
proved and nonselective; an unbounded visible corner can be hidden by a unit environment pivot.
MUST-128 — Direct-subunit closure requires a pre-divisor source-factorized contractive landing
from P-G194's conserved three-channel colligation, augmented by P-G206's prime-resolved
environment, to W-H212's completed positive column. P-G196 proves the map must realize a
prescribed nonzero aperture eigencharacter-gap commutator. One exact augmented conservation law
must retain that anomaly as a positive defect channel and imply target trace at most P-G175's
primitive collision budget. Transport and shorting are not open.
Housekeeping — the cyclic-module no-go proved this pass duplicated
`RHTower.SymplecticCyclicObstruction` (2026-07-11); the duplicate module was removed and the
surviving doubling/sign theorems live in `HTGeometry.SymplecticDoublingFree`.
## Tested producer classes (ULF-TERM-001; not an exhaustive classification)
F388 — Scoped obstructions cover the tested fixed functionals, assumed strip convergence,
free-orbit symmetries, and unit-dressed two-factor presentations. They do not classify every
possible mathematical mechanism. Amplified and direct sub-unit anchors are programmes, not the
only logically admissible alternatives.
MUST-127 — A direct sub-unit programme must identify the integer and independently prove its
source bound below `1`; this requirement does not apply to every possible RH proof.
## 2026-09-02 — direct-subunit completion-index correction
F413 — W-H197 already constructs unique rate-changing boundary transmuter
`((p+z)/(p+w))^2`; W-H198 gives exact rank-one `SU(1,1)` companion and Krein-charge
conservation. Rate-changing commutator/anomaly construction is closed.
F414 — W-H205 proves independent-cell assembly impossible: depth-zero companion trace is at least
`(115/1944) sum_p 1/p`, hence non-trace-class. Prime cells must mix before transmutation.
F415 — Exact paper fusion. For strict-right centered depth `a`, prime `p`, `lambda=log p`, primitive
weight `w=(115/864)/(p lambda^2)`, companion charge `kappa=w(lambda^4/a^4-1)`, and singleton
synchronized curvature `C=(3/8)lambda^2`,
`kappa+w=(115/(324a^4))(C/p)`. Formation curvature is exactly companion metric anomaly plus
primitive source charge.
F416 — Canonical metric subtraction does not leave zero. It leaves summable unsquared Euler weight
`w`; declaring residual zero deletes source provenance. Two absolute traces diverge; their
difference is trace class.
F417 — CCM one-sided Birman--Schwinger theory already gives finite-dimensional above-one dangerous
subspace, with restricted-Weil positivity iff that subspace vanishes. This supplies an integer but
not direct bound: ordinary positive-part `<1` is restricted-Weil positivity/RH restated.
F418 — Positive trace-class domination and positive coefficient-recovering cofinal regularization
of trace-one reflection incidence succeed exactly at neutral grade. Signed, nonlocal relative
subtraction must precede positivity and norms.
F419 — Synchronized squarefree recovery is strictly contractive on every finite nonempty support;
fixed-support first jet and absolute Ward index survive. Diffuse support yields strict limiting
factor `tau/(2sinh(tau/2))<1`, but literal Ward coefficient restoration costs its inverse square
root. Scalar damping alone is not direct selection.
CANNOT-201 — It cannot call completion transport, rate transmutation, companion construction, or
short-before-descent open; all are proved.
CANNOT-202 — It cannot assemble local Krein completions independently or seek a positive
trace-class majorant; corpus proves divergence/critical-line equivalence.
CANNOT-203 — It cannot require residual completion boundary to vanish after metric subtraction;
exact residual is primitive source charge.
CANNOT-204 — It cannot replace formation-strictness construction by dangerous-sector positive trace
bound; that is the RH wall in spectral notation.
F420 — Unsigned escape is a singular harmonic-density multiplicity, not ordinary Fredholm index.
It is reflection-even and equals `0/1`; balanced signed index is always zero. Any norm-continuous
Fredholm polarization through the neutral fibre has locally constant index and cannot realize the
escape jump.
F421 — Singular-trace normalization is also already classified. Prime-normal `log log` residue is
exactly `0/1`, but ordinary ordered-prime Dixmier residue is zero by prime sparsity; additive
singular traces kill the trace-class primitive Euler remainder and therefore lose its coefficient
provenance.
F422 — Exact object/current transport does not imply strict transport of exactness witnesses.
Corpus completion laws preserve coefficients and norm limits off line while compatible finite
null-homotopies may fail to assemble; their mismatch is the canonical completion obstruction.
CANNOT-205 — It cannot use ordinary essential codimension, signed relative Fredholm index, or an
additive Dixmier/log-residue trace as direct integer. The first two cancel or remain locally
constant; the last forgets precisely the summable source term that must finance selection.
MUST-129 — Direct-subunit frontier is pre-divisor prime-mixed formation strictness. Formation and
completion have equal non-trace-class principal metric and trace-class primitive difference.
Construct one coefficient-faithful coherent primitive for the finite relative cancellations, prove
its completion mismatch is unsigned escape multiplicity, and bound that obstruction by the
primitive source capacity `<1`. Objectwise transport, an unmarked trace-class quotient, positive
domination, or a post-divisor trace bound does not count.
Exact card:
`direct-subunit-anchor/tropicalized-defect-capacity-anchor.md`.
## 2026-09-02 — metaplectic AII† door closed (card `5-failed/metaplectic-transfer-operator-kramers.md`, ULF-META-001)
F389 — Lean: `Ξ` takes both strict signs above every height, so ξ has critical-line zeros of
odd order above every height and not every order of ξ is even (`RHTower.GlobalParityWall`).
Copies dichotomy: for `f^e·u` with `u` nonvanishing the order is `e·ord f`; even `e` makes all
orders even, odd `e` preserves parity; for ξ the parity of `ξ^e·u` is void or violated.
CANNOT-190 — It cannot read a parity constraint on `ord_ρ ξ` off any determinant presenting the
divisor of ζ through `e` copies (cusp count, Fricke pairs, Weil-representation components,
mirror pairs): `e` even is void, `e` odd is globally violated. The theta-multiplier transfer
operator has `e = 2` (two singular cusps `∞, 0` of `Γ₀(4)`, Fricke-paired).
FAIL-75 — ULF-META-001: the metaplectic transfer operator as an AII† model of ξ's divisor.
MUST-128 — Any Kramers-type structure must be restricted to `Re s > ½`; `s`-independent cocycles
(multiplier systems, symbols, Weil-representation signs) cannot supply the restriction.
## 2026-09-02 — door 1 attempted and refuted (card `5-failed/f1-frobenius-integrality-torsion-law.md`, ULF-F1-002)
F390 — Lean (`RHTower.FrobeniusTorsionLaw`): if every Arakelov coordinate of a zero of ξ is an
algebraic integer and Galois conjugates of coordinates are coordinates of zeros, then RH is
false; with contractive packets (the chamber) this is contradictory. Kronecker forces roots of
unity, the middle totative of each order gives a conjugate zero in the closed unit disc, and
infinitely many orders make zeros accumulate.
F391 — Lean: `p^ρ` algebraic for one `p ≥ 2` and `ρ` nonreal ⇒ `ρ` and `w(ρ)` transcendental
(Gelfond–Schneider). Paper: at most two primes have `p^ρ` algebraic (six exponentials).
CANNOT-191 — It cannot carry Weil–Deligne integrality on the zeros of ξ: in the normalised
coordinate integrality is incompatible with RH (torsion law); in the unnormalised coordinate it
fails at three primes; the two coordinates exclude each other.
CANNOT-192 — It cannot produce a positivity below RH: all-aperture Weil positivity is RH,
finite-aperture positivity is blind (C1–C4), symmetry never sources it, the Hodge star's
Frobenius compatibility is RH.
MUST-129 — Any F₁-door construction must be integral on the test-function side (integer
Lefschetz numbers such as `lcm(1..n)`), not on the eigenvalue side; it cannot have a
characteristic polynomial. The remaining Lean item is the six exponentials theorem.
Open Lean item (card `1-in-progress/six-exponentials-lean.md`): six exponentials theorem via
Siegel + multipoint Schwarz + Liouville, no zero-counting; corollary: not all of `p₁^ρ, p₂^ρ,
p₃^ρ` algebraic for nonreal `ρ`.
## 2026-09-02 — integral--nuclear homotopy defect
F423 — Absolute nuclear `T` is impossible. Any endomorphism inducing identity on a nonzero
Hausdorff escape quotient has norm at least one; faithful compact prime formation is already proved
nonproper. The source budget can act only after relative cancellation of two non-nuclear principal
parts.
F424 — Raw completion-minus-formation heat difference is insufficient: trace class does not make
its trace integral. Integrality requires a relative Hodge/Fedosov class (equivalently a trace-class
difference of theta-positive graph projections).
F425 — P-G186 canonically has a global prime-mixed Hilbert--Schmidt synthesis in its already-built
Burnol `L²` carrier. Its squared HS norm is `B_base=(216/115)B_Euler<2`; normalization by
`1/sqrt 2` makes total nuclear mass `<1`. P-G194 extends this to an exact three-channel isometry,
retaining every off-diagonal prime/depth entry.
F426 — Minimal surviving object is
`T(s)=Pi_Mul(R_theta^+(s))-Pi_Mul(R_ar^+(s))`, the relative theta-positive projection defect of
the multivalued horizons of the two completed pre-divisor all-prime relations. `Mul(R)` is the
kernel of source projection from the closed relation, hence exactly completion-created loss of a
finite null-homotopy. Relative projection trace is integral.
F427 — One common vertical class and one horizontal scalar horizon already exist separately.
`FrankensteinMeyerPrimeKoszulGammaReporter` gives one reporter cocyclic for every prime;
`DeningerCalderonWittAllCrossPrimeIncidenceKoszul` leaves exactly one scalar packet direction.
Their total-complex identification is missing.
F428 — Gamma admission cannot provide the missing homotopy. The all-cross-prime Gamma admission
operator is conservative on completed Green provenance, and annihilating its reflected-Gaussian
Green vector is already RH-equivalent.
CANNOT-206 — It cannot be an absolute compact reporter, raw relative heat trace, weighted sum of
local Neumann remainders, Frobenius homotopy 2-cocycle, block-diagonal prime index, or reflected
signed Fredholm index. It also cannot declare Gamma admission a source null-homotopy.
MUST-130 — Prove one source-specific relative-horizon factorization
`T=B*B-C*C` whose two canonical P-G194/P-G196/P-G206 defect columns have total HS mass
`B_base/2<1`, and prove its relative index at a strict-right specialization equals the one
common theta escape unit left by all-cross-prime incidence. This pre-divisor identity, not target
trace domination, would close RH. Card:
`direct-subunit-anchor/integral-nuclear-prime-mixed-homotopy-defect.md`.
F429 — Provenance-continuous completion cannot create homology from eventually exact stages
(`ExactCompletionDiagram.physical_exact`). Therefore an off-line class cannot be finite source
cohomology transported to completion; it is failure of finite contractions to survive completion.
F430 — Because off-line escape is a nonclosed-domain phenomenon, bounded harmonic projections are
not admissible. The correct `T` projects the multivalued horizons of the two closed relations.
Finite relations are single-valued; completion creates `Mul(R)=ker(sourceProjection)` exactly when
finite contractions fail to survive.
F431 — Trace-norm limits preserve trace (`traceTower_limit`). Hence a coherent nuclear completion
of zero-index finite homotopy defects still has trace zero. Any off-line index-one fibre forces
non-nuclearity or incoherence of the arithmetic/theta contractions.
CANNOT-207 — It cannot insert a class at finite level, call eventual exactness alone the source
mechanism, or assume trace-norm convergence of finite contractions. The first violates
pre-divisor provenance; the latter two assume the missing completion theorem.
MUST-131 — Construct the single graded landing
`A_s=gradedCompletionLanding(P-G194((1/sqrt 2)A_base))` and prove
`Pi_Mul(R_theta^+)-Pi_Mul(R_ar^+)=A_s* diag(+I,-I) A_s` on the pre-divisor total relation, retaining every
cross-prime Gram entry and P-G196 aperture commutator. This one identity simultaneously gives
integrality, nuclearity, and mass `<1`; strict-right index `1` then contradicts it.
F432 — P-G177 collision Gram and P-G186/P-G194 base-Cauchy Gram are not interchangeable. Corpus
proves diagonal rescaling `K_base(alpha,alpha)=(216/115)K_collision(alpha,alpha)`, not an entrywise
inter-carrier isometry. The homotopy defect therefore uses the P-G194 base carrier and its `<2`
quantum, normalized by `1/sqrt 2`; importing `sqrt(108/115)` into P-G194 is invalid.
CANNOT-208 — It cannot use diagonal proportionality to identify full kernels or mix P-G177's
`115/108` normalization with P-G194's three-channel colligation. Any future collision-carrier
version needs a separately proved all-entry transgression.
F433 — Off-line Meyer/theta escape lives at a nonclosed range/domain boundary. An ordinary
bounded harmonic projection would assume a Hodge decomposition and erase the carrier. Corpus
proves more: every closed relation retaining the off-line literal-source Xi graph is maximally
multivalued, so no closed single-valued operator model is admissible.
CANNOT-209 — It cannot define `T` through ordinary harmonic projections, a bounded Green inverse,
or a closed single-valued theta operator. It must be formed from the multivalued horizons of closed
relations before quotienting the completion defect away.
F434 — Target integrality is already stronger than theta escape counting. The closed Meyer Xi
relation has `Mul=0` on line and full scalar `Mul` off line; finite-packet source-projection kernel
has dimension exactly total analytic Xi multiplicity. For one zeroth-order off-line copy the
vertical index is unconditionally `1`. Missing work is only its pre-divisor all-prime formation
identification and source nuclear factorization.
## Nuggets of knowledge (2026-09-02, one line each; certificates in the cards named)
- **Weil–Deligne integrality is incompatible with RH itself.** If every Arakelov coordinate
  `w(ρ) = 1 − 1/ρ` of a zero is an algebraic integer and Galois conjugates of coordinates are
  coordinates, RH is false (`FrobeniusTorsionLaw`, F390).
- **The `q = 1` scale is what turns Weil's mechanism into torsion.** Over `𝔽_q` Frobenius
  eigenvalues have modulus `q^{1/2} ≠ 1` and escape Kronecker; over ξ the scale is `1`, so an
  integral unitary Frobenius has finite order, and the zeros are not torsion points.
- **The two Frobenius coordinates exclude each other.** `p^ρ` algebraic for one `p ≥ 2` makes
  `ρ` and `w(ρ)` transcendental (Gelfond–Schneider, F391); at most two primes have `p^ρ`
  algebraic (six exponentials, paper).
- **Any F₁ construction with a characteristic polynomial is dead**; admissible integrality lives
  on the test-function side, e.g. `lcm(1..n) = e^{ψ(n)}` (MUST-129).
- **Producer positivity is RH or blind.** All-aperture Weil positivity is RH; finite apertures
  cannot see a zero closer than the crowd; symmetry never sources it; Frobenius compatibility
  of the positive Hodge star is RH (CANNOT-192).
- **Every twin factorization of ξ is the square root dressed by a unit.** Non-diagonal twins,
  metaplectic channels, Gram balance carry no information beyond the root (`TwinRigidity`, F387).
- **No motive has half of ζ's divisor**: `L(M ⊕ N) = L(M)L(N)` and `𝟙` is simple.
- **ξ has critical-line zeros of odd order above every height**, so no structure doubling all
  multiplicities exists (`GlobalParityWall`, F389).
- **Parity read off `e` copies of ξ is void (`e` even) or violated (`e` odd)**; the theta
  multiplier on `Γ₀(4)` has exactly two singular cusps, Fricke-paired, `e = 2` (CANNOT-190).
- **Convergence of the Möbius series at one point is the zero-free half-plane** to its right;
  the individuation producer is the conclusion (F380).
- **Share ledgers are even in the off-line displacement** and every fixed functional pays one
  `log t` of crowd per zero; the line anchor equals on-line density (C1–C4, F379, F382).
- **A cyclic module carries only symmetric invariant forms; doubling any block is a free
  symplectic realization; `{±1}`-valued skew pairings are symmetric** (F386).
- **Producer obstructions are scoped, not exhaustive**; F388 does not prove that only two doors remain.
- **The direct sub-unit anchor already has its integer, its lift, and its budget in the corpus**
  (`thetaKakutaniEscapeMultiplicity`, cubic Loewner landing, primitive Euler capacity); the
  open step is the same-boundary identification, whose naive form is RH (ULF-DSA-003).
## 2026-09-02 — six exponentials theorem in Lean (card `3-formalized/six-exponentials-lean.md`)
F392 — Lean: for `x₀, x₁` rationally independent and `y₀, y₁, y₂` rationally independent, one of
`exp(x_i y_j)` is transcendental (`SixExponentials.six_exponentials`, Siegel + multipoint
Schwarz + Liouville, no zero-counting theorem); corollary: for nonreal `ρ` and distinct primes
`p, q, r`, not all of `p^ρ, q^ρ, r^ρ` are algebraic (`not_all_three_prime_cpow_isAlgebraic`).
Door 1's Theorem B is now certified; ULF-F1-002 has no open Lean item.
- **Nugget:** the six exponentials theorem needs no zero-density estimate: vanishing on `M³`
  points in a disc of radius `~M` against growth `exp(O(M))` forces an exponential polynomial to
  vanish identically through the Schwarz lemma alone, and Liouville upgrades "tiny at a sample
  point" to "zero" one level at a time.
## 2026-09-02 — door 2 audited (card `3-formalized/escape-multiplicity-offline-indicator-lean.md`)
F393 — Lean: the escape multiplicity of the direct sub-unit anchor is the off-line indicator,
`= if Re q = ½ then 0 else 1`; the fusion's gap `budget < (115/108)·multiplicity` holds exactly
off the line; its vanishing at every copy is RH (`RHTower.EscapeMultiplicityOffLineIndicator`).
CANNOT-193 — It cannot read a Ferrero–Washington anchor off an integer that is the indicator of
the conclusion's failure: the only bound below one unit for such an integer is the conclusion.
The corpus's direct sub-unit anchor is, as it stands, a receiver; its open "prime-mixed formation
strictness" has no formal statement and any version implying the capacity law is RH-strength.
MUST-130 — A direct anchor must name an integer defined without reference to the zero's
position, prove it positive at an off-line copy by a theorem, and bound it by an estimate that
does not pass through the target inequality. No such integer exists in the corpus (the knapsack
Euler characteristic, the completed-SEM contour index, and the escape multiplicity all fail one
of the three).
- **Nugget:** both doors of the terminal classification are, at the present state of the corpus,
  RH-equivalent receivers: door 1 by the torsion law and six exponentials, door 2 by the
  off-line-indicator audit. The corpus contains no non-RH-equivalent producer target.
## 2026-09-02 — integral--nuclear defect audit closed
F435 — Lean: verticalization commutes with incidence totalization,
`Mul(Tot_delta R)=Mul(R)∩ker(delta)`. A supplied strict-right Meyer fibre becomes exactly the
full-support cross-prime line `C eta`; its projector is rank-one, Schatten-1, and has trace and
trace norm exactly `1` (`IntegralNuclearRelationIncidenceHorizon`).
F436 — Lean: all zero-clock P-G186 Burnol columns form one literal all-prime Hilbert--Schmidt
synthesis `A_base`; `||A_base||_HS²=B_base<1`. Its covariance is Schatten-1 with
`Re Tr(A_base A_base*)=B_base<1` (`RoutePPrimitiveBurnolBaseNuclearSynthesis`). No normalization
or divisor enters; P-G186 retains every cross-prime Gram entry.
F437 — These are two incompatible positive survivors, not one operator. Any bounded landing of
the zero finite horizon defects is zero by dense-core continuity; any singular relation retaining
the completion-born horizon loses the inherited Schatten bound. Thus the identity
`Pi_theta-Pi_ar=A_s*Gamma A_s` is impossible under ULF-INHD-001's finite-core premises, not merely
unproved. The route is retired.
CANNOT-210 — It cannot transport an integral completion horizon through a bounded/contractive
Hilbert--Schmidt landing from finite defects that all vanish. Nor can a summable diagonal topology
select the horizon ray: summable weights admit every scalar; nonsummable weights admit only zero.
MUST-132 — Any successor must change the arithmetic relation and source topology before finite
completion, act nontrivially on finite witnesses, and derive a norm native to that topology. It
cannot reuse `B_base` through a bounded landing or call the source covariance and horizon projector
one `T` without proving an impossible identification.
## 2026-09-02 — MUST-130 attempted: no position-independent integer with an independent bound (card `5-failed/position-independent-integer-loop.md`)
F394 — Lean: off the line the paired Li coefficients are positive for arbitrarily large `n`;
unconditionally they are never eventually negative (`RHTower.LiSignOscillation`, mean value on
the torus via recurrence and the geometric sum).
CANNOT-194 — It cannot infer eventual negativity of the paired Li sequence from failure of RH
(`LiSignOscillation`). That linear-reader theorem does not prohibit nonlinear one-signed data.
MUST-131 — A direct anchor needs its own unsigned obstruction and independent bound; neither its
existence nor its impossibility follows from sign oscillation of a different observable.
F641 — Linear oscillation can coexist with positive integral nonlinear defects: `u₀=u₁=1`,
`uₙ₊₂=2uₙ₊₁−2uₙ` has both signs cofinally, but `uₙ₊₁²−uₙuₙ₊₂=2ⁿ>0` for every `n`
(`OscillationHankelDefect`: `HTGeometry.oscillation_all_positive_integer_defects`, Lean; standard axioms).
Its terms are `Re((1+i)^n)`; no identification with Li coefficients or RH source bound is claimed.
## 2026-09-02 — stage 4: `4-publication-ready/archimedean-integrality-obstructions.md`
The manuscript packages twin rigidity, global parity, Frobenius torsion, six exponentials,
off-line indicators, and Li sign oscillation. Its universal classification and claimed prohibition
of position-independent nonlinear one-signed data are not consequences of those scoped theorems.
## 2026-09-02 — successor object constructed: restricted prime--Gamma Toeplitz polar defect
F438 — For each pre-divisor admissible strict-right rectangle `D`, the continued prime--Gamma
current canonically forms one boundary unitary `u_D`. Hardy compression `A_D=P M_(u_D) P` and its
polar lift `W_D` define one graded defect
`T_D=diag(1-W_D W_D*,1-W_D* W_D)`. It uses no supplied zero and mixes all primes before
compression (`direct-subunit-anchor/restricted-prime-gamma-toeplitz-polar-defect.md`).
F439 — Paper theorem: `T_D` is positive finite-rank/nuclear and
`Tr T_D=|wind u_D|`; in the strict-right chamber its supertrace, ordinary trace, source contour,
and enclosed Xi multiplicity coincide. Its two Hankel seams are native nuclear dominators, with
`Str T_D=||H_(u_D*)||_HS^2-||H_(u_D)||_HS^2` and
`Tr T_D<=||H_(u_D*)||_HS^2+||H_(u_D)||_HS^2`. Lean pending; no RH claim.
F440 — This is not the retired bounded landing: finite local phases already have nonzero Hardy
seams, and no vanishing finite horizon projector is transported. The integer and its candidate
budget now live on the same compression. Naked winding remains a receiver; new leverage is the
exact unsquared-current = relative-nuclear-energy transgression.
CANNOT-211 — It cannot use arbitrary Xi inner/outer factorization as anomaly subtraction, import
`B_base`, take an operator-norm Euler limit, compress primes separately, or subtract after taking
norms. Each move is respectively circular, the retired impossible landing, formally blocked,
non-mixed, or coefficient-destroying.
MUST-133 (superseded by F441/MUST-134) — The first proposed lift asked for a global two-Hankel
residual bound `<1`. Fresh audit shows the available cubic residual already exceeds one and global
Wold/HS domination is RH-equivalent; only restricted properness or local anti-concentration
survives.
F441 — Fresh boundary audit kills the naive budget but exposes the higher mechanism. The positive
cubic mismatch is not sub-unit: its prime-two atom is
`(95/16)(log 2)^3>(95/16)(2/3)^3=95/54>1`. Identity-scale landing also overshoots the wall--Xi
cubic residual by factor `>2000`. Global Wold/Gamma domination and global ordinary HS admission
are separately exact RH receivers.
CANNOT-212 — It cannot identify the scalar Euler/Wold cubic mismatch with the Toeplitz seam
budget, use global Wold domination, or demand global physical Hilbert--Schmidt admission. It also
cannot use a linear aperture-covariant lift: rate-change intertwining is formally impossible.
MUST-134 — Recast formation in the restricted unitary group
`U_res(P)={U | [P,U] is HS}`. Finite Euler--Gamma phases have index zero; `T_D` is the integral
component-jump defect. Prove source counterphases make formation proper in the restricted metric,
or prove every local `H^(1/2)` concentration atom has mass `<1`. Degree quantization then forbids
all bubbles even though total residual energy exceeds one, forcing `T_D=0` and RH.
## 2026-09-02 — polar defect reinterpreted as completion-ionized charge
F442 — Generic critical compactness is now exact. Mironescu proves every bounded
`W^(1/2,2)(S1;S1)` degree loss is a finite list of escaping Möbius profiles; each costs the sharp
`4*pi^2` Gagliardo quantum. Hyder--Martinazzi give the equivalent `2*pi` degree quantum in their
half-harmonic normalization. Diffuse excess energy cannot carry a winding jump.
F443 — The prime-Bohr source already forms strongly in Haar `L2` for every `Re(s)>1/2`, but the
physical height orbit is dense Haar-null, so ambient `H2` has no canonical point restriction.
Full `C(PrimeTorus)`-linear RFHM sewing is worse: Lean proves it erases every nonempty native prime
support. Fixed-support prime recurrence therefore cannot produce confinement.
F443a — It cannot infer density-norm recovery from pointwise Euler recovery: the finite local clock `m_P(n)=prod_(p in P)(0 if p²|n; -1 if p|n; 1 otherwise)` equals `mu(n)` at each `n>=1` once the prime set `P` covers its prime divisors, but for every fixed finite prime set `P`, `lim_X X^(-1)sum_(1<=n<=X)|mu(n)-m_P(n)|²=6/pi²+prod_(p in P)(1-p^(-2))` (`eulerClockNat_eq_moebius`, `tendsto_density_sector_fracture_pi`, Lean). The last product tends to `6/pi²`, not zero (`tendsto_squarefreeSafeProduct`).
The exact finite-clock Gram survives and factors over shared/unshared primes (`eulerClockProd_gram`, Lean); it controls CRT averages, not a uniform moving-prime/integer-prefix limit. The obstruction is noncommuting limits, not failure of literal local factorization; it does not exclude every coupled completion or prove a covariance-return bound.
F444 — New paper theorem on the actual two seams: with Hardy number `N e_j=j e_j`,
`C_Theta(u)=Tr((N+1)H_u*H_u)+Tr((N+1)H_(u*)*H_(u*))`
equals `(1/2) sum_(n!=0)|n|(|n|+1)|uHat(n)|^2`. Bounded `C_Theta` is exactly an `H1`-properness
bound; Rellich compactness forces strong `H^(1/2)` convergence and preserves winding. For one
Blaschke charge `b_a`, total cost is `1/(1-|a|^2)` and excess number cost is
`|a|^2/(1-|a|^2)`, so boundary escape costs infinity.
F445 — Higher interpretation: literal finite formation is a neutral chiral dipole gas; completion
noncompactness permits ionization; `T_D` is the unbalanced integral charge left when one chirality
escapes; `C_Theta` is its canonical separation cost. Fixed mixed inertia, rapidity, Krein negative
directions, closed recurrence, and open lifted history are shadows of this one mechanism.
CANNOT-213 — It cannot use ambient prime-torus restriction, full reversible source linearity,
fixed finite-prime phase bounds, a scalar diffuse normalizer, or the heat-echo zero detector as the
producer. None controls the first moment of both oriented Hardy seams; two options destroy native
support or reuse completed Xi data.
MUST-135 — Construct source-only counterphases before winding extraction and prove the uniform
weighted-seam bound `sup_k C_Theta(v_(D,k))<infinity` for the literal prime-mixed relative phases,
after coefficientwise universal-anomaly subtraction. Theorem RPGT-B then forces every strict-right
contour winding to zero and closes RH. Weaker acceptable target: sub-unit energy for every escaping
Möbius profile, not every defect-measure atom.
F446 — Correction: `fieldOneFiniteStageSphericalScatteringSymbol` is a real critical-line phase,
not a strict-right boundary formation sequence. The latter can instead start from the explicit
pre-divisor family
`L_x(s)=sum_(n>=2)(Lambda(n)/log n)e^(-pi*x*n^2)n^(-s)`, `E_x=exp L_x`.
For every `x>0`, `L_x` is entire, `E_x` is zero-free, all prime-power Euler-log coefficients remain
unsquared, and `E_x -> zeta` on `Re(s)>1`.
F447 — New paper theorem RPGT-C: for zero-winding phases `u_k` weakly convergent in bounded
`H^(1/2)`, let `kappa_+/-` be loss of positive/negative chiral Hankel energy. Then
`wind(u)=kappa_- - kappa_+`. Hence positive completed winding implies `kappa_- >= 1`; the single
source inequality `kappa_-<1` forces `T(u)=0`. This is strictly weaker than uniform `H1`
properness and is the exact direct sub-unit anchor.
F448 — The chiral loss is a singular ordered-limit observable. For a Blaschke escape kernel,
`Tr((1-e^(-tau*N))|k_a><k_a|)=|a|^2(1-e^(-tau))/(1-|a|^2e^(-tau)) -> 1` as `|a|->1`, while
taking `tau->0` first gives zero. Completion and cooling do not commute; their commutator is the
integral charge. This evades bounded dense-core landing because finite phases already have
nonzero seams and no bounded source-to-horizon operator is asserted.
CANNOT-214 — It cannot use the critical-line scattering symbol as a strip approximation, make
an entire Euler gauge change contour charge, or identify the independent Burnol `<1` covariance
with chiral corona loss through a bounded factorization. Each move is formally closed.
MUST-136 — Use literal integer/Poisson self-duality to form a holomorphic anomaly for the Gaussian
Euler exponential, then prove weak boundary convergence and the native negative-chiral bound
`kappa_-(D)<1` on the same Hankel seam. RPGT-C then forces every strict-right winding to vanish.
F449 — `ULF-GECRF-001` constructs the anomaly exactly. With
`M_x(s)=integral_1^infinity e^(-pi*x*u^2)u^(-s)du`, take the entire primitive
`A_x'=M_x`, `A_x(2)=0`, and
`Phi_x=(1/2)s*pi^(-s/2)Gamma(s/2)exp(L_x+A_x)`. For every `x>0`, `Phi_x` is zero-free on
`Re(s)>0` and its current is `logDeriv(h_infinity)-J_x+M_x`. On `Re(s)>1`,
`M_x->1/(s-1)`, `A_x->Log(s-1)`, and `Phi_x->xi` locally uniformly. This is the literal
prime-atomic minus continuum-heat metric subtraction; no divisor or fitted normalizer enters.
MUST-137 — Counterterm construction is closed. Remaining theorem is now only: prove weak
`H^(1/2)` convergence of `Phi_x/|Phi_x|` to the completed Xi boundary phase on strict-right
contours and prove its negative chiral corona loss `<1`. Ordinary local-uniform convergence is
impossible exactly when a completed zero is enclosed, so the proof must be singular/ordered-limit.
F450 — The reflected source charts have exact transition
`G_x(s)=Phi_x(s)/Phi_x(1-s)` on `0<Re(s)<1`: it is zero-free,
`G_x(1-s)=G_x(s)^(-1)`, and `|G_x|=1` on `Re(s)=1/2`. Functional-equation action therefore lifts
through literal Gaussian Euler--continuum formation information-neutrally.
CANNOT-215 — The two-chart cocycle is not selection. It constrains gluing but cannot prevent the
common completed section from vanishing; treating reciprocal/unitary transition as RH repeats the
corpus functional-equation countermodels and balanced-index cancellation.
F451 — Safe-chart compactness is unconditional: on every closed contour in `Re(s)>1`, `Phi_x` and
its log derivative converge uniformly to `xi` and `xi'/xi`; normalized phases converge in `C1`,
so both chiral losses are zero. The defect is therefore not an Euler-product truncation artifact:
it is created only at singular passage from the safe Euler chart into the completed strip.
F452 — `ULF-RUCRI-001` constructs the requested single object. For a pre-divisor mixed boundary
phase `U`, let `R=U*PU`, `Delta=R-P`, and `mathsf T=Delta^3`. At critical `H^(1/2)` regularity,
`Delta` is Hilbert--Schmidt and `mathsf T` is one self-adjoint nuclear integral operator. Its trace
is the integer relative index, hence the boundary winding. Its `+/-1` endpoint spectrum recovers
the two polar kernel/cokernel multiplicities.
F453 — Cubic grade is forced, not decorative. Linear displacement retains orientation but need
not be trace class in `S2`; quadratic displacement is nuclear but reflection-even; cubic is the
first ordinary nuclear trace that is reflection-odd and integral. This explains why linear source
currents and quadratic positivity repeatedly fail while cubic Green/Cauchy/Loewner/Gamma-six
readers survive.
F454 — The integral kernel is explicit:
`d_u(z,w)=(conj(u(z))*u(w)-1)K_P(z,w)` and `mathsf T` is its threefold cyclic convolution.
For Gaussian Euler formation the exponent of `u` is one sum over all prime powers, so this kernel
contains mixed distinct-prime monomials before compression. `mathsf T` is not a sum of local
indices.
F455 — Exact source-clock fusion:
`B_base=(1/8) integral_0^infinity t^2[-zeta'/zeta(1+t)]dt
=(1/4)sum_(n>=2)Lambda(n)/(n log(n)^3)<1`.
Thus the Route-P/CCM base budget is the third inverse moment of the safe prime-log contraction
semigroup. Burnol aperture damping diagonalizes the same clock and its three-channel colligation
preserves full mixed matrix pairings.
CANNOT-216 — The Gamma-clock scalar identity alone cannot select. Declaring it equal to a Hankel
energy repeats the retired bounded landing; discarding Burnol cross terms loses formation. A valid
bridge must act on the degree-three cyclic chain and may be closed-graph/mapping-cone, not a
bounded one-particle map.
MUST-138 — Construct before divisor specialization a matrix-complete degree-three cyclic
transgression from Gaussian Euler/Burnol formation to the Hardy projection pair proving
`0<=Tr mathsf T_D<=B_base<1`. Since `Tr mathsf T_D` is strict-right multiplicity, this single
inequality closes RH. Exact falsifiers: wrong cyclic degree, loss of cross-prime coefficients, or
no trace-norm control by the Gamma-clock mass.
F456 — The “different source objects” gap is closed. For `t>0`,
`J(t)=pi^(t/2)/Gamma(t/2) int x^(t/2-1)J_x(1)dx`, while the same normalized Mellin transform of
`M_x(1)` is `1/t`. Thus the centered safe current `J(t)-1/t` is exactly the Mellin transform of
the Gaussian atomic-minus-continuum anomaly, and
`B_base=int K_3(x)J_x(1)dx` for an explicit positive Mellin--Gamma kernel. Gaussian formation,
prime-log aperture, continuum subtraction, and cubic capacity are one source law.
F457 — Literal integrality enters as a gap, not a slogan: continuum frequency reaches `log u=0`
and creates the non-trace-class pole `1/t`; integer atoms start at `n=2`, giving gap `log 2` and a
finite cubic action. The remaining selector must turn this gapped bulk action into the boundary
cubic Chern character without a positive diagonal majorant (CANNOT-216).
F458 — `B_base` is dynamic bulk action. For prime-mixed Burnol label Gram `C_B` and diagonal
semigroup `D_c` with full eigenvalue `exp(-c*(log n+i*kappa))`, matrix-complete colligation gives positive
`C_def(c)=C_B-D_c* C_B D_c`, retains cross-prime entries, and
`B_base=int_0^infinity d/dc Tr C_def(c) dc`. The flux density is the complete quadratic Green
current. Target `Tr mathsf T_D` is boundary topological charge; missing law is now a
bulk-to-boundary action inequality between two one-sided homotopies.
F459 — Correct ambient object is now explicit. The literal Hilbert--Schmidt Burnol synthesis
`A_base` defines the holomorphic restricted-Grassmannian cap
`Gamma_base(z)=graph(z A_base)`. With determinant-line normalization,
`Area(Gamma_base)=Tr(K_base(1+K_base)^(-1))<=Tr K_base=B_base<1`. Paper proof is
dependency-closed in `ULF-BGCA-001`; no RH claim.
F460 — This cap is pre-divisor, nonzero, and matrix-level prime-mixed. `K_base=A_base* A_base`
retains every cross-prime Gram entry before the determinant trace. The final area scalar is only a
shadow; any valid completion theorem must sew the full graph/determinant line, not import its
number as a target budget.
F461 — Corpus escape laws line up as one restricted-Grassmannian mechanism: Tate node charge is
boundary winding; FE reflection is anti-symplectic; an off-line divisor is a source-matched
escaping bubble; critical horizon multiplicity has a Schubert-cell reader; the cubic projection
trace is the integral boundary character. Interpretation: off-line zeros are completion bubbles,
not primary spectral objects.
CANNOT-217 — It cannot identify `pi_0` relative index with a `pi_2` bubble without a canonical
Bott suspension; use arbitrary symplectic rather than pseudoholomorphic sewing; scalarize away
cross-prime Gram entries; use fixed-support Quillen response, rectangular Evans Pluecker norm, or
a divisor-defined formation map. Each move is respectively ill-typed, nonpositive, non-mixed, or
already closed/circular.
MUST-139 — Construct coefficientwise from Gaussian Euler--continuum/Burnol formation a
Bott-suspended pseudoholomorphic sewing into `Gr_res,2` whose stable completion loss is a positive
determinant-line Schubert bubble, with
`E_base=E_residual+sum m_j`, `sum m_j=Tr mathsf T_D`, `E_residual>=0`. Then
`0<=Tr mathsf T_D<E_base<1` forces zero strict-right multiplicity and RH. Sharpest falsifier:
diffuse infinite-rank energy leakage or failure of the graph rotation to suspend the actual
completed Hardy phase.
F462 — `ULF-BGAF-001` makes the source geometry dynamic. Forward Burnol aperture damping extends
to a contraction semigroup `S_c`; for `A_c=S_c A_base`,
`K_c=A_c* A_c` decreases in Loewner order and
`E(c)=Tr(K_c(1+K_c)^(-1))` decreases from `E(0)<1` to zero. Interval action
`E(c)-E(d)` is nonnegative and exactly additive.
F463 — Matrix-completeness survives the nonlinear action filtration. For finite packets,
`K_c-K_d` is exactly the sum of positive boundary and tail-cocycle defect Grams, including all
cross-prime entries. The source now supplies a one-sided filtered continuation, not a static
capacity scalar; backward Burnol time is singular.
CANNOT-218 — It cannot use an arbitrary stable sewing that injects action, or infer target index
from source monotonicity alone. Source graph action is closed, but no current theorem says theta
completion is a filtration-nonincreasing canonical relation.
MUST-140 — Strengthen MUST-139 to a coefficient-native filtered Floer/Maslov law: construct the
theta correspondence so every Schubert/Maslov completion event has target action bounded by an
exact Burnol source interval. Unit determinant-line quantization plus total source action `<1`
then forbids index one. Exact open core remains canonical Bott suspension + infinite-rank
tightness, now with a required monotone continuation identity.
F464 — `ULF-DLLA-001` closes the observer/lift geometry. For any graph cap,
`Hol_det(boundary)=exp(2*pi*i*E)`. Two framed fillings of the same boundary differ in lifted area
by the integral determinant-line Chern number; a positive Schubert bubble subtracts its integer
degree from residual action while leaving holonomy unchanged.
F465 — Corpus independently predicts this quotient: Berry holonomy does not determine winding
action; closed determinant observation can have open logarithmic lift; periodic phase quotient can
hide nonzero integral carry; occupied strict frontiers carry integer holonomy coordinates. New
interpretation: `mathsf T_D` is the nuclear operator representative of the hidden deck
translation, not of determinant phase.
CANNOT-219 — Common determinant holonomy, FE cocycle, or phase recurrence cannot select RH: each
is invariant under adding an integral Schubert bubble. Unframed filling comparison is also
meaningless because a boundary gauge winding can insert an arbitrary deck integer.
MUST-141 — Construct a coefficient-native common determinant framing and prove
`Tr mathsf T_D=q(Euler graph filling, theta residual filling)`. Then prove theta continuation
selects the principal filtered lift, so
`E_base=E_residual+Tr mathsf T_D` with both energies nonnegative. This is the exact mechanism by
which `<1` kills the integer; phase equality alone is intentionally information-neutral.
F466 — Naive Paley--Wiener/characteristic-function transport is closed. Corpus already has exact
half-line-to-Hardy unitary transport, but proves no linear aperture-covariant operator—even
unbounded and radius-nonlocal—can change a primitive Burnol decay rate into a strict-right Xi
rate. Missing completion is necessarily nonstationary.
F467 — Strongest survivor is an exact curvature law: every prescribed rate-changing landing has
aperture-covariance defect with `c^-2` boundary jet `2*(w-z)`, retaining full complex displacement.
Thus the polar--Gamma term must be mixed connection curvature, not a scalar correction or norm
loss.
CANNOT-220 — It cannot use a flat contraction characteristic function, stationary convolution,
multiplier, Paley--Wiener landing, or functional calculus as completion transport. All preserve
the wrong aperture character and are formally killed.
MUST-142 — Build the Euler--theta determinant differential character over the two formation
coordinates `(Burnol aperture c, Gaussian heat x)`: horizontal graph action is `ULF-BGAF-001`,
vertical transport is the zero-free Euler--continuum family, mixed curvature is their forced
noncommutation after universal metric-anomaly subtraction, and boundary transgression is
`Tr mathsf T_D`. Prove the renormalized curvature is positive with total mass `<1`.
F468 — Ordinary positive Grassmannian is only the reduced/source-edge shadow, not the ambient
field. Actual theta Green boundaries converge to fixed rank-two mixed inertia with witnesses
`+1/6,-1/6`; boost-invariant reflection-symmetric positivity is formally zero; Gaussian formation
is atomic minus continuum. Pre-reduction geometry must be graded/Krein.
F469 — Four legs are forced: upper, reflected upper, lower, conjugate lower. Corpus constructs the
matrix-complete positive four-leg Hodge Gram and proves the natural two-leg diagonal flips sign
under a quarter-turn. Collapsing fourth leg to first, or demanding raw defect nonnegativity, is
exactly RH and cannot be assumed.
F470 — `ULF-ETRS-001` freezes the higher field: a four-leg restricted Krein Grassmannian with
Burnol aperture and Gaussian heat as formation coordinates; atomic/continuum supertrace removes
the universal metric anomaly; mixed polar--Gamma curvature carries forced rate-change work; odd
boundary transgression is the cubic `mathsf T`; positive Schubert quantization occurs only after
theta reduction.
CANNOT-221 — It cannot impose positivity before continuum/gauge reduction, collapse reflected
four-leg data, or use an arbitrary indefinite metric. These respectively force zero, assume RH,
or lose source provenance. Grading and fundamental symmetry must be derived from literal
Euler/continuum/FE formation.
MUST-143 — Construct the operator-valued Gaussian continuum leg on the same four-leg carrier as
the Burnol connection. Prove matrix-first relative trace-class curvature and positive reduction:
`E_Euler=E_reduced+Tr mathsf T_D`, `E_reduced>=0`. This one theorem would turn the closed `<1`
Euler action into RH without pretending the unreduced field is positive.
F471 — `ULF-FACHD-001` replaces bare-observer cubic defect by one formation-relative operator.
For completed boundary phase `u_(D,0)` and any zero-free Gaussian Euler--continuum phase
`u_(D,x)`, set `R_(D,x)=M_(u_(D,x))* P M_(u_(D,x))` and
`mathsf T_(D,x)=(R_(D,0)-R_(D,x))^3`. It is self-adjoint, nuclear, prime-mixed before
compression, and `Tr mathsf T_(D,x)=wind(u_(D,0))-wind(u_(D,x))` is integral.
F472 — Every positive Gaussian anchor has winding zero and all anchors are connected through the
restricted topology. Hence `Tr mathsf T_(D,x)` is independent of `x>0` and equals the continued
prime--Gamma contour multiplicity. The preferred representative uses `x=1`; it measures the
component jump from literal zero-free Euler--theta formation to singular completion, not from an
empty observer to Xi.
F473 — Relative cubic defects satisfy exact two-channel and trace-cocycle laws:
`T(u,v)=R_u(1-R_v)R_u-R_v(1-R_u)R_v` and
`Tr T(u,w)=Tr T(u,v)+Tr T(v,w)`. Operator additivity fails by a traceless nuclear associator;
this associator retains matrix data erased by the integral trace.
CANNOT-222 — Source ownership plus integrality is not selection. It cannot infer
`Tr mathsf T_D<B_base` from common boundary, equal winding identities, or homotopy invariance;
that would still import a scalar budget without a matrix-complete cyclic action map.
MUST-144 — Construct the coefficient-native degree-three transgression bounding the positive
channel of the formation-relative `mathsf T_D` by Burnol graph action. Exact closure is now on one
boundary and one projection pair: `0<=Tr mathsf T_D<=B_base<1`.
F474 — Naive Gaussian continuum synthesis on the Burnol carrier is impossible: its log-frequency
`lambda` column has norm square `1/(4 lambda^3)`, while continuum reaches `lambda=0`. A negative
Krein sign cannot repair an undefined infinity-minus-infinity covariance; subtraction must occur
before norms.
F475 — `ULF-CAGC-001` constructs the forced repair. Multiplying continuum and Euler columns by
the cubic aperture-energy gauge `(1-exp(-2c lambda))^(3/2)` makes both syntheses Hilbert--Schmidt.
Energy order `q` is integrable at zero iff `q>=3`; zero, linear, and quadratic defects diverge.
Thus cubic is independently minimal at source continuum wall and target `S_2` index wall.
F476 — Cubic-gauged Euler and continuum legs live on one carrier. Their full Gram retains
distinct-prime and atomic--continuum blocks; their graded range covariance is nuclear, and
conjugate doubling gives the required `(+,-,+,-)` field. Euler trace remains bounded by
`B_base<1`; continuum trace is finite for each positive heat/aperture.
CANNOT-223 — It cannot place raw continuum in a negative Hilbert leg, regularize only after trace,
or use first/second aperture defects. These objects do not exist in the required nuclear category.
MUST-145 — Build the cyclic boundary map from cubic-gauged four-leg relative covariance to
formation-anchored `mathsf T_D`, preserving full mixed Gram, and prove theta reduction leaves a
nonnegative residual. This is now the sole structural bridge before the sub-unit integer kill.
F477 — `ULF-OCSE-001` proves the cubic-gauged continuum columns are total in the Burnol carrier:
`closure span {r*exp(-lambda*r):lambda>0}=L2(0,infinity)`. The positive cubic multiplier is
nonzero at every positive label, so `closure(Ran A_0)=H_B` for every `x,c>0`.
F478 — Orthogonal continuum shorting is exactly zero: its range projection is `I`, hence
`(I-P_0)A_E=0`. Ordinary Hilbert completion has already erased the distinction required for
selection; a negative grading does not manufacture a complementary output subspace.
F479 — Before completion, Euler and continuum energy measures remain mutually singular: the
Euler measure is pure point on `{log n}`, while the Gaussian continuum measure is absolutely
continuous. Thus source provenance lives in the label measure class and source-to-completion
arrow, not in a closed subspace of the Burnol output.
CANNOT-224 — It cannot use orthogonal range quotient, output-space Schur shorting, or any
continuous reporter depending only on the completed Hilbert range. All annihilate or forget the
atomic/continuum formation distinction.
MUST-146 — Replace Hilbert-range reduction by a provenance-retaining mapping cone or rigged
cyclic relation for `[A_E A_0]`. Construct its degree-three boundary character to the
formation-relative `mathsf T_D`, then prove positive reduction before nonfaithful closure:
`0<=Tr mathsf T_D<=Tr K_E<B_base<1`.
F480 — `ULF-ZDIA-001` proves the continuum synthesis is compact, injective, dense-range, and
nonsurjective. Its inverse on `Ran A_0` is therefore a closed densely defined unbounded operator:
continuum completion has a canonical singular graph norm.
F481 — Every nonzero finite active Euler packet lies outside `Ran A_0` although its distance to
that range is zero. Equality with a continuum lift would equate an absolutely continuous Laplace
measure to a nonzero finite pure-point measure, forbidden by Laplace uniqueness and mutual
singularity.
F482 — Every continuum lift approximating such an Euler packet has norm tending to infinity.
Formation defect is therefore zero-distance/infinite-action, not a positive output residual. This
is the first exact location for the universal completion anomaly required by the working theory.
F483 — Canonical regularized lift action
`C_epsilon=A_E*(A_0 A_0*+epsilon I)^(-1)A_E` is positive, prime-matrix-complete, and nuclear for
every positive regulator; every active Euler diagonal diverges as the regulator vanishes. Corpus
Wold cubic renormalization has exactly the required coefficientwise divergence-minus-counterterm
shape, but its operator identification with this lift action is open.
CANNOT-225 — It cannot treat dense continuum approximation as admissibility, use bounded inverse
completion, or subtract an arbitrary scalar infinity. The inverse is unbounded, every finite
Euler atom has infinite raw lift action, and prime-independent ghost subtraction is already an
RH-equivalent receiver.
MUST-147 — Derive an operator-valued Wold/Poisson counterterm for `C_epsilon` from literal
integer/theta self-duality, prove trace-norm convergence of its finite part, and identify its cubic
cyclic boundary with `mathsf T_D`. Positive finite-part domination would close the sub-unit gate.
F484 — `ULF-MHPD-001` proves both formation legs are dense in the same Burnol carrier. Continuum
totality is Laplace uniqueness; Euler totality already follows from the prime-two depth tower
`{r*exp(-k log(2)r):k>=1}` by polynomial-moment uniqueness.
F485 — No bounded one-channel target operator can transport source provenance grading: acting as
`+I` on dense Euler range forces `F=I`, while acting as `-I` on dense continuum range forces
`F=-I`. Atomic/continuum sign is a genuine completion-descent anomaly.
F486 — Two channels are minimal and sufficient. Hadamard synthesis
`B(a,b)=(A_Ea+A_0b,A_Ea-A_0b)` is Hilbert--Schmidt with dense range, transports source grading to
target swap exactly, reconstructs both legs, and obeys the parallelogram conservation identity.
Functional-equation/Schwarz doubling then forces the observed four-leg `(+,-,+,-)` carrier.
CANNOT-226 — It cannot compress atomic/continuum provenance to one bounded completed observer.
Nor does arbitrary Krein doubling suffice: two-channel structure and swap are fixed by exact
Hadamard reconstruction; the conjugate pair is fixed separately by functional equation.
MUST-148 — Construct theta phase quotient on the derived four-leg Hadamard carrier and prove its
degree-three boundary is formation-relative `mathsf T_D`. Only after this exact boundary identity
may reduced positivity be used to compare its integer trace with `B_base<1`.
F487 — `ULF-CFPO-001` proves a parity no-go: any invariant `Q` fixed by an involution cannot,
through any postprocessing, determine a nonzero charge `q` reversed by that involution. Limits,
finite parts, functional calculus, traces, determinants, and covariance-native cyclic formulas
remain even because they still factor through `Q`.
F488 — The canonical inverse-completion family
`C_epsilon=A_E*(A_0 A_0*+epsilon I)^(-1)A_E` is unchanged by global source sign reversal, whereas
`Tr T(u,v)=wind(u)-wind(v)` changes sign under endpoint reversal/inversion. Therefore the proposed
covariance-only equation `Ch_3(C_rel)=mathsf T_D` is false or imports orientation circularly.
F489 — Corpus verifies this is arithmetic, not merely abstract: prime-power Koplienko Gram is
identical for a literal Euler coefficient and its negative, while the linear semilocal current
separates them. Theta recovers `logDeriv Xi` through an antisymmetric metric cross-current. Hence
metric action and oriented charge are two irreducible inputs.
CANNOT-227 — It cannot derive winding, horizontal sign, or `mathsf T_D` from positive covariance,
inverse-Gram action, its counterterm, or any functorial finite part alone. Renormalization removes
divergence; it does not create lost orientation.
MUST-149 — Construct a pre-divisor bivariant transgression pairing the renormalized singular
completion metric with the literal reflection-odd prime--Gamma/Maurer--Cartan current. Prove this
mixed current is nuclear, has boundary `mathsf T_D`, and inherits the `<1` Euler action bound.
F490 — `ULF-SSIN-001` constructs the missing source-side bivariant object explicitly. For the
source-normalized Stokes probability `pi_d` on primes, let `psi_d(p)=sqrt(pi_d(p))` and
`mathsf T_src(t)=sign(t)|psi_|t|><psi_|t||`. It is pre-divisor, self-adjoint rank one, nuclear,
reflection-odd, cross-prime at every matrix entry, preserves the unsquared current on its
diagonal, and has integral trace `sign(t)`.
F491 — `mathsf T_src(t)^3=mathsf T_src(t)` and its trace norm is exactly one. It is trace-norm
continuous separately in both horizontal chambers, but as `t->0` it converges strongly to zero
while one-sided traces remain `+1,-1`. Every compact observer sees zero. This is a literal closed
observer/open lifted-history law generated by the Euler source, not assumed as abstract corona
data.
F492 — The normalized scalar prime Stokes jump is half the jump of `Tr mathsf T_src`, hence one;
the pole--Gamma counterjump is minus one and their completed charge is zero. Prime current,
nuclear homotopy, and archimedean countercurrent obey one exact integral conservation identity.
CANNOT-228 — It cannot transport the source unit to completed `mathsf T_D` by a map continuous
only for strong/weak operator topology or through compact reporters: the source operator closes
to zero in exactly those topologies while its nuclear trace charge remains one.
MUST-150 — Construct the singular theta/Poisson relative boundary map carrying the source wall
class `[mathsf T_src]` to the completed rectangle class `[mathsf T_D]`, then prove its positive
target channel is paid by Euler budget `<1`. The source side now has the required orientation,
prime mixing, nuclearity, and integral unit; only conservation through singular completion remains.
F493 — `ULF-SCIN-001` upgrades the rank-one Stokes ray to the literal normalized cofinal child:
`mathsf T(t)_(p,q)=sign(t)sqrt(pi(p)pi(q))kappa(log p,log q)`, with cubic Burnol coherence
`kappa(a,b)=8(ab)^(3/2)/(a+b)^3`. It is pre-divisor, genuinely cross-prime, self-adjoint,
Schatten-one, reflection-odd, and has integral trace and trace norm `1`.
F494 — This full-coherence `mathsf T` is trace-norm continuous in each chamber and strongly tends
to zero in the fixed prime chart at the wall. Its source-forced quantile isometries instead
conjugate it to integral kernels on `L2(0,1)` converging to the unit-exponential cubic kernel.
Thus fixed observers lose the nuclear unit while a comoving source chart retains it.
F495 — Corpus `L2` quantile-kernel convergence plus positivity and exact trace conservation
upgrades to trace-norm convergence by positive trace-tightness. Ordinary Fredholm determinants
therefore converge locally uniformly, transporting linear Stokes charge, every cross-prime entry,
and all compound orders in one frame. This closes normalized-child determinant landing, not Xi
identification or the physical squared-child landing.
CANNOT-229 — It cannot interpret fixed-chart strong vanishing as disappearance of formation, use
only compact observers, or replace the missing completion map by direct aperture-wall Xi
identification. The same source section is zero strongly and nonzero in trace norm after its
endogenous singular frame change; direct Xi identification is already false.
MUST-151 — Construct a theta/Poisson relative boundary functor from the exponential-limit cubic
kernel plus pole--Gamma countercurrent to completed `mathsf T_D`, and prove its positive target
energy is bounded by the primitive Euler budget `<1`. This functor must act on marked relative
currents and their singular frames, not covariance alone.
F496 — `ULF-EWHC-001`: comoving wall operator has `Tr A=1` and exact
`Tr(A^2)=16/35`, hence `||A||<=4/sqrt(35)<1`. Reversing its Burnol Gram factorization gives
explicit positive trace-one Hankel partner `b(r,s)=24rs/(1+r+s)^4`, with same nonzero spectrum
and determinant. Literal prime-mixed formation is already a strict contraction before any divisor.
F497 — `I-A` is source-canonically invertible by norm-convergent Neumann series;
`det(I-zA)` is zero-free for `|z|<sqrt(35)/4`, and exact second coefficient is `19/70`. This is
unconditional source leverage, but direct/scalar wall-to-Xi identification is formally false, so
strict contraction must survive a divisor-changing relative boundary operation.
CANNOT-230 — It cannot be monotone CDF transport from exponential wall coordinates to two theta
half-intervals. That half-density sewing exists for every positive even density, and its
translation covariance is definitional conjugacy; it narrows no source class and changes no
spectral invariant. Fixed integer multiplication is also trivial in wall scale since its shift is
`2d log n ->0`.
MUST-152 — Use theta's singular Jacobian only inside an independent Poisson/functional-equation
boundary identity that changes divisor-bearing operator while preserving unsquared prime
formation and strict wall contraction. Coordinate sewing without such identity is gauge.
F498 — `ULF-SKPM-001`: for Kummer modulation `M_tau` of exponential wall operator `A`, complete
HS survival overlap is exactly
`C(tau)=6 integral_0^1 v^2(1-v^2)^2/(1+tau^2v^2)dv`. It is positive, even, strictly decreasing
in `|tau|`, starts at `16/35`, tends to zero, and satisfies `tau^2 C(tau)->16/5`. This fuses
prime Stokes formation, Burnol coherence, Kummer phase, and recurrence overlap.
F499 — Literal wall/Kummer joint chart is parabolic: `x=2d log p` forces spectral phase
`y=2d tau`. For fixed `tau`, quantile-transported phase conjugates converge in trace norm to
`M_tau A M_tau*`. Fixed nonzero height corresponds to infinite wall frequency; a uniform atomic
limit there remains open.
CANNOT-231 — Radial strict contraction cannot itself be recurrence clock; corpus already proves
nonzero cofinally recurrent orbit impossible. Radial formation and reversible phase must be
independent directions. Nor may phase conjugacy alone prove RH: it preserves spectrum and trace.
MUST-153 — Derive from literal theta/Poisson self-duality that completed recovery is
information-neutral for marked HS overlap after metric-anomaly subtraction. Then formation-born
off-line recurrence would conflict with exact source decoherence; absent that independent law,
recurrence descent remains an RH-equivalent receiver.
F500 — Squared-frequency response has a hidden exact law:
`C(sqrt(q))/(16/35)=E[(1+q Lambda)^-1]` for `Lambda~Beta(3/2,3)`. It is strictly completely
monotone, with every wall jet fixed by
`(-1)^n F^(n)(0)=48n!/((2n+3)(2n+5)(2n+7))`. Here `Lambda` is squared Cayley contrast
`((x-y)/(x+y))^2`, so one probability law generates the full phase-response tower.
F501 — `ULF-DHNJ-001`: normalized Kummer commutator energies of the prime-mixed wall satisfy
`m_n=||ad_X^n(A)||_2^2/((2n)!||A||_2^2)=105/((2n+3)(2n+5)(2n+7))`. Exactly,
`m_n=h(n+1)h(n+5/2)/(h(1)h(5/2))`, where `h(s)=-B(s+1/2,3/2)` is the corpus's literal
Euler odd-Hodge response. Thus full nuclear homotopy jet is a forced double-Hellinger boundary.
MUST-154 — Lift the correlated double-Hellinger state, not either scalar factor alone, through
literal theta/Poisson completion while retaining its positive decaying coface flux. Ordinary
closed coface quotient is impossible: it saturates off centre and recovery does not descend at
centre. Required carrier must preserve joint provenance before closure.
F502 — Normalized homotopy tails have canonical positive flux
`w_n=m_n-m_(n+1)=630/((2n+3)(2n+5)(2n+7)(2n+9))`, with `sum w_n=1` and
`m_n=sum_(k>=n)w_k`. Integral unit is total dissipation through open Hodge history, not constant
charge stored at any grade.
CANNOT-232 — It cannot be a closed linear one-marginal Hellinger boundary conserving nonzero
charge along factorially vanishing grades. Corpus proves this forces a vertical `(0,charge)` in
graph closure; ordinary adjacent-coface closed span is already diagonal at centre and top off it.
F503 — `ULF-PHIN-001` constructs final pre-divisor object on `ell2(Nat) tensor ell2(Primes)`:
`mathsf T(t)=diag(w_n) tensor mathsf T_form(t)`. It is prime-mixed in every history fibre,
Schatten-one, reflection-odd, trace `sign(t)`, trace norm one, and its tail traces reconstruct every
normalized Kummer commutator energy. Forced uniqueness follows from adjacent tail subtraction.
F504 — Comoving history--formation wall has direct norm bound
`||Phi tensor A||<=8/(3sqrt(35))<1` while retaining integral trace one. Fixed-chart strong limit is
zero; comoving trace-norm limits are `+/- Phi tensor A`. Off-line corpus target instead carries
one trace unit as multivalued prime-mixed relation horizon.
MUST-155 — Prove literal integer/Poisson self-duality makes anomaly-subtracted completion positive,
unital, trace-preserving, and grade-flux preserving on `mathsf T`, and identifies its divisor
specialization with the relation-horizon defect. Contractivity would send source norm `<1` to
`<1`, contradicting every strict-right target's rank-one projection norm `1`.
CANNOT-233 — Normality or trace preservation alone cannot close selection: normal channels can
concentrate diffuse trace-one densities into rank-one states. Existing fixed Möbius--Gamma/Xi
source map is formally expansive near the critical ray. Required law is a new anomaly-subtracted
bistochastic map on correlated history x prime provenance, not the existing scalar transport.
F505 — Lean certifies `ULF-PHIN-001` as one literal kernel on `ell2(Nat x Primes)`, not a tensor
analogy. `primeHodgeHistoryIntegralNuclearHomotopyDefect t` is the single signed pre-divisor wall
family: `T(-t)=-T(t)`, `Tr T(t)=sign(t)`, `||T(t)||_1=|sign(t)|`, positive with chamber orientation,
and every same-history cross-prime entry is nonzero off wall. Its diagonal is exactly signed theta
Mellin-six flux times unsquared prime density. Unit aperture recovers the prior closed `T`.
F506 — `ULF-PHSF-001`: tails `m_n` force unique positive nearest-neighbour survival ratio
`r_n=m_(n+1)/m_n=(2n+3)/(2n+9)` and hazard `h_n=6/(2n+9)`. Weighted shift
`C e_n=sqrt(r_n)e_(n+1)` has bounded left inverse `B`, positive exit defect `D2=I-C*C`, and exact
duality--adjunction fracture `(B-C*)C=D2`.
F507 — Conditional exit records `E_j(k)=w_(k+j)/m_k` and remainder `R_N(k)=m_(k+N)/m_k` obey the
Lean-certified operator law `sum_(j<N)E_j+R_N=I`. Initial readout of `E_n` and full prime-fibre
marginal of the integral nuclear `mathsf T` are the same `w_n`; this is object-level formation
ownership, not equality only after total summation.
F508 — `ker C=0`, `range C=range S`, `ind C=-1`, and Lean proves
`-ind C=sum_n w_n=Tr Phi=Tr mathsf T=1`. Thus `mathsf T` is a prime-mixed nuclear exit record of
one forced Fredholm history: Hodge flux, open recurrence, adjoint fracture, Toeplitz charge, and
formation are gauges of one mechanism.
FAIL-81 — Beta/Jacobi diffusion and generic minimal Wold/Stinespring dilation do not produce this
mechanism. The Beta response fixes a measure but not a unique Dirichlet form; every contraction
has a conservative dilation. Neither forces the rational tail, prime-fibre record, fracture, and
index simultaneously.
CANNOT-234 — It cannot close RH by trace preservation, unitality, generic dilation, scalar
functional equation, or one-response equality. Such maps may concentrate diffuse trace-one input
to a rank-one target or add invisible Krein spectators while preserving the advertised scalar.
MUST-156 — Prove literal integer/Poisson self-duality yields an anomaly-subtracted,
record-complete intertwiner of `(C,D2,B,mathsf T)` that exhausts the completed relation horizon.
It would preserve zero residual source survival; every strict-right Xi copy has rank-one residual
horizon, so exhaustion excludes it and reflection closes RH. This exact edge is open.
## 2026-09-03 — the F₁ object: shape forced by theorem (card `1-in-progress/f1-object-forced-shape.md`, ULF-F1-003)
F395 — Lean: eigen-characters of endomorphisms of finite free ℤ-modules are algebraic integers;
no finite free ℤ-module carries three Frobenii with a common eigen-functional of eigenvalues
`p^ρ, q^ρ, r^ρ` for nonreal `ρ`; unitary integral Frobenii are torsion on every eigen-character
(`RHTower.FrobeniusLatticeRigidity`).
CANNOT-195 — It cannot realise the zeros as joint Frobenius eigen-characters on any finitely
generated integral piece of an `𝔽₁`-cohomology (three primes suffice); the Frobenius must be the
scaling flow on an infinite-rank object whose integrality is that of the Dirichlet ring acting.
MUST-133 — The F₁ object is a cokernel of the zeta element `ζ = Σ[n]` of the Dirichlet ring on a
Poisson-admissible module (Meyer's `M_ζ = H_−/ζH_∩`); its zeros are the characters where `μ`
fails to act; its single missing datum is a geometrically produced positive Hodge form.
- **Nugget:** the zeros of ζ are a phenomenon of the archimedean line `z_p = p^{−s}` in the
  character torus of the dilation monoid; the Euler product has no zeros on the torus, and the
  line is Baker-generic. No finite algebraic specialization can see a zero.
## Cayley-collision record defect (`ULF-CCRHD-001`)
F509 — Raw squared cubic coherence has Cayley-contrast law `Beta(1/2,4)`, not the observed
`Beta(3/2,3)`. The latter is forced by relative density `lambda/(1-lambda)`: deletion of the
equal-prime metric part is the exact source anomaly transgression, not a fitted probability law.
F510 — On the oriented transgressed prime-pair state, survival `S=delta` and exit `E=sqrt(1-delta²)` obey `S*S+E*E=I`; `O(f)=(E S^n f)_n` is isometric and pure. History is generated by signed literal prime-pair contrast, with `||S^n Omega_H||²=m_n` and `||E S^n Omega_H||²=w_n`.
F511 — History dephasing gives one nonseparable positive nuclear `T=directSum_n |E S^n Omega_H><E S^n Omega_H|`, with `Tr T=||T||₁=1`, `||T||=2/3<1`, tail traces `m_n`. Under prime swap, `Omega_H,S` are odd, `E` even, grade `n` has parity `(-1)^(n+1)`. Positive `T` is reflection-even because dephasing removes the cross-grade coherences carrying orientation.
FAIL-82 — The generic operator-weighted shift `A_n=sqrt(I-w_nK)` gives the tautological defect
`I-C*C=directSum_n w_nK` but has nonzero infinite survival product because `sum w_n<infinity`.
It cannot supply record exhaustion; prime-dependent history must be formed before averaging.
CANNOT-235 — The abstract observability/dephasing formalism is classical and cannot select RH.
Acting only on positive `T` discards the reflection-odd unsquared amplitude and falls under
covariance blindness; trace preservation alone can still concentrate `T` to a rank-one horizon.
MUST-157 — Derive from literal integer/Poisson self-duality a singular relative boundary functor
on the marked colligation `(Omega_H,S,E)` plus pole--Gamma countercurrent. Record completeness must
carry its zero residual survival to the completed relation residual; any off-line rank-one horizon
would then be impossible. This refines `MUST-156`; the boundary functor remains open.
## Recent formation/completion laws
F512–F513 — Prime and theta histories share complementary observability, but prime endpoint order is cubic (`n³m_n->105/8`) while every fixed theta tilt is infinitely flat. FAIL-83/CANNOT-236: no fixed-scale isometry, stationary recovery, or bare conservation identifies their records.
MUST-158 — Completion needs moving history scale or independently derived singular clock.
F514–F515 — Unique finite Szegő subtraction is `pi exp(2|x|)`; residual is zero-free outer with dense nonclosed range. FAIL-84/CANNOT-237: scalar outer completion loses odd unsquared orientation and no other scalar coefficient works. MUST-159 — oriented Hardy double plus pole–Gamma current.
F516–F517 — Exit mean is `7/4`; finite recurrence forces `(d,K)` multiples of `(4,7)`.
FAIL-85/CANNOT-238: no finite monitored unitary realizes polynomial tail `w_n`; `7/4` is coarse.
F518–F520 — `D_N` is measurable weak `S₁` with residue `3N`; every exit `E_j` has residue `3`;
`T` shifts canonical finite part by `+1`. FAIL-86/CANNOT-239: direct determinant and fixed theta
hazard cannot select; residue misses finite-rank horizons. MUST-161 — inverse-saddle transport,
odd formation, and no `S₁` spectator remain required.
F396/MUST-134 — Three-prime Frobenius-stable finite ℤ-lattice is zero; Deninger producer must be
geometric Hodge positivity, not another radical/resolvent receiver.
F521 — Unique scale-6 inverse saddle has residue `3`; Hodge discrepancy is `3/(n log n)`.
F522 — Stein Gramian has trace `7/4`; exit sandwich `Phi` has trace `1`.
F523 — Degree-2 theta history and degree-3 prime formation give `Q`, `T=Q*Q`, trace `1`, prime-mixed.
CANNOT-240 — No fixed contraction carries two distinct clocks between degrees.
F524 — Mellin creator is `a∞(s)=Γ(s+1)/Γ(s+1/2)` with half-order critical-axis metric anomaly.
F525–F526 — Cofinite prime Gamma frames are total but nonproper; covariance whitening gives a
canonical unitary lift preserving every prime coefficient and history tail. This is exact
information-neutral completion, not selection.
F527–F529 — `T` reconstructs summable half-order aperture curvature; Gamma residue regrades
`Phi` to `((2n)!)^-2`, whose inverse energy is constant only at neutral grade. Polynomial
`T^(-1/2)` cannot stop factorial coface collapse or produce the `1/(n log n)` clock modulo `S₁`.
FAIL-89/90 — Petz recovery preserves every grade; nonabelian holonomy constrains composition, not
grade. Source-built nonseparable curvature is real, but divisor-specialized flatness is RH; small
trace selfcommutator cannot kill Fredholm index (`alpha*S` retains index `-1`).
F530/MUST-162 — `Gθ(s)=2Mθ₁(s)/(s(s-1))=Γ_R(s)` and normalized six-step holonomy equals `m_n`;
adjacent loss is `w_n`, so `T` is theta-formed before divisors. Need completed Xi relative energy
to be this boundary functional after forced metric renormalization with zero residual.
F531/F532 — `[C*,C]` is positive S1 with trace `1=-ind C=Tr T`; `m=tail(w)`, `r=m_succ/m`,
`kappa=Delta r`, and conversely `r=prefix(kappa),m=product(r),w=m(1-r)`.
F533/F534 [paper] — Gamma split recovers Cayley moments `m_n`; `T` is the unique cubic prime-clock
Lyapunov solution, a one-Jordan-step heat Gramian with source-generated proper inverse.
FAIL-91/F535/MUST-164 — Gamma spectators do not identify Xi. `T²` has capital one but
`[I⊗L,T_d²]~d^-1`; need anomaly-explicit cubic boundary and horizon exhaustion, not multiplicative
transport.
F536/CANNOT-242 [paper; Lean core] — For faithful compact `T`, `T-T²` is full; every continuous
multiplicative completion sending `T` to an idempotent is zero. A divisor horizon must arise by a
singular/nonmultiplicative completion (`ULF-PHFI-001`).
F397–F402 [Lean]/MUST-135–140 — Archimedean `1/2` is unique flow-invariant half-density, not
selector; Plancherel has no zero eigenvectors, atomic Weil `ell2` positivity is RH, Meyer `L1` has
no bounded star. Prime entry is log-soft; Sonin strictness plus aperture continuity is the live edge.
FAIL-92 — Generic Halmos/Naimark dilation manufactures a unit; dilation is not transport.
F537–F539 [paper] — Euler aperture has order-six Gram `C`, `Tr C<115/108`, but its sixth lowering
lands on a non-`ell2` vector; no bounded sixth source preserves literal Euler weights (`ULF-ESAC-001`).
F540/F541 [paper] — Unique order-six-to-cubic Mellin gauge has dense nonclosed range/unbounded
inverse; its correction is nonzero indefinite S1 with zero diagonal/trace. Gauge subtraction is
not rate transmutation (`ULF-EHGM-001`).
F542–F545 [paper/Lean core] — First-exit curvature reconstructs mixed
`T=Q(I-C*C)Q⊗A=G_A-U*G_AU`; `CQ=QU` with compact dense-range `Q`. Partial traces recover prime
packet/exit law, Riesz potential recovers survival, and index/flux/trace/norm are one unit.
F546/F547 [paper] — Same-defect completions are `G_A+R`, `R=U*RU`; no nonzero compact `R`, and
positive `R` repeats infinite mass. Observer `p` has harmonic infinite-trace and first-exit S1 lifts.
CANNOT-248 — Signed `T(t)` is a wall family, not trace-norm homotopy: integral trace and unit norm
force a jump at zero. Continuous dynamics must carry `T` as relative index, not as evolution.
FAIL-93/CANNOT-245/MUST-165/166 — Horizon data do not select harmonic over first-exit lift. A
viable field must derive its history boundary operation before observer specialization.
F548 [paper] — On every fixed physical prime edge, Pluecker block mass satisfies `D_e~c e^-6`,
while theta first-exit mass satisfies `w_e~(315/8)e^-4`. Their unique positive half-density
`sqrt(w_e/pi_e)` grows linearly and has exactly the `N+1` graph domain (`ULF-TPFOI-001`).
CANNOT-246/MUST-167 — No bounded diagonal coefficient-faithful Pluecker-to-theta completion exists.
Completion must be first-order unbounded, depth-mixing, or abandon literal coefficients.
F549 [paper] — The unique half-density has `s_(e+1)/s_e=1+1/e+O(e^-2)`; its formation residue
equals `(6-4)/2=1=-ind(C)=Tr(T)`, independent of prime edge (`ULF-IFOCC-001`).
F550 [paper] — The singular sandwich closes edgewise to a positive trace-one nuclear operator
whose literal Pluecker kernel moves with depth; this repairs the old `history tensor prime` defect.
CANNOT-247/F551 [paper] — This gauge cannot descend to shared prime-depth cells: overlap forces
`s_e=s_(e+1)`, contradicting linear escape. Finite connection is flat; obstruction is its improper
trivialization at the open formation end (`ULF-POSGND-001`).
MUST-168 — Any literal global completion must carry one unit graph connection with prime-dependent
blocks; derive that connection from integer/Poisson formation before any Xi specialization.
MUST-169 — Complete on the formation cover before quotienting to physical cells; subtract the
universal unit residue, then prove only the residual relation descends properly.
F557 — Paper theorem (`ULF-MPNLIH-001`): for each source prime edge `p<q`, the forced Euler/theta half-density ratio defines a bounded weighted shift on moving physical Pluecker null lines. Its self-commutator is self-adjoint Schatten-one, eventually positive outside a finite history head, and satisfies `Tr(T_pq)=1=-index(C_pq)`; finite-cutoff traces telescope exactly to the transport square `a_N`.
F558 — `T_(2,3)` is a distinguished fixed-edge moving-line realization, not the global requested object. Corpus already has `primeHodgeHistoryIntegralNuclearHomotopyDefect`, mixing every prime with exact first-exit/Fredholm reconstruction. Surviving novelty of `T_(2,3)` is only its physical moving-Pluecker realization.
CANNOT-249 — Flat connection/unbounded trivialization and weighted-shift trace-index theory are generic and already occur in corpus; they cannot be field core. Only source-forced completion-before-overlap realization is new residue.
CANNOT-250 — `T_pq` cannot be direct sub-unit anchor: `Tr(T_pq)=1` forces `||T_pq||_1>=1`; positivity is also unproved because global monotonicity of transport squares is unknown.
MUST-172 — Next selection theorem must derive, before divisor specialization, `completed boundary = T_pq + R_pq` with source-forced theta positivity and `Tr(R_pq)=0`; defining this residual or assuming its positivity is old RH receiver, not producer.
MUST-174 — `T_pq` retains six-minor mass and moving kernel line but not full rank-three Pluecker covariance; any Xi use must prove null-line sufficiency or lift the index defect coefficient-faithfully without losing trace conservation.
F561 — Paper theorem (`ULF-PCPOS-001`): fixed-presentation purification of moving full Pluecker covariances gives positive `S_1` trace-one `T` and the exact identity `1-Tr(T^2)=sum_(n,k)w_nw_k||u_n wedge u_k||^2`.
F562 — Failure audit: PCPOS's strict gap compares different depth fibres in one chosen presentation. Source-forced depth-dependent metric isometries can alter/erase this overlap; only a common-unitary gauge preserves it. PCPOS is a fixed-frame bridge, not coordinate-free selection leverage.
CANNOT-251 — Existing global `primeHodgeHistoryIntegralNuclearHomotopyDefect` already satisfies the literal requested description. Another fixed prime kernel or separable `diag(w) tensor A` is rediscovery. Purification/partial trace and weighted-shift theory are generic; only full moving Pluecker specialization survives.
F563 — Paper theorem (`ULF-POINH-001`): let `A` be P-G94's literal positive `S_1` physical-overlap Pluecker operator and `tau=Tr A>0`; `T=A/tau` is pre-divisor, faithful, prime/depth formed, positive `S_1`, with `Tr T=||T||_1=1` and `||T||<1`.
F564 — Intrinsic strictness law: for canonical source rays `alpha_i`, `1-Tr(T^2)=sum_(i,k)||alpha_i wedge alpha_k||^2>0`. One packet's proved rank three witnesses strictness; no cross-depth frame comparison is used.
F565 — Exact homotopy reconstruction: purify `T` by `Psi=sum_i delta_i tensor alpha_i`, lift `Psi` through theta Mellin-six survival shift (`index=-1`), apply first exit, then close theta and source-record observers. Output is exactly `T`, and `-index=Tr selfcommutator=Tr T=1`.
CANNOT-252 — Raw inter-depth fidelity is gauge-dependent. Any completion argument using `A_0!=A_1` without fixing source connection can be trivialized by independent fibre unitaries.
CANNOT-253 — POINH cannot close by positive coefficient-recovering prime damping: `riemannHypothesis_iff_xiReflectionIncidenceTraceOnePositiveCofinalRegularizationLanding` proves that whole trace-one cofinal repair class equivalent to RH. Missing completion must transform Pluecker/Kraus relations before scalar coefficient extraction.
MUST-175 — Derive from anomaly-subtracted integer/Poisson self-duality that completion commutes with POINH's canonical Kraus purification and two observer closures and is positive unital. Only then does `||T||<1` exclude a norm-one strict-right horizon; asserting landing remains the `ULF-DSA-003` RH-strength receiver.
F569 — Paper theorem (`ULF-INBSG-001`): for every positive compact injective infinite-dimensional `T`,
the norm-corona distance between scaled boundary-transfer germs is exactly
`||[E_eps(cT)]-[E_eps(dT)]||=|sqrt(c)-sqrt(d)|/(sqrt(c)+sqrt(d))`, independent of spectrum.
F570 — Exact three-organ conservation: for literal Poisson histories,
`||e_T(t²)-e_T(u²)||² + <psi_t,psi_u> = (t-u)²/(t+u)² + 4tu/(t+u)² = 1`.
F571 — Euler specialization `c=p^(2a)` makes oriented germ distance
`C=(p^a-1)/(p^a+1)=tanh(a log p/2)`.  From `G=1-C²` it reconstructs Burnol holonomy `4C/G`, Gamma
curvature `4C²/G`, Poisson visibility `sqrt G`, rapidity `artanh C`; reflection reverses only `C`.
F572 — Closed strong observer sends every scale germ to `I`, while open norm history separates scales.
A nonzero contrast is impossible for a finite-rank/gapped carrier; it is created exactly by faithful
compact spectrum accumulating at zero.
MUST-177 — Derive before divisor specialization that anomaly-subtracted integer/Poisson self-duality
identifies direct/reflected translations of the same boundary-transfer history modulo norm-null `C_0`.
Then F569 forces `p^(2a)=1`, hence `a=0`; asserting this equality on Xi fibres is only an RH classifier.
F577 — Paper theorem (`ULF-PBTIA-001`): for canonical purification `P=|Psi><Psi|`, `Cl(P)=T`,
singular completion and source-record closure have positive interchange anomaly
`A_(eps,c)=F_eps(cT)-Cl(F_eps(cP))=F_eps(cT)-c/(eps+c)T >= 0`.
F578 — Exact anomaly subtraction preserves unsquared source data:
`F_eps(cT)-A_(eps,c)=c/(eps+c)T -> T` in trace norm.  This is the operator shadow of Route P's
proved law “metric anomaly minus completion companion = literal primitive source,” not zero.
F579 — Every polarization has the same strong closed anomaly `A_(eps,c)->I-T`, but anomaly germs obey
`||[A_c]-[A_d]||=|sqrt(c)-sqrt(d)|/(sqrt(c)+sqrt(d))`; all transverse scale information lives in
the open completion/observer noncommutation.
CANNOT-255 — A moving anomaly is nonselective: subtracting each polarization's own `A_c` makes all
residual boundaries equal `T`.  “Residual vanishes/agrees after anomaly subtraction” has content
only when counterterm is fixed on pre-divisor theta source before horizontal specialization.
F580 — Formation-transfer germ mechanics now has a second nonprobabilistic chamber and exact
cross-species transport: anomaly-germ distance squared plus literal Poisson overlap equals one.
MUST-179 — Derive from literal integer/Poisson self-duality that actual Euler completion uses the
single theta-fixed anomaly germ `[A_1]`.  Then `[A_(p^a)]=[A_(p^-a)]` forces `a=0`; equality only at
Xi fibres remains a classifier, and strong equality is automatic at every grade.
F581 — Paper theorem (`ULF-POINH-001`, POINH-B): using the prime-mixed density as a local Fredholm
Euler multiplicity is impossible.  Exact `det(1-zT)^(-1)=(1-z)^(-1)` forces `Tr(T^2)=1`, while
physical Pluecker rank three gives `Tr(T^2)<1` by the exact wedge-dispersion identity.
CANNOT-256 — `T` cannot replace or rank-multiply local Euler atoms without corrupting prime-power
coefficients.  Its viable role is relational: completion history, observer interchange, or
non-scalar shorting formed after literal Euler coefficients and before divisor specialization.
F584 — Paper theorem (`ULF-SACWHT-001`): for any positive compact injective infinite-rank `T`, all
singular boundary-transfer scale germs generate one algebra:
`e_d=phi_(d/c)(e_c)`, `spectrum(e_c)=[0,1]`, `C*(e_c:c>0) ~= C_0((0,1])`.
F585 — Scale differences generate exactly the open-history ideal
`J=C*(e_c-e_d) ~= C_0((0,1)) ~= C_0(R)`; closed strong observation is endpoint evaluation in
`0 -> J -> C_0((0,1]) -> C -> 0`.
F586 — Cone middle algebra is contractible, so its connecting map `K_0(C)=Z -> K_1(J)=Z` is an
isomorphism; endpoint unit lifts to `e_1` and transgresses to winding-one `exp(2 pi i t)`.
F587 — Log-aperture translation crosses this cone extension to the one-dimensional Wiener--Hopf
extension; its compact ideal/index is the crossed-product form of theta first exit.  Sonin shell
cocycle independently recovers unsquared `Lambda(p^k)` from translation length `k log p`.
CANNOT-257 — Primary integral class is identical for every scale lift.  Although `||e_c-e_d||<1`,
`exp(2 pi i(e_c-e_d))` is null-homotopic.  No positive scale functional calculus can turn the
sub-unit contrast into an off-line integer.
MUST-181 — A viable direct-subunit mechanism must make literal prime formation twist the
Wiener--Hopf extension or quotient symbol itself, retain unsquared Euler shell coefficients, and
produce a failure-specific relative index with nuclear representative below source budget.  A
Möbius translate inside fixed cone is topologically trivial and is excluded.
CANNOT-258 — Prime marking/KMS existence does not repair CANNOT-257: every grade `a` defines the
unitary modular flow `beta_t^a(fU_gamma)=exp(i t a ell(gamma))fU_gamma`; `p^a` is its imaginary-time
value.  Crossed-product dynamics exists off wall.  Selection needs a failure-specific pairing of
this twist with Wiener--Hopf boundary class and literal nuclear ideal.
F588 — Ordered-cone law: if `e` is an order unit, `Phi` is positive, and nonzero `Phi(e)` spans an
extreme target ray, then `range(Phi) subset R Phi(e)`.  Thus positive landing of any faithful finite
compression of prime-mixed `T` on a rank-one horizon erases every transverse coefficient direction.
CANNOT-259 — This does not constrain actual Xi completion: P-G98 is singular boundary transfer
`E_eps(T)=T(eps I+T)^(-1)`, not a bounded positive map carrying `T` to the horizon.  Any viable law
must control its open singular history or anomaly quotient; positive-channel landing is closed.
F591 — [Lean] For positive trace-one Schatten-one `S`, exact pure-state radii are `inf_P||P-S||=1-||S||` and `inf_P||P-S||_1=2(1-||S||)`. The checked source is `S=primeHodgeHistoryRelativeCurvaturePrimeLift`, not the signed wall family `T(t)`: `||S||<=1/3`, `Tr S=||S||_1=1`, and primitive budget `B<115/216` (`primeHodgePurityCostFirewall`). Every rank-one projection lies at operator distance `>B` and nuclear distance `>2B` (indeed `>=4/3`) from this source.
CANNOT-260 — It cannot purify this `S` by a trace-class additive correction of nuclear norm `<=2B`, an operator-norm bounded-variation path of variation `<=B`, or a Schatten-one path differentiable everywhere with integrable derivative and action `<=2B` (`no_budgeted_traceClass_additive_pure_landing`, `primeHodgePuritySource_operatorPath_variation_gt_budget`, `primeHodgePuritySource_traceClassPath_action_gt_two_budget`, Lean). The norms, budgets and source are essential; this does not exclude arbitrary bounded maps, larger-cost paths, or singular completion.
CANNOT-261 — Retire MUST-183's finite-action transport: actual completion is singular/strong and
retains an open norm germ. No trace-norm path-length bound can be presumed to survive it; F591 only
constrains a source-generated relative nuclear representative.
F592 — Paper theorem `ULF-PHPTCIS-001`: prime visibility and signed contrast diagonal multipliers
`V_a,C_a` satisfy `V_a^2+C_a^2=I`; hence `Tr(V_aTV_a)+Tr(C_aTC_a)=Tr(T)=1`, grade-tail by
grade-tail, while every same-history cross-prime entry survives for `a!=0`.
CANNOT-262 — For `a!=0`, both two-channel charges lie strictly in `(0,1)`. The visible marginal is
not an integer; the full charge is integral but grade-blind. Information-neutral recovery cannot
discard contrast, so visibility-only direct-subunit selection is impossible.
F593 — Explicitly bounded history--prime `T` (`ULF-PHIN-001`) and physical Pluecker singular-source
`T` (`ULF-POINH-001`) are distinct. Pure-state radii survive arbitrary unitary transport, but prime
formation/completion do not; no structure-preserving intertwiner is proved.
MUST-184 — Construct before divisor a prime-marked pairing of open contrast history with the
singular-completion ideal: off-wall value integral and nonzero, nuclear representative bounded by
the literal Euler budget, completed relative class exhausting the horizon. It cannot be closed
visibility, total charge, fixed-cone scale, or a post-divisor endpoint bound.
F594 — `ULF-FBG-001`: blow up `a=0,p=infinity` by `u=a log p`. The literal
`(sech(u/2),tanh(u/2))` profile compactifies to a degree-one `RP1` kink with sharp action `1`; its
barrier gradient is exactly minus the prime-Gamma Bockstein and predicts the proved Schatten wall.
F595 — `ULF-FBG-002`: the framed orbit `mathcal T_a=W_a T W_a*` is positive prime-mixed `S1`,
`Tr=||.||_1=1`, trace-norm continuous across the wall, closes at `+-infinity`, and satisfies exact
information-neutral recovery `W_a*mathcal T_aW_a=T`.
F596 — Same object has an exact topology defect: for every `a!=0`, `||W_a-W_0||=sqrt 2` and
`||W_aW_a*-W_0W_0*||=1`, although `||mathcal T_a-mathcal T_0||_1->0`. Nuclear closure forgets a
fixed open prime-infinity frame defect.
CANNOT-263 — Whole projective kink cannot be a subunit residual: its action is at least `1` while
Euler budget is `<1`. It exists at every nonzero grade, so its degree alone is nonselective.
CANNOT-264 — Bare nuclear loop is contractible in positive trace-one `S1`; its constant integral
trace cannot select. Signed wall family is not a continuous homotopy. Frame cannot be discarded.
MUST-185 — Construct pre-divisor theta completion as a second framed cycle, cancel the universal
projective unit at frame level, and give the relative class a native prime-mixed nuclear
representative of norm `<=B_Euler<1` whose horizon pairing is unsigned escape. Trace/asymptotic
matching or singular pushforward of a finite budget does not qualify.
F597 — `ULF-FBG-005`: theta and cubic completion use reciprocal prime coordinates
`x=delta log p`, `y=(log p)/delta`, with `xy=log^2 p`; literal one-dimensional principal-symbol
identification is false.
F598 — Tensoring theta `v^2+c^2=1` with completion `h^2-k^2=1` gives a four-channel `O(2,2)`
frame. For every finite history--prime packet its source-fixed synthesis satisfies the exact
operator identity `A*JA=T_E`; cofinally these `J`-Grams converge in trace norm to prime-mixed
integral nuclear `T`. On the cubic diagonal this reconstructs anomaly = companion + source.
CANNOT-265 — Compact theta frame and split completion frame are not the same anomaly coordinate;
they are reciprocal legs. Identifying them, or taking channelwise absolute values before the
`J`-Gram cancellation, reproduces the old receiver/non-trace-class companion failures.
MUST-186 — Prove actual singular theta completion is a morphism of reciprocal framed `J`-Grams,
preserving cancellation and unsquared prime provenance before positive closure. Its relative
Schatten norm must be native to completion topology; only then can budget `<1` pair with unsigned
escape without violating the bounded/singular dichotomy.
F599 — The requested pre-divisor prime-mixed integral--nuclear homotopy defect already exists as
one Lean term `primeHodgeHistoryIntegralNuclearHomotopyDefect(t)`. For `t!=0` its kernel is
`1_(n=k) sign(t) w_n sqrt(mu_|t|(p)mu_|t|(q)) kappa(log p,log q)`; Lean proves `S1`, integral
trace `sign(t)`, trace norm one, reflection oddness, and every same-history cross-prime entry
nonzero. No zero/divisor enters.
F600 — Arithmetic identity of `T` is not supplied by those generic operator properties. On paper,
`T` is the unique bounded solution of the literal cubic prime-clock boundary law
`S_(I tensor L)^3(T(t))=8 sign(t) Phi tensor |b_|t|><b_|t||`, while its history tails are the
theta Mellin-six moments `m_n`. These two source laws force prime kernel and history factor.
F601 — Hostile correction to `ULF-FBG-005`: `A*JA=T` is a generic `J`-isometric dilation valid
for arbitrary positive trace-class `T`; it does not narrow the source model class. The card is a
bridge organizing reciprocal corpus coordinates, not a producer or selector.
CANNOT-266 — “Positive, prime-mixed, Schatten-one, integral trace” cannot characterize the
arithmetic object; many generic operators satisfy it. Any completion theorem preserving only
these invariants has forgotten literal formation and cannot close RH.
MUST-187 — Completion must intertwine `T`'s cubic prime-clock boundary equation and exact
theta-history tail flux before divisor specialization. Transporting only `T`, its trace, or a
generic `J`-Gram is information-neutral and does not qualify as source-to-horizon identification.
F602 — `ULF-RPBDT-001` gives a canonical trace density to the noncompact same-`T` completion
horizon. For every finite prime set `F` and history cutoff `N`, a positive fixed remainder
`R=U*RU` satisfies `Tr(P_(N,F)RP_(N,F))=N Tr(Q_F E_0*RE_0Q_F)` exactly; no infinite trace is used.
F603 — For any positive bounded completion `X-G_d=R`, inverse-clock cumulative cubic boundary
excess is the same quantity:
`sum_(p in F)[beta_p(X)-8b_d(p)^2]/(8log(p)^3)=Tr(Q_F E_0*RE_0Q_F)>=0`.
This is a same-object source/completion identity, not a bounded covariance landing.
F604 — Exact preservation of every cumulative unsquared prime coefficient forces `R=0`, even when
`R` has infinite total trace. If `E_0*RE_0` is a finite-rank projection, total excess is its
integer rank; excess `<1` forces zero. A rank-one horizon costs exactly one recurrent unit.
CANNOT-267 — Modular traciality, prime modular spectrum collapse, and reflected entropy neutrality
are already neutral-grade/RH classifiers. They do not derive admissibility from integer formation
and cannot be the higher producer (`ULF-MSA-FAILED`).
CANNOT-268 — A nonzero positive harmonic horizon cannot preserve all cumulative cubic prime
boundary coefficients. If a proposed completion is coefficient-transparent, its harmonic
remainder is zero; any claimed off-line horizon must exhibit positive boundary excess somewhere.
MUST-188 — `ULF-TRDS-001`: derive from literal integer/Poisson self-duality one positive relative
theta completion with `X-U*XU=T`, recurrent boundary excess `<=B_base<1`, and strict-right relation
incidence as nonzero grade-zero projection of the same harmonic remainder. These imply RH by
`1<=Ex<=B_base<1`; assuming any clause only on Xi fibres is still a receiver.
F605 — `ULF-CRSHC-001`: prime--Hodge reachability `W_d` and complete Burnol Euler covariance
`S_base` live on the same literal radial `L2(0,infinity)`. Their sandwich
`C_d=W_dS_baseW_d*` is canonical on `ell2(Primes)`, positive, nuclear, and fully prime-mixed.
F606 — `0<Tr(C_d)<=||W_d||^2 B_base<B_base<1`. Strictness follows because
`W_dW_d*=A_d` is positive compact, injective, infinite-rank, and trace one, hence `||W_d||^2<1`.
No numerical cutoff, abstract carrier unitary, zero, or divisor enters.
F607 — `X_d^src=G_d+I tensor C_d` is a positive bounded completion with exact displacement
`X_d^src-U*X_d^srcU=T_d` and recurrent excess `Ex(X_d^src)=Tr(C_d)<B_base<1`, despite infinite
ordinary trace. This closes construction of a same-carrier source-budgeted completion.
CANNOT-269 — Existence of a canonical sub-unit same-`T` completion does not select it: the
same-defect fibre contains arbitrary positive Toeplitz symbols. Calling `X_d^src` the actual theta
completion without a functional-equation source-factorization theorem is theatre.
MUST-189 — Revised `ULF-TRDS-001`: derive pre-divisor that anomaly-subtracted theta completion's
grade-zero harmonic covariance is `W_dVS_baseV*W_d*` for a source-forced contraction `V`; then
identify strict-right relation incidence as a projection in that same covariance. F604/F608 force
`1<=Tr(C_theta)<1`.
F608 — Common-radial admissibility is stable under every contraction: for `||V||<=1`,
`C_(d,V)=W_dVS_baseV*W_d*` yields a positive same-`T` completion with recurrent excess
`Tr(C_(d,V))<=||W_d||^2||V||^2B_base<B_base<1` (`ULF-CRSHC-001`).
CANNOT-270 — A fixed scalar mixture of Burnol's three exact aperture-colligation channels cannot
equal any strict-right completed conormal: source decay rates are `>=log 2`, target rate is
`Re(rho)-1/2<1/2`, and the tail ratio diverges (`ULF-FBCL-FAILED`, Lean-closed).
MUST-190 — Actual anomaly-subtracted functional-equation channel must change exponential type via
a nonlocal/aperture-covariant or additional defect channel while retaining a contractive
covariance factorization through `S_base`. Pointwise fixed-channel equality is excluded; only this
factorization can legitimately import the source `<1` bound.
F609 — `ULF-PQSCH-001`: every measurable radial contraction field `V(z)` on the phase circle
produces a positive operator-valued source density
`c(z)=W_dV(z)S_baseV(z)*W_d*` and a bounded positive Toeplitz history `R_V` with `U*R_VU=R_V`.
Thus `X_V=G_d+R_V` has the single conserved displacement `X_V-U*X_VU=T_d`; phases do not create
new defects.
F610 — Open history retains all Fourier blocks `C_j=integral z^j c(z)`, while Haar phase closure
is exactly `E_phase(R_V)=I tensor C_0`. Closure deletes nonzero temporal modes but preserves the
full grade-zero covariance and recurrent mass: `Ex(X_V)=Tr(C_0)`.
F611 — Every such source phase field obeys
`Tr(C_0)<=||W_d||^2B_base<B_base<1`; finite history--prime trace is exactly
`N Tr(Q_FC_0Q_F)`. The sub-unit anchor survives nonconstant open phase history, not only static
harmonic repetitions.
F612 — Norm-continuous paths of contraction fields give operator-norm-continuous same-`T_d`
completion paths. This is a genuine homotopy fibre: integral nuclear local charge stays fixed while
noncompact stationary history changes.
CANNOT-271 — Abstract Toeplitz recurrence is already in the corpus and phase dependence alone does
not evade the aperture-rate obstruction. If every channel commutes with radial translations, no
phase average can change primitive Burnol decay into strict-right Xi decay.
MUST-191 — Derive from integer/Poisson formation the actual theta contraction field, with a
polar--Gamma component that breaks aperture covariance before positive closure; then identify
strict-right relation incidence as a projection in its same grade-zero average. This gives the
closed contradiction `1<=Tr(C_0)<B_base<1`.
F613 — Hostile audit of the completion fibre: operator-valued Toeplitz phase lifting is a generic
bridge, not a producer. Functional-equation formation lifts are information-neutral, and arbitrary
phase fields preserve the same defect without selecting one completion.
F614 — Complete Green--Stokes positivity cannot finance a strict-right landing: its two positive
channels total `8||c||^2`, and even the canonical Krein-signed split tends to `(8/3)||c||^2`, both
strictly above the literal primitive budget for `c!=0`.
CANNOT-272 — Local `T`-completion instance of HARD LOCK P: do not seek selection from
positivity/order, phase averaging, or signed conservation. The surviving completed-source order
inequality for the pivot-resistant Julia--Wold orbit is proved equivalent to RH; assuming it merely
renames the endpoint.
MUST-192 — Any successor must be a pre-divisor formation law that acts before order comparison,
retains `T`'s cubic prime-clock equation and theta first-exit flux, and changes the completion
extension/quotient data rather than moving inside the already classified same-`T` fibre.

F615 — Lean separates algebraic formation from analytic admission. Every normalized arithmetic
function has a unique normalized Dirichlet-convolution half; the canonical squarefree half is
multiplicative, squares to the squarefree Euler source, and is holomorphic in its Euler chamber.
Yet its raw partial sums are unbounded at `s=6/11`; no cofinal raw or Cesàro pole schedule is
locally bounded there. Coefficientwise square roots therefore exist automatically and carry no
RH selection; the obstruction is extension through completion (`SquarefreeConvolutionHalfRigidity`,
`SquarefreeConvolutionHalfCofinalScheduleNoGo`, `SquarefreeConvolutionHalfCesaroAllCofinalNoGo`).
F616 — Lean closes the infinite-order scheduling loophole. Diagonal Laplace smoothing is not
locally bounded, and eventual bounded samples on any positive heat clock tending to zero force
the normalized adjacent gaps to escape every bound
`|tau_N-tau_(N+1)|=O(tau_(N+1)^(16/11))`. Independent pole degree does not change this once it is
at least `24` (`SquarefreeConvolutionHalfLaplaceDiagonalNoGo`,
`SquarefreeConvolutionHalfLaplaceScheduledNoGo`, `SquarefreeConvolutionHalfLaplaceTwoClockNoGo`).
CANNOT-273 — It cannot evade completion obstruction merely by increasing smoothing order,
changing a dense clock, or decoupling pole and heat clocks. Surviving scalar schedules must be
genuinely sparse in the exact `16/11` arithmetic metric, or alter source profile by a
source-derived singular/nonlinear correction.
F617 — Lean identifies constrained Weil positivity exactly. On the polar-moment-zero subspace, the restricted form is a scalar term plus the positive translation-defect energy `integral K_+(h) ||u-T_hu||^2/2` plus literal prime block, and equivalently the integral of the spectral density against one explicit multiplier. Nonnegativity of its ground energy at every aperture implies RH (`SuzukiWeilConstrainedKernelForm`, `ConstrainedWeilFourierMultiplier`, `riemannHypothesis_of_polarGroundEnergy_nonneg`).
CANNOT-274 — Polar constraints do not turn positivity into a producer. All-aperture constrained
positivity is now a Lean-certified RH endpoint; any finite-aperture inequality is a local gauge.
The prime-two finite-block certificate remains computation/paper evidence, not a Lean theorem.
F618 — Lean computes literal finite-Euler formation through second order. Its squared-radius
Hessian is exactly the sum of one-prime self jets and ordered two-prime bilinear jets; there is no
three-prime term. The two-mode product contribution cancels the diagonal covariance term, and the
true Euler-product log determinant has an explicit cubic remainder
(`SemilocalTwoModeBilinearResponse`, `SemilocalFinitePrimeSecondOrder`,
`SemilocalEulerProductLogDetRemainder`).
CANNOT-275 — A quadratic cross-prime compatibility, covariance, Gram, or Hessian cannot be the new
higher interaction: literal multiplication already exhausts that level pairwise. A genuinely new
formation law must enter through cubic/higher coherence or through nonlocal completion/extension
data. This independently supports retaining the cubic prime-clock law of `T`.
F619 — Route E's new Lean front localizes rather than solves its producer. Central/final defects,
both actual Case-I/II frequency regions, receiver-height costs, and source-fixed exceptional-volume
bounds are closed; the remaining harmonic statement is one collective Menon-normalized sum over
the growing ladder. Kloosterman completion likewise leaves cancellation only in incomplete
cross-modulus interaction, not equal-modulus or symmetrically completed blocks.
CANNOT-276 — It cannot infer global arithmetic cancellation from any fixed block, local large-value
bound, equal-modulus Gram, or symmetric two-leg completion. Local organs are now closed receivers;
the missing arithmetic law is collective and cofinal.
F620 — Formalization status sharpened: closed Lean certificates now cover the projective kink,
prime-framed integral-nuclear cycle, prime-Hodge purity-cost firewall, restricted-unitary cubic
projection algebra, and exact unsquared von-Mangoldt cubic budget. Lean also proves common-radial
contracted completions have recurrent excess `<1`, while every finite-rank projection horizon has
integer excess and excess `<1` forces zero. These certify corresponding portions of F594--F608 but
do not select actual theta completion.
F621 — Two advertised programmes remain incomplete and must not be promoted. Guth--Maynard has
only its Hermitian trace-defect/singular-value lemma in Lean, not the large-values theorem.
Entire-heat code excludes algebraic-differential orders zero and one and has a long local
order-two Strelitz/Newton reduction, but the global maximum-locus continuation is still missing;
the paper order-three floor is not yet a closed Lean theorem.
CANNOT-277 — Do not count numerical certificates, conditional assembly theorems, local Newton
branch packages, or one imported inequality as closed source laws. They constrain searches but do
not discharge a universal-law or RH gate.
F622 — `ULF-CCEL-001` defines powered-clock defect `omega_3(F)=D_E^3F-FD_X^3`; a splitting change adds `delta_3(H)=D_I^3H-HD_X^3`. This is algebraic, with no parameterized completion flow.
F623 — Lean proves lift independence in `coker(delta_3)`, vanishing iff a powered-clock-equivariant lift exists, and `D_E^3F=FD_X^3+i omega_3`. Actual deformation interpretation is unproved.
F624 — CCEL's unipotent example has powered-clock defect `3 id` and zero cubic coboundaries. It separates vector-space splitting from clock splitting; its first clock defect is already `id`. It does not establish a new obstruction beyond first-order clock equivariance (audit ULF-CDMA-001).
CANNOT-278 — Ordinary Busby perturbation by nuclear `T`, odd projection traces, cyclic/Massey
cocycles without arithmetic realization, and support-boundary regularizations do not answer the
gate. They respectively vanish in the corona, recover an old index, read a supplied class, or add
a boundary parameter without deforming theta completion.
MUST-193 — `ULF-PHCCED-001`: construct before Xi specialization the literal theta quotient landing
as a cubic-clock morphism; evaluate its lifting class on PCOB's unique
`S_Lambda^3(T)=8 sign(t) Phi tensor |b_t><b_t|`; prove this ideal value is the Xi escape incidence
and inherits the same primitive nuclear `<1` budget. Failure of any coefficientwise identification
retires the mechanism.
F625 — `ULF-PLCIE-001`: inverse prime heat on the literal formed density has exact weight `p^(2u)w_d(p)=8d log(p)p^(-(1+2(d-u)))`, summable exactly for `u<d`. Thus `d` is the maximal trace-ideal time of `T_d`; every finite-prime compression crosses it by an invertible gauge, while cofinal source completion cannot.
F626 — At forced exit `u=d`, first prime clock is exactly `8d(log p)^2/p`, the projective coefficient ray of the proved completion metric anomaly; equality of scalar normalization is open. Same source orbit has third forward jet `-S_Lambda^3(T_d)=-8 Phi tensor |b_d><b_d|`. Cubic birth and non-trace-class completion anomaly are therefore infinitesimal and endpoint shadows of one literal source flow.
CANNOT-279 — One-sided prime reflection and local Stokes multi-Rees channels are old/closed.
Finite-cutoff gauge failure, generic jets, and the always-one source survival index cannot select
the Xi `0/1` escape invariant; a divisor-fitted scalar match `8d=115/(864a^4)` is circular.
MUST-194 — Construct theta-forced normalization and relative cubic-clock boundary pairing for
`0<=u<d`; prove its integer is Xi escape multiplicity and its same ideal representative is the
anomaly-subtracted primitive Euler remainder with norm `<1`. This is sole PHCCED completion gate.
F627 — `ULF-PLCCKU-001`: raw inverse-heat endpoint is unbounded. On prime packets
`n<p<=n^2`, critical cubic-Cauchy Rayleigh quotients grow at least by a constant times
`sum log(p)/p`, which grows like `log n` from existing explicit Mangoldt-square bounds.
CANNOT-280 — Raw `T_(d,d)` is not a bounded extension element; trace normalization returns the
old nonselective aperture family. Only a source-canonical closed endpoint relation and its graph
projection/bounded transform survive. Retire PHCCED if that transform has universal cone class.
F628 — `ULF-PCLGF-001`: critical cubic prime kernel is exactly the Gram of literal Laplace synthesis `(A_*c)(t)=2t sum_p c_p(log p)^2p^(-t-1/2)`; before exit its column norm square is `w_(d,u)(p)`, so this family is Hilbert--Schmidt exactly for `u<d`.
F629 — `A_*` is unbounded but canonically closable: compact-away-from-zero `L2` tests lie densely in its adjoint domain, their prime coefficients dominated by `(log p)^4/p^(1+2epsilon)`; endpoint object is `Graph(cl A_*)`, not a finite part.
CANNOT-281 — Closed unbounded synthesis alone is nonselective, and the full-Schwartz theta-null
Hilbert-Gram category is nonclosable. Do not call the source graph an RH mechanism or transport it
naively into ordinary full-source `L2`.
MUST-195 — Build theta completion as a relative Calderon/graph projection against `cl A_*` in a
source-framed graph topology. Prove its nonconstant relative index equals Xi escape and its same
relative representative has the primitive Euler norm `<1`; otherwise retire PHCCED.
F630 — `ULF-PCLGF-001` is now Lean-proved: literal unsquared finite-prime Laplace synthesis has dense source domain; each `t>0` evaluation is an `ell2(Primes)` reporter; zero graph fibre is trivial; hence the critical cubic endpoint has a canonical closed graph retaining every core value.
CANNOT-282 — Neither closability nor its bounded graph transform selects Xi: they occur before theta comparison and closed-unbounded source syntheses already exist without RH consequences.
MUST-196 — Next object must be a relative theta Calderon class on this exact source graph, with prime labels retained in one representative whose boundary index is escape multiplicity and whose nuclear norm is the existing strict sub-unit Euler budget. Any separate representatives fail.
F631 — `ULF-MCPT-001`: sigma-trace reads the cubic associator as five modular-displacement channels; all vanish in the modular centralizer. Lean proves `P(C⁻¹(xP)C)P-xP=(bc/(ad-bc))xP`; block-separable density is blind. A prime-mixed `3/4<1` witness has ordinary cubic trace zero, modular cubic value `-1/8`, defect one.
F632 — Reflected diagonal prime-depth incidence is a flat coboundary: finite characteristic polynomials, determinants, and cyclic moments are horizontally blind.
`ULF-PBFMS-001` forms non-diagonal Burnol covariance from prime powers; every injective finite packet has full support and canonical inverse.
CANNOT-283 — KMS positivity, modular traciality, or an abstract twisted cocycle cannot be the producer. They are receivers unless literal Burnol density defines the modular action before Xi and theta compression itself creates its cofinal nonnaturality.
MUST-197 — Construct cofinal modular-compression class of finite full Burnol Grams, then prove one same-representative boundary theorem: its cubic twisted source pairing equals the ordinary formation-relative index and is bounded by `B_base<1`. Diagonal weights, bounded S3 limits, or a postulated KK/cyclic pairing fail.
F633 — Prime-mixed nuclear `T` is an observer: its unframed positive loop is null-homotopic; nested projections are diamond-flat and Schur elimination transitive.
F634 — For the defined frame, `H_C(U)=C⁻¹UCU⁻¹` has exact cocycle, reversal, modular intertwining and cubic transgression; `H_F(0)=1`, `H_F(a)≠1` off neutral. Identification of that frame with Poisson completion is unproved.
F634a — Exact fusion: `[C_F⊗I,U_F(a)]_(ir,js)=(C_F)_(ij)(U_j-U_i)_(rs)` with every Burnol edge `(C_F)_(ij)=A_iA_j2/c_(ij)^3≠0`.
F635 — `ULF-PDAMB-001` proves `PrimeDepthThetaModularAdmissible(a) ↔ a=0` via close 2/3 depth rates and block `I+g²/(de-g²)(I-U₃U₂⁻¹)`. Its frame uses `a log p/2`, ignoring depth; no classification for a valuation-clock replacement follows.
CANNOT-284 — Diagonal/commuting frames, finite determinant/phase/K1, old flat exponential depth coboundary (boundedness iff RH), raw curvature, quadratic Schur data, positivity, and unframed `T` cannot produce selection.
MUST-198 — Before using F635, derive its exact prime-only frame from theta/Poisson and prove Xi admission; neither is established. The other open edge remains one cofinal boundary representative equal to Xi escape and bounded by `B_base<1`.
F636 — `[PAPER-PROVED; not Lean]` ULF-CTRS-001: powered-clock defect differs from third transport jet by `3A(AF-FB)B`; CCEL's unipotent orbit is affine, so its true third jet is zero; `A_Q^3 f=fB^3` does not ensure ideal landing of `(L_A-R_B)^3F`.
F637 — `[PAPER-PROVED; not Lean]` Positive labelled clocks `a_i,b_j>=c>0`: cubic-root Schur recovery divides by `a_i²+a_i b_j+b_j²`, trace norm bound `1/(3c²)`; powered/ordinary defects have identical trace-class corrections on maximal coefficient domains, including cofinal near-resonances; smaller physical domains remain open.
F638 — `[PAPER ARGUMENT; not Lean]` `diag(n^-4 tanh(an))` is trace-class/C², smooth off zero, third neutral jet `-2/n` nonsummable, yet Calkin image zero in a split extension; cubic ideal-exit support inside a sub-unit norm ball does not supply an integral completion class (ULF-CDMA-001).
F639 — `RoutePPrimitiveBurnolApertureDampingSemigroup` already proves weighted shift `K_u f(t)=t/(t+u)f(t+u)`, contraction, primitive log-clock eigenfeatures and backward failure; a relative theta action must add information beyond this source semigroup.
CANNOT-285 — Do not identify clock cubes with transport third derivatives, count positive-clock reparametrization as a new selector, or call a declared tanh frame the literal theta completion without an identification theorem.
MUST-199 — Specify actual completion action and domains, retain mixed third-jet terms and affine zero-clock charge, then prove the unchanged same-representative Xi/Euler boundary identity. ULF-CDMA-001 records audit and survivor.
CANNOT-286 — It cannot obtain selection from density plus a declared closed admission set: `RHTower.nonempty_closedOrientedSourceAdmission_iff` (`RiemannDenseSourceClosedAdmissionLaw`) classifies existence as exactly the chosen `good` proposition; its global Xi specialization is exactly RH, not an unconditional construction.
MUST-200 — It must prove both source landing and the finite detector trace for the same independently constructed closed admission set; density then closes selection (`exists_deningerCompletedXiClosedHodgeAdmission_iff`, `xiCompletedGreenClosedHodgeLanding_iff_riemannHypothesis`); neither declaration supplies that set off neutral.
CANNOT-287 — It cannot retain prime identity as separate closed Burnol output sectors: every prime's full depth tower spans densely the same `L²(0,∞)`, with literal unsquared Euler amplitudes retained (`PrimeBurnolDepthCompletion.dense_primeBurnolLiteralDepthSpan`, Lean; general law `BurnolDepthCompletion.dense_burnolDepthSpan`).

CANNOT-288 — It cannot be a short-interval mean-square rate: no bound of Menon's shape on `∑_{x≤n<x+h} μ(n)` — at any rate `φ` with `N φ(N) ≫ N^(1/2+δ)`, even pointwise in the start, together with the corpus's averaged fibre hypothesis `AveragedShortInterval` — reaches the strict-half-power Möbius bound (Littlewood's criterion, RH) using only `|μ| ≤ 1`: a `±1` sequence satisfies all of them and violates every such bound (`RHTower.Sieve.routeE_shortIntervalRate_not_strictHalfPower`, Lean).
MUST-201 — It must derive actual theta admission, not prescribe prime-only contrast: that declared two-prime relation closes to its scalar graph when `p=q` or `a=0`, and to all `H×H` otherwise (`primeOnlyBurnolContrastRelation_closure`, Lean). This classifies the stated scalar action, not the full matrix frame or actual Xi completion.
F640 — Tail-rounding law (Lean): if a norm-summable sequence retains dense real span after every finite deletion, its integer span is dense; finite rounding error is bounded by the norm tail independently of coefficient size (`IntegralTailCompletion.dense_integer_span_of_summable_tail_dense`).
CANNOT-289 — It cannot recover discrete prime sectors by restricting Burnol coefficients to integers: every single prime's literal unsquared Euler depth columns still have dense integer span in real `L²(0,∞)` (`PrimeBurnolIntegralDepthCompletion.dense_integer_primeBurnolRealDepthSpan`, Lean). This retires unrestricted integer-combination repair, not bounded coefficients, multiplicative formation, or source-labelled graph topology.
F642 — The literal interacting squarefree Gibbs source already exists: prime insertion is `J_(S+p)(x)=J_S(x)−J_S(px)`, and finite-prime sections approximate `sum μ(n)e^(−nx)` with error at most `e^(−x(y+1))/(1−e^(−x))` for primes through `y` (`GibbsScaleContraction`, `GibbsInfiniteVolume`). Reconstructing this gas is not a new mechanism. The complete signed source is strictly negative on `[log(2)/5,log(4/3)]` (`mobiusDiscreteLaplaceTransform_re_neg_on_explicit_interval`, Lean): it cannot itself equal a nonnegative partition sum. This does not exclude signed observables or a two-copy representation.
F670 — It cannot count positive-Gibbs normalization as a new cancellation mechanism: for `x>0`, the exact source is `Phi(x)=Z(x) g(x)`, where `Z` is the positive squarefree exponential partition and `g` its parity expectation. The corpus already proves that `forall epsilon>0, exists C>=0, forall 0<x<=1, |g(x)|<=C x^(1/2-epsilon)` implies RH (`MobiusExponentialGibbsBoundary`: `mobiusSquarefreePartition_mul_gibbsParity`, `riemannHypothesis_of_mobiusSquarefreeExponentialGibbsMixing`, Lean). This is a proved consumer with an unproved mixing input, not unconditional RH; neither Gibbs existence nor the full-prime band law F656 establishes that input.
F671 — It cannot infer real-rootedness or a parity-current upper bound from conditional two-prime repulsion: the Gibbs Rayleigh gap is strictly positive, yet every fixed three-distinct-integer gas (`p,q,r>=2`) has no real cubic factorization at all sufficiently small positive coupling (`twoPrimeExponentialGibbsRayleighGap_pos`, `parity_vortex_three`, Lean). Positive survivor: `Disc_2/J_2 -> -4`, `Disc_3/J_3^2 -> -27`, hence eventually `J_3^2<=|Disc_3|` (`GibbsClusterRepulsion`). Repulsion measures current here; a repulsion lower bound does not supply the required current upper bound. These are fixed finite gases, not an RH exclusion.
F672 — It must distinguish finite stability from uniform parity suppression: two-, three-, and four-integer Gibbs gases have no closed-right-half-plane zeros (for distinct labels >=2 and positive coupling); arbitrary finite `S`, `x>=0`, is certified under `x prod_(p in S)(1+p)<1` (`GibbsSectorStability`, `quadruple_gas_sector_stable`, `gibbsDiagC_ne_zero_of_sigma`, Lean). That shrinking-coupling condition is essential to the stated all-order theorem; these certificates do not establish F670's joint-limit mixing input.
F673 — It cannot claim an all-primes instability theorem from the truncated-gas certificate alone. Given a light/heavy split at cardinality `J`, gas error from `sum_(j<=J) choose(k,j) z^j` is at most `(epsilon+exp(-R))(1+|z|)^k`; the sixth exponential section has no imaginary-axis zero and third Hurwitz minor `-1440` (`GibbsTruncationSection`, Lean). These declarations do not include a root-transfer/existence theorem for the actual prime gas. Positive survivor: a reversed energy ordering blocks the split; `{2,3,7}` already blocks level one (`GibbsEnergySpread`: `no_truncation_dichotomy_of_two_three_seven`, Lean). This does not prove natural-gas stability or rule out every higher-cardinality split.
F643 — Exact Gibbs energy balance loses only same-sign dilation coherence; dissipation vanishes exactly when normalized currents at `x,px` are opposites (`GibbsSignedCovarianceAccumulation`, `GibbsCriticalDissipationAntiscaleResonance`). Actual terminal-prime Mellin blocks have simultaneous gain at `t=π/log y`; generic insertion is not strict contraction.
CANNOT-290 — It cannot obtain cancellation by renaming covariance accumulation: its difference from the contraction baseline is exactly the endpoint current. Scalar first-trace normalization leaves antiscale coherence unchanged (`gibbsPrimeInsertion_accumulation_bound_iff_current_bound`, `routeEScalarFirstTrace_antiscale`).
CANNOT-291 — It cannot infer square-root cancellation from successor–dilation subdivision alone: its joint-eigenvector law holds for every completely multiplicative sequence, including logarithmic characters (`CCMFirstClockBlockSubdivisionTransfer`).
F644 — Finite Möbius Gamma--Hankel energy is `Γ(r)sum_(m,n≤N) μ(m)μ(n)/(m+n)^r`; its diagonal has a cutoff-uniform bound for `r>1`. An off-line zero forces the off-diagonal covariance to `+∞` on every strict-right line below it (`MobiusLaplaceGammaHankelWall`, `MobiusGammaHankelTransverseEscapeCone`).
MUST-202 — It must prove the covariance-return bound, not another transfer: bounded returns at arbitrarily large `N`, on exponents `r>1` arbitrarily close to `1`, are exactly RH (`mobiusLaplaceCofinalGammaHankelOffDiagonalFrequentlyUpperBounded_iff_riemannHypothesis`, `MobiusMertensFiniteSectionEnergy`, Lean; Littlewood converse discharged). Sparse returns are not a weaker conjecture. The return bound itself remains unproved.
F645 — Born probabilities and every diagonal-energy Born variance can remain unchanged under unimodular Euler twists carrying prescribed Helson zeros (`exists_phase_fisher_blind_with_prescribed_zero`, Lean). This does not exclude phase-sensitive interferometry or all possible QFI experiments.
F646 — Indeterminate Hamburger completions can share all local-time jets yet have incompatible recurrence; compact positive-spectrum families can separately share all perturbative jets yet differ nonperturbatively (`exists_infiniteJetQuantumRecurrenceSeparation`, `quantumRecurrenceGlobalCompletionWitness`, Lean). Neither theorem contradicts compact moment determinacy.
F647 — A finite observer's return is weighted edge-phase energy; its exact visible capacity is vertices minus coherence components (`finite_quantum_observer_coherence_law`, Lean). Observed recurrence need not be full-state or full-channel recurrence.
F648 — Must distinguish propagation bounds from exact recurrence constraints. Generic static nearest-neighbour qudit paths attain maximal projective rank, both clock exponents and every positive-weight replica floor (`exists_quditPath_everyChart_sameDraw_recurrenceCollisionLaw`, Lean). One fixed absolutely summable infinite spin field simultaneously has exponentially distance-suppressed flip commutators and maximal local-flip temporal rank `2^|F|` in every finite environment `F` (`quasiLocalInfiniteLBit_fullRank_and_commutatorBound`, Lean). Spatial locality, even with this infinite-volume influence bound, supplies no low-rank bound; these certificates supply no arithmetic rapid-return estimate.
F649 — Collective pure-generator QFI equals four times the complete covariance sum (`pureGeneratorQuantumFisher_collective_eq_four_mul_sum`, Lean). Its positivity does not bound cross terms by diagonal terms or pay coherent preparation cost. Equal SLD QFI and Hilbert--Schmidt speed under one fixed Hamiltonian coexist with exact tick returns versus strictly positive inverse-tick return defects (`qutrit_equal_information_global_recurrence_separation`, Lean); local information does not determine recurrence.
MUST-203 — It must distinguish cutoff returns `N->infinity` from time recurrence at fixed `N`; the quantum-recurrence manuscript's completed-time-then-size laws supply no joint-limit transfer. Any physics mechanism must retain the unnormalized arithmetic signal and prove that transfer or a direct cofinal estimate.
F650 — Literal cutoff-scale transfers `T_p F(N,x)=F(N div p,px)` still commute; `D_p=I+T_p` commutes with signed insertion `I-T_q`. Integer birth obeys `Delta T_p F=1_(p divides N+1) T_p Delta F` for every cutoff history, not only Mobius (`GibbsHardCutoffTransport`, Lean). The floors alone do not create noncommuting mixing; the birth identity alone supplies no Mobius-specific cancellation.
F651 — For `p>=2`, zero-boundary cutoff histories are determined by same-sign seams through exact finite alternating reconstruction. Nevertheless one history has `|D_p F|<=1` everywhere and `|F(p^K,x)|=K+1` (`exists_hardCutoff_unit_seam_logarithmic_escape`, Lean); injectivity does not imply uniform control.
F651a — It cannot gain an independent bound by stacking one-prime window energies: all equal the same Mertens palindromic energy (`mobiusMertens_primeWindowReversalEnergyUniversality`, Lean). Multiplication by an analytic nowhere-zero factor preserves the Mellin continuation wall (`mobiusLaplaceUnitTwistedMellinContinuationWall_iff`). Growing the included-prime aperture to cover every prime through cutoff `N` gives exactly the original Mertens convolution and the same open upper-bound predicate (`canonicalFinitePrimeApertureSecondCesaroSubpowerUpperBound_iff`). These classify the stated reports, not arbitrary joint source dynamics; neither a new relation nor a uniform moving-boundary estimate follows.
CANNOT-292 — It cannot bound all unnormalized cutoff histories using a zero initial boundary and uniformly bounded one-prime seams (`not_hardCutoff_unit_seam_uniform_bound`, Lean). This is a generic sup-bound obstruction, not a counterexample for Möbius coefficients, a Gamma--Hankel norm theorem, or a no-go for variable-hazard/adjoint/additional-source dynamics.
F652 — For every fixed `1/2<=sigma<1`, complete prime-cutoff energy `E(Y)=integral_(-1)^1 |Gamma(sigma+it)|² product_(p<=Y)|1-p^(-sigma-it)|² dt` tends to `+infinity` along all apertures; indeed `E(Y)/Y^b -> +infinity` for every real `b`. Every continuous nonnegative weight positive at zero has the same escape (`GibbsFullPrimeGammaEscape`; `GibbsPrimeIntegerFootprint`: `RHTower.fullEuler_weighted_energy_div_rpow_tendsto`, Lean).
CANNOT-293 — It cannot obtain bounded integer-prefix Gamma--Hankel returns by uniformly bounding unchanged complete prime products: those products have no bounded-energy cofinal subsequence even on a fixed bounded-height window (`not_fullPrimeEulerGammaEnergy_bounded_returns`, Lean). This rules out that approximation, not the Möbius integer-prefix estimate or cancellation between a prime product and its discarded integer tail; pointwise Gibbs recovery is not an energy bound.
F653 — The normalized divisor channel `C_eta f`, as its parameter `eta` decreases to `1`, is weakly null and killed by every fixed compact synthesis, but retains limiting squared norm `||f||²/zeta(2)` (`mobiusChannelPaper_weakly_null`, `mobiusChannelPaper_compact_synthesis_kills`, `mobiusChannelPaper_total_energy`, Lean). It cannot identify vanishing fixed observations with vanishing total mass; this channel parameter is not the critical Mellin abscissa.
F654 — It cannot repair full-prime Gamma energy by subtracting any fixed bounded-coefficient integer section of length `floor(Y)^k`: residual energy divided by full-prime energy tends to `1`, for every fixed natural `k` and `1/2<=sigma<1` (`fullPrimeEulerGamma_integer_section_residual_ratio_one`, `fullPrimeEulerGamma_mobius_section_residual_ratio_one`, `GibbsPrimeIntegerFootprint`, Lean). It must distinguish prime aperture from integer height. For `k>1` the full integer section is a correction, not the literal discarded prime-product tail; this does not bound or disprove bounded Möbius-prefix returns.
F655 — It must control the moving integer boundary layer: for every `r>1, delta>0`, `C_N(r)-integral_((N+1)^(-2))^delta x^(r-1) F_N(x)^2 dx -> T(r,delta)-D(r)`, where `T` is the genuinely integrable infinite-source exterior above `delta` and `D` the convergent diagonal. Energy below `(N+1)^(-2)` tends to zero; if total prefix energy escapes, the moving layer carries asymptotic fraction `1` (`MobiusIntegerCuspConfinement`: `tendsto_mobiusCovariance_sub_movingCusp`, `tendsto_mobiusMovingCusp_energy_ratio_one`, Lean). Fixed interior control cannot exclude boundary concentration; no moving-layer bound or RH proof follows.

## 2026-09-05 — Riemann–Siegel phase locking (card `1-in-progress/rs-phase-locking-geometric-mean-law.md`)

F640 — [Lean] The random-phase model of the approximate functional equation has an exact log-mean law: `⨍_φ log|2 Re(e^{iφ} w)| = log ‖w‖` (`RHTower.circleAverage_log_norm_two_re_mul`, via Jensen's max identity `circleAverage_log_norm_const_add` and doubling invariance `circleAverage_comp_sq`). Hence the torus model predicts `E log|ζ(1/2+it)| = E log|D(t)|`, the log-mean of the Riemann–Siegel amplitude.
F641 — [NUMERICAL, pod 2026-09-05; not Lean] The Steinhaus torus log-mean `c₀(N) = E log|∑_{n≤N} X_n n^{-1/2}|` is `≈ (1/8) log log N` (`0.200` at `N=10²`, `0.310` at `2·10⁵`), with log-variance slope `≈ 1/4`; the flow mean of `log|D(t)|` at RS length tracks it (`0.198, 0.216, 0.233` at `T = 10⁵, 10⁶, 10⁷`) while the flow mean of `log|ζ(1/2+it)|` is `0` (RH regime). The AFE phase `θ − arg D` is not uniform: `E log|cos| ≈ −0.93` against `−log 2`.
CANNOT-289 — It cannot be a torus/random-phase model of the critical line: that model's geometric mean of `|ζ|` grows like `(log t)^{1/8}` and its log-variance is `(1/4) log log t`, while Littlewood's lemma under RH gives geometric mean `1` and Selberg gives variance `(1/2) log log t`. Every statistic that transfers from the torus (mean square, MV, low moments) transfers the wrong log-mean; the RH content sits entirely in the phase law.
MUST-202 — An AFE-based producer must derive, from the arithmetic of `θ(t)` and `∑_{n≤√(t/2π)} n^{-1/2-it}`, the phase law `(1/T)∫ log|cos(θ − arg D)| = −log 2 − c₀(N(T)) + o(1)`; this is exactly `(L)`: `∑_{β>1/2}(β − 1/2) = o(T)`, a signed first-moment target strictly between the known `41 %` line proportion and RH, consistent as an open problem with a `1/log T` cluster of off-line pairs.
F642 — [Lean] Prime cutoff versus size cutoff: the Steinhaus torus log-mean of a prime-truncated random Euler product `∏_j (1 − r_j z_j)⁻¹` (`0 ≤ r_j < 1`) is exactly `0` (`RHTower.torusAverage_log_norm_eulerProduct`), while the size-truncated amplitude `1 + z₂/√2 + z₃/√3` has strictly positive torus log-mean (`RHTower.torusAverage_log_norm_three_pos`). The two random models of the critical line already differ in geometric mean at length three; the Riemann–Siegel phase is what converts one into the other, exactly under RH.
F656 — It must retain stretched-exponential integer height in full-prime formation: fixed `a=1-sigma in (0,1/2]`, `0<b<a<c`, restrict exact signed prime configurations to `Y^b<log n<=Y^c`. Their weighted `[-1,1]` energy/full-prime energy tends to `1`, for every continuous nonnegative weight positive at zero, including literal Gamma. The low section's relative energy tends to `0`; the high tail tends uniformly in real frequency to `0` in absolute norm (`GibbsEulerLogarithmicConfinement`: `fullEuler_configuration_band_energy_ratio_one`, `fullPrimeEulerGamma_configuration_band_energy_ratio_one`, Lean). Even corrections bounded by `M exp(k Y^b)` with `b<a` have vanishing relative energy. These are prime-smooth configurations, not the all-integer Mobius prefix; no bounded-return or RH selection law follows.
F657 — It cannot use vanishing raw thermal phase as a zero selector: `L_N=-sum_(n<=N)(-1)^(n+1)n^(-beta-it)/Z_N`, `Z_N=sum_(n<=N)n^(-beta)`, tends to zero and is eventually nonzero at every fixed `0<beta<1,t`; `zeta(1/2)!=0` is an explicit false positive (`DQPTThermodynamicReadout`, Lean). Arithmetic recovery amplifies an error `e` by exactly `Z_N||e||`, diverging for fixed nonzero `e`. Positive survivor: `-log|L_N|/log_2 N -> log 2` iff the strip point is a zeta zero; elsewhere its limit is `(1-beta)log 2` (`dqpt_freeEnergy_limit_eq_log_two_iff`). This rate reads the divisor, not its horizontal selection. The existing reflected-tail rate equality is exactly `beta=1/2` (`dqpt_reflected_rates_eq_iff`); no new RH producer follows.

## 2026-09-05 — theta completion with a source-forced phase (ULF-TRDS-001, retired to `5-failed`)

F658 — [Lean] The literal all-prime Burnol source is the Hankel operator of `−ζ'/ζ`: for real radial points `L₁, L₂ > 0`, `∑_pe f_pe(L₁) f_pe(L₂) = −L₁L₂ (ζ'/ζ)(1+L₁+L₂)` (`tsum_routePPrimitiveBurnolWindowFeature_mul_eq_neg_logDeriv_zeta`); its rate measure is `∑ Λ(n)/n · δ_{log n}`. Diagonal real-rate factorizations have Hankel form `∫|F_h(u)|² dν(u)`, with `F_h(u) = ∫ L e^{-uL} h`; this describes that factorization class, not every possible law on the carrier.
CANNOT-294 — It cannot realize the anomaly-subtracted theta/Xi completion as a positive source-factored covariance on the common radial carrier: the divisor side of the prime-density explicit formula is `pole − source` (rate measure `du − ∑Λ(n)/n·δ_{log n}`), and the Carleman pole form does not dominate the Euler source — on an explicit spike vector `∫_0^∞|F_h(u)|²du < Re⟨h, S_base h⟩`, below even the single `p = 2` atom (`poleHankelEnergy_radialSpike_lt_re_inner_baseNuclearSource`, Lean). The polar–Gamma counterterm has no finite radial form of its own (`½ψ((1+x)/2)` is not a Laplace transform); only its sum with the zero density is finite. TRDS.2/3/6 fail together.
MUST-204 — It must keep the radial no-go within its proved scope: `poleHankelEnergy_radialSpike_lt_re_inner_baseNuclearSource` excludes nonnegativity of the literal `pole - source` form on all carrier vectors, hence any positive covariance equal to that form. It does not exclude every pre-divisor law on `L²((0,infinity),dL)` or classify Toeplitz positivity/PNT decay as the only alternatives. A different signed, nonlinear, joint-parameter or completion mechanism requires its own theorem; the spike alone cannot retire it.
F659 — For every prime `p`, finite `s` and arbitrary complex weights `w_n`, put `F(z)=sum_(n in s) mu(n)w_n z^n` and `A_(p^j)=sum_(a mod p^j, gcd(a,p)=1) F(exp(2pi i a/p^j))`. Then `A_(p^j)=0` for `j>=3` and `A_p+A_(p^2)=-F(1)` (`MobiusRamanujanTwoLevelConservation`: `mobiusPrimitivePrimePowerReadout_high_vanish`, `mobiusPrimitivePrimePowerReadout_two_level_reconstruction`, Lean). Exact finite unsquared-source conservation; classical Ramanujan bridge, not a new RH mechanism.
CANNOT-295 — It cannot treat complete primitive prime-power sums as an independent tower of nonzero Möbius replicas: squarefreeness annihilates every level above two. These are unnormalized sums; normalized averages require totient weights. The law does not annihilate individual rational-point values or their quadratic energy, and supplies no cutoff-uniform upper bound.
F660 — Orthogonal `P<=Q`, arbitrary orthogonal `R`: set `D=Q-P`, `A=(I-D)RD`, `C=(R-P)^3-(R-Q)^3-(Q-P)^3`. Nuclearity of `C` alone forces `A` Hilbert--Schmidt, `Tr C=0`, `Re Tr(DCD)=-||A||_HS^2`, and `Re Tr((I-D)C(I-D))=||A||_HS^2` (`NestedSourceCubicConservation`: `nestedSourceCubicAssociator_nuclear_conservation`, Lean). No individual displacement is assumed compact. Positive survivor: finite matched transition energies, not merely trace cancellation; operator-theoretic bridge, novelty unverified.
CANNOT-296 — It cannot obtain a nonzero ordinary trace from `C=(R-P)^3-(R-Q)^3-(Q-P)^3` for orthogonal projections when either (i) `P,Q` commute and `C` is nuclear (F661), or (ii) `(R-Q)(Q-P)` is nuclear, without commutation (F669). Compact individual displacements are unnecessary. Case (ii) leaves combined-cubic nuclearity alone with noncommuting projections open. Zero trace could support exclusion only after an independent arithmetic identification; these theorems provide neither that identification nor an RH bound. Nontracial pairings and other defects remain outside their scope.
F661 — Commuting orthogonal `P,Q`, orthogonal `R`: set `U=Q-PQ`, `V=P-PQ`, `W=I-U-V`, `A=WRU`, `B=WRV`, `J=VRU`, `C=(R-P)^3-(R-Q)^3-(Q-P)^3`. If `C` is nuclear, all three transition maps are Hilbert--Schmidt; with squared energies `a,b,j`, the real traces of `UCU,VCV,WCW` are exactly `-a-2j,b+2j,a-b`, and `Tr C=0` (`CommutingSourceCubicConservation`: `commutingSourceCubicAssociator_nuclear_conservation`, Lean). Positive survivor: finite three-channel balance without compact displacements. Operator-theoretic bridge, not a claimed new field or RH mechanism.
F669 — Orthogonal `R,Q,P`, `A=R-Q`, `B=Q-P`: nuclearity of `AB` forces `BA` and all six mixed cubic words nuclear; the three channels `A^2B+AB^2`, `ABA+BAB`, `BA^2+B^2A` each have trace zero and sum to `C` (F661's definition). First channel is exactly `[AB,Q]`; the others have its trace by cyclicity (`MixedNuclearSourceCubicConservation`: `mixedNuclearSourceCubicAssociator_conservation`, Lean). Positive survivor: channelwise conservation without commuting projections or compact displacements. Trace-ideal bridge, not an arithmetic source bound or new RH architecture.
F662 — Actual critical profile `psi(y)=exp(-y/2) sum_n mu(n) exp(-n exp(-y))` tends to zero as `y -> -infinity`; fixed-coordinate dilations `psi(y-log t)` therefore vanish as `t -> infinity` by elementary exponential damping. At the opposite, critical end it has exact zeros above every height, yet some fixed positive amplitude is reached arbitrarily far right (`MobiusCriticalProfileReturnSeparation`: `exists_mobiusCriticalProfile_zero_above`, `mobiusCriticalProfile_cofinal_positive_excursions`, Lean). No RH assumption or simple-zero assumption. Corpus interpretation bridge, not a new selection mechanism.
MUST-205 — It must distinguish infinite-source point returns from bounded integer-prefix energy returns: F662 proves genuine critical point returns alongside persistent excursions; `y-log p` observations instead enter Laplace scale `p exp(-y) -> infinity`, not the critical boundary. Neither theorem supplies an upper bound on the moving-cusp integral or `C_N(r)`; any transfer needs a separate quantitative theorem.
F663 — It cannot match the full ordered reciprocal-ordinate singular sequence using bounded two-sided transport of the literal C1 global-mean positive root: that root is nuclear, the target is not (`GammaSewnPluckerNuclearRootTransportNoGo`, Lean). At every fixed positive aperture, the literal regularized Sonin common-source column has singular-prefix sum `O(log N)`, retaining mixed prime words; the target prefix is asymptotic to `log(N+1)^2/(2pi)`. Thus both the stated F2 moment weld and fixed-aperture coupled exact moments are impossible (`SoninRegularizedMomentWeldNoGo`, `SoninRegularizedCoupledMomentNoGo`, Lean). These statements do not exclude all source operators, escaping-aperture or projectively normalized families.
F664 — It cannot mistake ordered ordinates for the full complex divisor: `xiOrderedSignedPrimeOperator` has eigenvalues `+/-1/gamma_n` and is self-adjoint unconditionally; the inspected determinant identification with Xi assumes RH (`XiOrderedPrimeDeterminantNormalForm`). A target-free two-step logarithmic saddle is already trace-class close to this ordinate operator (`RoutePTwoStepWildSaddleTraceClassRelocation`, Lean). The signed Xi/RVM relative difference has ordinary trace exactly zero by paired-sector cancellation (`XiOrderedPrimeRelativeTraceCancellation`, Lean). Trace-class relocation supplies neither determinant equality nor an unsigned escape count.
MUST-206 — It must distinguish a source's insufficient full-spectrum density (F663) from missing horizontal selection (F664): correcting the density alone is already achievable without RH. A proposed relative-completion mechanism must retain horizontal displacement and prove its own arithmetic identification; neither an ordinate-only self-adjoint realization nor its zero signed relative trace supplies that identification.
F665 — It cannot treat unital coefficientwise damping as contraction in the additive Gamma--Hankel energy: for every `r>0`, a real multiplier fixing the coefficient at integer `1` contracts every finite real coefficient vector iff every multiplier is `1` (`GammaHankelAnchoredDiagonalRigidity`: `gammaHankel_unital_diagonal_contractive_iff`, Lean). Each frequency has nonzero overlap with the fixed first frequency. On the actual two-integer Mobius prefix, `mu(n)n^(-t)` strictly increases this energy for every `r,t>0` (`mobius_dirichlet_damping_two_energy_gt`, Lean). Positive survivor: exact identity-only classification. This is a peripheral-contraction bridge, not an RH mechanism; non-diagonal actions, changing the first coefficient, and other norms are outside the classification.
F666 — It cannot bound literal coefficientwise Mobius multiplication by any fixed constant in Gamma--Hankel energy, for any `r>0` (`MobiusGammaHankelMultiplierCollapse`: `RHTower.not_mobius_gammaHankel_multiplier_bounded`, Lean). A prime `p` and multiple of four `p<q<=p+4` give input `e^(-px)-e^(-qx)` with energy at most `(q-p)^2 Gamma(r+2)/(2p)^(r+2)` but output `-e^(-px)` with energy `Gamma(r)/(2p)^r`. Positive survivor: quadratic dipole estimate (`gammaHankelDipole_energy_le`); exact physical realization `v_n=x^((r-1)/2)e^(-nx)` retains every cross term (`norm_sum_gammaLaplaceAtom_sq`).
F667 — It cannot rescue that same Mobius endomorphism by allowing an unbounded closable domain: the atoms `v_(4k)`, `k>=1`, already span densely all physical `L2(0,infinity)` and are all killed by `mu`, while `v_1` is preserved. The graph closure contains the entire horizontal axis and nonzero vertical vector `(0,v_1)` (`dense_gammaSquarefulAtomSpan`, `no_closable_gammaLaplace_mobius_operator`, Lean; module F666). Positive survivor: squareful-atom totality. This obstruction is a moment-determinacy/completion bridge, not a new RH mechanism.
MUST-207 — It must distinguish a bounded grading in coefficient space from a closable endomorphism after additive completion (F666–F667). The defect needs no zero data and cannot by itself diagnose off-line zeros. These all-input operator obstructions do not disprove the prescribed Mobius-prefix return bound, or exclude source-to-output synthesis between different spaces, other norms, or nonlinear formation.
F668 — For every actual Xi zero rho of multiplicity m, the continued visible-coprime mixed-jet matrix through orders (m,m) has only its top corner: J_ij=0 unless i=j=m. Thus B(a,b)=a_m conj(b_m) J_mm; every packet supported in orders <m is annihilated, on or off the line, and the enlarged pairing's left radical is exactly {a:a_m=0} off-line and the whole space on-line (`VisibleCoprimeZetaJetRadical`: `visibleCoprimeZetaJetEntry_eq_corner`, `visibleCoprimeZetaJetPairing_radical_iff`, Lean). Positive survivor: exact radical/one-corner classification; a local analytic bridge, not a new RH mechanism.
MUST-208 — It cannot obtain a contradiction merely by pairing lower-order pole jets with that continued kernel: F668 already forces zero independently of horizontal position. The existing order-(m,m) sign detector (F86a) is outside the lower-jet packet. No interchange with the infinite coprime sum, global pole expansion, moving-cusp upper bound, or RH proof follows; those require separate theorems.

## 2026-09-05 — off-line first moment from one mollified mean square (OFFLINE-MOMENT-001, `3-formalized`)

F659 — [Lean] First-moment reading of the Levinson budget at `λ = 0`: for a bounded real Dirichlet polynomial `Ψ` with `b_1 = 1` and admissible heights `20 ≤ T₁ < T₂`, `2π ∑_{ρ∈[1/2,15/2]×[T₁,T₂]} m_ρ(Re ρ − 1/2) ≤ ½(T₂−T₁)log(Msq/(T₂−T₁)) + C + K(log T₂ + log Mb)` with `Msq ≥ ∫_{T₁}^{T₂}|ζΨ(1/2+it)|²` (`exists_zetaOffLineFirstMoment_le_of_line_meanSquare`; abscissa version `_of_mollified_meanSquare`). The mollifier's zeros only add mass; the pole gauge cancels exactly; the line is reached by continuity of the mean square in the abscissa.
MUST-205 — `(L)` (`∑_{γ≤T}(β−1/2)⁺ = o(T)`, equivalently vanishing log-mean of `|ζ|` on the line) is now pinned between `0` and the Jensen ceiling `½ log(1 + 1/θ)`: `0.5058` with Conrey's `θ = 4/7`, `0.5493` with Levinson's `θ < 1/2` (paper corollary; mean-value theorems not in Lean). Any producer for `(L)` must beat Jensen on the left edge, i.e. control the log-moment `E log|ζΨ|²` of a mollified product below `log E|ζΨ|²`; no mean-value theorem does this, and Farmer's `θ → ∞` conjecture is exactly the statement that the ceiling tends to `0`.
F660 — [Lean] Littlewood's lemma for `ζ` on `[1/2,15/2]×[T₁,T₂]` with explicit-constant edges: `|∫ log|ζ(1/2+it)| − 2π∑ m_ρ(β−1/2)| ≤ C + K log T₂` (`exists_zetaLine_littlewood_edge_budget`); hence the floor `∫ log|ζ(1/2+it)| ≥ −C − K log T₂` and the two-sided sandwich with the mollified mean-square ceiling (`exists_zetaLine_logMean_sandwich`). The `(L)` gate is now a fully two-sided Lean statement whose only non-Lean input is one mean value.
CANNOT-295 — It cannot lower the `(L)` ceiling with mean values alone: mean and variance of `Y = |ζΨ|²/E|ζΨ|²` (the mollified second and fourth moments) never force a positive Jensen gap — a two-point law with mean `1`, any variance `v`, and gap `< ε` exists for every `ε` (`exists_twoPoint_mean_one_variance_jensen_gap_lt`, Lean). Twisted fourth-moment theorems (Hughes–Young, Bettin–Bui–Li–Radziwiłł) are therefore inert for `(L)`; what is needed is an eighth moment, a small-ball/tail law for `ζΨ`, or the conjectural Gaussian limit of `ζΨ − 1` (which would give the ceiling `½E₁(θ) ≈ 0.24`).

## 2026-09-05 — distributional laws for `ζΨ − 1` (MOLL-DEV-001)

F661 — [Lean] The mollified deviation `W_M = ζΨ_M − 1` (linear mollifier of length `M`) has Dirichlet coefficients `Λ(k)/log M` for `1 < k ≤ M` (`mollifiedProductDirichletCoeff_eq_vonMangoldt`): its head is the truncated logarithmic derivative `−(1/log M)(ζ'/ζ)_{≤M}`. The head's critical-line variance is `1/2` independently of the length exponent: `∑_{k≤N}Λ(k)²/k/(log N)² → 1/2` (`tendsto_sum_vonMangoldt_sq_div_div_log_sq`) and the window mean square of the head is within `ε` of `1/2` on every window of length `≥ M²` (`exists_mollifiedDeviationHead_meanSquare_close`). With Conrey's `E|ζΨ|² → 1 + 1/θ` (not Lean), the tail plus cross term carries exactly `1/θ − 1/2`.
F662 — [Lean] Complex-Gaussian log-mean identity: for `W ~ CN(0,σ²)`, `E log|1+W|² = E₁(1/σ²)` in polar form (`complexGaussianLogMeanRadial_eq_expIntegralE1`, via Jensen's circle identity, one integration by parts and `u = r²/σ²`). Under the conjectured law `W_M → CN(0,1/θ)` this gives `E log|ζΨ|² → E₁(θ)` and the `(L)` ceiling `½E₁(4/7) ≈ 0.241` in place of Jensen's `0.506`; under RH it also gives the Möbius mollifier's own log-mean `E log|Ψ_M|² → E₁(θ) > 0`.
MUST-206 — The Gaussian law for `ζΨ − 1` must pass the fourth-moment test `lim E|ζΨ|⁴ = 1 + 4/θ + 2/θ²` against the Hughes–Young / Bettin–Bui–Li–Radziwiłł mollified fourth moment; its head is provably Gaussian only to order `2⌊1/θ⌋` (large primes carry the variance), and its tail is a long Dirichlet polynomial with Selberg-sieve coefficients beyond current mean-value technology. Any proof of the log-moment consequence must supply a small-ball or tail law, not moments (CANNOT-295).
F674 — [Lean] Fixed-frequency rank-one theta coefficient sewing has exactly normalized nonvanishing amplitudes `(a,b)=(1,±1)`, zero all-one normalized tangent, constant all-one-based formal amplitude families, and rates `q(n)=n²q(1)`, `h(n)=(n+1/2)²q(1)` (`HTGeometry.ThetaLatticeSewingRigidity`). Independently, `ThetaLatticeAddition.thetaLattice_addition` now proves the analytic identity `θ(z+w,τ)θ(z-w,τ)=θ(2z,2τ)θ(2w,2τ)+θh(2z,2τ)θh(2w,2τ)` for arbitrary complex `z,w` and upper-half-plane `τ`; `θh` is the half-integer series. Proof: explicit bijection of `Z²` with its two parity sectors, Gaussian atom identities, absolute convergence; `thetaLattice_duplication` specializes `w=0`. Positive survivor: actual nonlinear source equation plus separate coefficient/rate classification. Classical theta/parallelogram mathematics; Fourier-coefficient extraction and the Xi-zero-to-exact-arithmetic-deformation map remain unproved. No RH selection follows.
CANNOT-297 — It cannot substitute rigidity for a connection to Xi: a deformation space with zero tangent contains no nonzero Xi deformation to obstruct. For fixed integer/half-integer theta frequencies, normalized time-independent amplitudes are already rigid; allowing Gaussian heat rates adds only a common scale. This excludes that choice of deformation space, not all nonlinear arithmetic laws or time-dependent families. Evidence: `HTGeometry.ThetaLatticeSewingRigidity`, F674.
MUST-209 — It must connect actual Xi zeros to exact solutions of an independently specified arithmetic system, proving which integer operations and boundary conditions survive the deformation. Different mechanisms may cover different zeros, or one collective mechanism may cover the spectrum; either needs exhaustive coverage and control of cancellation between sectors. An algebraic tangent or nonlinear continuation of a zero is not that preservation theorem. At second order, `DE(u0)u''+D²E(u0)[v,v]=0`; forcing the quadratic term to vanish requires a proved operation annihilating the first term, with boundary/domain conditions checked. Evidence: exact source/Xi identification in `HedenmalmThetaSourceSpectrumExact`; multiplicity-preserving continuation, without arithmetic preservation or confinement, in `ThetaCuspHawkingNonlinearDivisorTransportEndpoint`.
MUST-210 — It must distinguish dynamics generating the arithmetic source from dynamics whose deformation modes are Xi zeros. The literal integer theta sum already follows a nonlinear polynomial ODE; Xi is the Fourier transform of an explicit observable along that trajectory. This is an exact source identity, not an identification of Xi zeros with solutions of the linearized ODE or with exact deformations. Finding another nonlinear source equation alone does not fill that gap. Evidence: `hasDerivAt_thetaCuspModularODEState`, `ofReal_thetaCuspFullSource_eq_completedThetaProfile_mul_modularFactor` in `PrimeArchThetaModularDifferentialClosure`; `thetaCuspFourierLaplace_eq_XiC_all` in `HedenmalmThetaSourceSpectrumExact` (Lean).
CANNOT-298 — It cannot infer an actual Xi zero from an exponentially small mode residual or an exponentially large source resolvent: both occur for the literal theta source outside the unconditional Xi zero strip. Unit approximate modes have exponentially small adjoint residual while their reciprocal parameters stay at least an inverse-quadratic distance from every true spectral point. A numerical or perturbative interaction mechanism therefore needs exact spectral identification or a quantitative error-to-spectrum theorem valid in its chosen norm; small residual alone is insufficient. Evidence: `HedenmalmThetaExteriorPseudospectralSeparation.thetaExterior_pseudospectral_separation`, `exists_exponential_thetaComplexResolvent_lower` (Lean); these bounds do not prohibit every approximation scheme or constrain arithmetic-preserving perturbations.
F663 — [Lean] Head fourth moment: `(1/(T₂−T₁))∫|H_M(1/2+it)|⁴ → 1/2 = 2(1/2)²` on windows with `8M²(1+log M²) ≤ (ε/4)(T₂−T₁)` (`exists_head_fourthMoment_close`; θ < 1/2); coefficient energy of `H_M²` tends to `1/2` (`tendsto_headFourthEnergy`) via the prime-power orientation classification (`primePow_quad_classification`) and `O(1/log⁴M)` one-prime exceptions. First rigorous Gaussian-moment law for `ζΨ − 1`.
CANNOT-296 — [numerical, pod 2026-09-05; not Lean] The full deviation `ζΨ − 1` is not `CN(0,1/θ)`: at `T = 10⁶` its kurtosis is `2.55/2.04/1.77` at `θ = 0.3/0.4/0.5` and `E log|ζΨ|² ≈ 0` at all three `θ` (Gaussian would give `E₁ ≈ 0.45–0.73`); the head is Gaussian (`kurt 1.96–1.99`, variance `≈ 1/2`) as proven. The mollified product is numerically an outer function: `E log|ζΨ|² ≈ 0 = E log|ζ|² + E log|Ψ|²`, i.e. `(L)` plus vanishing right-zero mass of the mollifier. Do not use `½E₁(θ)` as a target.
MUST-207 — The `(L)` residue is the outer law `E log|ζΨ_M(1/2+it)|² → 0` (equivalently `∑_{ζΨ(ρ)=0, β>1/2}(β−1/2) = o(T)`), a joint statement about `ζ`'s off-line zeros and the mollifier's own zeros right of the line; its head part is Gaussian and carries exactly half a unit of variance, its tail is a long sieve-weighted Dirichlet polynomial. Any producer must control the tail's small values, not its moments.
F664 — [ratios recipe + symbolic residues; not Lean] Mollified fourth moment `c₄(θ) = lim (1/T)∫_T^{2T}|ζΨ_M|⁴ = 1 + 8/(3θ) + 2/θ² + 2/(3θ³)` for the linear mollifier of length `T^θ` (`2-fully-proven/computations/mollified-fourth-moment-recipe/`); engine validated on Conrey's `1+1/θ`, the unmollified `L⁴/12`, and the rigorous head moments `1/2, 1/2, 1/12, 1/72` (Lean-proven; the recipe reproduces them only with closure sides decided in the regime θ<1/2). Not `CN(0,1/θ)`'s `1 + 4/θ + 2/θ²`; the `1/θ³` term is super-Gaussian. Numerics at `T ≤ 10⁷` rise toward it (ratio `2.11 → 2.185` at θ = 1/2).
MUST-208 — Any distributional law for `ζΨ − 1` must reproduce `c₄(θ) = 1 + 8/(3θ) + 2/θ² + 2/(3θ³)` together with `E log|ζΨ|² → 0` (outer identity) and the Gaussian head `CN(0,1/2)`; the tail `Tail_M = W_M − H_M` must carry the `(2/3)/θ³` fourth-moment growth and the dips at the zeros (`P(|ζΨ|² < ε) ≍ √ε/(πθ)`).
F665 — [Lean] Outer decomposition law for the mollified product: `ℓ_{ζΨ} = ℓ_ζ + ℓ_Ψ` on the line (`integral_log_norm_zeta_mul_edPoly_line`); mollifier Littlewood floor `ℓ_Ψ ≥ −(C + K log Mb)` uniformly in the heights (`exists_edPoly_line_logMean_floor`); producer direction `ℓ_ζ ≤ ℓ_{ζΨ} + C + K log Mb` (`exists_zetaLine_logMean_le_mollifiedProduct_logMean`): an outer law `ℓ_{ζΨ} = o(T)` for any bounded unit-head mollifier implies `(L)`.
F666 — [Lean] Torus upper law for Dirichlet polynomials: continuous Bohr transfer (`tendsto_contMoment_average_steinhaus`, Cesàro and dyadic windows) and `(1/T)∫_T^{2T} log|F| ≤ ½E_χ log max(|F_χ|², ε²) + η` eventually (`eventually_window_logMean_dpoly_le`); receiver direction for the linear mollifier `ℓ_{ζΨ_M}(T,2T) ≤ ℓ_ζ(T,2T) + T(J_M(ε) + η)` (`eventually_window_logMean_zeta_mul_linearMollifier_le`), `J_M(ε) = linearMollifierTorusLogMean M ε`.
CANNOT-297 — [numerical + heuristic; not Lean] The mollifier's right-zero mass is the torus Jensen mass `J_M = E_χ log|∑_{h≤M}μ(h)P(h)χ(h)h^{-1/2}|²`: for the linear mollifier `J_M ≤ 0.005` up to `M = 10⁴` (torus Monte Carlo) and `ℓ_Ψ(1/2) ≈ 0.003` at `T = 10⁵–10⁶`; for the sharp Möbius sum `J_M = 0.34, 0.43, 0.50` at `M = 10², 10³, 10⁴` (≍ log log M). `J_M > 0` strictly for large `M` (real diagonal zero at `r* ≈ log M/(2√M)`, conditional on `∑_{h≤M}μ(h)P(h)/√h → 1/ζ(1/2) < 0`), but exponentially small. The outer law `ℓ_{ζΨ_M} → 0` therefore holds iff `(L)` and `J_M → 0`; do not state it without the `J_M` correction.
MUST-209 — `(L) ⟺ ∀a>0: N(1/2 + a/log T, T) = o(T log T)` (fixed multiples of the mean spacing off the line carry a vanishing proportion of zeros); Selberg's density gives only `e^{−a/4}·T log T`. Any producer must control zeros at the mean-spacing scale; the mollified log-mean `ℓ_{ζΨ}` is its analytic avatar, and the mollifier's part is the deterministic torus quantity `J_M`.
MUST-210 — To turn the receiver direction of the outer law into the equivalence `(L) ⟺ lim ℓ_{ζΨ_M}(T,2T)/T = J_M`, prove the lower torus law `liminf ℓ_Ψ/T ≥ J_M` (uniform integrability of `log⁻|Ψ|` on the line via Poisson–Jensen with the `≪_M T` strip zeros). The producer direction needs nothing more.
F667 — [Lean] Small values of a mollifier on the line: `∫_{T₁}^{T₂} max(log ε − log|Ψ(1/2+it)|, 0) ≤ (C₁(T₂−T₁) + C₂(1+|T₁|+|T₂|))/log(1/ε)` (`exists_line_smallValues_bound`), via the interior lower bound `log|Ψ(w)| ≥ −C + ∑ m_a log|(w−c₀)−a|` (`exists_interior_log_lower_bound`; corpus cofactor factorization + minimum modulus) and the linear strip zero count. Lower torus law `(1/T)∫_T^{2T} log|Ψ_M| ≥ J_M(ε) − η − D_M/log(1/ε)` (`exists_eventually_window_logMean_linearMollifier_ge`).
F668 — [Lean] **`(L) ⟺ outer law for ζΨ_M`**: `zetaLine_logMean_le_iff_mollifiedProduct_logMean_le` (every `M > 1`), squeeze `exists_mollifiedProduct_logMean_squeeze_of_L`, ζ floor at all heights `exists_zetaLine_logMean_floor_all_heights`. The mollified log-mean converges to the torus Jensen mass `J_M` iff `∑(β−1/2)⁺ = o(T)`.
CANNOT-298 — [structural] The fixed-`M` equivalence `(L) ⟺ ℓ_{ζΨ_M}/T → J_M` (F668) is the decomposition `ℓ_{ζΨ_M} = ℓ_ζ + ℓ_{Ψ_M}` plus the two-sided torus law for the single Dirichlet polynomial `Ψ_M`; it carries no information about `ζ` beyond `(L)` itself. Do not cite it as progress on `(L)`; its content is the window-uniform Jessen–Tornehave law with explicit constants.
MUST-211 — The `(L)`-productive outer law is at `M = T^θ`: `ℓ_{ζΨ_{T^θ}}(T)/T ≤ J_{T^θ}(ε) + o(1)` would give `(L)`. Its torus side needs the log-mean of `Ψ_{T^θ}` uniformly in `M`: the small-values estimate is already uniform (`(log M)^4 T`), the missing piece is an effective Bohr transfer for `log max(|Ψ|², ε²)` (Weierstrass forces degree `≫ M ε^{-2}`, far beyond the mean-value range). Any producer must replace Weierstrass by a structural argument (e.g. Littlewood's identity on the torus side, or the peeling identity `E_z log|A + zB| = log max(|A|,|B|)` transported to the flow).
F669 — [Lean] Two-sided window torus law for every real bounded unit-head Dirichlet polynomial (`exists_window_logMean_torus_twoSided`): `J(ε) − η − D/log(1/ε) ≤ (1/T)∫_T^{2T} log|Ψ(1/2+it)| ≤ J(ε) + η` eventually, `J(ε) = ½E_χ log max(|∑ Re(b_n)χ(n)n^{-1/2}|², ε²)`.
F670 — [Lean] Off-line first moment with the on-line count retained (`exists_zetaOffLineFirstMoment_add_lineCount_le_of_mollified_meanSquare`): `2π[∑ m_ρ(Re ρ−1/2) + (1/2−σ₀)∑ m_ρ] ≤ ½(T₂−T₁)log(Msq/(T₂−T₁)) + C + K(log T₂+log Mb)`. Paper corollary on the Levinson line with Young/Conrey's `c(R,θ)` and `∑ m_ρ ≥ (1+κ)N/2`: `∑(β−1/2)⁺ ≤ (T/4π)[log c(R,θ) − (1+κ)R] + o(T)`, numerically `0.0714 T` (θ=4/7, κ=2/5, R=0.6) against Jensen's `0.0805 T` — the best explicit `(L)` constant in the corpus.
CANNOT-299 — `(L)` is not reachable by moment information: any finite set of moments of `ζΨ`, together with the Gaussian head and its orthogonality to the tail, is satisfied by the Jensen-tight coupling `W = √(1+σ²)e^{iα} − 1`, `α` partially locked to `arg H`; dip lower bounds from on-line zeros are unconditional only up to zero clustering (Fujii's pair count allows every zero a neighbour within `1/log T`); the shifted-line count improves the constant by `(1+κ)R` but `log c(R,θ) ≥ 2R` keeps it positive. `(L) ⟺ p_T(a) → 0` for fixed `a` is beyond Selberg-type density (`e^{−a/4}`).
F671 — [Lean] Zero density at scale `Δ` from the mollified first moment (`exists_zetaZeroDensity_scale_le_of_mollified_meanSquare`): `2π[Δ·N_{≥1/2+Δ} + (1/2−σ₀)N_{≥1/2}] ≤ ½(T₂−T₁)log(Msq/(T₂−T₁)) + C + K(log T₂+log Mb)`; Jensen loss `E₁(x) ≤ e^{−x}/x` (`expIntegralE1_le_exp_neg_div`). Paper: `p_T(a) ≤ 0.449/a` (Levinson line) and `≲ 0.38/(a−1)²` (right-shifted linear mollifier); exponential `e^{−2θa}` needs the sharp-head mollifier — Conrey's `8/7 = 2·4/7`.
CANNOT-300 — `p_T(a) → 0` at fixed `a` is not reachable by any mean-square (Jensen) density argument with a mollifier of fixed length `T^θ`: the charge is `log(1+h)` with `h = E|ζG(1/2+a/L)|² − 1` a fixed positive constant, while the true log-mean is `≍ h e^{−1/h}`; the density exponent at the mean-spacing scale equals `2θ`, so the only lever is the mollifier length (twisted second moment beyond `θ = 4/7`), the same wall as `(L)`, `κ → 1`, and Farmer's conjecture.

MUST-212 — The explicit Conrey-exponent density at the mean-spacing scale has exactly one external input: Conrey's mollified mean square on the right-shifted line `σ₀ = 1/2 + a'/log T`, length `T^θ` (`θ < 4/7`), with the sharp-head taper `P_ε(x) = min(1, x/ε)` and the shifted weight `h^{−a'/L}` (both absorbed into a Lipschitz `P`); its main term is `c(a',θ,ε) = 1 + (e^{2a'εθ}−1)(1−e^{−2a'})e^{−2a'θ}/(4a'²ε²θ²)`. Everything downstream is Lean (F675). Any improvement of the exponent `8/7` must lengthen the mollifier; no choice of `P` on `θ < 4/7` changes `2θ`.

F675 — [Lean] Zero density at scale `Δ` on any abscissa `1/4 ≤ σ₀ < 2` (`exists_zetaZeroDensity_scale_le_of_mollified_meanSquare_wide`; budget `exists_levinson_mollified_budget_le_wide`, the corpus proof with `σ₀ < 1/2` widened — that hypothesis was never used): `2π·Δ·N_{≥σ₀+Δ}(T₁,T₂) ≤ ½(T₂−T₁)log(Msq/(T₂−T₁)) + C + K(log T₂ + log Mb)`. With `σ₀ = 1/2 + a'/L`, `Δ = (a−a')/L` and MUST-212's `Msq`: `p_T(a) ≤ inf_{a'<a, ε} log c(a',θ,ε)/(2(a−a')) + o(1)`, numerically `p_T(a) ≤ (2.40 + o(1)) e^{−8a/7}` at `θ → 4/7` (optimum `a' ≈ a − 0.9`, `ε ≈ 1.2/a`; e.g. `a = 5`: `7.9·10⁻³` vs Chebyshev `0.449/a = 9.0·10⁻²`, vs linear taper `1.9·10⁻²`). This is Conrey's `N(σ,T) ≪ T^{1−(8/7)(σ−1/2)}` made explicit at `σ − 1/2 = a/log T`, and it is the sharpest unconditional statement about `p_T(a)` the corpus owns; `p_T(a) → 0` at fixed `a` (CANNOT-300) remains out of reach.

## 2026-09-05 — coprime deletion multiplication fibres (CBMF-001)

F679 — [Lean] Two zero-marginal arithmetic sources can leave a nonzero interaction under multiplication-fibre stabilization. The literal dyadic–triadic deletion grid has every row and column sum `0`; its source-retaining odometer records one opposite-sign unit cancellation in the product-`2` fibre, while collapsing `(m,n)` by `mn` changes squared integer mass from `12` to `10`, leaving exact defect `2` (`coprimeBlockMultiplicationFiber_closed`).
CANNOT-304 — An origin-labelled block moment is not intrinsic arithmetic orientation. For the literal `2×3` pointwise deletion carrier, cyclic origin change alters the integer first moment, while the apparent orientation charge is `0` in `ZMod 6` (`coprimeBlockMomentOrientation_noGo`). Do not use such moments or their Möbius–Laplace derivative analogue as selectors.
CBMF-002 — [Lean] Cannot infer a new arithmetic constraint merely by recording how many opposite-sign pairs were cancelled. Such a record can be reconstructed from familiar coefficients even when the residual signed value is zero. For the literal dyadic–triadic source, every fixed multiplication fibre stabilizes, and its full cancellation count equals eight explicit shifted divisor counts; the corresponding Dirichlet series is a fixed polynomial times `ζ²`. The coefficient classification and stabilization are closed in `RHTower.CoprimeFiberStabilization.coprimeFiberStabilization_closed`; proof and precise scope: `3-formalized/coprime-fibre-stabilization-collapse.md`. This retires the specified count, not every possible labelled-history construction.

CANNOT-301 — The peeling identity `E_z log|A + zB| = log max(|A|,|B|)` (corpus: `circleAverage_log_norm_const_add_mul`) cannot be transported from the Steinhaus torus to the flow `t ↦ (p^{-it})_p` for a mollifier `Ψ_{T^θ}`: transport would freeze the cofactors `A_p, B_p` while `p^{-it}` completes a period, but their spectra reach `log M ≥ log p` for every prime `p | n ≤ M` (no separation of scales), and the distributional transfer at length `T^θ` reaches only moments of order `< 1/θ` (the Montgomery–Vaughan diagonal range); beyond it the flow carries the swap terms (`c₄(θ)`), and the resonant modes `n/(n+1)` with `n ≤ T` smooth have positive density `ρ(1/θ)`. A uniform torus law for `log|Ψ_{T^θ}|` is a Steinhaus transfer of a log-mean at length `T^θ`, the same kind of statement as `(L)` (transfer for `log|ζ|` at length `T`). MUST-211 was misdiagnosed: the lower torus law is free up to `J_M` (`exists_edPoly_line_logMean_floor` is `T`-free), the upper one is not needed, and the `(L)`-productive statement is the mollified upper bound `ℓ_{ζΨ_{T^θ}}/T ≤ o(1)`, which equals `(L)` plus `RZM_flow(Ψ_{T^θ}) = o(T)` — strictly stronger than `(L)`. Verdict on the route: BRIDGE between two transfer statements; positive survivors F676, F677.

F676 — [Lean] The credited ceiling (`exists_zetaOffLineFirstMoment_add_mollifierZeroMass_le_of_mollified_meanSquare`): `2π[Σ_ζ m_ρ(Re ρ − ½) + Σ_Ψ m_w(Re w − ½)] ≤ ½(T₂−T₁)log(Msq/(T₂−T₁)) + C + K(log T₂ + log Mb)` — the mollifier's own right zeros, discarded by the corpus ceiling, are a free credit (`analyticOrderAt_mul`). Littlewood for `Ψ` in the upper direction (`exists_edPoly_line_logMean_le_zeroMass`: `∫log‖Ψ(½+it)‖ ≤ 2π·RZM(Ψ) + C + K log Mb`, `T`-free, so the mollifier's line log-mean *is* its right-zero mass up to `O(log Mb)`) gives the log-mean-credited ceiling (`exists_zetaOffLineFirstMoment_add_mollifierLogMean_le_of_mollified_meanSquare`): `2πΣ_ζ m_ρ(Re ρ−½) + ∫_{T₁}^{T₂} log‖Ψ(½+it)‖ ≤ budget`. Exact criterion exposed: `(L)` follows from any family with `½ log E_flow|ζΨ|² − ℓ_Ψ/T → 0`, i.e. a vanishing flow Jensen gap of `ζΨ`.

F677 — [Lean] The Steinhaus Jensen floor (`torusJensenFloor`, `SteinhausTorusJensenFloor.lean`): for every continuous `Ψ` of the first `k₀` phases, radii `0 ≤ r_j < 1` on `k₀+m` phases, `ε > 0`: `2J_ε(Ψ) + Σ_{j≥k₀} log(1−r_j²)⁻¹ ≤ log(E‖E_rΨ‖² + ε²B²∏_{j≥k₀}(1−r_j²)⁻¹)`; ingredients: factorization of the torus mean square over the large coordinates (`torusAverage_normSq_eulerAmp_restrict`, Poisson integral `⨍‖1−rz‖⁻² = (1−r²)⁻¹`), Jensen for the torus average (`torusAverage_log_max_le`), and `torusAverage_log_norm_eulerProduct`. With `r_j = p_j^{-1/2}`: in the Steinhaus model `½ log E|ζΨ|² − J(Ψ) ≥ ½Σ_{M<p≤T} log(1−1/p)⁻¹ ≈ ½ log(1/θ)` for every mollifier of the primes `≤ M = T^θ` — the credited ceiling is floored by the large-prime energy, with equality iff `|ζ_{≤M}Ψ|` is a.s. constant; at `θ = 4/7` the floor is `0.28` against the present Jensen constant `0.506`, so the credit can gain at most `½ log(1+θ) = 0.226` and the linear mollifier (`J_M ≈ 0.005`) gains nothing. The log-mean/mean-square method with full right-zero credit reaches `(L)` only as `θ → 1`: the same wall as `κ → 1` and Farmer, now with a structural cause (independence of the primes in `(M, T]`).

MUST-213 — Any `(L)` producer in the mollified-product family must make the flow Jensen gap of `ζΨ_{T^θ}` vanish; in the Steinhaus model this gap is at least the large-prime energy `½Σ_{M<p≤T} 1/p` (F677) for every `Ψ` of the primes `≤ M`, so either the mollifier length reaches `T^{1−o(1)}` (the twisted-moment wall) or the producer must use the non-Steinhaus arithmetic of the flow — the swap terms themselves — as a positive input rather than an error term.

CANNOT-302 — The swap terms cannot be made a positive input through moments: no positive moment of `|ζΨ|` (the fourth moment `c₄(θ)` of the recipe engine included) can sharpen the Jensen ceiling `E log|ζΨ|² ≤ log E|ζΨ|²`. For every mean `m₁ > 0`, every second moment `m₁² + v`, and every `δ > 0`, a two-point law (mass `1−p` at `m₁ − pd`, mass `p` at `m₁ + (1−p)d`, `d = √(v/(p(1−p)))`, `p → 0`) has exactly these moments and log-mean in `[log m₁ − δ, log m₁]` (`exists_twoPoint_logMean_ge`, Lean, F678): Jensen is saturated by rare large values, and Lyapunov makes higher moments strictly worse. The swap terms therefore enter the ceiling only through the mean square `c(θ) = 1 + 1/θ`, where flow and torus already agree. The flow Jensen gap is exactly `½ log c(θ) − (2π/T)[Σ_ζ(β−½)⁺ + Σ_Ψ(β−½)⁺] + O(log T/T)` (outer decomposition + Littlewood for `ζ` and for `Ψ`, F676), so it lies below the torus floor `½ log(1/θ)` iff the total right-zero mass of `ζΨ` exceeds `½ log(1+θ)·T/2π` (`0.226·T/2π` at `θ = 4/7`); the corpus numerics (`E log|ζΨ|² ≈ 0`) put that mass near `0`. Only lower-tail information (small values of `ζΨ` on the line, i.e. Gonek-type negative moments of `ζ'` at zeros, or fractional negative moments of `ζΨ`) can lower the gap; positive moments never can.

F678 — [Lean] Jensen saturation under a second-moment constraint (`JensenSecondMomentSaturation.lean`): `exists_twoPoint_logMean_ge` — `∀ m₁ v δ > 0, ∃ p a b, 0<p<1, 0<a, 0<b, (1−p)a + pb = m₁, (1−p)a² + pb² = m₁² + v, log m₁ − δ ≤ (1−p) log a + p log b ≤ log m₁`; with `twoPoint_moments`, `twoPoint_logMean_le` (Jensen from `strictConcaveOn_log_Ioi`), `neg_two_mul_le_log_one_sub`. The sup of a log-mean over laws with prescribed first two moments is the Jensen value `log m₁`.

CANNOT-303 — The lower tail of `|ζΨ|` on the critical line is not an `(L)` lever. (i) It cannot "pin the Jensen gap from below": `E log|ζΨ|² ≥ −O(log T/T)` is Littlewood's identity and is sharp. (ii) The one thing the lower tail gives is the *local Jensen deficit*: every on-line zero of `ζ` forces a dip that Jensen ignores; Poisson–Jensen on discs of radius `a/log T` centred on the line, averaged over the centre, gives the exact unconditional bound `Σ(β−½)⁺ ≤ (T/4π)[log C̄(a,θ) − κ a (π²/2 − 2)/(2π)]`, where `C̄(a,θ) = (1/4π)∫₀^{2π} w(φ) c_fix(a cos φ, θ) dφ` is the mean square of `ζΨ` on the circle weighted by the Poisson line weight `w(φ) = π|cos φ| − 2 + sin φ log((1+sin φ)/(1−sin φ))` (`(1/2π)∫w = 2`), `κ` the on-line proportion, and `π²/2 − 2 = ∫∫ log((1−uv)/|u−v|) du dv` the averaged line Green mass of a central zero (`Σ_{k odd} 1/(k²(k+2)) = π²/16 − 1/4`). At `θ = 4/7`, `κ = 0.4`: `0.0783T` (optimum `a = 0.30`) against Jensen `0.0805T` and the Levinson-line credit `0.0714T`; discs centred on the Levinson line give `0.0769T` — worse than the shift alone, because the symmetric disc cost grows where the left-of-line mean square grows exponentially while the deficit of an off-centre zero decays (`γ(x)/γ(0) = 0.58, 0.29, 0.10, 0.02` at `x = 0.25, 0.5, 0.75, 0.9`). (iii) A *uniform* small-ball estimate `P(|ζΨ| < ε) → 0` would need negative discrete moments `Σ_γ |ζ'(ρ)Ψ(ρ)|^{-1}` (Gonek) and control of zero clustering at scale `1/log T`; neither is unconditional, and clustering only reduces the deficit. Verdict: INSIGNIFICANT as an `(L)` tool; the family is exhausted at `0.0714T` up to per-cent refinements.

MUST-214 — Any producer that uses small values of `ζΨ` on the line must supply either a lower bound for `|ζ'(ρ)Ψ(ρ)|` at a positive proportion of on-line zeros together with a zero-spacing bound at scale `1/log T`, or an asymmetric weight in Littlewood's identity that beats the Levinson shift; the corpus owns neither, and CANNOT-300/301/302/303 close every symmetric-moment refinement.

## 2026-09-05 — Euler-deletion quasi-shuffle scaling (EDQS-001)

F680 — [Lean] A full modulus-`P` Euler-deletion jump block `(1,…,1,1−P)` closes at level one but retains exact diagonal quasi-shuffle bracket `P(P−1)`. For any nonzero finite complex source, chronological `P`-fold replication scales quadratic bracket by `P`, while Euler amplitude `P^(1−s)` scales it by `P^(2−2 Re(s))`; equality of these refinement scales has unique real exponent `Re(s)=1/2` (`eulerDeletionSignatureScaling_closed`, `eulerDilation_sigma_eq_half_of_quadraticRefinement`).
CANNOT-306 — Vanishing scalar endpoint does not identify higher path signatures or brackets. A zeta zero makes every Euler-deletion level-one endpoint vanish, but closed paths may retain arbitrary nontrivial higher signature; treating closure alone as refinement coherence assumes the missing producer.
MUST-215 — Must justify equating two refinement rules before comparing their exponents. Repeating a finite sequence `P` times multiplies the sum of squared jump sizes by `P`; multiplying each jump by `P^(1-s)` multiplies it by `P^(2-2 Re(s))`. Equality for a nonzero sequence forces `Re(s)=1/2`, but a zero total sum does not establish that equality. The arithmetic identification of the two operations is an additional theorem, not a consequence of the exponent calculation.

MIXED-CELL-001 — [Lean] Must keep both the changed cutoff and the variation of weights inside each integer block. Put `S_N=sum_(n=1..N)n^(-s)`, `c_p=p^(1-s)`, and `F_p(k)=S_k-c_p S_floor(k/p)-(1-c_p)Z`, where the centering value `Z` is arbitrary. For `T_p(N)=sum_(k=0..N-1)F_p(k)(k+1)^(-conj(s))`, literal subdivision gives `T_(pq)(pN)=T_p(pN)+|c_p|² T_q(N)+J_(p,q)(N)`. The retained correction is `c_p sum_(k<N)F_q(k)[sum_(r=1..p)(pk+r)^(-conj(s))-p(pk+p)^(-conj(s))]`. Three subdivisions impose the exact law `J_(p,q)(qN)+J_(pq,r)(N)=|c_p|² J_(q,r)(N)+J_(p,qr)(qN)`; they do not impose correction vanishing. Both identities hold for every complex exponent and every `Z`, including zero. Consequently their arithmetic consistency alone does not select zeta zeros or identify the squared-amplitude factor with replication count. Evidence: `DeletionMixedRefinement.mixedPrefix_mul` and `cellCorrection_cocycle` in `EulerDeletionMixedRefinementCarry.lean`.

MIXED-SCALE-001 — [Lean: fixed-modulus decomposition; paper: growing-modulus conclusions] Must distinguish a vanishing zero-dependent coefficient from a vanishing remainder. Let `S_N=sum_(n=1..N)n^(-s)`, `1/2<=sigma=Re(s)<1`, and `T_p=sum_(k>=0)[S_k-p^(1-s)S_floor(k/p)-(1-p^(1-s))zeta(s)](k+1)^(-conj(s))`. Its leading modulus term is `Kp^(2-2 sigma)`, where `K=zeta(2 sigma-1)/(1-conj(s))`; the next oscillatory coefficient is exactly `|zeta(s)|²`. At a critical-line zero, removing the leading term leaves real growth `-(1/2)log p`. At a hypothetical zero with `1/2<sigma<1`, the remaining real part instead tends to `-zeta(2 sigma)/2<0`. Neither remainder vanishes. These terms come from ordinary power-sum boundaries, without a zero-location assumption. Must not count recovery of the coefficient `|zeta(s)|²`, or boundedness after subtracting universal growth, as an additional constraint on a zero's location. The exact fixed-modulus identity, ordinary-cutoff convergence, and absolute convergence of the retained remainder series are Lean (`infiniteMixed_eq_decomposition`, `tendsto_mixedPrefix`, `summable_norm_remainder`). The critical boundary is exactly `-(1/2)log p` (`infiniteMixed_eq_critical`); it must not be replaced by a zeta value at its pole or erased by dropping endpoint terms. The growing-modulus conclusions and `Re W_1` identity in this entry remain paper results; [the decomposition and its formal scope](../euler-deletion-growing-modulus-decomposition.md) distinguish them from the checked equality. This is a [BRIDGE], not an arithmetic vanishing law. This does not prove impossibility of a different arithmetic identity.

MIXED-INVERSE-001 — [Lean] Must retain an arithmetic error that can be recovered exactly from the full family of scales. For `sigma=Re(s)>0`, `s!=1`, put `R_s(n)=sum_(k=1..n)k^(-s)-zeta(s)-n^(1-s)/(1-s)-n^(-s)/2` and `W_p=p^(1-s) sum_(n>=1)n^(-s) conjugate(R_s(pn))`. Every positive cutoff is recovered by the absolutely convergent identity `sum_(p>=1)mu(p) W_(mp)/(mp)=m^(-s) conjugate(R_s(m))`. At a zeta zero, its unit-cutoff value is `1/2-1/(1-conjugate(s))`, with norm greater than `1/2`; hence `sum_(p>=1)|W_p/p|>1/2`. Thus total remainder vanishing cannot describe such a zero. Admission is proved from `|R_s(n)|<=|s(s+1)|/(sigma+1) n^(-sigma-1)`, without assuming Möbius cancellation. Evidence: `infiniteRemainder_moebius_inversion`, `remainder_mass_gt_half_at_zero`; [formal scope](../../3-formalized/euler-deletion-remainder-reconstruction.md).

MIXED-INVERSE-002 — [Lean] Cannot infer an exact noncontracting refinement law from decay alone. If a sequence `f(q)->0` satisfies `f(pq)-f(p)-A f(q)+A f(1)=0` for every positive `q`, with fixed integer `p>1` and `|A|>=1`, then every positive-index value of `f` must be zero: the limit first gives `f(p)=A f(1)`, and iteration gives `f(p^n q)=A^n f(q)`. The arithmetic remainder `W` defined above decays like `p^(-2 sigma)` but has nonzero mass at a zeta zero. Therefore for every zero with `0<sigma<=1`, `s!=1`, and every `p>1`, some positive `q` has `W_(pq)-W_p-p^(2-2 sigma)W_q+p^(2-2 sigma)W_1!=0`. This applies separately to every zero class. It supplies the nonvanishing side of a possible contradiction; it does not prove that a strict-right-only vanishing theorem is impossible. Such a theorem still needs independent arithmetic content. Evidence: `eq_zero_of_decaying_refinement`, `exists_remainder_refinement_ne_zero_at_zero`.

ARITHMETIC-MIN-001 — [Lean] Cannot forbid finite downward excursions of the normalized arithmetic remainder at zeta zeros: the exact arithmetic mean forces them even on the critical line. Define `R_s(n)=sum_(k=1..n)k^(-s)-zeta(s)-n^(1-s)/(1-s)-n^(-s)/2`, `W_p=p^(1-s)sum_(n>=1)n^(-s)conjugate(R_s(pn))`, `u=conjugate(s)`, and `X_p=p Re(mu(p)W_p/[u(u+1)])`. At every zero with `0<Re(s)<1`, the absolutely convergent balance is `sum X_p/p^2=-Re(1/[u(1-u)])/2<0`. Write `S2=sum 1/p^2<=2`. At every critical-line zero of height `t`, some finite positive modulus has `X_p<-S2/[8(t^2+9/4)]`; assuming the opposite contradicts the exact mean `-1/[2(t^2+1/4)]`. Thus a proof by arithmetic classes must explain the retained signed excursions within its classes, rather than assume they are absent. Labeling the least attained negative minimum, with a separate nonattainment label, does give unique exhaustive coverage, but does not exclude off-line zeros in the finite-label classes. Evidence: `tsum_minimumProfile_div_weight_at_zero`, `exists_rightMinimumProfile_below_critical_boundary`, `existsUnique_arithmeticMinimumClass`; [formal scope](../../3-formalized/arithmetic-zero-minimum-classes.md).

ARITHMETIC-MIN-002 — [Lean] Cannot use `Re(zeta(s)/(s(s+1)))=0` alone to identify zeros or exclude off-line points. An exact arithmetic reformulation can still discard a component: for the actual normalized remainder sum `C(s)=sum_(p>=1)mu(p)W_p/[p conjugate(s)(conjugate(s)+1)]`, its zero boundary is `Q(s)=-1/[2 conjugate(s)(1-conjugate(s))]`, and `C-Q=-conjugate(zeta(s)/(s(s+1)))`. At every open-strip zero, every neighborhood contains a nonzero point satisfying `Re(C)=Re(Q)`; any strip zero also forces an off-line nonzero point satisfying that same equality. Analytic openness and the negative real-axis zeta value prove these statements without numerical data or a simplicity assumption. The projected equality already forces a negative weighted profile mean, negative entries, and negative minimum attainment below the decay exponent, so those consequences do not restore the lost component. Must add independent source information beyond this equality before claiming classwise exclusion. The omitted imaginary sum at a zero is `Im(s)(2 Re(s)-1)/(2 |conjugate(s)(1-conjugate(s))|^2)`; writing it down does not force it to vanish. This does not forbid other real-valued constraints or prescribe the global minimum labels of the nonzero witnesses. Evidence: `exists_nearby_nonzero_real_minimum_balance`, `exists_offline_nonzero_real_minimum_balance_of_zero`, `negativeMinimum_attained_of_real_balance`; [formal scope](../../3-formalized/arithmetic-minimum-phase-completeness.md).

ARITHMETIC-MIN-003 — [Lean] Must determine a proposed arithmetic classification's behavior at nonzeros before treating its labels as new zero information. A label can be defined without inspecting the critical line and still encode only a normalization exponent. For the actual ordinary power-sum remainder `R_s(N)=sum_(k=1..N)k^(-s)-zeta(s)-N^(1-s)/(1-s)-N^(-s)/2`, put `W_p=p^(1-s)sum_(n>=1)n^(-s)conjugate(R_s(pn))` and `u=conjugate(s)`. For every `sigma=Re(s)>0`, `s!=1`, the scaled sum satisfies `p^(2 sigma)W_p -> -u sum n^(-2 sigma-1)/12`. Thus the least-negative-minimum labels of `X_p=p Re(mu(p)W_p/[u(u+1)])` and `Y_p=p^(4 sigma-1) Re(mu(p)W_p/[u(u+1)])` are `(positive,0)` for every strict-right parameter and `(0,positive)` for every strict-left parameter, including nonzeros; `0` denotes nonattainment. Critical-line zeros instead have equal positive labels, because their exact arithmetic mean forces a finite value below the limiting lower boundary. Consequently `(0,0)` contains no strip zero. Cannot use this finite/nonattained pattern alone to distinguish zeros from nonzeros in either half-strip. At a strip zero, demanding both labels positive is exactly demanding critical-line location; a proof still needs an independent arithmetic law forcing it. The finite indices, values, and relations between moduli remain data to investigate. Evidence: `tendsto_infiniteRemainder_scaled`, `arithmeticMinimumClass_strict_right`, `arithmeticMinimumClass_strict_left`, `rightMinimum_attained_on_line`, `arithmeticMinimumClass_both_positive_iff`; [formal scope](../../3-formalized/arithmetic-global-minimum-classes.md).


ARITHMETIC-MIN-004 — [Lean] Must distinguish a sum's direction of approach from the sign of its limit. Removing small-prime multiples can force eventual monotonicity without supplying new information about zeros. For `sigma=Re(s)>0`, `s!=1`, define `R_s(n)=sum_(j=1..n)j^(-s)-zeta(s)-n^(1-s)/(1-s)-n^(-s)/2`, `u=conjugate(s)`, `g_s(n)=n^(-s)conjugate(R_s(n))/[u(u+1)]`, and `C_M=sum_(n>=1,gcd(M,n)=1)g_s(n)`. This is exactly the finite Möbius sum `sum_(d|M)mu(d)W_d/[d u(u+1)]`, with `W_d=d^(1-s)sum_(n>=1)n^(-s)conjugate(R_s(dn))`. As primes are removed, `C_(N!)` tends to the unit term `g_s(1)`. At every positive-height parameter, including nonzeros, `n^(2 sigma+1)g_s(n)->-1/[12(u+1)]` has negative imaginary part. Once every small exceptional index is removed, each further new prime strictly increases `Im(C_M)`, which remains strictly below `Im(g_s(1))`. Cannot count this universal late direction as a sign bound on the limit. At a positive-height strip zero, eventual `Im(C_(N!))<=0` is equivalent to `Re(s)<=1/2`, because the unit limit has imaginary part `Im(s)(2 Re(s)-1)/(2|u(1-u)|^2)`. Thus an eventual nonpositive ceiling still needs an independent arithmetic proof; neither reindexing nor late monotonicity provides it. This does not rule out other constraints using finite-prime data. Evidence: `coprimeRemainder_eq_sum_divisors`, `tendsto_coprimeRemainder_factorial`, `eventually_coprimeRemainder_strict_phase`, `eventually_coprimeRemainder_im_nonpos_at_zero_iff`; [exact formal scope](../../3-formalized/arithmetic-prime-sieve-phase.md). The stronger all-cutoff sign and monotonicity candidates are separately [numerically rejected](../../2-fully-proven/computations/arithmetic-prime-sieve-phase/REPORT.md), not Lean counterexamples.


ARITHMETIC-MIN-005 — [Lean] Cannot count mutually recoverable arithmetic records as independent constraints. For the actual ordinary remainder, the entire coprime-sieve record `C_M` and the original Möbius-weighted modulus record `b_m` satisfy both `C_M=sum_(d|M)b_d` and `b_m=sum_(uv=m)mu(u)C_v`, for every positive modulus. The inverse uses only finite divisors. A new coordinate system may help prove an estimate, but it has not added a premise about zeros. Must retain prime-exponent information if an argument needs to recover individual coefficients from these records: for any summable sequence `f`, a nonzero transfer `z delta_a-z delta_b` is invisible to every coprime sum `sum_(gcd(M,n)=1)f(n)` exactly when `a,b` have the same prime divisors. In particular, transferring `z` from index 4 to index 2 preserves every coprime observation, the unit coefficient, and the complete eventual tail; applied to the actual normalized remainder, it preserves its exact first asymptotic coefficient and allows any prescribed coefficient at 2. The sum over multiples of 4 changes by exactly `-z`. Full divisibility tests distinguish every pair of different indices. These auxiliary perturbed sequences are not alternative ordinary zeta remainders and need not obey their finite recurrence or the same pointwise bounds at modified indices. The unit value is not hidden; this does not establish or rule out its missing RH sign law. Evidence: `minimumBalanceTerm_eq_finite_sieve_inverse`, `coefficientTransfer_invisible_iff`, `exists_redistribution_with_prescribed_coefficient`, `coefficientTransfer_divisibility_invisible_iff`, `divisibilityObservation_redistributedRemainder_four`; [formal scope](../../3-formalized/arithmetic-sieve-prime-depth.md).

ARITHMETIC-PHASE-001 — [Lean; constant-speed model] Cannot assume a strictly negative margin survives a change of oscillation speed. For the periodic quadratic `b(x)=(fract(x)^2-fract(x))/2`, Lean proves every prefix `integral_(0..A)b(x)sin(lambda*x) dx` is nonpositive for `0<lambda<2*pi` and `A>=0`. At a complete turn `A=2*pi*K/lambda`, equality holds exactly when A is an integer. Positive whole turns coexist with this prefix law: at `lambda=4*pi/3`, the integral over `[3/2,3]` is strictly positive and restores the earlier negative prefix to zero. Must retain accumulated cancellation and handle these zero-margin endpoints when attempting to replace constant speed by the logarithmic phase of the actual arithmetic remainder. This theorem proves neither that the replacement preserves sign nor any constraint at zeta zeros. Evidence: [formal prefix law and exhaustive equality cases](../../3-formalized/arithmetic-linear-phase-prefix.md), [open logarithmic-clock problem](../arithmetic-log-phase-blocks.md).

ARITHMETIC-PHASE-002 — [Lean; literal finite source] Cannot require every complete oscillation of the arithmetic remainder to have a nonpositive imaginary contribution. Let `b(x)=(fract(x)^2-fract(x))/2`, `s=sigma+i*t`, and retain the original integer anchor in `N^(-s)*integral b(x)*x^(-conjugate(s)-2) dx`. For each fixed `sigma>0`, at arbitrarily large N with `t=(4*pi/3)*N<2*pi*N`, its second complete logarithmic turn, from `N*exp(2*pi/t)` to `N*exp(4*pi/t)`, has strictly positive imaginary part. Must retain cancellation between complete turns. The positive survivor is an exact source limit: after multiplication by `N^(2*sigma+2)`, the segment from `N*exp(a/N)` to `N*exp(b/N)` at `t=lambda*N` converges to `integral_(a..b)b(v)*sin(lambda*v) dv` for fixed `0<=a<=b`. Every fixed complete prefix with a strictly negative limiting value is therefore eventually negative; integer endpoint coincidences have zero limiting margin, whose first-order sign is resolved separately in ARITHMETIC-PHASE-003. Must distinguish this simultaneous growth of height and cutoff from a fixed-height tail estimate or a constraint at the unit cutoff. These heights are not asserted to be zeta zeros. Evidence: [exact source transport, limiting signs, and complete-turn refutation](../../3-formalized/arithmetic-logarithmic-phase-scaling.md).

ARITHMETIC-PHASE-003 — [Lean; literal finite source] Must examine the first signed correction when an exact arithmetic cancellation leaves a zero leading limit. Let `b(x)=(fract(x)^2-fract(x))/2` and `q_h(v)=(exp(h*v)-1)/h`. For each fixed `sigma>=-1`, `0<lambda<2*pi`, and positive integer endpoint m with `lambda*m=2*pi*K`, the actual clock prefix `J_h=integral_(0..m)b(q_h(v))*exp(-(sigma+1)*h*v)*sin(lambda*v) dv` satisfies `J_h/h -> Q<0` as `h->0+`. The exact coefficient is `Q=m*[(1-sigma)/lambda^3+sigma*cos(lambda/2)/(2*lambda^2*sin(lambda/2))-1/(4*lambda*sin(lambda/2)^2)]`; the proof retains the quadratic's slope jumps at every integer. At `h=1/N`, this is exactly the arithmetic remainder prefix after its proved change of variables and positive normalization, with height `t=lambda*N`. Together with the strictly negative leading limits at noninteger endpoints, this gives eventual negativity for every fixed positive number of complete turns. Cannot exchange “each turn count has a sufficient cutoff” with “one cutoff controls every turn count.” Must supply new uniform information for an all-prefix law at a finite cutoff, and an independent arithmetic constraint to reach the unit remainder at arbitrary zero height. Neither is proved by the first correction. Evidence: [exact first variation, exhaustive endpoint coverage, and quantifiers](../../3-formalized/arithmetic-clock-first-variation.md).

ARITHMETIC-CELL-001 — [Lean] Cannot infer the phase of a complete arithmetic remainder by expecting all sufficiently late integer cells to have a common sign. For the literal periodic quadratic `b(x)=(fract(x)^2-fract(x))/2`, let `J(sigma,t;m)=integral_(m..m+1) b(x)x^(-sigma-2)sin(t log x) dx`. At the exact fixed height `t=pi/log(2)`, Lean proves `(-1)^k J(sigma,t;2^k)<0` for every real `sigma` and every natural `k`; both signs occur beyond every cutoff. This is actual source information: for `s=sigma+it`, `sigma>0`, `s!=1`, the complex cell whose imaginary part is `J` equals `[conjugate(R_s(m))-conjugate(R_s(m+1))]/[conjugate(s)(conjugate(s)+1)]`, where `R_s(m)=sum_(j=1..m)j^(-s)-zeta(s)-m^(1-s)/(1-s)-m^(-s)/2`. Finite cell sums retain their endpoint exactly, and ordinary infinite cutoffs recover the initial normalized remainder. Must retain cancellation across cells when attempting a whole-tail phase estimate; the nonpositive periodic quadratic alone does not supply it. The fixed height is not asserted to be a zero, so this result does not exclude other zero-specific laws. The separate proposed bound `Im(n^(-s)conjugate(R_s(n))/[conjugate(s)(conjugate(s)+1)])<0` when `0<t<2*pi*n` remains a numerical lead, not a theorem or RH implication. Evidence and scope: [closed cell law](../../3-formalized/arithmetic-successor-cell-phase.md), [conjecture and Runpod results](../arithmetic-successor-phase-threshold.md).

## 2026-09-05 — Euler-deletion zero landing and second shadow (EDQS-002)

F681 — [Lean] Every positive-real-part zeta zero closes every modulus Euler-deletion Dirichlet path under ordinary chronological cutoffs. The proof uses bounded periodic coefficient sums, exact finite dilation, and pole-cleared analytic uniqueness; it needs no functional equation, reflection, or completed zeta (`eulerDeletionDirichletSum_eq_zero_of_riemannZeta_eq_zero`).
F682 — [Lean] At any hypothetical zeta zero with `Re rho > 1/2`, every nontrivial Euler-deletion path has finite positive diagonal energy and a canonical real chronological second shadow equal to exactly `-energy/2`, hence strictly negative (`eulerDeletionQuadraticEnergy_pos`, `tendsto_re_chronologicalSecondPrefix_eulerDeletion_of_zeta_zero`).
F683 — [Lean] At the same hypothetical zero, the full complex chronological self level and every ordered cross-modulus level converge absolutely under ordinary cutoffs. The self limit is nonzero, and all cross limits obey `H(P,Q)+conjugate(H(Q,P))+E(P,Q)=0` (`eulerDeletionChronologicalSecondLimit_ne_zero`, `eulerDeletionCrossLimits_quasiShuffle_zero`).
F684 — [Lean] Every nonempty finite product of pairwise-coprime deletion channels is the alternating sum `prod_(P∈B)a_P = sum_(empty≠S⊆B)(-1)^(|S|+1)a_(prod S)`. Therefore every positive-half-plane zeta zero closes every such cylinder path under one common chronological cutoff (`prod_blockDeletionCoefficient_eq_alternating`, `tendsto_eulerDeletionCylinder_prefix_of_zeta_zero`).
EDQS-RECON-001 — [Lean] Cannot count exactly reconstructible coordinates as independent source information. For `a_p(n)=1-p[p divides n]` and a finite pairwise-coprime family, its coefficient products and its single product-modulus channels reconstruct each other by explicit alternating subset sums. The reconstruction holds for every finite chronological word, every cutoff, and every choice of conjugated letters. Their simultaneous zero-endpoint conditions are equivalent (`cylinder_orderedStarWord_eq_base`, `base_orderedStarWord_eq_cylinder`, `cylinder_zeroEndpoints_iff_base`). A different coordinate description may help prove a theorem, but its extra coordinates are not extra hypotheses supplied by a zero.
EDQS-RECON-002 — [Lean] Must distinguish finite reconstruction from estimates uniform over growing data. In this reconstruction a subset of size `d` has absolute coefficient sum exactly `2^d-1`; for an ordered word those factors multiply (`coordinate_norm_sum`, `orderedWord_coefficient_norm_sum`). Thus these finite identities alone do not establish a uniformly bounded passage to an infinite family or infinite word length. This quantifies the expansion coefficients, not the attained norm of the arithmetic source.
EDQS-PERIOD-001 — [Lean] Cannot extract a nonzero invariant from complete-period ordered products of zero-average periodic signals with positive pairwise-coprime periods. For every nonempty word, summing products over strictly increasing times through a full product period gives zero; every other prefix is recovered exactly from its cutoff residue. The statement applies to `a_p(n)=1-p[p divides n]` even after independently shifting each signal's starting phase (`sourceWordPrefix_periodic`, `wordPrefix_eq_residue`, `shiftedWordPrefix_complete_period_zero`). This is generic independence of residue coordinates. Multiplying the terms by nonperiodic weights, or using periods sharing a prime factor, falls outside the vanishing theorem.
EDQS-STATIC-001 — [Lean] Cannot treat finite weighted divisibility statistics as unexplained higher arithmetic coupling. With positive integer `n` weighted proportionally to `n^(-alpha)`, `alpha>1`, divisibility by any finite family of positive pairwise-coprime moduli is exactly independent, with probabilities `p^(-alpha)`. Lean computes the weighted sum of every real function of those Boolean bits, not only pairwise moments (`tsum_finite_observable`). For `a_p(n)=1-p[p divides n]`, every nonempty product of distinct coprime channels centered at their actual weighted means has zero weighted sum at every such exponent (`tsum_centered_product_zero`). This covers functions of finitely many divisibility bits at one integer; temporal order between different integers and infinite-family limits remain outside the theorem. The mechanism is classical zeta-distribution independence, not new zero-location information.
EDQS-DOMAIN-001 — [Lean] Cannot use existence of an auxiliary ordered sum to isolate a zero when the sum already exists throughout an open region. For the explicit coefficients `a_P(n)=1-P[P divides n]`, the complex sum over `m<n` of `a_P(m)m^(-s)` times the conjugate of `a_Q(n)n^(-t)` converges under chronological cutoffs whenever both real parts are positive and their sum exceeds one, with no zero assumption. Thus existence of its self limit for `Re(s)>1/2` adds no restriction on zero location (`tendsto_chronologicalCrossPrefix_eulerDeletion_domain`, `tendsto_chronologicalSecondPrefix_eulerDeletion_domain`).
EDQS-ORDER-001 — [Lean] Must retain the changed ordering boundary when replacing integer indices by multiples. The strict condition `m<n` becomes `pm<qn`, with inner cutoff `floor((qn-1)/p)`. Deleting multiples in both coordinates gives four exact contributions, including the term where both coordinates are dilated. Their complete expression equals the original ordered sum for arbitrary inputs; the identity imposes no additional zero-specific condition. Its grouped limit can exist without separate limits of the four contributions (`ordered_deletion_eq_wedges`, `ordered_hermitian_deletion_eq_wedges`, `hermitianDilationCombination_converges`).
ODD-POWER-001 — [Lean] Cannot use square summability of arithmetic coefficients as a uniform bound for repeated multiplication. The odd weights `3^(-sigma),5^(-sigma),...` have finite square sum exactly when `sigma>1/2`. After multiplying finite truncations `k` times and grouping equal integer products, a squared-coefficient bound `C^(2k)` with one finite `C` for every truncation and every `k` exists exactly when `sigma>1`. At a fixed truncation of `r` terms with total weight `A`, the exact coefficient energy lies between `A^(2k)/(k+1)^r` and `A^(2k)`: distinct orderings with the same letter counts reinforce each other. For the literal signed replacement coefficients `b(1)=0`, `b(n)=(-1)^n` for `n>=2`, all contributions to an odd product have the common depth sign or are zero. This constrains coefficient-square estimates, not the complex sum across different products. Evidence: `OddDirichletPowerGrowth.oddEnergy_uniform_exponential_bound_iff`, `half_strip_power_failure`, and `replacement_word_odd_product_sign`; [paper argument and formal scope](../../5-failed/alternating-substitution-collision-growth.md).
CANNOT-307 — Level-one closure and formal commutation of scalar deletion operators cannot determine depth-two coherence. Closed paths with the same zero endpoint can have distinct chronological second levels, while fully expanding a pointwise commuting deletion square yields only a tautology (`closed_endpoint_does_not_determine_chronologicalSecond`).
CANNOT-308 — [numerical, pod 2026-09-05; not Lean] Raw self-area and raw cross-modulus carry are neither universally zero nor sign-definite at the first 12 known zeros for moduli `2,3,5,7`; both signs occur, and no cross logarithmic drift appeared through cutoff `2,000,000`. They cannot serve as a bare positivity/vanishing producer.
CANNOT-309 — Comparing two analytic continuations of one ordered deletion sum cannot produce zero-specific rigidity: agreement on a common absolute-convergence region forces agreement throughout any connected continuation domain. A floor/lattice-wedge reindexing identity is then an identity for every exponent, not an RH selector.
CANNOT-310 — Order-dependent intermediate reset-and-carry states do not suffice when all higher source differences are already flat. If iterated differences depend only on the final winning face, changing prime order supplies no holonomy (`iteratedPrimeDifference_tropicalShellIndicator`).
F685 — [Lean] The finite deletion cylinders are only squarefree multilinear, not a pointwise algebra: `a_P²=(P−1)+(2−P)a_P`; in particular `a_2²=1`, and the first `N` dyadic square coefficients sum to exactly `N` (`blockDeletionCoefficient_sq_eq`, `sum_blockDeletionCoefficient_two_sq`). Repeating a generator destroys bounded-prefix cancellation. Subtracting the constant square part gives only `(2−P)a_P` and kills the dyadic square (`blockDeletionCoefficient_centered_sq_eq`, `blockDeletionCoefficient_two_centered_sq_eq_zero`).
CANNOT-311 — Ordinary chronological deletion channels cannot form a unital pointwise algebra inside the bounded-prefix Abel class. Repeated generators introduce the constant stream; importing that stream through analytic continuation would move zeta continuation into the source and cannot supply source-first refinement coherence.
MUST-216 — Must distinguish closure under products of different coprime channels from closure under arbitrary products. For `a_P(n)=1-P[P divides n]`, the exact square law is `a_P²=(P-1)+(2-P)a_P`. Thus repeating a channel introduces a constant component; in particular `a_2²=1`. A cancellation argument proved only for products of different channels cannot silently use their squares.
F686 — [Lean] Literal modulus multiplication is interleaving, not independent replication: the `PQ` deletion source is the `P` source plus a copy of the `Q` source inserted at multiples of `P` with Euler amplitude. In every square-summable chamber `Re(s)>1/2`, the two legs have strictly negative overlap, so composite energy is strictly below the sum of the two leg energies (`deletionMellinSource_mul_eq_add_inserted`, `tsum_deletionSource_inserted_pair_re_neg`, `deletionMellinSource_composite_energy_strict`).
MEAN-DESCENT-001 — [Lean] Cannot infer critical-line selection from positive mass after removing source weights. For `E_p(s,n)=(1-p[p∣n])n^(-s)`, cancelling the Mellin weight before averaging kills composite interference and retains masses `p−1` and `p(q−1)`, but every finite recovered mass is independent of `s`. The complete dilation factor is `p^(2−2σ)p^(2σ)/p=p` for every `σ`. Must preserve the original weighted charge; other quotients remain unclassified (`EulerDeletionMeanInterferenceDescent`).
F687 — [Lean] Every commutative normed-algebra Euler-deletion development is exactly the exponential of the mapped scalar deletion prefix. At every positive-half-plane zeta zero its limit is therefore the unit (`eulerDeletionDevelopment_eq_exp_map_prefix`, `eulerDeletionDevelopmentLimit_eq_one_of_zeta_zero`).
CANNOT-312 — Centering cannot manufacture a missing quadratic deletion channel: after removal of the constant square part, every same-modulus square is only a scalar multiple of its original level-one channel, and the dyadic centered square is zero.
CANNOT-313 — A source-first deletion refinement cannot replace literal composite interleaving by orthogonal or independent copies. Exact arithmetic forces a nonzero negative interference term; deleting it assumes the missing refinement law.
CANNOT-314 — Scalar and commutative ordered-exponential lifts add no zero-location information beyond level-one deletion closure: they become the unit at every zeta zero in their half-plane of definition.
MUST-217 — Must preserve overlap corrections when measuring a sum of actual signals. Its squared size includes twice the real part of the cross product. Dropping a nonzero cross term changes that measurement. Replacing the two components by independent copies also changes the measured quantity; declaring the correction to vanish in a quotient requires a proved observation map compatible with that quotient. No particular quotient construction is forced by this fact. Must distinguish signed cancellation within components from cancellation between them: a source-derived bound on the sum of component energies still leaves the total interference to control. Concrete arithmetic evidence: the unconditional quadratic diagonal ceiling `RHTower.sum_mobiusDivisorDilationChannel_sq_le_quadratic` in `MobiusDivisorAbelQuadraticDiagonal` does not assert the required signed cross-term bound.

F688 — [Lean] Coprime deletion insertion has an exact squarefree grading:
`insert_P(a_Q)=a_Q-a_Pa_Q`. On one complete product block, the singleton grade `a_Q` and interaction
grade `a_Pa_Q` are orthogonal for uniform counting, and the insertion energy is exactly `P` times
the dense `Q`-channel energy (`deletionFactorizationInsertion_eq_cofactor_of_coprime`,
`sum_single_mul_interaction_product_block_eq_zero`,
`deletionFactorizationInsertion_uniform_replication_scale`). This realizes arithmetic replication
without independent copies, but only in the unweighted source form.

F689 — [Lean] The actual Mellin/Dirichlet weight destroys that uniform grade orthogonality. For
`alpha>1` and coprime `P,Q>1`, the grade-one/grade-two cross term is exactly
`Z(alpha)(1-P P^(-alpha))(1+Q(Q-2)Q^(-alpha))` and is strictly positive
(`deletionFactorizationGradeCross_eq_of_coprime`,
`deletionFactorizationGradeCross_pos_of_coprime`). Thus a static weighted associated grade cannot
declare literal interference zero in the quadratic convergence chamber.

F690 — [Lean] Removing a prescribed Mellin weight before arithmetic averaging erases its exponent:
the recovered composite interference has mean zero and the dilation/density factors reduce to
`P^(2-2 sigma)P^(2 sigma)/P=P` for every `sigma` (`recovered_interference_zero`,
`recovered_dilation_factor`). Any scale identity proved only after exact unweighting is
horizontal-location blind.

CANNOT-315 — A critical-exponent selector cannot come from uniform coefficient grading or from
unweighting followed by arithmetic mean: both recover the same replication factor for every
exponent. Nor can it call the weighted interaction a boundary without constructing a boundary map,
because that interaction is strictly positive wherever its quadratic sum converges.

MUST-218 — Must retain whatever dependence on an exponent is supposed to determine that exponent.
When the underlying coefficients are fixed and the exponent enters only through a prescribed
weight, removing that weight before averaging removes the exponent dependence. Such an identity
alone cannot select one horizontal location.
The existence of a different, selective comparison remains unproved; this does not force a unique
type of replacement mechanism.

MDFGT-SCHEDULE-001 — [Lean] Must retain diagonal charge when changing summation order. If closed-prefix and jump norms decay as `(n+1)^(-sigma)`, `sigma>1/2`, every row-stabilizing moving cutoff with `K_N(n)+1>=c(n+1)` for fixed `c>0` preserves its ordered limit. No upper cutoff bound is needed. For literal integer-deletion singleton/interaction signals, inclusive-minus-strict order retains the strictly positive original Mellin charge even at a hypothetical right-half zero (`source_schedule_boundary`, `canonical_source_boundary`). Cofinal schedule independence therefore does not supply annihilation; collapsing-ratio and higher-index constructions are not classified.
WORD-CARRY-001 — [Lean] Cannot treat a longer conditional sum as a new anomaly without evaluating its boundary. At a hypothetical right-half zeta zero, every finite mixed-label/conjugation word of literal integer-deletion jumps converges and has an absolutely summable latest-letter formula (`source_word_normal_form`). Its terminal factor is a vanishing single-letter prefix times a convergent shorter word. This closes the natural middle-index regrouping of three letters, not higher-word vanishing, bounds uniform in length, or associativity of a different arithmetic-label operation.

FULL-ENERGY-001 — [Lean] Must distinguish conservation of a complete observable from vanishing of one selected component. For literal integer deletion, full quadratic energy is factorization-flat coefficient by coefficient, while omitted square terms carry exactly the selected component's nonzero curvature (`omittedEnergy_curvature_eq`). Full-source associativity therefore does not itself select a horizontal zero location. Any argument discarding those terms needs a separate source law; non-quadratic and zero-specific laws remain unclassified.

CRITICAL-CHARGE-001 — [Lean] Cannot transfer source-sum vanishing through conjugate multiplication without a new law. At a genuine critical-line zeta zero, one fixed integer coefficient stream has ordered Mellin sum zero but its literal Hermitian pairing has limit `-8 log 2` (`exists_actual_zero_with_different_source_limits`). Pairing changes the exponent from `rho` to `rho+conjugate(rho)`. This disproves unrestricted zero-fibre annihilation of that charge, not a law confined to `Re(rho)>1/2`; ordered boundary convergence cannot be replaced by an unproved unordered sum.

F691 — [Lean] Cofactor insertion is a flat multiplicative action before chronological summation:
`I_P(I_Q x)=I_(PQ)x=I_Q(I_P x)` for every coefficient stream. Nested scalar cutoffs are equally
flat, `(N/P)/Q=(N/Q)/P` (`deletionCoefficientInsertion_comp`,
`deletionCoefficientInsertion_comm`, `deletionNestedCofactorCutoff_comm`). General floor transforms
compose by Dirichlet convolution (`floorTransform_comp`), so changing one-dimensional factor order
cannot create an associator.

CANNOT-316 — A source-first factorization transgression cannot live only in cofactor insertion or
nested scalar floor cutoffs: both forget factor order exactly. Renaming their zero associator as a
carry, cocycle, or higher grade adds no information.

MUST-219 — Must distinguish observing a final coefficient stream from observing its execution
history. If two sequences of operations produce exactly the same stream, every function of that
final stream agrees, including any number of subsequently formed sums or products. Inserting a
stream at multiples of `P` and then at multiples of `Q` has this commutation property. An order-sensitive proposal therefore needs
additional defined history data; increasing the number of indices alone does not establish such
data or its relation to a zeta zero.

F692 — [Lean] At simultaneous closed endpoints, the two complementary chronological orderings do
not cancel each other: polarized quasi-shuffle forces their Hermitian symmetrization to equal the
negative pointwise diagonal bracket (`endpoint_mul_star_endpoint_eq_cross_add_reverse_add_bracket`,
`eulerDeletionCrossLimits_quasiShuffle_zero`). For the coprime singleton/interaction deletion grades,
that diagonal is strictly positive by F689. Natural depth-two schedule comparison therefore retains
the weighted defect; it does not annihilate it.

CANNOT-317 — A two-index strict-order schedule cannot be the missing zero selector when its entire
boundary law is polarized quasi-shuffle. Endpoint closure then determines the schedule sum as minus
the nonzero diagonal, not as zero.

MUST-220 — Any remaining schedule-based deletion selector must begin at depth at least three and
exhibit a conditional factorization-tree grouping law not fixed by quasi-shuffle associativity.
Every required limit and rearrangement must be proved; treating two bracketings of an associative
quasi-shuffle product as distinct is invalid.

F693 — [Lean] Any finite same-clock weighted bilinear pairing has zero additive four-term
associator: `B(x,y)+B(x+y,z)-B(y,z)-B(x,y+z)=0`. Increasing from two inputs to three therefore
does not create order information when the operation remains additive and bilinear
(`deletionWeightedPairingPrefix_additive_associator_zero`).

F694 — [Lean] A nonzero higher defect can survive when composition acts on arithmetic labels rather
than by source addition. For pairwise-coprime integers `P,Q,R>1`, let
`D_alpha(P,Q)=Z(alpha)(1-P P^(-alpha))(1+Q(Q-2)Q^(-alpha))` and define
`K_alpha=D_alpha(P,Q)+D_alpha(PQ,R)-D_alpha(Q,R)-D_alpha(P,QR)`. For `alpha>1`,
`K_alpha=Z(alpha)(Q Q^(-alpha))(1-P P^(-alpha))(Q-1)(1-R^(2-alpha))`; hence it is negative on
`1<alpha<2`, zero exactly at `alpha=2`, and positive for `alpha>2`
(`deletionFactorizationGradeCurvature_eq_of_pairwise_coprime`,
`deletionFactorizationGradeCurvature_eq_zero_iff`).

CANNOT-318 — Adding a third input cannot rescue a selector whose only operation is a bilinear
pairing and source addition. Its factorization-tree associator vanishes algebraically before any
analytic or zero-specific information enters.

MUST-221 — A surviving higher-order selector must identify the operation that carries nontrivial
curvature and prove that operation is the one controlled by the analytic closure data. Changing
from additive source composition to multiplication of arithmetic labels may create curvature, but
the change of operation itself does not prove a closure theorem.

MUST-222 — A sign-definite nonzero invariant is not a contradiction. To exclude an analytic object,
one must independently prove that the object's defining closure forces that same invariant to
vanish; assuming equality of the compared factorization trees merely assumes the missing theorem.

F695 — [Lean] If an associative label product is centrally lifted by a binary correction `D`, the
lift need not remain associative: its associator is the four-term curvature of `D`. For the explicit
deletion correction in F694, `(P,a)⋆(Q,b)=(PQ,a+b+D_alpha(P,Q))` has associator `K_alpha(P,Q,R)`
and is provably nonassociative for pairwise-coprime `P,Q,R>1` throughout `1<alpha<2`
(`deletionFactorizationGradedMul_associator_second`,
`deletionFactorizationGradedMul_not_associative_of_pairwise_coprime`).

CANNOT-319 — Associativity of a base operation cannot justify equality of two factorization trees
after a non-cocyclic correction coordinate is attached. The correction must satisfy its own
cocycle law; nonzero four-term curvature is the exact obstruction.

MUST-223 — To annihilate a nonzero correction curvature on a special analytic fibre, one must
construct an observation or quotient, prove the correction is admitted by it, and derive that
admission from the fibre's actual closure data. Merely declaring the two lifted products coherent
assumes the result.

CANNOT-JP1 — Returning every coordinate to its starting value, even with every polynomial line
integral of coefficient degree at most three equal to zero, cannot imply absence of all higher
joint path information. The literal integer-count paths for moduli two and three give a closed
polygon passing all those tests but with `integral x*y^3 dx=1/10`. The general coprime-family
moment is also proved. A proof must justify the higher cancellation it needs; low-degree closure
cannot supply it. This finite unweighted statement makes no claim about cancellation for the
actual infinite weights defining zeta.
[Exact source and closed Lean certificate](../euler-deletion-joint-polygon-moment.md).

CANNOT-JP2 — Existence and invertibility of an ordered arithmetic product cannot select the
critical line if they already hold on an open region crossing it. For the literal discrepancies
`a_p(n)=1-p[p divides n]`, the products of `exp(n^(-s)*(a_2(n)X+a_3(n)Y))` converge to a
unit for every `Re(s)>1/5` and arbitrary `X,Y` in a complete complex normed unital algebra.
This includes noncommuting `X,Y` and every partial prefix, with no zeta-zero assumption.
For one fixed explicit target, convergence on the positive real axis holds exactly above `1/5`.
Any critical-line argument using this object must establish an additional relation derived
from the zero condition; convergence alone supplies none.
[Closed Lean convergence theorem](../../3-formalized/euler-deletion-joint-product-one-fifth.md) and
[actual-product sharpness](../../3-formalized/euler-deletion-joint-product-sharpness.md).

CANNOT-CM1 — Complete multiplicativity and exact finite arithmetic cancellation cannot by
themselves force a sign for a quadratic observation. There are strictly positive functions on
all positive integers, each satisfying `w(ab)=w(a)w(b)` and `w(1)=1`, with the same zero
deletion sums for every divisor of thirty through the same cutoff, but opposite quadratic
curvature signs. Opposite changes at two large prime values preserve those linear sums
exactly. Every scalar observation of these examples is controlled by its values at just three
weights and a shorter coefficient sum. This finite obstruction does not cover the literal
infinite weights `n^(-s)`; using their extra structure requires a separate proved relation.
[Exact classification and unconditional Lean countermodels](../../3-formalized/euler-deletion-paired-prime-freedom.md).

MUST-ATT1 — A change of arithmetic weights must preserve convergence of the original ordered
series before its analytic continuation can be used as a countermodel for that series.
Multiplying the weight at `p^k*m`, with `p` prime and `p` not dividing `m`, by `c^k` for
`0<c<1` preserves positivity and complete multiplicativity. Yet the unchanged deletion
coefficient `1-p[p divides n]` then gives a divergent ordinary series at every `Re(s)<1`.
The unique bounded-prefix repair replaces the multiplier `p` by `p/c`; it recovers
convergence for `Re(s)>0` but changes the source operation. Any curvature or compatibility
comparison using that repair must account for the changed coefficient.
[Exact digit remainder, normalization classification, and Lean admission theorem](../../3-formalized/euler-deletion-prime-attenuation-admission.md).

MUST-ATT2 — A proposed reduction of an arithmetic obstruction must include the normalization
needed to keep the changed source meaningful. Smaller input weights alone do not ensure a
smaller obstruction: reciprocal changes in the coefficients can cancel that reduction exactly.
In the proved deletion example, compensating a prime attenuation preserves the entire sign
boundary of the quadratic obstruction. If the first two test weights stay one, the obstruction
divided by total mass is exactly unchanged, even as the third and other prime weights vary.
This repair therefore requires a different proved identity or observable; shrinking the inputs
and reusing the old comparison cannot supply one. This restriction concerns the specified
repair, not every possible arithmetic deformation.
[Actual infinite-sum identity, full sign boundary, and Lean certificate](../../3-formalized/euler-deletion-compatible-curvature.md).

CANNOT-LIN1 — A different description of the same linear generators cannot bypass the open
approximation problem of a classical RH route. The first `N` terms of `1-p*[p divides n]`
sum to `N mod p`; division by `p` gives the published fractional-part sequence `fract(N/p)`.
Consequently all finite linear combinations, and their closures in the same carrier, agree
after an explicit coefficient rescaling. Increasing the family of moduli or calling the sums
arithmetic histories does not change this identification. A departure from this classical
route must use an additional proved operation or constraint; linear completion alone does
not supply it. This says nothing against nonlinear chronological information that is actually
retained and independently connected to the zero condition.
[Exact source dictionary, Lean certificate, and primary literature](../../3-formalized/euler-deletion-linear-span-audit.md).

MUST-AREA1 — A rank constraint must concern the actual accumulated quantity, not a different
object with similar notation. The alternating product of two endpoint vectors has rank at most
two. An ordered area instead adds alternating products from many pairs of times, so that
endpoint identity supplies no rank bound for it. In the literal arithmetic deletion paths,
remote calculations at three approximate zeta zeros strongly disfavor the proposed rank-two
area law. These are numerical diagnostics, not certified infinite counterexamples. A replacement
must provide an independent identity for the weighted ordered sums; rescaling channels or
quoting unweighted period cancellation supplies none.
[Exact candidate, scope of the second pass, and downloaded computation report](../euler-deletion-mixed-area-rank.md).

MUST-SURG1 — An obstruction to one way of inserting zeros must not be used to prohibit every
function with the resulting zero set. Multiplying a nonzero ordinary Dirichlet series by a specified
nonconstant polynomial leaves that class, but an additional analytic factor with no zeros can
change this conclusion. Lean verifies an ordinary Dirichlet series with unimodular completely
multiplicative coefficients whose continued divisor has just one simple zero at `3/4+i`.
Consequently Dirichlet-series membership and coefficient multiplicativity alone do not prohibit
finite divisors or off-line zeros. A proof concerning the literal zeta coefficients needs an
additional proved constraint. This correction does not impose a functional equation on the
counterexample and does not assert that arbitrary surgery preserves zeta's other properties.
[Exact scope correction and unconditional Lean witness](../dirichlet-polynomial-surgery-scope-audit.md).

MUST-SIGN1 — Cannot obtain critical-line confinement merely by restricting completely
multiplicative coefficients to real integers of modulus one. Bochkov's Theorem 2(2) permits
prescribed finite conjugation-symmetric zero and pole multisets in `21/40 < Re(s) < 1` with
coefficients in `{-1,1}` and meromorphic continuation to `Re(s)>21/40`. In particular, choose
simple zeros at `3/4+i` and `3/4-i` and no poles. This published result is not Lean-certified
here. It imposes neither zeta's functional equation nor its all-one coefficients. Any use of
coefficient integrality to locate zeta's zeros must exploit additional properties of its fixed
sequence.
[Primary theorem, page 3](https://arxiv.org/pdf/2207.08659).

MUST-PREFIX1 — A finite exact coefficient prefix needs a proved constraint on the unseen
coefficients before it can exclude off-line zeros. For every cutoff `N`, Lean constructs a
globally completely multiplicative coefficient sequence of unit modulus, equal to one at
every integer from one through `N`, whose ordinary Dirichlet series has a meromorphic
continuation with one simple zero at `3/4+i` and no other divisor in `Re(s)>0`.
The function can change with `N`; this does not give one counterexample agreeing with all
zeta coefficients at once. No functional equation is imposed. Thus even exact finite
agreement plus those global properties cannot supply the missing constraint. A verified
tail bound or a theorem using the full literal sequence remains outside this obstruction.
[Exact construction, scope, and proof status](../../3-formalized/not_new_scientific_knowledge/helson-finite-prefix-zero-freedom.md).

MUST-TAIL1 — Controlling coefficients must come with a proved control of their continued
function before passing to a limit after continuation. Strictly positive completely multiplicative
coefficients, bounded by one and agreeing with arbitrarily long exact zeta prefixes, can
converge to the all-one sequence in every weighted square distance
`sum |a_n-1|^2/n^(2 sigma)`, `sigma>1/2`, while their ordinary Dirichlet series continue to
zero-free analytic functions on `Re(s)>0` and fail to converge to zeta at every real point in
`(0,1)`. Thus these coefficient controls do not justify interchanging continuation and limits.
The failure occurs at regular, nonzero values of zeta and cannot alone distinguish its zeros.
No functional equation is imposed on these approximants; stronger arithmetic control is outside
this obstruction.
[Exact construction and closed Lean proof](../../3-formalized/not_new_scientific_knowledge/positive-prime-tail-translation.md).

CANNOT-AFF1 — Applying an arbitrary nonlinear rule to finitely many fixed congruence tests of
`a*n+b` cannot escape periodic coefficients: the result depends only on `n` modulo the product
of the test moduli. Its Dirichlet series is therefore a finite combination of the existing
Hurwitz-zeta functions in the absolute-convergence region. Neighboring inputs, overlapping
moduli, and non-invertible slopes do not alter this fact. This statement does not cover growing
moduli, operations on already-summed analytic functions, or ordered infinite histories.
[Exact scope and Lean scratch verification](../../5-failed/affine-congruence-pattern-architecture-audit.md).

CANNOT-MODEL1 — An inequality between assigned exponents for several named methods cannot rule
out every method in a family. Likewise a predicate defined as `False` proves no obstruction for
an arithmetic object that never appears in its definition. Such bookkeeping needs a separate
theorem connecting the model to the actual functions and estimates before it can exclude a proof
architecture. The corrected [method-model audit](../corpus-method-model-semantics-audit.md)
identifies a concrete corpus instance; it supplies no new analytic method.

CANNOT-BP1 — Cancellation of every linear divisor test in a finite arithmetic period cannot by
itself determine the sign of an arbitrary quadratic observation of the same coefficients. Give
the two occurrences of each residue weights `1+h` and `1-h`: every linear sum stays fixed, while
the corresponding squared-weight sum changes by `2 sum f h^2`. Lean gives two strictly positive
weight assignments on integers `1,...,60` with all divisor-of-30 endpoints zero and opposite signs
for one fixed quadratic observation. This is a finite counterexample; it makes no claim about the
actual infinite weights in the zeta function.

MUST-BP1 — A proof that passes from zero weighted sums to a sign or vanishing statement involving
squared weights must justify that passage for the actual weights. Merely retaining the same
arithmetic coefficients, adding more finite divisor tests, or keeping weights positive does not
supply the missing relation. Exact freedom formula and closed countermodels:
[balanced-period theorem](../../3-formalized/euler-deletion-balanced-period-freedom.md),
`RHTower.DeletionBalancedPeriods.positive_weights_closed_endpoints_opposite_curvatures`.

CANNOT-304 — No Littlewood weight beats the Levinson shift. Every weighted Littlewood identity for `log|ζΨ|` on the critical line is Green's identity `∫_line log|F| = (1/2π)∫_{∂Ω} log|F| β − Σ_{ρ∈Ω} φ_Ω(ρ)` with `φ_Ω` the Green potential of the line measure in a domain `Ω ⊇ line` and `β` its balayage onto `∂Ω`; the shift is the right half-plane (`φ̂ = 2πR`, `β` on `σ₀`), the disc method is the chord potential, the strip `{−R < x < R'}` gives `φ̂ = 2πRR'/(R+R')`. With the unconditional inputs (mean squares `c(x)` on lines `½ + x/log T`, on-line proportion `κ`, the `ρ ↔ 1−ρ̄` symmetry), the bound is `(1/4π)[log E_β c − credit]` and: (i) only translation-invariant `Ω` give every zero the same credit (else only `min_t φ` is usable); (ii) only right-unbounded `Ω` credit the off-line pairs (right member capped at `φ̂`), while for bounded symmetric `Ω` the pair credit decreases with the offset and, if kept, cancels the off-line mass identically (a consistency inequality `log E_β c ≥ φ̂/π`, no bound); (iii) the left half-plane is excluded since the far-left boundary term of Green's identity carries the functional-equation growth; (iv) `log c(−x) = log c₀ + x + c₂x² + …` with slope exactly `1` and `c₂ = 0.426` (`θ = 4/7`), so the half-plane's net is `κR/2 − c₂R²/2` while the symmetric strip's is `κρ/2 − (c₂ + ½)ρ²/2` — same first order, the convexity of `e^{−x}` doubles the second-order cost. Numbers (`θ = 4/7`, `κ = 0.4`, fixed coefficients): Jensen `0.0805T`; half-plane `0.0732T` (`R = 0.46`; `0.0714T` with the σ₀-renormalised mollifier); symmetric strip `0.0771T` (`ρ = 0.22`); asymmetric strip `0.0770T` (`R = 0.20, R' = 0.25`); disc `0.0783T` (`a = 0.30`). Zero-density bounds cannot credit off-line zeros in bounded domains (`p_T(s) = 1` for `s < 0.449`). The Littlewood-weight lever is exhausted: the corpus constant `0.0714T` is optimal in this family up to the mollifier profile (Conrey's `P, Q`) and renormalisation.

F679 — [Lean] The slope law of the Levinson mean square (`LevinsonMeanSquareSlopeLaw.lean`, `youngMeanSquare_slope_law`): for Young's functional `c_P(R) = 1 + (1/θ)·E(R)·∫₀¹(RθP + P')²`, `E(R) = ∫₀¹e^{2Rv}dv`, and every `C¹` profile with `P(0) = 0`, `P(1) = 1`: `c_P'(0) = c_P(0)`. Ingredients: `E(R) = (e^{2R}−1)/(2R)` (`youngE_eq`), `E'(0) = 1` from the third-order exponential bound (`hasDerivAt_youngE_zero`), the mollifier integral is the quadratic `∫P'² + R·2θ∫PP' + R²θ²∫P²` (`integral_shiftedProfile_sq`), and `∫₀¹2θPP' = θ(P(1)² − P(0)²) = θ` (`integral_two_theta_mul_profile_deriv`). So the left-shifted mean square grows at first order exactly like `e^{R}` for every mollifier, and the Levinson net gain `(1+κ)R/2 − R/2 = κR/2` is universal.

CANNOT-305 — The swap terms cannot reopen the mollified-Littlewood family through the slope: `d/dR log c_P(R)|₀ = 1` for every profile (F679), structurally because the twisted second moment is `A(x) + e^{−2x}B(x)` with the two singular terms sharing the functional-equation factor evenly at zero shift. Correction to the earlier "flow = torus at the mean square": the Steinhaus mean square of the linear-mollified product is `(1/θ)(3/2 + ½∫∫_{u+v>1}(u+v−1)²/(uv) + …) = (1/θ)(1.5725 + …)` against the flow's `1 + 1/θ`; they cross near `θ = 0.6`, so at `θ = 4/7` they nearly coincide (`2.8` vs `2.75`) and for smaller `θ` the torus overestimates — the swap term is negative at second-moment level. With CANNOT-300–304 the family is closed at `0.0714T` up to the profile optimisation; no further cycle should be spent inside it.

F680 — [Lean] The single-input explicit `(L)` constant (`SingleInputOffLineMomentConstant.lean`, `eventually_offLineMoment_le_of_gates`): from the two mollified mean-square gates on the same Levinson abscissa `σ₀ = ½ − R/log T` — `ZetaMollifiedMeanSquareGate R c₁` (mean square of `ζΨ` eventually `≤ (c₁+ε)(T₂−T₁)`) and the corpus `LevinsonMeanSquareGate R c₂` (mean square of `(ζ+λζ')Ψ`) — and any target `κ₀ + 2δ < 1 − log c₂/R`: for every `η > 0`, eventually `4π·Σ_{Im ρ ≤ V} m_ρ(Re ρ − ½) ≤ (log c₁ − (1+κ₀)R + η)·V`; letting `κ₀ → 1 − log c₂/R` the density of the off-line first moment is at most `(log c₁ + log c₂ − 2R)/(4π)`. Bricks: the census bridges (`OffLineMomentCensusBridge`: `2·Right = N + N₀` from `window_identity`, `xiOddFiberCount ≤ N₀`, window comparisons of the ceiling's zero finset with the census), Levinson's proportion at an arbitrary target (`LevinsonOddFiberDensityGeneral`, `eventually_oddFiber_ge_of_gate_general`: the corpus density proof with `1/3` freed; the only bound used is `κ₀ + δ ≤ 1`, slack `η ≤ 1/40`), the credited line-count ceiling, Riemann–von Mangoldt, and one window arithmetic lemma (`offLineMoment_window_arith`). Both external inputs are now instances of one theorem type — the twisted mollified mean square on the Levinson line (MUST-212 sharpened: `c₁ = c(P, 1, R, θ)`, `c₂ = c(P, Q, R, θ)` with Levinson's `Q`). With the paper values `R = 0.6`, `log c₁ = 1.735`, `log c₂ = 0.36`: `0.0712T`, the corpus constant.

F681 — [Lean] Item 7 of the mollified mean-square programme is closed as bookkeeping (`LevinsonGateFromDyadicMeanSquare.lean`, `levinsonReciprocalLogMeanSquareGate_of_dyadicLaw`): the exact interface the analytic lane must deliver is `DyadicDetectorMeanSquareLaw R c` — for every `ε > 0` and all large `U`, a mollifier of the gate's class and, for every `σ₀ = ½ − R/log T` with `T ∈ [U−1, U]` and every dyadic block `[a, v] ⊆ [20, U]` (`a ≤ v ≤ 2a`), `∫_a^v ‖(ζ + λζ')Ψ(σ₀+it)‖² ≤ (c+ε)(v−a) + ε(a + U/log U)` with `λ = 1/log U`. From it: zero-free edges `T₁ ∈ (20,21)`, `T₂ ∈ (U−1,U)` via `exists_horizontal_slices_avoiding_entire_zeros` on the entire detector times the mollifier; the dyadic decomposition `[T₁2^k, T₁2^{k+1}]` plus a partial last block (`Nat.find`, `sum_integral_adjacent_intervals`); `Σ_k T₁2^k ≤ 2T₂`, at most `3 log U` blocks, and `U ≤ 2(T₂−T₁)`, giving `(c + 11ε/13)(T₂−T₁)`. With F680 the whole chain from the dyadic law to the single-input `(L)` constant and the two cards' densities is Lean; the dyadic law is the single remaining analytic input (Conrey/Levinson twisted mean square on blocks).

F682 — [Lean] The `λ = 0` twin and the low blocks (`ZetaGateFromDyadicMeanSquare.lean`, `DyadicLawLowBlocks.lean`): `zetaMollifiedMeanSquareGate_of_dyadicLaw` turns `ZetaDyadicMeanSquareLaw R c` (the same per-block law for `‖ζΨ(σ₀+it)‖²`) into the `ζΨ` gate of F680, so the single-input `(L)` constant now rests on the two dyadic laws (`λ = 0` and `λ = 1/log U`) and nothing else; `integral_normSq_mollifiedDetector_low_block_le` bounds any block `[a, v] ⊆ [20, 2T₀]` by `(v−a)(C(T₀)·N)²` with `C(T₀)` the detector's bound on `[¼,½] × [20, 2T₀]` (`exists_detector_bound_low`) and `‖Ψ‖ ≤ N` (`norm_edPoly_le_card`), so with `N = U^θ`, `θ < ½`, every block below a fixed height is covered by the law's slack `ε U/log U` alone: the analytic input is needed only on blocks `[a, 2a]` with `a ≥ T₀(ε)`.

## MUST-215 (2026-09-05)
MUST: prove `RHTower.SharpEnergyInput C` for some explicit `C` (`HighBlockParameters.lean`): the sharp-cutoff critical mollified energy against the displaced gate mollifier `b_d(m) = μ(m) log(N/m)/log N · m^{−1/2+d}` is bounded uniformly in the head length `u < ⌈a^{51/100}⌉`, in `0 < d ≤ 1/4`, and in `1 ≤ a ≤ U`, for all large `U` (`N = ⌊U^{1/20}⌋`). With it, `RHTower.exists_zetaDyadicMeanSquareLaw_of_sharpEnergyInput` gives `ZetaDyadicMeanSquareLaw R c` and hence the `ζΨ` gate of the single-input `(L)` constant. This is Graham/Barban–Vehov uniformity in upper-bound form with the `m^{d}` weight; the corpus bound `sum_harmonic_sq_barbanVehovCoeff_le` carries an `M² log³ M` defect and does not suffice.

CANNOT-320 — The mean square of a mollified half of the approximate functional equation cannot be bounded independently of the mollifier length. With a Barban–Vehov mollifier of length `N` and any head cutoff, sharp or smooth, the coefficient energy of the mollified half-sum is `≍ log N`: the diagonal kernel `log min(m₁,m₂)` carries a sharp cutoff whose Selberg diagonalisation is bounded below by the Dress–Iwaniec–Tenenbaum constant `lim Σ_{d,e≤y} μ(d)μ(e)/[d,e] > 0`. Only the full sum of the two halves and the cross term is `O(1)`; splitting the second moment into direct, dual and cross pieces and bounding each in absolute value loses a factor `log N`. A bounded constant needs the product functional equation (twisted second moment).

## 2026-09-06 — degree-four Jensen certificates

CANNOT-321 — A quartic Jensen polynomial cannot be certified from independent bounds on the three dispersions `D_l = m(n+l)m(n+l+2)/m(n+l+1)² − 1` of its five moments. Along the equal-dispersion (log-normal) diagonal the tolerance is `≍ 1/b`, `b = n + ½`, and the exact log-normal reference is a rescaled Hermite quartic hyperbolic for every `D·b < 1`; transverse to the diagonal (a change of `D_{n+1}` alone, equivalently of the second difference `D₀ − 2D₁ + D₂`) the tolerance is `≍ 1/b²`, because the individual perturbation terms at `z = −b` are `≍ b⁴|ε|` against a reference value `≍ b²` and only the correlated log-normal structure cancels them. Any box sandwich on the moment ratios is therefore useless at degree four, and the previously recorded diagonal tolerance `2/(3b)` was an artefact of a dropped same-order term.

MUST-224 — A dispersion certificate of degree-four Jensen hyperbolicity for `Ξ` must supply two-sided control of the size-biased theta dispersions with relative precision `O(1/n)`: bounds `Var(log s)·b ≤ 1/2`, `|κ₃(log s)| ≲ b^{−3/2}`, `|κ₄(log s)| ≲ b^{−2}` for the tilted measures `x^{2κ}Φ(x)dx` at real tilts `κ ≥ n`. Curvature-infimum bounds cannot deliver this precision (in the logarithmic variable the curvature infimum is zero); the estimates must be localised at the tilted mode. With these inputs and `b ≥ 2000` the quartic is hyperbolic (Lean, sign alternation at five explicit points).

CANNOT-322 — The Jensen–Pólya lane cannot individuate zeros in the regime `d = o(n)`: for `n³ log²(n+2) ≥ K d⁵` the Jensen polynomial `J^{d,n}` of `Ξ` is hyperbolic unconditionally (Holland, arXiv:2608.08682, August 2026), by matching the first five Taylor ratios exactly with a real-rooted finite-free product of two Jacobi hypergeometric factors and a fifth-order multiplier stability principle; the joint zero law along the wedge is Wigner's semicircle. The input is the sectorial saddle asymptotic of `log M_z` for the continued theta moments `M_z = ∫Φ(u)u^{2z}du`, whose second, third and fourth derivatives are `2/(x𝓛_x)`, `−2/(x²𝓛_x)`, `4/(x³𝓛_x)` with `𝓛_x` the Lambert-type solution of `x = L(πe^L + ¾)`; so `D₀·b → 0` like `2/log n`, `D₀ − D₁ ≍ 2/(n² log n)`, `D₀ − 2D₁ + D₂ ≍ 2/(n³ log n)`, and the two-sided dispersion control of MUST-224 is a formalisation target, not a research target. Any finite-order model matching stops below `d ≍ n log n`: with `K` matched Jacobi factors the Hermite–Genocchi residual is `≍ (d + 2√(nd))^{2K+1}/(n^{2K}(2K+1)! log n)`.

MUST-225 — RH information in the Jensen–Pólya lane sits only at `d ≳ n`, and there it is the Laguerre–Pólya property of derivatives: with `F₀(x) = Σ γ(j)x^j/j!` (`Ξ(t) = F₀(−t²)`, order `½`) and `J^{d,n+1} = (J^{d+1,n})'/(d+1)`, all `J^{d,n}` for one fixed `n` are hyperbolic iff `F₀^{(n)}` is Laguerre–Pólya (Pólya), which by the Pólya–Wiman and Fourier–Pólya theorems for order `< 2` (Craven–Csordas–Norfolk, Kim; Ki–Kim) holds for some `n` iff `Ξ` has only finitely many non-real zeros. Hence the first non-hyperbolic degree `d*(n)`, if finite, satisfies `d*(n) ≥ c n^{3/5} log^{2/5}(n+2)` for every `n`, and any off-line zero remains visible at every derivative order. A producer in this lane must control the Taylor coefficients below the saddle threshold, where no asymptotic model exists, jointly with the asymptotic ones; the perturbative wedge is RH-blind by theorem.

## Uniform integrated prime-error criterion

CANNOT-323 — It cannot require recovery of an optimal square-root constant as a universal prerequisite for RH. Write `D(X)=X−1−Σ_{n≤X}Λ(n)log(X/n)`, where `Λ` is the von Mangoldt function. The corpus proves that **any** finite uniform bound `|D(X)|≤B√X` for `X≥1` implies RH; no prescribed small value of `B` is required. A sharp sign estimate for a particular Weil form is one possible proof strategy, not a necessary restriction on every arithmetic proof (`riemannHypothesis_iff_logChebyshevDeficitPrimitive_bound`, `CCMRestrictedWeilPoleCompressionRHCriterion.lean`).

MUST-226 — RH must be equivalent to a uniform square-root bound for the signed integrated prime error `X−1−Σ_{n≤X}Λ(n)log(X/n)`. The constant may be any finite value; the uniformity in `X` and the square-root exponent carry the mathematical content. A bound with an unbounded logarithmic loss does not meet this exact criterion. Individual unsigned prime terms and formal source identities alone do not supply the required signed bound (`riemannHypothesis_iff_logChebyshevDeficitPrimitive_bound`).

## First central logarithmic moment test

CANNOT-324 — It cannot have a negative degree-one central moment test: writing `−Ξ'(t)/(tΞ(t)) = Σ M_k t^(2k)` at zero for the completed critical-line Xi function, `a²M₀ + 2abM₁ + b²M₂ ≥ 0` for all real `a,b`, unconditionally. Therefore any negative polynomial witness in this RH-equivalent moment criterion must have degree at least two. Exact theta-source integration proves this first block without assuming zero locations; higher-degree signs remain open (`forall_primeArchSourceTraceHankel_linear_nonneg_stein`, `ThetaGibbsSteinSourceMinor.lean`).

MUST-227 — The zero margin of the fixed exponential-pole criterion is a constant-level artefact of its test transforms (the even and odd transforms `ê_a(t)`, `ô_a(t)` are real with real zeros, so a single zero ordinate can sit where the transform vanishes), not a property of the exponent. Its aperture-window averages `∫_a^{a+1} E_±(a')da'` are still equivalent to RH — an off-line zero `ρ₀ = β₀ + iγ₀` contributes `e^{2aβ₀}` times an oscillating factor that dominates every on-line term and changes sign — while under RH they satisfy `∫_a^{a+1}E_± ≥ 0.94·c₀(e−1)e^a`, because the averaged cross term is bounded by `(e+1)Σ_ρ|ρ|^{−3}√X ≈ 0.004√X` against the mean `c₀(e−1)√X ≈ 0.079√X`. Consequently a producer may lose constant factors on window averages; what it cannot lose is the exponent: every equivalent form of the criterion is von Koch's statement that the weighted prime error `Σ_{n≤e^h}Λ(n)/√n − 2e^{h/2}` grows at most polynomially in `h`, and the criterion is a one-parameter family of linear functionals of that error against the kernel derivative `K_a'`, `K_a(h) = 4sinh(a − h/2) + 2(2a − h)cosh(h/2)`. Sharpness of constants and control of the exponent are separate obligations; only the second carries RH, and no sieve, mean-value, or positivity mechanism supplies it.

MUST-228 — The zero infimum of the fixed-pole relative margin is a Kronecker asymptotic, not a practical obstruction: with the first 1500 zero ordinates the worst relative margin over apertures `a ≤ A` is `0.42` for `A = 10³` and `0.33`/`0.31` (even/odd) for `A = 10⁶`, decaying roughly like `0.5 − 0.013·log A`; at the prime-entry checkpoints `a = log p/2` it stays above `0.48` for all `p ≤ 10⁸`, and consecutive primes give nearly equal values because the margin is a slowly varying function of the aperture. Hence any argument that reaches the sign with a loss of a fixed factor below `3` on windows of apertures up to astronomically large `A` is not excluded by the constant-level sharpness; what excludes every known argument is the exponent (MUST-227). A producer must therefore be built around the exponent `Θ = ½`, and the corpus's Route O checkpoint reduction (odd signs at prime powers above two, even signs everywhere) does not change the required strength.

CANNOT-324 — In the two-pole Weil criterion the self-pairings of the archimedean pole vectors `p_± = e^{±x/2}1_{[−a,a]}` cannot carry RH: `Q(p_±) = c₀e^a − 2e^a(E_M(2a) + γ) + 2e^{−a}(ψ(X) − X) + O(ae^{−a})` (Lean, `PoleBoundaryLogSharpConstant`), and an off-line zero of real part `β` enters it only as `e^{a(2β−1)} = o(e^a)` for every `β < 1`; positivity of either pole vector at all large apertures therefore follows from Mertens' constant and any zero-free region `Θ < 1`, and is a prime-number-theorem statement. The entire RH content of the criterion is the cross-pairing `Re Q(p₊,p₋) = Σ_ρ X^ρ/ρ² + O(1)`, a mean-zero almost-periodic fluctuation of the zeros whose off-line terms `e^{2aβ}` exceed the self-energies `e^a` exactly when `β > ½`. RH is the Cauchy–Schwarz inequality `|Q(p₊,p₋)|² ≤ Q(p₊)Q(p₋)` for this single pair at every aperture: the angle between the two archimedean pole directions in the Weil form is well defined iff RH.

MUST-229 — The criterion is the archimedean Weil bound with a regularised genus. The self-energy coefficient `c₀ = 2 + γ − log 4π = Σ_ρ 1/(ρ(1−ρ))` is the convergent analogue of the zero count `2g = Σ_{zeros} 1` of a curve, and `|C(a)| ≤ A(a)` reads `|N(X) − M(X)| ≤ c₀·√X` with `N(X) = Σ_{n≤X}Λ(n)(1+1/n)log(X/n)` the weighted point count and `M(X)` its explicit smooth main term — exactly the shape `|#C(F_q) − (q+1)| ≤ 2g√q`, whose only known producer is the Hodge index theorem on `C × C`. Any producer for RH must therefore supply the archimedean Hodge index (signature `(1,∞)` of the Weil form on the arithmetic square), with the genus term `c₀√X` produced from Mertens' constant, the boundary mass `1 − log 2` and `κ`, and the cross term controlled with no loss in the exponent; prime-sum estimates cannot replace the index.

MUST-230 — [Lean] The archimedean genus is a certified positive constant and the pole self-energy is unconditionally positive at large apertures: `A(a)e^{−a} → 2 + γ − log 4π` with `γ > 0.545` and `log 4π < 2.534` (so the constant exceeds `0.011`), hence `A(a) > 0` for all large `a`, from Mertens' theorem with the Euler constant (`Σ_{n≤x}Λ(n)/n − log x → −γ`, now a corpus theorem) and the prime number theorem with error term. Therefore any claimed obstruction to the fixed-pole criterion located in a self-pairing is spurious; the obstruction is the cross pairing alone (CANNOT-324), and a producer must be judged only by whether it controls `Σ_ρ X^ρ/ρ²` at scale `√X`.

CANNOT-325 (corrected) — A zero-lag self-pairing of the Weil form cannot see the exponent of an off-line zero, but the exponent is not confined to reflection pairings: for the pole windows `f_a = e^{x/2}1_{[−a,a]}` the Weil pairing is exactly `Q(f_a,f_b) = 2cosh((a+b)/2)·Φ(a−b) − 2cosh((a−b)/2)·Φ(a+b)` with the lag function `Φ(L) = Σ_ρ e^{L(ρ−1/2)}/(ρ(1−ρ))`, so an off-line zero `β + iγ` enters a same-orientation pairing through the aperture *difference* as `e^{(a−b)(β−1/2)}` and a reflection pairing through the aperture *sum* as `e^{(a+b)(β−1/2)}`; only the diagonal `a = b` is blind (`Q(f_a) = 2cosh(a)Φ(0) − 2Φ(2a)`, off-line part `e^{a(2β−1)} = o(e^a)`). Consequently a producer may be a statement about lags between apertures of one orientation; it need not involve the reflection `x ↦ −x`. The earlier form of this entry, which located the exponent only in reflection pairings, was wrong.

MUST-231 — [Lean] The archimedean genus is the regularised zero count, certified with no RH premise: `Σ'_ρ 1/(ρ(1−ρ)) = 2 + γ − log 4π`, the sum running over the nontrivial zeros of `ξ` with multiplicity (`ArchimedeanGenusZeroSum`), via `completedRiemannZeta₀(1) = 1 + (γ − log 4π)/2` (the first Li coefficient `λ₁`), the corpus's Hadamard product of `ξ`, and reflection pairing of the Mittag-Leffler terms. Hence one certified constant is simultaneously the prime-side coefficient of the exponential-pole self-energy (Mertens, boundary mass, `κ`), the first Li coefficient, and the zero sum: the fixed-pole criterion `|C(a)| ≤ A(a)` is the Weil bound `|N(X) − M(X)| ≤ (Σ_ρ 1/(ρ(1−ρ)))·√X` with the zero count in the role of `2g`. Any producer must reproduce this constant from the source and control the cross pairing `Σ_ρ e^{2aρ}/ρ²`; nothing else is left to identify.

MUST-232 — The Weil form of the pole family is governed by one even continuous function, the lag function `Φ(L) = Σ_ρ e^{L(ρ−1/2)}/(ρ(1−ρ))`, absolutely convergent for every real `L` with no hypothesis (`|term| ≤ e^{|L|/2}/|ρ(1−ρ)|`), with `Φ(0) = 2 + γ − log 4π` (Lean, MUST-231). RH ⟺ `Φ` is bounded ⟺ `|Φ(L)| ≤ Φ(0)` for all `L` ⟺ `Φ` is positive-definite (Bochner: under RH `Φ` is the Fourier transform of the positive zero measure `Σ_ρ δ_γ/|ρ|²`; conversely an off-line zero gives the Laplace transform of `Φ` a pole in `Re s > 0`). Its prime side is exact and elementary: for `L > 0`, `X = e^L`, `Φ(L) = e^{−L/2}(X − ψ(X)) + e^{L/2}(Σ_{n≤X}Λ(n)/n − L + γ) − e^{−L/2}B(X)`, `B(X) = log 2π − 1 + ½log(1 − X^{−2}) + X·artanh(1/X)`, equivalently `Φ = Φ_arch + Σ_{n≤X} 2Λ(n)n^{−1/2}sinh((L − log n)/2)` with `Φ_arch(L) = e^{L/2}(1 + γ − L) − e^{−L/2}B(e^L)`: an archimedean germ plus one convex kink of slope `Λ(n)/√n` at every prime power (Landau's bias), and the archimedean log-singularities of `B` at `X = 1` cancel so that `Φ(0+) = 2 + γ − log 4π` from the prime side (verified against 1500 zeros to `10⁻⁶`). Therefore the "sharp one-sided constant `Σ_ρ|ρ|^{−2}`" of the fixed-pole criterion is not an estimate to be reached: it is the value `Φ(0)` of the same function, and the inequality `|Φ(L)| ≤ Φ(0)` is the trivial bound of a positive-definite function. The whole RH content is positive-definiteness (equivalently, under RH `Φ` is the mean autocorrelation of Cramér's function `Ψ(x) = e^{−x/2}(e^x − ψ(e^x))`, and the criterion is Cramér's mean-square criterion `∫_1^X (ψ(t) − t)²t^{−2}dt = O(log X)`); no estimate that produces a constant is asked for, and no estimate that loses the exponent is allowed.

MUST-233 — Positive-definiteness of the lag function pins every prime power: with all prime powers `≤ P` kept and the rest omitted, `Φ_P` stops being positive-definite (Toeplitz test on `[−L, L]`) at `L_pd(P) = log n₁ + δ` where `n₁` is the next prime power and `δ ∈ [0.013, 0.05]` for all 42 truncation points `P ≤ 2048` tested; the two-by-two test `|Φ_P| ≤ Φ(0)` fails at `log n₁ + δ'`, `δ' ∈ [0.04, 0.19]`, larger when the missing weight `Λ(n₁)/√n₁` is smaller (prime powers of 2 and 3). Mechanism, a theorem under RH: `Φ` dips at each prime power (the kink is convex, the values `Φ(log n)` are negative and use a sizable fraction of the budget `−Φ(0)`), and without the upward kink the continuation crosses `−Φ(0)` once `2Λ(n₁)n₁^{−1/2}sinh((L − log n₁)/2) > Φ(L) + Φ(0) ≤ 2Φ(0)`, i.e. within `δ' ≤ 2·arcsinh(Φ(0)√n₁/Λ(n₁))`. Hence the archimedean genus `2 + γ − log 4π ≈ 0.046` is small enough that the positivity budget is exhausted within a fixed small lag past any omitted prime power: the prime side of a positive-definite lag function is tight at every prime power, so no producer can treat any finite set of primes as negligible, and every "smoothed" or "sieved" prime input that misplaces prime mass by more than the tolerance below the kink weight destroys the positivity it is meant to prove (`2-fully-proven/computations/lag-function-pd-horizon/`).

MUST-234 — Positive-definiteness of the lag function is locally rigid at every prime power (theorem under RH, elementary): on any window `[0,L]` the Toeplitz operator of `Φ` is `Σ_ρ |ρ|^{−2}|e^{iγx}⟩⟨e^{iγx}|`, trace class with trace `L·Φ(0)` and spectrum accumulating at `0` (its spectral measure is atomic with density `~ log ξ/(2πξ²)`), while moving or rescaling a single kink by `ε ≠ 0` adds a signed absolutely continuous spectral density `~ ε·Λ(n)n^{−1/2}·sin(ξ log n)/ξ`, which exceeds `log ξ/ξ²` at high frequency and is negative on half of every period; so the perturbed function is not positive-definite on the window for any `ε ≠ 0` (numerically: tolerance `10⁻⁵…10⁻⁴` on a 500-point grid of `[0,6]`, shrinking with the grid; `2-fully-proven/computations/lag-function-pd-rigidity/`). Two consequences for producers: (i) the positivity to be produced is marginal — a trace-class positive operator with infimum of spectrum `0` on every window, no spectral gap on any test space — so no argument that produces positivity with a uniform gap (coercivity, strict Hankel/Toeplitz PSD with a margin, a strictly positive symbol) can be the producer; (ii) the prime side cannot be replaced by any approximation of the prime powers, however accurate, on any window: positivity holds only for the exact positions `log n` and exact weights `Λ(n)/√n`, given the archimedean germ. Together with MUST-233 this is the exact sense in which the fixed-pole/lag criterion is "sharp": sharpness is not a constant but the absence of any spectral gap.

MUST-235 — [Lean] The explicit formula with the genus kernel `1/(s(1−s))` is certified with no hypothesis: for every real `X > 1`, `Σ'_ρ X^ρ/(ρ(1−ρ)) = (X − ψ(X)) + X·(Σ_{n≤X}Λ(n)/n − log X + γ) − log 2π + Σ_{k≥1} X^{−2k}/(2k(2k+1))`, the left side absolutely convergent over the zeros of `ξ` with multiplicity (`LagExplicitFormula.lag_explicit_formula`). Its proof is termwise residue calculus on the Mittag-Leffler expansion of `−ζ'/ζ` (Hadamard product plus the digamma series `ψ(s) = −γ + Σ_k(1/(k+1) − 1/(s+k))`, now in the corpus), Perron evaluations of two-, double- and three-pole rational kernels by Mellin inversion (`PerronRationalKernels`), and a single dominated interchange with the majorant `(1+t²)^{−3/4}`; no zero-density input, no contour past the zeros, no truncation error. Consequently the lag function `Φ(L) = Σ_ρ e^{L(ρ−½)}/(ρ(1−ρ))` has a certified prime side for `L > 0` (`weilLagFunction_eq_prime_side`), `Φ(0) = 2+γ−log 4π`, `Φ` is even, and under RH `|Φ(L)| ≤ Φ(0)` for all `L` (`norm_weilLagFunction_le_of_riemannHypothesis`): RH implies the sharp prime-side bound `|e^{−L/2}(X − ψ(X)) + e^{L/2}(Σ_{n≤X}Λ(n)/n − L + γ) − e^{−L/2}(log 2π − S(X))| ≤ 2 + γ − log 4π` with the constant of MUST-231 and no logarithmic loss. Every sharp-cutoff prime criterion of the corpus can now be attached to this identity; the missing converse `Φ bounded ⇒ RH` is a Laplace-transform argument on the zero side.

MUST-236 — [Lean] The lag criterion is a certified equivalence with the sharp constant built in: `RH ⟺ Φ is bounded on ℝ`, `Φ(L) = Σ'_ρ e^{L(ρ−½)}/(ρ(1−ρ))` (`WeilLagFunctionCriterion.riemannHypothesis_iff_weilLagFunction_bounded`), and under RH the bound is `Φ(0) = 2 + γ − log 4π`. Since `Φ` has the certified prime side of MUST-235 for `L > 0` and is even, this reads: RH ⟺ the explicit prime-side function `e^{−L/2}(X − ψ(X)) + e^{L/2}(Σ_{n≤X}Λ(n)/n − L + γ) − e^{−L/2}(log 2π − S(X))`, `X = e^L`, is bounded, and then it is bounded by `2 + γ − log 4π`. The converse is a zero-side Laplace argument: the Mellin transform `F(s) = ∫_0^1 Φ(−log y) y^{s−1}dy` is holomorphic on `0 < Re s < 2` when `Φ` is bounded, equals the Mittag-Leffler series `G(s) = Σ_ρ (ρ(1−ρ))^{−1}/(s − (ρ−½))` on `Re s > ½`, and an off-line zero chosen with maximal real part on its horizontal line gives a pole of `G` whose right horizontal ray is pole-free; the identity theorem along the ray forces `F` to blow up at the pole. Consequently, for this criterion "losing a constant" costs nothing and "losing the exponent" is impossible: boundedness by any `M` already gives RH and hence the sharp `M = Φ(0)`; the whole content is boundedness, exactly as MUST-232 stated on paper.

MUST-237 — [Lean] The lag criterion is one-sided: `RH ⟺ Φ is bounded above ⟺ Φ is bounded below`, with `Φ` real-valued (`WeilLagFunctionOneSided.riemannHypothesis_iff_weilLagFunctionReal_bddAbove`, `…_bddBelow`), and under RH the bounds are `±(2 + γ − log 4π)`. Mechanism (Landau): a one-sided bound makes `M ∓ Φ` a nonnegative density, the Laplace transform of `(M ∓ Φ)du + du` has an abscissa of convergence which is a genuine singularity (the corpus's `false_of_analyticAt_abscissa`), but the transform agrees on `Re s > ½` with `(M+1)/s ∓ G(s)` — analytic at every real point `> 0` because `ξ` has no real zeros — and the real-analytic identity theorem carries the agreement down to the abscissa; so the abscissa is `0`, the transform is holomorphic on `Re s > 0`, and the analytic-extension theorem of MUST-236 gives RH. Consequence for producers: it suffices to prove that the explicit prime-side function `e^{−L/2}(X − ψ(X)) + e^{L/2}(Σ_{n≤X}Λ(n)/n − L + γ) − e^{−L/2}(log 2π − S(X))` never falls below some fixed `−M` (primes never too sparse in this weighting), or never rises above some `M`; either half alone is RH, and neither can be reached by an estimate that loses the exponent.

MUST-238 — [Lean] **The integer lag law.** RH is a single explicit inequality over the integers with the exact constant: with `a_n := Φ(log n) = [(n − ψ(n)) + n(Σ_{m≤n}Λ(m)/m − log n + γ) − log 2π + S(n)]/√n`, `S(n) = Σ_{k≥1} n^{−2k}/(2k(2k+1))`, one has `a_1 = 2 + γ − log 4π` and `RH ⟺ ∀ n ≥ 1, a_n ≤ a_1` (`WeilLagFunctionInteger.riemannHypothesis_iff_integerLag_le_one`, `riemannHypothesis_iff_integerLagInequality`); equivalently `RH ⟺ (a_n) bounded above ⟺ (a_n) bounded below` (`…_bddAbove`, `…_bddBelow`). Mechanism: on `[log n, log(n+1))` the prime side of `Φ` is a sum of five monotone pieces, so `|Φ(L) − a_{⌊e^L⌋}| ≤ 30` (`weilLagFunctionReal_integerLag_interval`), and the one-sided criterion MUST-237 does the rest. Consequently the integer lags obey a **dichotomy with no intermediate regime** (`integerLag_dichotomy`): either every `a_n` lies in `[−a_1, a_1]` (RH), or `(a_n)` is unbounded above and unbounded below (¬RH). No logarithmic loss, no two-sidedness, no `n ≥ n₀`: the classical Schoenfeld-type criteria `|ψ(x) − x| ≤ √x log²x/(8π)` are replaced by one exact, one-sided inequality whose constant is the value at `n = 1`.

MUST-239 — [Lean] **The ceiling is tight and recurrent.** Under RH, `a_1 = 2 + γ − log 4π` is the exact supremum of `{a_n : n ≥ 2}` (`WeilLagFunctionRecurrence.isLUB_integerLag_of_riemannHypothesis`), and it is approached along the powers of every base: for every `b` and `ε > 0` there is `m ≥ 1` with `a_1 − ε < a_{b^m} ≤ a_1` (`exists_pow_integerLag_gt_of_riemannHypothesis`, `integerLag_law`). Mechanism: under RH `Φ(L) = Σ_ρ cos(γ L)/(¼+γ²)` with positive weights of total `a_1`; simultaneous Dirichlet approximation of finitely many ordinates `γ log b/2π` (corpus `exists_simultaneous_dirichlet`) returns all leading phases to `0`. So the integer lag inequality of MUST-238 has **zero margin at infinitely many integers in every geometric progression**: no proof of it can lose any constant anywhere along `b^m`, and any proof must control the joint distribution of the phases `γ log b` exactly. The lower ceiling is asymmetric: `inf a_n = −a_1` would need all `cos(γ log n) ≈ −1` simultaneously, which Dirichlet approximation cannot supply and which is equivalent to a ℚ-linear-independence statement on the ordinates; only `inf a_n < 0` is forced (mean value `0`). Unconditionally the ceiling is a limit point: for every `ε > 0` there are arbitrarily large `n` with `a_n > 2 + γ − log 4π − ε` (`frequently_integerLag_gt`: recurrence under RH, unboundedness otherwise), so `limsup a_n ≥ 2 + γ − log 4π` always, with equality iff RH; under RH the supremum of every tail `{a_n : n ≥ N}` is the ceiling (`isLUB_integerLag_tail_of_riemannHypothesis`).

MUST-240 — [Lean] **The unconditional `Ω±(√n)` law and the almost-periodicity criterion.** For the genus-kernel prime error `E(n) = (n − ψ(n)) + n(Σ_{m≤n}Λ(m)/m − log n + γ) − log 2π + S(n)` one has, with no hypothesis: `E(n) > (2 + γ − log 4π − ε)√n` for infinitely many `n` (every `ε > 0`), and `E(n) ≤ −η√n` for infinitely many `n` (some `η > 0`) (`WeilLagFunctionOmega.genusKernelError_omega_pm`). Mechanism of the negative side under RH: `Φ` is a Bohr almost-periodic exponential series (corpus `expSeriesCarrier`) with Bohr mean `0` because no zero has ordinate `0`; if `Φ` were eventually `≥ −η` for every `η`, its negative part would tend to `0`, the corpus vanishing lemma would make `Φ ≥ 0` everywhere, and a nonnegative almost-periodic function of mean `0` vanishes (corpus `eq_zero_of_bohrMean_eq_zero_of_nonneg`), contradicting `Φ(0) > 0`; the transfer to integers uses the sharpened interval bound `|Φ(L) − a_{⌊e^L⌋}| ≤ 3(log n + 2)²/√n → 0`; without RH the integer lags are unbounded below (MUST-238). Also `RH ⟺ Φ is Bohr almost periodic` (`riemannHypothesis_iff_isBohrAlmostPeriodic_weilLagFunction`; `Φ` is continuous unconditionally). Consequences: the sign of `E(n)` is not a producer (both signs occur infinitely often whatever the zeros do); the only RH-sensitive quantity is the *size* of the positive excursions, whose exact ceiling is `(2 + γ − log 4π)√n`; the negative ceiling `−(2+γ−log 4π)√n` is RH-sensitive on one side only (unbounded below iff ¬RH) and its attainment is a ℚ-independence question.

MUST-241 — [Lean] **The floor law: the infimum of the integer lags is a Diophantine statement about the ordinates.** Under RH, `−a_1 = −(2 + γ − log 4π)` is the exact infimum of `{a_n : n ≥ 2}` **if and only if** the ordinates have *no odd relation*: every integer relation `Σ c_γ γ = 0` among finitely many distinct ordinates has even coefficient sum (`WeilLagFunctionFloor.integerLag_floor_law`, predicate `NoOddRelation`). Mechanism: reaching the floor means all phases `γ log n` sit near `π` mod `2π`; an odd relation forces `1 = e^{i·0} ≈ (−1)^{Σ c_γ} = −1` (unimodular product bound `norm_prod_zpow_sub_one_le`); conversely with all relations even, `γ ↦ π` extends to a homomorphism of the group generated by finitely many ordinates, which on the corpus's rationally independent integral basis (`exists_rat_independent_intSpanning`) is a torus target reached by the corpus Kronecker theorem (`kronecker_approx`), and Bohr almost periodicity plus the sharp interval bound move the lag to a large integer. Contrast with MUST-239: the ceiling `a_1` is the exact supremum with **no** Diophantine input, the floor `−a_1` is the exact infimum **exactly** under the parity condition. Linear independence of the positive ordinates (LI) implies the condition; the condition is strictly weaker than LI (it tolerates even relations). So the explicit sequence `a_n` sees the Diophantine structure of the zeros through its floor and nothing else: the ceiling is universal, the floor is arithmetic.

CANNOT-326 — **Route O is a receiver in every form; its exact open content is one one-sided prime-window inequality.** The fixed-pole, lag, integer-lag, Gram-matrix and mean-square forms of Route O are all Lean-equivalent to RH (MUST-236–241), and each reduces to the single statement: for all `X`, `√X·∫_X^∞ (ψ(t) − t + log 2π + ½log(1 − t^{−2})) t^{−2} dt ≥ −C` (the future prime deficit beyond `X`, averaged against `dt/t²`, is never large at scale `1/√X`), equivalently `Φ(L) ≤ a_1` with `Φ' − Φ/2 = (ψ(X) − X + c(X))/√X`. The prime side is a positive pole term `e^{L/2}(T − L) + …` minus a negative prime term `−√X(T − L + 1) − …` whose divergent parts cancel exactly and whose bounded remainder is `Φ`; RH is the statement that the remainder is bounded, and the ceiling `a_1` is tight along every geometric progression (MUST-239), so no argument that loses a constant can prove it. No known producer reaches the `√X` scale one-sidedly: sieves bound primes from above; exponential-sum zero-free regions give scale `X exp(−c(log X)^{3/5})`; mean-value theorems for the mean square `(1/T)∫_0^T Φ² → Σ_ρ|ρ(1−ρ)|^{−2}` (RH) need Dirichlet polynomials of length `e^T`, beyond every large-sieve regime. Positive survivors: MUST-238 (integer law, dichotomy), MUST-239 (universal ceiling), MUST-240 (`Ω±`, almost periodicity), MUST-241 (arithmetic floor). In prime language the two one-sided halves are: (bounded above) `Σ_{m≤n}Λ(m)(n/m − 1) ≤ n log n − (1+γ)n + log 2π − S(n) + a_1√n`, an upper bound on a manifestly positive prime sum, equivalently `∫_n^∞ (ψ(t) − t)t^{−2}dt ≥ −a_1/√n − O(1/n)` (future primes never too sparse); (bounded below) `∫_n^∞ (ψ(t) − t)t^{−2}dt ≤ M/√n` (future primes never too dense). Either half alone is RH. The only created prime-side positivity in the literature is de la Vallée Poussin's (`Λ ≥ 0` times a positive trigonometric polynomial on the Euler-product side `σ > 1`), which yields zero-free regions of width `1/log t`, i.e. scale `t·exp(−c(log t)^{3/5})`, and lower-bound sieves (GPY/Maynard) rest on Bombieri–Vinogradov whose errors are `N/log^A N`; neither reaches scale `√n`. Any further Route O work must supply a *new* one-sided bound for primes in `[X/c, cX]` at scale `√X`, not another equivalent form.

MUST-242 — [Lean] **The lag exponent is the whole distance to RH, and its unconditional value is `½` up to a subexponential loss.** Writing `Φ(L) = e^{θL}·(…)`, RH ⟺ `θ = 0` (MUST-236/238), any fixed-width zero-free region `β ≤ 1 − c` ⟺ `θ ≤ ½ − c`, and with no hypothesis `|Φ(L)| ≤ C e^{L/2} e^{−c L^{1/10}}` for large `L`, i.e. `|a_n| ≤ C √n e^{−c (log n)^{1/10}}` (`WeilLagFunctionFrontier.weilLagFunctionReal_frontier`, `integerLag_frontier`, `tendsto_weilLagFunctionReal_mul_exp_neg_half`), from the corpus's prime number theorem with error term through the quantitative Mertens deviation `Σ_{k≤x}Λ(k)/k − log x + γ = E(x)/x − ∫_x^∞ E(t)t^{−2}dt = O(e^{−c(log x)^{1/10}})` (`mertensDeviation_eq`, `mertensDeviation_bound`). So the certified state of the lag lane is: exponent `½` provable, exponent `0` is RH, and every intermediate exponent `½ − c` is a fixed-width zero-free region — the first genuinely new unconditional statement in this lane would be *any* exponent below `½`, which no analytic method reaches (the Borel–Carathéodory/3-4-1 mechanism yields widths `r/sup log|ζ|` that vanish along heights where `|ζ(1+it)|` is unbounded; the corpus's `BorelCaratheodoryCeiling` makes this exact: width `≪ 1/log log t`, never fixed). A producer for RH must therefore move the exponent by `½` at once; there is no known partial credit between `½` and `0`.

SOURCE-COMPRESSION-001 — [Lean: complete source comparison; paper: continuation] Cannot assume that preserving possible off-line zeros requires preserving every individual prime position. Group the ordinary primes in each interval `[k^4,(k+1)^4)`, `k>=2`, and replace them by the same number of copies of their geometric mean, retaining smaller primes. The full Euler-log discrepancy has the unconditional bound `(240|s|² exp(2|s|)+30) k^(1-4 Re(s))`; its sum is holomorphic for `Re(s)>1/2`, and the actual finite Euler quotients converge to a nonzero holomorphic multiplier there. Consequently, on paper, the compressed Euler product has a continuation with precisely the same zeros in this region. Must distinguish this controlled simplification from a zero-free estimate: cancellation in the retained prime counts and logarithmic means is still unproved. This comparison does not preserve an unchanged functional equation or fixed archimedean Weil form. Evidence: `quarticPrimeEulerDiscrepancy_bound`, `differentiableOn_quarticPrimeEulerDiscrepancySum`, `tendsto_quarticPrimeCompressionFinite`; [formal and paper scope](../../3-formalized/prime-log-block-compression.md).

MUST-243 — [Lean] **The interface any geometric producer must fill.** RH ⟺ the lag kernel `K(x,y) = Φ(log x − log y)` is positive semidefinite on the multiplicative group of positive reals ⟺ every arithmetic Gram matrix `(Φ(log(n/m)))_{n,m≤N}` is positive semidefinite (`WeilLagFunctionGram.riemannHypothesis_iff_lagGramKernel_posSemidef`, `riemannHypothesis_iff_arithmeticGramForm_nonneg`); under RH the quadratic form is `Σ_ρ (¼+γ²)^{−1} |Σ_x c_x x^{iγ}|²`, and the converse needs only the `2×2` minors on `{1, n}`, which are `2(a_1 − a_n)`. The entries `Φ(log(n/m))` are explicit prime sums at the rational point `n/m` (genus-kernel explicit formula), so this is a positive-definite kernel on the group of principal divisors of `Spec ℤ`. Consequently a geometric producer (Deligne/Weil-type) must supply an intersection pairing on the divisors of `Spec ℤ` whose regularised values are `Φ(log(n/m))` — Frobenius-graph pairings `(Γ_{log n}·Γ_{log m})` weighted by the archimedean genus kernel `1/(ρ(1−ρ))` — together with a Hodge-index inequality that is exactly `Φ(0) ≥ Φ(L)`, tight along every geometric progression (MUST-239). Any weaker positivity (a kernel that is positive only up to a constant, or only on a subgroup with a gap) does not reach RH: the kernel's `2×2` minors already carry the whole statement, and the ceiling has zero margin. On the zero carrier (functions on the zero copies, the corpus's Deninger `H¹` carrier) the same kernel is the Gram form of the Frobenius orbit `v_x(ρ) = x^{ρ−½}` under the reflection-twisted bilinear form `B(f,g) = Σ_ρ f(ρ) g(1−ρ)/(ρ(1−ρ))`: unconditionally `B(v_x, v_y) = Φ(log x − log y)` (`WeilLagFunctionCarrier.reflectForm_frobeniusVector`), and RH ⟺ `B ≥ 0` on the span of the Frobenius orbit (`riemannHypothesis_iff_reflectForm_nonneg`); under RH the reflection is complex conjugation and `B` is the Hermitian form `Σ_ρ |f(ρ)|²/|ρ|²`. So the geometric producer must make the reflection `ρ ↦ 1−ρ` act as a conjugation on a positive form — the Hodge-star/Frobenius compatibility of the corpus's Deninger gate — and its values on the Frobenius orbit are forced to be the explicit prime sums `Φ(log(n/m))`.

MUST-244 — [Lean] **Which lag sets carry RH.** Because the lag function is continuous, a one-sided bound on any lag set whose closure contains a half-line bounds `Φ` on the half-line and gives RH (`WeilLagFunctionDense.riemannHypothesis_of_bddAbove_on_dense`). The lags `k log p + l log q` of two distinct primes form a dense subgroup of `ℝ` (the logarithms of two primes are ℚ-independent by unique factorisation), so **RH ⟺ `Φ` is bounded above on the `{p,q}`-rationals `p^k q^l`** for any two distinct primes (`riemannHypothesis_iff_bddAbove_two_prime_rationals`): the values of the explicit prime-side function at the `{2,3}`-rationals alone decide RH. By contrast the lags of a single prime `m log p`, of the primes `log p`, and of an arithmetic progression `log n` (`n ≡ a mod q`) are closed discrete sets, so continuity gives nothing there; for a single base the converse is open (`b`-resonance, card §10), and for the primes it is open because the unconditional prime-gap bound `p^{0.525}` is far too weak for the interval bound `|Φ(L) − a_n| ≤ 3(log n+2)²/√n·(gap)` and the Landau route needs the logarithmic singularities of the prime zeta function at `ρ − ½ + ρ''/k`. So the discrete data that carry RH are exactly the lag sets that are dense in a half-line; sparse discrete lag sets carry RH only through a separate analytic mechanism, not through the values alone.

MUST-245 — [numerical, pod 2026-09-06; not Lean] **The finite Weil-positivity margin is of order `1/N`.** For the arithmetic Gram matrices `G_N = (Φ(log(n/m)))_{n,m≤N}` (RH ⟺ all `G_N ⪰ 0`, MUST-243) the least eigenvalue satisfies `λ_min(G_N)·N ≈ 0.084 → 0.089` for `N = 50 … 3200`, i.e. `λ_min ≍ 1/N`, relative size `≈ 2/N²` of the trace; the largest eigenvalues are `w_ρ N` for the leading zeros (`λ_max/N → 1/(¼+γ₁²)`), and the two-prime lattice forms behave the same way (`λ_min ≈ 0.07/dim`). The elementary cusp bound gives `λ_min ≤ (log N)/(2πN)`; the observed margin is smaller by `log N`, so nearby Frobenius vectors combine to remove the logarithm. Consequences: (i) any producer must deliver on the Frobenius span not just nonnegativity but a least eigenvalue `≍ 1/N`, a quantitative Hodge-index margin; (ii) an off-line zero at height `T` moves `G_N` by at most `N² log T/(πT)`, so finite Gram positivity below `N ≈ (T/log T)^{1/2}` is unconditional information about zeros only up to height `T`, and numerical PSD checks of the lag kernel can never outrun the verified zero-free height; (iii) the exact limit `λ_min·N → c*` is an open, falsifiable conjecture whose value would be a new spectral invariant of the zeros (compare Burnol's `a_1/log N` for the Báez-Duarte distance, a different scaling). Computation folder: `2-fully-proven/computations/lag-gram-margin/`.

MUST-246 — [Lean] **The local zero count is `≪ log t`, with no Gamma-function input.** For `|t| ≥ 4` at most `40·log(180|t|)` zero copies of `ξ` (counted with multiplicity) have ordinate within `1` of `t` (`ZetaLocalZeroCount.card_le_of_ordinates_in_window`). Mechanism: Jensen's inequality for `ζ` itself on the disc of radius `1.85` around `2 + it` (outer radius `1.95`), which contains every zero with `½ ≤ β` and `|γ − t| ≤ 1`, avoids the pole and needs no bound on `Γ`; the sphere bound is the Euler–Maclaurin representation at `N = 1`, `‖ζ(σ+it)‖ ≤ 3/2 + 1/‖1−s‖ + 2|t|/σ` on `0 < σ ≤ 2` (`norm_riemannZeta_le_strip`, from the vendored `Zeta0EqZeta`/`ZetaBnd_aux1`), and the centre bound `‖ζ(2+it)‖ ≥ 1/3`; multiplicities of `ζ` and `ξ` agree in the strip (`meromorphicOrderAt_xi_eq_zeta`, via `ξ = z(z−1)Γ_ℝ(z)ζ(z)/2`), and the reflection `ρ ↦ 1−ρ` moves the zeros with `β < ½` to the window at `−t`. Consequences: every argument that needs `N(t+1) − N(t) ≪ log t` (partial-fraction bounds for `ζ'/ζ` away from zeros, the prime-lag criterion, determinant comparisons) can now be run in Lean; the Gamma-vertical-decay and Phragmén–Lindelöf bricks are not needed for it, because Jensen on `ζ` in `Re s > 0` replaces Jensen on `ξ`. The constants `40`, `180` are crude and improvable; the `log` is sharp.

MUST-247 — [Lean] **`ζ'/ζ` is `≪ log t / δ` at distance `δ` from the zeros, from the corpus partial fraction alone.** For `½ ≤ σ ≤ 2`, `t ≥ 4` and `0 < δ ≤ 1` with every zero copy of `ξ` at distance `≥ δ` from `s = σ + it`: `‖ζ'/ζ(s)‖ ≤ (3700 + 5K₀)·log t / δ`, where `K₀` is the (finite) number of zero copies of height `≤ 6` (`ZetaLogDerivZeroDistance.norm_logDeriv_zeta_le`; `smallHeightCopies_finite` from the discreteness of the zero set and finiteness of the multiplicity fibres). Mechanism: the corpus explicit-formula partial fraction `logDeriv ξ(s) − logDeriv ξ(s₀) = Σ'_ρ ((s−ρ)⁻¹ − (s₀−ρ)⁻¹)` with anchor `s₀ = 3 + it`, the term bound `‖s₀−s‖/(‖s−ρ‖‖s₀−ρ‖) ≤ (5/2)/(max(δ,k)·max(2,k))` on the window `k = ⌊|t−γ|⌋`, the window count `≤ 80 log(180(t+k+1)) + K₀` (MUST-246 on both sides of `t`), and the telescoped tails `Σ_{k≥2} 1/k² ≤ 1`, `Σ_{k≥2} log(k+2)/k² ≤ 7`; the boundary pieces are `‖ζ'/ζ(3+it)‖ ≤ 2`, `‖1/s‖, ‖1/(s−1)‖ ≤ ¼` and the digamma bound `‖Γ_ℝ'/Γ_ℝ(σ+it)‖ ≤ log t + 2 + 2π + log 2` (corpus `norm_digamma_vertical_le_log`). No Gamma vertical decay, no Phragmén–Lindelöf, no zero-free region enters. Consequences: `Σ_ρ 1/(1+(t−γ)²) ≪ log t`, the Landau-type contour integrals of `ζ'/ζ` across the strip, the prime-lag assembly (MUST-244), and any Lean zero-density or explicit-formula-with-error argument can now use the standard `ζ'/ζ ≪ log t` input with explicit constants; the constant `3700 + 5K₀` is crude and the dependence `1/δ` is sharp (a single zero at distance `δ`).

MUST-248 — [Lean] **Single-base lag detection law: an attained off-line maximal real part is detected by every base.** For any integer base `b ≥ 2` and the geometric lag sequence `a_{b^m} = Φ(m log b)`: if the maximal real part `β₀ = max_ρ Re ρ` of the zero copies is attained and `β₀ > ½`, then `a_{b^m}` is unbounded above, with `a_{b^m} ≥ (c/2)·b^{m(β₀−½)}` along a sequence of exponents, `c = Σ_{Re ρ = β₀} Re(1/(ρ(1−ρ))) > 0` (`WeilLagFunctionSingleBase.exists_pow_integerLag_gt_of_attainedTop`). Hence (`riemannHypothesis_or_not_attained_of_forall_le`) **a bounded single-base sequence forces RH or a supremum of real parts that no zero attains**, and (`riemannHypothesis_or_infinite_offLine_of_forall_le`) **RH or infinitely many off-line zeros**. Mechanism: `Re(1/(ρ(1−ρ))) = (β(1−β)+γ²)/|ρ(1−ρ)|² > 0` for every copy (`lagWeight_re_pos`), so the top level carries positive real weight and cannot cancel; simultaneous Dirichlet approximation of finitely many top-level ordinates (corpus `exists_simultaneous_dirichlet`, scaled by `N` to reach arbitrarily large exponents) makes the top-level phase sum `≥ 5c/8`; the lower levels contribute `o(b^{m(β₀−½)})` by dominated convergence of the absolutely summable weights (`tendsto_lowerTail`) — no gap below `β₀` is needed. Consequences: (i) the single-base criterion `RH ⟺ sup_m a_{b^m} < ∞` (Route O lag front, "one-prime-orbit sufficiency") is open exactly in the regime where the real parts of the off-line zeros accumulate at their supremum without attaining it, a regime no known zero-density or Turán power-sum tool excludes; (ii) every "finitely many exceptional zeros" scenario (Siegel-zero-type, or any hypothetical single off-line pair) is excluded by boundedness along one geometric progression `b^m` — sparse arithmetic data at powers of `2` alone suffice against finitely many exceptions; (iii) compare the prime-lag criterion, whose Landau assembly is blind exactly at `Θ = 1` (notes): sparse lag sets detect off-line zeros only under an isolation condition on real parts, dense lag sets (MUST-244) need none.

MUST-249 — [Lean] **Shadow law: a bounded single-base lag sequence forces accumulation of zeros, modulo the base lattice, in the upward vertical shadow of every off-line zero.** Write `z_q = b^{ρ_q−½}` (`baseNode`). The sequence `a_{b^m} = Σ_q w_q z_q^m` is the coefficient sequence of the node series `Σ_q w_q/(1 − z_q t)`, and every node `1/z_q` is a genuine pole with residue of positive real part (aliased copies add, `lagWeight_re_pos`). If `|a_{b^m}| ≤ M` for all `m`, the generating function is analytic on the unit disc (`differentiableOn_lagGen`), so for every off-line copy `q₀` (`Re ρ₀ > ½`, hence `|1/z_{q₀}| < 1`) the segment from `0` to `1/z_{q₀}` must meet the closure of the other poles `{1/z_q : z_q ≠ z_{q₀}}` (`WeilLagFunctionShadow.exists_segment_mem_closure_shadowPoles`); otherwise the identity theorem along a convex tube around the segment forces the aliased weight to vanish (`not_bounded_of_clean_shadow`). In zero coordinates: zeros `ρ_q` with `ρ_q ≢ ρ₀ (mod 2πi/log b)` accumulate at some point of `{β ≥ β₀, γ ≡ γ₀ (mod 2π/log b)}`. Consequences: (i) together with MUST-248 (attained maximum), the single-base criterion `RH ⟺ sup_m |a_{b^m}| < ∞` is open exactly in the regime where the supremum of real parts is not attained and every off-line zero has a dirty shadow, i.e. the derived set of the zeros modulo the lattice contains a closed belt separating every isolated off-line zero from the pole-free region `β > Θ`; (ii) the only unconditional information on this derived set is Landau's equidistribution of `γ log b mod 2π`, which puts the belt at `β = ½` — below every off-line zero — so no known tool excludes belts above; (iii) any producer working with sparse lag samples must control this derived set, dense lag sets (MUST-244) need nothing. If every off-line copy has a clean shadow, single-base boundedness gives RH (`riemannHypothesis_of_forall_abs_le_of_clean_shadows`).

CANNOT-327 — [Lean] **A single-base lag criterion cannot be proved from the structural data of the zero side alone.** The single-base sequence `a_{b^m} = Σ_q w_q z_q^m` (`z_q = b^{ρ_q−½}`) carries only: positive summable weights, nodes accumulating at a top modulus `R = b^{Θ−½} > 1` from inside, and (when the supremum is not attained, MUST-248) no node of maximal modulus. These data do not force unbounded power sums: for every `R > 1` there is an explicit countable configuration of nodes of modulus `< R`, positive summable weights, moduli accumulating at `R`, and `|Σ_i w_i z_i^m| ≤ 1` for every `m ≥ 1` (`RingRecursionWitness.exists_positive_configuration_bounded_powerSums`); in the unit-disc normalisation the power sums are `≤ e^{−λm}` for any prescribed rate `λ > 0` (`exists_positive_configuration_powerSums_le`). Mechanism: ring `N` is the set of `N`-th roots of unity, rotated by `π/N` or not, at radius `e^{−5/√N}` with total weight `c_N`; its power sum at `m` is `c_N ρ_N^m (−1)^{s_N m/N}` if `N ∣ m` and `0` otherwise, so ring `m` is chosen by recursion over the proper divisors of `m` to cancel all earlier rings up to the positive seed `e^{−λm}`; the weights stay summable because `(ρ_N/ρ_m)^m ≤ e^{−2√m}` for every proper divisor `N ≤ m/2` and the seed costs `e^{5√m−λm} ≤ e^{25/(4λ)}`, giving `c_m ≤ K m e^{−2√m} + e^{25/(2λ)} e^{−λm/2}`. Consequences: (i) together with MUST-248/249, one-prime-orbit sufficiency (`RH ⟺ sup_m a_{b^m} < ∞`, Route O lag front) is exactly the statement that the zeros of `ξ` do not realise, modulo `2πi/log b`, such a ring-cancellation pattern; any proof must use arithmetic input about the zeros (location, count, weights `1/(ρ(1−ρ))` tied to heights, ordinate distribution), not positivity or summability; (ii) a producer built on a single geometric progression of lags is structurally impossible, in line with MUST-244: the producer must control a dense lag set or the full kernel; (iii) [analysis, not Lean] the known distributional facts do not bite either: placing ring `N` at heights `≍ N³` (ordinates `(π(s+2j)/N + 2πK_j)/log b` with `K_j` spread over a window of relative width `N^{−2}`) keeps the weights `1/(ρ(1−ρ))` nearly equal (relative deviation `N^{−2}`, which the recursion absorbs: adjacent rings feed back with ratio `≈ 1` but the total deviation `Σ_N c_N N^{−2}` is summable), respects the local count `N(t+1) − N(t) ≪ log t` (MUST-246), the Riemann–von Mangoldt density, and every polynomial zero-density bound `N(σ,T) ≪ T^{c(σ)}` (raise the height exponent), and the cancellation demands stay below the realisable weights by the factor `e^{−2√m}`; so a proof must use the Euler product or functional equation identities themselves, not counts, densities, or weights; (iv) the analogous obstruction for prime lags is the `Θ = 1` blind spot (notes, `integer-lag-law-notes.md`).

MUST-250 — [Lean] **One-sided exponential growth of the lag function forces a zero-free half-plane, and bounded prime lags force the strip `¼ ≤ Re ρ ≤ ¾`.** (i) If `Φ(L) ≤ M e^{aL}` for all `L ≥ 0` with `0 ≤ a < ½`, then every zero copy has `Re ρ ≤ ½ + a` (`WeilLagFunctionGrowth.re_le_half_add_of_weilLagFunctionReal_le_exp`): the nonnegative density `M e^{au} − Φ(u)` plus the measure `e^{au}du` has Laplace transform `(M+1)/(s−a) − G(s)` on `Re s > ½` (`G` the lag pole series), Landau's theorem pins the abscissa at `a`, so `G` extends analytically to `Re s > a`, and the pole `ρ − ½` of `G` (`re_le_half_add_of_lagPoleSeries_extension`, the extension theorem for a general half-plane) excludes `Re ρ > ½ + a`. (ii) The integer lags are Lipschitz over a gap: `|a_m − a_n| ≤ 8(m−n+1)(log m + 2)²/√n` for `n ≤ m ≤ 2n` (`WeilLagFunctionPrimeGap.abs_integerLag_sub_le`), hence `|Φ(L) − a_n| ≤ 11(⌊e^L⌋−n+1)(log 2n+2)²/√n` for `log n ≤ L`, `⌊e^L⌋ ≤ 2n`. (iii) With the corpus's unconditional Hoheisel theorem (a prime in `(z, z + z^{71/100}]` for large `z`) and Bertrand, every large `X` has a prime `p ≤ X` with `⌊X⌋ < p + p^{71/100}` (`exists_prime_short_gap`), so `a_p ≤ M` for all primes gives `Φ(L) ≤ M + 457776 e^{(23/100)L}`, hence `Φ(L) ≤ M₃ e^{L/4}` on `L ≥ 0`, and by (i): **`sup_p a_p < ∞ ⟹ ¼ ≤ Re ρ ≤ ¾` for every zero** (`re_le_three_quarters_of_primeLag_le`, `one_quarter_le_re_of_primeLag_le`). Consequences: the prime-lag data are not blind to zero-free strips (they are blind only to RH itself through the interval route); the Landau route for the prime criterion (notes) needed `Θ < 1` and now has it, so its assembly would give **`RH ⟺ sup_p a_p < ∞`** — an RH criterion in prime values only, `(p − ψ(p)) + p(M(p) − log p + γ) − log 2π + S(p) ≤ M√p`; any prime-gap exponent `θ < 1` suffices for (iii) with strip `Re ρ ≤ θ`; the Lipschitz law (ii) is the quantitative form of MUST-238's interval bound and shows that lag sets with gaps `≤ n^{θ}` decide the strip `Re ρ ≤ θ`, gaps `≤ √n · n^{o(1)}` decide RH.

MUST-251 — [Lean] **RH ⟺ the lag sequence is bounded above on the prime powers.** `riemannHypothesis_iff_primePowerLag_bddAbove : RH ↔ ∃ M, ∀ n, Λ(n) ≠ 0 → a_n ≤ M` (`PrimeLagLandauCriterion`), with `a_n = Φ(log n) = Σ_ρ n^{ρ−½}/(ρ(1−ρ))` real; under RH `|a_n| ≤ a_1 = 2+γ−log 4π`. Converse mechanism (no computation, no premise): put `Θ = sup Re ρ`; MUST-250 gives `Θ ≤ ¾` from the prime values alone. The Dirichlet series `Σ_n (M − a_n) Λ(n) n^{−1−s}` has nonnegative coefficients, converges on `Re s > Θ − ½` (`|a_n| ≤ W n^{Θ−½}`), and equals `M(−ζ'/ζ)(1+s) − Σ_ρ w_ρ (−ζ'/ζ)(s+3/2−ρ)` there (`PrimeLagLandauSeries.LSeries_lagCoeff_eq`; the interchange needs `Σ_ρ |w_ρ| log(2+|γ|) < ∞`, proved from MUST-246 dyadic windows in `PrimeLagLandauWeights`). The right side is analytic on the box `Θ−½−η < Re s < ¾`, `|Im s| < 3η` (far terms: MUST-247 `ζ'/ζ ≪ log t/δ`; near terms: finitely many, poles avoided since every zero has `|γ| ≥ 6η`; `PrimeLagLandauContinuation.differentiableOn_landauG`). Landau's theorem (corpus `landau_local_summability_transfer`) then forces convergence at the real point `Θ−½−η/4`, so the series is analytic on `Re s > Θ−½−η/4`. A zero `ρ₀` with `Re ρ₀ > Θ − η/8` of maximal real part on its horizontal line gives the ray `ρ₀−½+t`, `0 < t ≤ ¼`, on which the right side is `≥ ‖W₀‖/t − C` (`landauG_ray_lower_bound`: aliased weight `W₀ = Σ_{ρ=ρ₀} w_ρ` has `Re W₀ > 0`; residue of `−ζ'/ζ` at `1` via `tendsto_neg_logDeriv_riemannZeta_sub_one_div_real`; non-aliased near terms continuous on the closed segment; far tail bounded by the majorant); the real-analytic identity theorem along the ray and continuity of the series at `ρ₀−½` contradict. Consequences: (i) `¬RH ⟹ ∀ M ∃ prime power n, a_n > M` — a one-sided, prime-power-supported Ω-law, sharpening MUST-248/249 (which needed a base or a dense set); (ii) RH is equivalent to the single inequality on prime powers `(n − ψ(n)) + n(M(n) − log n + γ) − log 2π + S(n) ≤ M√n` (integer lag law, MUST-238) — a receiver: no positivity is produced, the theorem only certifies that the prime-power data see every off-line zero; (iii) the prime-power restriction is exactly what Landau needs (nonnegative coefficients weighted by `Λ`), and primes alone suffice once the `k ≥ 2` part (analytic on `Re s > Θ − 1`) is subtracted — not yet in Lean; (iv) the gap law of MUST-250 (gaps `≤ n^θ` decide `Re ρ ≤ θ`) plus this criterion locate the entire RH content of the lag sequence in its values at prime powers, i.e. in `ψ` and the Mertens sum at prime powers: **a proof of RH via lags must bound `a_{p^k}` above, and any such bound is a statement about `ψ(p^k) − p^k` and `Σ_{q ≤ p^k} Λ(q)/q − log p^k + γ` jointly at prime powers, with the `S(n)` boundary term.**

MUST-252 — [Lean] **For every `k ≥ 1`, RH ⟺ the lag sequence is bounded above on the `k`-th powers; what makes a lag subsequence decide RH is the analytic continuation of its counting Dirichlet series, not its gap size.** `PowerLagLandauCriterion.riemannHypothesis_iff_powLag_bddAbove (hk : 1 ≤ k) : RH ↔ ∃ M, ∀ m ≥ 1, a_{m^k} ≤ M`. Mechanism: the nonnegative series `Σ_m (M − a_{m^k}) m^{−k−u}` converges for `Re u > k(Θ−3/2)+1` and equals `M ζ(k+u) − Σ_ρ w_ρ ζ(u + 3k/2 − kρ)` (`PowerLagLandauSeries.LSeries_powLagCoeff_eq`); the zero-side sum converges locally uniformly wherever the arguments stay in `Re ≥ ½` at a fixed distance from `1`, by the corpus exponent-½ bound `‖ζ(w)‖ ≤ (4 + 1/d)√(‖w‖+2)` and the new summability `Σ_ρ |w_ρ| √(2+|γ|) < ∞` (`summable_lagWeight_mul_sqrt`: MUST-246 unit windows, `log(k+3)+2 ≤ 8k^{1/4}`, majorant `16(240+K₀)k^{−5/4}`); every pole `kρ − 3k/2 + 1` has imaginary part `kγ ≠ 0`, so a box of height below `k·min|γ|/2` around the real abscissa is pole-free and Landau (`landau_local_summability_transfer`) moves the abscissa left; the ray from the pole of a zero of maximal real part on its horizontal line carries `‖ζ(1+t)‖ ≥ 1/(2t)` (`exists_norm_riemannZeta_ge_inv`, from mathlib's `riemannZeta_residue_one`) times the aliased weight of positive real part (`powLandauG_ray_lower_bound`), against continuity of the series at the pole. Unlike MUST-251 no prime-gap input and no `Θ ≤ ¾` are needed: `ζ(kw)` has the single real pole `w = 1/k`. Consequences: (i) the `k`-th powers have gaps `≈ k n^{1−1/k}`; the Lipschitz/interval route of MUST-250 extracts from them only `Re ρ ≤ 1 − 1/k`, so **the gap law of MUST-250 is not the true law**; (ii) the true law, exposed by the proof: a subsequence `N` decides RH one-sidedly as soon as its counting series `F_N(w) = Σ_{n∈N} n^{−w}` continues meromorphically a little past its abscissa `α` with only real poles and vertical growth of exponent `< 1` — then `Σ_{n∈N}(M − a_n)n^{−1−s} = M F_N(1+s) − Σ_ρ w_ρ F_N(3/2 + s − ρ)` has its first singularities at the non-real points `ρ − 3/2 + α`, the real axis right of `α − 1` is regular, and Landau pushes the abscissa past a pole; bases `b^m` have `F(w) = 1/(1 − b^{−w})` with the non-real poles `2πij/log b` **on** the abscissa, which is exactly the shadow obstruction of MUST-249/CANNOT-327; (iii) therefore a lag-based route to RH may restrict to an arbitrarily sparse polynomial-type subsequence: for `N = {m^k}` the entire RH content is the one-sided inequality `a_{m^k} ≤ M`, i.e. `Φ(k log m) ≤ M`; the receiver/producer status is unchanged (visibility certified, no bound produced).

MUST-253 — [Lean] **The counting-function law is a theorem: any nonnegative weight whose generating Dirichlet series continues past its abscissa away from the real axis, with sub-linear vertical growth and a singularity on the real axis, gives a one-sided RH criterion.** `LagCountingFunctionLaw.LagWeightSystem`: data `c : ℕ → ℝ` (`c ≥ 0`), `F : ℂ → ℂ`, abscissa `α`, margin `η₀ > 0`, exponent `0 ≤ A < 1`, with (H1) `HasSum (term c w) (F w)` for `Re w > α`; (H2) `F` differentiable on `Re w > α`; (H3) for every `g > 0` a constant `C` with `F` differentiable and `‖F w‖ ≤ C(1+|Im w|)^A` on `α − η₀ ≤ Re w ≤ α + 2`, `|Im w| ≥ g`; (H4) `‖F(α + t)‖ → ∞` as `t → 0⁺`. Theorem `LagWeightSystem.riemannHypothesis_iff_lag_bddAbove : RH ↔ ∃ M, ∀ n, c n ≠ 0 → a_n ≤ M`. Proof: the series `Σ c(n)(M − a_n) n^{−s}` has nonnegative coefficients, converges for `Re s > α + Θ − ½`, equals `M F(s) − Σ_ρ w_ρ F(s − ρ + ½)` there (interchange by `Σ |w_ρ| Σ c(n) n^{−x} < ∞`), and the right side is differentiable on boxes avoiding the same-ordinate points by (H3) and the new `Σ_ρ |w_ρ| (2+|γ|)^A < ∞` for every `A < 1` (`summable_lagWeight_mul_rpow`, MUST-246 windows with `log(k+3)+2 ≤ (2/ε) k^ε`); Landau transfer; the ray from `α + ρ₀ − ½` (`ρ₀` maximal on its line) carries `‖W₀‖·‖F(α+t)‖ − C` with `Re W₀ > 0`, and (H4) contradicts continuity. Instances: `F = ζ(k·)` (`k`-th powers, MUST-252: (H3) from the exponent-½ bound, (H4) from `riemannZeta_residue_one`), `F = −ζ'/ζ` with `c = Λ` (prime powers, MUST-251: (H3) needs `Θ ≤ ¾` from MUST-250 to keep the zeros of `ζ` out of `Re w ≥ 1 − η₀`), `F = ζ` (`c ≡ 1`, the integer criterion). Predicted new instances: `c = 1_{primes}` with `F = P` (prime zeta; (H3) needs a `log ζ` bound in `Re w ≥ 1 − η₀` away from `w = 1`, again under `Θ ≤ ¾`; (H4) is the logarithmic singularity, which (H4) admits) — this would give **RH ⟺ sup_p a_p < ∞** in Lean; polynomial images of arithmetic progressions (Hurwitz zeta); any set whose counting series is a Dirichlet polynomial combination of such. Structural content: the RH content of the lag route is carried by every weight of this class; the only obstruction ever met is a non-real singularity of `F` on the abscissa (bases: `1/(1 − b^{−w})`), i.e. the shadow law; no positivity is produced.
