# Exact Gram completion and cyclotomic radical of arithmetic curvature

Status: formalized. Targeted Lean checks passed.

## Mathematical result

For primitive-root prefix energy E_m and natural indices i,j, the kernel
K_m(i,j) = (E_m(i)+E_m(j)-E_m(dist(i,j)))/2
is the actual real Gram kernel of the geometric prefixes at primitive m-th roots.

Its full quadratic form on an arbitrary finite real packet is the sum of squared norms of the weighted primitive prefixes. The raw distance kernel is conditionally negative, with the exact value minus twice that square energy on zero-total-mass coefficients.

If P(X) is the packet's prefix polynomial, completed energy is zero exactly when Phi_m divides P over the real polynomial ring. For a finite conductor family the radical is the intersection of these divisibility conditions.

## Positive survivor

Scalar arithmetic positivity alone cannot be used as positivity of the uncentered translation kernel. The precise replacement is an actual positive Gram completion retaining all mixed entries, with a completely classified algebraic radical. The cyclotomic norm floor gives uniform separation of distinct prefix classes, but does not remove packet relations.

## Lean declarations

TheArithmeticCurvatureHasAnExactGramCompletion.lean:
- primitiveRootPrefixEnergy_dist_eq
- primitivePrefixGram_eq_sum_inner
- primitivePrefixGram_quadratic_eq
- primitivePrefixGram_quadratic_nonneg
- primitiveRootPrefixEnergy_conditional_quadratic_eq
- arithmeticOverlapCurvature_natCast
- totient_le_primitive_prefix_distance

CyclotomicDivisibilityClassifiesTheOverlapGramRadical.lean:
- primitivePrefixGram_quadratic_eq_zero_iff_cyclotomic_dvd
- primitivePrefixGram_family_eq_zero_iff

Both files are in formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory and wired into that programme umbrella.

## Validation

First module checked and its olean generated solely for the new importing modules. Second module passed direct lake --old env lean. Printed capstone dependencies contain only propext, Classical.choice and Quot.sound. No numerical experiments, new assumptions, or full builds.

## Limits and continuation

This is a finite arithmetic operator theorem. It is not an identification with the complete Weil overlap operator. Continued work is tracked in ../1-in-progress/astra-cyclotomic-affine-overlap-comparison.md: conductor completion, actual source comparison, rational refinement and the remaining complete-form transfer.

## Conductor completion

`AllDivisorConductorsRecoverTheDiscreteBridge.lean` is certified. Summing primitive energies over all orders dividing Q gives the full root energy. Removing order one gives `k*(Q-k)` for k<=Q; centering gives the exact mixed kernel `Q*min(i,j)-i*j`. Its quadratic form is nonnegative for arbitrary real coefficients and every finite family of prefix lengths in [0,Q]. Both printed capstones use only the standard axioms listed above. The module is wired into the CACT umbrella.

This completes omitted cyclic frequencies. It does not assert coercivity for a single primitive order, nor a comparison with the full Weil source.

## Actual prime-source comparison

`PrimeResidueWindowsControlEveryGramPacket.lean` is certified and wired into CACT. One residue-error mass tends to zero and controls every signed pattern, hence every finite real or complex Gram packet, uniformly over feature families and coefficients chosen after the height.

A stronger one-sided result is also certified: actual prime-window Gram forms dominate `(log B-log A-epsilon)` times their unit-mean Gram, at one common fixed-conductor horizon. Non-unit prime powers contribute nonnegatively and impose no extra penalty in this lower bound. The full residue norm remains necessary for the stated absolute error estimate. All five printed capstones use only the standard axioms.

These are actual source theorems, including prime powers. They do not identify the completed Weil correction with the Gram packet, and give no growing-conductor rate.

## Positive conductor lift under rational refinement

`RationalRefinementCompletesTheCyclotomicGram.lean` passed Lean with standard axioms only. For m>1, L>0,

`L² A_m(k/L) = sum_{e | mL, e/gcd(e,L)=m} E_e(k)`.

The same equality holds for every mixed entry of the centered Gram. Möbius inversion after dilation has only coefficients zero and one. Hence every finite rational-grid quadratic form is nonnegative for arbitrary real coefficients. Finer resolution adds primitive conductors; it does not preserve the original finite feature dimension. The module is wired into CACT. A final direct audit will include removal of an unreachable tactic.

## Real-variable extension

`TheRealOverlapCurvatureIsConditionallyNegative.lean` passed its final direct audit with only the standard axioms. Continuity and common rational-grid approximation prove `arithmeticOverlapGram_quadratic_nonneg` for every finite family of nonnegative real positions. Translation gives `arithmeticOverlapCurvature_conditional_quadratic_nonpos` for arbitrary real positions and zero-total-mass coefficients. On the first unit cell, `arithmeticOverlapGram_unit_cell` identifies the kernel exactly as `phi(m)*min(x,y)`.

The module is wired into CACT. This is arithmetic-kernel positivity; the actual signed complete Weil comparison remains unresolved.

## Literal prime-prefix specialization

`ActualPrimePrefixesDominateTheirCyclotomicGram.lean` passed its final direct audit with only the standard axioms. `primeClassKappa_arithmeticPrefixResidueEnergy` identifies the exact unit mean with the complete primitive Gram divided by the totient. `eventually_actualPrimePrefixGram_dominates` transfers that identity to the literal von Mangoldt source, uniformly over all finite real coefficient packets and all prefix lengths, including height-dependent choices. The conductor and multiplicative window remain fixed. The module is wired into CACT.

The complete Weil form subtracts its non-ratio prime term; this auxiliary lower bound does not supply the missing complete-form comparison.

## Moving affine parameters

`ActualAffinePrimeWindowsAreUniformInTheirParameters.lean` proves `eventually_affineRamanujanPrimeWindow_uniform`. One horizon controls both affine parameters simultaneously at fixed conductor and multiplicative window. The residue-pattern norm is bounded by `q*phi(q)`; applying the common source estimate at tolerance `epsilon/(q*phi(q))` proves the result. Its final direct audit passed with only the standard axioms. The module is wired into CACT.

## Exact prime-block identity

`CyclotomicCompletionIsThePrimeBlockJumpEnergy.lean` proves `completedCyclotomicGram_eq_primePacketJumpEnergy`. For a prime-supported packet below `Q`, the full divisor-conductor Gram equals

`Q * sum_{n<Q} primePacketJumpSum(S,a,n)^2 / (n*(n+1))`.

Proof: interchange the finite sums, apply the completed mixed kernel `Q*min(p,q)-p*q`, and use the existing exact pronic jump-energy identity. No moment cancellation hypothesis is required. The capstone passed Lean with only the standard axioms; an unused trailing tactic was removed before the final audit. The module is wired into CACT.

## Closure of the existing synthesis proof

`TransMetzlerWeilPositivity/TheFixedProfileReachesAnIteratedLogEndpoint.lean` proves `overlapGrowthSuperGevrey_endpoint`, `endpointSuperGevreyRatio_isLittleO`, and `riemannHypothesis_iff_steklovDCProfile_nonneg_endpoint`.

Put `L=log(log N)`, `u=log L`, and `c=L*u^2*log u`. Eventually `1<=c<=L*u^3`, so the existing cubic schedule gives `N/c -> infinity`. Since `N/c<=N`, monotonicity of the iterated logarithms bounds the receiver's denominator at `N/c` by `L*u^2`. Its growth quotient is therefore at least `log u -> infinity`. Finally, `c/(L*u^beta)=log u/u^(beta-2) -> 0` for every `beta>2`. The already constructed Steklov profile discharges every profile input in the existing receiver theorem.

Both printed capstones passed Lean with only the standard axioms. Two unused trailing tactics were removed before the final audit. The module is wired into the TransMetzlerWeilPositivity umbrella. This closes an existing paper proof; it is not a positivity result for the actual arithmetic form.
