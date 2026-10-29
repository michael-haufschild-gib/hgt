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
