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
