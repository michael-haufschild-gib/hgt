# Arithmetic zero minimum classes and their exact mean

- **ID:** ARITHMETIC-ZERO-MINIMUM-CLASSES
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), [BRIDGE]; finite-label RH exclusion remains open
- **Source:** [frozen conjectures, paper proofs, failures, and remaining problem](../1-in-progress/arithmetic-zero-minimum-classes.md)

## Definitions and scope

For the actual ordinary power-sum error and deletion remainder,

`R_s(n)=sum_(k=1..n)k^(-s)-zeta(s)-n^(1-s)/(1-s)-n^(-s)/2`,

`W_p=p^(1-s)sum_(n>=1)n^(-s)conjugate(R_s(pn))`,

put `u=conjugate(s)`, `b_p=Re(mu(p)W_p/[p u(u+1)])`, and `P_a(p)=p^(a+1)b_p`.

The first profile is `X=P_1`; the second is `Y=P_(4 Re(s)-1)`. Lean proves their literal arithmetic forms

`X_p=p Re(mu(p)W_p/[u(u+1)])`,

`Y_p=Re(mu(p)W_p/[u(u+1)])/[p |p^(-s)|^4]`.

Neither definition branches on zero location. A profile's label is the least positive integer attaining a negative global minimum, or a separate nonattainment label. Lean encodes that separate label by `0`; it is not the profile value at index zero. The arithmetic class is the pair of labels. Ties and nonattainment are included exactly.

## Proved mathematical content

1. Every complex exponent has exactly one arithmetic class; no zero assumption is used for coverage.
2. At a zero with `0<sigma=Re(s)<1`, every weighted profile has the same absolutely convergent negative balance:

   `sum_(p>=1)P_a(p)/p^(a+1)=-Re(1/[u(1-u)])/2<0`.

3. The actual bound is `|P_a(p)|<=[sum_(n>=1)n^(-2 sigma-1)]/(sigma+1) p^(a-2 sigma)`. Thus `P_a` decays if `a<2 sigma`. Every strict-right zero has a finite first label; every strict-left zero has a finite second label. A zero with both labels zero lies on the critical line.
4. Every positive label is squarefree. On the critical line, the two profiles and therefore their labels agree.
5. With `S2=sum_(p>=1)1/p^2<=2`, every lower bound `b` on `X` obeys `b S2<=-Re(1/[u(1-u)])/2`. This applies in particular to the minimum value of each attained class.
6. Every critical-line zero has a positive modulus satisfying

   `X_p < -S2/[8(t^2+9/4)]`, where `t=Im(s)`.

The last claim is a symbolic consequence of the exact mean and a telescoping reciprocal-square bound. It uses neither a computed zero nor a numerical inequality involving pi. Matching this threshold to the limiting lower boundary and concluding critical-line minimum attainment are now formalized in [the global audit](arithmetic-global-minimum-classes.md), which also determines the coarse labels at every parameter in either open half-strip, including nonzeros.

## Lean certificate

Module: `GaloisForLFunctions.RHTower.ArithmeticZeroMinimumClasses`.
Namespace: `RHTower.DeletionMixedRefinement`.

| Claim | Declaration |
|---|---|
| Literal arithmetic definitions | `rightMinimumProfile_eq`, `leftMinimumProfile_eq` |
| Unique exhaustive coverage | `existsUnique_arithmeticMinimumClass` |
| Absolute weighted admission | `summable_minimumProfile_div_weight` |
| Exact zero-specific balance | `tsum_minimumProfile_div_weight_at_zero` |
| Strict negativity | `minimum_boundary_neg` |
| Height-independent profile envelope | `abs_minimumProfile_le` |
| Decay | `tendsto_minimumProfile` |
| Strict-right / strict-left confinement | `rightMinimum_attained_at_strict_right_zero`, `leftMinimum_attained_at_strict_left_zero` |
| Both nonattained labels force the line | `re_eq_half_of_arithmeticMinimumClass_zero_zero` |
| Positive-label support | `squarefree_of_negativeMinimumClass` |
| Class-specific minimum constraint | `attained_rightMinimum_mean_bound` |
| Critical-line finite undershoot | `exists_rightMinimumProfile_below_critical_boundary` |
| Equal labels on the line | `arithmeticMinimumClass_labels_eq_on_line` |

The generic minimum lemma explicitly states decay and existence of a negative entry. The zero-specific applications prove both from the actual arithmetic source. No unknown analytic estimate or class-exclusion principle is assumed.

## What remains unproved

The finite minimum classes have not been excluded at off-line zeros. In particular, equality of the two profiles on the critical line cannot be used to establish equality at an arbitrary zero. Coverage and the arithmetic mean do not fill that gap. No theorem in this module proves RH or states an RH implication with the missing class-exclusion law supplied as an extra premise.

[Runpod diagnostics](../2-fully-proven/computations/arithmetic-zero-minimum-classes/REPORT.md) reject two proposed producer principles. Those numerical results are separate from the Lean certificate.

## Verification

The complete scratch source and the published source passed `lake env lean`. The final serialized `LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.ArithmeticZeroMinimumClasses` audit passed. The leaf is wired into `GaloisForLFunctions.RHTower`; no full or umbrella build was run.

All 34 public declarations (25 theorems and 9 definitions) were audited with `#print axioms` in a separate scratch file. Their only reported axioms were the standard Lean foundations `propext`, `Classical.choice`, and `Quot.sound`; no added mathematical axiom or computational certificate was used. The corpus index was refreshed, and `scripts/formal_tools.py lint --check-generated` passed with exit code 0. All owned Lean and Runpod experiment processes completed; the remote cleanup check found no experiment processes remaining.
