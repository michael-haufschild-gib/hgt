# The full signed escape Gram is forced by the cofactor kernel

- **ID:** the-full-signed-escape-gram-is-forced-by-the-cofactor-kernel
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** Q-III actual signed-data classification.
- **Lean status:** Full signed table and normalized fixed traces passed Lean with
  standard axioms. Promoted to
  `ArithmeticDefectRigidity/TheSignedCofactorGramHasNoExtraCoordinates.lean` and
  wired; final source-only check passed. The existing moving residual-operator
  comparison passed its transitive axiom audit too.

## Statement

Let `A` be the actual damped Möbius receiver, `R` its power-subtracted
cofactor residual, and `F=A+R` the forcing remainder. Along every escaping
common cofactor-Gram subsequence with limit `K`, the joint normalized Gram
table of the fixed dilates of `A`, `R`, and `F` has blocks

```
       A    R    F
A      K   -K    0
R     -K    K    0
F      0    0    0.
```

Thus in the completed actual module, each fixed residual cofactor is `-v_j`
and each fixed forcing-remainder cofactor is zero. The source-defined signed
table exists along the same subsequence; no second compactness choice is
needed. This identifies the normalized signed table, not the unbounded
moving cofactor sum before its boundary power has been removed.

## Dependency-closed paper proof

The existing exact inversion law gives `R(n)=F(n)-A(n)` for every positive
cell, and all three source rows vanish at zero. The existing forcing estimate
gives `||F||_T<=B_epsilon` for all horizons. Sharp pronic dilation therefore
gives `||D_jF||_T<=B_epsilon/sqrt(j)`, while
`||D_jA||_T<=sqrt(E_T/j)`.

Cauchy–Schwarz bounds each normalized mixed forcing/receiver covariance by
`B_epsilon/(sqrt(j*k)*sqrt(E_T))`, and each forcing/forcing covariance by
`B_epsilon^2/(sqrt(j*k)*E_T)`. Both tend to zero on escape. Expand each
residual entry using `D_jR=D_jF-D_jA`; the stated blocks follow from convergence
of the original cofactor table. Complexification preserves these identities.
The Gram realization then identifies residual vectors with negatives of
receiver vectors and forcing vectors with zero vectors.

At the pole-trace level, the already proved exact source formula gives
`trace(D_jA)=j^(epsilon-1)*forcingPowerCoefficient(epsilon)`. Consequently every
fixed trace divided by `sqrt(E_T)` also tends to zero on escape. The unscaled
trace remains nonzero and fixes the subtraction coefficient. There is no
claim that this source trace extends continuously to the escape Hilbert space.

The existing bounded residual/dilation commutator shows that applying the
source renormalized-residual operator before or after dilation has the same
normalized limit, even with a dilation index depending on the horizon.
`admits_or_moving_cofactor_commutator_vanishes` proves this directly. Thus the
operator realization of the residual has the same fixed signed Gram blocks
as direct dilations of `R`.

## Consequence and limit

The complete fixed signed Gram table and normalized fixed pole traces add no
new Hilbert coordinates beyond `K`. Any further arithmetic exclusion must
retain information beyond those limiting coordinates: the moving cofactor
relation, its unscaled trace, a finer normalization, or additional source
constraints. This does not show that arbitrary positive kernels are actual
Möbius limits and does not prove Kronecker-curve generation.

## Dependencies checked in source

- `TheForcingSplitsIntoAPowerAndAnAdmittedRemainder`: exact inversion and
  horizon-independent forcing budget.
- `TheRenormalizedCofactorIsAntipodalOnEscape`: receiver-residual signed pairing
  and total-variation estimates.
- `FixedCofactorsHaveAHarmonicBoundaryTrace`: invariant absolute trace domain
  and exact dilation trace.
- `CofactorRenormalizationHasABoundedDilationCommutator`: paid commutator.
- `TheCofactorLimitCarriesACyclicDilationAction`: every actual common kernel and
  its completed cyclic dilation module.

## Gates

- [x] Dependency-closed paper proof.
- [x] Verify the joint covariance limits using the existing zero-origin facts.
- [x] Formalize normalized trace vanishing and residual-operator comparison.
- [x] Audit axioms, check leaf source, wire umbrella.

The final source-only check of `TheSignedCofactorGramHasNoExtraCoordinates.lean`
passed. Its signed table and normalized trace theorems, together with the
existing exact commutator and moving normalized comparison, depend only on
`propext`, `Classical.choice`, and `Quot.sound`. No umbrella was compiled.
