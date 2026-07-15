# Formal core of the finite-jet projective-horizon Page transition

- **ID:** `projective-horizon-page-transition-core`
- **Stage:** 3-formalized
- **Type:** LEAN THEOREM PACKAGE
- **Scientific status:** `[FORMALIZED] [AXIOM-CLEAN] [NOVELTY PROVISIONAL]`
- **Paper theorem:** `projective-horizon-finite-jet-page-transition`
- **Module:**
  `formal/GaloisForLFunctions/HTGeometry/ProjectiveHorizonPageTransition.lean`

## Formal result

For every row shift `n` and window size `r`, Lean proves

```text
det (choose(n+i,k))_(i,k in Fin r) = 1
```

and hence

```text
det (-choose(n+i,k))_(i,k in Fin r) = (-1)^r != 0.
```

The negative matrix is the exact reciprocal-jet linearization minor at the formal jet
`X(t)=exp(-t/2)`, since `d(X^-1)=-X^-2 dX` and `X^-2=exp(t)` there. The nonzero determinant is the
certificate that any consecutive reciprocal packet detects the maximum possible number of low raw
jet directions.

Lean also proves the finite-resolution arithmetic law. With

```text
ambient   = N+1,
raw count = N+1-m,
inv count = N+1-n,
rank      = raw count + min(m,inv count),
```

the rank equals the smaller of ambient and total observable count. Consequently

```text
ambient-rank     = m+n-(N+1),
observable-rank  = (N+1)-(m+n),
```

using truncated natural subtraction. These are precisely the hidden-source and compatibility-
relation branches of the paper theorem, and both vanish at the critical order `N=m+n-1`.

For the higher-rank chart transition `(p,u) -> (p^-1,u/p)`, Lean additionally proves the weighted
Pascal identity

```text
det(choose(n+i,k) q^(n+i-k)) = q^(rn)
```

and the exact longitudinal determinant `(-1)^r 2^(rn)`. Together with the unweighted transverse
blocks, this is the determinant core of the projective-dimension capacity law.

## Main declarations

```text
shiftedPascalMatrix_det
reciprocalJetLinearizationMinor_det
reciprocalJetLinearizationMinor_det_ne_zero
exponentialPascalMatrix_det
projectiveLongitudinalLinearizationMinor_det
projectiveLongitudinalLinearizationMinor_det_ne_zero
finiteHorizonObservationRank_eq_min
finiteJetAmbientCount_sub_observationRank_eq_hidden
finiteHorizonObservableCount_sub_rank_eq_relations
finiteHorizon_page_balance
finiteHorizonHiddenCount_at_page
finiteHorizonRelationCount_at_page
```

## Verification

The targeted leaf build

```text
lake build GaloisForLFunctions.HTGeometry.ProjectiveHorizonPageTransition
```

passes. A scratch `#print axioms` audit reports only `propext`, `Classical.choice`, and
`Quot.sound`. No full project build was run.

## Boundary

The Lean module certifies the decisive Jacobian minor and the exact rank bookkeeping. The passage
from a nonzero characteristic-zero Jacobian minor to transcendence degree is the standard Jacobian
criterion and is retained in the paper proof. This card does not claim that derivative resolution
is physical time, nor that the unmarked horizon law selects the zero divisor needed for RH.
