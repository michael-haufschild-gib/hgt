# Gamma unit translation has exactly rank-one clock curvature

- **ID:** `gamma-rank-one-clock-curvature`
- **Stage:** 3-formalized
- **Type:** CONCRETE HT SOURCE FIELD / FINITE-RESOLUTION CURVATURE THEOREM
- **Scientific status:** `[LEAN-FORMALIZED] [EXACT MODEL THEOREM] [NOVEL INTERPRETATION PROVISIONAL]`
- **Parents:**
  - `../1-in-progress/calibrated-clock-curvature-class.md`
  - `../1-in-progress/constraint-curvature-integration-stack.md`
- **Statement:** The canonical finite Taylor shadows of unit translation have exactly rank-one
  incompatibility across every positive clock truncation, and their compressed action on the new
  highest-jet boundary is exactly the identity. The boundary vector is the factorial tail of the
  infinite periodic conormal.

## Finite shadows

Let `O_N=C^N` record raw derivatives `a_0,...,a_(N-1)`. The canonical finite unit-translation
shadow is

```text
(E_N a)_i=sum_(j=i)^(N-1) a_j/(j-i)!.                    (1)
```

Let `p_N:O_(N+1)->O_N` forget the highest derivative. Define

```text
kappa_N=p_N E_(N+1)-E_N p_N.                             (2)
```

## Exact curvature theorem

Cancellation of every retained Taylor coefficient gives

```text
kappa_N(a)_i=a_N/(N-i)!,             0<=i<N.             (3)
```

Define

```text
v_N=(1/N!,1/(N-1)!,...,1).                               (4)
```

Then

```text
kappa_N(a)=a_N v_N,                                      (5)
range(kappa_N)=C v_N,                                    (6)
rank(kappa_N)=1,                       N>=1.              (7)
```

Thus the whole finite-shadow incompatibility is the outer product of top-jet evaluation with one
boundary vector. The transpose vectors `(4)` are the finite tails of the already-formalized
infinite Taylor conormal

```text
nu(h)=sum_(n>=1) h^(n)(0)/n!=h(1)-h(0).                  (8)
```

Equations `(3)`--`(8)` identify one exact source mechanism:

```text
finite translation curvature
  = exposed factorial boundary line
  -> accumulated analytic translation conormal.          (9)
```

Let

```text
b_N=1-i_N p_N                                             (10)
```

be the projector onto the new highest-jet line, where `i_N` appends zero. The missing boundary
self-symbol is also exact:

```text
b_N E_(N+1)b_N=b_N.                                       (11)
```

Thus the Gamma-model colligation has factorial outgoing transfer and unit internal boundary
symbol. Equation `(11)` is Lean-formalized.

## Lean declarations

`GaloisForLFunctions.HTGeometry.GammaPeriodicConstraintCorona` contains:

- `gammaClockTranslationCoefficient`;
- `gammaClockTranslation`;
- `gammaClockTruncate`;
- `gammaClockCurvature`;
- `gammaClockCurvature_apply`;
- `gammaClockBoundaryVector`;
- `gammaClockCurvature_eq_outerProduct`;
- `range_gammaClockCurvature`;
- `gammaClockBoundaryVector_ne_zero`;
- `finrank_range_gammaClockCurvature`.
- `gammaClockExtendZero`;
- `gammaClockTranslation_extendZero`;
- `gammaClockBoundaryProjector`;
- `gammaClockBoundaryProjector_apply_last`;
- `gammaClockBoundaryProjector_apply_castSucc`;
- `gammaClockBoundaryCompression_eq_projector`.

The module's existing object cache was reused. The touched source passed one direct Lean check; no
build was run for this extension.

## Scientific boundary

Finite Taylor translation, cancellation, and a rank-one outer product are elementary. Low
displacement rank is established structured-matrix theory. The theorem is not claimed as new for
linear algebra.

The translation matrices, factorial transfer, and unit boundary symbol are universal jet
kinematics; none depends on Gamma. They therefore cannot by themselves be an HT source invariant.
This is a source-specificity no-go.

The positive interpretation is sharper: they form a canonical integrable vacuum colligation over
which Gamma supplies a distinguished affine source section, period-one tangent, and periodic
conormal. The source field must couple this universal colligation to Gamma's descent anomaly rather
than identify the kinematics with the source.

It does not prove a nonzero obstruction. The forward-compatibility theorem proves algebraic
Ind-integrability: unit-translation shadows commute exactly with zero-extension. Gamma's analytic
unit translation should integrate this field uniquely after affine normalization; that stronger
source-topological theorem remains open.

## Gates

- [x] finite translation shadow defined
- [x] exact curvature coefficient proved
- [x] outer-product factorization proved
- [x] exact range line proved
- [x] rank-one theorem proved at every positive resolution
- [x] exact compatibility with forward zero-extension proved
- [x] exact unit boundary self-symbol proved
- [x] factorial vector matched formally to the coefficients used by the infinite conormal
- [ ] global analytic integration map constructed
- [ ] unique normalized Gamma primitive proved
- [ ] source-presentation invariance proved
