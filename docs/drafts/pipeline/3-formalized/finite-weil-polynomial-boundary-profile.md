# Finite Weil polynomial boundary profile

Status: FORMALIZED — three native leaves, all 20 declaration audits, and dependency checks passed.

## Objective

Classify boundary behavior of the normalized, fixed-degree polynomial approximations already verified in `WeilLogShiftPolynomialTiltApproximation`. Prove atomwise divergence exactly at zero target weights, identify the entire divergent polynomial, and obtain finite renormalized limits and leading logarithmic limits at every coefficient and evaluation point.

## Corpus evidence

- `FiniteLawPositiveApproximation`: Q_n=t_n U+(1-t_n)Q, t_n=1/(n+1), strict positivity, exact TV error.
- `WeilLogShiftPolynomialTiltRealization`: interpolation of log(Q_n(i)/base_i), exact node evaluation, distinct first coordinates.
- `WeilLogShiftPolynomialTiltApproximation`: actual normalized polynomial potentials and actual-measure TV convergence.
- Local Mathlib Lean: log continuity at nonzero values, log divergence, Lagrange interpolation as a finite-sum linear map, polynomial coefficient/evaluation sum formulas, and finite-sum convergence.

Documented corpus search `polynomial boundary` in WeilLogShift returned nine eligible declarations: seven on the different summability-domain boundary, the prior TV approximation root, and its nearby domain-weight definition. Project Lean source searches found no interpolated boundary-potential profile or interpolation-limit theorem. No external sources or computations.

## Dependency-closed paper proof

Write x_i for distinct canonical first coordinates, w_i>0 for base masses, and U_i>0 for uniform masses.

1. Q_n(i) tends to Q_i. For Q_i>0, continuity gives log(Q_n(i)/w_i) tending to log(Q_i/w_i).
2. If Q_i=0, Q_n(i)=U_i/(n+1), hence the exact identity log(Q_n(i)/w_i)=log(U_i/w_i)-log(n+1). This tends to minus infinity. Conversely, positive Q_i gives a finite limit, incompatible with minus-infinity convergence.
3. Let z_i be one if Q_i=0 and zero otherwise. Define b_i=log(U_i/w_i) at zero weights and log(Q_i/w_i) at positive weights. Then log(Q_n(i)/w_i)+log(n+1)z_i tends to b_i for every index.
4. Let Z_Q interpolate z_i and B_Q interpolate b_i, both of degree<r+1. Interpolation is a finite-sum linear map, so step 3 passes to every polynomial evaluation and coefficient: p_n+log(n+1)Z_Q tends to B_Q in both senses.
5. Divide by log(n+1), which tends to infinity. The bounded renormalized term divided by log(n+1) tends to zero; rearrangement gives p_n/log(n+1) tending to -Z_Q, pointwise and coefficientwise. The n=0 denominator is irrelevant because the algebraic rearrangement holds eventually.
6. Distinct-node evaluation proves Z_Q=0 iff every Q_i>0. Thus the target zero pattern exactly determines whether the logarithmic drift vanishes and which polynomial direction remains.

All final canonical-law roots quantify arbitrary r, k, and target Q without auxiliary assumptions. Positivity of actual base masses discharges every generic weight premise.

## Planned artifacts

- `HTGeometry/FiniteLawBoundaryLogProfile.lean`
- `HTGeometry/FinitePolynomialInterpolationLimits.lean`
- `RHTower/WeilLogShiftPolynomialBoundaryProfile.lean`

## Verification progress

- Native API audit passed after replacing the deprecated `tendsto_finset_sum` alias with `tendsto_finsetSum`; 26 local API signatures verified.
- `FiniteLawBoundaryLogProfile` passed with an empty native log. The log-growth composition needed an explicit natural-successor function type before simplifying casts; all three occurrences were corrected.
- `FinitePolynomialInterpolationLimits` passed with an empty native log. Its finite-sum argument was generalized to any field with continuous addition and multiplication, because no real-specific fact is used. This follows directly from the same dependency-closed paper proof: finite sums and fixed-scalar products preserve convergence.
- The actual canonical-law root passed with an empty native log after removing one unnecessary `simpa` warning. Both theorem-area umbrellas include the three new modules exactly once.
- Actual-root final audit passed: all 20 declarations (16 theorems, four definitions) use only `propext`, `Classical.choice`, and `Quot.sound`; no residual diagnostics. The scratch verifies 34 API bindings.
- Metadata audit passed: three fresh leaf objects, seven fresh direct import edges, and clean source whitespace.
- Repository lint snapshot: 367 warnings and ten unrelated unreachable modules: `RHTower.LocalRectangleArgumentBound`, `RHTower.PaperPrimeArchMaskedObservation`, `HTGeometry.L2PhysicalSolidObservation`, `HTGeometry.LpFiberMasks`, `HTGeometry.LpFiberObservation`, `HTGeometry.LpFiberSolidHull`, `HTGeometry.LpHilbertFiberMasks`, `HTGeometry.PaperGenealogyFiberDefects`, `HTGeometry.PaperGenealogyFiberObservation`, and `HTGeometry.PaperModulationPhysicalObservation`. No new-module lint errors.
- Final scratch and metadata/axiom checker are prepared at `/tmp/hgt-polynomial-boundary-profile-final-audit.lean` and `/tmp/hgt-polynomial-boundary-profile-audit.py`.

## Exact new insight

The zero-weight pattern determines the entire leading logarithmic direction of the normalized polynomial potentials. For every target law Q, all r and k, every real evaluation point, and every coefficient, `p_n/log(n+1)` tends to `-Z_Q`. Subtracting this drift gives the finite polynomial profile B_Q. The drift vanishes exactly in the strictly positive simplex, and atom evaluations tend to minus infinity exactly at zero target weights. These are properties of the same fixed-degree, partition-one potentials whose actual tilted laws converge in TV.

## Next conjecture, not proved here

Since Z_Q has node values zero or one, it should be idempotent modulo the nodal polynomial N: `N ∣ Z_Q^2-Z_Q`. A stronger candidate classifies every possible drift polynomial: `p=Z_Q` for some probability law Q iff `degree(p)<r+1`, `N ∣ p^2-p`, and `p≠1`. The exclusion of one records that a probability law has at least one positive atom. Search the local corpus and audit a dependency-closed paper proof before formalization; neither classification nor novelty is claimed here.
