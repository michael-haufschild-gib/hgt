# PW positive boundary regularization: three-moment no-go

## Claim

`[PW-B] [ROUTE-CLASS KILL] [LEAN-PROVED] [NOVELTY CANDIDATE]`

Proof chain under attack:

`conditionally regularized infinite PW Borel-grade interaction -> new global recoil invariant -> partner balance -> shared Ward extinction -> RH`.

Let `M_r(i,j)` be any boundary-regularization family of countable cross-grade matrices. Assume, eventually as `r -> 1-`, each `M_r` is moment-admissible and entrywise nonnegative, and its residual energies have finite limits at PW spectral coordinates `x=1,2,5` (the points `s=0,i,2i`). Then:

1. every residual-energy limit is one quadratic `A x^2 + B x + C`, uniquely reconstructed from those three samples;
2. `A,B,C >= 0`;
3. either `A=B=C=0`, so the regularized observable is identically blind, or its full recoil-energy limit vanishes on an actual Xi divisor exactly on the critical wall;
4. in the nonblind case, universal vanishing is equivalent to RH.

Thus no positive pointwise boundary regularization of moment-admissible countable PW matrices—including Abel/Cesaro/cutoff families—creates an infinite-grade invariant. Escape requires loss of a finite three-sample boundary value, signed/complex coupling, nonlinearity, or a genuinely singular non-pointwise operation.

## Corpus basis

- `schwarzschildParikhWilczekBorelGradeResidual_eq_coordinate_add_shift`: every grade is affine in one spectral coordinate.
- `schwarzschildParikhWilczekCountableMatrixResidualEnergy_three_moment`: every moment-admissible countable matrix is a quadratic in that coordinate.
- `schwarzschildParikhWilczekCountableMatrixCrossGradeEnergy_factorization`: full energy is wall factor squared times residual energy.
- `schwarzschildParikhWilczekBorelSpectralCoordinate_gt_one`: actual Xi support lies in `x>1`.
- Existing countable theorem explicitly leaves conditionally renormalized interaction as survivor; no corpus result passes a varying regularization family to its boundary.

## Paper proof

For fixed `r`, write

`P_r(x) = a_r x^2 + b_r x + c_r`.

At `s=0,i,2i`, the PW spectral coordinate is respectively `1,2,5`. Hence

`P_r(1)=a_r+b_r+c_r`,

`P_r(2)=4a_r+2b_r+c_r`,

`P_r(5)=25a_r+5b_r+c_r`.

Vandermonde inversion gives

`a_r = (P_r(5)-4P_r(2)+3P_r(1))/12`,

`b_r = (8P_r(2)-7P_r(1)-P_r(5))/4`,

`c_r = (15P_r(1)-10P_r(2)+P_r(5))/6`.

Therefore convergence of the three samples forces coefficient convergence to `A,B,C`, and polynomial continuity gives `P_r(x) -> A x^2+B x+C` for every spectral point.

Entrywise nonnegativity makes every `a_r,b_r,c_r` nonnegative because PW grade shifts are nonnegative. Closedness of `[0,infinity)` gives `A,B,C>=0`. If their sum is zero, all vanish. Otherwise, for `x>1`,

`A x^2+B x+C >= A+B+C > 0`.

The full boundary energy is consequently

`W(s)^2 (A x(s)^2+B x(s)+C)`.

On Xi support the second factor is positive in the nonblind case, while `W(s)=0` iff `Re(s)=1/2` because Xi ordinates are nonzero. This proves the dichotomy and RH equivalence.

## Novelty audit

Internal search found finite and absolutely summable three-moment classifications, but no boundary-family/Vandermonde rigidity or positive regularization dichotomy. Primary PW tunneling literature located conservation-law and entropy-correction expansions, not this Borel-grade boundary classification. External novelty remains candidate pending expert review.

## Formalization

Module: `GaloisForLFunctions.RHTower.ThetaCuspHawkingParikhWilczekPositiveBoundaryRegularizationThreeMomentNoGo`.

Closed capstone: `pwPositiveBoundaryRegularization_threeMoment_noGo`.

Verified by direct Lean check and target-only `lake build`. Axioms: `propext`, `Classical.choice`, `Quot.sound` only.

## Status

Paper proof and Lean formalization complete.

