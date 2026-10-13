# Finite Weil maximal power-covariance determinant

Status: formalized and verified, 2026-10-12. Increment complete; corpus research continues.

## Exact statement

For `r,k : Nat`, real `a,b,d`, let `z_i` be the existing canonical fluctuation
points and `x_i=z_i(0)`. Put

`w_i = edgeMass_i * exp(Q(z_i)) / sum_j edgeMass_j * exp(Q(z_j))`.

Then the covariance matrix of `(X,X^2,...,X^r)` under the actual quadratic tilt
has determinant

`det(Vandermonde(x))^2 * product_i w_i`.

This includes `r=0` and imposes no subcriticality or schedule on `k`.

The support geometry can also be made independent of `k`: the squared
Vandermonde factor equals

`product_i product_{j>i} ((j-i)^2 / (r+1))`.

Thus the only dependence on depth and tilt lies in the product of atom weights.

## Prior local Lean evidence

- `HTGeometry.FiniteModalHankelRank` already proves the uncentered finite modal
  Hankel determinant formula over a commutative ring. Reuse this exact theorem.
- `WeilLogShiftFinitePowerThreshold` and `WeilLogShiftPowerCovarianceRank` prove
  the rank and determinant sign, not the determinant's value.
- `WeilLogShiftQuadraticTiltLaw` and `WeilLogShiftObservableLaw` give the exact
  normalized finite sum for every real observable.
- The three-atom Gibbs collision determinant is a fixed-size example; it does
  not supply arbitrary-rank centered covariance.
- Local source searches for covariance/determinant declarations and centered
  moment matrices found no existing general centered-moment determinant bridge.
  No external novelty claim is made.

## Closed paper proof

For any sequence `s` over a commutative ring with `s(0)=1`, subtract `s(i)` times
row zero from each positive row of the `(r+1)`-square Hankel matrix. Determinant
is unchanged. Column zero is now `(1,0,...,0)`, and the remaining block has
entries `s(i+j+2)-s(i+1)*s(j+1)`. Expand along column zero. Thus this centered
block has the original Hankel determinant.

Take `s(n)=sum_i w_i*x_i^n`. Normalization gives `s(0)=1`. Apply the existing
finite modal Hankel determinant theorem, giving squared Vandermonde determinant
times the product of weights. No positivity or distinctness is needed for this
algebraic identity.

For the stronger explicit-support formula, the existing point definition gives
`x_j-x_i=(j-i)/sqrt(r+1)`. Since `r+1>0`, its square is `(j-i)^2/(r+1)`.
Square the existing `Matrix.det_vandermonde` product and distribute the square
over the finite products. This derives the explicit factor above. A local
lexical `Vandermonde` search in `WeilLogShift` returned no indexed declarations;
source searches found no existing point-gap-square or Vandermonde theorem there.

For the actual finite tilt, the existing integral-ratio formula and finite base
law give the displayed weights. Their sum is one by integrating the constant
one; all are positive because every base atom and exponential are positive.
Every observable is L2 under the actual law. Therefore the existing covariance
identity `E[XY]-E[X]E[Y]` identifies the actual power-covariance matrix with the
centered finite-moment block. All helper premises are discharged at the root.

## Lean files

- `HTGeometry/FinitePowerCovarianceDeterminant.lean`
- `RHTower/WeilLogShiftQuadraticTiltWeights.lean`
- `RHTower/WeilLogShiftPowerCovarianceDeterminant.lean`
- `RHTower/WeilLogShiftPowerCovarianceProduct.lean`: explicit support factor.

## Verification

- Four native leaf builds passed with empty logs and fresh objects.
- Nine declarations (eight theorems and one definition) audited through the final
  product root: only `propext`, `Classical.choice`, and `Quot.sound`.
- Twenty-one API checks passed in the final native audit. The concrete squared
  support-gap proof also passed independently before entering the source tree.
- All seven direct project imports are fresh; both umbrellas are wired. Source
  whitespace and umbrella `git diff --check` passed.
- Formal lint snapshot: 367 existing size warnings and seven unrelated modules
  unreachable from their umbrellas: `RHTower.PaperWoldExactNorm`,
  `RHTower.PaperWoldHardyContraction`, `RHTower.PaperWoldHardyEscape`,
  `RHTower.PaperWoldHardySharpness`, `RHTower.PaperWoldSharpCutoffs`,
  `HTGeometry.RectangularSchurBound`, and `HTGeometry.SharpHardySchur`.
  No finding concerns the four new files. Unrelated files were not modified.
- Artifacts: `/tmp/hgt-maximal-power-determinant-final-audit.lean` and `.log`,
  `/tmp/hgt-maximal-power-determinant-audit.py`, the two API scratch files,
  `/tmp/hgt-maximal-power-determinant-lint.log`, and four native leaf logs.

## Exact gain and premise audit

The former rank/sign result is strengthened to the actual determinant value.
The support factor depends only on `r`; all dependence on `k,a,b,d` sits in the
product of explicit positive normalized weights. Both concrete root theorems
quantify over every finite `r,k` and all real tilt coefficients. The algebraic
normalization premise and analytic L2 premises are discharged at those roots.
The stronger explicit-support formula was separately checked against the local
corpus and proved on paper before formalization.

## Next local question

Investigate a sharp upper bound and equality classification for the determinant
from the normalized positive weights, or an exact relation to their information
deficit from the uniform law. These are next conjectures, not results claimed here.
