# Full-source energy versus selected factorization charge

## Target and scope

Audit the candidate RH implication “source factorization is associative, therefore the
selected grade-mixing charge has zero curvature.” No zero-annihilation law is assumed.
The source is fixed: `a_p(n)=1-p[p|n]`, and, for coprime labels,
`a_pq=a_p+a_q-a_p a_q`.

Corpus dependencies: `EulerDeletionFactorizationGraded` supplies this coefficient identity
and the weighted selected charge `D(p,q)=Σ a_p a_q² n^(-α)`.
`EulerDeletionCompositeInterference` supplies full-source energies.
`EulerDeletionFactorizationCurvature` computes the nonzero curvature of `D`.
Searches for energy/composite, factorization/correction, and curvature/completion found
these results but no identification of the full quadratic increment with `D`.

## Conjecture and paper proof

Retain every term in the literal square. Its half-energy increment is

`F(p,q)=Σ [a_p a_q + (a_p a_q)²/2 - a_p² a_q - a_p a_q²] n^(-α)`.

Pointwise expansion gives
`F(p,q)=(E(pq)-E(p)-E(q))/2`, hence its multiplicative four-term boundary is zero.
This already holds at each integer and for every finite weighted cutoff.

The terms omitted by selecting only `D` are independently specified by the same square:
`C(p,q)=Σ [a_p a_q + (a_p a_q)²/2 - a_p² a_q] n^(-α)`.
Thus `F=C-D`; the four-term boundary of `C` equals the previously proved curvature of `D`.
For `α>1`, summability follows from the three source squares and
`a_q²=(q-1)+(2-q)a_q`. All coefficients and both cross orientations remain literal.

Consequences: full quadratic source conservation is compatible with nonzero selected
curvature. Associativity of the full energy does not by itself annihilate `D`.
This does not rule out a different, zero-selected chronological source law.
No Xi divisor transport, multiplicity statement, boundary index, or RH proof is claimed.

## Formal result and verification

`formal/GaloisForLFunctions/RHTower/EulerDeletionFullEnergyFactorization.lean`,
namespace `RHTower.DeletionFullEnergy`:

- `fullCoefficient_eq`: pointwise half-energy decomposition with literal coefficients.
- `weighted_prefix_curvature_zero`: full conservation for every finite cutoff and any weights.
- `fullEnergy_eq_mellinNormSq`: identification with the three actual complex Mellin-source
  norm-square sums; not an independently chosen energy model.
- `fullEnergy_curvature_zero`: full weighted conservation for `α>1`.
- `omittedEnergy_eq`, `omittedEnergy_curvature_eq`: independently specified omitted square
  terms satisfy `C=F+D` and carry exactly the selected curvature.
- `omittedEnergy_curvature_neg`: their boundary is strictly negative for `1<α<2` and
  pairwise-coprime labels greater than one; it cannot be discarded as zero there.

Scratch checked, targeted leaf olean compiled without warnings, imported audit of eight
capstones passed with only `propext`, `Classical.choice`, `Quot.sound`. Wired into `RHTower`;
no umbrella build. Global lint found seven unrelated concurrent unwired modules; none in
this change. No computational experiments used. This is a source-identification audit
using standard polarization, not a mathematical novelty claim or a replacement RH producer.

## Research consequence

Do not promote associativity of the full quadratic source into associativity of the central
lift defined using `D` alone. The full source supplies a compensating boundary for every
admissible exponent. An RH argument still requires an independently derived, zero-specific
law about the selected channel; this result neither constructs that law nor rules out every
chronological/non-quadratic construction.
