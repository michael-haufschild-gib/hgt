# Exact seam-power factor of the complete upper determinant

- **ID:** TT-C116-SEAM-POWER
- **Stage:** 3-formalized
- **Source:** `weightedSourceQuadratic_eq`, `weightedSixthSlope_eq`, and
  `seamReset_division` in the current Lean corpus.
- **Lean status:** complete. Three production leaves and all 19 public
  declarations passed direct `lake --old env lean` audits; axiom sets contain
  only propext, Classical.choice and Quot.sound. RHTower umbrella wired.

Production: `ThetaCuspRatioSquarePowerDescent`, `ThetaCuspRatioUpperSeamPower`,
and `ThetaCuspRatioReducedDeterminantTransport`. Capstones:
`upper_determinant_core_eq`, `upper_determinant_transport_factor`, and
`actual_upper_determinant_core_identity`.

## Statement

For every complex load c, the complete upper determinant has an exact
polynomial factorization `upperCenterDeterminant c = U^26 * R_c`.
All three coefficients of the upper quadratic have a common factor U^13.
No moment, cofactor, or load term is discarded. This is an identity, not a
positivity claim or a truncation near U=0.

## Dependency-closed paper proof

Write s for the existing square homomorphism, which sends U to U² and
fixes K and Z. First prove the following descent: if `s(P)=U^(2n+1)*Q`,
then `P=U^(n+1)*R` for a polynomial R.

For n=0, evaluate at U=0. Since s preserves evaluation there, P vanishes
on that hyperplane. The existing seam-reset division identity gives P=U*R.
For the inductive step, the same argument gives P=U*S. Substitute this in
the assumed identity and cancel U² in the polynomial domain. This yields
`s(S)=U^(2n+1)*Q`, and induction gives S=U^(n+1)*R. Thus P has the next
required power. Polynomial funext and seam-reset division justify the
hyperplane step over the existing complex coefficient field.

The corpus identity `weightedSourceQuadratic_eq` gives U^25 as a factor
after applying s, hence U^13 before applying s. The center-slope term has
U^26 after applying s by `weightedSixthSlope_eq 23` and
`weightedLoadedLinear_eq`; this also contains U^25 and descends to U^13.
Therefore `upperCenterQuadratic c eta = U^13 * V(c,eta)` for every c,eta.

Write the upper quadratic as A+2B*eta+D*eta². Its values at 0,1,-1 recover
the complete coefficients by the exact polarization identities

`A=q(0)`, `B=(q(1)-q(-1))/4`,
`D=(q(1)+q(-1)-2q(0))/2`.

Each coefficient is consequently U^13 times a polynomial. Substitution
in the existing definition `upperCenterDeterminant c=A*D-B²` gives U^26
times the corresponding reduced determinant. This proves the statement
for every complex load without a sign assumption.

## Consequence for the hard sign problem

On the actual positive ray, U=u²>0, so the desired determinant sign is
exactly the sign of the reduced polynomial R_c. The C115 normalized
candidate `Re Q/(u^52*k^34)` becomes `Re R_c/k^34`. Its derivative has
numerator `K*squareLie(R_c)-34*squareField(K)*R_c`, with positive
denominator `6*u*k^35`. The sign of this numerator remains open; this
factorization supplies no monotonicity premise.

The full weighted-jet construction continues. This exact structural
reduction should be used before expanding the determinant or seeking a
source-cone certificate.
