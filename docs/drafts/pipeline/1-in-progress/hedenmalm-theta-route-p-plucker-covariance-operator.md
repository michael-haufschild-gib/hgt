# Hedenmalm theta Route P: full Pluecker covariance operator (P-G91)

Status: in progress

## Conjecture P-G91

P-G82--P-G90 scalarized each six-minor physical packet to a complementary-Fisher fraction. The
discarded object is the full covariance of the six selected-pair incidence vectors. For each
adjacent-prime depth cell, this covariance should be a canonical positive semidefinite,
non-diagonal operator on the four source labels, with kernel exactly the constant direction.

This is the first source-forced operator capable of evading P-G90: its negative cross entries can
cancel diagonal first-moment mass, and spectralizing the coupled matrix can move poles away from
the bare reciprocal-gap nodes.

## Construction

For physical six-minor probability `pi` and selected-pair incidence vector `b_s in {0,1}^4`, set

```text
C = sum_s pi_s b_s b_s^T - (sum_s pi_s b_s)(sum_s pi_s b_s)^T.
```

Equivalently,

```text
x^T C y = E_pi[(b_s.x)(b_s.y)] - E_pi[b_s.x] E_pi[b_s.y].
```

Required paper/Lean closure:

1. exact identification `x^T C x = normalizedFiniteVariance pi (selectedSum x)`;
2. positive semidefiniteness from pairwise-dispersion identity;
3. `C 1 = 0` because every selected pair has cardinality two;
4. kernel classification: `x^T C x = 0` iff all four coordinates of `x` agree, using strict
   positivity of every physical Pluecker minor;
5. genuine non-diagonality: positive quotient rank plus constant kernel force a nonzero cross term;
6. assemble adjacent-prime/depth blocks through P-G86 inverse incidence, then define coupled compact
   operator by sandwiching reciprocal-gap multiplication with this covariance.

## Falsifiers and pivots

- If full covariance is diagonal or has a larger physical kernel, retire this construction.
- If cofinal assembly is nonsummable, change overlap/normalization, not positivity proof.
- If the coupled first moment still exceeds completed first moment, retain kernel classification as
  positive survivor and test the full boundary Hessian including complementary-Fisher diagonal.
- No target-moment fitting is permitted; every coefficient must come from physical Pluecker weights,
  inverse incidence, or Gamma/polar sewing.

## Completion gate

Formalize source covariance and quotient rigidity; prove cofinal operator positivity, compactness,
anti-Herglotz resolvent, and equality of all coupled moments with `normalizedPrimeArchMoment`.
