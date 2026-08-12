# Hedenmalm theta Route P: physical Pluecker spectral operator (P-G91--P-G92)

Status: local covariance and pole-moving spectral operator fully proved in Lean; cofinal assembly in progress

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

Completed paper/Lean closure:

1. exact identification `x^T C x = normalizedFiniteVariance pi (selectedSum x)`;
2. positive semidefiniteness from pairwise-dispersion identity;
3. `C 1 = 0` because every selected pair has cardinality two;
4. kernel classification: `x^T C x = 0` iff all four coordinates of `x` agree, using strict
   positivity of every physical Pluecker minor;
5. genuine non-diagonality: positive quotient rank plus constant kernel force a nonzero cross term.

P-G92 closes the local spectral landing:

6. represent covariance as a Hermitian positive-semidefinite `4 x 4` matrix;
7. sandwich it by positive square-root reciprocal-gap node diagonal;
8. classify transformed nullspace as span of explicit inverse-square-root node vector;
9. prove exact rank three and a nonzero off-diagonal entry;
10. prove pole movement: coupled matrix has a nonzero zero-mode although every bare
    reciprocal-gap node is strictly positive.

First missing step is now cofinal adjacent-prime/depth direct-sum assembly, including a
source-forced block coefficient and trace/summability proof.

Formal file:

- `formal/GaloisForLFunctions/RHTower/GammaSewnMobiusApertureStokesPhysicalPluckerCovariance.lean`
- `formal/GaloisForLFunctions/RHTower/GammaSewnMobiusApertureStokesPhysicalPluckerSpectralMatrix.lean`

Headline declarations:

- `gammaSewnOrderedPrimeDepthPlucker_rate_injective`;
- `gammaSewnCriticalPrimeDepthPacket_probability_pos`;
- `gammaSewnCriticalPrimeDepthPacket_PluckerCovariance_nonneg`;
- `gammaSewnCriticalPrimeDepthPacket_PluckerCovariance_self_eq_zero_iff_constant`;
- `exists_gammaSewnCriticalPrimeDepthPacket_PluckerCovariance_offDiagonal_ne_zero`.
- `gammaSewnCriticalPrimeDepthPacket_PluckerSpectralMatrix_posSemidef`;
- `gammaSewnCriticalPrimeDepthPacket_PluckerSpectralMatrix_mulVec_eq_zero_iff_smul_kernel`;
- `gammaSewnCriticalPrimeDepthPacket_PluckerSpectralMatrix_rank_eq_three`;
- `exists_gammaSewnCriticalPrimeDepthPacket_PluckerSpectralMatrix_offDiagonal_ne_zero`;
- `gammaSewnCriticalPrimeDepthPacket_PluckerSpectralMatrix_zeroMode_off_bareNodeGrid`.

## Numerical pre-certification of next operator

For the literal prime `2/3`, depth `0/1` hostile packet, external high-precision evaluation gives
covariance eigenvalues approximately

```text
0, 0.0655082, 0.258339, 0.365914.
```

Thus quotient rank is exactly three, consistent with Lean kernel theorem. Sandwiching by squared
reciprocal-gap multiplication and testing the information-depleted source vector gives a first
coupled contribution near `1.09104e-4`, below the rigorous completed first-moment ceiling
`1.8e-4`; unlike every diagonal predecessor, leading packet is no longer an immediate first-moment
contradiction. This is pre-certification only, not theorem or fitted normalization.

## P-G92 higher principle

P-G83, P-G85, P-G89, and P-G90 are one obstruction seen at four compression levels:
inverse incidence, Schur reduction, and spectralization do not commute. Scalarization before
spectralization preserves bare node grid and therefore cannot remove first-moment excess.
Retaining incidence covariance first creates a rank-three quotient geometry; node congruence
then changes operator spectrum itself. Common-mode null line is not information loss introduced
by fitting: it is forced by cardinality-two Pluecker incidence law.

## Falsifiers and pivots

- If full covariance is diagonal or has a larger physical kernel, retire this construction.
- If cofinal assembly is nonsummable, change overlap/normalization, not positivity proof.
- If the coupled first moment still exceeds completed first moment, retain kernel classification as
  positive survivor and test the full boundary Hessian including complementary-Fisher diagonal.
- No target-moment fitting is permitted; every coefficient must come from physical Pluecker weights,
  inverse incidence, or Gamma/polar sewing.

## Completion gate

Prove cofinal operator positivity, compactness, anti-Herglotz resolvent, and equality of all
coupled moments with `normalizedPrimeArchMoment`.
