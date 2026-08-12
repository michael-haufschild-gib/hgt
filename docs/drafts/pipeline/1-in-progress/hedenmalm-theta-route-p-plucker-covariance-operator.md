# Hedenmalm theta Route P: physical Pluecker spectral operator (P-G91--P-G95)

Status: local pole movement, cofinal trace-class assembly, physical overlap sewing, and global
faithfulness fully proved in Lean; resolvent/completed-moment identification is open

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

P-G93 closes the canonical direct-sum assembly:

11. choose the source-forced coefficient `D_z / sum_w D_w`, where `D_z` is P-G84's physical
    adjacent-prime denominator term; prove strict positivity, summability, and total mass one;
12. express every weighted local spectral block as the Gram matrix of six centered physical
    Pluecker source vectors;
13. assemble these vectors into an absolutely nuclear positive rank-one series on
    `ell^2((depth,edge),label)`;
14. prove the global operator positive, Schatten-one, compact, and exactly block diagonal with
    matrix entry `blockWeight_z * spectralBlock_z(i,j)`;
15. prove each block's inverse-square-root common mode embeds as a nonzero vector in the global
    kernel.

P-G93 therefore constructs a cofinal operator without fitted damping. It also proves direct-sum
assembly alone is too reducible: its kernel contains one nonzero common mode for every
depth/adjacent-prime block. First missing step is a source-native inter-block coupling which sews
these null lines before spectral pushforward while preserving positivity and trace class.

P-G94 closes that sewing without adding a new coefficient. The error was the Hilbert-space model:
P-G93 gave every packet a disjoint copy of its four labels, whereas adjacent packets share literal
prime-depth cells. Place packet `(e,n)` on physical labels

```text
(e,n), (e+1,n), (e,n+1), (e+1,n+1).
```

Then horizontal and vertical neighbors overlap on two labels. Lean proves:

16. physical label map is injective within every packet and has exact horizontal/vertical overlap;
17. source-normalized centered rank-one series on `ell^2(depth,prime-index)` remains positive,
    Schatten-one, and compact;
18. every individual weighted P-G92 block matrix is retained exactly under physical embedding;
19. a local common-mode vector is annihilated by its own block, but its restriction to the next
    adjacent-prime block is not in that block's kernel;
20. neighboring-block quadratic energy is strictly positive, so every embedded P-G93 null vector
    is formally outside the global P-G94 kernel.

Thus packetwise null bundle was created by artificial direct-sum duplication. Literal source
overlap supplies inter-block coupling automatically.

P-G95 closes the global-kernel question left open by P-G94. If the positive global sum kills a
physical vector, positivity forces every local block to kill its four-coordinate restriction. The
complex local kernel classification makes that restriction a scalar multiple of the explicit
reciprocal-node kernel vector. Literal depth overlap identifies adjacent scalars. Its zeroth kernel
coordinate is exactly the critical Stokes gap

```text
g(e,p) = (e+1) inverseTilt(1/2,p).
```

Any nonzero glued gauge therefore has coordinates bounded below by one fixed positive constant
along every valuation depth and cannot belong to `ell^2(depth,prime-index)`. The scalar is zero on
every depth line; horizontal overlap then propagates zero across every prime label. Lean proves:

21. a global zero is killed by every positive local block;
22. every complex local block kernel is exactly the complex span of the explicit kernel vector;
23. depth-overlap identifies the local gauge coefficients;
24. the kernel section equals the linearly growing Stokes gap and no nonzero section is square
    summable;
25. the physical overlap operator is injective, and its real quadratic form is strictly positive
    on every nonzero physical vector.

Formal file:

- `formal/GaloisForLFunctions/RHTower/GammaSewnMobiusApertureStokesPhysicalPluckerCovariance.lean`
- `formal/GaloisForLFunctions/RHTower/GammaSewnMobiusApertureStokesPhysicalPluckerSpectralMatrix.lean`
- `formal/GaloisForLFunctions/RHTower/GammaSewnMobiusApertureStokesCofinalPluckerSpectralOperator.lean`
- `formal/GaloisForLFunctions/RHTower/GammaSewnMobiusApertureStokesPhysicalOverlapPluckerSpectralOperator.lean`
- `formal/GaloisForLFunctions/RHTower/GammaSewnMobiusApertureStokesPhysicalOverlapPluckerFaithfulness.lean`

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
- `gammaSewnCriticalCofinalPluckerPositiveSpectralOperator_isPositive`;
- `gammaSewnCriticalCofinalPluckerPositiveSpectralOperator_memSchattenClass_one`;
- `gammaSewnCriticalCofinalPluckerPositiveSpectralOperator_matrix`;
- `gammaSewnCriticalCofinalPluckerPositiveSpectralOperator_kernelVector`;
- `gammaSewnCriticalCofinalPluckerKernelVector_ne_zero`.
- `gammaSewnCriticalAdjacentPrime_PluckerKernelTransportNext_mulVec_ne_zero`;
- `gammaSewnCriticalPhysicalPluckerSpectralOperator_isPositive`;
- `gammaSewnCriticalPhysicalPluckerSpectralOperator_memSchattenClass_one`;
- `gammaSewnCriticalPhysicalPluckerSpectralBlockOperator_matrix`;
- `gammaSewnCriticalPhysicalPluckerSpectralBlockOperator_rightBlock_quadratic_ne_zero`;
- `gammaSewnCriticalPhysicalPluckerSpectralOperator_embeddedKernelVector_ne_zero`.
- `gammaSewnCriticalPhysicalPlucker_depthGaugeCoefficient_zero`;
- `gammaSewnCriticalPhysicalPluckerSpectralOperator_injective`;
- `gammaSewnCriticalPhysicalPluckerSpectralOperator_apply_eq_zero_iff`;
- `gammaSewnCriticalPhysicalPluckerSpectralOperator_re_inner_pos_iff`.

## P-G93 higher principle

P-G83 and P-G93 together distinguish two independent assembly obstructions. Complete-graph
packet overlap duplicates local incidence and destroys summability. Adjacent-prime direct sum
fixes multiplicity and gives a canonical nuclear operator, but preserves one isolated conservation
law per block. Thus **normalization and sewing do not commute**: normalizing disconnected packets
creates infinitely many exact zero modes. Gamma/polar completion must first identify or transport
their common-mode currents through an inter-block incidence differential; only then may the
operator be compactly spectralized. The next object is not another block coefficient. It is a
source-forced coupling on the bundle of local null lines.

## P-G94 higher principle

P-G93's null-bundle obstruction is not intrinsic. It is the shadow of replacing a Čech-like
overlap system by its disjoint coproduct. Physical Pluecker packets are charts on one prime-depth
lattice; their common-mode laws are local gauges, and overlap transition maps make an embedded
local gauge visible to its neighbor. Therefore **spectralization must occur after physical label
descent, not on a direct sum followed by an invented coupling**. This is the same noncommutation
principle seen in P-G83--P-G90 at a higher categorical level: incidence descent, normalization,
and spectralization do not commute. P-G94 performs descent first and removes the spurious local
zero modes while keeping positivity and nuclearity.

## P-G95 higher principle

P-G94's local gauge does globalize algebraically, but its canonical section is not a physical
Hilbert vector. Depth overlap forces the section to be the Stokes gap, and Gamma-sewn valuation
geometry makes that gap grow instead of decay. Thus **local nullity becomes a non-normalizable
boundary mode rather than a global eigenmode**. The source did not destroy gauge freedom; physical
completion expelled it to the boundary of `ell^2`. Any later resolvent construction must respect
zero as a boundary-spectral phenomenon and must not reinsert this section as a normalizable state.

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
- If any inter-block coupling is added without a literal source incidence or Gamma/polar boundary
  map, reject it as fitted.
- If sewing the common-mode bundle necessarily breaks positivity, pivot to a signed conservative
  colligation and prove anti-Herglotz order at the transfer-function level rather than operator
  positivity.
- If the coupled first moment still exceeds completed first moment, retain kernel classification as
  positive survivor and test the full boundary Hessian including complementary-Fisher diagonal.
- No target-moment fitting is permitted; every coefficient must come from physical Pluecker weights,
  inverse incidence, or Gamma/polar sewing.

## Completion gate

Construct the P-G95 faithful compact operator's source-selected anti-Herglotz resolvent/transfer
function and exact trace moments; identify its Gamma/polar sewn transfer and every moment with
`normalizedPrimeArchMoment`; then invoke Julia saturation. Zero may occur only as a
non-normalizable boundary mode, not as an added Hilbert-space kernel vector. No additional
inter-block coefficient is permitted: physical overlap is the sewing.
