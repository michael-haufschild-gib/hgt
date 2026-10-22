# Hedenmalm theta Route P: physical Pluecker spectral operator (P-G91--P-G104)

Status: local pole movement, cofinal trace-class assembly, physical overlap sewing, global
faithfulness, actual-Xi Hilbert admission, source-native stable entire determinant, fixed-node
first-trace no-go, boundary-capacity law, and complete canonical-resolvent amplification no-go
fully proved in Lean; direct physical determinant identification and scalar positive boundary
resolvent repair are retired; unique one-negative-index shorting target and its canonical Julia
defect coefficient are classified; oriented Gamma/polar realization and source annihilation are
open; zero boundary spectrum is classified

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

P-G96 closes actual-Xi Hilbert admission. The two involution-fixed positive charts from the
coefficient-faithful horizontal landing have coordinates

```text
reporterScale(e,n) * sourceZeroHorizontalPrimeCarrier(q,p_n).
```

Every actual Xi centered rate lies in `(-1,1)`, so the Bockstein magnitude is at most
`p^(|t|-1) <= 1`. The reporter scale squared is bounded by P-G84's summable physical denominator
term times the fixed reciprocal-gap node bound. Lean therefore proves:

26. both fixed positive Xi reporter charts are square summable over the physical prime-depth
    lattice and define literal P-G95 Hilbert vectors;
27. both vectors are reflection odd and vanish exactly when `Re(q)=1/2`;
28. the faithful physical operator kills the lower admitted Xi vector exactly on the critical
    line;
29. its quadratic energy is strictly positive exactly off the critical line.

This is a source-faithful positive detector, not an annihilation theorem. The remaining producer
must force this already-defined energy to vanish from completed Gamma/polar source geometry.

P-G97 classifies the spectral boundary forced by P-G95. The physical Hilbert space contains an
infinite orthonormal prime-depth family. A compact injective operator on this space cannot have
closed range. Positivity makes the operator self-adjoint, and self-adjoint injectivity makes its
range dense. Lean proves:

30. the physical prime-depth Hilbert space is not finite dimensional;
31. normalized unit vectors exist whose P-G95 images converge to zero;
32. the operator range is dense, nonclosed, proper, and the operator is not surjective;
33. zero belongs to the operator spectrum but is not an eigenvalue.

Thus P-G95 did not remove zero from spectral geometry. It converted exact local nullity into a
continuous boundary singularity. Any Gamma/polar transfer regular at zero or using a bounded
inverse there is now formally impossible.

P-G98 closes source-native stable determinant existence. The P-G94/P-G95 operator is already
Schatten-one, hence Hilbert--Schmidt. Passing to its canonical coordinate kernel introduces no new
normalization. Positivity and injectivity imply every finite principal compression is positive
definite: zero-extending a block eigenvector preserves its quadratic form, and zero energy would
put a nonzero physical vector in global kernel. Lean proves:

34. canonical coordinate kernel is Hilbert--Schmidt and reconstructs physical operator exactly;
35. every zero of every finite `det2(I-z T_s)` is strictly positive real;
36. every zero of reflected finite determinant `det2(I+u T_s)` is strictly negative real;
37. finite determinants converge pointwise and locally uniformly on closed discs to an entire
    regularized determinant;
38. every zero of cofinal reflected determinant is strictly negative real.

This is source-faithful SP-E limit missing from artificial depth-square construction. It closes
stability and cofinal determinant assembly, not arithmetic identification with Xi.

P-G99 closes direct arithmetic identification negatively and extracts its strongest survivor.
Regularized `det2` has zero first derivative, so its direct Xi identification is impossible.
Multiplying by the canonical trace exponential restores the ordinary Fredholm determinant and
makes its first derivative the literal nuclear source mass.  Lean then identifies every covariance
diagonal as Bernoulli variance and proves

```text
sourceTrace
  = sum_z blockWeight_z
      sum_i node_z,i * m_z,i * (1-m_z,i).
```

Critical Stokes bounds give every packet node sum `<2/25`; the global real inequality
`m(1-m)<=1/4` makes every local trace `<1/50`, even for arbitrary real coordinate means.  Since
block weights are positive and sum to one, `sourceTrace<=1/50`.  Independent completed-source
arithmetic gives `thetaCuspNormalizedEvenMoment 1 / 2>1/50`.  Hence canonical ordinary determinant
also has wrong first jet.  Reweighting six-minor probabilities cannot repair it.  Physical
operator survives as stable reference geometry; final arithmetic carrier must leave fixed-positive-
node Bernoulli class through source-derived node change/amplification, signed/indefinite channel, or
non-Bernoulli singular boundary transfer compatible with P-G97.

Formal file:

- `formal/GaloisForLFunctions/RHTower/GammaSewnMobiusApertureStokesPhysicalPluckerCovariance.lean`
- `formal/GaloisForLFunctions/RHTower/GammaSewnMobiusApertureStokesPhysicalPluckerSpectralMatrix.lean`
- `formal/GaloisForLFunctions/RHTower/GammaSewnMobiusApertureStokesCofinalPluckerSpectralOperator.lean`
- `formal/GaloisForLFunctions/RHTower/GammaSewnMobiusApertureStokesPhysicalOverlapPluckerSpectralOperator.lean`
- `formal/GaloisForLFunctions/RHTower/GammaSewnMobiusApertureStokesPhysicalOverlapPluckerFaithfulness.lean`
- `formal/GaloisForLFunctions/RHTower/GammaSewnMobiusApertureStokesPhysicalPluckerEntireDeterminant.lean`
- `formal/GaloisForLFunctions/RHTower/NuclearRankOneTrace.lean`
- `formal/GaloisForLFunctions/RHTower/GammaSewnMobiusApertureStokesPhysicalPluckerOrdinaryDeterminant.lean`
- `formal/GaloisForLFunctions/RHTower/GammaSewnMobiusApertureStokesPhysicalPluckerFirstTraceNoGo.lean`
- `formal/GaloisForLFunctions/RHTower/GammaSewnMobiusApertureStokesPhysicalPluckerBoundaryTraceCapacity.lean`
- `formal/GaloisForLFunctions/RHTower/GammaSewnMobiusApertureStokesPhysicalPluckerBoundaryAmplificationNoGo.lean`
- `formal/GaloisForLFunctions/RHTower/GammaSewnMobiusApertureStokesPhysicalPluckerBoundarySpectralShellNoGo.lean`
- `formal/GaloisForLFunctions/RHTower/RouteEPCubicSourceNormalizationKreinShorting.lean`
- `formal/GaloisForLFunctions/RHTower/FrankensteinPluckerXiHilbertAdmission.lean`
- `formal/GaloisForLFunctions/RHTower/GammaSewnMobiusApertureStokesPhysicalOverlapPluckerBoundarySpectrum.lean`

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
- `summable_norm_sq_frankensteinXiLowerPrimeCarrier`;
- `frankensteinXiLowerPhysicalPluckerHilbertCarrier_eq_zero_iff`;
- `gammaSewnCriticalPhysicalPluckerSpectralOperator_apply_xiLower_eq_zero_iff`;
- `gammaSewnCriticalPhysicalPluckerSpectralOperator_xiLower_energy_pos_iff`.
- `gammaSewnCriticalPhysicalPluckerSpectralOperator_hasApproximateUnitKernel`;
- `gammaSewnCriticalPhysicalPluckerSpectralOperator_denseRange`;
- `gammaSewnCriticalPhysicalPluckerSpectralOperator_zero_mem_spectrum`;
- `gammaSewnCriticalPhysicalPluckerSpectralOperator_zero_not_eigenvalue`.
- `gammaSewnCriticalPhysicalPluckerKernel_toOperator`;
- `gammaSewnCriticalPhysicalPluckerFiniteDet2_zero_pos`;
- `gammaSewnCriticalPhysicalPluckerStableFiniteDet2_zero_re_im`;
- `gammaSewnCriticalPhysicalPluckerStableEntireDet2_zero_re_im`;
- `tendstoUniformlyOn_gammaSewnCriticalPhysicalPluckerStableFiniteDet2`.
- `fourRatePluckerCovariance_coordinateDelta_self_eq_bernoulliVariance`;
- `gammaSewnCriticalPhysicalPluckerNuclearTraceMass_eq_tsum_bernoulliTrace`;
- `gammaSewnCriticalPhysicalPlucker_arbitraryBernoulliTrace_lt_one_div_fifty`;
- `gammaSewnCriticalPhysicalPluckerNuclearTraceMass_le_one_div_fifty`;
- `gammaSewnCriticalPhysicalPluckerOrdinary_firstJet_ne_theta`.
- `tendsto_gammaSewnCriticalPhysicalPluckerWeightedBoundaryPacketTrace`;
- `gammaSewnCriticalPhysicalPluckerWeightedBoundaryPacketTrace_add_smul_inverse_eq_four`;
- `gammaSewnCriticalPhysicalPlucker_canonicalBoundarySplit_cannot_rebalance_fourthDepth`;
- `positiveBoundaryInverse_eq_real_smul_imp_operator_eq_smul`;
- `norm_gammaSewnCriticalPhysicalPluckerSpectralOperator_le_one_div_fifty`;
- `gammaSewnCriticalPhysicalPlucker_canonicalBoundaryResolvent_cannot_rebalance_near_zero`.
- `routeEPCubicPolarPivotShortedFourthDepthEnergy_eq_parent_iff`;
- `routePPrimitiveFourthDepth_sourceFaithful_pairTrace_eq_fullPolarShort`;
- `routePPrimitiveFourthDepth_sourceNormalizationKreinShorting_classification`.

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

## P-G96 higher principle

Normalizability is not the Xi obstruction. Physical denominator decay admits the literal
coefficient-faithful Xi reporters to the same Hilbert space on which local gauges are expelled.
Faithfulness then converts horizontal displacement into strictly positive bulk energy. Thus the
remaining wall is an **annihilation/trace law, not an admission or kernel-classification law**:
completed Gamma/polar geometry must explain why every actual divisor has zero detector energy.

## P-G97 higher principle

Faithfulness and compactness force a third state between kernel and invertibility: **zero is
continuous boundary spectrum**. Local Stokes gauges become approximate unit gauges, not
normalizable eigenvectors. This explains why earlier routes alternated between spurious kernels
and nonclosable clocks: both are shadows of one boundary-spectral law. Correct completion must use
a singular, renormalized zero-boundary transfer; a bounded zero resolvent cannot exist.

## P-G98 higher principle

Stable Eulerian structure appears automatically after faithful physical incidence descent. Local
rate-pair normalization severed overlap geometry, then tried to repair gauge sewing and source mass
by scalar rescaling. P-G94 descent keeps literal overlap; P-G95 faithfulness turns positive
semidefinite compressions into positive definite ones; regularized determinant theory converts that
operator fact into finite and cofinal strict real-rootedness. Remaining wall is arithmetic: identify
completed Xi content of an already-stable source determinant or its P-G97-compatible boundary
transfer.

## P-G99 higher principle

Stable incidence descent and completed arithmetic charge are distinct layers.  P-G94--P-G98 fix
overlap, gauge sewing, positivity, faithfulness, and zero geometry, but their fixed reciprocal-gap
nodes impose a universal first-trace capacity.  Bernoulli coordinate reweighting cannot create the
missing archimedean charge because its curvature has global apex `1/4`.  The recurring uniform-
metric gap, fourth-depth `1/64` debt, zero `det2` jet, and deficient ordinary trace are shadows of
one principle: **completion charge must enter before or at singular boundary transfer, not by
reweighting a positive incidence covariance after spectralization**.

## P-G100--P-G102 boundary classification

P-G100 proves canonical zero-boundary transfer changes global capacity: every fixed physical
coordinate tends to one, source-weighted packet trace tends to four, and its exact polar
countercurrent tends to `-4`.  The identity

```text
W(eps) + eps R(eps) = 4
```

shows missing capacity is a literal inverse-density trace.  But P-G101 separates cofinal rank
recovery from local source amplification.  Both bounded halves of resolvent partition are
contractions and cannot realize SP-E's unique nonnegative amplitude eight.

P-G102 closes apparent unnormalized-inverse survivor for existing positive physical operator.
Resolvent gain `c` forces original spectral shell `1/c-eps`.  At `c=8`, shell is
`1/8-eps`.  Positivity and literal nuclear expansion give

```text
||T|| <= nuclearTraceMass <= 1/50.
```

Therefore amplitude eight is impossible on every nonzero vector whenever
`0<eps<21/200 = 1/8-1/50`.  In particular it cannot persist toward continuous zero boundary.
Canonical positive scalar resolvent is fully retired as source-normalization repair.  Positive
survivor is sharper: any successful correction must change operator before inversion or create an
oriented off-diagonal source/co-source shorting; it cannot be a scalar function of current `T`.

## P-G102 higher principle

Trace shortage, zero-boundary rank escape, and amplitude debt are three inequivalent spectral
notions.  Boundary transfer repairs rank capacity, but exact Radon--Nikodym gain selects a positive
spectral shell.  Because source trace already bounds entire positive spectrum, a missing
coefficient cannot be created by scalar functional calculus after positive spectralization.
Recurring failure is shadow of one ordering law: **completion must alter oriented incidence before
forming positive operator; post-spectral scalar resolvents preserve spectral budget and cannot
manufacture source normalization**.

## P-G103 Krein shorting classification

Positive Schur complements cannot solve additive normalization debt: shorting through positive
parent pivot `w` changes depleted leg to `w/64-r^2/w<=w/64`. Oriented polar pivot `-w` changes sign
and restores parent exactly iff

```text
r^2 = (63/64)w^2.
```

Unique nonnegative cross is `(sqrt 63 / 8)w`; determinant of exact two-channel block is `-w^2`.
Full cross `r=w` gives `65w/64`, exactly source-faithful pair trace. This `65/64` duality shows
equal source/polar residues do not create correction; they reproduce original debt. Missing object
is now coefficient-rigid: literal Gamma/co-Poisson/Stokes cross pairing at attenuated value, with
one negative pivot, before positive compression.

## P-G104 fourth-depth Julia defect

P-G103's coefficient is not an independent overlap parameter. Two coefficient-faithful Route-P
depth-square steps have exact squared-energy factor `1/64`, hence normalized Hilbert amplitude
`c=1/8`. Canonical positive Julia completion has defect

```text
d = sqrt(1-c^2) = sqrt(63)/8.
```

For parent amplitude `a=sqrt w`, source-axis transport is `(a,0)->(ca,da)`. Literal child energy
`(ca)^2=w/64` and defect energy `(da)^2=63w/64` sum to `w`; parent--defect pairing is
`a(da)=dw`, exactly unique P-G103 polar cross. P-G179's physical half-dyadic dilation gives same
law after two iterations. The coefficient problem is closed. Remaining problem is orientation and
provenance: identify this canonical defect coordinate with actual Gamma/co-Poisson/Stokes co-source
and actual polar pivot before compression.

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

Direct P-G98 determinant identity is retired at first trace by P-G99; scalar functional calculus
of current positive operator is retired as normalization repair by P-G101--P-G102.  Do not compare
more direct Fredholm coefficients, tune six-minor probabilities, or reuse transfer/inverse as a
scalar channel. P-G104 already derives required cross magnitude from canonical fourth-depth Julia
defect. Identify that defect coordinate with literal oriented Gamma/co-Poisson/Stokes co-source and
short it against actual polar pivot `-w`, before inversion. It must be
compatible with P-G97 continuous zero spectrum and P-G96 admitted Xi carrier, and its first
coefficient must derive missing completed charge before all higher moments/divisor are identified
with `normalizedPrimeArchMoment`.  Then prove completed Gamma/polar source geometry annihilates
faithful detector energy and invoke Julia saturation. Zero may occur only as non-normalizable gauge
boundary mode or literal zero Xi carrier, not as added Hilbert-space kernel vector. No fitted
inter-block coefficient is permitted: physical overlap already supplies sewing.
