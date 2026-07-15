# Quantum replica Hausdorff convexity

- **ID:** `quantum-replica-hausdorff-convexity`
- **Stage:** 1-in-progress
- **Type:** `[BRIDGE]` exact quantum-information value relation / general corpus strengthening
- **Scientific status:** standard unit-interval density-spectrum constraint transferred to the
  rectangular Hilbert--Schmidt constraint API; novelty is not claimed
- **Verification status:** narrow Lean verification complete; no full build and no concurrent
  Lean process was run

## Claim

For a Hilbert--Schmidt constraint channel `C`, put

```text
T = C† C,
m = Tr(T) = ||C||_HS^2,
M_k = Re Tr(T^(k+1)),
P_k = M_k / m^(k+1).
```

The normalized positive effect `rho = T/m` is a density operator when `m > 0`.  Its spectral
values lie in `[0,1]`, so its replica values `P_k = Tr(rho^(k+1))` form a Hausdorff moment
sequence.  The source formalization establishes the first new complementary condition beyond
the already available monotonicity:

```text
0 <= P_k - 2 P_(k+1) + P_(k+2).
```

Before division this is

```text
D_k = m^2 M_k - 2 m M_(k+1) + M_(k+2) >= 0.
```

No spectral theorem is needed for this order.  If `k = 2n`, then

```text
D_(2n) = ||m C T^n - C T^(n+1)||_HS^2.
```

If `k = 2n+1`, then

```text
D_(2n+1) = ||m T^(n+1) - T^(n+2)||_HS^2.
```

Thus the difference is a static constraint square, not a propagated flow.

The same positive-effect moments also obey the homogeneous adjacent Hankel relation

```text
M_(k+1)^2 <= M_k M_(k+2),
P_(k+1)^2 <= P_k P_(k+2).
```

This is Hilbert--Schmidt Cauchy--Schwarz between consecutive power columns.  Unlike the
Hausdorff difference, both sides have the same channel-rescaling degree, so the relation survives
projective normalization without any bound on `m`.

## General HTGeometry value

`formal/GaloisForLFunctions/HTGeometry/QuantumReplicaHausdorff.lean` adds a rectangular,
zeta-independent API:

- the exact real-scalar Hilbert--Schmidt quadratic expansion;
- master-effect power columns and their Hankel trace pairing;
- real trace moments, mass, and normalized replica moments;
- even/odd trace-moment representations as Hilbert--Schmidt norm squares;
- exact even/odd representations of the complementary second difference;
- nonnegativity of both the unnormalized and normalized differences.
- squared real-part Hilbert--Schmidt Cauchy--Schwarz;
- homogeneous log-convexity of raw and density-normalized replica moments.
- preservation of adjacent log-convexity under coordinatewise limits.
- a countable orthogonal-instrument Bessel bound from square-summable local operator ceilings;
- a master-effect replica-step bound `M_(k+1) <= ||C||^2 M_k`, and its fixed-radius form.

The file is imported by the `HTGeometry` umbrella.  Every future hypertranscendental constraint
channel of the form `C` can use the theorem without importing any zeta or Sonin declaration.

The mathematical all-order statement is stronger:

```text
(-Delta)^r P_k >= 0  for every k,r.
```

Only `r = 1` (the earlier replica contraction) and `r = 2` (this card) have source
formalizations.  Promoting the complete Hausdorff sequence should reuse the existing
`StieltjesMomentProblem` / Hausdorff machinery through a spectral representing measure for the
normalized compact master effect.  That spectral-measure bridge remains open and is not claimed
as Lean-proved.

## Direct RHTower consumer

For the coupled all-prime Sonin column `C_a`, let

```text
S_k(a) = Tr((C_a† C_a)^(k+1)),
P_k(a) = Re S_k(a) / Re S_0(a)^(k+1).
```

`SoninCoupledPrimeArchGramTransfer.lean` now identifies `P_k(a)` with the general quantum replica
moment and exposes

```text
0 <= P_k(a) - 2 P_(k+1)(a) + P_(k+2)(a),

0 <= Re S_0(a)^2 Re S_k(a)
       - 2 Re S_0(a) Re S_(k+1)(a)
       + Re S_(k+2)(a),

Re S_(k+1)(a)^2 <= Re S_k(a) Re S_(k+2)(a).
```

The quotient-free form remains available without assuming the coupled source is nonzero.  It is
strictly stronger than isolated moment nonnegativity and one-step replica monotonicity, and it
cuts the simultaneous source moment locus by a closed quadratic family.

When `Re S_0(a)>0`, the last inequality also has the genuinely projective form

```text
(Re S_(k+1)(a) / Re S_0(a))^2
  <= (Re S_k(a) / Re S_0(a))
       (Re S_(k+2)(a) / Re S_0(a)).
```

No zeroth-mass ceiling occurs in this form.

The concrete Sonin outcome channels also give a second, genuinely aperture-independent family.
Put

```text
W = sum_(p,k) |w_(p,k)|^2,
R_S = 16 W.
```

The newly exposed source factorization proves

```text
||C_a x||^2
  = sum_(p,k) ||w_(p,k) R_(a,p,k) x||^2
  <= R_S ||x||^2,

||C_a† C_a|| <= R_S,

Re S_(k+1)(a) <= R_S Re S_k(a),

Re S_k(a) / Re S_0(a) <= R_S^k,

0 <= R_S Re S_k(a) / Re S_0(a)
       - Re S_(k+1)(a) / Re S_0(a).
```

Here every local exact residual satisfies `||R_(a,p,k)|| <= 4`, uniformly in aperture and
prime-power scale, and the logarithmic Euler coefficients are already square-summable.  No
subunitality or Kraus-completeness hypothesis is assumed.

## Direct route audit

The density-normalized second difference still contains the unscaled source mass, so that exact
formula alone does not pass to the projective target.  The uniform instrument estimate removes
that particular obstruction by replacing the varying mass with the fixed radius `R_S`.  Any
coordinatewise limit of positive-mass projective Sonin moment ratios must obey the displayed
`R_S` envelope and first scaled difference, without assuming convergence or boundedness of
`Re S_0(a)`.  This directly discharges the former *finite source-radius* hypothesis.

The remaining route problem is now sharper: prove the complete all-order scaled-difference
hierarchy at `R_S`, construct the nonzero aperture schedule, and prove its projective moment-ratio
convergence.  No comparison with the endpoint-calibrated radius is required for the implication:
`riemannHypothesis_of_scaledPrimeArchHausdorffMomentDifferencesNonnegative` accepts every positive
radius, and the source now proves `0 < R_S`.  The uniform bound alone supplies only the first
scaled difference and does not construct the schedule.

No RH implication is claimed from the new inequality alone.

The homogeneous log-convexity relation removes that particular mass obstruction.  Any
coordinatewise limit of positive-mass coupled moment ratios must itself be log-convex.  It is
therefore an unconditional compatibility test for proposed projective aperture schedules, rather
than the conditional finite-radius test supplied by the Hausdorff difference.  It still does not
construct a schedule or prove the full target Hankel form positive: adjacent `2 x 2` minors do not
control arbitrary polynomial tests.

## Quantum-instrument audit

`[ROUTE REVIVED BY SOURCE FACTORIZATION]` The earlier shortcut through an *assumed* subunital
Kraus/POVM realization remains invalid.  However, subunitality is unnecessary.  The exact Sonin
correction factorization already gives the uniform local bound `||R_(a,p,k)|| <= 4`; Parseval over
the orthogonal outcome labels and square-summability of the Euler weights then prove the Bessel
bound with radius `R_S = 16 W`.  The older aperture-dependent Hilbert--Schmidt area estimate is
still true but is no longer the relevant operator-norm control.

This is the same energy bookkeeping as a countable quantum instrument, derived from the concrete
source rather than postulated as a completeness relation.  It supplies the fixed compact-support
radius required for projective source moments.  Formalizing all higher scaled Hausdorff
differences from `0 <= C_a†C_a <= R_S I` remains a useful next corpus extension; the first scaled
difference and the all-order geometric envelope are already source-formalized.

## Adjacent quantum-Fisher audit

`[ROUTE RETIRED]` Replacing the existing pure-state projective Fisher value by mixed-state quantum
Fisher or Wigner--Yanase skew information does not improve the live variance comparison.  The
relevant density is a function of the coupled effect `T`, and the moment observables are
polynomials in that same `T`; they commute.  The mixed-state unitary Fisher/skew-information
channel therefore vanishes, while the pure-state projective Fisher value already present in the
corpus is exactly four times the required normalized variance.  The mixed-state substitution
would discard the classical spectral variance rather than bound it.

## Physics provenance

- A. Elben, S. T. Flammia, H.-Y. Huang, R. Kueng, J. Preskill, B. Vermersch, and P. Zoller,
  *The randomized measurement toolbox*, Nature Reviews Physics 5 (2023), 9--24,
  [arXiv:2203.11374](https://arxiv.org/abs/2203.11374).  The review treats higher density-matrix
  moments as measurable multi-copy observables and records positivity inequalities among them.
- A. Neven, J. Carrasco, V. Vitale, C. Kokail, A. Elben, M. Dalmonte, P. Calabrese, P. Zoller,
  B. Vermersch, R. Kueng, and B. Kraus, *Symmetry-resolved entanglement detection using partial
  transpose moments*, npj Quantum Information 7 (2021), 152,
  [arXiv:2103.07443](https://arxiv.org/abs/2103.07443).  The paper uses ordered moment inequalities
  and the Stieltjes moment problem to test operator positivity; its lowest moment condition is the
  homogeneous inequality `p_1 p_3 >= p_2^2`.
- X.-D. Yu, S. Imai, and O. Guehne, *Optimal Entanglement Certification from Moments of the
  Partial Transpose*, Physical Review Letters 127 (2021), 060504,
  [arXiv:2103.06897](https://arxiv.org/abs/2103.06897).  The paper organizes quantum moment
  constraints through positive Hankel matrices, the parent mechanism for adjacent replica
  log-convexity.
- G. Chiribella, G. M. D'Ariano, and P. Perinotti, *Realization schemes for quantum instruments
  in finite dimensions*, Journal of Mathematical Physics 50 (2009), 042101,
  [arXiv:0810.3211](https://arxiv.org/abs/0810.3211).  Its instrument/POVM dilation framework is
  the physics provenance for retaining orthogonal outcome labels and summing their channel
  energies; the Sonin theorem derives the needed Bessel ceiling directly rather than assuming
  instrument completeness.
- G. Toth and F. Frowis, *Uncertainty relations with the variance and the quantum Fisher
  information based on convex decompositions of density matrices*, Physical Review Research 4
  (2022), 013075,
  [DOI 10.1103/PhysRevResearch.4.013075](https://doi.org/10.1103/PhysRevResearch.4.013075).
  This supplies the mixed-state QFI/variance comparison used in the adjacent no-go audit.

## Verification status

The general APIs in `QuantumChannelEnergyAugmentation.lean` and
`QuantumReplicaHausdorff.lean` pass exact-module builds and direct file checks.  The supporting
general modules `FiniteConstraintGroupAverage.lean`, `L2PairingEnergy.lean`,
`HilbertSchmidtRectangular.lean`, and `TwoProjectionQuantumWalk.lean` also pass their exact-module
builds and direct checks.  No numerical check, full build, or concurrent Lean process was run.
The card remains in stage 1 because the source-to-target convergence/comparison step is still
open, not because the recorded declarations are unverified.
