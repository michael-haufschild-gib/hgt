# Prime--Gamma physical Pluecker entire determinant

- **ID:** `prime-gamma-physical-plucker-entire-determinant`
- **Stage:** 3-formalized / needs audit
- **Type:** `[THEOREM] [EXACT POSITIVE SURVIVOR] [SP-E GATE]`
- **Parents:**
  `hedenmalm-theta-route-p-plucker-covariance-operator.md`,
  `route-e-p-sp-e-cubic-source-normalization-debt.md`
- **Lean:**
  `formal/GaloisForLFunctions/RHTower/GammaSewnMobiusApertureStokesPhysicalPluckerEntireDeterminant.lean`

## Conjecture attacked

The fourth-depth two-column construction failed because unit normalization hid a factor `1/64`
in transported source mass.  Conjecture: abandon artificial depth pairing and use P-G94's literal
physical-overlap Pluecker covariance operator.  Its source normalization, cross-prime/depth sewing,
positivity, Schatten-one budget, compactness, and injectivity are already closed.  The operator's
coordinate kernel should therefore generate a source-faithful cofinal SP-E determinant without any
amplitude correction or fitted coefficient.

## Exact construction

Let `T` be P-G94/P-G95's physical-overlap operator on
`ell^2(N x N)`, and let

```text
K(i,j) = (T e_j)(i)
```

be its canonical coordinate kernel.  Schatten-one factorization implies that `T` is
Hilbert--Schmidt; the kernel/operator round trip is exact.  Define

```text
D(z)       = det_2(I - z T),
D_st(u)    = D(-u),
D_s(z)     = det_2(I - z T_s),
D_st,s(u)  = D_s(-u),
```

where `T_s` is finite principal coordinate compression.

For every finite block, a nonzero eigenvector `v` with compression eigenvalue `mu` has zero
extension `w`.  Double truncation does not change its quadratic form:

```text
<w,T_s w> = <w,T w>.
```

P-G94 positivity makes right side nonnegative.  P-G95 injectivity plus positive-operator
quadratic-kernel detection makes it nonzero, hence strictly positive.  Thus `mu>0` and every zero
`z=mu^-1` of `D_s` is strictly positive real.  The same argument for a zero of the cofinal
regularized determinant uses the reciprocal-eigenvector theorem for Hilbert--Schmidt det2 and
again gives `z>0`.

Therefore every zero of each reflected `D_st,s` and of `D_st` is strictly negative real.
Finite-section determinant theory gives pointwise and locally uniform convergence

```text
D_st,s -> D_st
```

on every closed complex disc.

## Strongest positive survivor

SP-E now has an unconditional source-native stable entire-function limit:

1. no unit-diagonal normalization;
2. no amplitude-eight repair;
3. no fitted damping or inter-block coefficient;
4. literal six-minor Pluecker covariance and physical prime/depth overlap;
5. every finite approximant strictly negative-real-rooted after reflection;
6. locally uniform convergence to an entire limit with same strict zero ray.

This closes the determinant-existence, source-normalization, sewing, trace-class, finite-stability,
and cofinal-stability gates simultaneously.

## Higher principle

Depth-square normalization debt and P-G93's false local kernels were shadows of same error:
spectralizing before physical descent.  A source covariance is not a bag of independently
normalizable local columns.  It is a sheaf-like overlap object whose chart intersections both sew
gauge directions and fix Radon--Nikodym mass.  Once descent is performed first, positivity plus
global faithfulness automatically provides strict finite stability.  Stable Eulerian structure is
therefore not manufactured by local rate separation; it is the spectral shadow of faithful
positive incidence descent.

The remaining RH obstruction is also sharpened.  Stability alone is no longer missing.  One must
identify arithmetic content of this already-stable determinant: completed Gamma/polar geometry
must prove its logarithmic coefficients, divisor, or a source-selected transform coincide with
completed Xi.  Since P-G97 places zero in continuous spectrum, any such identification must use a
renormalized boundary transfer rather than bounded inversion of `T`.

## Conjecture loop audit

1. **Conjecture:** repeat a unit-diagonal fourth-depth block cofinally.
   **Failed:** coefficient-faithful transport depletes partner mass by `1/64`.
2. **Pivot:** repair by source-derived amplitude eight.
   **Stalled:** corpus has no lawful local channel paying exact `63/64` trace debt.
3. **Conjecture:** six Boolean history bits might provide a literal 64-fold fibre.
   **Rejected before formalization:** corpus contains no relevant source map with that fibre; this
   would be numerical coincidence theatre.
4. **Pivot:** retain full P-G94 physical covariance instead of inventing a corrected two-column
   compression.
   **Proved:** canonical trace-class coordinate determinant and all finite/cofinal zero-ray laws.
5. **Next conjecture:** completed Xi is not the determinant itself but a source-selected
   renormalized boundary transfer or completed logarithmic moment transform of `T` compatible with
   P-G96 reporter admission and P-G97 continuous zero spectrum.

## Open core exposed

1. Compute source-native trace/log-determinant coefficients of `T` in terms of the already-proved
   six-minor covariance series; compare first two with `normalizedPrimeArchMoment` without target
   fitting.
2. Determine whether direct det2 identification is possible.  A mismatch at first or second
   completed moment is an immediate no-go and must trigger transfer-function pivot.
3. If direct identity fails, construct P-G97-compatible renormalized zero-boundary transfer whose
   logarithmic moments are the completed Xi moments and whose finite sections retain divisor
   convergence.
4. Prove source annihilation of P-G96's admitted actual-Xi reporter energy, or an equivalent exact
   completed-moment identity.
5. Only then invoke existing Julia/Route-P RH receiver.  Current theorem does not prove RH.

## Novelty audit

Targeted internal search found the P-G94/P-G95 operator and generic Hilbert--Schmidt det2
infrastructure separately, but no bridge proving strict real-rootedness of every physical principal
compression, its reflected SP-E form, or local-uniform cofinal source determinant.  Targeted
primary-literature search found standard regularized Fredholm determinant theory and unrelated
Eulerian real-rootedness, not this prime--Gamma six-minor physical-overlap construction.  Claim is
an internal cross-module deduction; no external priority claim is made.

## Formal status

Lean proves without added axioms:

- `gammaSewnCriticalPhysicalPluckerSpectralOperator_isHilbertSchmidt`;
- `gammaSewnCriticalPhysicalPluckerKernel_isHS`;
- `gammaSewnCriticalPhysicalPluckerKernel_toOperator`;
- `inner_liftBlockLp_physicalPlucker_toOperator_truncKernel_eq`;
- `gammaSewnCriticalPhysicalPluckerFiniteDet2_zero_pos`;
- `gammaSewnCriticalPhysicalPluckerStableFiniteDet2_zero_re_im`;
- `gammaSewnCriticalPhysicalPluckerEntireDet2_zero_pos`;
- `gammaSewnCriticalPhysicalPluckerStableEntireDet2_zero_re_im`;
- `tendsto_gammaSewnCriticalPhysicalPluckerStableFiniteDet2`;
- `tendstoUniformlyOn_gammaSewnCriticalPhysicalPluckerStableFiniteDet2`;
- differentiability of both determinant conventions.

Verification uses direct `lake env lean` and target-only module build.  Umbrella import is wired;
no umbrella build is run.
