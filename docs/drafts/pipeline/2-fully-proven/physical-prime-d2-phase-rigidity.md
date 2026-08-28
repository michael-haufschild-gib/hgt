# Physical prime D2 phase rigidity

- **ID:** `physical-prime-d2-phase-rigidity`
- **Stage:** 2 — fully proven on paper
- **Type:** THEOREM / NO-GO (Lean)
- **Source route:** D2 / FCRJ physical corrected-prime contour
- **Statement:** Scalar D2 real-part floors transmit pointwise through squared physical contour
  weights exactly at real transform phase; D2 and all-schedule physical negative witnesses are
  nevertheless globally equivalent.

## Goal

Determine whether D2's scalar lower bound on `2 Re(infinitePrimeFlux)-log(height)` can directly
supply the remaining corrected-prime contour zero-floor. Close the naive pointwise route if complex
phase prevents it, while retaining the strongest exact cross-route witness theorem.

## Gates

- [x] 0 → 1 in-progress: corpus-derived phase-rigidity conjecture and route map
- [x] 1 → 2 fully-proven: dependency-closed proof and no-go classification
- [x] 2 → 3 formalized: closed Lean theorems, direct check, targeted build, axiom audit
- [ ] 3 → 4 publication-ready: standalone theorem/no-go note

## Exact theorem

For `w : ℂ`, let `M(w)` mean that multiplication by `w` preserves the preorder induced by real
part on every pair of complex numbers. Lean proves the exact classifiers

```text
M(w)   <-> Im(w)=0 and Re(w)>=0,                            (1)
M(v^2) <-> Im(v)=0.                                         (2)
```

Hence the squared physical two-edge contour weight transmits a scalar prime-defect floor exactly
when the unsquared transform has real phase. Under that phase condition, every D2 floor
`K <= 2 Re(infinitePrimeFlux(s))-log(Im s)` yields the corresponding weighted complex-defect floor.

An `EvenSchwarzRealEntireMode` is an entire mode satisfying `f(-z)=f(z)` and
`conj(f(z))=f(conj z)`. The exact symmetry-fixed locus is

```text
[every even Schwarz-real entire mode is real at z]
  <-> Im(z)=0 or Re(z)=0.                                   (3)
```

The reverse direction is sharp: at every off-axis point, the entire polynomial `f(z)=z^2` obeys
both symmetries and has nonzero imaginary part. The physical two-edge transform belongs to this
class. D2's coordinate map

```text
z(s)=-i(s-1/2),  1/2+i z(s)=s,
Re z(s)=Im s,     Im z(s)=1/2-Re s                          (4)
```

sends every D2 point `0<Re s<1/2`, `Im s>233/20` strictly off both axes. Thus evenness,
Schwarz reality, and entireness do not supply the missing phase condition on D2's contour edge.

Finally define D2 cofinal unboundedness below by requiring, below every proposed floor, a
Gaussian-rational point in that tail. Lean proves

```text
D2 defect cofinally unbounded below <-> not RH,              (5)

D2 defect cofinally unbounded below
  <-> every cofinal admissible corrected-prime schedule
      has one eventually uniformly negative physical sample. (6)
```

The closed unit-detector form of `(6)` is included.

## Proof

For `(1)`, testing the multiplier on `0,I` and `I,0` kills its imaginary part; testing `0,1`
forces nonnegative real part. The converse is ordinary monotonicity under nonnegative real
scaling. Expanding `v^2` proves `(2)`: a nonnegative-real square forces the base imaginary part to
vanish.

For `(3)`, conjugation fixes the real axis and equals negation on the imaginary axis; Schwarz
reality and evenness therefore force real values there. Off both axes, `Im(z^2)=2 Re(z) Im(z)` is
nonzero, giving the entire sharpness witness. Formula `(4)` is exact complex algebra and puts every
D2 point off-axis.

For `(5)`, RH supplies the previously proved common D2 lower bound, contradicting cofinal
unboundedness. Failure of RH supplies a point below every floor by the existing pure-prime tail
escape theorem. Both `(5)` and Loop 89's all-schedule negative-witness theorem are exactly
`not RH`, yielding `(6)`.

## No-go closure

- **Exact killing theorem/mechanism:** `(2)--(4)` prove that a pointwise transfer from the scalar
  D2 floor through a squared complex contour weight requires real physical-transform phase, while
  D2 geometry lies outside the entire even/Schwarz symmetry-fixed locus. Those symmetries alone
  cannot provide the missing positivity.
- **Strongest positive survivor:** conditional weighted-floor transport at real phase, exact
  axis classification `(3)`, and global D2/all-contour failure dictionary `(5)--(6)`.
- **New insight:** D2 and physical corrected-prime contours share a global RH obstruction but not a
  pointwise positive-kernel mechanism. A successful direct weld must add a phase identity,
  conjugate-edge pairing, or an imaginary-prime-flux estimate; scalar real-part control plus
  even/Schwarz symmetry is formally insufficient.
- **Status:** dependency-closed; Lean module verified and wired.

## Lean certificate

- Module:
  `formal/GaloisForLFunctions/RHTower/XiPhysicalPrimeApertureThetaAbelEnergyPrimeD2PhaseRigidity.lean`
- Umbrella: `formal/GaloisForLFunctions/RHTower.lean`
- Direct check: PASS
- Targeted build: PASS (`12918/12918`)
- Axiom audit: `[propext, Classical.choice, Quot.sound]`
- Principal declarations:
  `ComplexRealPartMonotoneMultiplier`,
  `complexRealPartMonotoneMultiplier_iff`,
  `complexRealPartMonotoneMultiplier_sq_iff`,
  `EvenSchwarzRealEntireMode`,
  `all_evenSchwarzRealEntireMode_real_iff_axis`,
  `gaussianRat_d2Point_evenSchwarzRealEntireMode_phase_not_forced`,
  `physicalTwoEdge_weighted_primeArchLogHeightComplexDefect_floor`,
  `primeArchLogHeightDefectGaussianRatPositiveFrequencyAboveCofinallyUnboundedBelow_iff_not_rh`,
  `d2CofinallyUnboundedBelow_iff_allPrimeCofinalSchedulesEventuallyNegativeWitness`

## Route impact and remaining burden

This closes the most direct D2-to-physical-contour positivity proposal. D2's real-part bound cannot
be multiplied pointwise by the squared off-axis physical kernel using only its established
symmetries. The surviving proof options are narrower and explicit: prove the actual physical
transform real on the relevant off-axis D2 locus, pair contour edges so phases cancel before order
is applied, control the missing imaginary part of prime flux, or prove the corrected-prime floor
by a genuinely global arithmetic estimate. Equation `(6)` shows these are representations of one
failure, but it does not prove RH.

## Novelty audit

Targeted corpus and primary-literature searches through 2026-08-27 found no exact classification
of the symmetry-fixed real-phase locus for these physical two-edge weights, no D2 strip-to-contour
phase obstruction, and no D2/all-cofinal-corrected-prime failure-witness dictionary. Recent work on
logarithmic-derivative bounds controls real parts or moduli, while Weil/screw-function work packages
positivity through test-function or operator structure; none states `(1)--(6)` for this physical
prime contour. Candidate-new content is restricted to this route-specific synthesis.

Primary comparison points:

- A. Chirre and B. Molero Ravines, [*Explicit conditional bounds for ζ(s) at the edge of the
  critical strip*](https://arxiv.org/abs/2602.06199).
- M. Suzuki, [*Weil's quadratic form via the screw function*](https://arxiv.org/abs/2606.09096).
- T. Kim et al., [*A Numerical Realization of Suzuki's Weil-Quadratic-Form Operator*](https://arxiv.org/abs/2607.24830).
- A. Connes and C. Consani, [*The Scaling Hamiltonian*](https://arxiv.org/abs/1910.14368).

## Log

- 2026-08-27 — Mandatory corpus search found the exact D2 defect and physical prime contour, but no
  scalar-to-complex weighted floor bridge.
- 2026-08-27 — Conjectured complex real-part multiplier classification, symmetry-axis boundary,
  and global D2/FCRJ witness equivalence.
- 2026-08-27 — Proved multiplier and square classifiers, exact entire-symmetry locus, D2 off-axis
  geometry, and conditional weighted-floor survivor.
- 2026-08-27 — Proved D2 cofinal-unboundedness iff false RH and iff eventual negativity on every
  cofinal physical corrected-prime schedule.
- 2026-08-27 — Direct check, targeted `12918/12918` build, standard axiom audit, and wiring passed.
- 2026-08-27 — Global lint reached the new wired module with no local violation; repository-wide
  gate remains blocked only by unrelated concurrently edited unwired RHTower/HTGeometry modules.
