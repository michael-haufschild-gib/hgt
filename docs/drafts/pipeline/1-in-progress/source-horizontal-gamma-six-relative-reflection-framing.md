# Source-horizontal Gamma-six relative reflection framing

- **ID:** `source-horizontal-gamma-six-relative-reflection-framing`
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) / EXACT NO-GO / FRANKENSTEIN SEAM / NOT RH
- **Source:** `rh-current-frontier-map.md`;
  `source-horizontal-gamma-six-curved-suspension-hodge-trace.md`;
  `RouteRHyperbolicGaugePolarReductionNoGo.lean`;
  `HedenmalmThetaGreenReflectionPairNoGo.lean`;
  `HedenmalmThetaMobiusHyperbolicRapidity.lean`
- **Formal module:**
  `formal/GaloisForLFunctions/RHTower/SourceHorizontalGammaSixRelativeReflectionFraming.lean`
- **Statement:** Gamma-six curved suspension is framed difference of two conjugate involutions.
  Their positive idempotents have same unframed invariants at every grade, while framed relative
  determinant is exactly one quarter of positive Gamma-six curvature. Route-P Cayley coordinate is
  normalized fixed-metric skew of transported idempotent.

## Goal

Determine whether expanded corpus can turn curved-suspension determinant into source-derived
annihilator rather than another RH receiver. Required theorem must preserve forward/reflected
coefficients, fixed source framing, prime labels, and divisor multiplicity.

## Exact construction

For horizontal grade `a`, put

```text
R   = [[0,1],[1,0]],
T_a = [[0,exp(a)],[exp(-a),0]],
H_a = diag(exp(a/2),exp(-a/2)),
D_a = [[0,exp(a)-1],[exp(-a)-1,0]],
P_0 = (I+R)/2,
P_a = (I+T_a)/2.
```

Lean proves unconditionally

```text
R^2=T_a^2=I,
T_a=H_a R H_a^-1,
T_a=R diag(exp(-a),exp(a)),
D_a=T_a-R,
P_a=H_a P_0 H_a^-1,
P_a^2=P_a,
tr(P_a)=tr(P_0)=1,
det(P_a)=det(P_0)=0,
P_a-P_0=D_a/2,
det(P_a-P_0)=K(a)/4,
K(a)=2(cosh(a)-1).
```

Thus every conjugacy, trace, determinant, rank/index, and polar-sign reporter identifies `P_a`
with `P_0` for all `a`. Horizontal displacement lives only in relative fixed framing.

## Heavy conjecture loop

### C0 -- metric commutator compresses to determinant curvature

**Conjecture.** Compress Hedenmalm metric commutator to reflected Xi root pair and use cyclic trace
to obtain positive scalar multiple of `det D_a`.

**Verdict: FALSIFIED BY EXISTING EXACT LAWS.** Signed boundary flux is reflection-odd and pair
trace cancels unconditionally. Squaring removes sign and adds positive pair energy; it supplies no
annihilator. This reproduces `HedenmalmThetaGreenReflectionPairNoGo`, not new source law.

### C1 -- curved suspension is difference of absolute transports

**Conjecture.** Reinterpret `D_a` as relative defect between one fixed source reflection and its
half-density transport.

**Verdict: PROVED.** `D_a=T_a-R`, both `R,T_a` are involutions, and
`T_a=H_a R H_a^-1`. Polar factorization is `T_a=R M_a` with positive diagonal
`M_a=diag(exp(-a),exp(a))`; polar/sign part `R` is constant for every grade.

### C2 -- involution or idempotent class retains horizontal coordinate

**Conjecture.** Spectrum, trace, determinant, or idempotent class of `T_a`/`P_a` detects `a` and
can be combined with source index theorem.

**Verdict: FALSIFIED EXACTLY.** `T_a` is conjugate to `R`; `P_a` is conjugate to `P_0` and both are
trace-one determinant-zero idempotents. Unframed stable/index data erase displacement before any
arithmetic input. This is stronger finite-dimensional model of Route-R polar and measured-index
blindness walls.

### C3 -- relative framed determinant survives erasure

**Conjecture.** Pair `(P_a,P_0)` retains coordinate even though either idempotent alone does not.

**Verdict: PROVED SHARPLY.** `P_a-P_0=D_a/2` and

```text
det(P_a-P_0)=K(a)/4,
det(P_a-P_0)>0 <-> a!=0,
P_a=P_0 <-> a=0.
```

This is positive survivor of C2. Correct carrier is framed pair of conjugate idempotents, not one
stable idempotent class.

### C4 -- source reflection makes transported carrier self-adjoint

**Conjecture.** Functional-equation involution should turn idempotence into orthogonal projection
in fixed physical metric and force `a=0`.

**Verdict: FALSIFIED AS STATED; SAME-FIBRE SURVIVOR PROVED.** Source reflection gives only

```text
P_a^*=P_-a
```

for every `a`. Cross-fibre adjointness is compatible with every off-line pair. Required stronger
law is same-fibre self-adjointness

```text
P_a^*=P_a <-> a=0.
```

At any actual prime clock and multiplicity-labelled Xi divisor copy this condition is equivalent
to critical-line placement. Holding for every copy is equivalent to RH.

### C5 -- Route-P Cayley coordinate is independent extra reporter

**Conjecture.** Julia/Cayley saturation and fixed-metric self-adjointness may be two constraints,
allowing one to force other.

**Verdict: FALSIFIED; STRONGER IDENTITY PROVED.** Define normalized transpose-skew

```text
S(a) = (Re(P_a[0,1])-Re(P_a[1,0]))
       /(Re(P_a[0,1])+Re(P_a[1,0])).
```

Then

```text
S(a)=tanh(a)
    = mobiusCriticalTwoSidedCayleyDiscrepancy(u(a),0),
u(a)=(exp(2a)-1)/2.
```

Route-P Cayley saturation, Route-R fixed-metric positive-polar handoff, equality `T_a=R`, equality
`P_a=P_0`, and Gamma-six flatness are one equation in different coordinates. They cannot prove
one another without a new source input.

### C6 -- Gauss-Hodge mass descends to unframed idempotent invariant

**Conjecture.** Existing Gauss-Hodge Euler current may be derivative of trace/determinant of one
transported idempotent, letting cyclicity kill it.

**Verdict: FALSIFIED AND REPLACED.** Individual trace and determinant are constant. Exact surviving
transgression is

```text
gaussHodgeMassCurrent
  = a * d/da [4 * gaussWeight * Re det(P_(log(p)a)-P_0)].
```

Gauss-Hodge mass is derivative of framed relative determinant only. Cyclicity of an individual
carrier cannot annihilate it.

### C7 -- pinned-mean normalization identifies reflected theta root lines

**Conjecture.** Since every actual theta divisor eigenvector has same nonzero pinned mean and each
nonzero eigenspace is one-dimensional, mean normalization might identify reflected root lines and
force same-fibre framing.

**Verdict: FALSIFIED; SECOND-FUNCTIONAL WELD PROVED.** Reflection changes reciprocal eigenvalue, so
one-dimensionality applies to two different eigenspaces. Equal monopole normalizes each line but
does not identify them. Actual missing coordinate is rank-two boundary flux/centered dipole. Lean
now proves coefficient-faithfully for every prime label and divisor multiplicity copy

```text
artanh(S(log(p) * centeredRate(q)))
  = -log(p) * thetaXiRankTwoBoundaryFlux(q)
      /(thetaMass * thetaXiRootEnergy(q)).
```

Denominator is strictly positive. Therefore fixed-fibre idempotent self-adjointness is equivalent
pointwise to zero genuine theta-root boundary flux. This closes actual root-to-relative-framing
comparison; it still does not provide source annihilation of flux.

## Higher universal principle

All current failures are shadows of one quotient:

> Functional-equation transport supplies conjugacy class and cross-fibre adjointness. Stability,
> index, trace, determinant, transported metrics, and polar sign see only that unframed class.
> Horizontal grade is relative position of two source framings. RH requires a source law that
> rigidifies relative position into equality in one fixed physical metric.

This is why ordinary stabilization accepts raw curvature, why polar normalization erases grade,
why reflected trace cancels, why squared energy remains positive, and why Cayley saturation is an
endpoint rather than producer.

## Exact open producer

Construct an arithmetic theorem, before zero specialization, that promotes the already-proved
cross-fibre identity

```text
P_q^* = P_R(q)
```

to same-fibre orthogonality of actual coefficient-faithful root carrier

```text
P_q^* = P_q.
```

It must use data absent from bare functional equation: literal Euler--Gamma numerical source,
prime labels, divisor multiplicity, and fixed physical Xi metric. Equivalently prove fixed source
diagonal frame is preserved, or framed relative determinant vanishes. Any argument invariant under
positive half-density conjugacy cannot work.

## Formal capstones

- `sourceHorizontalGammaSixCurvedSuspension_eq_reflection_difference`
- `sourceHorizontalGammaSixTransportedReflection_eq_halfDensity_conj`
- `sourceHorizontalGammaSixTransportedReflection_eq_bare_mul_polarMagnitude`
- `sourceHorizontalGammaSixTransportedReflectionIdempotent_eq_halfDensity_conj`
- `det_sourceHorizontalGammaSixTransportedIdempotent_sub_bare`
- `sourceHorizontalGammaSix_unframedIdempotents_blind_but_relativeDet_pos_iff`
- `sourceHorizontalGammaSixFixedMetricSkewRatio_eq_cayleyDiscrepancy`
- `sourceHorizontalGammaSixTransportedReflectionIdempotent_conjTranspose`
- `sourceHorizontalGammaSix_crossFibreAdjoint_but_not_selfAdjoint_iff`
- `gaussHodgeMassCurrent_eq_euler_relativeReflectionDeterminant`
- `sourceHorizontalGammaSixPrimePhysical_artanh_fixedMetricSkewRatio_eq_thetaFlux`
- `sourceHorizontalGammaSixPrimePhysical_idempotentSelfAdjoint_iff_thetaFlux_zero`
- `sourceHorizontalGammaSixPhysicalReflectionIdempotentsSelfAdjoint_iff_riemannHypothesis`

## Gates and status

- [x] 0 → 1: source-pure exact carrier and attack recorded;
- [x] heavy conjecture/fail/pivot loop executed;
- [x] paper algebra dependency-closed;
- [x] Lean declarations unconditional and direct module check green;
- [x] targeted module build green; capstone axiom audit reports only `propext`,
  `Classical.choice`, and `Quot.sound`;
- [x] module wired into `GaloisForLFunctions.RHTower` umbrella;
- [ ] global lint: blocked only by unrelated concurrently owned modules not yet reachable from
  their umbrellas; this module is reachable and not named by lint errors;
- [ ] external novelty audit;
- [ ] arithmetic same-fibre orthogonality producer;
- [ ] RH.

No RH proof is claimed. Terminal theorem is an equivalence; missing left-hand proof is isolated
without hiding it in positivity, admission, or transport assumptions.
