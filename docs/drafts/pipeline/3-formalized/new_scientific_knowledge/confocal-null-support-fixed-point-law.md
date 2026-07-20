# Confocal null-support fixed-point law

- **ID:** `confocal-null-support-fixed-point-law`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Scientific status:** `[NEW SCIENTIFIC KNOWLEDGE — INTERNAL NOVELTY AUDIT PASSED]`
- **Statement:** Every exterior confocal distance-sum envelope of a bounded Lorentz source is the
  unique nonnegative fixed point of its ordinary null-coordinate support function under one
  projective scalar map; the fixed-point operator has the universal contraction modulus `M / R`.

## Goal

Replace the route's degree-dependent estimates and presentation-specific geometry by one universal
law.  The law must apply to every nonempty bounded source in the two-dimensional Lorentz cone,
without atomicity, moment, Bernstein, differential-algebraic, or RH assumptions.

## Exact theorem

Let

```text
C = {(x,a) in R^2 : |x| <= a},
u(x,a) = a-x,
v(x,a) = a+x,
ell_lambda(x,a) = u(x,a)+lambda v(x,a),
h_S(lambda) = sup_{q in S} ell_lambda(q).
```

For `R>0` and `d>=0`, define the projective parameter and support operator

```text
lambda_R(d) = d/(2R+d),
Phi_(S,R)(d) = h_S(lambda_R(d)).
```

For a nonempty source `S subset C` satisfying `a(q)<=M` for every `q in S`, with
`0<=M<R`, let

```text
G_S(R) = sup_(q in S) [a(q)+sqrt(R^2-2R x(q)+a(q)^2)],
D_S(R) = G_S(R)-R.
```

Then:

1. **Pointwise projective linearization.**  For every `q in C` with `a(q)<R` and every
   `d>=0`,

   ```text
   g_R(q) <= R+d  iff  ell_(lambda_R(d))(q) <= d.       (PL)
   ```

2. **Universal fixed-point law.**  The exterior envelope defect is the unique nonnegative
   solution of

   ```text
   d = Phi_(S,R)(d).                                    (FP)
   ```

   Equivalently,

   ```text
   D_S(R) = h_S(D_S(R)/(2R+D_S(R))).
   ```

3. **Universal contraction law.**  On the nonnegative half-line,

   ```text
   |Phi_(S,R)(d)-Phi_(S,R)(e)| <= (M/R)|d-e|.           (CL)
   ```

   Since `M/R<1`, the fixed point is unique.  The modulus is independent of the cardinality,
   topology, atomicity, or presentation of `S`.

   The modulus is optimal.  For the singleton null-ray source `S={(M,M)}`,

   ```text
   Phi_(S,R)(d)=2M d/(2R+d),
   ```

   so every proposed nonnegative modulus `c<M/R` fails for some `d>0`.

4. **Support-field stability.**  If `S,T` obey the same radius bound and

   ```text
   sup_(0<=lambda<=1) |h_S(lambda)-h_T(lambda)| <= epsilon,
   ```

   then

   ```text
   |D_S(R)-D_T(R)| <= epsilon/(1-M/R).                  (ST)
   ```

5. **Exact radical.**  `D_S(R)=0` exactly when `h_S(0)=0`, equivalently every occupied
   Lorentz point lies on the positive null ray `a=x>=0`.  Thus the only zero mode of the
   projective support dynamics is the positive-real source ray.

6. **Dimension-free form.**  Let `E` be any real inner-product space, fix a unit vector `e`,
   and lift

   ```text
   z |-> (<z,e>, ||z||).
   ```

   Then

   ```text
   ||z||+||R e-z||
   ```

   is exactly the lifted Lorentz branch.  Hence (PL), (FP), (CL), (ST), the sharp modulus, and
   the radical classification hold verbatim for arbitrary bounded sources in `E`.  The law is
   therefore independent of ambient dimension as well as source cardinality.

## Proof

### 1. Null-coordinate linearization

For `q=(x,a) in C`, put

```text
g_R(q)=a+sqrt(R^2-2Rx+a^2).
```

The already proved Lorentz half-space identity is

```text
g_R(q)<=L
iff
a<=L and Rx-La >= (R^2-L^2)/2.                         (1)
```

Set `L=R+d`.  Since `a<R<=R+d`, the first inequality is automatic.  Multiplying the
second inequality by two and using `u=a-x`, `v=a+x` gives

```text
d v +(2R+d)u <= d(2R+d).
```

Because `2R+d>0`, division gives exactly

```text
u + [d/(2R+d)]v <= d,
```

which is (PL).

### 2. The envelope is a fixed point

Let `D=D_S(R)`.  Every branch is at least `R` and at most `G_S(R)`, so `D>=0` and
`g_R(q)<=R+D` for every `q in S`.  By (PL),

```text
ell_(lambda_R(D))(q)<=D.
```

Hence `h_S(lambda_R(D))<=D`.

Conversely, suppose `b` is an upper bound for all values of
`ell_(lambda_R(D))`.  For each `q`, write `d_q=g_R(q)-R`.  Then `0<=d_q<=D`; the map
`lambda_R` is increasing; and `v(q)>=0`.  Applying (PL) at equality to `d_q` gives

```text
d_q=ell_(lambda_R(d_q))(q)
   <=ell_(lambda_R(D))(q)
   <=b.
```

Taking the least upper bound of the branch defects yields `D<=b`.  Thus `D` is the least
upper bound of the null functional and

```text
D=h_S(lambda_R(D)).
```

### 3. Contraction and uniqueness

For `d,e>=0`, direct subtraction gives

```text
|lambda_R(d)-lambda_R(e)|
 = 2R|d-e|/[(2R+d)(2R+e)]
 <= |d-e|/(2R).                                        (2)
```

On the Lorentz cone, `0<=v=a+x<=2a<=2M`.  Therefore ordinary support-function comparison
gives, for `lambda,mu in [0,1]`,

```text
|h_S(lambda)-h_S(mu)|<=2M|lambda-mu|.                  (3)
```

Combining (2) and (3) proves (CL).  If `d,e` are two nonnegative fixed points, then

```text
|d-e|<= (M/R)|d-e|.
```

As `M/R<1`, this forces `d=e`.  Together with the fixed point already supplied by the
envelope, this proves (FP).

### 4. Stability

Let `D_S,D_T` be the two fixed points.  Add and subtract
`h_S(lambda_R(D_T))`, then use (CL) for the first difference and the support-field error for
the second:

```text
|D_S-D_T| <= (M/R)|D_S-D_T|+epsilon.
```

Rearrangement proves (ST).

### 5. Radical

If `D=0`, (FP) gives `h_S(0)=0`.  Since `u=a-x>=0` on `C`, a nonempty source has
`h_S(0)=0` exactly when `u=0` at every source point, i.e. `a=x>=0`.  Conversely such points
have `g_R(q)=R` whenever `R>a`, so `D=0`.

### 6. Sharpness and dimension-free reduction

For `S={(M,M)}`, direct evaluation gives

```text
h_S(lambda)=2M lambda,
Phi_(S,R)(d)=2M d/(2R+d).
```

The difference quotient against `d=0` is `2M/(2R+d)`.  Given any `0<=c<M/R`, choosing
`d=(M-cR)/(c+1)>0` makes this quotient strictly larger than `c`.  Thus `M/R` is the least
uniform contraction modulus.

For a unit vector `e` in a real inner-product space, Cauchy--Schwarz places
`(<z,e>,||z||)` in the Lorentz cone, and polarization gives

```text
||R e-z||^2=R^2-2R<z,e>+||z||^2.
```

Taking the nonnegative square root identifies the arbitrary-dimensional branch with the
two-dimensional lifted branch.  The full theorem follows by applying the Lorentz law to the
image of the source under this axial lift.

## Why this is a universal law

The nonlinear moving-focus envelope in every real inner-product space has been reduced exactly to
the fixed point of a one-variable contraction built from an ordinary linear support function.  No
feature of the source other than one radius bound enters the sharp contraction modulus.  The result
simultaneously classifies the field, its stability, its radical, and its presentation quotient.

The prior confocal hull theorem is recovered by intersecting the half-spaces
`ell_(lambda_R(D_R))<=D_R`; exposed orbit recovery becomes ordinary support-face recovery.  The
Bernstein--Abel theorem supplies a particular source field to which this universal law applies,
but is not used in its proof.

## Novelty audit

Targeted comparison covered:

- classical support functions and support-face reconstruction;
- focal functions and Minkowski-style theorems for convex reflectors, especially V. Oliker,
  *A Minkowski-style theorem for focal functions of compact convex reflectors*, Trans. AMS 360
  (2008), 563--574, DOI `10.1090/S0002-9947-07-04569-2`;
- semidefinite and algebraic representations of `k`-ellipses;
- standard confocal-ellipse and Lorentz-cone geometry.

Those theories provide parent language, but the audit found no prior statement of the
null-coordinate projective identity (PL), the self-consistent fixed-point equation (FP), or the
source-independent contraction modulus `M/R`.  The novelty claim is the exact conjunction
`(PL)+(FP)+(CL)`, not support functions or contraction mappings separately.

## Gates

- [x] 0 -> 1: source-pure universal statement and complete proof architecture
- [x] attack as false: positive-null-ray radical and `R=M` contraction boundary classified
- [x] targeted parent-literature comparison found no theorem match
- [x] 1 -> 2: dependency-closed paper proof, including sharpness and dimension-free reduction
- [x] 2 -> 3: unconditional Lean theorem, exact module build, and axiom audit
- [ ] 3 -> 4: integrate as the single paper theorem

## Formalization target

`formal/GaloisForLFunctions/HTGeometry/ConfocalNullSupportFixedPoint.lean`

Required theorem surface:

- `liftedConfocalBranch_le_add_iff_nullFunctional_le`
- `confocalProjectiveParameter_lipschitz`
- `confocalNullSupport_lipschitz`
- `confocalEnvelopeDefect_eq_nullSupport_fixedPoint`
- `confocalNullSupport_fixedPoint_unique`
- `confocalEnvelopeDefect_eq_iff_nullSupport_fixedPoint`
- `confocalEnvelopeDefect_stability`
- `confocalEnvelopeDefect_eq_zero_iff_positiveNullRay`
- `confocalNullSupportOperator_contraction_modulus_optimal`
- `liftedConfocalBranch_axialLorentzLift`
- `axialEnvelopeDefect_eq_iff_nullSupport_fixedPoint`

The exact development check

```text
lake env lean GaloisForLFunctions/HTGeometry/ConfocalNullSupportFixedPoint.lean
```

passes without diagnostics.  The final module audit

```text
lake build GaloisForLFunctions.HTGeometry.ConfocalNullSupportFixedPoint
```

passes.  The headline axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Log

- 2026-07-19 -- extracted by rewriting the self-consistent confocal half-space normal in Lorentz
  null coordinates; internal novelty audit passed against support-function, focal-function,
  reflector, and `k`-ellipse parents.
- 2026-07-19 -- strengthened to the optimal modulus and arbitrary real inner-product spaces;
  promoted after exact Lean development, module, and axiom audits.

## Global projective support--envelope duality (2026-07-20 strengthening)

The pointwise fixed-point law assembles into a strictly stronger global classification.  Define

```text
rho_S(lambda)=h_S(lambda)(1-lambda)/(2lambda).
```

If `h_S(0)>0` (equivalently, the source is outside the positive-null radical), then

```text
{(R,D_S(R)): R>M}
 = {(rho_S(lambda),h_S(lambda)):
      0<lambda<1 and rho_S(lambda)>M}.                     (GD)
```

Moreover `rho_S` is injective on the displayed admissible domain and the inverse coordinate is

```text
lambda=D_S(R)/(2R+D_S(R)).                                (GI)
```

Thus the complete nonlinear exterior envelope and the admissible part of the ordinary linear
support graph are not merely related pointwise: they are two coordinates on the same object.  The
radical is the complementary exact case `D_S(R)=0` for every `R>M`.

The proof is algebraic but global.  The fixed-point law gives `D=h(lambda)` at
`lambda=D/(2R+D)`; nonradicality makes `D,lambda` positive, and solving for `R` gives `(GD)`.
Conversely, a point of the support graph makes `h(lambda)` a nonnegative fixed point at radius
`rho_S(lambda)`, so uniqueness recovers the envelope.  Two parameters with the same admissible
radius therefore give the same unique defect, and `(GI)` forces the parameters to coincide.

The formal theorem surface is:

- `confocalRadiusFromProjective`;
- `confocalProjectiveParameter_radiusFromProjective`;
- `confocalRadiusFromProjective_projectiveParameter`;
- `confocalNullSupport_mono`;
- `confocalNullSupportRadius`;
- `confocalExteriorDefectGraph_eq_projectiveSupportGraph`;
- `confocalNullSupportRadius_injective_on_exterior`;
- `confocalNullSupport_eq_on_common_exterior_trace`;
- `confocalNullSupport_lorentzLift_zero_eq_transverseDefectEnvelope`.

The exact source-file check passes with no diagnostics.  This strengthening is now integrated into
the single main theorem of the publication manuscript.  The earlier gate “3 -> 4: integrate as the
single paper theorem” is therefore closed for the mathematical content; final typesetting and
publication audit remain document-level tasks.

**Final formal audit (2026-07-20).**  The focused module build
`lake build GaloisForLFunctions.HTGeometry.ConfocalNullSupportFixedPoint` passes.  A scratch
`#print axioms` audit of every new global-duality declaration reports only `propext`,
`Classical.choice`, and `Quot.sound`; there are no project axioms or conditional scientific
hypotheses.
