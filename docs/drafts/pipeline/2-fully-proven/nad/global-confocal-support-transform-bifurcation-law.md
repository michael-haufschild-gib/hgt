# Global confocal-support transform and null-radical bifurcation law

- **ID:** `global-confocal-support-transform-bifurcation-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / CONVEX GEOMETRY / CONFOCAL ENVELOPES / PROJECTIVE DUALITY
- **Scientific status:** `[PAPER-PROVED] [NOVELTY UNVERIFIED]`
- **Statement:** For every nonempty bounded Lorentz source, its confocal distance-sum field on all
  positive radii, its complete null-support field, and its maximal Lorentz hull determine one
  another by an explicit projective transform.  The realized defect is the greatest nonnegative
  support fixed point at every radius.  Off the null radical it is the unique fixed point; on the
  radical it undergoes an exact finite-radius extinction bifurcation.

## Goal

Remove the artificial exterior restriction `R>M` from the geometric half of the bicompletion
paper.  The contraction estimate genuinely requires `R>M`; the projective support-envelope
classification does not.  The stronger theorem must classify the interior branch and the positive
null radical rather than silently discarding them.

## Setup

Let

```text
C = {(x,a) in R^2 : |x|<=a}
```

and let `S` be a nonempty subset of `C` for which `a<=M` on `S`, with `M>=0`.  Put

```text
b_q(R) = a + sqrt(R^2 - 2 R x + a^2),
G_S(R) = sup_(q in S) b_q(R),
D_S(R) = G_S(R)-R,                                  R>0.       (1)
```

In null coordinates

```text
u(q)=a-x,       v(q)=a+x,
h_S(lambda)=sup_(q in S) [u(q)+lambda v(q)],        0<=lambda<=1,
lambda_R(d)=d/(2R+d),
rho_S(lambda)=((1-lambda)/(2lambda))h_S(lambda),    0<lambda<1. (2)
```

Define the complete positive-defect and projective support graphs by

```text
Gamma_D(S)={(R,D_S(R)):R>0, D_S(R)>0},
Gamma_h(S)={(rho_S(lambda),h_S(lambda)):
             0<lambda<1, h_S(lambda)>0}.                    (3)
```

Finally let

```text
K_h(S)={q in C : u(q)+lambda v(q)<=h_S(lambda)
                  for every 0<=lambda<=1},                  (4)
```

and let `K_G(S)` be the largest Lorentz source whose confocal branches lie below `G_S(R)` for
every `R>0`.

## Main theorem `[PAPER-PROVED]`

For every source above:

1. The actual defect is a support fixed point at every positive radius,

   ```text
   D_S(R)=h_S(lambda_R(D_S(R))).                             (5)
   ```

   More strongly, it is the greatest nonnegative solution of

   ```text
   d=h_S(lambda_R(d)).                                      (6)
   ```

   There is at most one positive solution.

2. The complete positive-defect graph is exactly projective:

   ```text
   Gamma_D(S)=Gamma_h(S).                                   (7)
   ```

   On this graph the inverse coordinate is

   ```text
   lambda=D_S(R)/(2R+D_S(R)).                               (8)
   ```

3. If `h_S(0)>0`, then `rho_S` is a decreasing homeomorphism

   ```text
   (0,1) -> (0,infinity),                                  (9)
   ```

   `D_S(R)>0` for every `R>0`, and `(5)` has exactly one nonnegative solution for every radius.

4. If `h_S(0)=0`, then every source point lies on the positive null ray.  With

   ```text
   A_S=h_S(1)/2=sup_(q in S) q.2,                           (10)
   ```

   one has the exact radical law

   ```text
   h_S(lambda)=2A_S lambda,
   rho_S(lambda)=A_S(1-lambda),
   D_S(R)=2 max(A_S-R,0).                                  (11)
   ```

   Thus zero is always a fixed point; a second, positive fixed point exists exactly for
   `0<R<A_S`, and the realized defect is that positive branch.  At `R=A_S` the two branches merge
   and the defect vanishes identically thereafter.

5. The two nonlinear transforms are mutually faithful:

   ```text
   D_S=D_T on (0,infinity)  <->  h_S=h_T on [0,1]           (12)
   ```

   for any two nonempty bounded Lorentz sources.  Their common field determines the exact maximal
   quotient

   ```text
   K_G(S)=K_h(S).                                          (13)
   ```

Consequently the all-radius confocal field, the full one-dimensional null support, and the maximal
Lorentz hull are three coordinates on the same quotient object.  The exterior contraction theorem
is the stable large-radius chart of this global transform, not its domain of validity.

## Paper proof

### 1. Null positivity and a global branch identity

For `q=(x,a) in C`, put `u=a-x` and `v=a+x`.  Then `u,v>=0` and `u+v=2a`.
The radicand in `(1)` is

```text
(R-x)^2+(a^2-x^2)>=0.                                     (14)
```

Since `a>=|x|`, direct comparison with `|R-x|` gives `b_q(R)>=R` for every `R>=0`.
Hence

```text
d_q(R)=b_q(R)-R>=0.                                       (15)
```

The defining square identity for `b_q(R)` gives

```text
2R(d_q-u)+d_q^2-2a d_q=0.                                 (16)
```

Because `2R+d_q>0`, `(16)` is equivalent to

```text
d_q(R)=u+lambda_R(d_q(R))v.                               (17)
```

This is the pointwise projective identity without any assumption that the focus lies outside the
source radius.

We also need the global sublevel form.  If `d>=0` and `a<=R+d`, then squaring is legitimate and
the standard Lorentz half-space calculation gives

```text
b_q(R)<=R+d  <->  u+lambda_R(d)v<=d.                       (18)
```

The former exterior proof used `a<R` only to infer `a<=R+d`; equation `(18)` records the exact
hypothesis actually needed.

### 2. The envelope fixed point at every radius

Fix `R>0`, write `D=D_S(R)`, and let `lambda=lambda_R(D)`.  Boundedness of `S` makes all suprema
finite.  From `(15)` and nonemptiness, `D>=0`.

For every `q in S`, the least-upper-bound property gives `d_q(R)<=D`.  Monotonicity of
`lambda_R` and `v(q)>=0`, followed by `(17)`, gives

```text
d_q(R)
 =u(q)+lambda_R(d_q(R))v(q)
 <=u(q)+lambda v(q)
 <=h_S(lambda).                                           (19)
```

Taking the supremum yields `D<=h_S(lambda)`.

Conversely `b_q(R)<=G_S(R)=R+D`, and `a<=b_q(R)<=R+D`.  Equation `(18)` therefore gives

```text
u(q)+lambda v(q)<=D                                       (20)
```

for every `q in S`.  Taking the supremum gives `h_S(lambda)<=D`.  Together with `(19)` this proves
`(5)` for every `R>0`.

### 3. Strict projective radius order

Assume first that `S` contains a nonzero point.  Then `h_S(lambda)>0` for every `lambda in (0,1)`.
For one source point define

```text
r_q(lambda)=((1-lambda)/(2lambda))[u(q)+lambda v(q)].      (21)
```

For `0<lambda<mu<1`, direct subtraction gives

```text
r_q(lambda)-r_q(mu)
 =u(q)/2 (1/lambda-1/mu)+v(q)/2 (mu-lambda).               (22)
```

Let `c` be half the smaller of the two positive coefficients in `(22)`.  Choose points of `S`
whose `u+mu v` values tend upward to `h_S(mu)`.  Since `u+v>=u+mu v`, equation `(22)` gives

```text
rho_S(lambda)>=rho_S(mu)+c h_S(mu)>rho_S(mu).              (23)
```

Thus `rho_S` is strictly decreasing.  The bounded support field is Lipschitz, so `rho_S` is
continuous on `(0,1)`.  Also `rho_S(lambda)->0` as `lambda->1-`.

If `h_S(0)>0`, then `rho_S(lambda)->infinity` as `lambda->0+`, proving `(9)`.

### 4. Exact graph equality and greatest-fixed-point selection

Suppose first that `D_S(R)>0`.  Equation `(5)` and the algebraic inverse identities give

```text
R=rho_S(lambda_R(D_S(R))),
D_S(R)=h_S(lambda_R(D_S(R))).                              (24)
```

This proves `Gamma_D(S) subset Gamma_h(S)` and `(8)`.

Conversely fix `0<lambda<1` with `d=h_S(lambda)>0` and put `R=rho_S(lambda)>0`.
Then `lambda_R(d)=lambda`, so `d` is a positive solution of `(6)`.  Let `D=D_S(R)`, which satisfies
`(5)`.

If `D<d`, choose `e` strictly between them.  Every branch is at most `R+D<R+e`, so `(18)` gives

```text
h_S(lambda_R(e))<=e.                                      (25)
```

Consequently

```text
rho_S(lambda_R(e))<=((1-lambda_R(e))/(2lambda_R(e)))e=R.  (26)
```

But `e<d` implies `lambda_R(e)<lambda_R(d)=lambda`; strict decrease `(23)` gives the opposite
strict inequality.  Hence `D>=d`.

If `D>d`, the same argument with the roles of `D` and `d` replaced is unnecessary: both are
positive fixed points, so `(24)` gives

```text
rho_S(lambda_R(D))=R=rho_S(lambda_R(d)).                  (27)
```

Strict injectivity of `rho_S` and injectivity of `lambda_R` give `D=d`.  Thus `(7)` holds.  The
same reasoning shows that every positive solution of `(6)` is the actual defect and hence that
there is at most one.

If `S={(0,0)}`, then `h_S=0` and `D_S=0`, so the positive graphs are both empty and all conclusions
above remain valid after the evident degenerate interpretation.

Since the actual defect is always a nonnegative fixed point, and every positive fixed point equals
it, the actual defect is the greatest nonnegative fixed point.  If `h_S(0)>0`, zero is not a fixed
point, while `(5)` and monotonicity give `D_S(R)>=h_S(0)>0`; this proves the uniqueness assertion in
clause 3.

### 5. Radical bifurcation

Suppose `h_S(0)=0`.  Since every `u(q)>=0`, one has `u(q)=0` for every source point.  Hence
`x=a>=0`, the source lies on the positive null ray, and

```text
h_S(lambda)=lambda sup_(q in S)v(q)=2A_S lambda.           (28)
```

Substitution into `(6)` gives

```text
d=2A_S d/(2R+d),
d[d-2(A_S-R)]=0.                                          (29)
```

The greatest nonnegative solution is exactly `2 max(A_S-R,0)`, proving `(11)` and the complete
bifurcation statement.  Conversely a source on the positive null ray has `h_S(0)=0`, so this is an
exact classification rather than a one-way implication.

### 6. Faithfulness of the nonlinear transform

If `h_S=h_T`, then the two fixed-point equations `(6)` have the same greatest nonnegative solution
at every radius, so `D_S=D_T`.

Conversely assume `D_S=D_T`.  If `S` contains a nonzero point, fix `lambda in (0,1)`.  By `(7)`, at

```text
R=rho_S(lambda)
```

the common defect is positive and equals `h_S(lambda)`.  Formula `(8)` recovers the same `lambda`
from the common pair `(R,D(R))`; applying `(5)` to `T` yields

```text
h_T(lambda)=D_T(R)=D_S(R)=h_S(lambda).                    (30)
```

If `S` is the zero source, then `D_S` vanishes identically.  Equation `(7)` shows that a nonzero
`T` would have a nonempty positive-defect graph, so `T` is also the zero source.  Thus the support
fields agree on `(0,1)` in all cases, and continuity supplies the endpoints.  This proves `(12)`.

### 7. Equality of the maximal hulls

If `S={(0,0)}`, then `G_S(R)=R` for every `R>0`.  A Lorentz point `q` whose branch lies
below this field for every positive radius must have `u(q)=v(q)=0`: a point with `u(q)>0`
has positive defect at every radius, while a point with `u(q)=0<v(q)` has positive defect for
every radius below `q.2`.  Hence `K_G(S)={(0,0)}`.  The defining inequalities in `(4)` give
the same conclusion for `K_h(S)`.  We may therefore assume below that `S` contains a nonzero
point, so `h_S(lambda)>0` throughout `(0,1)`.

First suppose `q in K_G(S)`.  For every `lambda in (0,1)` with `h_S(lambda)>0`, take the graph
point `(R,d)=(rho_S(lambda),h_S(lambda))`.  The field inequality gives

```text
b_q(R)<=R+d.
```

Since `a<=b_q(R)`, equation `(18)` gives `u(q)+lambda v(q)<=h_S(lambda)`.  Continuity supplies the
endpoints, so `q in K_h(S)`.

Conversely let `q in K_h(S)` and fix `R>0`.  If `D_S(R)>0`, put
`lambda=lambda_R(D_S(R))`.  Then

```text
u(q)+lambda v(q)<=D_S(R).                                 (31)
```

Because `u,v>=0`, `(31)` implies

```text
2a=u+v<=(u+lambda v)/lambda
   <=D_S(R)/lambda=2R+D_S(R)<=2(R+D_S(R)).                (32)
```

Thus `a<=R+D_S(R)`, and `(18)` gives `b_q(R)<=G_S(R)`.

If `D_S(R)=0`, clause 3 excludes the transverse case.  Clause 4 gives `u(q)=0` and
`a<=A_S<=R`, whence `b_q(R)=R=G_S(R)`.  Therefore `q in K_G(S)` and `(13)` follows.

Every step uses only order completeness of `R`, the Lorentz cone inequalities, and elementary
projective algebra.  No compactness, attainment, differentiability, finite support, or exterior
radius is assumed.

## Hostile proof audit

1. **Small-radius branch ambiguity.**  Below the source radius the fixed-point equation may have
   two nonnegative roots.  The theorem does not claim uniqueness there: it proves greatest-root
   selection and classifies the second root exactly on the radical.
2. **Unattained suprema.**  The proof uses only least-upper-bound inequalities.  The sole
   approximating sequence in `(23)` is the defining property of a finite real supremum; no active
   source point is assumed.
3. **Zero source.**  The singleton zero source is split explicitly; otherwise `h(lambda)>0` on
   `(0,1)` and strict projective order applies.
4. **Hidden exterior assumption.**  The only sublevel step uses `a<=R+d`.  For the actual field it
   follows from `a<=b_q(R)<=G_S(R)`; for the reverse hull direction it follows from `(32)`.
5. **Radical circularity.**  The extinction law comes from `h(0)=0`, nonnegativity of every null
   coordinate, and the factored fixed-point equation `(29)`, not from an exterior zero theorem.

The dependency-closed proof survives these attacks and the source-level formalization design
audit.  The higher-dimensional master theorem is developed separately by applying this exact
fiber law to every unit direction of a Lorentz cone.

## Preliminary novelty audit

Classical support-function theory reconstructs a closed convex body from all linear support
directions.  Oliker's focal-function Minkowski theorem characterizes convex reflectors generated by
confocal paraboloids.  Neither parent found in the first audit states the all-radius distance-sum
transform `(7)`, greatest-fixed-point selection `(6)`, exact null-radical extinction `(11)`, or the
three-way quotient equivalence `(12)`--`(13)`.

Closest primary comparison:

- V. I. Oliker, *A Minkowski-style theorem for focal functions of compact convex reflectors*,
  <https://arxiv.org/abs/math/0612757>.
- R. Schneider, *Convex Bodies: The Brunn--Minkowski Theory*, support-function reconstruction.

Exact-formula searches for the rational coordinate `d/(2R+d)`, distance-sum envelopes in Lorentz
null coordinates, and all-radius confocal/support graph inversion found no matching theorem.  This
is not a priority proof; status remains `[NOVELTY UNVERIFIED]` pending a citation-graph audit after
formal verification.

## Gates

- [x] exact global statement isolated
- [x] complete paper proof written
- [x] small-radius multiple-root obstruction classified positively
- [x] zero source and unattained-supremum cases audited
- [x] preliminary parent-theory and exact-formula search completed
- [x] final hostile source-level proof audit
- [x] move to Stage 2 as `[PAPER-PROVED]`
- [x] formalize the exact theorem and all missing general-radius lemmas (`ConfocalGlobalSupportTransform.lean` + `ConfocalGlobalSupportFaithfulness.lean`)
- [x] run one narrow source check and final module build
- [x] axiom audit (`[propext, Classical.choice, Quot.sound]`)
- [ ] incorporate the strengthened single theorem into the manuscript

## Log

- 2026-07-20 -- The exterior graph theorem was interrogated at `R<=M`.  The contraction fails
  there, but the geometry does not: the actual defect remains a support fixed point and is selected
  as the greatest root.  The only extra root occurs on the positive null radical and undergoes an
  exact extinction at the maximal axial radius.  This yields a global field/support/hull transform
  rather than an exterior estimate with exceptions.

## Lean progress

- 2026-07-24 — **Parts 1–4 already formalized** (corpus audit) in
  `formal/GaloisForLFunctions/HTGeometry/ConfocalGlobalSupportTransform.lean` (axioms
  `[propext, Classical.choice, Quot.sound]`):
  * pointwise projective identity (17) and nonneg defect (15): `le_liftedConfocalBranch`,
    `liftedConfocalBranch_sub_eq_nullFunctional_projective_global`;
  * all-radius fixed-point law (5)/(6) and greatest/unique selection (part 1):
    `confocalGlobalDefect_eq_nullSupport_fixedPoint`, `confocalGlobalDefect_isGreatest_fixedPoint`,
    `confocalNullSupport_positive_fixedPoint_unique_global`;
  * projective graph equality (7) (part 2):
    `confocalGlobalPositiveDefectGraph_eq_fullProjectiveSupportGraph`;
  * strict projective radius order (part 3): `confocalProjectiveParameter_strictMono`,
    `confocalNullSupportRadius_strictAnti_of_support_pos`;
  * exact radical extinction-bifurcation law (11) (part 4):
    `confocalNullSupport_zero_iff_positiveNullRay_global`,
    `confocalGlobalDefect_eq_two_mul_max_radicalHeight_sub`.
- 2026-07-24 — **Part 5 (transform faithfulness), forward direction formalized** in
  `HTGeometry/ConfocalGlobalSupportFaithfulness.lean` (axioms `[propext, Classical.choice,
  Quot.sound]`): `confocalGlobalDefect_eqOn_of_nullSupport_eqOn` — equal null support fields on
  `[0,1]` force equal all-radius defects on `(0,∞)` (`h_S = h_T ⟹ D_S = D_T`, the `h ↦ D` half of
  (12)), since the defect is the greatest nonnegative fixed point of the support-driven operator.
  **Remaining for full closure:** the reverse direction of (12) (`D_S = D_T ⟹ h_S = h_T`, by
  inverting the projective graph, with the `h_S(0)=0` radical case) and the all-radius maximal-hull
  identity (13) `K_G(S) = K_h(S)` (removing the exterior `R > M` restriction present in the
  corpus's `mem_confocalHullOfField_add_defect_iff_nullFunctional_le`).
- 2026-07-24 — **Maximal-hull identity (13), forward inclusion `K_h(S) ⊆ K_G(S)` formalized** in
  `HTGeometry/ConfocalGlobalSupportFaithfulness.lean` (axioms `[propext, Classical.choice,
  Quot.sound]`): `confocalNullSupportHull` (def of `K_h(S)`) and
  `confocalNullSupportHull_subset_confocalHullOfField` — a point whose null functionals are dominated
  by the source support field on `[0,1]` lies in the all-radius confocal hull.  The proof uses the
  **interior** sublevel form (`liftedConfocalBranch_le_add_iff_nullFunctional_le_of_snd_le_add`, valid
  without any exterior `R > M` restriction) at the actual defect together with the fixed-point identity
  `D_S(R) = h_S(λ_R(D_S(R)))`; the `λ = 1` support constraint supplies the height bound
  `q.2 ≤ G_S(R)`.  **Remaining for (13):** the reverse inclusion `K_G(S) ⊆ K_h(S)` (needs the
  projective surjectivity of `ρ_S` onto the radius half-line, with the `h_S(0)=0` radical case), and
  the reverse of the faithfulness (12).
- 2026-07-24 — **Reverse hull inclusion `K_G(S) ⊆ K_h(S)`, core recovery formalized** in
  `HTGeometry/ConfocalGlobalSupportFaithfulness.lean` (axioms `[propext, Classical.choice,
  Quot.sound]`): `confocalNullFunctional_le_nullSupport_of_mem_hull` — for every strictly-interior
  projective direction `λ ∈ (0,1)` with `h_S(λ) > 0`, a point `q` of the all-radius confocal hull has
  `nullFunc q λ ≤ h_S(λ)`.  Proof: at `R = ρ_S(λ)` the realized defect equals `h_S(λ)` (projective
  graph inversion via `confocalPositiveFixedPoint_eq_envelopeDefect_global` +
  `confocalProjectiveParameter_radiusFromProjective`), so the interior sublevel form transports the
  branch bound `b_q(R) ≤ G_S(R)` to the null constraint.  This is the mathematical core of the reverse
  inclusion.  **Remaining for `K_G ⊆ K_h` (hence `K_G = K_h`, (13)):** extend to the boundary
  directions `λ ∈ {0,1}` by continuity of `h_S` (`confocalNullSupport_lipschitz`) and the affine null
  functional, plus the degenerate `h_S(1) = 0 ⇒ S ⊆ {0}` case.  With `K_G = K_h` the reverse
  faithfulness (12) follows (`h_S` is the null support function of `K_h(S)`).
- 2026-07-24 — **Maximal-hull identity (13) closed for the non-degenerate case** (`h_S(1) > 0`), in
  `HTGeometry/ConfocalGlobalSupportFaithfulness.lean` (axioms `[propext, Classical.choice,
  Quot.sound]`):
  * `confocalHullOfField_subset_confocalNullSupportHull_of_pos` — `K_G(S) ⊆ K_h(S)`: on `(0,1)` the
    null support is positive (a positive `h_S(1)` forces a source point of positive height, keeping
    every interior support value positive), so the core recovery applies; the boundary directions
    `λ ∈ {0,1}` follow by continuity of `h_S` (`confocalNullSupport_lipschitz`) and the affine null
    functional (`squeeze_zero_norm'` + `le_of_tendsto_of_tendsto`).
  * `confocalHullOfField_eq_confocalNullSupportHull_of_pos` — **`K_G(S) = K_h(S)`** by antisymmetry
    with `confocalNullSupportHull_subset_confocalHullOfField`, the all-radius maximal-hull identity
    (13) with the exterior `R > M` restriction removed.
  **Remaining:** the degenerate `h_S(1) = 0 ⇒ S ⊆ {0}` edge case (then `G_S(R)=R`, `h_S ≡ 0`, and a
  hull point is forced to the origin) to make (13) unconditional; the reverse faithfulness (12) then
  follows since `h_S` is the null support function of `K_h(S)`.
- 2026-07-24 — **Part 5 complete → entire theorem formalized.**  Added, in
  `HTGeometry/ConfocalGlobalSupportFaithfulness.lean` (axioms `[propext, Classical.choice,
  Quot.sound]`):
  * `confocalHullOfField_subset_confocalNullSupportHull` — the reverse inclusion `K_G(S) ⊆ K_h(S)`
    unconditionally (non-degenerate case via continuity of `h_S`; degenerate `h_S(1)=0` case via the
    envelope collapsing to the radius and the origin argument).
  * `confocalHullOfField_eq_confocalNullSupportHull` — **`K_G(S) = K_h(S)`**, the maximal-hull
    identity (13), unconditional, exterior `R > M` restriction removed.
  * `confocalNullSupport_eq_sSup_nullSupportHull` — the null support is the support function of the
    null-support hull.
  * `nullSupport_eqOn_of_globalDefect_eqOn` and `globalDefect_eqOn_iff_nullSupport_eqOn` — the reverse
    direction and the full equivalence of the transform faithfulness (12): `D_S = D_T on (0,∞) ↔
    h_S = h_T on [0,1]`.
  With parts 1–4 in `ConfocalGlobalSupportTransform.lean` (defect fixed point, greatest/unique,
  projective graph equality, radical bifurcation) and forward faithfulness
  `confocalGlobalDefect_eqOn_of_nullSupport_eqOn`, **all five parts of the main theorem are now
  formalized unconditionally**.  Only the non-Lean manuscript-integration gate remains.
