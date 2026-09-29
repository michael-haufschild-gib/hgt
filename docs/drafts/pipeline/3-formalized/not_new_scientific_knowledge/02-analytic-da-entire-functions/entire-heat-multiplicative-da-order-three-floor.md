# Entire-Heat Multiplicative DA Anchors Have Differential Order at Least Three

- **ID:** entire-heat-multiplicative-da-order-three-floor
- **Stage:** 3-formalized / not new scientific knowledge
- **Type:** THEOREM (paper) / BRIDGE / ROUTE NO-GO
- **Scientific status:** `[BRIDGE]` — a direct heat-decay consequence of the classical Valiron-Zimogljad-Strelitz growth wall for algebraic differential equations of order at most two
- **Statement:** An infinite-spectrum one-sided periodic heat orbit that is entire for every complex time cannot have a first- or second-order DA anchor in its multiplicative Fourier coordinate.

## Goal

Determine how much algebraic-differential complexity is forced by entire backward heat evolution before using arithmetic information about the Fourier coefficients. The theorem concerns general complex amplitudes. Its downstream consequence applies only to heat-route implementations whose DA test is imposed on the ordinary generating function in the multiplicative Fourier coordinate.

## Gates

- [x] Exact one-sided periodic heat class fixed.
- [x] Complete unconditional paper proof.
- [x] No arithmetic or coefficient-height hypothesis.
- [x] Parent-theory gate: **FAILS scientific novelty.** Once the zero-order estimate is written down, the conclusion is an immediate application of the classical order-two growth theorem.
- [x] Formalization: **DONE (2026-09-29), unconditional.**  The card theorem is
  `HTGeometry.EntireHeatOrderTwoFloor.entireHeat_eventually_zero_or_not_differentiallyAlgebraicOfOrder_le_two`
  (either `a_n = 0` eventually, or no ADE of order `≤ 2`).  Its corollary
  `three_le_of_differentiallyAlgebraicOfOrder_entireHeat` gives the minimal-order-three
  consequence.  The theorem uses only the card's literal heat hypothesis (pointwise convergence at
  every complex `(t, z)`), and `EntireCoeffs` is derived from it.
  Proof step 1 is also formalized: the super-Gaussian bound is `superGaussianCoeffs_of_entireHeat`,
  and `log M_h(r) = o((log r)^2)` is `entireHeat_norm_le_exp_mul_log_sq`.  Orders zero and one come
  from `EntireHeatDifferentialOrderFloor`.

  Order two is `not_differentiallyAlgebraicOfOrder_two_entireHeat`.  It replaces the
  Valiron–Zimogljad–Strelitz component argument with a circle bootstrap, which the heat class makes
  available:
  - `StrelitzSecondJetGap`: lexicographic isolation of the order-two log-jet relation gives a gap
    `ρ/2 < |v| ≤ ρ` forbidden once `|z|, |f|, |u|` are large.
  - `StrelitzCircleJetCalculus`: `∂_θ u = i v`, and the circle average of `u` is constant across
    zero-free annuli.  Radially, `d log|f| / d log r = Re u`.
  - `StrelitzCircleBootstrap`: one clean circle propagates to all larger circles by continuous
    induction, which forces `f` to be a polynomial.
  - `SuperGaussianPlateauEulerJets`: at a plateau midpoint, `|u - n| ≤ 32q` and `|v| ≤ 64q`.
    The plateau comes from the corpus `exists_wide_plateau` / `term_le_midplateau`.

  All capstones audit to `[propext, Classical.choice, Quot.sound]`.  The paper proof of the
  bootstrap is in `entire-heat-order-two-circle-bootstrap.md`.

## Theorem `[PROVED HERE] [BRIDGE]`

Let `(a_n)_(n>=0)` be complex numbers and suppose

`u(t,z) = sum_(n>=0) a_n exp(-4 pi^2 n^2 t) exp(2 pi i n z)`

converges locally uniformly on `C^2`. Define the multiplicative anchor

`h(w)=sum_(n>=0) a_n w^n`.

Then either:

1. `h` is a polynomial, equivalently `a_n=0` for all sufficiently large `n`; or
2. `h` is transcendental entire and satisfies no algebraic differential equation of differential order at most two over `C(w)`.

Consequently, if the infinite-spectrum anchor `h` is DA, its minimal algebraic-differential order is at least three.

## Proof

### 1. Entire backward time gives zero logarithmic type at the quadratic scale

For every `A>0`, evaluate the orbit at `t_A=-A/(4 pi^2)`. The resulting power series

`h_A(w)=sum_(n>=0) a_n exp(A n^2) w^n`

is entire. Cauchy's estimate on `|w|=1` gives a constant `M_A>0` such that

`|a_n| <= M_A exp(-A n^2)`                                                    `(1)`

for all `n`.

For `r>=1`, put `L=log r`. Completing the square in the maximum-modulus estimate gives

`M_h(r) <= M_A sum_(n>=0) exp(-A n^2+nL)`

`        <= M_A C_A exp(L^2/(4A))`,                                           `(2)`

where `C_A` is a finite Gaussian-sum constant independent of `r`. Hence

`limsup_(r->infinity) log M_h(r)/(log r)^2 <= 1/(4A)`.

Since `A>0` is arbitrary,

`log M_h(r)=o((log r)^2)`.                                                     `(3)`

In particular, a nonpolynomial `h` is a transcendental entire function of ordinary order zero.

### 2. Differential orders zero, one, and two are impossible

An order-zero algebraic differential equation is an algebraic equation over `C(w)`; an entire solution is algebraic entire and therefore a polynomial.

The Valiron-Zimogljad-Strelitz theorem states that every transcendental entire solution of an algebraic differential equation of differential order at most two with rational-function coefficients has positive ordinary order. Applied over `C(w)`, this contradicts (3).

Thus a nonpolynomial `h` satisfies no ADE of order at most two. If it is DA at all, its minimal ADE order is at least three. `square`

## Exact route consequence

The theorem rules out the following heat-route implementation:

1. encode the deformation by a one-sided integer-frequency heat series;
2. require joint entireness for all complex time, including arbitrarily far backward time;
3. detect the proposed arithmetic phase by a first- or second-order ADE for the multiplicative Fourier anchor `h(w)`.

For an infinite source, such an ADE cannot occur at any anchor to which the same entire-complex-time estimate applies. A DA escape, if one exists, begins only at differential order three.

The theorem does not rule out the actual de Bruijn-Newman deformation, which has a continuous Fourier kernel and whose phase concerns zero reality rather than low-order differential algebraicity in a multiplicative lattice coordinate. It also does not exclude DA anchors of differential order at least three.

## Parent and sharpness audit

1. G. Valiron constructed a transcendental entire order-zero solution of a third-order algebraic differential equation: *Sur les fonctions entieres d'ordre nul et les equations differentielles*, Bull. Soc. Math. France 53 (1925), 34-42.
2. V. V. Zimogljad proved that every transcendental entire solution of a second-order algebraic differential equation with rational-function coefficients has positive order.
3. Sh. Strelitz gave a unified account and another proof in *Three Theorems on the Growth of Entire Transcendental Solutions of Algebraic Differential Equations*, Canad. J. Math. 35 (1983), 1110-1128.
4. Valiron's example shows that the differential-order threshold `3` is sharp for the parent zero-order growth theorem. It does not show sharpness inside the stricter super-Gaussian heat class (3).

## Successor residue

`[OPEN CORE]` Decide whether the stronger growth condition `log M_h(r)=o((log r)^2)` excludes transcendental DA entire functions of every finite differential order. Equivalently, decide whether a nonpolynomial DA entire series can have Taylor coefficients satisfying `|a_n|=O_A(exp(-A n^2))` for every `A>0`. A positive answer would remove both the order-three escape and all coefficient arithmetic from the finite-spectrum theorem.

## Log

- 2026-07-11 — Proved the coefficient-free differential-order-three floor and classified it `[BRIDGE]` under the direct-parent gate.
- 2026-09-04 — Formalization advanced through an exact last-variable reduction:
  `StrelitzDerivativePolynomial` converts the fixed nonzero second-order log-jet relation into a
  fixed nonzero polynomial in `v = z u′`, with coefficients polynomial in `(z,u)`, whose value
  along the escaping Wiman sequence is superpolynomially small.  Remaining order-two core is the
  Newton/Puiseux branch selection and maximum-modulus connected-component argument; card remains
  stage 2 until that exact residue is closed.
- 2026-09-04 — `StrelitzBaseCoefficient` now extracts the opposite Newton face exactly: after
  specializing `(u,v)` and retaining `z`, every `z^k` coefficient is evaluation of a fixed
  bivariate complex polynomial, and the coefficient at the largest `z`-degree is nonzero.  The
  retained-`z` polynomial inherits superpolynomial decay along the selected Wiman sequence.
  Remaining residue is to isolate this nonzero highest face analytically and globalize one of its
  Newton/Puiseux branches on maximum-modulus components.
- 2026-09-04 — `StrelitzHeatJetGrowth` proves the required heat-scale separation along that same
  sequence: `x → ∞`, `ν(exp x)/x → 0`, and eventually `ν ≤ x`, `|u| ≤ 2x`, `|v| ≤ x²`.
  Thus both logarithmic jets are polylogarithmic in `|z|`; next exact step is the finite-sum
  estimate isolating the nonzero highest `z`-coefficient face.
- 2026-09-04 — `StrelitzBaseFaceDecay` completes that finite-sum estimate.  After division by the
  highest power of `|z|`, every lower coefficient face carries at least one `exp(-x)` factor, which
  dominates its fixed polynomial growth in the heat-scale jets.  Hence an assumed order-two ADE
  produces a fixed nonzero `S ∈ C[u,v]` with `|S(u_n,v_n)| → 0`; no `z`-coefficient remains.
  Remaining residue is the bivariate Newton/Puiseux branch classification and its globalization on
  maximum-modulus components.
- 2026-09-04 — `StrelitzJetCurveRootProximity` splits `S` as a fixed polynomial in `v` over
  `C[u]`.  Since `|u_n| → ∞`, specializations eventually retain a fixed positive `v`-degree and a
  leading coefficient bounded away from zero.  Actual specialized roots are selected with
  `|v_n-root_n| → 0`.  Remaining residue is now strictly the asymptotic Puiseux classification of
  those roots and the global maximum-modulus component argument.
- 2026-09-04 — `StrelitzJetCurveRootGrowth` gives all specialized curve coefficients one explicit
  polynomial envelope in `|u|`.  The eventual leading-coefficient floor and Cauchy's root bound then
  force every selected numerical branch to have at most polynomial growth in the escaping first
  logarithmic jet.  This supplies the bounded-above logarithmic slopes required for the next
  Newton-edge subsequence extraction; reciprocal lower growth and global branch continuation remain.
- 2026-09-04 — `StrelitzJetCurveReciprocalGrowth` stabilizes the least nonzero `v`-coefficient under
  the same escaping specializations.  Reversing the specialized polynomial turns every nonzero
  selected root into its reciprocal, and a second Cauchy estimate proves that reciprocal also has a
  fixed polynomial envelope.  Nonzero branches therefore have two-sided polynomial scale; finite
  logarithmic-slope extraction and global continuation remain.
- 2026-09-04 — `StrelitzJetCurveNewtonSlope` turns that two-sided scale into a finite Newton
  classification.  Compactness selects a cofinal subsequence with a limiting logarithmic root
  slope; the corpus log-scale noncancellation theorem forces two distinct curve monomials to attain
  the maximal weight.  The limit is therefore their explicit rational Newton slope.
- 2026-09-04 — `StrelitzJetCurveNewtonEdge` turns every extracted slope into its exact maximal-face
  polynomial.  Both slope-defining monomials have nonzero leading coefficients on that face, and
  the corpus edge-root theorem supplies a genuine nonzero complex root.  Matching the numerical
  root sequence to one edge root and the global maximum-modulus component argument remain.
- 2026-09-04 — `StrelitzJetCurveBranchDichotomy` makes the numerical branch analysis exhaustive.
  Either roots are eventually nonzero and carry the rational Newton-edge package, or exact zero
  roots recur on a strictly increasing cofinal subsequence; in the latter case proximity proves
  the observed second logarithmic jet tends to zero.  Global analytic treatment of both branches
  remains.
- 2026-09-04 — `StrelitzJetCurveCoefficientPhase` retains coefficient phase at the Wiman points.
  The exact relative-error estimate makes radial normalization of the first logarithmic jet tend
  to `1`; combining this with the corpus norm-escape leading-monomial theorem proves that every
  coefficient row, normalized by its matching first-jet norm power, converges to its complex
  leading coefficient.  Normalized-root compactness, edge-root matching, and global continuation
  remain.
- 2026-09-04 — `StrelitzJetCurveNormalizedRoot` removes the extracted real Newton power from the
  selected numerical root and proves, by an exact logarithm/rpow identity, that its residual
  logarithmic exponent is zero.  This closes scale normalization without assuming boundedness.
  Remaining local step is the finite-face dominance argument upgrading subpolynomial size to a
  compact annulus and identifying the resulting limit with an actual edge root.
- 2026-09-04 — `StrelitzJetCurveNewtonFaceDominance` proves both ends of normalized-root
  compactness.  At infinity the largest index on the maximal Newton face dominates the exact root
  equation; at zero the smallest index does.  Constructive cofinal subsequence extraction converts
  those contradictions into one eventual annulus with positive inner radius.
- 2026-09-04 — `StrelitzJetCurveEdgeLimit` closes local numerical branch matching.  A convergent
  cofinal subsequence in that annulus has nonzero limit; after exact real-power scaling, lower
  Newton faces vanish and the surviving finite sum is literally the edge polynomial evaluated at
  that limit.  The local Newton/Puiseux residue is closed.  Only the maximum-modulus
  connected-component globalization, including the zero-root branch, remains.
- 2026-09-04 — `StrelitzJetCurveMatchedDichotomy` packages the local result without an omitted
  branch.  Eventual nonzero roots yield a rational Newton slope, exact maximal face, nonzero exact
  edge root, and convergence of normalized numerical roots on a strict cofinal subsequence;
  recurrent exact-zero roots force the observed second jet to zero on such a subsequence.  Direct
  source check, targeted leaf build, and axiom audit pass; axioms are
  `[propext, Classical.choice, Quot.sound]`.  Global maximum-modulus component continuation remains.
- 2026-09-04 — `StrelitzEntireHeatMatchedDichotomy` composes the exact entire-heat root-selection
  theorem with the exhaustive matched-edge dichotomy under precisely the card's original
  assumptions.  Its conclusion retains every Wiman-point, jet-error, specialization-root, and
  proximity assertion together with the matched-edge-or-zero alternative.  Direct source check,
  targeted leaf build, and axiom audit pass; axioms are
  `[propext, Classical.choice, Quot.sound]`.  Global continuation remains the only Card 8 gap.
- 2026-09-04 — `StrelitzJetCurveQuadraticDecay` transfers the Wiman second-jet estimate through
  selected-root proximity and proves `|root_n| / nu_n^2 -> 0`.  No rate or nonvanishing assumption
  is added.  Direct source check, targeted leaf build, and axiom audit pass; axioms are
  `[propext, Classical.choice, Quot.sound]`.
- 2026-09-04 — `StrelitzJetCurveSubquadraticEdge` proves `|u_n|/nu_n -> 1`, transfers selected-root
  decay to `|root_n|/|u_n|^2 -> 0`, and excludes Newton exponents `p >= 2` by contradiction with
  the matched nonzero normalized-root limit.  Its exhaustive strengthened dichotomy carries
  `p < 2` in the nonzero branch.  `StrelitzEntireHeatSubquadraticDichotomy` derives this directly
  from the original Card 8 assumptions.  Direct source checks, targeted leaf builds, and all five
  new-theorem axiom audits pass; axioms are `[propext, Classical.choice, Quot.sound]`.
- 2026-09-04 — `StrelitzJetCurveZeroBranch` turns the recurrent-zero alternative into exact
  algebra: evaluation at the specialized zero root is evaluation of the constant-in-`v`
  coefficient, and an escaping first-jet sequence forces that fixed coefficient polynomial to be
  identically zero; equivalently `X` divides the curve polynomial.  Direct source check, targeted
  leaf build, and all four axiom audits pass; axioms
  are `[propext, Classical.choice, Quot.sound]`.
- 2026-09-04 — `StrelitzEntireHeatSubquadraticFactorDichotomy` packages the exact algebraic
  alternative directly under the original entire-coefficient, entire complex-time heat,
  infinite-support, and order-two ADE assumptions.  Its nonzero branch is a matched Newton edge
  with slope `p < 2`; its zero branch has the literal factor `X` and a cofinal vanishing observed
  second jet.  Direct source check, targeted leaf build, and new-theorem axiom audit pass; axioms
  are `[propext, Classical.choice, Quot.sound]`.  Global maximum-locus branch continuation remains.
- 2026-09-04 — `StrelitzJetCurveSlopeSign` splits the matched nonzero branch at the exact sign
  boundary.  Nonnegative slopes retain `0 ≤ p < 2`; negative slopes force both selected-root norm
  and observed second-jet norm to tend to zero on a strict cofinal subsequence; the recurrent-zero
  branch retains the literal `v` factor.  The original entire-heat hypotheses now imply this full
  trichotomy.  Direct source check, targeted leaf build, and all four new-theorem axiom audits pass;
  axioms are `[propext, Classical.choice, Quot.sound]`.  Global maximum-locus continuation remains.
- 2026-09-04 — `StrelitzSublinearDerivativeObstruction` formalizes the nonnegative-slope ODE
  endpoint.  It integrates derivative floors and ceilings, rules out negative normalized limits on
  escaping real branches, and proves that any nonzero limit of `K'(x)/K(x)^p` with `p ≥ 0`
  contradicts `K(x)/x → 0`.  Direct source check, targeted leaf build, and all seven new-theorem
  axiom audits pass; axioms are `[propext, Classical.choice, Quot.sound]`.  Card 8 still needs the
  unconditional global maximum-locus branch supplying these exact scalar data.
- 2026-09-04 — `StrelitzLogRadialDerivatives` proves the exact log-radius differential bridge:
  `d(log ‖f‖)/d(log r) = Re(zf'/f)` and
  `d Re(zf'/f)/d(log r) = Re(z(zf'/f)')`, together with the complex-valued middle identity.
  Direct source check, targeted leaf build, and all five new-theorem axiom audits pass; axioms are
  `[propext, Classical.choice, Quot.sound]`.  Card 8 remains stage 2 pending construction and
  continuation of the enlarged Strelitz set component on which these identities can be integrated.
- 2026-09-04 — `StrelitzAngularCurvature` differentiates `log ‖f‖` twice along the exact circle
  path and proves `Re(z(zf'/f)') ≥ 0` at every nonvanishing point of the full maximum-modulus
  locus.  Entire-function differentiability is discharged internally.  Direct source check,
  targeted leaf build, and all four new-theorem axiom audits pass; axioms are
  `[propext, Classical.choice, Quot.sound]`.  This constrains the phase of any branch meeting the
  maximum locus but does not replace the remaining enlarged-set continuation.
- 2026-09-04 — Maximum-circle witnesses are now preserved from the second-derivative
  Wiman--Valiron selection through the entire Strelitz reduction, root-selection, matched-edge,
  subquadratic, factor, and slope-sign APIs.  Legacy theorem signatures remain available as exact
  wrappers.  `StrelitzMaximumPointSlopeSign` then proves that the complete slope trichotomy can be
  realized at genuine maximum-modulus points, with `Im(zf'/f)=0` and
  `Re(z(zf'/f)') ≥ 0` at every selected point.  Direct source checks, targeted leaf builds, and all
  new-theorem axiom audits pass; axioms are `[propext, Classical.choice, Quot.sound]`.  Card remains
  stage 2: the paper's enlarged open set and its unbounded connected-component continuation are
  still required to turn these pointwise signs into the global scalar branch contradiction.
- 2026-09-04 — `StrelitzNonnegativeEdgePhase` proves that, in the nonnegative-slope branch,
  selected-root proximity survives Newton normalization and the matched nonzero edge root lies in
  the closed right half-plane.  `StrelitzMaximumPathDerivative` then proves the exact differential
  identity on every smooth local maximum-modulus path: if the second Euler jet is `v` and
  `Re(v) > 0`, the derivative of the real first Euler jet is `normSq(v) / Re(v)`; if
  `Re(v) = 0`, then `v = 0`.  `StrelitzMaximumPathObstruction` closes the resulting scalar
  endpoint, including purely imaginary limiting edge roots: a nonzero second-jet limit normalized
  by any nonnegative power forces a fixed positive derivative floor and contradicts sublinearity.
  Direct source checks, targeted leaf builds, and all new-theorem axiom audits pass; axioms are
  `[propext, Classical.choice, Quot.sound]`.  Card remains stage 2 only because the paper's enlarged
  Strelitz set and global branch continuation have not yet been constructed in Lean.
- 2026-09-04 — `StrelitzMaximumNorm` and `StrelitzMaximumSlope` construct the exact choice-free
  logarithmic maximum modulus and its canonical convex right slope.  `StrelitzMaximumSlopeGrowth`
  proves that infinite coefficient support forces this slope to diverge and that sublogarithmic
  central index forces it to be sublinear.  `StrelitzEntireHeatMaximumSlope` derives both facts
  directly from the card's original entire complex-time heat and infinite-support assumptions;
  no auxiliary growth premise is exposed.  The maximum-path realization was separated into
  `StrelitzMaximumPathSlope`, while `StrelitzLogJetDefs` removes the former import dependency on
  the Newton chain.  Direct source checks, targeted leaf builds, and all new-theorem axiom audits
  pass; axioms are `[propext, Classical.choice, Quot.sound]`.  Card remains stage 2: the enlarged
  set `H`, its relevant unbounded component, and global algebraic-branch continuation are still
  required.
- 2026-09-29 — Order two closed in Lean without the Strelitz enlarged-set component argument.
  - A second-jet gap from lexicographic isolation, together with a continuous circle bootstrap,
    turns one clean circle into polynomial growth.
  - Super-Gaussian plateaus supply clean circles with absolute jet errors `32q` / `64q`.
  - Card theorem `entireHeat_eventually_zero_or_not_differentiallyAlgebraicOfOrder_le_two` is
    unconditional, with axioms `[propext, Classical.choice, Quot.sound]`.
  - Moved to `3-formalized/not_new_scientific_knowledge/02-analytic-da-entire-functions/`.
