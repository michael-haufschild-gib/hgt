# Vanishing of the higher cohomology of the structure sheaf on a polydisc and on a torus cover

- **ID:** `holomorphic-sheaf-cohomology-vanishing`
- **Stage:** 1-in-progress
- **Type:** INFRASTRUCTURE PROGRAMME
- **Serves:** `deninger-pro-stein-cylinder-analytic-leaf` (item 2 of its Remaining list),
  `deninger-pro-log-stein-kummer-residue-square`,
  `deninger-archimedean-kummer-homology-current-lift`,
  `deninger-strict-pro-log-collar-trace-kernel`

## Target

\[
  H^q(Z,\mathcal O_Z)=0\qquad (q\ge 1),\qquad Z=(\mathbb C^\times)^r .
\]

The sheaves of the cell filtration are free on `Z`, so this is the only sheaf-cohomological input
those four cards need.  It does **not** require the general theory of coherent analytic sheaves;
it requires the Dolbeault resolution of `O` and global solvability of `∂̄` on `Z`.

## What is already built

| Step | Statement | Where |
|---|---|---|
| D1 | Cauchy–Pompeiu on a disc | `HTGeometry/CauchyPompeiu.lean` |
| D2 | `∂̄ u = g` for compactly supported `C¹ g` on `ℂ` | `HTGeometry/DbarSolve.lean` |
| D3 | Dolbeault–Grothendieck on a polydisc | `HTGeometry/DbarPolydiscSolve.lean` |
| — | fine ⟹ Čech-acyclic, module coefficients | `HTGeometry/CechFineAcyclicModule.lean` |
| — | several-variable analyticity, Cauchy formula on a polydisc | see the cylinder card's Lean status |

## The chain still to build

**B2 — global `∂̄` on a polydisc.**  D3 solves on every strictly smaller polydisc.  The passage to
the whole polydisc is the classical exhaustion: write `P = ⋃_m P_m` with `P_m ⊂⊂ P_{m+1}`, solve on
each `P_m`, and correct the difference of consecutive solutions.  For `q ≥ 2` the correction is
exact and no approximation is needed.  For `q = 1` the difference of consecutive solutions is
holomorphic on `P_m`, and one needs to approximate it uniformly on `P_{m-1}` by a function
holomorphic on all of `P` — on a polydisc that is **truncation of the Taylor series**, which the
corpus already owns through several-variable analyticity.  So the Runge step here is elementary and
does not need Oka–Weil.

**B3 — the same on a polyannulus.**  `Z = (ℂ^×)^r` is exhausted by the closed polyannuli
`A_m = {1/m ≤ |z_i| ≤ m}`.  The approximation step is **truncation of the Laurent series**, which
needs the Laurent expansion in several variables — the one genuinely new analytic ingredient, and
an elementary one: it is the Cauchy integral over the distinguished boundary of the polyannulus,
split into the two geometric series in `z_i/w_i` and `w_i/z_i`.

**B4 — from `∂̄` to sheaf cohomology.**  The Dolbeault resolution
`0 → O → A^{0,0} → A^{0,1} → ⋯` is exact by D3; each `A^{0,q}` is fine because smooth partitions of
unity exist, hence Čech-acyclic by `CechFineAcyclicModule`; therefore
`H^q(Z, O) ≅ H^q(Γ(Z, A^{0,•}))`, which is zero by B3.  The Čech side is already available; what is
needed is the statement of the sheaf `O` and of the sheaves `A^{0,q}` on `Z`, and the comparison.

## Order of work

B2, then B3, then B4.  Each is a separate module under `HTGeometry/`.

## B2 progress — the local Cauchy formula and the Runge step, landed (2026-08-06)

**`formal/GaloisForLFunctions/HTGeometry/PolydiscCauchyLocal.lean`.**
`polydiscSet` is the open polydisc as a set (for equal radii it is the metric ball of the supremum
norm), `torusMap_mem_polydiscSet` puts the distinguished boundary of a smaller polydisc inside the
larger, and the four `cons` lemmas transport holomorphy between a polydisc and its coordinate
slices.  The theorem is

  `polydiscCauchyFormula_of_differentiableOn` — **the Cauchy integral formula on a polydisc from
  holomorphy on that polydisc alone**, for Banach-valued functions.

The corpus previously had this only for entire functions.  The induction is the same — the torus
integral becomes an iterated circle integral, the remaining kernel factors out of the innermost one,
and the one-variable Cauchy formula closes the step — with the domain hypotheses tracked, so every
slice is holomorphic on a neighbourhood of the closed disc it is integrated over.  The inner step is
now rewritten with `circleIntegral.integral_congr` rather than a global `simp only`, because the
inner identity holds only on the circle.

**`PolydiscAnalytic.lean` refactor.**  `polydiscSeries_hasSum_of_affineLineEntire` and
`polydiscHasFPowerSeriesOnBall_of_affineLineEntire` used entireness in exactly one place, to invoke
the Cauchy formula.  Both are now derived from `polydiscSeries_hasSum_of_cauchy` and
`polydiscHasFPowerSeriesOnBall_of_cauchy`, which take the Cauchy formula as a hypothesis.  The
original statements survive verbatim as corollaries.

**`formal/GaloisForLFunctions/HTGeometry/PolydiscApproximation.lean`.**

- `differentiable_partialSum` — the partial sums of a formal multilinear series are **entire**.
- `polydiscHasFPowerSeriesOnBall_of_differentiableOn` — the Cauchy power series of a function
  continuous everywhere and holomorphic on a polydisc.
- `exists_entire_approx_of_differentiableOn` — approximation on the ball of convergence.
- `exists_entire_approx_closedBall` — **the Runge step with no loss of radius**: for `ρ < R < R₁`,
  a function continuous everywhere and holomorphic on the polydisc of radius `R₁` is approximated
  uniformly on `closedBall c ρ`, to any accuracy, by an entire function.  The proof bounds the terms
  of the Cauchy series on the smaller closed polydisc by `((k+1)^n)(ρ/R)^k M`, which is summable and
  independent of the point, and takes a partial sum.

Axiom audit: every declaration of the two new modules and of the refactored one is within
`propext, Classical.choice, Quot.sound`.

This is the whole approximation half of B2.  Note the shape of the hypothesis: *continuous
everywhere, holomorphic on the polydisc*.  That is exactly what the Mittag-Leffler construction
supplies, because `dbar_polydisc_solve` returns a solution smooth on the whole space and the
difference of two consecutive solutions is holomorphic only where both solve the same equation.

### Next in B2

The assembly needs **Weierstrass' theorem in several variables**: a locally uniform limit of
functions holomorphic on a polydisc is holomorphic there.  With the local Cauchy formula in hand the
proof is: pass to the limit in the Cauchy integral over a small torus around each point — the kernel
is bounded there and the convergence is uniform on the compact torus — and feed the resulting
formula to `polydiscHasFPowerSeriesOnBall_of_cauchy`, which gives analyticity at that point.

## Weierstrass in several variables, landed (2026-08-06)

`formal/GaloisForLFunctions/HTGeometry/PolydiscWeierstrass.lean`:

- `polydiscSet_const` — a polydisc with equal radii is the ball of the supremum norm on
  `Fin n → ℂ`.  This is what lets the polydisc statements be read as ball statements and back.
- `tendsto_torusIntegral_smul` — **uniform convergence passes through a torus integral against a
  bounded kernel**: the difference of the integrals is the integral of the difference, and
  `norm_torusIntegral_le_of_norm_le_const` turns a uniform bound on the integrand into a bound on
  the integral.
- `differentiableOn_of_tendstoUniformlyOn` — **Weierstrass' theorem in several complex variables**:
  a limit, uniform on every closed ball strictly inside, of functions holomorphic on a ball is
  holomorphic on that ball.  At each point one takes a torus of radius `r` around it small enough
  that the closed ball of radius `2r` stays inside; the kernel is bounded there by `(r − s)^{-n}`
  where `s` is the distance from the evaluation point to the centre; the Cauchy formulas of the
  approximants pass to the limit; and `polydiscHasFPowerSeriesOnBall_of_cauchy` turns the limiting
  formula into analyticity at that point.

Axiom audit: all three within `propext, Classical.choice, Quot.sound`.

Mathlib has this only in one variable (`DifferentiableOn.analyticOnNhd` is stated for `ℂ → E`).
With it, the Mittag-Leffler assembly has all its ingredients:
`dbar_polydisc_solve` for the local solutions, `exists_entire_approx_closedBall` for the Runge step,
and this for the limit.

## B2 COMPLETE — global solvability of `∂̄` on `ℂⁿ` (2026-08-06)

`formal/GaloisForLFunctions/HTGeometry/DbarGlobalSolve.lean`:

- `map_I_single_at`, `map_I_at`, `differentiableAt_complex_of_dzbarAt_eq_zero`,
  `differentiableOn_complex_of_dzbarAt_eq_zero` — the Cauchy–Riemann criterion **at a point** and
  hence **on a set**.  The corpus had it only in the everywhere form.
- `dzbarAt_eq_zero_of_differentiable`, `differentiable_updateEmbed_complex`,
  `dzbarAt_eq_zero_of_differentiableOn` — the converse: `∂̄` of a holomorphic function vanishes,
  pointwise on an open set.
- `contDiffAt_of_differentiableOn` — a globally continuous function holomorphic on an open set is
  `C^∞` there, through the local Cauchy power series.
- `exists_dbar_approx_sequence` — **the corrected sequence**: local solutions on the balls of
  radius `m + 1` from `dbar_polydisc_solve`, consecutive differences holomorphic there by the
  Cauchy–Riemann criterion, corrected by entire functions from `exists_entire_approx_closedBall` so
  that consecutive corrected solutions differ by at most `2^{-m}` on the ball of radius `m`.
- `dbar_global_solve` — **`∂̄u = f` is globally solvable on `ℂⁿ`**: a smooth `∂̄`-closed datum
  `f : Fin n → (Fin n → ℂ) → ℂ` on the whole space has a smooth `u` with `∂̄_j u = f_j` everywhere.

  The corrected sequence converges: at every point the tail is dominated by a geometric series, so
  the sum `w = v₀ + ∑ (v_{m+1} − v_m)` exists; the convergence is uniform on every closed ball, so
  `w` is continuous; on the ball of radius `N` the partial sums `v_{k+N} − v_N` are holomorphic and
  converge uniformly on closed sub-balls, so Weierstrass makes `w − v_N` holomorphic there; hence
  `w` is smooth and `∂̄_j w = ∂̄_j v_N = f_j` on that ball, and every point lies in one.

Axiom audit: all seven within `propext, Classical.choice, Quot.sound`.

**This is Cartan theorem B for `ℂⁿ` in Dolbeault form.**  Nothing of this kind existed in Lean.

### Remaining

B3 — the same on `(ℂ^×)^r`.  The exhaustion is by polyannuli `1/m ≤ |z_i| ≤ m` and the only new
analytic ingredient is the **Laurent expansion in several variables**: the Cauchy integral over the
distinguished boundary of a polyannulus, split into the two geometric series in `z_i/w_i` and
`w_i/z_i`.  Everything else — the corrected sequence, the uniform limit, Weierstrass — is now
generic and reusable: only `exists_entire_approx_closedBall` has to be replaced by its Laurent
counterpart, approximation by Laurent polynomials, which are holomorphic on `(ℂ^×)^r`.

B4 — the Čech/Dolbeault comparison, using `CechFineAcyclicModule` for the fine resolution.

## B3 first half — the Dolbeault lemma on a polyannulus (2026-08-06)

`formal/GaloisForLFunctions/HTGeometry/DbarProductSolve.lean`.

The Dolbeault induction never used that the factors of the domain are discs.  It used exactly three
things: that moving one coordinate inside its own factor stays in the domain, that the domain is
open, and that a cutoff in the distinguished coordinate is available.  All three hold for any
product of open plane domains.

- `productDomain`, `mem_productDomain`, `productDomain_mono`, `isOpen_productDomain`,
  `update_mem_productDomain` — the product of a family of plane domains and its three properties.
- `dbar_product_step_smooth` — the induction step on a product domain.
- `dbar_product_solve_aux`, `dbar_product_solve` — **the Dolbeault–Grothendieck lemma on a product
  domain**, run along a decreasing chain `Dom : ℕ → Fin n → Set ℂ` with a cutoff pair supplied for
  each consecutive link.  The induction shrinks the domain once per coordinate, so the conclusion
  lands on `Dom n`.  Indexing the recursion by both the number of directions still to clear and the
  position in the chain is what makes the bookkeeping close: the step at `(m+1, o)` produces a
  solution on `Dom (o+1)` and recurses at `(m, o+1)`, landing on `Dom (o+1+m) = Dom (o+(m+1))`.
- `annulus`, `isOpen_annulus`, `annulus_mono`, `contDiff_normSq_complex`,
  `exists_annulus_cutoff` — **the annulus cutoff**.  It is a bump in the *squared* radius, which is
  a polynomial in the real coordinates and therefore smooth everywhere, including at the origin
  where the radius itself is not differentiable.  That is the whole trick.
- `exists_bounded_bump` — a compactly supported bump equal to one on a bounded product domain.
- `annulusChainIn`, `annulusChainOut`, `dbar_polyannulus_solve` — **the Dolbeault–Grothendieck
  lemma on a polyannulus**: a smooth `∂̄`-closed datum on the polyannulus of radii `(a, b)` has a
  smooth primitive on every strictly smaller polyannulus.  The chain interpolates geometrically,
  `A o = a + (a' − a)(1 − 2^{-o})`, so it is strictly decreasing at every step and still contains
  the target after `n` steps.

Axiom audit: every declaration within `propext, Classical.choice, Quot.sound`.

### Remaining for B3

Only the Runge step changes: the approximating functions must be holomorphic on all of `(ℂ^×)^r`
rather than entire, so `exists_entire_approx_closedBall` is replaced by approximation by **Laurent
polynomials**, from the Laurent expansion in several variables — the Cauchy integral over the
distinguished boundary of a polyannulus, split into the two geometric series in `z_i/w_i` and
`w_i/z_i`.  The Mittag-Leffler assembly itself (`exists_dbar_approx_sequence` and
`dbar_global_solve`) is then the same argument with balls replaced by polyannuli.

## The Cauchy formula on an annulus, landed (2026-08-06)

`formal/GaloisForLFunctions/HTGeometry/AnnulusCauchy.lean`:

- `annulusAt`, `isOpen_annulusAt`, `closedAnnulus_subset` — the open annulus about a centre and its
  relation to the closed annulus between intermediate radii.
- `circleIntegral_sub_inv_eq_zero_of_lt` — **the Cauchy kernel integrates to zero over a circle
  that does not enclose its pole**, by Cauchy's theorem on the disc.
- `annulusCauchyFormula` — **the Cauchy integral formula on an annulus**, Banach-valued: for `f`
  holomorphic on the annulus of radii `(a, b)` and `a < r < ‖z − c‖ < R < b`,

    `(∮_{C(c,R)} (ζ−z)⁻¹ • f ζ) − (∮_{C(c,r)} (ζ−z)⁻¹ • f ζ) = 2πi • f z`.

  The difference quotient `dslope f z` is holomorphic on the whole annulus (mathlib's removable
  singularity theorem), so its two circle integrals agree by mathlib's annulus invariance; what
  remains is `f z` times the kernel integral, `2πi` outside and `0` inside.

Axiom audit: both within `propext, Classical.choice, Quot.sound`.

Mathlib has the annulus *invariance* of circle integrals but no annulus Cauchy formula and no
Laurent theory at all.  This is the base case of the several-variable Laurent expansion: iterating
it coordinatewise gives the `2^n`-term Cauchy formula on a polyannulus, and expanding each kernel
factor in the appropriate geometric series — `z_i/ζ_i` on the outer circles, `ζ_i/z_i` on the inner
ones — gives the Laurent series.

## The Laurent decomposition, landed (2026-08-06)

`formal/GaloisForLFunctions/HTGeometry/LaurentAnnulus.lean`:

- `laurentOuter`, `laurentInner` — the Cauchy transforms of the outer and inner boundary circles.
- `laurent_decomposition` — **on the annulus a holomorphic function is their sum**, immediately from
  `annulusCauchyFormula`.
- `laurentOuter_hasFPowerSeriesOnBall` — the outer part is analytic on the whole disc bounded by the
  outer circle.  This is mathlib's `hasFPowerSeriesOn_cauchy_integral`, which turned out to be
  exactly the statement needed, so the outer half costs nothing.
- `exists_entire_approx_laurentOuter` — **uniform approximation of the outer part by entire
  functions** on every smaller disc.
- `laurentCoeff`, `norm_laurentCoeff_le` — the inner Laurent coefficients and the bound
  `‖a_k‖ ≤ r^k M r` from the maximum on the circle.
- `hasSum_laurentInner` — **the inner part is the sum of its Laurent series** `∑_k (z−c)^{-(k+1)} a_k`
  at every point outside the circle.  The kernel is expanded in the geometric series in
  `(ζ−c)/(z−c)`, which converges because the point is outside; the interchange of sum and integral
  is the corpus's `hasSum_torusIntegral` used in dimension one through mathlib's
  `torusIntegral_dim1`.

Axiom audit: all within `propext, Classical.choice, Quot.sound`.

The partial sums of the inner series are polynomials in `(z−c)^{-1}`, holomorphic away from the
centre; together with the outer approximation by polynomials this is the one-variable Runge step on
an annulus.  What remains for B3 is to iterate the decomposition over the coordinates — a sum over
subsets `S ⊆ Fin n`, with the inner expansion in the coordinates of `S` and the outer in the rest —
and then to replay the Mittag-Leffler assembly of `dbar_global_solve` with balls replaced by
polyannuli.

## The Runge step on an annulus, landed (2026-08-06)

`formal/GaloisForLFunctions/HTGeometry/LaurentAnnulus.lean`, sections `InnerApprox` and
`RungeAnnulus`:

- `laurentInnerPartial`, `differentiableOn_laurentInnerPartial` — the partial sums of the inner
  Laurent series, **polynomials in `(z − c)⁻¹`, holomorphic away from the centre**.
- `exists_approx_laurentInner` — **uniform approximation of the inner part** outside a circle of
  radius larger than the one the coefficients are taken on, by bounding the tail with
  `(Mr/ρ)·(r/ρ)^k` — a bound independent of the point.
- `sphere_subset_annulusAt`, `exists_bound_on_sphere` — a circle inside the annulus, and the maximum
  of a continuous function on it.
- `exists_punctured_approx_annulus` — **the Runge step on an annulus**: a function holomorphic on
  the annulus of radii `(a, b)` is approximated uniformly on every closed sub-annulus, to any
  accuracy, by a function holomorphic on the punctured plane.  The outer part goes to a polynomial,
  the inner part to a polynomial in `(z − c)⁻¹`, and the two halves of the error are split evenly.

Axiom audit: all within `propext, Classical.choice, Quot.sound`.

This is the one-variable Runge theorem for annuli, in exactly the form the Mittag-Leffler assembly
consumes.  Its several-variable analogue — approximation on a closed polyannulus by functions
holomorphic on `(ℂ^×)^n` — follows by iterating the Laurent decomposition over the coordinates, a
sum over subsets `S ⊆ Fin n` with the inner expansion in the coordinates of `S` and the outer in the
rest.  That iteration and the Mittag-Leffler replay are what remain for B3.

## Corpus audit before building further (2026-08-06)

Ran `scripts/formal_tools.py research` on "annulus Laurent series", "Runge approximation
polynomial", "Stein coherent sheaf", "Dolbeault complex forms", "holomorphic parameter integral
derivative", "Cech cohomology sheaf acyclic", plus greps over the module names.

**Reusable, and it changes the plan for B4.**  Sheaf cohomology on a topological space is already
corpus-owned:

- `RHTower/Deninger/DeningerFlasqueAcyclic.lean` — `deningerSheafCohomology U F n`, sheaf cohomology as the
  `Ext` out of the free abelian sheaf on an open set; `deningerSheafCohomologyZeroEquiv`, degree
  zero is sections; **`deningerFlasque_isZero_cohomology`, a flasque sheaf has no higher
  cohomology**.
- `RHTower/Deninger/DeningerOpenFreeSheaf.lean` — the free abelian sheaf on an open set and its hom
  adjunction, the representing object of the above.
- `RHTower/Deninger/DeningerSkyscraperAcyclic.lean`, `RHTower/Deninger/DeningerRestrictedPrimeAcyclic.lean`,
  `RHTower/Deninger/DeningerArakelovBoundarySheaf.lean` — worked instances of proving acyclicity in that
  framework, including through mathlib's site-level `Sheaf.H`.
- `RHTower/Deninger/DeningerCechHomotopy.lean`, `DeningerCechGlue.lean`, `DeningerCechSplit.lean`, and
  `HTGeometry/CechFineAcyclicModule.lean` — the Čech side, fine ⟹ Čech-acyclic with module
  coefficients.

So **B4 is assembly, not construction**: what is needed is the sheaf of holomorphic functions and
the sheaves of smooth `(0,q)`-forms on an open subset of `ℂⁿ`, the exactness of the Dolbeault
resolution (which is the local statement already proved), and acyclicity of the form sheaves.

**Not present anywhere in the tree, and therefore genuinely new here**: annulus Laurent series
(`MeromorphicLaurentCoefficient` is Laurent *at a pole*, through analytic shifts of a meromorphic
germ — a different object), Runge approximation, Stein theory, the Dolbeault complex, and
holomorphy of a parameter integral.  `Bottcher/BasinColimit.lean` has a gluing theorem over a nested
exhaustion (`exists_global_branch_of_coherent_levels`) but only for *coherent* families, where
consecutive members agree; the Mittag-Leffler situation, where they differ by a holomorphic
correction, is not covered by it.

One real collision was found and fixed: `laurentCoeff` is taken by
`HTGeometry/MeromorphicLaurentCoefficient.lean`; ours is now `annulusLaurentCoeff`.

## Local analyticity and parameter holomorphy, landed (2026-08-06)

Two pieces that unblock the several-variable Laurent induction.

**Continuity hypotheses removed from the series layer.**  `polydiscSeries_hasSum_of_cauchy` and
`polydiscHasFPowerSeriesOnBall_of_cauchy` used to demand `Continuous f` on the whole space; they now
take `ContinuousOn f` on the distinguished boundary alone, and `exists_bound_on_torus` was rewritten
to take the maximum on that compact torus rather than on a closed ball.  Consequently
`polydiscHasFPowerSeriesOnBall_of_differentiableOn`, `exists_entire_approx_of_differentiableOn`,
`exists_entire_approx_closedBall` and `contDiffAt_of_differentiableOn` need **no continuity
hypothesis at all** — holomorphy on the domain supplies it.  This was the obstruction to using them
for a function that exists only on a polyannulus.

**`PolydiscWeierstrass.lean`, new:**

- `analyticAt_of_differentiableOn` — **holomorphy on an open set implies analyticity there**, in
  several variables.  mathlib has this only in one variable.
- `contDiffAt_complex_of_differentiableOn`, `continuousOn_fderiv_of_differentiableOn` — hence
  smoothness over `ℂ`, and continuity of the differential on the domain.

**`CircleIntegralParam.lean`, new:**

- `consLin`, `consLin_apply`, `cons_eq_consLin_add`, `hasFDerivAt_consMap`, `norm_consLin_le` —
  prepending a first coordinate as an affine map with continuous linear part of norm at most one.
- `differentiableAt_circleIntegral_slice` — **the circle integral of a slice of a holomorphic
  function is holomorphic in the remaining variables.**  The derivative is taken under the integral
  sign with `hasFDerivAt_integral_of_dominated_of_fderiv_le` at `𝕜 = ℂ`; the domination is uniform
  because the differential of a holomorphic function is continuous and the product of the circle
  with a closed ball inside the parameter domain is compact.

Axiom audit: every declaration within `propext, Classical.choice, Quot.sound`.

This is the inductive step's missing ingredient: the Laurent coefficients of a function of several
variables are holomorphic in the remaining variables, so the one-variable Runge step can be applied
coordinate by coordinate.

## The uniform Laurent approximation, landed (2026-08-06)

`formal/GaloisForLFunctions/HTGeometry/LaurentAnnulus.lean`, sections `UniformApprox`,
`TailBound`, `LaurentApprox`, `UniformBound`:

- `outerCoeff`, `cauchyPowerSeries_diag`, `norm_outerCoeff_le` — the outer Taylor coefficients on
  the outer circle, their identification with the diagonal of mathlib's `cauchyPowerSeries`, and the
  Cauchy estimate `‖c_k‖ ≤ M / R^k`.
- `norm_sub_partialSum_le`, `tsum_geometric_tail` — the error of a partial sum is the tail of a
  dominating series, and the tail of a geometric series in closed form.
- `laurentApprox`, `differentiableOn_laurentApprox` — the Laurent partial sum, outer Taylor part
  plus inner principal part, **holomorphic away from the origin**.
- `norm_sub_laurentApprox_le` — **the uniform bound**:

    `‖f z − laurentApprox f r R N z‖ ≤ M·(σ/R)^N/(1−σ/R) + (Mr/ρ)·(r/ρ)^N/(1−r/ρ)`

  for `a < r < ρ ≤ ‖z‖ ≤ σ < R < b`, where `M` bounds `f` on the two circles.

The point of the explicit form is that **the bound mentions the function only through `M`**.  The
earlier `exists_punctured_approx_annulus` hides the number of terms inside an existential, so it
cannot be applied uniformly in a parameter; this version can, because one `N` works for the whole
family as soon as `M` is uniform.  That is exactly what the coordinate-by-coordinate induction
needs: at each step the coefficients are circle integrals, holomorphic in the remaining variables by
`differentiableAt_circleIntegral_slice`, and the number of terms is chosen once.

Axiom audit: every declaration within `propext, Classical.choice, Quot.sound`.

## B3 Runge half COMPLETE — the several-variable Runge theorem (2026-08-06)

`formal/GaloisForLFunctions/HTGeometry/PolyannulusRunge.lean`:

- `sliceOuterCoeff`, `sliceInnerCoeff`, `continuous_circle_zpow`,
  `differentiableOn_sliceOuterCoeff`, `differentiableOn_sliceInnerCoeff` — **the Laurent
  coefficients of the first-coordinate slice are holomorphic in the remaining variables**, from
  `differentiableAt_circleIntegral_slice`.  The kernels `ζ^{-(k+1)}` are continuous along the
  circle, which is why the parameter lemma was stated with circle continuity rather than global
  continuity.
- `closedPolyannulus`, `isCompact_closedPolyannulus`, `closedAnnulus`, `isCompact_closedAnnulus`,
  `closedAnnulus_subset_annulus`, `closedPolyannulus_subset`, `cons_mem_annulusProduct` — the
  compact closed polyannuli and their inclusions.
- `laurentApprox_slice` — the Laurent partial sum of a slice, written through the slice
  coefficients.
- `exists_punctured_approx_polyannulus` — **the Runge theorem on a polyannulus**: a function
  holomorphic on the polyannulus of radii `(a, b)` is approximated uniformly on every closed
  sub-polyannulus `[ρ, σ]`, to any accuracy, by a function holomorphic on `(ℂ^×)^n`.

The induction splits off one coordinate.  The Laurent partial sum in that coordinate has error
`M(σ₀/R₀)^N/(1−σ₀/R₀) + (Mr₀/ρ₀)(r₀/ρ₀)^N/(1−r₀/ρ₀)`, which depends on the function only through
its maximum `M` on a compact set, so a single `N` serves the whole slice family; its `2N`
coefficients are holomorphic on the tail polyannulus, and the induction hypothesis approximates each
to accuracy `η = (ε/2)/(Λ+1)` where `Λ = ∑_{k<N}(σ₀^k + ρ₀^{-(k+1)})` is the operator weight of the
partial sum.  The two halves of the error are then `ε/2` each.

Axiom audit: every declaration within `propext, Classical.choice, Quot.sound`.

**B3 now needs only the Mittag-Leffler replay**: the corrected sequence of `exists_dbar_approx_sequence`
and the limit argument of `dbar_global_solve`, with balls replaced by polyannuli,
`dbar_polydisc_solve` by `dbar_polyannulus_solve`, and `exists_entire_approx_closedBall` by
`exists_punctured_approx_polyannulus`.  Every ingredient is now in place, including Weierstrass,
which applies verbatim on any ball inside `(ℂ^×)^r`.

## The punctured space, its exhaustion, and the polyannulus cutoff (2026-08-06)

`formal/GaloisForLFunctions/HTGeometry/DbarPuncturedSolve.lean`:

- `puncturedSpace`, `isOpen_puncturedSpace` — `(ℂ^×)^n` as a product domain.
- `puncturedExhaustion`, `puncturedExhaustion_mono`, `mem_puncturedExhaustion_of_mem` — the
  increasing exhaustion by the polyannuli `1/(m+2) < |z_i| < m+2`, and the fact that it fills the
  space: for a point with all coordinates nonzero, the coordinates are bounded above by the pi norm
  and their inverses are bounded because the index set is finite.
- `exists_polyannulus_cutoff` — **a smooth cutoff between two nested polyannuli**, one on the inner
  and supported in the outer, as the product of the coordinate annulus cutoffs.  This is what makes
  a datum defined only on the punctured space into a globally smooth one at each stage of the
  exhaustion, which is what `dbar_polyannulus_solve` consumes.

Also weakened `differentiableOn_of_tendstoUniformlyOn` (Weierstrass) and
`tendsto_torusIntegral_smul` from global continuity to continuity **on the ball**, since the
corrected sequence on `(ℂ^×)^r` is continuous only there.

Axiom audit: within `propext, Classical.choice, Quot.sound`.

## The corrected sequence on the punctured space (2026-08-06)

`formal/GaloisForLFunctions/HTGeometry/DbarPuncturedSolve.lean`:

- `wirtingerAntihol_sub`, `dzbarAt_sub_at` — **`∂̄_j` is subtractive at a point of
  differentiability**.  The corpus's `dzbarAt_sub` needs global differentiability, which the
  corrected sequence does not have: the Runge corrections are holomorphic only on the punctured
  space.
- `puncturedClosed`, `puncturedClosed_subset`, `puncturedClosed_mono`,
  `exists_mem_puncturedClosed` — the closed polyannuli of the exhaustion, their inclusion in the
  open ones, their monotonicity, and the fact that every point of the punctured space lies in all
  late ones.
- `exists_dbar_punctured_sequence` — **the corrected sequence**: local solutions from
  `dbar_polyannulus_solve` on the polyannuli `1/(m+2) < |z_i| < m+2`, consecutive differences
  holomorphic there by the Cauchy–Riemann criterion, corrected by functions holomorphic on all of
  `(ℂ^×)^n` from `exists_punctured_approx_polyannulus` so that consecutive corrected solutions
  differ by at most `2^{-m}` on `1/(m+1) ≤ |z_i| ≤ m+1`.

Axiom audit: within `propext, Classical.choice, Quot.sound`.

The limit argument is the last step of B3, and is the same as `dbar_global_solve`: the tail is
dominated by a geometric series so the sum exists at every point of the punctured space; the
convergence is uniform on every closed polyannulus of the exhaustion, so the limit is continuous
there; on any ball inside the punctured space the partial sums are holomorphic and converge
uniformly, so Weierstrass makes the difference holomorphic; hence the limit is smooth and solves
the system wherever the member does.

## B3 COMPLETE — global solvability of `∂̄` on `(ℂ^×)^n` (2026-08-06)

`formal/GaloisForLFunctions/HTGeometry/DbarPuncturedSolve.lean`:

  `dbar_punctured_solve` — **a smooth datum on `ℂⁿ` that is `∂̄`-closed on `(ℂ^×)^n` has a
  primitive there**: there is `u`, smooth at every point of `(ℂ^×)^n`, with `∂̄_j u = f_j` on
  `(ℂ^×)^n` for every `j`.

Supporting: `puncturedExhaustion_subset_closed`, and inside the proof the monotonicity of both
exhaustions in the index, the geometric domination of the tail, uniform convergence on every closed
polyannulus, continuity of the limit there, and the Weierstrass step on every ball inside the
punctured space.

**This is Cartan theorem B for `(ℂ^×)^n` in Dolbeault form, in degree one.**  With
`dbar_global_solve` it is the second complete instance of the Dolbeault programme, and the harder
one: on `ℂⁿ` the Runge step is truncation of a Taylor series, on `(ℂ^×)^n` it is the several-variable
Laurent theorem built above.

Axiom audit: `propext, Classical.choice, Quot.sound`.

### What B4 now needs

The corpus already owns sheaf cohomology (`deningerSheafCohomology`,
`deningerSheafCohomologyZeroEquiv`, `deningerFlasque_isZero_cohomology`,
`DeningerOpenFreeSheaf`) and the Čech side (`CechFineAcyclicModule`, `DeningerCechHomotopy`).  What
is left is to write down the sheaf of holomorphic functions and the sheaves of smooth `(0,q)`-forms
on an open subset of `ℂⁿ`, to observe that the Dolbeault sequence is exact — which is the local
statement `dbar_polydisc_solve` — and that the form sheaves are acyclic, and to read off
`H^q(Z, O_Z) = 0`.

## B4 design, and what it really needs (2026-08-06)

Two routes to `H^q(Z, O_Z) = 0`, and the scope question they expose.

**Degree one is reachable now, without building a single sheaf.**  `H^1(Z, O) = 0` in Čech form is
the classical Dolbeault argument done by hand:

  given a cover `{U_i}` of `Z` with a subordinate smooth partition of unity `ρ` and a holomorphic
  cocycle `F_{ij}` on the overlaps, set `g_i := ∑_k ρ_k F_{ik}` (extended by zero).  Then
  `g_i − g_j = F_{ij}` because `∑ρ = 1` and `F` is a cocycle, so `∂̄g_i = ∂̄g_j` on overlaps and the
  local `∂̄g_i` glue to one global `(0,1)`-datum `h`, which is `∂̄`-closed because the antiholomorphic
  derivatives commute.  `dbar_punctured_solve` gives `u` with `∂̄u = h` on `Z`, and `s_i := g_i − u`
  is holomorphic on `U_i` with `s_i − s_j = F_{ij}`.

  The corpus's `CechFineAcyclicModule` is the same averaging trick one degree down, so its shape is
  reusable.  The fiddly part is domain bookkeeping: the glued `h` is defined on `⋃U_i`, and
  `dbar_punctured_solve` wants a globally smooth datum, so either the cover must be a cover of `ℂⁿ`
  or `h` must be cut off.

**Degrees `q ≥ 2` need the `(0,q)` Dolbeault layer**, which is the honest remaining gap.  The corpus
has the objects — `DbarForm n q := (Fin q → Fin n) → (Fin n → ℂ) → ℂ` and `dbarOp`, the alternating
sum of the `∂̄_k` over the slots — but every solvability theorem built so far is degree one: the
datum is indexed by `Fin n` and the primitive is a scalar.  The induction that proves
`dbar_polydisc_solve` has to be replayed with forms: at each step one clears the direction `k` from
the top coefficient family using the same coordinatewise Cauchy transform, and the residue is a form
of the same degree with one fewer active direction.  The cutoff, the slab estimates, the smoothness
of the transform and the recursion structure all carry over unchanged; what changes is the
bookkeeping of the index tuples and the sign in `dbarOp`.

So the order is: `(0,q)` Dolbeault on a polydisc → on a product domain → the exhaustion arguments
again (they are generic in the degree) → then B4 in all degrees, for which the sheaf-theoretic side
is already corpus-owned.

## The `(0,q)` layer: first pieces, and a design finding (2026-08-06)

`formal/GaloisForLFunctions/HTGeometry/DbarFormsBasic.lean`:

- `SmoothForm`, `formSub`, `SmoothForm.sub`, `SmoothForm.differentiable` — smoothness of a form and
  the difference of two forms.
- `dbarOp_smooth` — **the Dolbeault operator preserves smoothness**, from
  `contDiff_infty_dzbarAt`.
- `dbarOp_sub` — **it is subtractive**.
- `FormBelow`, `FormBelow.mono` — "the form uses only directions below `m`", the predicate the
  induction decreases.
- `consFace_zero`, `consFace_succ`, `dbarOp_cons` — **the Dolbeault operator on a tuple with a
  prepended index separates the zeroth slot**:

    `∂̄G (cons k J) = ∂̄_k (G J) + ∑_t (−1)^{t+1} ∂̄_{J t} (G (cons k (face_t J)))`.

  This is the form-level analogue of `cechD_cons`, and it is the identity the induction step turns
  into "solving in direction `k` and disturbing nothing above it".

**The design finding.**  `DbarForm n q := (Fin q → Fin n) → (Fin n → ℂ) → ℂ` indexes coefficients by
*arbitrary* `q`-tuples, with no antisymmetry, so it is the **non-alternating** model.  The classical
Dolbeault induction needs the decomposition `f = dz̄_k ∧ g + h` with `h` free of `dz̄_k`, and that
decomposition is only available for alternating families: with arbitrary tuples, `f J` for a `J`
containing `k` in a slot other than the first is independent data, and nothing ties it to
`f (cons k J')`.

So before the `(0,q)` induction can be written, the model has to be fixed: either add an
alternating predicate to `DbarForm` and prove `dbarOp` preserves it, or re-index by strictly
increasing tuples and restate `dbarOp` with the insertion sign.  The increasing-tuple model makes
the decomposition definitional — the tuples containing `k` as their largest entry are exactly the
`cons`-images — at the cost of restating the operator; the alternating-predicate model keeps
`dbarOp` as it is at the cost of a combinatorial preservation lemma and of carrying the predicate
through every step.  **The increasing-tuple model is the one to build**, because the induction's
hypothesis "uses only directions below `m`" is then a statement about the largest entry, which is
exactly what `Fin.cons` exposes.

Everything already proved — the cutoff, the slab estimates, the smoothness of the coordinatewise
Cauchy transform, the recursion over the chain of domains, and both exhaustion arguments — is
degree-agnostic and will be reused unchanged.

## The set-indexed model and the first clause of the `(0,q)` step (2026-08-06)

`formal/GaloisForLFunctions/HTGeometry/DbarAltForms.lean`:

- `SetForm`, `insertSign`, `setDbar` — `(0,q)`-forms indexed by finite sets of directions, with the
  Dolbeault operator as the signed sum over deletions, the sign being the parity of the number of
  smaller directions already present.
- `SmoothSetForm`, `setFormSub`, `setDbar_smooth`, `setDbar_sub`, `SetFormBelow`,
  `SetFormBelow.mono` — the same basic layer as for tuples, in the model the induction can use.
- `setDbar_insert` — **the operator separates the distinguished direction**: on `insert k T` the
  `k`-term is `±∂̄_k (f T)` and every other term keeps `k` inside the index.
- `insertSign_ne_zero`, `insertSign_mul_inv` — the sign is a unit.
- `setTransform` — **the primitive**: on a set not containing `k` it is the coordinatewise Cauchy
  transform of the cut-off top coefficient, normalized by the inverse insertion sign; on a set
  already containing `k` it is zero.  That second clause is what makes the induction close: in
  `setDbar_insert` every term other than the `k`-term evaluates `setTransform` at a set containing
  `k`, hence at zero.
- `setDbar_setTransform_top` — **the first clause of the step**: on the small domain, where both
  cutoffs are one, `insertSign k T · ∂̄_k (setTransform f … k T) = f (insert k T)`.

The proof needed complex-scalar linearity of `∂̄` at a point, which the corpus had only for real
scalars (`dzbar_const_smul`); it is proved here inline through the Wirtinger form, including the
non-differentiable branch.

Axiom audit: within `propext, Classical.choice, Quot.sound`.

## The residue clause of the `(0,q)` step (2026-08-06)

`setDbar_setTransform_eq` — **on a set containing the distinguished direction, the differential of
the transform is exactly the top coefficient**:

  `setDbar (setTransform f χ ψ k) (insert k T) z = f (insert k T) z`

whenever `k ∉ T` and both cutoffs are one at `z`.  The `k`-term of `setDbar_insert` reproduces the
coefficient by `setDbar_setTransform_top`, and every other term evaluates the transform at
`(insert k T).erase j`, a set that still contains `k` because `j ∈ T` and `k ∉ T` — so the transform
is zero there by construction and its `∂̄_j` vanishes.

So the residue `setFormSub f (setDbar (setTransform f χ ψ k))` vanishes on **every** set containing
`k`, with no appeal to `∂̄`-closedness.  That is the half of the induction step which the tuple model
could not even state.

The other half — that the residue also vanishes on sets containing a direction strictly above `k`,
where `f` itself vanishes — is where closedness enters, exactly as in degree one: for a set `S` not
containing `k` but containing some `l > k`, the terms with `j ≠ l` vanish because
`insert k (S.erase j)` still contains `l` and `f` is zero there, while the term `j = l` is killed by
expanding `setDbar f (insert k S) = 0`, in which every summand other than the wanted one is a
derivative of a coefficient at a set containing `l`.

Axiom audit: `propext, Classical.choice, Quot.sound`.

## The closedness crux of the `(0,q)` step (2026-08-06)

`dzbarAt_eq_zero_of_setDbar_zero` — **closedness forces the derivative along a direction in which
the form vanishes**: if `∂̄f = 0` on an open `P` and `f S = 0` on `P` for every `S` containing `l`,
then `∂̄_l (f W) = 0` on `P` for every `W` not containing `l`.

The proof is short and is the exact analogue of the degree-one step `∂̄_j f_k = ∂̄_k f_j = 0`:
expand `∂̄f` at `insert l W`; by `setDbar_insert` the `l`-term is `insertSign l W · ∂̄_l (f W)` and
every other summand differentiates a coefficient at `(insert l W).erase j`, a set that still
contains `l` — so that coefficient vanishes on an open neighbourhood and its derivative is zero by
locality of `∂̄`.  Since the insertion sign is a unit, the `l`-term is zero.

With it and `setFormSub_setTransform_eq_zero` the induction step has both halves in the set model:
the residue vanishes on every set containing the distinguished direction (by construction of the
transform, no closedness needed), and on every set containing a direction strictly above it (by this
lemma, feeding `dzbarAt_dbarSliceSolution_eq_zero` exactly as in degree one).

Axiom audit: `propext, Classical.choice, Quot.sound`.

## The `(0,q)` step: both clauses proved (2026-08-06)

`dzbarAt_setTransform_eq_zero` — **the transform is annihilated by every direction along which the
top coefficient is already `∂̄`-closed on the domain.**  This is the degree-one second clause
transported to the set model: the cutoff in the distinguished coordinate commutes with `∂̄_j` for
`j ≠ k`, the second cutoff is invisible by locality because it is one on the domain, and
`dzbarAt_dbarSliceSolution_eq_zero` then kills the whole `k`-line.  The normalization by the inverse
insertion sign is carried through by the complex-scalar linearity of `∂̄` proved alongside it.

`setFormSub_setTransform_eq_zero` — the residue vanishes on every set containing the distinguished
direction.

So both clauses of the step are proved:

| where | why |
|---|---|
| sets containing `k` | the transform is zero on sets containing `k`, so the differential reduces to its `k`-term, which reproduces the coefficient |
| sets containing some `l > k` | `f` vanishes there, and `dzbarAt_eq_zero_of_setDbar_zero` plus `dzbarAt_setTransform_eq_zero` kill the differential term by term |

Axiom audit: within `propext, Classical.choice, Quot.sound`.

## The `(0,q)` induction step, assembled (2026-08-06)

`setDbar_step_below` — **subtracting the differential of the transform lowers by one the highest
direction the form uses**:

  if `f` is `∂̄`-closed on `productDomain D` and uses only directions `≤ m`, and `k` is the direction
  with `(k : ℕ) = m`, then `f − ∂̄(setTransform f χ ψ k)` uses only directions `< m` on
  `productDomain D'`.

The proof splits on whether the index set contains `k`.  If it does, the residue is zero by
`setFormSub_setTransform_eq_zero`, with no closedness used.  If it does not, then the offending
direction `l` satisfies `l ≠ k` and hence `(l : ℕ) > m`, so `f` itself vanishes there; the
differential of the transform is then killed term by term — the terms `j ≠ l` because the coefficient
at `insert k (S.erase j)` still carries `l`, and the term `j = l` because
`dzbarAt_eq_zero_of_setDbar_zero` turns closedness into the vanishing of `∂̄_l` at
`insert k (S.erase l)`.

This is the general-degree analogue of `dbar_product_step_smooth`, and like it, it is stated over an
arbitrary **product domain**, so it applies to polydiscs and polyannuli alike without any further
work.

Axiom audit: `propext, Classical.choice, Quot.sound`.

### Remaining in the `(0,q)` chain

The recursion over directions (the analogue of `dbar_product_solve_aux`, which is a plain induction
on the number of directions still to clear, with the chain of domains supplying the cutoffs), and
then the two exhaustion arguments, which are degree-agnostic: `exists_dbar_approx_sequence` /
`dbar_global_solve` over `ℂⁿ` and `exists_dbar_punctured_sequence` / `dbar_punctured_solve` over
`(ℂ^×)ⁿ` are written entirely in terms of "solve on a member of the exhaustion, correct the
difference, take the limit", and the only degree-dependent input is the step above.

## What the recursion needs next: `d² = 0` in the set model (2026-08-06)

Writing the recursion over directions exposed the one identity the degree-one chain got for free.

In degree one the residue's `∂̄`-closedness came from `dzbarAt_comm` — the antiholomorphic
derivatives commute — used directly.  In general degree the residue is `f − ∂̄G` and its closedness
is `∂̄f − ∂̄∂̄G = 0`, so it needs

  `setDbar (setDbar f) = 0`,

which is `dzbarAt_comm` plus the sign bookkeeping: expanding twice gives
`∑_{k ∈ S} ∑_{j ∈ S.erase k} ε(k,S) ε(j, S.erase k) ∂̄_k ∂̄_j f (S \ {k,j})`, and the terms of the
pairs `(k,j)` and `(j,k)` carry the same set and the same iterated derivative but opposite signs,
because

  `insertSign k (S.erase k) · insertSign j ((S.erase k).erase j)
     = − insertSign j (S.erase j) · insertSign k ((S.erase j).erase k)`.

That sign identity is the crux; with it the double sum is an involution-paired cancellation.

Also noted while setting up the recursion: `SetForm` does not track the degree, so the induction's
base case needs `f ∅ = 0` as an explicit hypothesis — a form of positive degree has no
degree-zero part.  It is preserved by the step, since the differential of anything is zero at the
empty set (an empty sum), so `(f − ∂̄G) ∅ = f ∅ = 0`.

So the order is: `setDbar_setDbar_eq_zero` → the recursion over directions (the analogue of
`dbar_product_solve_aux`, whose shape is already fixed by the degree-one proof) → the two
exhaustions, which are degree-agnostic → B4.

### The sign identity, verified by hand

For `j ≠ k` both in `S`, write

  `a = |{i ∈ S : i < k}|`,  `c = |{i ∈ S : i < j}|`,
  `b = |{i ∈ S \ {k,j} : i < j}|`,  `d = |{i ∈ S \ {j,k} : i < k}|`.

Then `insertSign k (S.erase k) = (−1)^a`, `insertSign j ((S.erase k).erase j) = (−1)^b`,
`insertSign j (S.erase j) = (−1)^c`, `insertSign k ((S.erase j).erase k) = (−1)^d`.

Take `j < k` without loss of generality.  Deleting `k` does not change the count below `j`, and `j`
is not below itself, so `b = c`.  Deleting `j` removes exactly one element below `k`, and `k` is not
below itself, so `d = a − 1`.  Hence

  `(−1)^a (−1)^b = (−1)^{a+b}`  and  `−(−1)^c (−1)^d = −(−1)^{b+a−1} = (−1)^{a+b}`,

so the two orders of deletion carry opposite signs and the double sum of `setDbar ∘ setDbar` cancels
in pairs, `∂̄_k ∂̄_j` being symmetric by `dzbarAt_comm`.  This is what has to be formalized next; the
work is the two cardinality identities `b = c` and `d = a − 1` in `Finset.filter` form.

## The sign identity, formalized (2026-08-06)

`filter_erase_self`, `filter_erase_two_lt`, `filter_erase_two_lt'`, `insertSign_swap` in
`DbarAltForms.lean`.

The three `Finset.filter` identities are exactly the counting facts derived by hand above: deleting
a direction never changes the count strictly below it; deleting a *larger* direction does not change
the count below a smaller one; deleting a *smaller* direction removes exactly one element from the
count below a larger one, which is `Finset.card_erase_of_mem`.  With them,

  `insertSign k (S.erase k) · insertSign j ((S.erase k).erase j)
     = −(insertSign j (S.erase j) · insertSign k ((S.erase j).erase k))`   for `j < k ∈ S`,

so the two orders of deleting a pair of directions carry opposite signs.  That is the whole content
of `d² = 0` beyond `dzbarAt_comm`: the double sum of `setDbar ∘ setDbar` pairs `(k,j)` with `(j,k)`,
the iterated derivatives agree by commutativity and the coefficients are at the same set, and the
signs cancel.

Axiom audit: `propext, Classical.choice, Quot.sound`.

## `d² = 0`: linearity and the expansion (2026-08-06)

`dzbarAt_const_mul` — **`∂̄_j` is homogeneous under a complex constant.**  The corpus had only the
real-scalar version; the insertion signs are complex, so this was needed three times over and is now
factored out, including the branch where the slice is not differentiable.

`dzbarAt_finset_sum` — **`∂̄_j` is additive over a finite sum**, by induction on the index set.

`setDbar_setDbar_expand` — **the double differential expands into a sum over ordered pairs of
distinct directions**:

  `∂̄(∂̄f) S = ∑_{k ∈ S} ∑_{j ∈ S.erase k} ε(k,S∖k)·ε(j,S∖{k,j}) · ∂̄_k ∂̄_j f (S∖{k,j})`.

With `insertSign_swap` giving the sign flip and `dzbarAt_comm` the symmetry of the iterated
derivative, the pairing `(k,j) ↦ (j,k)` is a fixed-point-free involution of the index set whose
terms cancel, which is `d² = 0`.

Axiom audit: all three within `propext, Classical.choice, Quot.sound`.

## `d² = 0` PROVED (2026-08-06)

`setDbar_setDbar_eq_zero` — **the Dolbeault operator on set-indexed forms squares to zero**, for
any form with `C²` coefficients.

The double sum is transported to a sum over `S.sigma (fun k => S.erase k)`, the set of ordered pairs
of distinct directions of `S`, and `Finset.sum_involution` is applied to the transposition
`⟨k,j⟩ ↦ ⟨j,k⟩`.  It is fixed-point free because the pair is distinct; the two terms have the same
coefficient because `erase_erase_comm`, the same iterated derivative because `dzbarAt_comm`, and
opposite signs because `insertSign_swap`.

This was the last identity the general-degree recursion was waiting on: the residue of the induction
step is `f − ∂̄G`, and its `∂̄`-closedness is now `∂̄f − ∂̄∂̄G = 0 − 0`.

Axiom audit: `propext, Classical.choice, Quot.sound`.

## The `(0,q)` layer: every local ingredient is proved (2026-08-06)

`setFormAdd`, `SmoothSetForm.add`, `setDbar_add`, `setDbar_empty`, `smoothSetForm_setTransform`
complete the algebraic layer.  The full inventory of `DbarAltForms.lean`:

| piece | content |
|---|---|
| `SetForm`, `insertSign`, `setDbar` | the model and the operator |
| `setDbar_smooth`, `setDbar_add`, `setDbar_sub`, `setDbar_empty` | its formal properties |
| `setDbar_insert` | separation of a distinguished direction |
| `setTransform`, `smoothSetForm_setTransform` | the primitive and its smoothness |
| `setDbar_setTransform_top`, `setFormSub_setTransform_eq_zero` | first clause of the step |
| `dzbarAt_setTransform_eq_zero` | second clause of the step |
| `dzbarAt_eq_zero_of_setDbar_zero` | closedness crux |
| `setDbar_step_below` | **the induction step** |
| `dzbarAt_const_mul`, `dzbarAt_finset_sum` | `∂̄` linearity, complex scalars and finite sums |
| `insertSign_swap`, `erase_erase_comm`, `setDbar_setDbar_expand` | the sign combinatorics |
| `setDbar_setDbar_eq_zero` | **`d² = 0`** |

Everything is degree-agnostic and stated over an arbitrary **product domain**, so it applies to
polydiscs and polyannuli alike.

### The one remaining shape question for the recursion

The recursion over directions is the analogue of `dbar_product_solve_aux` and needs, at each link of
the chain and each direction, the cut-off pair together with the analytic data the step consumes:
the slab radius, the two bounds, smoothness and compact support of the cut-off top coefficients —
**for every index set `T`**, because the transform is applied to all of them at once.  In degree one
there was a single coefficient and these were five plain hypotheses; here they are five families
indexed by `T`, and the statement is only writable if they are bundled.

The natural bundling is a `Prop`-valued predicate `StepCutoff D D' k f` asserting the existence of
`chi`, `psi` and the families, since `chi` and `psi` are data and cannot live in a structure field
of a `Prop`.  With that predicate the recursion reads exactly like `dbar_product_solve_aux`: induct
on the number of directions still to clear, apply `setDbar_step_below` at `k = ⟨m, _⟩`, use
`setDbar_setDbar_eq_zero` for the residue's closedness and `SmoothSetForm.sub` for its smoothness,
recurse, and assemble with `setDbar_add`.

## The `(0,q)` Dolbeault–Grothendieck lemma PROVED (2026-08-06)

`cutCoeff`, `StepCutoff`, `setDbar_solve_aux`, `setDbar_solve` in `DbarAltForms.lean`.

`StepCutoff D D' k f` bundles what one link of a chain of product domains supplies at a direction:
the two cutoffs, and — indexed by the set `T` — the slab radius, the two bounds, smoothness and
compact support of the cut-off top coefficients.  The bundling has to be an existential `Prop`
because `chi` and `psi` are data.

`setDbar_solve_aux` is the induction on the number of directions still to clear, with the same shape
as `dbar_product_solve_aux`: for `n ≤ m` the hypothesis is vacuous and the step is a
re-application; otherwise the step at `k = ⟨m, _⟩` produces the transform `G`, the residue
`f − ∂̄G` is smooth (`SmoothSetForm.sub`), vanishes at the empty index (`setDbar_empty`), is
`∂̄`-closed (`setDbar_sub` and `setDbar_setDbar_eq_zero`) and lies below `m` (`setDbar_step_below`);
the recursive solution `v` is assembled with `setDbar_add` into `G + v`.

`setDbar_solve` — **the `(0,q)` Dolbeault–Grothendieck lemma on a product domain**: a smooth
`∂̄`-closed form of positive degree on the first domain of the chain has a smooth primitive on the
`n`-th.  Since the statement is over an arbitrary product domain, it covers **polydiscs and
polyannuli in every degree at once**.

Axiom audit: `propext, Classical.choice, Quot.sound`.

### What is left

The two exhaustion arguments at general degree.  Both are written entirely as "solve on a member of
the exhaustion, correct the difference by something holomorphic on the whole space, take the limit",
and every ingredient of that is degree-agnostic — `dbar_polydisc_solve` is replaced by
`setDbar_solve` with the polydisc chain, `dbar_polyannulus_solve` by the same with the polyannulus
chain, and the corrections come from the same Runge theorems, applied to each coefficient of the
form separately.  Then B4.

## The cut-off data from a pair of bumps (2026-08-06)

`stepCutoff_of_bumps` — **`StepCutoff` follows from the two bumps alone.**  Smoothness and compact
support of the cut-off top coefficients come from the second bump; the slab radii and the two bounds
are then the usual consequences of compact support, chosen uniformly in the index set by `choose`,
with the two slab radii merged by a maximum.

This is what makes the `(0,q)` lemma usable: the chain of polydiscs supplies its bumps from
`exists_polydisc_bumps` and the chain of polyannuli from `exists_annulus_cutoff` together with
`exists_bounded_bump`, exactly as in degree one — so both instantiations of `setDbar_solve` reduce
to the bump constructions already proved.

Axiom audit: `propext, Classical.choice, Quot.sound`.

## Recipe for the two instantiations of `setDbar_solve`

Both are transcriptions of the degree-one proofs, with the chain and the bumps unchanged.

**Polydisc.**  Chain `Dom o i := Metric.ball (c i) (R o i)` with the geometric interpolation
`R o i := r i − (r i − ρ i)(1 − 2^{-o})`, so `R 0 = r`, `R` is strictly decreasing in `o`, and
`R n i > ρ i`.  Note `polydisc c s = productDomain (fun i => Metric.ball (c i) (s i))`
definitionally, so no translation is needed.  The link cutoffs come from `exists_polydisc_bumps`
with radii `(R o, R (o+1))` and the outer bound `Rmax := 1 + ∑ i |r i|`, and `stepCutoff_of_bumps`
turns them into `StepCutoff`.  Conclusion: a smooth `∂̄`-closed form of positive degree on
`polydisc c r` has a smooth primitive on `polydisc c ρ`.

**Polyannulus.**  Identical, with `Dom o i := annulus (A o i) (B o i)` for the two geometric chains
`annulusChainIn` and `annulusChainOut` already defined, and the link cutoffs from
`exists_annulus_cutoff` and `exists_bounded_bump` — exactly the `hcut` built inside
`dbar_polyannulus_solve`, which can be lifted out and reused verbatim.

**The exhaustions.**  `exists_dbar_approx_sequence` / `dbar_global_solve` and
`exists_dbar_punctured_sequence` / `dbar_punctured_solve` are written as "solve on a member of the
exhaustion, correct the difference, take the limit".  At general degree the same proof runs
coefficientwise: the difference of two consecutive primitives is a `∂̄`-closed form of degree `q−1`
whose coefficients are holomorphic where both solve, so each coefficient is corrected by the Runge
theorem already proved (`exists_entire_approx_closedBall` for `ℂⁿ`,
`exists_punctured_approx_polyannulus` for `(ℂ^×)ⁿ`), and the estimates are summed over the finitely
many index sets.  Weierstrass applies to each coefficient separately, so
`differentiableOn_of_tendstoUniformlyOn` is used unchanged.

## The `(0,q)` Dolbeault lemma on a polydisc, in every degree (2026-08-06)

`polydiscChain`, `setDbar_polydisc_solve` — **a smooth `∂̄`-closed form of positive degree on
`polydisc c r` has a smooth primitive on every strictly smaller `polydisc c ρ`**, in every degree.

The chain is the geometric interpolation `R o = r − (r − ρ)(1 − 2^{-o})`: it starts at `r`, is
strictly decreasing, and still contains `ρ` after `n` steps.  Each link's cutoffs come from
`exists_polydisc_bumps` and are turned into `StepCutoff` by `stepCutoff_of_bumps`.  Because
`polydisc c s` is definitionally `productDomain (fun i => ball (c i) (s i))`, no translation between
the two notions of domain is needed anywhere.

This is `dbar_polydisc_solve` generalized from degree one to all degrees, and it is the local
statement the Dolbeault resolution needs — the exactness of `0 → O → A^{0,0} → A^{0,1} → ⋯` at
every point.

Axiom audit: `propext, Classical.choice, Quot.sound`.

## The `(0,q)` Dolbeault lemma on a polyannulus, in every degree (2026-08-06)

`setDbar_polyannulus_solve` — **a smooth `∂̄`-closed form of positive degree on the polyannulus of
radii `(a, b)` has a smooth primitive on every strictly smaller polyannulus**, in every degree.

Same shape as the polydisc instantiation: the chains `annulusChainIn` and `annulusChainOut` already
built for degree one, the link cutoffs from `exists_annulus_cutoff` and `exists_bounded_bump`, and
`stepCutoff_of_bumps` to package them.

Both instantiations of `setDbar_solve` are therefore done, and the `(0,q)` local theory is complete:

| domain | degree one | every degree |
|---|---|---|
| polydisc | `dbar_polydisc_solve` | `setDbar_polydisc_solve` |
| polyannulus | `dbar_polyannulus_solve` | `setDbar_polyannulus_solve` |

Axiom audit: `propext, Classical.choice, Quot.sound`.

## A structural simplification for `q ≥ 2`, and what degree tracking is still needed

Setting up the exhaustion at general degree turned up a fact that changes the remaining work.

**For `q ≥ 2` the exhaustion needs no Runge step at all.**  In degree one the difference of two
consecutive local primitives is a *holomorphic function* on the smaller ball, and a holomorphic
function cannot in general be corrected to zero — only approximated, which is why the whole Laurent
and Runge apparatus was necessary.  In degree `q ≥ 2` the difference `u_{m+1} − u_m` is a
`∂̄`-closed form of degree `q − 1 ≥ 1`, and the local lemma applies to *it*: on a slightly smaller
polydisc it is `∂̄w_m` for some `w_m`.  Replacing `u_{m+1}` by `u_{m+1} − ∂̄w_m` makes it agree with
`u_m` exactly on that smaller domain, so the corrected sequence **stabilizes** and the limit is
defined pointwise with no convergence argument, no Weierstrass, and no approximation.

So the remaining exhaustion work splits: degree one is already done (`dbar_global_solve`,
`dbar_punctured_solve`), and degrees `≥ 2` need only the stabilization argument, which is much
shorter.

**What degree tracking is needed.**  `SetForm` is inhomogeneous — a family over all finite index
sets — and `setDbar u {k} = ±∂̄_k (u ∅)`, so the degree-zero part of a primitive is visible in the
degree-one part of its differential.  For the stabilization argument the forms must be homogeneous,
so a predicate

  `SetFormDeg q f := ∀ S, S.card ≠ q → f S = 0`

has to be added, together with the observations that it is preserved by the construction: the
transform of a form of degree `q` has degree `q − 1`, because `setTransform f χ ψ k T` involves only
`f (insert k T)`, which vanishes unless `|T| = q − 1`, and the coordinatewise Cauchy transform of the
zero function is zero.  The residue and the recursive primitive then stay homogeneous of the right
degrees.

## Degree tracking, landed (2026-08-06)

`SetFormDeg`, `SetFormDeg.empty`, `SetFormDeg.sub`, `SetFormDeg.add`, `dbarSliceSolution_zero`,
`setTransform_deg`, `setDbar_deg` in `DbarAltForms.lean`.

- A form of positive degree has no degree-zero part, which is the hypothesis `setDbar_solve` needs.
- **The transform of a form of degree `q + 1` has degree `q`**: `setTransform f χ ψ k T` involves
  only `f (insert k T)`, which vanishes unless `|T| = q`, and the coordinatewise Cauchy transform of
  the zero function is zero.
- **The differential of a form of degree `q` has degree `q + 1`**: every summand differentiates a
  coefficient at a set of cardinality `|S| − 1`, which vanishes unless that is `q`.
- Degree is preserved by sums and differences.

With these the stabilization argument for `q ≥ 2` is expressible: the difference of two consecutive
local primitives is homogeneous of degree `q − 1 ≥ 1`, hence has no degree-zero part, hence is
`∂̄`-exact on a smaller domain by `setDbar_polydisc_solve`, and the correction makes consecutive
members agree exactly rather than approximately.

Axiom audit: within `propext, Classical.choice, Quot.sound`.

## The stabilizing exhaustion for `q ≥ 2`: the construction to write

Hypotheses: an increasing family `P : ℕ → Set (Fin n → ℂ)` exhausting `Ω`, and local solvability
"every `∂̄`-closed form of degree `q` on `P (m+1)` with no degree-zero part has a primitive on
`P m`" — which is `setDbar_polydisc_solve` for the ball exhaustion and
`setDbar_polyannulus_solve` for the polyannulus one.

Construction.  Let `u m` solve `∂̄(u m) = f` on `P m`.  Define `v` recursively with `v 0 := u 0` and

  `v (m+1) := u (m+1) + ∂̄ w_m`,  where `∂̄ w_m = v m − u (m+1)` on `P (m−1)`.

The right-hand side is legitimate: `v m − u (m+1)` is `∂̄`-closed on `P m` because both solve
`∂̄· = f` there, and it is homogeneous of degree `q − 1 ≥ 1`, so it has no degree-zero part
(`SetFormDeg.empty`) and the local lemma applies to it.  Then `∂̄(v (m+1)) = f` on `P (m+1)` by
`setDbar_setDbar_eq_zero`, and `v (m+1) = v m` on `P (m−1)`.

So the sequence is eventually constant at each point: for `z ∈ P M` the value `v m z` is the same
for all `m ≥ M+1`, and `u z := v (M+1) z` is well defined.  No convergence, no Weierstrass, no
approximation — the whole Laurent and Runge apparatus is needed only for `q = 1`, which is already
done in both geometries.

The one Lean subtlety is that `w_m` depends on `v m`, so the recursion is dependent: the state to
recurse on is the subtype of forms carrying the invariant (smooth, homogeneous of degree `q`, solving
`∂̄· = f` on `P m`), and `Nat.rec` on that subtype produces the sequence together with its
properties, the agreement `v (m+1) = v m` on `P (m−1)` being read off the step.

## Degree threaded through the whole `(0,q)` chain (2026-08-06)

`setDbar_solve_aux`, `setDbar_solve`, `setDbar_polydisc_solve` and `setDbar_polyannulus_solve` now
carry the degree: from `SetFormDeg (q+1) f` they conclude `SetFormDeg q u` for the primitive, as
well as its smoothness and the equation.

This was needed, not cosmetic.  The stabilization argument for `q ≥ 2` corrects a primitive by a
primitive **of the difference of two primitives**, and to apply the local lemma to that difference
one must know it is homogeneous of positive degree — otherwise `SetFormDeg.empty` does not apply and
the local lemma has no hypothesis to consume.  Threading the degree costs only `setTransform_deg`
and `setDbar_deg` at the step, and `SetFormDeg.add` at the assembly.

The `(0,q)` local theory is therefore complete and self-contained:

  `SetFormDeg (q+1) f` ∧ smooth ∧ `∂̄`-closed on the larger domain
    ⟹ ∃ `u`, smooth, `SetFormDeg q u`, `∂̄u = f` on the smaller domain,

for polydiscs and polyannuli alike, in every degree.

Axiom audit: `propext, Classical.choice, Quot.sound`; no `sorry` anywhere in the module.

## The Dolbeault complex is exact in every positive degree (2026-08-06)

`GaloisForLFunctions/HTGeometry/DbarExhaustionSolve.lean`.

**The stabilizing exhaustion.**  `DbarStageSolvable E` says the system is solvable from `E (m+1)`
to `E m` in every degree; `setDbar_exhaustion_solve` upgrades that to global solvability on the
union, for closed forms of degree `q + 2`.  The step `dbarPrimitiveOn_step` takes a primitive `u` on
`E (m+1)`, a primitive `v` on `E (m+3)`, forms the closed difference `v − u` of degree `q + 1 ≥ 1`,
solves `∂̄w = v − u` on `E m`, and returns `v − ∂̄w`: a primitive on `E (m+2)` that agrees with `u`
on `E m`, by `setDbar_setDbar_eq_zero`.  The sequence is therefore *exactly* constant near every
point, and the pointwise limit is smooth because it agrees with a fixed member on a neighbourhood.

Two Lean points worth keeping.  The recursion is dependent — the step needs the invariant of its
input — so it is run through a total step function obtained by `by_cases` on the invariant and
`choose`, with the sequence built by `Nat.rec` and the invariant re-proved by induction.  And the
pointwise limit is `fun S z => useq (idx z) S z` with `idx z` the least stage containing `z`; the
proof that this agrees with `useq m` on all of `E m` is the whole content, and it gives both
smoothness (`ContDiffAt.congr_of_eventuallyEq`) and the equation (`setDbar_congr_on_isOpen`).

**Instances.**  `polydiscExhaustion` (concentric polydiscs of radius `m + 1`) and
`puncturedExhaustion` (polyannuli `1/(m+2) < |z_i| < m+2`) are stagewise solvable by
`setDbar_polydisc_solve` and `setDbar_polyannulus_solve`.

**Degree one.**  `pointForm u₀` is the degree-zero form carrying `u₀` at `∅`; its differential is
`∂̄_k u₀` at `{k}` and zero elsewhere.  `dzbarAt_comm_of_setDbar_zero` extracts from closedness at
the two-element set `{j,k}` exactly the compatibility `∂̄_k f_j = ∂̄_j f_k`, because the two signs
are `+1` and `−1`.  So the degree-one case reduces to `dbar_global_solve` / `dbar_punctured_solve`.

**Capstones.**

  `setDbar_exact_global`    : on `ℂ^n`, every smooth `∂̄`-closed form of degree `q + 1` is `∂̄u` for
                              a smooth form `u` of degree `q`.
  `setDbar_exact_punctured` : the same on `(ℂ^×)^n`, with the primitive smooth on the punctured
                              space.

Both unconditional; axioms `propext, Classical.choice, Quot.sound`.  This is Cartan's theorem B for
these two domains, in the concrete Dolbeault form, and it is the whole analytic input to the
vanishing of the coherent cohomology of a complex torus in positive degrees.

## The sheaf-cohomological half: what is built and what the route is (2026-08-06)

The analytic half (Cartan B in Dolbeault form on `ℂ^n` and `(ℂ^×)^n`, every positive degree) is
closed.  The remaining passage to `H^q(Z, O_Z) = 0` in the corpus's own sheaf cohomology
`deningerSheafCohomology U F n = Ext (deningerOpenFree U) F n` is a chain of standard results that
mathlib does not have.  Three of its links are now built.

**Acyclic resolutions.**  `RHTower/Deninger/DeningerAcyclicResolution.lean`.
`DeningerAcyclic F` says all higher cohomology of `F` vanishes.  Two consequences of the covariant
`Ext` sequence: `deningerExt_eq_zero_of_shift` (dimension shifting: with acyclic middle term, a
class of the subsheaf in degree `n+2` comes from degree `n+1` of the quotient) and
`deningerExt_one_eq_zero_of_lift` (degree one dies when sections of the middle term surject onto
sections of the quotient).  Iterating gives `deningerResolution_ext_eq_zero`: **an acyclic
resolution whose sections surject onto the sections of the successive kernels kills all higher
cohomology.**  This is the exact shape Cartan B is used in — the analytic input is precisely the
surjectivity of sections, i.e. global solvability of `∂̄`.

**The Godement sheaf.**  `RHTower/Deninger/DeningerGodement.lean`.
`deningerGodementSheaf F` is `U ↦ ∏_{x ∈ U} F_x`, the sheaf of arbitrary sections of the stalks.
It is a sheaf because the underlying presheaf of types is the presheaf of dependent functions, it is
flasque because a family defined on a smaller open set extends by zero, and the germ map
`deningerGodementι` is a monomorphism by `section_ext`.  This gives the short exact sequence
`0 → F → C⁰(F) → C⁰(F)/F → 0` with flasque — hence acyclic — middle term.

**Fine sheaves.**  `RHTower/Deninger/DeningerFineSheaf.lean`.
`DeningerFineAction F` is a multiplication of sections by continuous real functions, additive in
both arguments, compatible with restriction, unital, and vanishing on any open set where the
function vanishes.  The last axiom is what makes a partition of unity usable.  Two inheritance
theorems close the induction that the dimension shift needs:

- `DeningerFineAction.godement` — the sheaf of arbitrary sections of the stalks of a fine sheaf is
  fine, the multiplication acting through `stalkFunctor`;
- `deningerFineAction_of_epi` / `DeningerFineAction.godementQuotient` — a fine structure transports
  along an epimorphism intertwining the multiplications, so the Godement quotient of a fine sheaf is
  fine.  The support axiom survives because an epimorphism of sheaves is locally surjective, so
  every germ downstairs comes from a section upstairs that the multiplication already kills.

**Why this closes.**  Every kernel of the Godement resolution of a fine sheaf is again fine.  So
once "fine implies degree one vanishes" is available, dimension shifting through the Godement
resolution gives acyclicity in every degree — no soft-sheaf theory, no paracompactness induction
over closed sets.

**What is left, and the exact shape of it.**  One theorem: for `X` paracompact and `F` fine, and
any short exact sequence `0 → F → B → G → 0` of sheaves, `Γ(X,B) → Γ(X,G)` is surjective.  Note it
is only ever needed at `U = ⊤`, because both `deningerExt_eq_zero_of_shift` and
`deningerExt_one_eq_zero_of_lift` consume acyclicity at the same open set at which they conclude.
That removes the usual difficulty that a partition of unity on an open subset need not extend
continuously to the ambient space.

The proof is the classical cocycle argument.  Local lifts `s_i ∈ B(V_i)` of `g`; the differences
`c_{ij} = s_i − s_j` lie in `F(V_i ⊓ V_j)` by left exactness of sections; a partition of unity `ρ_i`
subordinate to `{V_i}`; and `t_i := s_i − ∑_j (ρ_j c_{ij})^0` where the exponent is extension by
zero.  On overlaps `∑_k ρ_k (c_{ik} − c_{jk}) = ∑_k ρ_k c_{ij} = c_{ij}`, so `t_i = t_j` and the
`t_i` glue to a preimage of `g`.  Three pieces of infrastructure are needed for it:

1. extension by zero of `ρ · t` from `V ⊓ W` to `V` when `tsupport ρ ⊆ W` — a two-piece gluing,
   the compatibility being exactly the support axiom of the fine action;
2. locally finite sums of sections — a family `e_j ∈ F(V)` such that every point has a neighbourhood
   on which all but finitely many restrict to zero has a unique sum, defined by gluing the finite
   partial sums;
3. left exactness of sections — `π(b) = 0` implies `b` comes from `F`, because the sections functor
   on sheaves is a composite of two right adjoints and therefore preserves kernels.

Axiom audit for everything landed: `propext, Classical.choice, Quot.sound`.

## Fine sheaves on a paracompact space are acyclic (2026-08-06)

The theorem named as the remaining gap above is proved, unconditionally, in
`RHTower/Deninger/DeningerSheafGluing.lean`, `RHTower/Deninger/DeningerFineLifting.lean` and
`RHTower/Deninger/DeningerFineSurjective.lean`.

  `deningerFine_acyclicOn : DeningerFineAction F → DeningerAcyclicOn F ⊤`

for `X` normal and paracompact.  With `deningerResolution_ext_eq_zero` this is the entire
sheaf-theoretic half of Cartan's theorem B.

**The infrastructure it needed, all of it new.**

- `deningerGlue`, `deningerGlue'`, `deningerGlue_two`, `deningerRes_ext`, `deningerRes_ext_two`,
  `deningerRes_of_overlap` — gluing over a cover, over a two-piece cover, and with the
  compatibility stated on every common refinement rather than on the intersection (which is what
  makes the two-piece arguments free of `inf`-commutativity bookkeeping).
- `deningerLocallyFiniteSum` — **a locally finite family of sections has a sum.**  The finite
  partial sums over the members of a cover on which the family is finitely supported agree on
  overlaps, so they glue; the sum restricts to the finite partial sum on *every* open set where the
  family is finitely supported, which is the form the argument actually consumes.
- `deningerSections_exact` and `deningerSections_injective` — sections are left exact, and a
  monomorphism of sheaves is injective on sections.  Both go through the corepresentation
  `Hom(deningerOpenFree U, F) ≃ Γ(U,F)`: a section corresponds to a map out of the free abelian
  sheaf, and `ShortComplex.Exact.lift` / `cancel_mono` do the rest.  This avoids having to prove
  that the sections functor preserves kernels.
- `deningerExtendByZero` — if `tsupport ρ ⊆ W`, then `ρ · t` extends by zero from `V ⊓ W` to `V`.
  The two pieces are `V ⊓ W` and `V ∖ tsupport ρ`; on the overlap the product vanishes by the
  support axiom of the fine action.  This is the only place the axiom is used, and it is the reason
  the axiom is stated as "vanishing on an open set where the function vanishes" rather than
  pointwise.

**The lifting theorem** `deningerFine_sections_surjective`: for a short exact sequence of sheaves
whose kernel is fine, global sections of the quotient lift.  Local lifts `s_i` over `V_i`,
differences `c_{ij} = s_i − s_j` in the kernel, a partition of unity `ρ_i` subordinate to `{V_i}`,
correction `E_i = ∑_j (ρ_j c_{ij})^0`, and `t_i = s_i − ι(E_i)`.  On an overlap, term by term,
`(ρ_k c_{ik})^0 − (ρ_k c_{jk})^0 = ρ_k c_{ij}` — checked on the two-piece cover `V_k` and off
`tsupport ρ_k` — and summing over the finitely many `k` alive near a point gives
`(∑_k ρ_k) c_{ij} = c_{ij}` because the partition sums to one there.  So the `t_i` glue.

**Acyclicity** then follows by induction on the degree through the Godement resolution: degree one
by the lifting theorem against the flasque `C⁰(F)`, and degree `n+2` by dimension shifting to degree
`n+1` of `C⁰(F)/F`, which is fine by `DeningerFineAction.godementQuotient`.

Only at `U = ⊤` — deliberately, since a partition of unity on an open subset need not extend to the
ambient space, and `deningerExt_eq_zero_of_shift` and `deningerExt_one_eq_zero_of_lift` consume
acyclicity at exactly the open set at which they conclude.  `DeningerAcyclic` was accordingly split
into the per-open `DeningerAcyclicOn`.

Axiom audit for every declaration: `propext, Classical.choice, Quot.sound`.

**What remains for `H^q(Z, O_Z) = 0`.**  Only the concrete instantiation: the sheaf of holomorphic
functions and the sheaves of smooth `(0,q)`-forms on `Z`, their fine structures (multiplication by
smooth functions, with smooth partitions of unity), the Dolbeault sequences as short exact sequences
of sheaves (surjectivity is the *local* `∂̄`-lemma, already proved), and the surjectivity of global
sections (the *global* `∂̄`-lemma, `setDbar_exact_global` / `setDbar_exact_punctured`, already
proved).  Both halves of Cartan B now exist; what is left is to connect them.

## The concrete Dolbeault sheaves, and why the multiplier had to become a parameter (2026-08-06)

**The multiplier refactor.**  `DeningerFineAction F` is now `DeningerFineAction F R` for
`R : AddSubgroup C(X, ℝ)` carrying `1`.  The reason is forced: multiplying a *smooth* form by a
merely continuous bump does not give a smooth form, so the sheaves of the Dolbeault resolution
cannot be modules over all of `C(X,ℝ)`.  Everything downstream carries `R`:
`DeningerFineAction.godement`, `deningerFineAction_of_epi`, `godementQuotient`,
`deningerExtendByZero`, the lifting theorem and the acyclicity theorem.

The partition-of-unity input is now the explicit predicate

  `DeningerHasPartitions R` — every pointwise-indexed open cover has a subordinate, locally finite
  family in `R` summing to one,

with `deningerHasPartitions_top` proving it for `R = ⊤` on a normal paracompact space from mathlib's
`PartitionOfUnity.exists_isSubordinate`.  The smooth case will instantiate the same predicate from
`SmoothPartitionOfUnity`.  This is strictly better than the previous form: the analytic input is
named, and the acyclicity theorem no longer carries topological typeclass assumptions of its own.

**The domain as a space.**  `RHTower/Deninger/DeningerDomainSpace.lean`.  An open `Ω ⊆ ℂ^n` becomes
`deningerSpace Ω`, so that `⊤` of that space is `Ω` itself — which is what the acyclicity theorem
needs, since a partition of unity on a proper open subset need not extend to the ambient space.
`deningerAmb U` is the ambient open set of an open set of the domain, and `deningerExtend f` is the
extension of a section by zero to all of `ℂ^n`.  Because `Ω` is open, the extension agrees with the
section near each of its points (`deningerExtend_eventuallyEq`), which is what makes every analytic
condition stated through it local and restriction-stable.

**The sheaves.**  `RHTower/Deninger/DeningerDolbeaultSheaf.lean`.

  `DeningerFormPred q f` : the coefficients vanish off the sets of `q` directions, and near every
  point the extension agrees with a **globally smooth** `SetForm` on `ℂ^n`.

Stating smoothness through a global model, rather than through local differentiability, is the
design decision that makes the entire corpus Dolbeault theory usable verbatim: `setDbar_smooth`,
`setDbar_add`, `setDbar_setDbar_eq_zero`, `setDbar_polydisc_solve` and `setDbar_exact_global` are
all statements about globally smooth forms, and `deningerSetDbar_model` says the differential of a
section is computed by any of its local models (by `setDbar_congr_of_eventuallyEq`).

`DeningerClosedFormPred q` adds the vanishing of that differential.  Both are local predicates
closed under the group operations, so `DeningerLocalGroupData` — the general gadget turning such a
predicate into a sheaf of abelian groups, built in `RHTower/Deninger/DeningerLocalSheaf.lean` on top of
mathlib's `subpresheafToTypes` — produces

  `deningerFormSheaf Ω q`       : smooth `(0,q)`-forms,
  `deningerClosedFormSheaf Ω q` : closed smooth `(0,q)`-forms; for `q = 0` the holomorphic functions.

Axiom audit: `propext, Classical.choice, Quot.sound`.

**What is left.**  The maps `deningerClosedFormSheaf Ω q ⟶ deningerFormSheaf Ω q` (inclusion) and
`deningerFormSheaf Ω q ⟶ deningerClosedFormSheaf Ω (q+1)` (the differential), short exactness of
each step — the epimorphism being the *local* `∂̄`-lemma — the fine action by smooth functions with
`DeningerHasPartitions` from `SmoothPartitionOfUnity`, and the surjectivity on global sections,
which is `setDbar_exact_global` / `setDbar_exact_punctured`.  Then
`deningerResolution_ext_eq_zero` gives `H^q(Ω, O) = 0`.

## The Dolbeault resolution is short exact (2026-08-06)

`RHTower/Deninger/DeningerDolbeaultSheaf.lean`.

**The maps.**  `deningerFormIncl Ω q : K^q ⟶ A^q` is the inclusion of the closed forms;
`deningerFormDbar Ω q : A^q ⟶ K^{q+1}` is `f ↦ ∂̄f`, computed on the ambient extension.  That the
target is the *closed* forms of degree `q+1` is `deningerDbarSection_pred`: the degree comes from
`setDbar_deg` applied to a local model, and the closedness from `setDbar_setDbar_eq_zero`.  Both
maps are well defined because `deningerSetDbar_model` computes the differential from any local
model, and models exist on explicit open neighbourhoods (`exists_model_open`).

**Exactness at the middle** is not proved by an abstract argument but by exhibiting the inclusion as
the kernel: `deningerFormStep_isKernel` builds, for any `k : T ⟶ A^q` with `k ≫ ∂̄ = 0`, the lift
`deningerKernelLift` into the closed forms, which is legitimate precisely because `k`'s sections are
killed by `∂̄`.  Then `ShortComplex.exact_of_f_is_kernel`.  This avoids needing that the sections
functor is exact or that exactness of sheaves is checked on stalks.

**The epimorphism is the local `∂̄`-lemma.**  `deningerFormDbar_locallySurjective`: given a closed
form of degree `q+1` over `U` and a point `x`, take a local model `g` on an open `N`, note that `g`
is closed on `N ∩ deningerAmb U` (again by `setDbar_congr_on_isOpen`), pick `ε` with
`ball c ε ⊆ N ∩ deningerAmb U` and observe `polydisc c ε ⊆ ball c ε` by `pi_norm_lt_iff`, and apply
`setDbar_polydisc_solve` on that polydisc.  The primitive `u` is *globally* smooth of degree `q`, so
it is its own model, and the section `y ↦ u · y` over the corresponding open set of the domain has
`∂̄ = h` there.  Hence `Epi` via `isLocallySurjective_iff_epi`, and

  `deningerFormStep_shortExact : (deningerFormStep Ω q).ShortExact`.

**Truncation.**  `HTGeometry/SmoothTruncation.lean`: `exists_contDiff_eventuallyEq` — a function
smooth on an open set agrees, near each of its points, with a globally smooth function.  Multiply by
a bump supported in a ball inside the open set and extend by zero; the ball and the complement of
the closed ball carrying the bump cover the space.  Checked against the corpus first: the existing
bump machinery is all *specific* cutoffs (`exists_annulus_cutoff`, `exists_polyannulus_cutoff`,
`exists_polydisc_bumps`, `cutoff_slab_support`, `SmoothWeight`) — none of them turns an arbitrary
germ into a global function, so this is new rather than a duplicate.  It is what will carry the
smooth partition of unity on the domain into the global-model form the sheaves are stated in.

Axiom audit for all of it: `propext, Classical.choice, Quot.sound`.

## The form sheaves are fine, and the exact route to the smooth partitions (2026-08-06)

`RHTower/Deninger/DeningerDolbeaultFine.lean`.

`DeningerSmoothMult Ω` is the subgroup of `C(deningerSpace Ω, ℝ)` of functions whose extension by
zero agrees, near every point of the domain, with a globally smooth function on `ℂ^n` — the same
"global model" device the form sheaves use, so the two match without any conversion.  It contains
`1` because the domain is open.  `deningerFormFineAction Ω q` is the multiplication
`(ρ · f)(y)(S) = ρ(y) f(y)(S)`; the model of the product is the product of the models, which is why
the multiplier subgroup had to be stated with global models rather than with local
differentiability.

**The remaining three items, with every ingredient verified to exist.**

1. `DeningerHasPartitions (DeningerSmoothMult Ω)`.  The route that works, and the one to take:
   refine the given cover `V x` to `W x ⊆ V x` with `closure (W x)` compact — then
   `SmoothPartitionOfUnity.exists_isSubordinate` on the manifold `↥Ω` (instances checked:
   `IsManifold` and `T2Space` are found; `SigmaCompactSpace ↥Ω` is
   `sigmaCompactSpace_of_locallyCompact_secondCountable` after `Ω.2.locallyCompactSpace`) produces
   members with `tsupport` inside a compact set, hence `HasCompactSupport`.  Then
   `ContMDiff.extend_zero` gives `ContMDiff` of the extension by zero **on `ℂ^n`**, and
   `contMDiff_iff_contDiff` turns that into `ContDiff ℝ ⊤` — a *global* model, which is exactly
   membership in `DeningerSmoothMult Ω`.  Note this route needs no truncation at all; the
   compact-support refinement replaces it.  `HTGeometry.exists_contDiff_eventuallyEq` remains as the
   general tool for germs that are not compactly supported.
2. Surjectivity of `Γ(⊤, A^q) → Γ(⊤, K^{q+1})`.  A global section of `K^{q+1}` over `⊤` has, at
   every point, a global smooth model; on `Ω = ℂ^n` or `(ℂ^×)^n` the whole section *is* a global
   `∂̄`-closed `SetForm` of degree `q+1`, and `setDbar_exact_global` / `setDbar_exact_punctured`
   produce the primitive, which is again a section because it is globally smooth.
3. `deningerResolution_ext_eq_zero` with `K i := deningerClosedFormSheaf Ω i`,
   `A i := deningerFormSheaf Ω i`, `ι i := deningerFormIncl Ω i`, `π i := deningerFormDbar Ω i`,
   `hSE := deningerFormStep_shortExact`, `hacy i := deningerFine_acyclicOn hpu
   (deningerFormFineAction Ω i)`, and `hlift` from item 2 — giving `H^{q+1}(Ω, O_Ω) = 0`, with
   `O_Ω = deningerClosedFormSheaf Ω 0`.

Axiom audit for everything landed: `propext, Classical.choice, Quot.sound`.

## Cartan's theorem B for `ℂ^n`, closed (2026-08-07)

  `RHTower.deningerHolomorphic_ext_eq_zero (q : ℕ)
     (x : deningerSheafCohomology ⊤ (deningerClosedFormSheaf ⊤ 0) (q + 1)) : x = 0`

unconditional, axioms `propext, Classical.choice, Quot.sound`.  `H^{q+1}(ℂ^n, O) = 0` in the
corpus's own sheaf cohomology `Ext(deningerOpenFree U, F, n)`, for every `q ≥ 0`.

The three inputs that closed it:

- **Smooth partitions of unity** — `deningerHasPartitions_smooth`.  Refine the given cover to
  relatively compact opens (`exists_compact_between` on a singleton, then take the interior; the
  closure is a closed subset of a compact set).  `SmoothPartitionOfUnity.exists_isSubordinate` on the
  manifold `↥Ω` then yields members with `tsupport` inside a compact set, so `HasCompactSupport`
  holds and `ContMDiff.extend_zero` gives smoothness of the extension by zero **on `ℂ^n`**, which
  `contMDiff_iff_contDiff` turns into `ContDiff ℝ ⊤` — a global model, i.e. membership in
  `DeningerSmoothMult Ω`.  `deningerExtendFun_eq_extend` identifies the corpus's extension with
  `Function.extend Subtype.val · 0`.  Instances needed and now supplied on `deningerSpace Ω`:
  `ChartedSpace`, `LocallyCompactSpace`, `IsManifold`, `SigmaCompactSpace` (the last via
  `sigmaCompactSpace_of_locallyCompact_secondCountable`); `deningerSpace` had to become an `abbrev`
  so instance search sees through it.
- **Global solvability on sections** — `deningerFormDbar_globalSurjective`.  Over `ℂ^n` every
  ambient point lies in the ambient open set of `⊤`, so a section that agrees with a smooth model
  near each point is `ContDiffAt` everywhere, hence `ContDiff` by `contDiff_iff_contDiffAt`: the
  section *is* a globally smooth `SetForm`.  `setDbar_exact_global` then produces the primitive,
  which is again a section because it is globally smooth.
- **The assembly** — `deningerResolution_ext_eq_zero` with the Dolbeault resolution, its
  short exactness, `deningerFine_acyclicOn` of the fine form sheaves, and the surjectivity above.

**The punctured case, and exactly what it needs.**  `(ℂ^×)^n` fails only at the second input:
`setDbar_exact_punctured` asks for a form smooth on all of `ℂ^n`, and the extension by zero of a
section on the punctured space is not smooth across the boundary.  The fix is local, not structural:
every stage of `puncturedExhaustion` is a polyannulus whose closure is compact inside the punctured
space, so it suffices to truncate.  Build

  `exists_smooth_setForm_eq_on` — for `K` compact inside an open `W` on which `F` is coefficientwise
  `ContDiffAt`, a globally smooth `G` agreeing with `F` on a neighbourhood of `K`,

from `exists_smooth_zero_one_of_isClosed` applied to `K` and the complement of the interior of a
compact neighbourhood of `K` in `W` (so `tsupport χ ⊆ W`), with the same two-open-cover smoothness
argument as `HTGeometry.exists_contDiff_eventuallyEq`.  Feeding the truncation into
`setDbar_polyannulus_solve` gives `DbarStageSolvable (puncturedExhaustion n)` for merely locally
smooth closed forms, and `setDbar_exhaustion_solve` then runs unchanged.

## Cartan's theorem B for `(ℂ^×)^n`, closed (2026-08-07)

  `RHTower.deningerHolomorphic_ext_eq_zero_punctured (q : ℕ)
     (x : deningerSheafCohomology ⊤ (deningerClosedFormSheaf (deningerPunctured n) 0) (q+1)) :
     x = 0`

unconditional, axioms `propext, Classical.choice, Quot.sound`.  This is the statement the Deninger
pro-Stein card consumes: the finite character stages are `(ℂ^×)^r`, and their structure sheaves —
and hence their finite free modules — have no higher cohomology.

**What had to be generalized, and why it was a local repair.**  The whole `∂̄` apparatus was written
for forms smooth on all of `ℂ^n`, but a section over the punctured space extends by zero only, and
that extension is not smooth across the boundary.  The fix is truncation, and it enters at exactly
three places:

- `HTGeometry.exists_contDiff_family_eqOn` — a family of functions smooth on an open set `W` is,
  after one cutoff equal to one near a compact `K ⊆ W` and supported in `W`, globally smooth and
  unchanged on an open neighbourhood of `K`; and the truncation kills whatever the family killed,
  which is what preserves the degree of a form.  Built from
  `exists_contMDiffMap_zero_one_of_isClosed` between `K` and the complement of a compact
  neighbourhood, with the same two-open-cover smoothness argument as
  `exists_contDiff_eventuallyEq`.
- `exists_dbar_punctured_sequence` (degree one, the Runge case) used global smoothness in exactly
  one place — the call to `dbar_polyannulus_solve` at each stage.  Truncating on the closed
  polyannulus of that stage replaces it, and `dbar_punctured_solve` now needs only `ContDiffAt` on
  the punctured space.
- `DbarStageSolvable` now carries the ambient set and takes `SmoothSetFormOn g X`;
  `dbarStageSolvable_puncturedExhaustion` truncates on `closedPolyannulus (1/(m+3)) (m+3)`, and
  `dbarStageSolvable_polydiscExhaustion` needs no truncation at all because
  `SmoothSetFormOn g univ` *is* `SmoothSetForm g` by `contDiff_iff_contDiffAt`.

So `setDbar_exact_punctured` now assumes only `SmoothSetFormOn f (puncturedSpace n)`, which is what
a sheaf section provides, and `deningerFormDbar_globalSurjective_punctured` follows; the primitive
is turned back into a section by taking a global model near each point with the same truncation
lemma applied to a singleton.

Both capstones are in place:

  `deningerHolomorphic_ext_eq_zero`           : `H^{q+1}(ℂ^n, O) = 0`
  `deningerHolomorphic_ext_eq_zero_punctured` : `H^{q+1}((ℂ^×)^n, O) = 0`

## The cell-induction step of `(7)` (2026-08-07)

Two more consequences of the covariant `Ext` sequence, in `RHTower/Deninger/DeningerAcyclicResolution.lean`,
are exactly what the pro-Stein card's induction over a finite relative cell filtration consumes:

- `deningerAcyclicOn_middle` — **acyclicity is two-out-of-three**: if the sub- and quotient sheaves
  of a short exact sequence are acyclic on an open set, so is the middle term.  A class of the
  middle term in degree `n+1` dies in the quotient, hence comes from the subsheaf, where it is zero.
- `deningerSections_surjective_of_acyclic` — **sections are exact when the subsheaf is acyclic**:
  the obstruction to lifting a section of the quotient is its connecting image in `H^1` of the
  subsheaf.  Proved through the corepresentation, with `deningerExt_addEquiv₀_mk₀` supplying the
  inverse of `mk₀` in degree zero.

Together with `deningerHolomorphic_ext_eq_zero_punctured` these give the card's step verbatim: a
subquotient of the semi-free filtration is acyclic for global sections, so the attachment of derived
sections is the attachment of sections, and the induction closes.
