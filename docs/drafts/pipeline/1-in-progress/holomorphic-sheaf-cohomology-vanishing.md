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

- `RHTower/DeningerFlasqueAcyclic.lean` — `deningerSheafCohomology U F n`, sheaf cohomology as the
  `Ext` out of the free abelian sheaf on an open set; `deningerSheafCohomologyZeroEquiv`, degree
  zero is sections; **`deningerFlasque_isZero_cohomology`, a flasque sheaf has no higher
  cohomology**.
- `RHTower/DeningerOpenFreeSheaf.lean` — the free abelian sheaf on an open set and its hom
  adjunction, the representing object of the above.
- `RHTower/DeningerSkyscraperAcyclic.lean`, `RHTower/DeningerRestrictedPrimeAcyclic.lean`,
  `RHTower/DeningerArakelovBoundarySheaf.lean` — worked instances of proving acyclicity in that
  framework, including through mathlib's site-level `Sheaf.H`.
- `RHTower/DeningerCechHomotopy.lean`, `DeningerCechGlue.lean`, `DeningerCechSplit.lean`, and
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
