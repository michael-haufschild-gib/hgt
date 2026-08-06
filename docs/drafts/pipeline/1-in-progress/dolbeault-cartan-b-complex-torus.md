# Cartan theorem B for the character stage $(\mathbb C^\times)^r$

- **ID:** `dolbeault-cartan-b-complex-torus`
- **Stage:** 1-in-progress
- **Type:** INFRASTRUCTURE (Lean) — named blocker of four Deninger cards
- **Statement:** $H^q\big((\mathbb C^\times)^r,\mathcal O\big)=0$ for $q\ge 1$.

## Why

Four stage-2 Deninger cards name Cartan theorem B on the finite character stage as their single
remaining gap:

- `deninger-pro-stein-cylinder-analytic-leaf` — `(7)`, the relative cell statement.  Its own record
  says: *"what is left is Cartan theorem B at the finite Stein stages … Concretely the statement
  needed is `H^q(Z, O_Z) = 0` for `q ≥ 1` on `Z = (ℂ^×)^r`, since the sheaves of the cell filtration
  are free there."*
- `deninger-pro-log-stein-kummer-residue-square` — the acyclicity/filtered passage `(12)`--`(14)`.
- `deninger-archimedean-kummer-homology-current-lift` — the pro-Stein direct image `(7)`.
- `deninger-derived-stratum-kummer-arithmetic-coefficient` — waits on the first of these.

`DeningerStageStein.lean` already proves the stage is Stein (holomorphically convex and separable).
What is missing is the cohomological consequence, and with it the whole $\bar\partial$ layer:
nothing in mathlib or in the corpus mentions $\bar\partial$.

## Route

The Dolbeault route, in five layers.  Each is a self-contained Lean deliverable.

### D1 — Cauchy–Pompeiu at the centre of a disc

For $h$ continuously $\mathbb R$-differentiable on a neighbourhood of $\overline{D(0,R)}$,
$$
 h(0)=\frac1{2\pi i}\oint_{|w|=R}\frac{h(w)}{w}\,dw-\frac1\pi\iint_{|w|<R}\frac{\bar\partial h(w)}{w}\,dA(w).
$$

**No two-dimensional Stokes theorem is needed.**  mathlib's divergence theorem is stated on boxes,
not discs, so the proof runs in polar coordinates instead.  With
$I(r)=\oint_{|w|=r}h(w)\,dw/w=i\int_0^{2\pi}h(re^{i\theta})\,d\theta$:

1. $\partial_\theta\big[h(re^{i\theta})\big]=ire^{i\theta}\partial h-ire^{-i\theta}\bar\partial h$
   integrates to zero over the full circle, so
   $\int_0^{2\pi}e^{i\theta}\partial h\,d\theta=\int_0^{2\pi}e^{-i\theta}\bar\partial h\,d\theta$;
2. $\partial_r\big[h(re^{i\theta})\big]=e^{i\theta}\partial h+e^{-i\theta}\bar\partial h$, so by 1,
   $I'(r)=2i\int_0^{2\pi}e^{-i\theta}\bar\partial h(re^{i\theta})\,d\theta$;
3. polar coordinates turn $\iint_{\varepsilon<|w|<R}\bar\partial h(w)\,dA(w)/w$ into
   $\int_\varepsilon^R\!\!\int_0^{2\pi}e^{-i\theta}\bar\partial h\,d\theta\,dr=(I(R)-I(\varepsilon))/2i$;
4. $I(\varepsilon)\to 2\pi i\,h(0)$ by continuity.

### D2 — the compactly supported $\bar\partial$ equation on $\mathbb C$

For $g$ of class $C^1$ with compact support, $u(z)=-\frac1\pi\iint g(z-w)\,dA(w)/w$ is $C^1$ and
$\bar\partial u=g$.  Differentiation under the integral sign is legitimate in that form because the
singularity does not move with $z$ and $1/w$ is locally integrable; the identity $\bar\partial u=g$
is D1 applied to $w\mapsto g(z-w)$.

### D3 — the $\bar\partial$-Poincaré lemma on a polydisc

$\bar\partial u=f$ solvable for every $\bar\partial$-closed $(0,q)$-form on a polydisc, by induction
on the number of variables in which $f$ involves $d\bar z_j$ (Hörmander 2.3.3), using D2 with a
cutoff and an exhaustion.

### D4 — the Dolbeault isomorphism

$H^q(X,\mathcal O)\cong H^q\big(\Gamma(X,\mathcal A^{0,\bullet}),\bar\partial\big)$, because the
sheaves of smooth $(0,q)$-forms are fine and D3 makes $\mathcal A^{0,\bullet}$ a resolution of
$\mathcal O$.  The corpus already owns the acyclicity half in the shape it needs:
`DeningerFlasqueAcyclic.lean` proves flasque sheaves have no higher cohomology and
`DeningerOpenFreeSheaf.lean` proves injective $\Rightarrow$ flasque.

### D5 — global solvability on $(\mathbb C^\times)^r$

Exhaust by compact polyannuli and approximate by Laurent polynomials.  In this case Runge
approximation is explicit: the Laurent expansion converges uniformly on compact polyannuli, so the
usual convergence-forcing correction is available without any general Runge theorem.

## Gates

- [x] D1a Wirtinger derivatives (`HTGeometry/WirtingerDerivative.lean`)
- [x] D1b angular and radial derivatives on a circle, and the equal-circle-integrals identity
      (`HTGeometry/CircleWirtinger.lean`)
- [x] D1c radial derivative of the circle mean (`HTGeometry/CauchyPompeiu.lean`)
- [x] D1d polar coordinates on an annulus, and the limit `ε → 0`
      *(mathlib has only the whole-plane change of variables `Complex.integral_comp_polarCoord_symm`;
      restrict it to the annulus with `Set.indicator` and iterate with Fubini, then use
      `Function.Periodic.intervalIntegral_eq` to move the angle from `(-π, π)` to `(0, 2π)`)*
- [x] D1 Cauchy–Pompeiu at the centre of a disc — `HTGeometry.cauchyPompeiu_center`
- [x] D2 compactly supported $\bar\partial$ equation on $\mathbb C$ — `HTGeometry.dzbar_dbarSolution`
- [x] D3a local solvability in one variable — `HTGeometry.exists_dbar_local`
- [x] D3b(i) the several-variable $(0,q)$ layer, `∂̄`, and `ker ∂̄ = 𝒪` in degree zero
- [x] D3b(ii-a) solving `∂̄_k U = G` in one coordinate with the others as parameters
- [x] D3b(ii-b) `∂̄_j` commutes with the coordinatewise Cauchy transform for `j ≠ k`
- [x] D3b(ii-c0) the `∂̄_j` calculus needed by the induction
- [x] D3b(ii-c1a) the full Fréchet derivative of the coordinatewise Cauchy transform
- [x] D3b(ii-c1b) smoothness by induction on the order (Banach-valued transform)
- [x] D3b(ii-c1c) `C^∞` preservation for both transforms
- [x] D3b(ii-c1d-i) slab far-field estimates
- [x] D3b(ii-c1d-ii) transform lemmas restated on slab hypotheses
- [x] D3b(ii-c2a) the induction *step*, packaged
- [x] D3b(ii-c2b-i) the polydisc layer: line-closure and the vanishing hypothesis
- [x] D3b(ii-c2b-ii) the cutoff on a polydisc, and the step in polydisc form
- [x] D3b(ii-c2b-iii-A) the assembly algebra of the recursion
- [x] D3b(ii-c2b-iii-B) `∂̄_i ∂̄_j = ∂̄_j ∂̄_i` for `C²` functions — `HTGeometry.dzbarAt_comm`
- [x] D3b(ii-c2b-iii-C-i) the moving-disc support of the Cauchy integrand
- [ ] D3b(ii-c2b-iii-C-ii) the two-piece split estimate
- [ ] D3b(ii-c2b-iii-D) the recursion itself
- [ ] D3 $\bar\partial$-Poincaré on a polydisc
- [x] D4a fine ⟹ Čech-acyclic, coefficients in a module (`HTGeometry/CechFineAcyclicModule.lean`)
- [ ] D4b instantiate at the sheaves of smooth `(0,q)`-forms
- [ ] D4 Dolbeault isomorphism
- [ ] D5 global solvability on $(\mathbb C^\times)^r$, hence $H^q=0$ for $q\ge1$
- [ ] feed back into the four Deninger cards

## Log

- 2026-08-06 — created; route fixed after confirming that mathlib has no $\bar\partial$ layer, that
  its divergence theorem is box-only, and that the polar-coordinate proof of D1 needs only
  one-dimensional calculus plus mathlib's polar-coordinate change of variables.

- 2026-08-06 — D1a and D1b landed unconditionally, axiom audit
  `propext, Classical.choice, Quot.sound` for every declaration, both modules wired into
  `GaloisForLFunctions.HTGeometry`.
  - `WirtingerDerivative.lean` — `wirtingerHol`, `wirtingerAntihol` and the decomposition
    `f' v = ∂ · v + ∂̄ · conj v` of a real-linear endomorphism of `ℂ`; `wirtingerAntihol_eq_zero_iff`
    identifying the vanishing of `∂̄` with complex linearity; the operators `dz`, `dzbar` on
    functions, with `dzbar_eq_zero_of_differentiableAt` giving the Cauchy–Riemann equations and
    `dz = deriv` on holomorphic functions; and `hasDerivAt_comp_wirtinger`, the derivative along a
    real curve.
  - `CircleWirtinger.lean` — continuity of `dz` and `dzbar` for a `C¹` function;
    `hasDerivAt_circle_angle` (`∂_θ = i(w ∂h − w̄ ∂̄h)`) and `hasDerivAt_circle_radius`
    (`∂_r = e^{iθ} ∂h + e^{-iθ} ∂̄h`); and `circle_angle_integral_eq`, the identity
    `∮ w ∂h = ∮ w̄ ∂̄h` obtained by integrating the angular derivative over a closed circle.  This
    is the step that replaces a two-dimensional Stokes theorem.

- 2026-08-06 — D1c landed unconditionally in `HTGeometry/CauchyPompeiu.lean`, axiom audit
  `propext, Classical.choice, Quot.sound`, wired into `GaloisForLFunctions.HTGeometry`.
  - `hasDerivAt_circleMean` — the circle mean is differentiable in the radius and its derivative is
    the integral of the radial derivative.  Differentiation under the integral sign uses
    `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`; the dominating bound is the
    supremum of `‖∂h‖ + ‖∂̄h‖` on the closed ball of radius `|r| + 1`, finite because `∂h` and `∂̄h`
    are continuous and the ball is compact, and it dominates because `|e^{iθ}| = 1`.
  - `hasDerivAt_circleMean_dzbar` — on a circle of nonzero radius only `∂̄` survives:
    `(d/dr) circleMean h r = 2 ∫₀^{2π} e^{-iθ} ∂̄h(r e^{iθ}) dθ`.  The `∂` term is removed by
    `circle_angle_integral_eq` after cancelling the common factor `r`.

- 2026-08-06 — **D1 closed.**  `HTGeometry/CauchyPompeiu.lean`, axiom audit
  `propext, Classical.choice, Quot.sound` for every declaration.
  - `lintegral_ball_norm_inv`, `integrableOn_norm_inv_ball`, `integrableOn_dzbar_div_ball` — **the
    Cauchy kernel is locally integrable in the plane**, proved by the polar change of variables:
    the area element cancels the singularity exactly, so the integral over a ball of radius `R` is
    at most `2πR`.  mathlib has no lemma of this shape.
  - `polarCoord_symm_eq_circleMap`, `setIntegral_annulus_dzbar_div` — the `∂̄` kernel over an
    annulus in polar coordinates, obtained from `Complex.integral_comp_polarCoord_symm` by
    restricting with an indicator; mathlib has only the whole-plane change of variables.
  - `setIntegral_annulus_eq_intervalIntegral` — Fubini turns it into an iterated interval integral.
  - `circleMean_sub_eq_annulus` — integrating the radial derivative of the circle mean from `ε` to
    `R` and rewriting gives `circleMean h R − circleMean h ε = 2 ∬_{ε<|w|<R} ∂̄h(w)/w dA`.
  - `iUnion_annulus`, `monotone_annulus`, `circleMean_zero`, `cauchyPompeiu_center` — the annuli
    increase to the punctured ball, the kernel is integrable there, so the limit `ε → 0` gives
    **Cauchy–Pompeiu at the centre**:
    `circleMean h R − 2π·h(0) = 2 ∬_{|w|<R} ∂̄h(w)/w dA(w)`.

- 2026-08-06 — **D2 closed.**  `HTGeometry/DbarSolve.lean`, axiom audit
  `propext, Classical.choice, Quot.sound` for every declaration.
  - `wirtingerAntiholL` — `∂̄` of a real-linear map as a *continuous linear functional*, which is
    what lets it be moved through a Bochner integral of operators.
  - `exists_radius_of_hasCompactSupport` — a radius outside which both `g` and `fderiv ℝ g` vanish.
  - `hasFDerivAt_cauchyIntegral` — **differentiation of the Cauchy transform under the integral
    sign**, via `hasFDerivAt_integral_of_dominated_of_fderiv_le`: the singularity does not move
    with `z`, the derivative of the integrand is bounded by `M‖w‖⁻¹` on a fixed ball and vanishes
    off it, and that bound is integrable by `integrableOn_norm_inv_ball`.
  - `integrable_fderivKernel` — the same bound gives integrability of the derivative kernel.
  - `integral_dzbar_kernel` — **Cauchy–Pompeiu for a compactly supported source**:
    `∫_ℂ ∂̄g(z−w)/w dA(w) = π·g(z)`.  Applying `cauchyPompeiu_center` to `t ↦ g(z−t)` on a disc
    containing the translated support kills the boundary circle mean, and
    `dzbar_comp_const_sub` (new, in `WirtingerDerivative.lean`, with `wirtinger_ext` and
    `hasFDerivAt_comp_const_sub`) supplies the sign.
  - `dbarSolution`, `dzbar_dbarSolution` — **`∂̄u = g`** for `u(z) = (1/π)∫ g(z−w)/w dA(w)`.

- 2026-08-06 — **D3a closed.**  `HTGeometry.exists_dbar_local` : for `C¹` `f` and any centre `z₀`
  and radius `r > 0` there is `u` with `∂̄u = f` on `closedBall z₀ r`.  Cutting off by a
  `ContDiffBump` reduces to `dzbar_dbarSolution`.  Axiom audit
  `propext, Classical.choice, Quot.sound`.

### D3b — design for the several-variable layer

The remaining half of D3 is the Dolbeault–Grothendieck lemma in `n` variables.  Design fixed here
so the build can continue across sessions:

* **Encoding.**  A smooth `(0,q)`-form on an open `Ω ⊆ (Fin n → ℂ)` is a coefficient family
  `f : (Fin q → Fin n) → (Fin n → ℂ) → ℂ` alternating in the index tuple.  This keeps `∂̄` a finite
  signed sum and avoids building a bundle-valued exterior algebra.
* **The operator.**  `(∂̄f)_{j₀…j_q}(z) = Σ_k (-1)^k ∂̄_{j_k} f_{j₀…ĵ_k…j_q}(z)`, where `∂̄_j` is
  `dzbar` in the `j`-th coordinate with the others frozen — the one-variable operator already built
  in `WirtingerDerivative.lean`, precomposed with `Function.update`.
* **`∂̄ ∘ ∂̄ = 0`** from equality of mixed partials (`ContDiff` symmetry of the second derivative).
* **The induction (Hörmander 2.3.3).**  Induct on the largest `k` with `f` involving `dz̄_k`.  At
  each step solve a one-variable `∂̄` problem in `z_k` with the other coordinates as parameters,
  using `dbarSolution` applied slicewise.  The two facts needed beyond D2 are that the Cauchy
  transform of a smooth compactly supported family is smooth in the parameters, and that it is
  holomorphic in any parameter in which the source is holomorphic — both are
  differentiation-under-the-integral arguments of the same shape as
  `hasFDerivAt_cauchyIntegral`, with the same dominating bound.

### D4 — corpus audit (2026-08-06): most of this already exists

A search of the tree before building any more turned up the following, all of it reusable and none
of it to be rebuilt:

| Asset | Module | Bearing |
|---|---|---|
| **fine ⟹ Čech-acyclic in every degree**, by the partition-of-unity contracting homotopy `δK + Kδ = id` | `RHTower/DeningerCechHomotopy.lean` (`deningerCechK`, `deningerCech_homotopy`, `deningerCech_exact`) | this *is* the D4 bridge |
| Čech degree zero = global sections (compatible families glue, uniquely) | `RHTower/DeningerCechGlue.lean` | the `H⁰` half |
| first Čech cohomology splits for a fine cover | `RHTower/DeningerCechSplit.lean` | the `q = 1` instance |
| Ext-based sheaf cohomology, `flasque ⟹ acyclic`, `injective ⟹ flasque`, free abelian sheaf on an open | `RHTower/DeningerFlasqueAcyclic.lean`, `DeningerOpenFreeSheaf.lean`, `DeningerSkyscraperAcyclic.lean`, `DeningerRestrictedPrimeAcyclic.lean` | the derived-functor side |
| CDGA, its cohomology, morphisms, quasi-isomorphisms; filtered colimits of CDGAs; cohomology commutes with them | `HTGeometry/CDGA.lean`, `CDGAColimit.lean`, `CDGAColimitQuasiIso.lean` | the algebra of `(7)` on the pro-Stein card |
| relative Sullivan stages and towers over an arbitrary directed order, `cohomology_computed_at_stages` | `HTGeometry/GradedSullivan{Stage,Tower,Graded,Augmented}.lean` | the "relative Sullivan algebra as a filtered union of finite cell stages" of `(7)` |

So D4 does **not** have to be built from scratch.  `deningerCech_exact` is exactly "a fine sheaf is
acyclic", proved in every degree by multiplying by a partition of unity.  Its only limitation is
that `DeningerCechCochain X ι q` is `ℝ`-valued; the proof uses nothing but scalar multiplication and
finite sums, so generalizing the target to an arbitrary `ℝ`-module — which is what the sheaves of
smooth `(0,q)`-forms are — is mechanical and is the next step.

There is **no** operad, `E_∞`, spectra, motivic-cohomology or cotangent-complex material anywhere in
the tree; those four cards genuinely need new area-scale theories, and the audit confirms it.

### D4 — the remaining bridge, in its corrected form

Turning local `∂̄`-exactness into `H^q(Z, 𝒪) = 0` needs the sheaves of smooth `(0,q)`-forms to be
acyclic.  The corpus already owns an Ext-based sheaf cohomology (`DeningerFlasqueAcyclic.lean`,
with `flasque ⟹ acyclic` and `injective ⟹ flasque` from `DeningerOpenFreeSheaf.lean`), so what is
missing is *soft ⟹ acyclic* for sheaves of modules over the sheaf of smooth functions, i.e. the
partition-of-unity argument.  mathlib has smooth partitions of unity
(`SmoothPartitionOfUnity`) but no softness theory; that theorem is the next area-sized target after
D3b.

- 2026-08-06 — **D3b(i) landed.**  `HTGeometry/DbarSeveral.lean`, axiom audit
  `propext, Classical.choice, Quot.sound` for every declaration.
  - `dbarSlice`, `dzbarAt`, `dzAt` — the coordinate slices and their one-variable Wirtinger
    derivatives; `DbarForm`, `dbarOp` — `(0,q)`-forms as alternating coefficient families and the
    Dolbeault operator as the signed sum `Σ_k (-1)^k ∂̄_{j_k}`.
  - `map_smul_of_map_I` — a real-linear functional on a complex space is complex linear as soon as
    it commutes with multiplication by `i`, proved from `c • x = c.re • x + c.im • (i • x)`.
  - `hasFDerivAt_updateEmbed`, `hasFDerivAt_dbarSlice` — the coordinate embedding is affine with
    derivative `Pi.single j`, so the slice differential is the full differential along the
    coordinate line.
  - `map_I_single`, `map_I_of_dzbarAt_eq_zero` — **the several-variable Cauchy–Riemann equations**:
    vanishing of every `∂̄_j` makes the real differential commute with `i`, first in each coordinate
    direction and then, by the `Pi.single` decomposition, on all of `ℂⁿ`.
  - `differentiable_complex_of_dzbarAt_eq_zero`, `analyticOnNhd_of_dzbarAt_eq_zero` — hence
    **`ker ∂̄ = 𝒪`**: `∂̄F = 0` makes `F` holomorphic, and analytic through the corpus's
    `PolydiscAnalytic.analyticOnNhd_of_differentiable`.  This is the degree-zero exactness of the
    Dolbeault resolution.

- 2026-08-06 — **D3b(ii-a) landed** in `HTGeometry/DbarSeveral.lean`, audit
  `propext, Classical.choice, Quot.sound`.
  - `dbarSliceSolution` — the coordinatewise Cauchy transform, solving the one-variable equation in
    the `k`-th coordinate with the others as parameters.
  - `dbarSlice_dbarSliceSolution`, `dzbarAt_dbarSliceSolution`,
    `dzbarAt_dbarSliceSolution_of_compactSupport` — **`∂̄_k U = G`**.  The parameters do not move
    under the slice, so this is `dzbar_dbarSolution` applied fibrewise; the slice hypotheses are
    discharged from `HasCompactSupport G` by `contDiff_updateEmbed` and
    `hasCompactSupport_slice` (which uses `‖t‖ ≤ ‖update z k t‖`).
  - `dbarSliceSolution_eq_integral` — **the transform is a convolution along a coordinate line**,
    `U(y) = (1/π) ∫ G(y − e_k w)/w dA(w)`.  This is the form in which the singularity no longer
    moves with the parameter, so differentiation under the integral is available in *every*
    direction, not only the `k`-th.
  - `norm_pi_single`, `exists_radius_pi` — the two supporting facts for that differentiation.

  **The blocker on D3b(ii-b) is elaboration cost, not mathematics.**  The proof of
  `HasFDerivAt (fun y => ∫ w, G (y − e_k w)/w) (∫ w, w⁻¹ • fderiv ℝ G (y₀ − e_k w)) y₀` is the exact
  analogue of `hasFDerivAt_cauchyIntegral` (which is proved, for `H = ℂ`), with the same dominating
  bound `M‖w‖⁻¹·1_{ball}` and the same three side conditions; every hypothesis was written and
  type-checked individually, but `hasFDerivAt_integral_of_dominated_of_fderiv_le` with
  `H = (Fin n → ℂ)` exceeds 4·10⁶ heartbeats at `whnf` even with all implicits pinned.  Next
  attempt: replace the `Pi` type by a `ContinuousLinearEquiv`-transported model with cheaper
  instances, or prove the `HasFDerivAt` by hand from `hasFDerivAt_cauchyIntegral` composed with the
  coordinate embedding, which keeps `H = ℂ` throughout and moves the several-variable dependence
  into a plain composition.

- 2026-08-06 — **D3b(ii-b) closed**, and the elaboration blocker is gone.  The fix was the route
  recorded above: keep `H = ℂ` throughout by differentiating the *slice* of the transform rather
  than the transform itself, so `hasFDerivAt_integral_of_dominated_of_fderiv_le` is applied with a
  one-dimensional parameter space, exactly as in `hasFDerivAt_cauchyIntegral`.  Axiom audit
  `propext, Classical.choice, Quot.sound` for every declaration.
  - `opNorm_single_le`, `norm_coord_le`, `hasFDerivAt_updateSlice`,
    `dzbarAt_eq_wirtingerAntihol` — the coordinate inclusion has operator norm at most one, the
    slice derivative is the full differential composed with it, and `∂̄_j` is the antiholomorphic
    Wirtinger part of that composite.
  - `hasFDerivAt_sliceSolution_along` — **differentiation under the integral sign along a
    coordinate `j ≠ k`**.  The dominating bound is again `M‖w‖⁻¹` on a fixed ball, finite by
    `integrableOn_norm_inv_ball`, and the far-field vanishing uses that the `k`-th coordinate of
    the integration point is `y_k − w`, whose norm grows with `‖w‖`.
  - `integrable_sliceFderivKernel` — the same bound gives integrability of the derivative kernel.
  - `dzbarAt_dbarSliceSolution_of_ne` — **`∂̄_j U = T_k(∂̄_j G)` for `j ≠ k`**, where `T_k` is the
    coordinatewise Cauchy transform.  Together with `dzbarAt_dbarSliceSolution_of_compactSupport`
    (`∂̄_k U = G`) these are the two facts the Dolbeault–Grothendieck induction runs on: solving in
    one direction fixes that direction and transports the others without introducing new ones.

- 2026-08-06 — **D3b(ii-c0) landed**: the `∂̄_j` calculus the induction runs on, audit
  `propext, Classical.choice, Quot.sound`.
  - `dzbarFunctional`, `dzbarFunctional_apply`, `dzbarAt_eq_functional` — `∂̄_j` is a *continuous
    linear functional* applied to the differential, `∂̄_j G = Λ_j (fderiv ℝ G)`.  Everything below
    follows from that one identification.
  - `contDiff_dzbarAt` — **`∂̄_j` loses exactly one degree of smoothness**,
    `ContDiff ℝ (m+1) G → ContDiff ℝ m (∂̄_j G)`, via `ContDiff.fderiv_right`.
  - `dzbarAt_add` — additivity.
  - `hasCompactSupport_dzbarAt` — `∂̄_j` preserves compact support, via
    `HasCompactSupport.fderiv` and `comp_left`.

### The one remaining input for the induction

The Hörmander induction on the highest `dz̄` direction is now fully set up: `∂̄_k T_k(f_k) = f_k`
and `∂̄_j T_k(f_k) = T_k(∂̄_j f_k) = T_k(∂̄_k f_j)` (using `∂̄`-closedness), so
`g_j := f_j − ∂̄_j T_k(f_k)` vanishes in direction `k` and in every direction above it, and the
induction hypothesis applies to `g`.

What is still needed is that `g` inherits the *smoothness* hypothesis, i.e. that the coordinatewise
Cauchy transform `T_k` of a `C^∞` compactly supported function is again `C^∞`.  Each single
derivative is already available — `hasFDerivAt_cauchyIntegral` in the `k`-th direction and
`hasFDerivAt_sliceSolution_along` in the others, both with the dominating bound `M‖w‖⁻¹·1_{ball}` —
so the missing step is the *iteration*.  The clean mechanism, fixed here:

* generalize `dbarSolution`, `hasFDerivAt_cauchyIntegral` and `hasFDerivAt_sliceSolution_along`
  from a `ℂ`-valued source to a Banach-space-valued one (`E` normed over `ℝ`, complete).  Every
  proof carries over unchanged: the bound is `M‖w‖⁻¹·1_{ball}`, the integrability comes from
  `integrableOn_norm_inv_ball`, and nothing uses multiplicativity of the target;
* then `fderiv ℝ (T_k G) = T_k^{E}(fderiv ℝ G)` with `E = (Fin n → ℂ) →L[ℝ] ℂ`, because the
  derivative of the integrand is `w⁻¹ • fderiv ℝ G (y − e_k w)`, which is exactly the integrand of
  the `E`-valued transform applied to `fderiv ℝ G`;
* induct on the order with `contDiff_succ_iff_fderiv`: `ContDiff ℝ (m+1) G` gives
  `ContDiff ℝ m (fderiv ℝ G)` with compact support, hence `ContDiff ℝ m (T_k^E (fderiv ℝ G))` by
  the inductive hypothesis, hence `ContDiff ℝ (m+1) (T_k G)`.

With that in place the Hörmander induction closes and D3 is complete.

- 2026-08-06 — **D3b(ii-c1a) closed, and the earlier elaboration blow-up is fully diagnosed and
  fixed.**  `hasFDerivAt_piCauchyIntegral` gives the *full Fréchet* derivative of the coordinatewise
  Cauchy transform on `(Fin n → ℂ)`:

  `d/dy ∫ G(y − e_k w)/w dA(w) = ∫ w⁻¹ • fderiv ℝ G (y − e_k w) dA(w)`.

  The earlier attempt at exactly this statement exceeded 4·10⁶ heartbeats at `whnf`; the fix was to
  hoist *every* side condition out of the tactic block into its own top-level lemma
  (`pi_far_norm`, `pi_continuous_arg`, `pi_measF`, `pi_measF'`, `pi_boundInt`, `pi_Fint`,
  `pi_bound`, `pi_diff`), leaving the main proof a single application of
  `hasFDerivAt_integral_of_dominated_of_fderiv_le`.  With the side conditions elaborated separately
  the whole thing goes through.  Axiom audit `propext, Classical.choice, Quot.sound` throughout.

  This is precisely the identity the smoothness induction needs: it exhibits `fderiv ℝ (T_k G)` as
  the *same* transform applied to `fderiv ℝ G`, so once the transform is generalized to a Banach
  target the induction `ContDiff ℝ (m+1) G → ContDiff ℝ (m+1) (T_k G)` closes by
  `contDiff_succ_iff_fderiv`.

- 2026-08-06 — **D3b(ii-c1 closed: the coordinatewise Cauchy transform preserves smoothness.**
  Axiom audit `propext, Classical.choice, Quot.sound` throughout.
  - `piCauchyB` — the transform for a Banach-valued source,
    `T_k G (y) = ∫ w⁻¹ • G(y − e_k w) dA(w)`.  Generalizing the target costs nothing: the
    dominating bound `M‖w‖⁻¹·1_{ball}` and `integrableOn_norm_inv_ball` never use multiplicativity.
  - `piB_measF`, `piB_Fint`, `piB_bound`, `piB_diff` — the four side conditions, hoisted, exactly
    as in the scalar case.
  - `continuous_piCauchyB` — continuity, by `MeasureTheory.continuousAt_of_dominated` with the
    bound taken on a unit ball around each point (the radius grows with the base point, so the
    domination has to be local; that is why the statement is proved through `ContinuousAt`).
  - `hasFDerivAt_piCauchyB` — **`fderiv ℝ (T_k G) = T_k (fderiv ℝ G)`**: the differential of the
    transform is the transform of the differential.
  - `contDiff_piCauchyB` — **`ContDiff ℝ m G` and compact support give `ContDiff ℝ m (T_k G)`**, by
    induction on `m` through `contDiff_succ_iff_fderiv`, the inductive step being applied to the
    `((Fin n → ℂ) →L[ℝ] F)`-valued transform.  This is the input the Hörmander induction was
    waiting on.

- 2026-08-06 — **D3b(ii-c1c) landed**: `contDiff_infty_piCauchyB`,
  `dbarSliceSolution_eq_piCauchyB`, `contDiff_infty_dbarSliceSolution` — both transforms preserve
  `C^∞`, the scalar one being `π⁻¹` times the Banach-valued one.  Axiom audit
  `propext, Classical.choice, Quot.sound`.

### Correction to the D3b(ii-c2) design

An earlier note here described the induction as if the cut-off source stayed `∂̄`-closed.  It does
not, and that has to be handled explicitly:

* the transform `T_k` needs a *compactly supported* source, so `f_k` must be cut off by a bump `χ`
  before `T_k` is applied;
* `∂̄_j(χ f_k) = χ ∂̄_j f_k + (∂̄_j χ) f_k`, and the second term does not vanish, so
  `∂̄_j T_k(χ f_k) = T_k(∂̄_j(χ f_k))` is *not* zero for `j > k` on all of `ℂⁿ`;
* what is true, and what the induction must carry, is that the identity holds **on the smaller
  ball where `χ ≡ 1`**: there `∂̄_j(χ f_k) = ∂̄_j f_k = ∂̄_k f_j = 0` for `j > k`.

So the induction statement has to be *local*, of the shape

> for every `m`, every open `Ω`, every smooth `f` with `∂̄_i f_j = ∂̄_j f_i` on `Ω` and `f_j = 0` on
> `Ω` for `j ≥ m`, and every `p ∈ Ω`, there are a neighbourhood `V ⊆ Ω` of `p` and a smooth `u`
> with `∂̄_j u = f_j` on `V` for every `j`,

with each induction step shrinking `V`.  Finitely many steps, so the shrinking terminates.  Every
analytic ingredient for this is now in place — `dzbarAt_dbarSliceSolution_of_compactSupport`,
`dzbarAt_dbarSliceSolution_of_ne`, `contDiff_infty_dbarSliceSolution`, `contDiff_dzbarAt`,
`dzbarAt_add`, `hasCompactSupport_dzbarAt`, and `ContDiffBump` for the cutoffs — what remains is the
bookkeeping of the shrinking neighbourhoods and the index induction.

### Second correction to D3b(ii-c2): the cutoff must be in the `k`-th variable alone

The shrinking-domain reading recorded above is *not* how Hörmander's induction actually works, and
the difference matters for the Lean hypotheses.  The problem with a bump `χ(z)` in all variables is
that `∂̄_j(χ f_k) = χ ∂̄_j f_k + (∂̄_j χ) f_k`, and `T_k` integrates over the whole `k`-th line, so
it sees the region where `∂̄_j χ ≠ 0` no matter how small the target neighbourhood is.  The
`j > k` directions are then not killed and the induction does not descend.

The resolution is that **the cutoff is a function of the `k`-th coordinate only**, `χ(z) = χ₀(z_k)`.
Then `∂̄_j χ = 0` for every `j ≠ k`, so

* `∂̄_k T_k(χ f_k) = χ f_k = f_k` on the slab where `χ₀ ≡ 1`, and
* `∂̄_j T_k(χ f_k) = T_k(χ ∂̄_j f_k) = 0` for `j > k`, exactly as required,

and no shrinking of the *other* coordinates is needed at all.

The cost is that `χ f_k` is **not compactly supported** — it is supported in a slab
`{z | z_k ∈ K}` with `K ⊂ ℂ` compact, unbounded in the other coordinates.  So the transform layer
has to be restated with

* `∃ S, ∀ z, S < ‖z k‖ → G z = 0` (slab support in the `k`-th coordinate),
* `∀ z, ‖G z‖ ≤ M₀` and `∀ z, ‖fderiv ℝ G z‖ ≤ M` (global bounds),

in place of `HasCompactSupport G`.  Every existing proof survives this change essentially
unchanged, and in fact becomes slightly simpler: the far-field estimate already only ever used the
`k`-th coordinate, since `(y − e_k w)_k = y_k − w`, so `pi_far_norm` becomes a statement about
`‖y_k − w‖` and no longer needs to control `‖y‖`.  `dzbarAt_dbarSliceSolution` was already stated
slicewise and needs no change; it is `hasFDerivAt_sliceSolution_along`,
`hasFDerivAt_piCauchyIntegral`, `integrable_sliceFderivKernel`, `piB_*` and `contDiff_piCauchyB`
that take the new hypotheses.

That refactor is the next step; after it the induction has no remaining obstruction.

- 2026-08-06 — **D3b(ii-c1d-i) landed**, axiom audit `propext, Classical.choice, Quot.sound`.
  - `slab_of_compactSupport` — compact support implies slab support in every coordinate, since
    `‖x k‖ ≤ ‖x‖`.  So the slab hypothesis is *weaker* than the one the current lemmas carry, and
    restating them on it is a strict generalization that keeps every existing caller working.
  - `slab_far_norm` — the far-field estimate for the full transform, now depending only on
    `‖y₀ k‖` rather than `‖y₀‖`, because `(y − e_k w)_k = y_k − w` and no other coordinate moves.
  - `slab_far_slice` — the same for the `j ≠ k` slice, where the `k`-th coordinate of the
    integration point is `y_k − w` whatever the `j`-th parameter does.

  These are the two estimates every remaining hypothesis of the transform layer rests on; with them
  in slab form, restating `hasFDerivAt_sliceSolution_along`, `integrable_sliceFderivKernel`,
  `hasFDerivAt_piCauchyIntegral`, the `piB_*` family and `contDiff_piCauchyB` is mechanical
  substitution of `‖·‖` by `‖· k‖` in the vanishing hypothesis and of `‖y₀‖` by `‖y₀ k‖` in the
  ball radius.

- 2026-08-06 — **D4a landed, by generalizing existing corpus work rather than rebuilding it.**
  `HTGeometry/CechFineAcyclicModule.lean`, axiom audit `propext, Classical.choice, Quot.sound`.
  `RHTower/DeningerCechHomotopy` already had the partition-of-unity contracting homotopy for
  *real-valued* Čech cochains; its proof uses only scalar multiplication and finite sums, so it is
  carried out here for cochains valued in an arbitrary real module — the generality the sheaves of
  smooth `(0,q)`-forms need.
  - `CechCochain`, `cechExtendZero`, `cechExtendZero_apply` — module-valued cochains and extension
    by zero, via `Set.indicator` so no decidability hypothesis is needed.
  - `cechD`, `cechK` — the differential and the averaging homotopy.
  - `cechD_cons`, `cechFace_zero`, `cechFace_succ` — the simplicial identities.
  - `cech_homotopy` — **`δK + Kδ = id` in every degree**.
  - `cech_exact` — **every cocycle is a coboundary**: a fine coefficient has no higher Čech
    cohomology.

- 2026-08-06 — **D3b(ii-c1d closed: the transform layer now runs on slab hypotheses**, which is what
  the Dolbeault induction actually supplies.  Done by *refactoring* the existing proofs rather than
  duplicating them: the compact-support hypothesis was only ever used to extract `S, M, M₀` and the
  far-field vanishing, and the far-field argument already went through the `k`-th coordinate alone.
  Axiom audit `propext, Classical.choice, Quot.sound`.
  - `hasCompactSupport_slice_of_slab` — slab support gives compactly supported slices in the `k`-th
    coordinate, uniformly in the others.
  - `dzbarAt_dbarSliceSolution_of_slab` — **`∂̄_k T_k(G) = G`** for a slab-supported source.
  - `hasFDerivAt_sliceSolution_along_slab`, `integrable_sliceFderivKernel_slab` — the `j ≠ k`
    derivative and its kernel integrability, on slab hypotheses `∀ x, S < ‖x k‖ → G x = 0` (and the
    same for `fderiv`) plus global bounds.
  - `dzbarAt_dbarSliceSolution_of_ne` — **`∂̄_j T_k(G) = T_k(∂̄_j G)` for `j ≠ k`**, now on slab
    hypotheses.

  With the cutoff `χ(z) = χ₀(z_k)` a function of the `k`-th coordinate alone, `χ · f_k` satisfies
  exactly these hypotheses, and `∂̄_j χ = 0` for `j ≠ k` makes `∂̄_j(χ f_k) = χ ∂̄_j f_k`, so the
  `j > k` directions are killed.  The induction has no analytic obstruction left; what remains is
  its index bookkeeping.

- 2026-08-06 — **The cutoff lemma, and the final form of the induction's domain hypothesis.**
  Landed (audit `propext, Classical.choice, Quot.sound`):
  - `dzbar_const_smul` — `∂̄` is homogeneous under a constant real scalar, including the
    non-differentiable case, where both sides are zero.
  - `dzbarAt_slabCutoff_smul` — **a cutoff in the `k`-th coordinate alone commutes with `∂̄_j` for
    `j ≠ k`**: `∂̄_j(χ(z_k)·f) = χ(z_k)·∂̄_j f`.  This is exactly why the induction cuts off in one
    variable, and it is now a theorem rather than a remark.

  **Third and final correction to the domain hypothesis.**  Neither "shrink the neighbourhood" nor
  "cut off in all variables" is right; both were recorded above and both fail, for the same reason:
  `T_k` is *nonlocal along the `k`-th coordinate line*, so to conclude `∂̄_j T_k(f_k) = 0` one needs
  `∂̄_j f_k = 0` on the whole `k`-line through the target point, not merely near it.  Hörmander's
  hypothesis supplies exactly that, and it is a hypothesis about the *shape of the domain*: on a
  **polydisc** `D = ∏ ball(c_i, r_i)`, moving the `k`-th coordinate keeps the point in `D`, and
  `∂̄`-closedness together with `f` not involving `dz̄_{k+1},…,dz̄_n` makes the coefficients of the
  `dz̄_k` part *holomorphic in `z_{k+1},…,z_n` on all of `D`*.  Then with `χ = χ(z_k)` supported in
  `ball(c_k, r_k)`:

  * `∂̄_k T_k(χ f_k) = χ f_k = f_k` where `χ ≡ 1`, and
  * `∂̄_j T_k(χ f_k) = T_k(χ ∂̄_j f_k) = 0` for `j > k`, because the integrand samples `f_k` only at
    points of `D` — the other coordinates never move — where `∂̄_j f_k` vanishes identically.

  So the Lean statement of the induction must be relative to a polydisc and use `ContDiffOn`, with
  the transform integrating over the `k`-disc.  Every analytic ingredient is in place; this is the
  shape the remaining bookkeeping has to take, and the two earlier readings recorded above are
  superseded.

- 2026-08-06 — **D3b(ii-c2a) landed: the induction step is now a single theorem.**  Axiom audit
  `propext, Classical.choice, Quot.sound`.
  - `dzbarAt_dbarSliceSolution_eq_zero` — **vanishing along the `k`-th coordinate line kills the
    transported derivative**: `∂̄_j T_k(F) (z) = 0` as soon as `∂̄_j F` vanishes on the whole `k`-line
    through `z`.  This is the exact mechanism identified in the domain-hypothesis correction: `T_k`
    is nonlocal only along that line, and the other coordinates never move under the integral.
  - `dbar_induction_step` — the step, packaged as
    `∃ U, (∀ z, ∂̄_k U z = F z) ∧ ∀ j ≠ k, ∀ z, (∂̄_j F vanishes on the k-line through z) → ∂̄_j U z = 0`.
    The first clause removes direction `k`; the second says no direction above `k` is created.
    On a polydisc, `∂̄`-closedness supplies the hypothesis of the second clause, since moving the
    `k`-th coordinate keeps the point in the domain.

  What is left of D3 is to iterate this step down the directions and assemble `u`, which is
  bookkeeping over `Fin n` with no further analytic content.

- 2026-08-06 — **D3b(ii-c2b-i) landed: the polydisc layer.**  Axiom audit
  `propext, Classical.choice, Quot.sound`.
  - `polydisc`, `mem_polydisc_iff` — the product of coordinate discs.
  - `update_mem_polydisc` — **a polydisc is closed under moving one coordinate inside its own
    disc**.  This is the geometric property the whole induction rests on, and it is why the domain
    must be a product: the `k`-line through a point of the polydisc, cut down to the `k`-th disc,
    stays inside.
  - `dzbarAt_eq_zero_of_eventually_zero` — a function vanishing near a point has vanishing `∂̄_j`
    there.
  - `dzbarAt_vanishes_on_line` — **on a polydisc, `∂̄`-closedness plus `f_j ≡ 0` makes `∂̄_j f_k`
    vanish on the whole `k`-line through any point of the polydisc**.  This is exactly the
    hypothesis `dzbarAt_dbarSliceSolution_eq_zero` consumes, so the step and the geometry now meet.

  Remaining for D3: multiply by a cutoff `χ(z_k)` supported in the `k`-th disc to make the source
  slab-supported (`dzbarAt_slabCutoff_smul` already shows `∂̄_j` passes through it for `j ≠ k`), then
  iterate the step down the directions.

- 2026-08-06 — **D3b(ii-c2b-ii) landed: the induction step now takes polydisc data directly.**
  Axiom audit `propext, Classical.choice, Quot.sound`.
  - `isOpen_polydisc` — a polydisc is open.
  - `cutoff_slab_support` — a cutoff in the `k`-th coordinate makes any source slab supported.
  - `dzbarAt_cutoff_vanishes_on_line` — **the cut-off source is `∂̄_j`-closed along the whole
    `k`-line**: off the support of the cutoff the product vanishes, and on it the point stays inside
    the polydisc, where `∂̄`-closedness applies.  This discharges the hypothesis of
    `dzbarAt_dbarSliceSolution_eq_zero` from polydisc data, which is the join between the analytic
    step and the geometry.
  - `dbar_polydisc_step` — **the step in polydisc form**:

    > given a cutoff `χ` supported in the `k`-th disc and equal to one on the polydisc, there is `U`
    > with `∂̄_k U = f_k` on the polydisc, and `∂̄_j U = 0` on the polydisc for every `j ≠ k` along
    > which `f_j` vanishes there.

    The cutoff is invisible where it is one, and it kills exactly the part of each coordinate line
    that leaves the polydisc.

  All that is left of D3 is to iterate this down the directions `k = n-1, …, 0` and add up the
  partial solutions — a finite recursion with no further analytic or geometric content.

- 2026-08-06 — **D3b(ii-c2b-iii-A) landed**, and the remaining obligations of D3 are now completely
  enumerated.  Axiom audit `propext, Classical.choice, Quot.sound`.
  - `dzbarAt_zero`, `dzbarAt_sub` — the base case of the recursion and the subtraction it needs.
  - `dzbarAt_add_solution` — **the assembly step**: if `U` solves part of the system and `v` solves
    the residue `f − ∂̄U` on a set, then `U + v` solves `f` there.

  Writing the recursion out showed exactly two facts are still missing, and nothing else:

  1. **`∂̄_i ∂̄_j = ∂̄_j ∂̄_i` for `C²` functions.**  The residue `g_j := f_j − ∂̄_j U` must again be
     `∂̄`-closed, and `∂̄_i g_j − ∂̄_j g_i = ∂̄_j ∂̄_i U − ∂̄_i ∂̄_j U`.  For `i = k` this is already
     available (`∂̄_k U = F` and the commutation give both sides equal to `∂̄_j F`); for `i, j ≠ k`
     it reduces, through the commutation applied twice, to symmetry of the mixed partials of the
     source.  Route: `∂̄_j F = Λ_j(fderiv ℝ F)` with `Λ_j` a continuous linear functional
     (`dzbarAt_eq_functional`, already proved), so `∂̄_i ∂̄_j F = Λ_i(Λ_j ∘L fderiv² F)` and the
     statement follows from mathlib's `second_derivative_symmetric`.
  2. **A uniform bound for the transform.**  The recursion also needs `g` to inherit the global
     bounds.  It does: `T_k(F)` is bounded by `2·(sup‖F‖)·R` whenever `F` is supported in a slab of
     radius `R`, because `∫_{D(a,R)} |w|⁻¹ dA ≤ ∫_{D(0,R)} |w|⁻¹ dA = 2πR` for every centre `a` —
     a rearrangement bound, provable by the same polar computation as `lintegral_ball_norm_inv`.
     The same bound applied to `fderiv ℝ F` controls the derivative.

  With those two, the recursion in `D3b(ii-c2b-iii-D)` is `Fin n` bookkeeping over
  `dbar_polydisc_step` and `dzbarAt_add_solution`.

- 2026-08-06 — **D3b(ii-c2b-iii-B closed.**  `dzbarAt_comm` : `∂̄_i ∂̄_j F = ∂̄_j ∂̄_i F` for `C²` `F`.
  Axiom audit `propext, Classical.choice, Quot.sound`.  The proof is the one the earlier note
  predicted: `∂̄_j F = Λ_j(fderiv ℝ F)` for a fixed continuous linear functional `Λ_j`
  (`dzbarAt_eq_functional`), so the iterated operator is `Λ_i(Λ_j ∘L fderiv² F)`, an explicit
  combination of `fderiv² F (e_i a) (e_j b)` for `a, b ∈ {1, i}`, and mathlib's
  `second_derivative_symmetric` swaps the two arguments.  This is what makes the residue
  `g_j := f_j − ∂̄_j U` inherit `∂̄`-closedness, which is what lets the recursion descend.

  One obligation now remains before the recursion: the uniform bound
  `‖T_k F‖ ≤ 2·(sup‖F‖)·R` for `F` supported in a slab of radius `R`, from
  `∫_{D(a,R)} |w|⁻¹ dA ≤ 2πR` uniformly in the centre `a`.

- 2026-08-06 — **D3b(ii-c2b-iii-C-i) landed.**  Axiom audit `propext, Classical.choice, Quot.sound`.
  - `cauchyIntegrand_eq_zero_of_notMem`, `cauchyIntegrand_support_subset` — for a slab-supported
    source the Cauchy integrand is supported in `closedBall (y_k) S`.

  Note the disc **moves with the base point**, which is exactly why a bound uniform in `y` does not
  follow from `lintegral_ball_norm_inv` (a fixed-ball estimate) and needs the split below.

  **The remaining estimate, in the form to be proved.**  For `‖G‖ ≤ M` and `G` slab-supported of
  radius `S > 0`, split `closedBall (y_k) S` at `‖w‖ = S`:

  * on `closedBall (y_k) S ∩ ball 0 S`, use `‖G(y − e_k w)/w‖ ≤ M‖w‖⁻¹` and
    `∫_{ball 0 S} ‖w‖⁻¹ ≤ 2πS` (`lintegral_ball_norm_inv`, already proved) — contributes `2πMS`;
  * on `closedBall (y_k) S \ ball 0 S`, use `‖w‖ ≥ S` so the integrand is at most `M/S`, and
    `volume (closedBall (y_k) S) = πS²` (`Complex.volume_closedBall`) — contributes `πMS`.

  Hence `‖T_k G (y)‖ ≤ 3πMS` uniformly in `y`.  No rearrangement inequality is needed, which is why
  this split was chosen over comparing with the centred disc.
