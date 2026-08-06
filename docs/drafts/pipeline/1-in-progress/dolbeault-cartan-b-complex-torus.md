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
- [ ] D3b(ii) the Dolbeault–Grothendieck lemma by induction on the `dz̄` directions
- [ ] D3 $\bar\partial$-Poincaré on a polydisc
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

### D4 — the remaining bridge, and why it is the hard one

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
