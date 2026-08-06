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

- [ ] D1 Cauchy–Pompeiu at the centre of a disc
- [ ] D2 compactly supported $\bar\partial$ equation on $\mathbb C$
- [ ] D3 $\bar\partial$-Poincaré on a polydisc
- [ ] D4 Dolbeault isomorphism
- [ ] D5 global solvability on $(\mathbb C^\times)^r$, hence $H^q=0$ for $q\ge1$
- [ ] feed back into the four Deninger cards

## Log

- 2026-08-06 — created; route fixed after confirming that mathlib has no $\bar\partial$ layer, that
  its divergence theorem is box-only, and that the polar-coordinate proof of D1 needs only
  one-dimensional calculus plus mathlib's polar-coordinate change of variables.
