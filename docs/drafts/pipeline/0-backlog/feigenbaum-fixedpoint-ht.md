# Feigenbaum Fixed-Point Function: Hypertranscendence

- **ID:** feigenbaum-fixedpoint-ht
- **Stage:** 0-backlog
- **Type:** OPEN CONJECTURE
- **Source:** Turing id=1697 / hgt session 2026-06-24
- **Priority:** HIGH — new family, HT status open, constants transcendence open

## Object

The Feigenbaum fixed-point function g: ℂ → ℂ is the unique (normalized) solution of

  g(x) = −(1/α) g(g(αx)),    g(0) = 1,

where α ≈ −2.5029... is determined self-consistently as the inverse of the spatial
scaling constant. The function g is real-analytic on (−1,1) and extends analytically
to a strip in ℂ via complex-analytic proof (Lanford 1982, Epstein 1986–1999).

The functional equation is a FIXED-POINT CONDITION for the doubling renormalization
operator R[f](x) = −(1/α)f(f(αx)). g is characterized entirely by this constraint —
there is no differential recurrence, no closed-form hypergeometric formula, no generating
series of known algebraic type.

## Why g is a native HT candidate

The hgt founding metaphor applies literally here: g is fixed by a constraint, not
propagated by a flow. The renormalization fixed-point equation is the constraint; g has
no algebraic ODE, no finite-order Mahler equation, no hypergeometric handle.

**HT status: OPEN.** Cold-codex probe (Turing id=1697) confirmed: neither the HT status
of g nor its natural boundary in ℂ is known. Becker–Bergweiler does NOT transfer (their
result is about Böttcher coordinates of polynomial dynamics; the Feigenbaum equation is
not a polynomial iteration in the same sense). The Écalle tree / resurgence literature
treats g as a transseries object but has not proved HT.

**Constants: transcendence OPEN.** The Feigenbaum constants α ≈ −2.5029... and
δ ≈ 4.6692... (the period-doubling rate) are not known to be even IRRATIONAL. This is
an open problem at the level of "is π transcendental" in difficulty — but 50 years more
recent.

## Constraint-not-flow metaphor

The renormalization fixed-point is precisely the Wheeler–DeWitt analogy from the hgt
founding document: no clock (no parameter propagating the solution), only a constraint
(the functional equation) fixing the object uniquely. This is a stronger form of
"constraint not flow" than the Böttcher case, because:
- Böttcher: fixed by a topological conjugacy equation (Φ∘f∘Φ^{-1} = z²), which comes
  from polynomial iteration → there IS a flow (the dynamics of f).
- Feigenbaum: fixed by a renormalization equation involving g∘g (self-composition), not
  arising from any polynomial flow.

## Connection to natural boundaries

Epstein--Lascoux (1981) prove that the Feigenbaum function is analytic and uniform in a
domain with a natural boundary. More precisely, their construction gives a domain `D`
of analyticity and then argues that continuation beyond `D` would contradict continuation
of the inverse branch, so `D` is a natural domain of holomorphy for `g`. Buff later records
the same maximal-extension picture as a simply connected dense domain `W_c`, citing
Epstein and McMullen, and proves non-continuability across `partial W_c`.

This source-kills the first version of Gate 1 as an extraction problem: non-continuability
is already in the literature. It does **not** prove HT. A natural boundary by itself does
not imply differential transcendence; an algebraic differential equation involves
`g,g',...,g^(n)`, so the boundary-separation schema does not supply an independent
side-field analytic at a crossing point.

[CONJECTURE — corrected] The Feigenbaum fixed point is hypertranscendental. The natural
domain of holomorphy is strong evidence for non-holonomic behavior, but the missing gate
is an argument that a finite algebraic differential relation would force analytic
continuation or otherwise contradict the renormalization fixed-point constraint.

## The crossing problem

For algebraic independence over a separately analytic side-field, boundary-separation
would need:
- the boundary of the maximal Feigenbaum domain cannot be crossed by `g`;
- the companion field is analytic at some boundary point outside coefficient and
  discriminant bad loci.

For **HT**, this is not enough, because the companion functions in an algebraic
differential relation are derivatives of `g` itself. The real crossing problem is therefore:
can one prove that any finite ADE for `g` would produce a continuation mechanism across
the Epstein--Lascoux boundary, despite the derivatives sharing the same obstruction?
That is the missing theorem.

## Comparison with Böttcher

| Böttcher φ_c                         | Feigenbaum g                          |
|--------------------------------------|---------------------------------------|
| Fixed by: φ_c ∘ f_c ∘ φ_c^{-1} = z² | Fixed by: g = R[g] (renorm. FP)      |
| Natural boundary: J_c                | maximal domain boundary `partial D` / `partial W_c` |
| HT: PROVED (Becker-Bergweiler)       | HT: OPEN                              |
| Constants: c ∈ ℂ (parameter)         | Constants: α, δ IRRATIONAL NOT KNOWN  |
| Crossing lemma: Green's function     | Crossing lemma: J_F uncountable (easy)|
| Obstacle: none known                 | Obstacle: ADE-continuation gate |

## Attacks to try

1. **ADE-continuation gate**: Epstein--Lascoux already give a natural domain of holomorphy.
   The needed new theorem is narrower and harder: prove that any finite ADE for the
   Feigenbaum fixed point would force continuation across that boundary, or derive a direct
   contradiction from the renormalization equation plus the ADE.

2. **Écalle transseries route**: g has a transseries expansion in the Écalle formalism.
   If the transseries is not algebraically generated (not a D-finite generating series), that
   might give a HT obstruction via a different route. [OPEN — Écalle experts haven't proved
   this, but the transseries has infinitely many generators]

3. **Irrational period route**: Can the renormalization eigenvalue α be used to show g
   satisfies no finite-degree algebraic ODE? Analogy: the Airy function satisfies a
   second-order linear ODE; the Feigenbaum g satisfies a NON-LINEAR functional equation.
   A functional equation argument might directly exclude finite-order algebraic ODEs without
   going through the natural boundary.

4. **Wild-analogy: gear-train renormalization**: The Feigenbaum equation is a gear-ratio
   fixed point (self-similar gearing, like a quine for dynamical systems). Gear-train
   analysis gives: the gear ratio α is transcendental because it's the spectral radius of
   an operator on an infinite-dimensional function space, not a finite-degree algebraic
   number. Can this operator-spectral argument bound the algebraic degree of g over ℂ(x)?

## Novelty gate

- **NOVEL?** "Is the Feigenbaum fixed-point function hypertranscendental?" is not answered
  in the sources checked here. The natural-boundary component is known, so novelty cannot
  be claimed there. The potentially new part is an ADE-obstruction theorem using the
  renormalization constraint.
- **SIGNIFICANT?** Extends the HT class beyond polynomial dynamics and classical special
  functions into renormalization theory. Opens a new structural lane: constraint-not-flow
  via fixed-point equations, not via conjugacy equations. Grade: HIGH — new object family,
  not just a variant of the existing objects.

## Log

- 2026-06-24 — Created by Wheeler after Turing id=1697 proposed the Feigenbaum function
  as a native HT candidate with confirmed OPEN status. Cold codex verified HT unknown,
  constants transcendence unknown, Becker-Bergweiler does not apply.
- 2026-06-24 — Professor corrected the gate structure. Epstein--Lascoux already prove a
  natural domain of holomorphy, and Buff records the maximal-extension picture. This does
  not imply HT by boundary-separation, because an ADE relation uses derivatives of `g`,
  not an independent analytic companion field.

## 2026-06-24 — Turing id=1744 + Haiku id=1745: HT-composition principle FALSE (update on attacks)

**HT∘HT-inner is NOT generally HT.** Counterexample: Γ∘Γ^{-1} = id (DA). Both Γ and Γ^{-1} (locally) are HT, but composition = identity = DA. Therefore:

- Attack 1 (ADE-continuation gate): KILLED — g ∉ H^∞(W_c) at its natural boundary domain.
- Attack via "HT∘HT = HT" principle: KILLED — counterexample exists.
- The question is NOW GENUINELY TWO-SIDED: the C-F constraint g(g(λx)) = -λg(x) is a compositional eigenfunction equation. This could EITHER force g DA (like the inverse equation ψ∘H = id) OR allow g HT. No presumption of HT.

## 2026-06-24 — Turing id=1747: Schwarzian three-point equation (sharpest structural attack)

The Schwarzian σ = {g,x} satisfies the three-point renormalization equation:

  σ(x) = λ²[σ(g(λx)) · g'(λx)² + σ(λx)]

Verified numerically by Turing (12-digit agreement at x = 0.1, 0.15, 0.2, 0.25).

Contrast with j-function: {j,τ} = rational(j)·(j')² — a ONE-POINT algebraic ODE (j is DA).

g's Schwarzian equation involves THREE POINTS (x, λx, g(λx)) — a self-referential functional equation. Whether it can be "collapsed" to a pointwise algebraic ODE for σ (and hence a pointwise ADE for g) is the exact criterion for g DA vs HT.

**Why collapse seems impossible [CONJECTURE]:**
- A pointwise ODE A(x, σ, σ', ...) = 0 for σ would need to be compatible with the three-point equation.
- The three-point equation relates σ(x) to σ(λx) and σ(g(λx)) — a q-difference-differential constraint with q = λ (irrational).
- For generic irrational q and generic ODE, the combined q-difference-ODE system is overdetermined (no solution).
- The Galois group of the q-difference equation with irrational q = λ is "large" (full GL_n or ℂ*), preventing algebraic reduction.

**Gap:** nonlinear q-difference Galois theory for irrational q is not developed. This is the shared bottleneck with the weld non-formality (Turing id=1751: non-commuting difference-Galois is the missing tool).

## Active surviving attacks

1. **Schwarzian three-point → q-difference Galois**: Does there exist a meromorphic σ satisfying BOTH a pointwise polynomial ODE AND the three-point Schwarzian equation above? If no → g HT. This is the concrete open question.

2. **Difference-Galois on g(g(λx)) = -λg(x) directly**: Treat the C-F equation as a nonlinear q-difference equation. The Galois group of this equation (nonlinear, q = λ irrational) determines whether g is algebraic/DA. Linear q-difference Galois theory: Di Vizio-Hardouin-Wibmer. Nonlinear extension: open.

3. **Is g DA at all? (Turing id=1744 suggestion)**: Before proving g HT, check whether the C-F constraint FORCES g DA. I.e., could a polynomial ADE be consistent with g(g(λx)) = -λg(x)? An explicit search for low-degree, low-order ADEs might find or rule out DA solutions. If no DA solution exists at low orders → strong evidence for g HT.


## 2026-06-24 — Source correction: rational Koenigs HT is known; Feigenbaum gate is polynomial-like straightening

**Promptability audit.** No computation was run. The fork was source-theoretic and changed the proof route:

- Claim A: Koenigs/Schroeder linearizer HT is open even for rational maps or polynomials with attracting fixed point.
- Claim B: rational-map Schroeder functions are classified by Ritt / Becker--Bergweiler; the attracting rational case is already forced hypertranscendental.

The sources choose Claim B. Fernandes's survey (arXiv:2102.12168) restates Becker--Bergweiler's theorem: if a Schroeder function is differentially algebraic, then the fixed point is repelling and the function lies in the explicit exceptional list. The same survey states that attracting and repelling Schroeder solutions converge locally. Primary citation: P.-G. Becker and W. Bergweiler, *Hypertranscendency of conjugacies in complex dynamics*, Math. Ann. 301 (1995), 463--468, DOI 10.1007/BF01446639.

**Imported corollary.** Let `R in C(z)` have degree at least two and an attracting fixed point `a` with multiplier `0 < |mu| < 1`. Let `phi` be the inverse Koenigs/Schroeder linearizer,

```text
phi(mu z) = R(phi(z)),   phi(0)=a,   phi'(0) != 0.
```

Then `phi` is hypertranscendental over `C(z)`. Proof: if `phi` were differentially algebraic, Becker--Bergweiler's classification would put the Schroeder fixed point in the repelling case, contradiction.

**DA-conjugacy transfer lemma.** Let `h` be an analytic germ with an attracting fixed point of nonzero multiplier `mu`. Suppose a locally univalent differentially algebraic germ `psi` conjugates it to such a rational map `R` near the fixed point:

```text
psi(h(z)) = R(psi(z)).
```

If `phi_h(mu z)=h(phi_h(z))` is the inverse Koenigs linearizer of `h`, then `psi o phi_h` is the inverse Koenigs linearizer of `R`. Since differentially algebraic germs are closed under composition, `phi_h` differentially algebraic would imply `psi o phi_h` differentially algebraic, contradicting the imported corollary. Hence `phi_h` is hypertranscendental whenever the straightening conjugacy available to the germ is itself differentially algebraic on the relevant local coordinate.

**Feigenbaum consequence.** Buff's *Geometry of the Feigenbaum map* states that the Cvitanovic--Feigenbaum equation can be read as a linearizing equation: `f_lambda(z)=f(lambda z)` has an attracting fixed point `x0` of multiplier `-lambda`, and `f` is its linearizer. The same paper records that `f: W -> C_lambda` is quadratic-like and hybrid-conjugate to the Feigenbaum polynomial.

Therefore the Feigenbaum HT gate is not "Koenigs with nonzero multiplier is open" for rational maps. That door is already closed by Becker--Bergweiler. The actual unresolved gate is:

> Can the polynomial-like / hybrid straightening of the Feigenbaum map be promoted, on the relevant attracting-basin linearizer germ, to a differentially algebraic analytic conjugacy to a rational polynomial model?

If yes, the DA-conjugacy transfer lemma proves Feigenbaum HT. If no, any DA counter-scenario for the Feigenbaum linearizer must hide precisely in the non-DA or non-analytic nature of the straightening, not in the mere presence of a nonzero attracting multiplier.

**Grade.** This is a BRIDGE/source-correction, not a new final theorem. It kills the stale q-difference / "Koenigs HT open for polynomials" framing and relocates the live obstruction to DA-regularity of polynomial-like straightening.

### Application gap audit: ordinary hybrid straightening is not enough

The DA-conjugacy transfer lemma applies to the attracting map whose inverse Koenigs linearizer is `f`, namely `f_lambda(z)=f(lambda z)`. Buff's standard quadratic-like straightening, however, conjugates the quadratic-like map

```text
f: W -> C_lambda
```

to the Feigenbaum polynomial. It does **not** by itself conjugate

```text
f_lambda(z)=f(lambda z)
```

to a rational map. Indeed, if `chi o f = P o chi`, then

```text
chi(f_lambda(z)) = chi(f(lambda z)) = P(chi(lambda z)),
```

which becomes a conjugacy for `f_lambda` only if the straightening coordinate also controls the scaling `z -> lambda z` in a compatible analytic way.

So the corrected transfer gate is narrower:

> Find a locally univalent DA analytic germ `psi` and a rational map `R` of degree at least two such that `psi o f_lambda = R o psi`; or prove that ordinary straightening plus a `lambda`-equivariance identity supplies such a germ.

Without that extra equivariance, Becker--Bergweiler cannot be imported into Feigenbaum. The current gain is still useful: the rational Koenigs baseline is closed, and the exact missing structure is now a DA **scaling-compatible** straightening, not generic polynomial-like straightening.

### Notation audit: coordinate vs inverse Schroeder function

Becker--Bergweiler's theorem is often stated for the inverse Schroeder/Poincare form

```text
phi(mu z) = R(phi(z)).
```

Buff's Feigenbaum `f` is the Koenigs coordinate form

```text
f(f_lambda(z)) = -lambda f(z).
```

This does not change the rational baseline. A locally univalent differentially algebraic germ has a differentially algebraic local inverse, so if either the Koenigs coordinate or its inverse were differentially algebraic, the other would be too. Thus Becker--Bergweiler excludes both forms for non-superattracting attracting rational maps.

The DA-conjugacy transfer lemma should therefore be read in either equivalent form. For a coordinate conjugacy `psi o h = R o psi`, the rational Koenigs coordinate `F_R` gives `F_R o psi` as a Koenigs coordinate for `h`; local uniqueness gives `F_R o psi = c F_h`. If `F_h` and `psi` were differentially algebraic, then composing with the DA local inverse of `psi` would make `F_R` differentially algebraic, contradicting the rational baseline.

### Local analytic conjugacy is too cheap

A further route-kill: replacing "DA analytic conjugacy" by mere "analytic conjugacy" makes the transfer gate vacuous. Any two one-dimensional attracting germs with the same nonzero multiplier are locally analytically conjugate to the same linear map by Koenigs theory. Thus one can locally analytically conjugate `f_lambda` to an attracting rational germ with matching multiplier without learning anything about HT.

The gate must retain the differential-algebraic qualifier. The non-promptable content is not local analytic conjugacy; it is whether any scaling-compatible conjugacy can be chosen inside the DA category. That is exactly where Becker--Bergweiler bites: a DA choice would transfer the known rational HT obstruction back to Feigenbaum.

## 2026-06-24 — Ritt anchor and DA-germ transfer boundary

Turing id=1772 identified the exact rational-map anchor: Ritt's theorem, with a modern Galoisian proof by
Di Vizio--Fernandes, *A Galoisian proof of Ritt theorem on the differential transcendence of Poincare functions*
(arXiv:2102.08268). For a rational base map `R`, a DA Poincare/Schroeder function falls into Ritt's exceptional
periodic list; non-exceptional polynomial Poincare functions are HT. Di Vizio--Fernandes also prove a partial
extension for algebraic base functions.

This sharpens the Feigenbaum gate:

> Feigenbaum HT would follow from a Ritt-type theorem for the polynomial-like map `f_lambda(z)=f(lambda z)`, or
> from a scaling-compatible straightening that brings `f_lambda` into Ritt's rational/algebraic finite-base
> setting.

But the transfer cannot be weakened to "the base germ is DA." New gatekeeper card:

`docs/drafts/pipeline/0-backlog/ritt-algebraicity-load-bearing.md`

It proves the countermodel

```text
F(z)=tan(z),
h(z)=arctan(mu tan(z)),  0<|mu|<1,
F(h(z))=mu F(z),
```

where both `F` and `h` are DA local germs, `h` is not algebraic over `C(z)`, and the Koenigs coordinate `F` is
DA. Thus Ritt's algebraic finite-base hypothesis is load-bearing. A Feigenbaum proof must use polynomial-like
finite-degree/global structure, not only local DA functional-equation data.

### 2026-06-24 — Rational linearization trichotomy cross-link

The rational-map linearization baseline is now recorded separately in
`rational-linearization-ht-trichotomy.md`:

- Schroeder/Koenigs/Poincare rational linearizers are classified by Ritt / Becker--Bergweiler.
- Boettcher rational linearizers are classified by Becker--Bergweiler.
- Abel/Fatou rational linearizers are always HT.

Therefore Feigenbaum novelty must not be claimed from any rational fixed-point corner. The live gate remains
polynomial-like or scaling-compatible straightening for `f_lambda(z)=f(lambda z)`, because the Feigenbaum object
is not a rational map on the sphere.
