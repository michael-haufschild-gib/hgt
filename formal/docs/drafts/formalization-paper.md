# A Machine-Checked Framework for Algebraic Independence via Natural Boundaries: the Böttcher c-Velocity and the Perturbed Böttcher Coordinate

`[SEARCH register — working draft of an ITP/CPP/JAR-style formalization paper. Prior-art citations
verified by search/fetch on 2026-07-03 (see §7 and the companion claim map); mathematical claims are
tagged [PROVED HERE] (axiom-clean Lean 4) or [CITED] (external, formalized here). Novelty statements
are labelled and gated on the checks in §7.]`

---

## Abstract

We give a fully machine-checked (Lean 4 / Mathlib) development of algebraic independence over the
rational function field `ℂ(z)` between two analytic germs pinned by functional equations under
**different substitutions**:

* `u₀(z) = Σ_{n≥0} 2^{-(n+1)} z^{-(2^{n+1}-1)}`, the Böttcher **c-velocity** at the monomial fiber
  `z ↦ z²` (the parameter derivative `∂_c φ_c |_{c=0}` of the Böttcher coordinate), a lacunary
  series with natural boundary the unit circle, satisfying the **Mahler** equation
  `u₀(z²) = 2z·u₀(z) − 1` under the monomial substitution `T : z ↦ z²`;
* `φ_b = ` the inverse Böttcher coordinate of `z ↦ z² + b`, satisfying `φ_b(z²+b) = φ_b(z)²` under
  the **nonlinear, non-monomial dynamical** substitution `S_b : z ↦ z² + b`.

The independence is proved not by Mahler's method — which requires a common monomial substitution
and is thereby inapplicable to the pair `(T, S_b)` — but by a **natural-boundary obstruction**: a
polynomial relation would analytically continue `u₀` across `|z| = 1`. We formalize this method as a
reusable engine, localize the parameter region where it applies **sharply** (the critical curve `ρ`,
maximum `2 + √2`, a *directional* not modulus condition), and lift the independence along the whole
finite Böttcher root tower (a Kummer descent, coherent as a `ℤ₂` inverse system). Everything is
axiom-clean: `#print axioms` yields exactly `[propext, Classical.choice, Quot.sound]`.

To our knowledge this is the first formalization of (i) transcendence of Böttcher coordinates over a
function field, (ii) algebraic independence between a natural-boundary germ and a dynamical
coordinate stated in a faithful germ-field carrier, and (iii) a sharp-threshold pair in complex
dynamics. The cross-substitution independence itself lies beyond the linear/monomial frontier of the
difference-Galois independence theory of Adamczewski–Dreyfus–Hardouin and Schäfke–Singer (§7).

---

## 1. Introduction

### 1.1 The problem shape

Two analytic functions can each be "fixed by a constraint rather than propagated by a flow": `u₀` and
`φ_b` are each the *unique* solution (in their regime) of a functional equation, with no generative
recursion. Asking whether they are algebraically independent over `ℂ(z)` is asking whether the two
constraints are *incommensurable*. When the two constraints are difference equations under the **same**
kind of substitution — both monomial Mahler operators `x ↦ x^{p_i}` — this is the domain of Mahler's
method and its modern difference-Galois refinements (Nishioka; Adamczewski–Dreyfus–Hardouin;
Schäfke–Singer). Our pair is deliberately **outside** that domain: `u₀` lives under the monomial `z↦z²`,
but `φ_b` lives under the nonlinear dynamical `z ↦ z²+b`, which is not a Mahler operator and whose
equation `φ_b(z²+b)=φ_b(z)²` is nonlinear. The difference-Galois machinery does not reach it.

### 1.2 What we do instead

We use the **boundary geometry**. `u₀` has the unit circle as a natural boundary (its doubly
exponential lacunary gaps, Hadamard); `φ_b`, being the Böttcher coordinate, is analytic on a window
that *crosses* the unit circle for suitable `b`. A polynomial relation `P(z, u₀, φ_b) = 0` on that
window, solved for `u₀` against `φ_b`'s analyticity, would continue `u₀` across `|z|=1` — impossible.
This is method-classical in spirit but **substitution-agnostic**, which is exactly why it reaches the
pair `(T, S_b)`. We turn it into a reusable Lean engine and push three further contributions:
the **sharp parameter geometry** (where the window exists), the **germ-field carrier** (so that
"no relation" is a statement about the actual functions, not a syntactic artifact), and the **finite
root tower** (Kummer descent, all levels independent, coherent as a pro-object).

### 1.3 Contributions

- **C1 [PROVED HERE].** First machine-checked transcendence of Böttcher coordinates over `ℂ(z)`:
  `bottcher_transcendental_far` (any far domain) and the window family `phiB_transcendental`
  (`‖b‖ > 2+√2`).
- **C2 [PROVED HERE].** First formalized algebraic independence between a natural-boundary germ (`u₀`,
  boundary `|z|=1`) and a dynamical coordinate `φ_b`, in the faithful carrier
  `meroField U = FractionRing (analyticSubring U)` — `NoRelation` there is a statement about the
  functions. Unconditional over the entire viable parameter region (`u0_mstep_independence`).
- **C3 [PROVED HERE].** A machine-checked **sharp-threshold pair** in complex dynamics: coverage for
  all `‖b‖ > 2+√2` together with an obstruction witness at `b = −(2+√2)` (`window_threshold_sharp`),
  and the *direction-dependence* pair `b = ±3` (`window_dichotomy_modulus_three`) — same modulus,
  opposite viability.
- **C4 [PROVED HERE].** The finite Böttcher **root tower**: an abstract Kummer descent
  `noRelation_pow_descent` (`NoRelation K (Fⁿ) G → NoRelation K F G`, any fields, any `n`), its
  coherent `ℤ₂`-tower form (`u0_coherent_kummer_tower`), and cross-program reuse — the q62 Böttcher
  pair's full root tower (`KummerRootApplications`).
- **C5 [PROVED HERE].** First formalized instances toward Nguyen's Question 6.2(a) (arithmetic
  dynamics), the quadratic nonexceptional family (`q62_independence` and the disconnected/mixed cases).
- **Reusable infrastructure.** The natural-boundary engine (`NaturalBoundaryTranscendence`), the
  carrier-generic descent (`kappaP`/`descend_algebraicP`/`pullAn`), the assembly functor, and the
  general lemmas `analyticOnNhd_of_continuousOn_exp_eq`, `exists_analyticOnNhd_pow_eq`,
  `noRelation_pow_descent(_both)` — all field/carrier-generic, usable beyond this paper.

The whole development is axiom-clean; the unified entry point is
`U0Capstone.u0_full_bottcher_tower_capstone` (pillars 1–5 in one statement).

---

## 2. The objects and their functional equations

### 2.1 `u₀`, the Böttcher c-velocity (`U0Series`, `U0NaturalBoundary`)

`def u0 (z : ℂ) : ℂ := Σ' n, 2^{-(n+1)} · z^{-(2^{n+1}-1)}` (`U0Series.u0`). Facts formalized:
summability for `‖z‖ ≥ 1`; the **Mahler functional equation** `2 z · u₀ z = 1 + u₀ (z²)`
(`U0Series`); and the **natural boundary** at `|z|=1` — `U₀(x) = u₀(1/x)` has doubly exponential
lacunary gaps, so it does not continue across the unit circle (`U0NaturalBoundary`). Dynamically,
`u₀ = ∂_c φ_c |_{c=0}`: the first-order velocity of the Böttcher coordinate as the monomial map `z²`
is perturbed.

### 2.2 `φ_b`, the inverse Böttcher coordinate (`Bottcher.BottcherCoord`)

`bottcherCoord b z = exp (bottcherLog b z)`, analytic and nowhere zero on the escape region
`escapeOpen b = {z : max 2 ‖b‖ < ‖z‖}`, with the **Böttcher functional equation**
`bottcherCoord b (z²+b) = (bottcherCoord b z)²` (`bottcherCoord_quadratic`) and its iterate
`bottcherCoord b (f_b^[n] z) = (bottcherCoord b z)^(2^n)` (`bottcherCoord_iterate`). The substitution
`S_b : z ↦ z²+b` is nonlinear and non-monomial; the equation is nonlinear (squaring on the right).

### 2.3 The carrier: germ fields (`U0MeroCarrier`)

For an open, preconnected, nonempty, infinite `U ⊆ ℂ`, `analyticSubring U` is the ring of germs of
functions analytic on `U`, and `meroField U = FractionRing (analyticSubring U)` its fraction field.
`NoRelation (RatFunc ℂ) F G` (`Bottcher.Q62`) means *no nonzero bivariate polynomial over `ℂ(z)`
vanishes at `(F,G)`* — evaluated on the actual germs, via `(P.map (aeval G)).eval F`. This carrier is
the reason the independence statements are about functions, not formal symbols.

---

## 3. Main results (theorem inventory)

All statements are `[PROVED HERE]`, axiom set `[propext, Classical.choice, Quot.sound]`.

| Result | Lean name | Statement |
|---|---|---|
| Böttcher transcendence, far | `Bottcher.bottcher_transcendental_far` | `φ_c` transcendental over `ℂ(z)` on any far domain |
| Window transcendence | `U0PhiLargeDescent.phiB_transcendental` | `φ_b` transcendental, all `‖b‖ > 2+√2` |
| Sharp window independence | `U0WindowSharpness.window_threshold_sharp` | `u₀ ⟂ φ_b` for all `‖b‖ > 2+√2` **and** obstruction at `−(2+√2)` |
| Directional dichotomy | `U0DichotomyWitness.window_dichotomy_modulus_three` | `b=3` viable, `b=−3` obstructed (same `‖b‖`) |
| Viability boundary closed | `U0ParameterSpace.isClosed_obstructed` + curve point | `𝒪` closed; certified `ρ`-point at `arg b ≈ 126.9°` |
| m-step branch exists | `U0PhiMStep.exists_mstep_branch` | analytic `ψ = φ_b∘f_b^[N]` on a window crossing `|z|=1`, any viable `b` |
| **Viable-region independence** | `U0PhiMStepFar.u0_mstep_independence` | `u₀ ⟂ ψ` for **every** viable `b` (unconditional) |
| Sub-threshold witnesses | `U0MStepInstances.u0_mstep_independence_subthreshold` | independence at `b=3` and 5 slice points, all `‖b‖<2+√2` |
| Kummer descent (abstract) | `U0MStepKummer.noRelation_pow_descent` | `NoRelation K (Fⁿ) G → NoRelation K F G`, any fields/`n` |
| Kummer-layer independence | `U0MStepKummer.u0_mstep_kummer_independence` | `u₀ ⟂` any field root `χ^(2^k)=ψ` |
| Concrete Kummer branch | `U0KummerBranch.u0_mstep_kummer_branch_independence` | a genuine analytic `2^k`-th root, `⟂ u₀` |
| **Coherent tower** | `U0KummerBranch.u0_coherent_kummer_tower` | one log ⟹ inverse system `(χ_{k+1})²=χ_k`, all `⟂ u₀` |
| q62 instances | `Bottcher.q62_independence`, `q62_mixed`, `q62_disconnected_both` | `φ_{c₁} ⟂ φ_{c₂}`, nonexceptional |
| q62 root towers | `KummerRootApplications.q62_roots_independence` (+mixed/both) | every root of `φ_{c₁} ⟂` every root of `φ_{c₂}` |
| Unified capstone | `U0Capstone.u0_full_bottcher_tower_capstone` | pillars 1–5 in one statement |

---

## 4. Method

### 4.1 The natural-boundary engine (`NaturalBoundaryTranscendence`)

`no_poly_relation_of_natural_boundary_arc` (specialized to `u₀`): if `f` does not continue across a
boundary arc and a separable polynomial relation with a boundary-analytic partner holds on a lens
crossing the arc, then the relation is trivial. For `u₀` the arc is the unit circle (smooth, so the
lens `D ∩ ball z₀ ρ` is preconnected — cleaner than at a fractal Julia set), and the partner is the
window branch of `φ_b`. This is the substitution-agnostic core: it never inspects `S_b`.

### 4.2 The far descent (`U0PhiLargeDescent`, `U0PhiMStepFar`)

Transcendence of `ψ = φ_b∘f_b^[N]` descends from `bottcher_transcendental_far` along the polynomial
map `f_b^[N]`: the carrier-generic embedding `kappaP` / `descend_algebraicP` and the germ pullback
`pullAn` transport an algebraic relation on the far image back to the window. A key simplification
(this work): openness of the far image follows from the **open mapping theorem** for positive-degree
polynomials (`Polynomial.isOpenQuotientMap_eval`) — no derivative-nonvanishing hypothesis, hence no
puncturing of the carrier, hence unconditional over the whole viable region.

### 4.3 The sharp parameter geometry (`U0WindowSharpness`, `U0ParameterSpace`, `U0CriticalCurveSlice`)

The window exists iff the filled Julia set `K_b` avoids the closed unit disk. The obstructed set `𝒪`
is closed; the covering constant is exactly `2+√2` (attained at `b=−(2+√2)`), and viability is
directional: `b = 3` viable, `b = −3` obstructed. Square-tree certificates verify slice points along
the critical curve `ρ`.

### 4.4 The Kummer tower (`U0MStepKummer`, `U0KummerBranch`)

`noRelation_pow_descent` is the transcendence-degree fact `trdeg K(F,G) = trdeg K(Fⁿ,G)` in
bivariate-elimination form, proved directly on the `NoRelation` definition (two-case split on
`P.map (aeval G)`; no MvPolynomial bridge). A concrete analytic `2^k`-th root exists because the
window disk is simply connected (`exists_analyticOnNhd_pow_eq`, via a continuous log upgraded to
analytic by `analyticOnNhd_of_continuousOn_exp_eq`); generating all levels from **one** log yields
the coherent `ℤ₂` tower.

---

## 5. Formalization architecture

- **Scale & discipline.** ~3 program areas under `GaloisForLFunctions` (`Hurwitz`, `U0`, `Bottcher`),
  unified in `MainTheorems`; the U0 program is ~40 modules. Lint gate forbids any active
  `sorry`/`admit`/`axiom`/`opaque`/`unsafe`; every capstone verified `#print axioms =
  [propext, Classical.choice, Quot.sound]`.
- **Carrier design as a contribution.** Representing "algebraic independence of functions" as
  injectivity into `FractionRing (analyticSubring U)` makes the statements faithful and gives a clean
  functorial descent (`kappaP`, `pullAn`, the assembly functor). This is reusable for any
  independence-of-germs formalization.
- **Genericity.** The natural-boundary engine, the descent, and the Kummer machinery are stated for an
  arbitrary carrier / arbitrary fields, so the same lemmas serve `u₀`, the q62 Böttcher pair, and (in
  principle) any committed `NoRelation`.

---

## 6. What is proved here vs. cited

- `[CITED, formalized here]` The *transcendence* mechanisms are Mahler/Becker–Bergweiler–Nishioka in
  spirit (multiplicity/height doubling under the substitution). We do not claim the underlying number
  theory as new; the contribution is its first machine-checked form for these dynamical objects.
- `[PROVED HERE, novelty-bearing]` The *joint independence* `u₀ ⟂ φ_b` under different substitutions,
  via the natural-boundary obstruction; the *sharp directional geometry*; the *coherent root tower*;
  and the *carrier + engine + descent* infrastructure.
- The analytic Hurwitz-zeta theory is in Mathlib (Loeffler–Stoll); our Hurwitz lane proves
  independence-side (no-relation) statements only — complementary.

---

## 7. Relation to prior work and the novelty gate

Verified on 2026-07-03 (fetch/search; see companion claim map for URLs).

1. **girving/ray** (Lean 4, 2023): Böttcher's theorem, Multibrot connectedness — purely
   topological/geometric, *nothing* on transcendence, independence, or natural boundaries. Our tree
   does not import it. → C1/C2 are new relative to ray.
2. **Adamczewski–Dreyfus–Hardouin(–Wibmer), "Algebraic independence and linear difference equations"**
   (arXiv:2010.09266, JEMS). The state of the art for cross-substitution independence: pairs `(φ,σ)`
   of operators, *including* Mahler `x↦x^{p₁}, x↦x^{p₂}`. **Scope (verified):** equations must be
   **linear** and operators must be **monomial** (shift / q-difference / Mahler); "nonlinear
   substitutions like `x↦x²+b` are not addressed." Our `φ_b` is nonlinear under a non-monomial
   substitution → **outside ADH**. `[CONJECTURE — this is the load-bearing novelty claim; it holds
   under the verified scope of ADH, but a referee should confirm no follow-up extends ADH to nonlinear
   dynamical substitutions.]`
3. **Schäfke–Singer, "Consistent systems of linear differential and difference equations"**
   (arXiv:1605.02616): linear systems, consistency hypothesis, Mahler among the operators. Same
   linear/monomial restriction → does not reach `(T, S_b)`.
4. **Nguyen, arXiv:1310.2329**, Question 6.2: independence of Böttcher coordinates `φ_{c₁},…,φ_{cₙ}`
   of *disintegrated polynomials*. That is a `φ ⟂ φ` question (our C5/q62 lane formalizes instances);
   it is **not** the `u₀ = ∂_c φ ⟂ φ_b` pairing of C2.
5. **Saleh, "Bialgebraic geometry of Böttcher coordinates"** (arXiv:2606.24553, 2026): Ax–Lindemann /
   Ax–Schanuel–type functional-transcendence classification of a *single* Böttcher coordinate `Ψ_f`.
   Verified: no parameter-derivative / c-velocity, no Mahler pairing, no natural-boundary method →
   complementary, no collision.
6. **Costin–Huang, "Behavior of lacunary series at the natural boundary"** (arXiv:0810.3027, Adv.
   Math.): analytic behavior of lacunary series (like `u₀`) at their natural boundary — background for
   the boundary side; not an algebraic-independence result.

**Gate verdict.** The *formalization* contributions (C1–C5, infrastructure) clear NOVEL × SIGNIFICANT
with zero litigation risk: none of Böttcher-coordinate transcendence, natural-boundary germ
independence, the sharp-threshold pair, or the germ-field carrier exists in any proof assistant. The
*pure-mathematical* novelty of the cross-substitution independence rests on item 2's verified scope
(linear/monomial only); it is a genuine bridge from the natural-boundary method to a regime the
difference-Galois theory does not cover, and is stated as `[CONJECTURE]` pending a referee's scan for
any nonlinear-substitution extension.

**Do NOT claim** (per the claim map): "first Böttcher formalization" (ray); "first formalized
transcendence" (numbers corpus, 2010s); "resolves Question 6.2" (instances only); novelty of the
analytic Hurwitz theory.

---

## 8. Limitations and future work

- The `u₀`-side natural boundary is used axiom-cleanly, but the *deep* transcendence input on the
  `φ_b` side (`bottcher_transcendental_far`) is itself a substantial committed development; a
  self-contained paper should either cite the Mahler mechanism or present its formalization as part of
  the contribution.
- The critical-curve `ρ` is certified at finitely many slice points; a closed-form description of `ρ`
  (the `∂𝒱 = closure(pattern-region)` conjecture, `U0ParameterSpace.ObstructedEqClosurePattern`)
  remains open.
- The coherent tower carries a natural `ℤ₂`-action permuting the roots; its full profinite
  Galois/monodromy structure is future work (genuinely new mathematics, not formalization).
- Extending the natural-boundary engine to *fractal* Julia-set boundaries (non-preconnected lens)
  needs repelling-cycle / Koenigs theory not yet in the infrastructure.

---

## Suggested venue

Formalization track: **CPP / ITP / JAR**. The paper is a formalization contribution first (C1–C5 +
infrastructure, zero novelty-litigation risk); the cross-substitution independence (§7 item 2) is the
mathematical highlight and can anchor the introduction, stated with its scope caveat. A pure-math
companion note ("cross-substitution independence beyond the linear-Mahler frontier; the sharp
directional window `ρ_max = 2+√2`") becomes viable if the ADH-scope check is confirmed by a specialist.

## Sources (verified 2026-07-03)

- ray: <https://github.com/girving/ray>
- ADH: <https://arxiv.org/abs/2010.09266>
- Schäfke–Singer: <https://arxiv.org/abs/1605.02616>
- Nguyen Q6.2: <https://arxiv.org/abs/1310.2329>
- Saleh, bialgebraic Böttcher: <https://arxiv.org/abs/2606.24553>
- Costin–Huang, lacunary natural boundary: <https://arxiv.org/abs/0810.3027>
- Böttcher integrality (background): <https://arxiv.org/abs/1708.09275>
- Loeffler–Stoll, zeta/L in Lean: <https://arxiv.org/abs/2503.00959>
