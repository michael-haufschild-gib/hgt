# Formalization-paper claim map — verified prior art and claim boundaries

`[SEARCH register — working note for a prospective ITP/CPP-style paper. Every citation below was
verified by actual search/fetch on 2026-07-02; nothing here is recalled-only.]`

## Verified prior art

1. **girving/ray** (Geoffrey Irving, Lean 4) — <https://github.com/girving/ray>.
   VERIFIED 2026-07-02 (README fetched). Formalizes: Böttcher's theorem (local analytic
   coordinate near a monic superattracting fixed point, with parameter analyticity), analytic
   continuation of the Böttcher map to the postcritical region, Multibrot/Mandelbrot
   connectedness, plus Hartogs, Grönwall area theorem, Koebe 1/4. **Contains nothing on
   transcendence, algebraic independence, natural boundaries, or value relations** — the
   development is topological/geometric. Our tree is independent of ray (no import).

2. **Nguyen, "Algebraic independence of local conjugacies and related questions in polynomial
   dynamics"**, arXiv:1310.2329 (math.NT, 2013). VERIFIED 2026-07-02 (PDF text extracted).
   `Question 6.2` exists verbatim: *(a) give a necessary and sufficient condition for the
   Böttcher coordinates φ₁,…,φₙ of disintegrated polynomials to be algebraically independent
   over K(t); (b) the value-independence question at algebraic points of large modulus.*
   Our q62 citation is sound; the tree formalizes quadratic instances of (a).

3. **Formalized transcendence corpus** (all number-transcendence, none function-field/germ):
   - mathlib: Liouville numbers are transcendental (Lean).
   - Jujian Zhang, transcendence of e in Lean —
     <https://jjaassoonn.github.io/transcendental/src/doc/main.pdf>.
   - Bernard–Bertot–Rideau–Théry, e and π transcendental in Coq — arXiv:1512.02791.
   - Eberl (Isabelle/HOL) e, π; Koutsoukou-Argyraki–Li–Paulson, irrationality and transcendence
     criteria for infinite series in Isabelle — arXiv:2101.05257.
   - Gelfond–Schneider theorem in Lean 4 — arXiv:2603.24823 (2026).
   - (Function-field-adjacent: Mason–Stothers in Lean 4, arXiv:2408.15180 — polynomial abc,
     not independence of transcendental functions.)

4. **Loeffler–Stoll, "Formalizing zeta and L-functions in Lean"** — arXiv:2503.00959; mathlib's
   `HurwitzZeta` (even/odd), analytic continuation + functional equation via `jacobiTheta2`.
   VERIFIED 2026-07-02. This is the ANALYTIC theory of Hurwitz zeta; our Hurwitz lane proves
   INDEPENDENCE-side statements (no-relation results for Hurwitz-type series families) — a
   complementary claim, no collision.

5. **Natural boundaries / algebraic independence of analytic germs in proof assistants**:
   searches (Lean/mathlib/Coq/Isabelle × natural boundary, algebraically independent germs,
   meromorphic germ fields) surfaced nothing. `[As of 2026-07-02; absence of evidence — phrase
   any paper claim as "to our knowledge", not as a theorem about the corpus.]`

## Claim map (what the paper may and may not claim)

**C1 — safe.** First machine-checked *transcendence* statements for Böttcher coordinates over
`ℂ(z)` (`bottcher_transcendental_far` and the window family `phiB_transcendental`, all
parameters `‖b‖ > 2+√2`). New relative to ray (topology only) and to the transcendence corpus
(numbers, not function germs).

**C2 — safe.** First formalized *algebraic independence* between a natural-boundary object
(`u₀`, boundary `|z| = 1`) and a dynamical coordinate, stated in a faithful carrier — the germ
field `meroField U = FractionRing (analyticSubring U)` — where `NoRelation` is a statement
about the actual functions. The carrier design + carrier-generic descent
(`kappaP`/`descend_algebraicP`) + assembly functor are themselves reusable contributions.

**C3 — safe, phrase carefully.** A machine-checked *sharpness pair*: coverage for all
`‖b‖ > 2+√2` AND an obstruction witness at `b = −(2+√2)` (`window_threshold_sharp`), plus the
direction-dependence pair at `b = ±3` (`window_dichotomy_modulus_three`). Formalized negative
results/optimality certificates are rare; claim as "to our knowledge the first formalized
sharp-threshold pair in complex dynamics".

**C4 — safe.** First formalized instances toward a NAMED open question in arithmetic dynamics
(Nguyen Question 6.2(a), quadratic family) — the q62 lane's theorems.

**Do NOT claim:** "first Böttcher formalization" (ray, 2023); "first formalized transcendence"
(numbers corpus since 2010s); "resolves Question 6.2" (instances only); novelty of the
analytic Hurwitz zeta theory (mathlib has it — our claim is independence-side only); the
Lindemann–Weierstrass analytic part also exists in Lean per the corpus search — avoid implying
generic transcendence machinery is new.

## Sources

- <https://github.com/girving/ray>
- <https://arxiv.org/abs/1310.2329>
- <https://arxiv.org/abs/2503.00959>
- <https://arxiv.org/abs/2603.24823>
- <https://arxiv.org/abs/1512.02791>
- <https://arxiv.org/abs/2101.05257>
- <https://arxiv.org/abs/2408.15180>
- <https://jjaassoonn.github.io/transcendental/src/doc/main.pdf>
- <https://www.cst.cam.ac.uk/seminars/list/212209>

---

## Check #1 — cross-substitution Mahler independence (verified 2026-07-03)

Question: does existing difference-Galois / Mahler theory already give `u₀ ⟂ φ_b`, where u₀ is under
the monomial substitution `z↦z²` (a linear Mahler eqn) and φ_b is under the nonlinear dynamical
`z↦z²+b` (nonlinear eqn `φ_b(z²+b)=φ_b(z)²`)?

**Verdict: NO — the pair is outside the frontier of the state-of-the-art. Novelty claim survives.**

6. **Adamczewski–Dreyfus–Hardouin(–Wibmer), "Algebraic independence and linear difference equations"**
   — arXiv:2010.09266 (JEMS). VERIFIED 2026-07-03 (abstract fetched). THE state-of-the-art for
   cross-substitution independence: pairs of operators `(φ,σ)` including **Mahler** `φ:x↦x^{p₁},
   σ:x↦x^{p₂}`; solutions `f` (φ-linear) and `g` (σ-linear), both transcendental, are alg. independent
   over ℂ(x) if the parameters are sufficiently independent (settles Loxton–van der Poorten). **SCOPE
   (verified by fetch):** equations must be **LINEAR**; operators must be **MONOMIAL** (shift `x+h`,
   q-dilation `qx`, Mahler `x^p`). "Arbitrary nonlinear substitutions like `x↦x²+b` are not
   addressed." ⟹ φ_b (nonlinear eqn, non-monomial substitution `z²+b`) is DOUBLY outside ADH; the
   natural-boundary method reaching `u₀⟂φ_b` is a genuine bridge beyond difference-Galois theory.

7. **Schäfke–Singer, "Consistent systems of linear differential and difference equations"** —
   arXiv:1605.02616. VERIFIED 2026-07-03. Linear systems + consistency hypothesis; Mahler among the
   operators; hypertranscendence via Galois theory. Same LINEAR/MONOMIAL restriction — does not reach
   `(z↦z², z↦z²+b)`.

8. **Saleh, "Bialgebraic geometry of Böttcher coordinates"** — arXiv:2606.24553 (2026). VERIFIED
   2026-07-03 (abstract fetched). Ax–Lindemann / Ax–Schanuel functional-transcendence classification
   of a SINGLE Böttcher coordinate `Ψ_f` (f-bialgebraic sets). NO parameter-derivative/c-velocity, NO
   Mahler pairing, NO natural-boundary method. Complementary to our `u₀=∂_c φ ⟂ φ_b` — no collision.
   (Note: relevant to CITE for single-coordinate Böttcher functional transcendence.)

9. **Costin–Huang, "Behavior of lacunary series at the natural boundary"** — arXiv:0810.3027 (Adv.
   Math.). VERIFIED 2026-07-03. Analytic behavior of lacunary series (u₀'s class) AT the natural
   boundary; background for the boundary side, NOT an algebraic-independence result.

**Refined claim C2′ (novelty-bearing, labelled [CONJECTURE] pending referee):** the joint independence
`u₀ ⟂ φ_b` under DIFFERENT substitutions (monomial Mahler `z↦z²` vs. nonlinear dynamical `z↦z²+b`)
is beyond the linear/monomial frontier of ADH/Schäfke–Singer; the natural-boundary obstruction reaches
it precisely because it is substitution-agnostic. Referee action: confirm no ADH follow-up extends to
nonlinear dynamical substitutions.

## Sources (added 2026-07-03)
- <https://arxiv.org/abs/2010.09266>  (ADH — algebraic independence & linear difference equations)
- <https://arxiv.org/abs/1605.02616>  (Schäfke–Singer — consistent systems)
- <https://arxiv.org/abs/2606.24553>  (Saleh — bialgebraic geometry of Böttcher coordinates)
- <https://arxiv.org/abs/0810.3027>   (Costin–Huang — lacunary series at natural boundary)
