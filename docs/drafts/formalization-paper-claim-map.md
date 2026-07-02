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
