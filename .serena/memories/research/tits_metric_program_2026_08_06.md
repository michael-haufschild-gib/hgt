# Tits metric across apartments — COMPLETE 2026-08-06

**The programme below is finished.**  `TitsDivergenceRate.lean` closes it:
`tendsto_rayDist_div` (the divergence rate exists for arbitrary directions), `titsRate` (the Tits
distance), `titsRate_diagOp` (inside an apartment it is the chordal distance, so it extends the
flat metric).  Supporting: `ObserverHomothety.lean` (`observerDist_metricRay_smul_le`),
`CompoundHomothety.lean`, `CompoundExponentialTransport.lean`, `CompoundExponential.lean`,
`CompoundOperatorOrder.lean`, `CordesGeneralExponent.lean`.

With it the card's `2 -> 3` gate is closed and the card moved to
`docs/drafts/pipeline/3-formalized/new_scientific_knowledge/projective-horizon/`.
Only `3 -> 4` (external audit) remains, which is not a Lean task.

The rest of this file is the record of how it was built — keep it for the traps section.

# Tits metric across apartments — the last item of gate 2 -> 3

Card: `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/projective-horizon/projective-ht-horizon-symmetric-space-boundary.md`

Everything else on the card is formalized (19 modules).  The basepoint change closed on
2026-08-06 (`BasepointChange.lean`, `MovedRayPencil.lean`).  **Only one item is left**:

> the Tits metric between boundary points of *different* apartments

## What the statement reduces to

For unit traceless directions `T, S` put `f t = observerDist (exp (t T)) (exp (t S))`.
The Tits distance of the two boundary points is the divergence rate `lim_{t→∞} f t / t`
(Bridson–Haefliger II.9.8: the angle satisfies `2 sin (∠/2) = lim f t / t`).

Two halves:

- **Bounded**: `f t ≤ 2 t` — immediate from the triangle inequality (already formalized) and
  `observerDist_metricRay` (`d (I, exp (t T)) = t ‖T‖`).  **This half is free.**
- **Monotone**: `f t / t` is nondecreasing.  Equivalent to the geodesic homothety contraction

  ```text
  d (exp (λ X), exp (λ Y)) ≤ λ · d (exp X, exp Y),    λ ∈ [0,1].          (H)
  ```

Monotone + bounded ⟹ the limit exists, for *arbitrary* directions, i.e. across apartments.
Inside an apartment `observerDist_metricRay_diagOp_unit` already gives
`f t = |t| √(2 − 2 ⟪w, w'⟫)`, so the rate is `2 sin (θ/2)` and the Tits metric *extends* the
chordal metric already computed.  That is the whole item.

## The route to (H) — four steps, all mechanical given what exists

`(H)` is Araki–Lieb–Thirring plus Karamata, and every ingredient is already in the corpus.

1. **Cordes for a general exponent.  DONE 2026-08-06** —
   `CordesGeneralExponent.lean`, `norm_exp_smul_mul_exp_smul_le`:
   `‖exp (s x) * exp (s y)‖ ≤ ‖exp x * exp y‖ ^ s` for self-adjoint `x, y`, `s ∈ [0,1]`.
   Also `exp_rpow : (exp x) ^ s = exp (s • x)` (needs `0 ≤ s`), `exp_smul_one`, `exp_smul_sub`.
   The trick that made it work: absorb the normalising scalar into the exponent
   (`z = (log c) • 1 - y`), so the functional calculus only ever sees exponentials and no
   scalar-versus-rpow algebra is needed.

2. **Araki–Lieb–Thirring as log-majorization.  NEXT.**  With
   `B_λ = exp (-λX/2) exp (λY/2)` and `A_λ = B_λ B_λ*` the pencil of the two rays at time `λ`,
   the identity `‖Λ^k A_λ‖ = ‖Λ^k B_λ‖²` plus step 1 *applied on the k-th compound* gives

   ```text
   ‖Λ^k A_λ‖ = ‖Λ^k B_λ‖² ≤ ‖Λ^k B_1‖^{2λ} = ‖Λ^k A_1‖^λ,
   ```

   i.e. `∏_{i≤k} λ_i (A_λ) ≤ (∏_{i≤k} λ_i (A_1))^λ`.  Two things are needed to run step 1 there:

   - **(a) the compound algebra must be a C\*-algebra.**  CONFIRMED: `Matrix κ κ ℂ` has a global
     `ContinuousFunctionalCalculus ℝ _ IsSelfAdjoint` instance (mathlib
     `Analysis/Matrix/HermitianFunctionalCalculus.lean`) but **no `PartialOrder` and no
     `StarOrderedRing`** — so the order lemmas cannot be used on matrices.  Work on the CLM side:
     `EuclideanSpace ℂ κ →L[ℂ] EuclideanSpace ℂ κ` has every instance
     (`CStarAlgebra`, `PartialOrder`, `StarOrderedRing`, `NormOneClass`) once
     `Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap` is imported — this is exactly what
     `ExponentialMetricIncreasing.lean` already relies on for `E →L[ℂ] E`.  Move compounds there
     along `Matrix.toEuclideanCLM`, a `StarAlgEquiv`; `Matrix.toEuclideanCLM_toLp` and
     `ofLp_toEuclideanCLM` are both `rfl`, and `EuclideanSpace.inner_eq_star_dotProduct` connects
     the inner product to `matQuadForm`.
   - **(b) `Λ^k (exp W) = exp (D_k W)` with `D_k W` self-adjoint.**  Do NOT build the derivation
     abstractly (`Λ^k` is multiplicative, not additive).  Diagonalise: `W = U D U*` gives
     `Λ^k (exp W) = (Λ^k U) (Λ^k (exp D)) (Λ^k U)*` by `compound_mul` and
     `compound_conjTranspose`, and `Λ^k (exp D)` is by `compound_diagonal` the diagonal of the
     subset products `∏_{i∈S} e^{d i} = e^{∑_{i∈S} d i}`.  So `D_k W := (Λ^k U) E (Λ^k U)*`
     with `E` the real diagonal of subset sums — visibly self-adjoint.

   `CompoundKyFan.lean` is the model for the *shape* of the argument, but note its mechanism is
   quadratic-form comparison, which gives multiplicative constants only.  ALT needs the exponent,
   so it must go through the operator norm and step 1, not through that file's method.

   **The order form of step 1 is already proved** (2026-08-06): `exp_smul_le_of_exp_le` in
   `CordesGeneralExponent.lean` gives `exp y ≤ c exp x → exp (s y) ≤ c^s exp (s x)` from Löwner–
   Heinz alone, no norms.  Applied in the compound algebra with the two `CompoundKyFan` lemmas
   (`compound_quadForm_le` produces the hypothesis at time 1 from a products bound,
   `prod_le_of_compound_quadForm_le` reads the conclusion at time λ back as a products bound),
   this *is* the ALT step.  So what remains of step 2 is only (a) the CLM/`matQuadForm`
   dictionary and (b) the compound-exponential identity.
   Useful mathlib names, verified: `Matrix.exp_diagonal`, `Matrix.exp_conj` (needs `IsUnit U`),
   `Matrix.IsHermitian.spectral_theorem`.  Corpus side: `compound_mul`, `compound_conjTranspose`,
   `compound_diagonal`, `compound_unitary`, `compound_rdiag`.

3. **Turn log-majorization into (H).**  Take logs: `log λ(A_λ) ≺ λ · log λ(A_1)` with equal
   totals (both are `λ (tr Y − tr X)`, so it is genuine majorization, not just weak).  Then
   Karamata for the square.  **Karamata is FREE here** — no new work:
   instantiate the existing `sqrt_sum_sq_le_of_topSum_le` with `b := λ • b` and `c := 0`.  Its
   hypothesis `topSum m a ≤ topSum m b + topSum m c` becomes `topSum m a ≤ λ · topSum m b`, and
   its conclusion `√∑a² ≤ √∑b² + √∑c²` becomes `√∑a² ≤ λ √∑b²`.

4. **Assemble.**  `(H)` ⟹ `f t / t` nondecreasing ⟹ with `f t ≤ 2 t` the limit exists.
   Define `titsDist` as that limit, prove it is the chordal value in a flat.

## Traps

- Löwner–Heinz in mathlib is `CFC.rpow_le_rpow` on a C*-algebra, so steps 1–2 live in
  `E →L[ℂ] E` / `A`, **not** in the corpus's `E →ₗ[ℂ] E` + `IsSymmetric` world.  A bridge is
  needed at step 3 (`sqrtOp`/`invOp`/`logOp` ↔ CFC).  Check `PolarTransportUnitary.lean`,
  `CfcEigenvector.lean`, `CfcNormBound.lean` — the corpus already uses CFC in several places;
  reuse whatever bridge is there before writing a new one.
- Step 1 needs `b` invertible.  Everything applied is an exponential, so it *is* invertible —
  state it for invertible arguments rather than fighting a perturbation argument.

## Dead ends already ruled out (do not retry)

- Bhatia's Riemannian proof of NPC — needs the Fréchet derivative of the operator exponential,
  absent from mathlib.
- Proving the divergence-rate limit by sub/superadditivity of `f`: `f` is neither, and the
  factorisation `e^{(s+t)X} e^{(s+t)Y} = e^{sX} (e^{tX} e^{sY}) e^{tY}` leaves mixed terms.
- Golden–Thompson in the naive direction: it bounds `‖e^{X+Y}‖` from above, which is the wrong
  side for the metric-increasing statement.  The usable direction is
  `‖e^{x+y}‖ = ‖e^{(x+y)/2}‖² ≤ ‖e^{x/2} e^{y/2}‖²`, from the existing `norm_exp_add_le`.

## Names verified against this toolchain (2026-08-06)

`GoldenThompsonNorm.lean` already imports both files these live in, so step 1 needs no new import:

- `CFC.rpow_le_rpow : p ∈ Set.Icc 0 1 → a ≤ b → a ^ p ≤ b ^ p`  — Löwner–Heinz, exactly the
  shape step 1 wants, and it takes no separate `0 ≤ a` argument.
- `CFC.rpow_rpow`, `CFC.rpow_def`, `CFC.rpow_natCast`, `CFC.rpow_one`, `CFC.rpow_neg`,
  `CFC.sqrt_eq_rpow` all exist.
- `CFC.rpow_mul` and `CFC.rpow_two` do **not** exist — use `CFC.rpow_rpow` and
  `CFC.rpow_natCast`.
- `Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog` cannot be imported:
  its olean has an incompatible header in this build.  So the bridge `(exp x) ^ p = exp (p • x)`
  must be derived from `cfc_comp` rather than from a ready-made `exp`/`rpow` lemma there.

The existing `norm_exp_half_mul_exp_half_sq_le` proof is the exact template for the general
exponent: conjugate by `exp (-y)`, take the root, conjugate back by `exp (y/2)`.  Only its third
step changes — `CFC.sqrt_le_sqrt` becomes `CFC.rpow_le_rpow` at exponent `s`.


## Progress log

- **Step 1 DONE** 2026-08-06 — `CordesGeneralExponent.lean`.  Both the norm form
  (`norm_exp_smul_mul_exp_smul_le`) and, more usefully, the **order form**
  (`exp_smul_le_of_exp_le`): `exp y ≤ c exp x → exp (s y) ≤ c^s exp (s x)`.
- **Step 2 plumbing DONE** 2026-08-06 —
  - `CompoundOperatorOrder.lean`: `toEuclideanCLM_le_iff` is the dictionary between
    `matQuadForm` comparison (the language of `CompoundKyFan`) and `≤` in the CLM C\*-algebra
    (the language of the functional calculus).  Plus `matQuadForm_eq_inner`, `re_inner_swap`,
    `isSelfAdjoint_toEuclideanCLM`, `matQuadForm_sub`.
  - `CompoundExponential.lean`: `compound_conj_rdiag_exp` — the compound of an exponential ray is
    an exponential ray, `Λᵏ (Vᴴ diag(exp (t w)) V) = (Λᵏ V)ᴴ diag(exp (t σ)) (Λᵏ V)`, `σ` the
    subset sums.  Plus `compoundGen` (the induced generator, `t`-independent),
    `isHermitian_compoundGen`, `exp_smul_rdiag`, `rdiag_conjTranspose`,
    `isHermitian_conj_rdiag'`, `compound_conjTranspose_mul_self`,
    `compound_mul_conjTranspose_self`.

## What is left, precisely

**Steps 1 and 2 are DONE** (2026-08-06).  The log-majorization is
`quadForm_compound_expRay_le` in `CompoundHomothety.lean`:

```text
Λᵏ Q₁ ≤ c Λᵏ P₁   →   Λᵏ Q_t ≤ c ^ t Λᵏ P_t      (0 ≤ t ≤ 1)
```

for exponential rays `P_t = Vᴴ diag(exp (t p)) V`, `Q_t = Wᴴ diag(exp (t q)) W`, stated as a
comparison of Hermitian forms so it plugs straight into the two Ky Fan lemmas.  Supporting:
`CompoundExponentialTransport.lean` (`toEuclideanCLM_exp`, `isometry_toEuclideanCLM`),
`CompoundExponential.lean`, `CompoundOperatorOrder.lean`
(`toEuclideanCLM_le_iff`, `toEuclideanCLM_smul_le_iff`, `exp_smul_le_of_exp_le_clm`).

**Step 3 is DONE** (2026-08-06): `observerDist_metricRay_smul_le` in `ObserverHomothety.lean`
is `(H)` itself — `d (exp (λT), exp (λS)) ≤ λ d (exp T, exp S)` for `λ ∈ [0,1]`.  Karamata in
scaled form is `sqrt_sum_sq_le_smul_of_topSum_le`; the totals come from
`prod_relOp_eigenvalues_metricRay` (the product of the relative spectrum along a ray is
`exp (t (tr S - tr T))`).

**Remaining: step 4 only.**

(iv) the limit — `f t / t` nondecreasing (from `(H)`) and `≤ 2` (triangle inequality) gives the
  divergence rate; define `titsDist`; check it against `observerDist_metricRay_diagOp_unit`
  inside an apartment.

## Hard-won traps

- **Missing `StarOrder` import causes a runaway, not an error.**  Instantiating the abstract C\*
  contraction at an operator algebra hits a `whnf` heartbeat timeout unless
  `Mathlib.Analysis.InnerProductSpace.StarOrder` is imported (it carries
  `StarOrderedRing (E →L[𝕜] E)`).  Symptom looks like a defeq blowup; raising `maxHeartbeats`
  does not help.  `Mathlib.Analysis.InnerProductSpace.Positive` alone is not enough — it gives the
  Loewner `PartialOrder` but not the `StarOrderedRing`.
- `CFC.rpow_def` is stated over `ℝ≥0`; the real-valued form is `CFC.rpow_eq_cfc_real` (takes
  `0 ≤ a`).
- `Complex.coe_smul` may fail to rewrite across instance paths; restate it once as a local lemma
  proved by `exact Complex.coe_smul _ _` (defeq is accepted where `rw` matching is not), then
  rewrite with the local version.
