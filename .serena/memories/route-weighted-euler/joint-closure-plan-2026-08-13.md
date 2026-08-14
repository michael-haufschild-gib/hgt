# weighted-euler-tangent-global-graph-decoupling — last card step (5c)

Card: `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/other/weighted-euler-tangent-global-graph-decoupling.md`.
All analytic content is closed (4c/8a unconditional).  **Only the joint capstone (3)/(18)/(19)
remains**, and it reduces to one hypothesis `helim` of the already-proved
`HTGeometry.topologicalClosure_primeQuadrantGraph_eq_top`:

```
helim : ∀ (f₁ : PrimeTangent →L[ℝ] ℝ) (f₂ : holoQuadrant →L[ℝ] ℝ),
  (∀ p : Nat.Primes, f₁ (primeTangentGen p) + f₂ (eulerTangentElement p) = 0) →
  ∀ y : holoQuadrant, f₂ y = 0
```

## Pre-existing assets (do NOT rebuild)
- `HTGeometry.PrimeQuadrantGraph`, `HTGeometry.QuadrantHolomorphic`, `HTGeometry.PrimeTangentSpace`,
  `HTGeometry.LocallyConvexDenseOfVanishingDual`, `HTGeometry.ContinuousMapLocallyConvex`.
- `RHTower.WeightedEulerGrowingCarrierElimination.compactFourierBorel_eq_zero_of_primeLog_graph_annihilation_critical`
  ⇒ `∀ m, L (s ^ m) = 0` from prime-indexed annihilation with `0 < α ≤ Re (s k) ≤ β < 1` and
  `‖lam p‖ ≤ C · criticalNorm (primeCoordinateField p)`.
- **Rectangle Cauchy formula is vendored**: `GaloisForLFunctions.PNTPlus.ResidueCalcOnRectangles`
  (root namespace: `RectangleIntegral`, `RectangleIntegral'`, `HIntegral`, `VIntegral`,
  `RectangleBorderIntegrable`, `ContinuousOn.rectangleBorder_integrable`,
  `ResidueTheoremInRectangle`, `ResidueTheoremOnRectangleWithSimplePole`,
  `HolomorphicOn.vanishesOnRectangle`) + `HTGeometry.RectangleResidueTheorem`;
  `Complex.Rectangle z w = [[z.re,w.re]] ×ℂ [[z.im,w.im]]` is mathlib.
  A duplicate winding-number/CIF pair was written and deleted 2026-08-13 — never rebuild it.

## Built 2026-08-13 — 9 modules, compiling, axiom-clean, umbrella-wired
(`formal/GaloisForLFunctions/HTGeometry/`, namespace `GaloisForLFunctions.HTGeometry` unless noted;
all appended to `GaloisForLFunctions/HTGeometry.lean`; `formal_tools.py lint` shows no findings for
them — the 36 lint errors in the tree are other agents' unreachable modules.)

1. `CompactOpenDualCarrier.lean` (ns `HTGeometry`) — `exists_compact_dual_bound`.
2. `FactorThroughRange.lean` — `rangePreim`, `factorRange`, `factorRange_apply_of_eq`,
   `factorRangeCLM`, `factorRangeCLM_apply_of_eq`.
3. `CarrierComplexFunctional.lean` — **`exists_complex_functional_of_bound`**.
4. `QuadrantReflectedCarrier.lean` — `rect`, `doubledRect`,
   `exists_rect_of_isCompact_subset_criticalQuadrant`, `conj_mem_doubledRect`,
   `isPreconnected_compl_rect`, `midStrip`.  HAZARD: use `open _root_.HTGeometry`.
5. `QuadrantRestrictionSchwarz.lean` — `quadrantRestrict`, `feEulerTangent_conj`.
6. `ContinuousMapCauchyTransform.lean` — `coordMap`, `kernelFun`, `resolventElt`,
   `resolventUnit`, `cauchyTransform`, `resolventInv`, `resolventInv_eq`,
   `differentiableAt_resolventInv`, `continuousOn_resolventInv`,
   `analyticOnNhd_cauchyTransform`, `norm_cauchyTransform_le`, `tsum_geometricKernel_eq`,
   `cauchyTransform_eq_zero_of_lt`.
7. `ReflectedCarrierFunctional.lean` — `precompCLM`, `inclMap`, `conjMap`, `sigmaMap`,
   `doubledFunctional`, `doubledFunctional_apply_of_sigma_eq`,
   `cauchyTransform_doubledFunctional`; `Transfer` section: `conjTransferMap`, `sigmaTransfer`,
   `conjFunctional` (arg `hmap : ∀ z ∈ K₂, conj z ∈ K₁`), `cauchyTransform_conjFunctional`.
8. `CauchyTransformGluing.lean` — `glueStrip`, `differentiable_glueStrip`,
   `norm_cauchyTransform_le_of_far`, **`cauchyTransform_eq_zero_of_glue`**.
9. `CarrierAnnihilatesHolomorphic.lean` — **`clm_rectangleIntegral`** (a CLM commutes with
   `RectangleIntegral`, given `RectangleBorderIntegrable`), `cauchyFamily K G v = G v • resolventInv K v`,
   `cauchyFamily_apply`, `continuousOn_cauchyFamily`.

## NEXT (exactly two things)

**(N1) DONE 2026-08-13.**  `CarrierAnnihilatesHolomorphic.lean` now also has
`notMem_of_horizontal_side`, `notMem_of_vertical_side`, `mem_rectangle_of_side`,
`rectangleBorderIntegrable_cauchyFamily`, `rectangleIntegral_cauchyKernel`
(the rectangle Cauchy formula in boundary-integral normalisation, from the vendored
`ResidueTheoremOnRectangleWithSimplePole`), `rectangleIntegral_congr_off`, and the capstone
**`apply_eq_zero_of_cauchyTransform_eq_zero`**:
`IsOpen U`, `DifferentiableOn ℂ G U`, `Complex.Rectangle z₁ z₂ ⊆ U`, `K` strictly inside the
rectangle, `L : C(K,ℂ) →L[ℂ] ℂ` with `∀ v ∉ K, cauchyTransform L v = 0`, and `gK : C(K,ℂ)` with
`gK z = G z` ⇒ `L gK = 0`.  Axiom-clean.

### N1-EXTRAS ALSO DONE 2026-08-13 (all compiling, umbrella-wired)
- `CauchyTransformGluingVertical.lean` — `glueVert`, `differentiable_glueVert`,
  **`cauchyTransform_eq_zero_of_glue_re`** (vertical twin, thresholds `c₁ < c₂`:
  `Kc ⊆ {Re ≥ c₂}`, `Kc' ⊆ {Re ≤ c₁}`).
- `QuadrantReflectedCarrier.lean` += `compl_doubledRect_eq`,
  **`isPreconnected_compl_doubledRect`** (needs `0 < c`, `c ≤ d`).
- `ReflectedCarrierFunctional.lean` += `feReflMap`, **`feReflFunctional`**,
  `one_sub_notMem_of_notMem`, `precompCLM_feReflMap_kernelFun`,
  **`cauchyTransform_feReflFunctional`** (`Ĉ_{R_*L}(v) = -Ĉ_L(1-v)`), and
  **`cauchyTransform_comp_precompCLM`** (transform unchanged by restricting from a larger carrier).

### INTERFACE BRIDGE BUILT 2026-08-13
`formal/GaloisForLFunctions/RHTower/WeightedEulerCarrierTangent.lean` (wired into
`GaloisForLFunctions/RHTower.lean`, compiling):
`norm_compactExponentialTest_coordMap_lt_one` (contractive test on a carrier with `α ≤ Re`),
**`compactPrimeEulerUnitTangent_coordMap`** (`compactPrimeEulerUnitTangent (coordMap K) p k
= primeEulerUnitTangent p k`), and the two `rfl` identifications
`primeEulerUnitTangent_eq_eulerTangent`, `primeEulerUnitFETangent_eq_feEulerTangent`
(so `RHTower.primeEulerUnitFETangent = HTGeometry.feEulerTangent = u_p`, confirming the finding
below).

### INTERFACE FINDING (2026-08-13, must be handled in N2)
`RHTower.compactPrimeEulerUnitTangent s p` evaluates to `primeEulerUnitTangent p (s k)` — the
**non-symmetrised** tangent `w_p(s) = (log p)·p^{-s}/(1-p^{-s})²`, i.e. `HTGeometry.eulerTangent`.
The card's graph generator is the FE-symmetrised `u_p = w_p(s) - w_p(1-s)`
(`HTGeometry.feEulerTangent` = `RHTower.primeEulerUnitFETangent`).
So the functional fed to the carrier elimination must be
`B := A - R_*A` with `R s = 1 - s` and `(R_*A) h := A (h ∘ R)`, because
`A (u_p) = (A - R_*A) (w_p) = B (w_p)`.
Carrier of `B`: `Ktot := Kt ∪ R '' Kt` where `Kt = doubledRect a b c d`; since `1/2 < a ≤ b < 1`,
`R '' Kt` has real parts in `[1-b, 1-a] ⊆ (0, 1/2)`, so `Ktot ⊆ {1-b ≤ Re ≤ b}` with
`0 < 1-b` and `b < 1` — exactly the `0 < α ≤ Re ≤ β < 1` the elimination needs.
Cauchy transforms: `Ĉ_{R_*A}(v) = -Ĉ_A(1-v)`, so `Ĉ_B(v) = Ĉ_A(v) + Ĉ_A(1-v)`.
Consequently the assembly needs **two** separations, and therefore a second gluing lemma:
a *vertical-strip* analogue of `cauchyTransform_eq_zero_of_glue` (same proof with `re`/`im`
exchanged: carriers in `{Re ≥ α'}` and `{Re ≤ -α'}` after translating the critical line to `0`),
used first to pass from `Ĉ_B ≡ 0` to `Ĉ_A ≡ 0` off `Kt` (separation across the critical line),
and then the existing horizontal one to pass from `Ĉ_A ≡ 0` to `Ĉ_L ≡ 0` off `Kc`
(separation across the real axis).  Build `CauchyTransformGluingVertical.lean` by mirroring
`CauchyTransformGluing.lean`, or better: generalize the existing file to an arbitrary real-linear
separating functional (`fun z => z.im` and `fun z => z.re - 1/2`).

### ASSEMBLY PIECE 1 DONE 2026-08-13
`formal/GaloisForLFunctions/RHTower/WeightedEulerCarrierSetup.lean` (wired, compiling):
`structure QuadrantCarrierData (f₂ : holoQuadrant →L[ℝ] ℝ)` bundling
`a b c d`, `1/2 < a`, `a ≤ b`, `b < 1`, `0 < c`, `c ≤ d`, `hquad : rect a b c d ⊆ criticalQuadrant`,
`L : C(rect a b c d, ℂ) →L[ℂ] ℂ`, and `hL : ∀ g, (L (quadrantRestrict hquad g)).re = f₂ g`; plus
**`exists_quadrantCarrierData`** producing one.  (Needs
`set_option maxHeartbeats 1000000` and explicit `(M := ↥holoQuadrant) (K := ↥(rect a b c d))` on
`exists_complex_functional_of_bound`, else `whnf` times out.)
Also added `norm_le_of_mem_rect` in `QuadrantReflectedCarrier.lean` (explicit `‖z‖` bound).

### ASSEMBLY PIECE 1b DONE 2026-08-13 — `WeightedEulerCarrierBlocks.lean` (wired, compiling)
In `namespace RHTower.QuadrantCarrierData`, for `D : QuadrantCarrierData f₂`:
`D.Kc = rect a b c d`, `D.Kcbar = rect a b (-d) (-c)`, `D.Kt = doubledRect a b c d`,
`D.Kt' = doubledRect (1-b) (1-a) c d`, `D.Ktot = D.Kt ∪ D.Kt'`, with
`half_lt_b`, `one_sub_b_pos`, `one_sub_a_lt_a`, `one_sub_b_le_a`, `one_sub_a_le_b`,
compactness of all five, **`CompactSpace` instances for all five**,
`Kc_subset_Kt`, `Kt_subset_Ktot`, `Kt'_subset_Ktot`, `conj_mem_Kt`, `conj_mem_Kcbar`,
`Kc_im`, `Kcbar_im`, `Kt_re`, `Kt'_re`, **`one_sub_mem_Kt'`** (`z ∈ Kt → 1 - z ∈ Kt'`),
`Ktot_re` (`1-b ≤ Re ≤ b`), `norm_le_of_mem_Ktot` (explicit radius).

### ASSEMBLY PIECE 2a DONE 2026-08-13 — `WeightedEulerCarrierFunctionals.lean` (wired, compiling)
In `namespace RHTower.QuadrantCarrierData`: `D.Lc = D.L` (retyped on `D.Kc`),
**`D.doubled`** (`doubledFunctional` across the real axis, on `D.Kt`),
**`D.reflected`** (`feReflFunctional` across the critical line, on `D.Kt'`),
**`D.total`** (`doubled ∘ precomp - reflected ∘ precomp`, on `D.Ktot`), with
`cauchyTransform_doubled` (`= Ĉ_Lc v + conj (Ĉ_Lc (conj v))`),
`cauchyTransform_reflected` (`= -Ĉ_doubled (1-v)`), and
**`cauchyTransform_total`** (`= Ĉ_doubled v + Ĉ_doubled (1-v)`).

### ASSEMBLY PIECE 2b-i DONE 2026-08-13 — `WeightedEulerCarrierGraph.lean` (wired, compiling)
`D.Kt_re_pos`, `D.Kt_re_lt_one`, **`D.feTangentKt hp : C(D.Kt, ℂ)`** (the symmetrised Euler
tangent on the right pair of blocks) and **`D.sigmaMap_feTangentKt`** (conjugation fixes it —
the hypothesis `doubledFunctional_apply_of_sigma_eq` consumes).
Also DONE in this file: `precompCLM_feTangentKt` and **`total_feTangent`**:
`(hval : ∀ z : D.Ktot, h z = eulerTangent p z) → D.total h = ((2 * f₂ (eulerTangentElement p) : ℝ) : ℂ)`.
LEAN NOTE: finish with `exact congrArg (fun r : ℝ => ((2 * r : ℝ) : ℂ)) (D.hL (eulerTangentElement p))`
— do NOT `simp only [Lc]` first, that unfolds `D.Kc` to `rect …` and breaks the `ContinuousLinearMap`
instance match.
**ALSO DONE**: `mem_Ktot_corner` and **`total_coord_pow_eq_zero`**:
`(hgr : ∀ p : Nat.Primes, f₁ (primeTangentGen p) + f₂ (eulerTangentElement p) = 0) →
∀ m, D.total (coordMap D.Ktot ^ m) = 0` — the carrier elimination is DISCHARGED
(`lam n := if h : n.Prime then ((2 * f₁ (primeTangentGen ⟨n,h⟩) : ℝ) : ℂ) else 0`,
`C := 2 * ‖f₁‖`, `α := 1 - D.b`, `β := D.b`).
So the only remaining steps for the card are: far-field vanishing + strip identity theorem +
the two gluings ⇒ `∀ v ∉ D.Kc, cauchyTransform D.Lc v = 0`; then
`apply_eq_zero_of_cauchyTransform_eq_zero` ⇒ `helim` ⇒ (3)/(18)/(19) ⇒ promote.
Superseded sketch:
```
theorem total_feTangent (p : Nat.Primes) (h : C(D.Ktot, ℂ))
    (hval : ∀ z : D.Ktot, h z = eulerTangent p (z : ℂ)) :
    D.total h = ((2 * f₂ (eulerTangentElement p) : ℝ) : ℂ)
```
proof sketch: `hsplit : precompCLM (inclMap D.Kt_subset_Ktot) h
  - precompCLM (feReflMap _) (precompCLM (inclMap D.Kt'_subset_Ktot) h) = D.feTangentKt hp`
(by `ext` + `hval`, since `feEulerTangent p z = eulerTangent p z - eulerTangent p (1 - z)` is `rfl`);
then `total`, `map_sub`, `doubledFunctional_apply_of_sigma_eq _ _ _ (D.sigmaMap_feTangentKt hp)`,
then `precompCLM (inclMap D.Kc_subset_Kt) (D.feTangentKt hp)
  = quadrantRestrict D.hquad (eulerTangentElement p)` by `ext`, and finally `D.hL`.

### PITFALL noted 2026-08-13 for piece 2b
The symmetrised tangent restricted to `D.Kt` needs a `C(D.Kt, ℂ)` bundle
`feTangentKt p := ⟨fun z => feEulerTangent p z, _⟩`.  Its continuity CANNOT come from
`differentiableOn_feEulerTangent` (that is stated on `criticalQuadrant`, and `D.Kt` dips into the
lower half plane).  Use instead: `(differentiableOn_eulerTangent hp).continuousOn` on `{0 < re}`
for the first term, and its composition with `z ↦ 1 - z` (mapping `{re < 1}` into `{0 < re}`) for
the second, then `.sub` and `.restrict`; `D.Kt ⊆ {0 < re} ∩ {re < 1}` follows from
`Kt_re`/`Ktot_re` with `0 < 1 - b` and `b < 1`.  A first draft that tried the quadrant route was
deleted unbuilt.

### ASSEMBLY PIECE 2b (next) — `WeightedEulerCarrierVanishing.lean`
Goal: from `D : QuadrantCarrierData f₂`, `f₁`, and the graph relation, prove
`∀ v ∉ D.Kc, cauchyTransform D.Lc v = 0`.
Concrete steps (all inputs proved):
* graph: `compactPrimeEulerUnitTangent_coordMap` (α := 1-b) rewrites the elimination's generator to
  `primeEulerUnitTangent p ·`; `map_sub` turns `B` of it into `A (u_p|_Kt)`; then
  `doubledFunctional_apply_of_sigma_eq` (Schwarz reality via `feEulerTangent_conj`) and `hL` give
  `A (u_p|_Kt) = ((2 * f₂ (eulerTangentElement p) : ℝ) : ℂ)`.
  Take `lam p := ((2 * f₁ (primeTangentGen p) : ℝ) : ℂ)`, `C := 2 * ‖f₁‖`;
  `hdual` from `norm_primeTangentGen` + `criticalNorm_coordinate`.
* `compactFourierBorel_eq_zero_of_primeLog_graph_annihilation_critical` (α := 1-b, β := b) ⇒
  `∀ m, B (coordMap Ktot ^ m) = 0`.
* `cauchyTransform_eq_zero_of_lt` (r from `norm_le_of_mem_rect`) ⇒ `Ĉ_B` vanishes far out;
  identity theorem on the convex strip `{1-a < Re < a} ⊆ Ktotᶜ` ⇒ `Ĉ_B = 0` there.
* `cauchyTransform_comp_precompCLM` + `cauchyTransform_feReflFunctional` rewrite `Ĉ_B` as
  `Ĉ_A(v) - Ĉ_{A'}(v)`; feed `cauchyTransform_eq_zero_of_glue_re` (`c₁ := 1-a`, `c₂ := a`,
  `L₁ := A`, `L₂ := -A'`, `hpre := isPreconnected_compl_doubledRect`) ⇒ `∀ v ∉ Kt, Ĉ_A v = 0`.
* `cauchyTransform_doubledFunctional` + `cauchyTransform_conjFunctional` turn that, on
  `midStrip c ⊆ Ktᶜ`, into the `hagree` of `cauchyTransform_eq_zero_of_glue`
  (`Kc' := Kcbar`, `L' := conjFunctional _ L`, `hpre := isPreconnected_compl_rect`) ⇒ the goal.

### ASSEMBLY PIECE 3 — `WeightedEulerJointClosure.lean`
`weightedEuler_helim`: choose `a' ∈ (1/2, a)`, `b' ∈ (b, 1)`, `c' ∈ (0, c)`, `d' > d`, apply
`apply_eq_zero_of_cauchyTransform_eq_zero` with `U := criticalQuadrant`, `z₁ := a' + c'·I`,
`z₂ := b' + d'·I`, `gK := quadrantRestrict hquad y`, giving `L (quadrantRestrict hquad y) = 0`,
hence `f₂ y = 0`.  Then `(3) := topologicalClosure_primeQuadrantGraph_eq_top weightedEuler_helim`;
`(18)` the same statement for the generated group; `(19)` via
`dense_affine_of_topologicalClosure_eq_top`.  Then axiom audit, card update, `git mv` to stage 3.

**(N2) assembly** `WeightedEulerJointClosure.lean` (new module, RHTower or HTGeometry):
`exists_compact_dual_bound` → `exists_rect_of_isCompact_subset_criticalQuadrant` (gives
`Kc = rect a b c d`) → `exists_complex_functional_of_bound` with `T = quadrantRestrict`
(gives `L` with `(L (quadrantRestrict g)).re = f₂ g`) → `Kt = doubledRect a b c d`,
`A = doubledFunctional` → `A (compactPrimeEulerUnitTangent …) = 2 f₂(u_p) = -2 f₁(primeTangentGen p)`
via `doubledFunctional_apply_of_sigma_eq` + `feEulerTangent_conj` → critical carrier elimination ⇒
`∀ m, A (coordMap Kt ^ m) = 0` → `cauchyTransform_eq_zero_of_lt` off a big disc; identity theorem
(`AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero`) on the convex `midStrip c`
(⊆ `Ktᶜ`) ⇒ `cauchyTransform A = 0` there → rewrite by `cauchyTransform_doubledFunctional` and
`cauchyTransform_conjFunctional` to get the `hagree` of `cauchyTransform_eq_zero_of_glue`
(`Kc' = rect a b (-d) (-c)`, `L' = conjFunctional _ L`) ⇒ `∀ v ∉ Kc, cauchyTransform L v = 0`
→ (N1) ⇒ `f₂ g = 0` ⇒ `helim` → `topologicalClosure_primeQuadrantGraph_eq_top` = card `(3)`;
`(18)` the same for the generated group; `(19)` = `dense_affine_of_topologicalClosure_eq_top`.
Then `#print axioms`, update the card, `git mv` to
`docs/drafts/pipeline/3-formalized/new_scientific_knowledge/other/`, fix relative links.
