# weighted-euler-tangent-global-graph-decoupling — the last card step (5c) and its plan

Card: `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/other/weighted-euler-tangent-global-graph-decoupling.md`.
Everything analytic is closed (4c/8a unconditional). **Only the joint capstone (3)/(18)/(19) remains.**

## What already exists (do not rebuild)
- `HTGeometry.PrimeQuadrantGraph`: `primeQuadrantGen`, `primeQuadrantGraph`, and
  `topologicalClosure_primeQuadrantGraph_eq_top` — **already reduces (3) to one hypothesis**
  `helim : ∀ f₁ f₂, (∀ p, f₁ (primeTangentGen p) + f₂ (eulerTangentElement p) = 0) → ∀ y, f₂ y = 0`.
- `HTGeometry.QuadrantHolomorphic`: `criticalQuadrant`, `holoQuadrant` (ℝ-submodule of
  `C(criticalQuadrant, ℂ)`), `feEulerTangent`, `differentiableOn_feEulerTangent`.
- `HTGeometry.PrimeTangentSpace`: `PrimeTangent = lp (fun _ : Nat.Primes => ℝ) 1`,
  `primeTangentGen`, `primeTangent_eq_zero_of_forall_gen`.
- `HTGeometry.LocallyConvexDenseOfVanishingDual`, `HTGeometry.ContinuousMapLocallyConvex`
  (compact-open basis + `LocallyConvexSpace ℝ C(X,ℂ)`).
- `RHTower.WeightedEulerGrowingCarrierElimination.compactFourierBorel_eq_zero_of_primeLog_graph_annihilation_critical`
  — for `L : C(K,ℂ) →L[ℂ] ℂ`, `s : C(K,ℂ)` with `0 < α ≤ Re (s k) ≤ β < 1`, prime-indexed
  annihilation and `‖lam p‖ ≤ C·criticalNorm (primeCoordinateField p)` give
  `compactFourierBorel L s ≡ 0` and `∀ m, L (s^m) = 0`.
- **RECTANGLE CAUCHY FORMULA ALREADY EXISTS** in the vendored area
  `GaloisForLFunctions.PNTPlus.ResidueCalcOnRectangles`:
  `RectangleIntegral`, `RectangleIntegral'`, `ResidueTheoremInRectangle`,
  `ResidueTheoremOnRectangleWithSimplePole`, plus `HolomorphicOn.vanishesOnRectangle`.
  `HTGeometry.RectangleResidueTheorem` extends it to poles of any order.
  Do NOT rebuild the rectangle winding number or CIF (a duplicate was written and deleted
  2026-08-13).

## Plan for `helim` (designed, not yet built)
1. **Carrier.** Continuity of `f₂ : holoQuadrant →L[ℝ] ℝ` in the compact-open topology gives a
   compact `K₀ ⊆ criticalQuadrant` and `C ≥ 0` with `|f₂ g| ≤ C·sup_{K₀} ‖g‖`
   (`hasBasis_nhds_zero_continuousMap` + scaling).
2. **Rectangle enclosure.** `a = min Re K₀ > 1/2`, `b = max Re K₀ < 1`, `c = min Im K₀ > 0`,
   `d = max Im K₀`; `K := [a,b]×[c,d] ⊆ Q₊`, `K₀ ⊆ K`.
3. **Carrier symmetric under the critical reflection** `R s = 1 - conj s`:
   `Ǩ := ([1-b,1-a] ∪ [a,b]) × [c,d]`; `R Ǩ = Ǩ`, `K ⊆ Ǩ`, `Ǩ ⊆ {1-b ≤ Re ≤ b}` with
   `0 < 1-b` and `b < 1`.  `ℂ \ Ǩ` is connected because `Ǩ = S × [c,d]` with `S ⊆ ℝ` closed: the
   upward vertical ray from any point off `Ǩ` misses `Ǩ`.
4. **Complexify.** `f₂` factors through the restriction `holoQuadrant → C(K,ℂ)` (the bound makes it
   well defined), extend by real Hahn–Banach to `Φ : C(K,ℂ) →L[ℝ] ℝ`, complexify with
   `StrongDual.extendRCLike` to `L : C(K,ℂ) →L[ℂ] ℂ`, `Re L = Φ`.
5. **Reflection functional.** `τ h z := conj (h (1 - conj z))` is conjugate-linear, so
   `L♭ h := conj (L (τ h |_K))` is ℂ-linear; put `A := L - L♭` on `C(Ǩ,ℂ)`.
   `τ u_p = -u_p` (Schwarz reality + FE-oddness of the symmetrised Euler tangent), hence
   `A u_p = 2 Re L (u_p|_K) = 2 f₂ (u_p) = -2 f₁ (primeTangentGen p)` — real and bounded by
   `2‖f₁‖ · (log p)/p`.  Feed the critical carrier elimination with `α = 1-b`, `β = b`.
6. **Cauchy transform.** From `A (s^m) = 0` for all `m` (and the Laplace representations
   `(z-w)⁻¹ = ∫₀^∞ e^{-tz} e^{tw} dt` for `Re w < α`, `-∫₀^∞ e^{-tw} e^{tz} dt` for `Re w > β`,
   which use `compactFourierBorel A s ≡ 0`) get `Ĉ_A ≡ 0` on `ℂ \ Ǩ` by the identity theorem.
   Then `Ĉ_L` and `-ψ`, `ψ w := conj (Ĉ_L (1 - conj w))`, glue to an entire function vanishing at
   infinity, so Liouville gives `Ĉ_L ≡ 0` on `ℂ \ K`.
7. **Rectangle CIF.** For `g ∈ holoQuadrant` with extension `G` on `Q₊`, take a rectangle
   `K' ⊋ K` still inside `Q₊`; `ResidueTheoremOnRectangleWithSimplePole` (PNTPlus) writes
   `G|_K` as the boundary integral of `G(w)·(w - ·)⁻¹`; commuting `L` with the interval integrals
   (`ContinuousLinearMap.integral_comp_comm`, `ContinuousMap.evalCLM`) gives
   `L (G|_K) = ∮ G(w) Ĉ_L(w) dw = 0`, hence `f₂ g = Re L (G|_K) = 0`.
8. Then `topologicalClosure_primeQuadrantGraph_eq_top` gives (3); `(18)` is the same statement for
   the generated group and `(19)` follows from `dense_affine_of_topologicalClosure_eq_top`.
