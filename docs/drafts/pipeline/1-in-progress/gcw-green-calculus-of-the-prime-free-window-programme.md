# Green calculus of the prime-free window (GCW) — programme card

- **ID:** gcw-programme
- **Stage:** 1-in-progress
- **Type:** programme (review-1311 obstacles-summary §2.9, §2.21; B194, B195, A162)
- **Source:** docs/reports/review-1311/obstacles-summary.md §2.9
- **Lean:** `formal/GaloisForLFunctions/GreenCalculusOfThePrimeFreeWindow/`, umbrella
  `formal/GaloisForLFunctions/GreenCalculusOfThePrimeFreeWindow.lean`, README in the folder.

## Goal
Potential theory of the inverse `G_D` of the neutral part of the dyadic window `(D, 2D]`, the
mediator of the overlap law (MAFT `hermNegIndex_neutralWindow_overlap_eq_one_iff`). Questions:
(1) two-sided bounds of the sliver blocks of `G_D` uniform in `D`; (2) lower bound for `μ_D`;
(3) first overlap step in Green form; (4) excess per step; (5) closed form of the Green kernel.

## Notation
`F(n) = n log n`, `ΔF(m) = F(m+1) − F(m)`, `D(n) = Δ²F`, `κ = γ + log 2π`.
`N⁰(x,y) = δ ϱ(x) − ½(D(x+y+1) + D(|x−y|))`, `ϱ(x) = ΔF(x) − κ`. `M_D = N⁰` on `[D, 2D)`.
Window `(R, 2D+b]`, `D = R+a`: ends `E₁ = (R, D]`, `E₂ = (2D, 2D+b]`.

## Mathematical targets
- P1 middle prime-free: `x<y<2x ⇒ ⌊y/k⌋<x` for `k≥2`; `neutralWindow Q D D = neutralWindow 1 D D`.
- P2 flat-packet bound: `μ_D ≥ −N⁰(1,1) = κ + ½D(3) − 2 log 2 ≈ 1.199` (constant vector,
  `sum_neutralBlock_dyadic`).
- P3 potential floor: `M = V + 𝓔`, `𝓔 ⪰ 0` ⇒ `μ_D ≤ −min V_D`; closed form
  `V(x) = ΔF(x) − κ − ½[ΔF(x−A) + ΔF(B−1−x)] − ½[ΔF(x+B) − ΔF(x+A)]` on `(A, B]`.
- P4 loss law without derivative: if `M+C` invertible, `≥ 0` on `φ^⊥`, and Schur complement
  `S_C ⪰ −x`, then `N+C+x` is `≥ 0` on the hyperplane `⟨m + (M+C)⁻¹Pe, φ⟩ = 0`, so index `≤ 1`.
  With parts of index `≤ 1` at level `C < μ_D`: `S_C` has PSD diagonal blocks, `S_C ⪰ −‖X_C‖`.
- P5 inverse antitone at equal index: `A ⪯ B`, both invertible of the same index ⇒
  `B⁻¹ ⪯ A⁻¹` (Haynsworth on `[[B, 1],[1, A⁻¹]]` over both corners).
- P6 tower: `(range ι_m)^⊥` is charge-free, so `M_{mD}` is `⪰ 1/5000` there; hence
  `ι_mᵀ G_{mD} ι_m = (M_D − E)⁻¹`, `E ⪰ 0`, and `G_D ⪯ ι_mᵀ G_{mD} ι_m` by P5.
- P7 pencil: ratio `≤ 3`: `P_i = −𝒥_i − w𝒞_i`, `S(w) = S(0) − wΞ − w²Π`,
  `Π = 𝒞ᵀG𝒞` (sliver blocks), `Ξ = 𝒥ᵀG𝒞 + 𝒞ᵀG𝒥`; twin = `w ↦ −w`.
- P8 exact Green identities: `G_D φ = −φ/μ`, `G_D V_D = 𝟙`, `G_D v_S = χ_S` for sub-windows `S`.
- P9 magnitude reading (not a theorem): floors at aperture `≈0.36` are of prolate size
  (`10⁻³–10⁻²`), so `‖G₊‖` is large; crude norm bounds cannot give the first step.

## Modules
Formalized (compile clean, wired into the umbrella):
1. `TheGreenMatrixOfTheDyadicMiddleHasABoundStateChannelAndAPositiveChannel` — `OneBoundState`,
   `positiveChannel` (`0 ⪯ G₊ ⪯ 1/c` on `φ^⊥`), `primeFreeMiddle` (P1), `bindingEnergy > 1` (P2),
   `greenMatrix`, `overlapSchur`, overlap law in Green form, `riemannHypothesis_iff_forall_greenForm`.
2. `TheLossOfAnOverlapStepIsAdditiveBelowTheBindingEnergyOfTheMiddle` — levels
   (`OneBoundState.add_diagonal`), Dirichlet principle `positiveChannel_ge`, `S_C` grows at unit
   speed, P4 (`hermNegIndex_fromBlocks_add_diagonal_le_one`), additive loss law on windows,
   first step margin `≤ ‖X₀‖`, refinement at a level,
   `riemannHypothesis_iff_overlapSchur_bddBelow`, `…_forall_overlapSchur_nonneg`,
   `…_forall_harmonic_nonneg`, `riemannHypothesis_of_level_function`.
3. `TheCertifiedFloorsAreAPrioriBoundsForTheGreenMatrixAndTheConditionalEnergies` — certified
   ground-state and conditional floors, `−1 ⪯ G_D ⪯ 5000`, and an upper binding bound.
4. `ChargeCancellationPreservesTheCertifiedFloor` — spectral floor also for `J<R`, exact
   charge-cancellation Schur floor, and the local neutral-orthogonal overlap criterion.

All A162 components have clean transitive axiom audits; see
`../3-formalized/a162-certified-window-floors-and-overlap-calculus.md`.

Planned:
5. Sliver blocks of `G_D`; potential theory `M = V + 𝓔` (P3), `μ_D = −⟨V⟩_φ`, P8.
6. Inversion at equal index, tower monotonicity (P5, P6).
7. Contact pencil and sign twin (P7).
8+. Boundary-map norms (Hilbert inequality), first step, no-go for norm bounds.

## Log
- 2026-11-14 — card created; README first draft written; modules 1–2 formalized.
