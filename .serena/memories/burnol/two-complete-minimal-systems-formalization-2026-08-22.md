# Burnol arXiv:math/0203120 — "Two complete and minimal systems …" Lean programme

Card: `docs/drafts/pipeline/1-in-progress/burnol-two-complete-minimal-systems-lean-formalization.md`
(full statement-by-statement inventory of the paper, layer plan, and the Theorem 2.1 brick list).

## Landed — 14 modules, all axiom-clean, umbrella-wired, `lake build <module>` green

### Abstract / reusable (HTGeometry)
| Module | Content |
|---|---|
| `MinimalCompleteSystem` | §3 terminology + Remark: `IsCompleteSystem`/`IsMinimalSystem`/`IsDualSystem`; minimal ⇔ ∃ dual; dual unique for a complete system; dual is minimal; minimality pulls back along a continuous linear map (Prop. 6.4 argument); completeness pushes along a dense-range map (Prop. 6.6); the Hardy-disc example `b0 − b(n+1)` whose dual is not complete |
| `MonotoneDisjointInfiSup` | `⨅(Aᵢ ⊔ Bᵢ) = (⨅Aᵢ) ⊔ (⨅Bᵢ)` for monotone internally disjoint families + Hilbert corollary (the Prop. 4.6 mechanism) |
| `MinimalCompleteSystemChain` | §7 opening: `IsCompleteSystemIn`, minimality downward / completeness upward closed, indices `a₁`,`a₂` in `EReal` |
| `OrthogonalCodimensionOne` | `A = 𝕜∙w ⊔ (A ⊓ (𝕜∙w)ᗮ)`; `f ⊥ (A ⊓ (𝕜∙w)ᗮ) ↔ P_A f ∈ 𝕜∙w` (Prop. 4.5 second proof) |
| `TruncatedMellinEntire` | **B1** `s ↦ ∫_a^b φ(t)t^{-s}dt` entire, `0 < a ≤ b`, `φ ∈ L¹` |
| `OscillatoryPowerIntegral` | **B4** IBP: `‖∫_a^T e^{ilt}t^{-s}dt‖ ≤ (2a^{-σ}+‖s‖a^{-σ}/σ)/|l|`, uniform in `T`, `Re s > 0` |
| `TruncatedPowerFourierBound` | **B3** `𝓕(1_{(T,T')}t^{-s})(u) = ∫_T^{T'}e^{-2πiut}t^{-s}dt` + its `1/|u|` bound |
| `InvAbsTailL2` | the tail kernel `1_{|u|>a}/|u|` is `L²`; `invAbsTailNorm` |

### Sonine-specific (RHTower)
| Module | Content |
|---|---|
| `SoninForbiddenClosedSum` | `L²(−a,a) + F(L²(−a,a))` is **closed** (Burnol's [6] input), via `friedrichsCosine ≤ √‖P_B P_A P_B‖` |
| `SoninCarrierApertureChain` | band membership/monotonicity, `⨅_{b>a}` of each band, and **Prop. 4.6** `(⨆_{b>a}K_b)⁻ = K_a` |
| `SoninCarrierApertureLimits` | §2 chain ends: `K = ∪_{a>0}K_a` (dense), `{0} = ∩_{a>0}K_a` |
| `SoninTruncatedMellinCauchy` | **B5** `‖∫_T^{T'}t^{-s}f(t)dt‖ ≤ ((2T^{-σ}+‖s‖T^{-σ}/σ)/2π)·N(a)·‖f‖` for `f ∈ K_a` |
| `SoninTruncatedMellinFamily` | `soninTruncMellin` entire, increment formula, factored Cauchy estimate |
| `SoninMellinHalfPlaneExtension` | **B6 / Thm 2.1 analytic half**: `soninMellinExtension f a` is holomorphic on `Re s > 0`, equals `soninMellinIntegral f` on `Re s > 1/2`, and `‖soninMellinExtension f a s‖ ≤ a^{-σ}·(…)·‖f‖` (the continuity half of Thm 2.1, past the critical line) |

## Reuse map — do NOT rebuild

- `RHTower/L2MellinUnitary.lean` (`mellinUnitary`); `BurnolSoninEvenCosineAperture` (`soninExtendedSpace` = `L_a`);
  `SoninEulerCornerConcrete` (`centralSoninCarrier` = `K_a`, `norm_centralSoninAlternatingBlock_lt_one`);
  `SoninApertureRestrictionDefect.centralSoninCarrier_antitone`; `SoninL2ShellNull` (transversality);
  `HTGeometry/FriedrichsClosedSum`; `HTGeometry/HalfPlaneGapApproximation.differentiable_integral_kernel`;
  `RHTower/L2FourierIntegralBridge.l2_fourier_coeFn_eq_l1_fourier_of_integrable`;
  `RHTower/SoninDeBrangesCarrier` (the two half-plane bricks, `soninMellinIntegral`, `soninMellin_integrableOn`);
  `RHTower/SuzukiScrewAdjointWitness.norm_integral_mul_le_l2`;
  `CCMArchimedeanFourierMellinScattering.archimedeanMellinUnitary_evenFourierTransform` (the L² functional equation).
- `HTGeometry/NonstationaryPhaseIteration` is the *vanishing-endpoint* IBP — different from `OscillatoryPowerIntegral`.

## Duplicate guard — run it every time

`scripts/lean_dupcheck.py <file.lean …>`.  `lake build <new module>` passes on a colliding name
(the twin modules are never imported together); only the **area umbrella** breaks.  Caught
`centralSoninCarrier_antitone`, `hasDerivAt_phase`, `norm_phase`, `continuousOn_ofReal_cpow`.

## Next: brick B7 (the weld) — the only thing between here and Theorem 2.1

1. `fourierUnitary` preserves `centralSoninCarrier a` (needs `𝓕(cPF)=cFF`, `𝓕(cFF)=cPF`, reflection
   invariance of the symmetric band; corpus has `fourierUnitary_l2Reflection`).
2. The **pointwise** functional equation `f̂(s) = χ(s)·(F₊f)^(1−s)` a.e. on the critical line —
   bridge from the corpus's L²-level `archimedeanMellinUnitary_evenFourierTransform`.  This is the
   genuinely missing piece; the shifted-Mellin route (`t^{-σ}f ∈ L¹∩L²` for `σ > 1/2`) looks best.
3. Identity theorem on the strip `0 < Re s < 1` to glue with the reflected extension.

After Thm 2.1: §4 (Prop. 4.1–4.3, Lem. 4.4, Prop. 4.5/4.7, Thm. 4.8/4.9), §5 (Titchmarsh `1/ζ` on
`|Im s| = Tₙ`, the residue series), §6 (Krein mean-type), §7 (Levin CRG).  Missing infrastructure in
build order: Hardy `H²` of a half-plane + Paley–Wiener, mean type / Nevanlinna class, Krein's
theorem, Levin completely-regular growth.
