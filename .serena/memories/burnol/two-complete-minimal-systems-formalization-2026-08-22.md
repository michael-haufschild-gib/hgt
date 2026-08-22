# Burnol arXiv:math/0203120 — "Two complete and minimal systems …" Lean programme

Card: `docs/drafts/pipeline/1-in-progress/burnol-two-complete-minimal-systems-lean-formalization.md`
(full statement-by-statement inventory of the paper, the layer plan, and the Theorem 2.1 brick list).

## Landed (all axiom-clean, umbrella-wired, `lake build <module>` green)

| Module | Paper content |
|---|---|
| `HTGeometry/MinimalCompleteSystem.lean` | §3 terminology + Remark: `IsCompleteSystem`, `IsMinimalSystem`, `IsDualSystem`; minimal ⇔ ∃ dual; dual unique for a complete system; dual is minimal; minimality pulls back along a continuous linear map (Prop. 6.4 argument); completeness pushes along a dense-range map (Prop. 6.6 argument); the Hardy-disc example `u n = b 0 − b (n+1)` complete+minimal with dual `−b(n+1)` **not** complete |
| `HTGeometry/MonotoneDisjointInfiSup.lean` | the lattice identity of the Prop. 4.6 proof: `⨅(Aᵢ ⊔ Bᵢ) = (⨅Aᵢ) ⊔ (⨅Bᵢ)` for monotone internally disjoint families over a nonempty linear order + its Hilbert corollary |
| `HTGeometry/MinimalCompleteSystemChain.lean` | §7 opening: `IsCompleteSystemIn`, minimality downward closed / completeness upward closed along an antitone chain, the indices `a₁`, `a₂` in `EReal` |
| `HTGeometry/OrthogonalCodimensionOne.lean` | the mechanism of Burnol's *second* proof of Prop. 4.5: `A = 𝕜∙w ⊔ (A ⊓ (𝕜∙w)ᗮ)` and `f ⊥ (A ⊓ (𝕜∙w)ᗮ) ↔ P_A f ∈ 𝕜∙w` |
| `HTGeometry/TruncatedMellinEntire.lean` | **brick B1**: `s ↦ ∫_a^b φ(t)t^{-s}dt` is entire for `0 < a ≤ b`, `φ ∈ L¹(a,b)` |
| `HTGeometry/OscillatoryPowerIntegral.lean` | **brick B4**: one integration by parts, `‖∫_a^T e^{ilt}t^{-s}dt‖ ≤ (2a^{-σ}+‖s‖a^{-σ}/σ)/\|l\|` **uniformly in T**, for `Re s > 0` |
| `RHTower/SoninForbiddenClosedSum.lean` | Burnol's input from [6]: `L²(−a,a) + F(L²(−a,a))` is **closed**; via `friedrichsCosine ≤ √‖P_B P_A P_B‖` |
| `RHTower/SoninCarrierApertureChain.lean` | band membership/monotonicity, `⨅_{b>a}` of each band, and **Prop. 4.6** `(⨆_{b>a} K_b)^− = K_a` |
| `RHTower/SoninCarrierApertureLimits.lean` | §2 chain ends: `K = ∪_{a>0}K_a` (dense) and `{0} = ∩_{a>0}K_a` |

## Reuse map — do NOT rebuild these

- Mellin–Plancherel unitary: `RHTower/L2MellinUnitary.lean` (`mellinUnitary`).
- `L_a` = `soninExtendedSpace` (`BurnolSoninEvenCosineAperture`), monotone
  (`BurnolSoninApertureMonotone`), closed (`BurnolSoninRieszVector`).
- `K_a` = `centralSoninCarrier` (`SoninEulerCornerConcrete`), antitone
  (`SoninApertureRestrictionDefect.centralSoninCarrier_antitone`).
- The **two de Branges bricks** (holomorphy of `M(f)` on `Re z > 1/2` and of `M(F₊f)(1−z)` on
  `Re z < 1/2`): `RHTower/SoninDeBrangesCarrier.lean`.  Only the *weld* is missing.
- Functional equation `M(F₊f) = reflect ∘ χ ∘ M(f)` on the even carrier:
  `RHTower/CCMArchimedeanFourierMellinScattering.archimedeanMellinUnitary_evenFourierTransform`.
- `L¹∩L²` agreement of the unitary `L²` Fourier transform with the Fourier integral:
  `RHTower/L2FourierIntegralBridge.l2_fourier_coeFn_eq_l1_fourier_of_integrable`.
- Parametric-integral entirety criterion: `HTGeometry/HalfPlaneGapApproximation.differentiable_integral_kernel`.
- Friedrichs angle ⇔ closed sum: `HTGeometry/FriedrichsClosedSum.lean`.
- Nonstationary phase with *vanishing endpoints*: `HTGeometry/NonstationaryPhaseIteration.lean`
  (different from `OscillatoryPowerIntegral`, which keeps the boundary terms).

## Duplicate guard (learned the hard way — twice)

`scripts/lean_dupcheck.py <file.lean …>` lists every declaration name in the given files that
already exists elsewhere in the tree.  `lake build <new module>` passes on a colliding name because
the two modules are not imported together — only the **area umbrella** breaks.  Run it before
wiring anything.  It caught `centralSoninCarrier_antitone` and `hasDerivAt_phase`/`norm_phase`.

## Next bricks (Theorem 2.1 = de Branges entirety)

* **B3** — identify `F(1_{a<|t|<T}|t|^{-s})(u)` with the even form of `oscPowerIntegral`.
* **B5** — `‖K_{a,T}(s) − K_{a,∞}(s)‖_{L²(|u|>a)} ≤ C(s,a)T^{-Re s}`, locally uniform in `s`.
* **B6** — Weierstrass (mathlib `TendstoLocallyUniformlyOn.differentiableOn`).
* **B7** — glue with the reflected brick on `0 < Re s < 1` via the scattering identity.

Then the whole of §4 (Prop. 4.1–4.3, Lem. 4.4, Prop. 4.5/4.7, Thm. 4.8/4.9), §5 (Titchmarsh `1/ζ`
on `|Im s| = Tₙ`, the residue series), §6 (Krein mean-type), §7 (Levin CRG) remain.  Missing
infrastructure, in build order: Hardy `H²` of a half-plane + Paley–Wiener, mean type / Nevanlinna
class, Krein's theorem, Levin completely-regular growth.
