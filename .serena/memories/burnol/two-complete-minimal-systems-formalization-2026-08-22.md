# Burnol arXiv:math/0203120 — "Two complete and minimal systems …" Lean programme

Card: `docs/drafts/pipeline/1-in-progress/burnol-two-complete-minimal-systems-lean-formalization.md`
(statement-by-statement inventory, layer plan, and the **frozen B7 weld plan** — read that first).

## Landed — 21 modules, axiom-clean, umbrella-wired, `lake build <module>` green

### `HTGeometry/` (reusable)
`MinimalCompleteSystem` (§3 Remark + minimal/complete/dual theory) ·
`MonotoneDisjointInfiSup` (`⨅(Aᵢ⊔Bᵢ)=(⨅Aᵢ)⊔(⨅Bᵢ)`) · `MinimalCompleteSystemChain` (§7 indices) ·
`OrthogonalCodimensionOne` · `CodimensionTwoOrthogonalSum` (the codimension-two law) ·
`TruncatedMellinEntire` (B1) · `OscillatoryPowerIntegral` (B4) · `TruncatedPowerFourierBound` (B3) ·
`InvAbsTailL2` · `DampedPowerOscillation` (damped amplitude, bound **uniform in ε and A**) ·
`PowerFourierGamma` (**`∫_0^∞ t^{-s}e^{itL}dt = Γ(1−s)(−iL)^{s−1}`**, `0<Re s<1`, any `L ≠ 0`) ·
`TruncatedPowerFourierLimit` (Burnol's kernel `C_a(u,s)` as a limit).

### `RHTower/` (Sonine-specific)
`SoninForbiddenClosedSum` · `SoninCarrierApertureChain` (**Prop. 4.6**) ·
`SoninCarrierApertureLimits` (§2 chain ends) · `SoninTruncatedMellinCauchy` (B5) ·
`SoninTruncatedMellinFamily` · `SoninMellinHalfPlaneExtension` (**Thm 2.1 analytic half** +
bounded evaluation) · `SoninExtendedOrthogonalBand` (description of `L_a`) ·
`SoninBandCodimensionTwo` (**Prop. 4.5**, full-line model) ·
`SoninCarrierFourierInvariance` (`𝓕` preserves `centralSoninCarrier a` on even vectors).

## Corpus already owns (verified by search — do NOT rebuild)

- **Prop. 4.3 for `L_a`**: `BurnolSoninDividedShift.burnolShift_mem_soninExtendedSpace`.
- Two de Branges half-plane bricks + `soninMellinIntegral`: `RHTower/SoninDeBrangesCarrier.lean`.
- L² functional equation: `CCMArchimedeanFourierMellinScattering`; `zetaChi = Γ_ℝ(1−s)/Γ_ℝ(s)`
  (`ZetaCarrier`, `ArchimedeanPrimeCrossTerm.zetaChi_eq_pi_cpow_mul_gamma_ratio`).
- `evenFourierTransform_mem_evenCentralSoninCarrier` (`SoninApertureFourierParityNoGo`).
- `BarnesMellinRepresentation.integral_cpow_mul_exp_neg_mul_Ioi` (complex-rate Euler integral) and
  `integrableOn_cpow_mul_exp_neg_mul_Ioi`.
- `OscillatoryIntegrationByParts.norm_integral_oscillatory_le` (one-IBP oscillatory bound).
- `L2MellinUnitary`, `L2FourierIntegralBridge`, `FriedrichsClosedSum`,
  `HalfPlaneGapApproximation.differentiable_integral_kernel`,
  `SuzukiScrewAdjointWitness.norm_integral_mul_le_l2`, mathlib `riemannZeta_one_sub`.
- NOTE: `RHTower.conj_ofReal_cpow` exists **twice** (`BaezDuarteDetectorGram`, `HeatEnergyExpand`).
  Use a different name; mine is `HTGeometry.conj_cpow_ofReal_base`.

## Verified NOT in the corpus (genuinely open)

Titchmarsh `|ζ(s)|⁻¹ < |s|^A` on horizontal lines `Tₙ`; §5 residue series; Krein's theorem; Levin
CRG; Hardy `H²` of a half-plane / Paley–Wiener; Prop. 4.5's even restatement; Prop. 4.7;
Thm 4.8 (L-property); Thm 4.9; nontriviality of `K_a` at every aperture.

## Duplicate guard
`scripts/lean_dupcheck.py <file.lean …>` before wiring — a colliding name passes
`lake build <module>` and breaks only the **area umbrella**.  Caught: `centralSoninCarrier_antitone`,
`hasDerivAt_phase`, `norm_phase`, `continuousOn_ofReal_cpow`.

## Next (B7 weld — steps 1–3 done, see the card for the full chain)
4. DCT: `soninMellinExtension f a s = ∫ C_a(u,s) g(u) du` using the uniform `C/|u|` bound.
5. `∫ E_a(u,s)g(u)du = ∫_0^a t^{-s}f(t)dt = 0` since `f` vanishes on `(0,a)`.
6. evenness ⇒ `Γ(1−s)∫(−2πui)^{s−1}g = 2(2π)^{s−1}Γ(1−s)sin(πs/2)·ĝ(1−s)`.
7. glue ⇒ `f̂` entire.  The identification `c = Γ_ℝ(1−s)/Γ_ℝ(s)` is needed only for the
   Γ-completed statement, not for entirety.
