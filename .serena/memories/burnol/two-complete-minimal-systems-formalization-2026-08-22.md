# Burnol arXiv:math/0203120 — "Two complete and minimal systems …" Lean programme

Card: `docs/drafts/pipeline/1-in-progress/burnol-two-complete-minimal-systems-lean-formalization.md`
(statement-by-statement inventory of the paper, layer plan, Theorem 2.1 brick list).

## Landed — 17 modules, axiom-clean, umbrella-wired, `lake build <module>` green

### `HTGeometry/` (abstract, reusable)
`MinimalCompleteSystem` (§3 Remark + the whole minimal/complete/dual theory) ·
`MonotoneDisjointInfiSup` (`⨅(Aᵢ⊔Bᵢ) = (⨅Aᵢ)⊔(⨅Bᵢ)`) ·
`MinimalCompleteSystemChain` (§7 indices `a₁`,`a₂`) ·
`OrthogonalCodimensionOne` (`A = 𝕜∙w ⊔ (A ⊓ (𝕜∙w)ᗮ)`; `f ⊥ (A ⊓ (𝕜∙w)ᗮ) ↔ P_A f ∈ 𝕜∙w`) ·
`CodimensionTwoOrthogonalSum` (**the codimension-two law**: removing one direction from each of two
transverse closed summands leaves an exactly 2-dimensional orthogonal complement; plus Friedrichs
cosine monotonicity and closedness of the shrunken sum) ·
`TruncatedMellinEntire` (B1) · `OscillatoryPowerIntegral` (B4 IBP bound) ·
`TruncatedPowerFourierBound` (B3) · `InvAbsTailL2` (the `1/|u|` tail kernel is `L²`).

### `RHTower/` (Sonine-specific)
`SoninForbiddenClosedSum` (`L²(−a,a)+F(L²(−a,a))` closed) ·
`SoninCarrierApertureChain` (**Prop. 4.6**) · `SoninCarrierApertureLimits` (§2 chain ends) ·
`SoninTruncatedMellinCauchy` (B5) · `SoninTruncatedMellinFamily` ·
`SoninMellinHalfPlaneExtension` (**Thm 2.1 analytic half**: holomorphic continuation of `M(f)` to
`Re s > 0`, plus the bounded-evaluation corollary) ·
`SoninExtendedOrthogonalBand` (**Burnol's description of `L_a`** as the perpendicular of the
mean-zero band, for even vectors) ·
`SoninBandCodimensionTwo` (**Prop. 4.5** in the full-line model).

## Corpus already owns (verified by search — do NOT rebuild)

- **Prop. 4.3 for `L_a`**: `BurnolSoninDividedShift.burnolShift_mem_soninExtendedSpace`
  (`1/2 < Re ρ < 1`), with the whole `burnolShift`/`burnolCoShift` divided-shift calculus.
- The **two de Branges half-plane bricks**: `RHTower/SoninDeBrangesCarrier.lean`
  (`soninMellinIntegral`, `soninMellin_integrableOn`, holomorphy on `Re z > 1/2` and `Re z < 1/2`).
- The **L² functional equation**: `CCMArchimedeanFourierMellinScattering.archimedeanMellinUnitary_evenFourierTransform`
  (`ccmArchimedeanScatteringPhase t = conj (zetaChi (linePt t))`).
- `𝓕` preserves the even carrier: `SoninApertureFourierParityNoGo.evenFourierTransform_mem_evenCentralSoninCarrier`.
- Mellin–Plancherel unitary `L2MellinUnitary`; `L2FourierIntegralBridge`; `FriedrichsClosedSum`;
  `HalfPlaneGapApproximation.differentiable_integral_kernel`;
  `SuzukiScrewAdjointWitness.norm_integral_mul_le_l2`;
  `BarnesMellinRepresentation.integral_cpow_mul_exp_neg_mul_Ioi` (`∫₀^∞ t^{s−1}e^{−wt} = Γ(s)w^{−s}`);
  `GammaGaussianEnvelope.evenChiFactor` (`χ = Γ_ℝ(1−s)/Γ_ℝ(s)`).

## Verified NOT in the corpus (genuinely open)

Titchmarsh's `|ζ(s)|⁻¹ < |s|^A` on horizontal lines `Tₙ`; the residue series of §5; Krein's theorem
(entire + Nevanlinna in two half-planes ⇒ finite exponential type); Levin CRG theory; Hardy `H²` of
a half-plane / Paley–Wiener; Prop. 4.5's even restatement; Prop. 4.7; Thm 4.8 (L-property);
Thm 4.9; **nontriviality of `K_a` at every aperture** (needs the co-Poisson witness — the corpus's
`BurnolCoPoissonInhabitedAudit` records this as its own open gap).

## Duplicate guard — run every time
`scripts/lean_dupcheck.py <file.lean …>`.  A colliding name passes `lake build <module>` and only
breaks the **area umbrella**.  Caught so far: `centralSoninCarrier_antitone`, `hasDerivAt_phase`,
`norm_phase`, `continuousOn_ofReal_cpow`.

## Next
1. **B7 (weld)** → Thm 2.1: (i) `𝓕` preserves `centralSoninCarrier a`; (ii) pointwise functional
   equation on the critical line bridged from the corpus L² scattering identity (shifted-Mellin
   route: `t^{−σ}f ∈ L¹∩L²` for `σ > 1/2`); (iii) identity theorem on `0 < Re s < 1`.
2. Even-subspace restatement of Prop. 4.5 (all pieces present: `A'`, `B'` reflection-invariant, so
   the 2-dimensional complement already lies in `evenSubspace`).
3. Hardy `H²` of the half-plane **defined à la Paley–Wiener** (image of `L²(a,∞)` under the Mellin
   transform) — this makes Prop. 4.1 near-tautological and unblocks §4/§6/§7.
