# Deninger NSK folder → stage 3 (2026-08-13)

Cards: `docs/drafts/pipeline/.../new_scientific_knowledge/deninger/`
1. `deninger-half-density-floquet-euler-boundary-dichotomy` — **DONE, moved to 3-formalized**
2. `deninger-algebraic-cyclotomic-milnor-amplitude` — active
3. `deninger-selective-positive-cell-h0-preservation` — pending

## Card 1 COMPLETE — every item of the card is Lean-proved, axioms clean

New modules (all wired into `RHTower.lean`; the criterion into `HTGeometry.lean`):
- `RHTower/DeningerFloquetLatticeMeasure.lean` — **(23)** `deningerFloquetMeasure`
  = `∑_q (q^{-2}/log q) ∑_{m∈ℤ} δ_{m/log q}`; `lintegral_deningerFloquetMeasure`;
  `deningerFloquetNode_eq_iff` (no shared nonzero node, via `logPrime_linearIndependent_int`);
  `deningerFloquetMeasure_compl_support`; `deningerFloquetMeasure_Icc_le` (linear mass growth);
  `IsFiniteMeasureOnCompacts` instance.
- `RHTower/DeningerFloquetMeasureEnergy.lean` — `deningerFloquetSample h ξ = 𝓕(e^{t/2}h) ξ`;
  `deningerFourierSample_hasSum`; **`lintegral_deningerFloquetSample_normSq`** = **(24)**.
- `RHTower/DeningerFloquetAtomicMeasure.lean` — nodes are atoms; `..._ae_eq_zero`.
- `RHTower/DeningerSourceModulation.lean` — `deningerModulate` (multiply by `e^{2πict}`).
- `RHTower/DeningerFloquetGaussianAtom.lean` — `deningerFloquetAtom ξ₀ σ`,
  **`deningerFloquetSample_atom`** = `e^{-π(ξ-ξ₀)²/σ}` (via mathlib `fourier_gaussian_pi'`).
- `RHTower/DeningerFloquetHilbert.lean` — **(26)**: `deningerFloquetSample_memLp`,
  `deningerFloquetSample_integral_normSq` (isometry), `deningerFloquetLp`,
  `deningerFloquetLp_span_topologicalClosure = ⊤`.
- `RHTower/DeningerFloquetPoissonSample.lean` — `deningerCriticalLine ξ = 1/2 - 2πIξ`;
  `deningerFloquetSample_eq_strongLogMellin`; **`deningerFloquetSample_poissonSource`** = **(29)**;
  `deningerFloquetResonance`.
- `RHTower/DeningerFloquetPoissonFlow.lean` — `mellin_deningerMeyerCapFlow` (`e^{cs}`),
  `deningerFloquetSample_capFlow`, `deningerFloquetProfile_ne_zero`.
- `RHTower/DeningerFloquetPoissonClosure.lean` — `deningerFloquetAtomLp`,
  `deningerFloquetBoundary`, `deningerFloquetResonanceSpan`, `deningerFloquetBoundary_le`.
- `RHTower/DeningerFloquetPoissonCompleteness.lean` — `deningerGaussianCharacter_integral`,
  **`deningerFloquetFlow_orthogonal_inf_eq_bot`** (general: any cap element with nowhere-vanishing
  critical-line Mellin), **`deningerFloquetBoundary_topologicalClosure`** = **(27)**,
  **`deningerFloquetBoundary_closure_orthogonal`** = **(28)**.
- `RHTower/DeningerFloquetBoundedCorrection.lean` — **§7**: `..._vanishing`, `..._factors`,
  `..._unique`.
- `RHTower/DeningerFloquetDepletedCorrection.lean` — §7 on the depleted sector:
  `deningerMeyerCapDepletion`, `mellin_deningerMeyerCapDepletion`,
  `deningerFloquetDepletedBoundary_topologicalClosure`, `..._factors`.
- `HTGeometry/OrthogonalClosureCriterion.lean` —
  `submodule_topologicalClosure_eq_of_orthogonal_inf_eq_bot`, `mem_span_orthogonal`.

Key corpus inputs reused: `meyerPoissonTestSource : DeningerMeyerCap` +
`mellin_meyerPoissonTestSource_ne_zero` (CCMConnesConsaniZetaCycles),
`deningerMeyerStrongLogMellin_boundary_eq_zeta_mul_mellin_of_re_pos`,
`deningerPoissonSource`, `deningerMeyerCapFlow`, `polyGaussSchwartz_mem_deningerExpSchwartz`,
`schwartzDilate_mem_deningerExpSchwartz`, `deningerExpSchwartzOfBounds`, `cexpLin` +
`iteratedDeriv_cexpLin`, `continuous_fourier_of_integrable`.

## Card 2 next: `deninger-algebraic-cyclotomic-milnor-amplitude`
Remaining: `(1)` `K_q^M(F)⊗ℝ = 0` for algebraic `F/ℚ`, `q ≥ 2`; `(2)` the two-term homotopy shape;
`(4)` the formality consequence.  Card imports `(1)` from Gallauer Rem 6.8 + Borel.  NOTE: for
*Milnor* K-theory the classical route is Bass–Tate/Tate (K_2 of a number field is torsion via tame
symbols into the finite residue-field unit groups; `K_q^M ≅ (ℤ/2)^{r_1}` for `q ≥ 3`), which is far
more elementary than Borel's rational K-theory.  Existing: `HTGeometry/MilnorKTheory.lean`
(`MilnorK`, `milnorSymbol`, Steinberg), `HTGeometry/MilnorWittKTheory.lean`,
`RHTower/DeningerMilnorAmplitude.lean`.
