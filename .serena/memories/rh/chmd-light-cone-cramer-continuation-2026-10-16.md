# CHMD light-cone decomposition + Klein–Gordon Cramér continuation (2026-10-16)

STATUS MUST-1534 (light-cone decomposition), MUST-1535 (KG Cramér leading law), MUST-1536 (massless continuation to all Re≠0, simple poles at all ±log n ± i), MUST-1537 (KG exact expansion), CANNOT-560 (KG wave has no meromorphic continuation at primes), MUST-1538 (archimedean ±i singularity; exact boundary singular set). Card: docs/drafts/pipeline/3-formalized/chmd-light-cone-cramer-continuation-2026-10-16.md. Standard axioms, lake --old green, wired (HTGeometry.lean after BesselJGeneratingFunction; RHTower.lean after CHMDStage22).

Modules (namespace RHTower.CHMDLightCone unless noted):
1. HTGeometry/KleinGordonLightConeBesselKernel — lightConeBessel B(w)=Σ(−w/4)^k/(k!(k+1)!), entire, besselJ_one_eq, Beta integrals, cos_mul_eq_lightCone, lightConeBesselReal.
2. CHMDDAlembertSechKernel — dAlembertKernel D=2/sinhSlope, residue −2i/π at i.
3. CHMDLightConePrimeKernelDecomposition — chmdPrimeKernel_eq_free_sub_tail; waves = lightConeTransmute of massless; masslessPrimeWave_pos.
4. CHMDMasslessZeroWaveExplicitFormula — masslessZeroWave, kgZeroWave on |Im|<1; masslessZeroWave_ofReal.
5. CHMDArchimedeanLevyTranslateForm — arch = continuous prime distribution ω.
6. CHMDMasslessContinuationPieces — cutoff-a pieces, rectangle deformation, prime tail bounds.
7. CHMDMasslessCramerContinuation — masslessContinuation a (Re v > a), archContinuation_congr, residues.
8. CHMDMasslessBoundaryContinuation — masslessBoundaryWave (global, 4 quadrants via neg/conj), masslessZeroWave_cramer.
9. CHMDKleinGordonTransmutationComplexTime — kgZeroWave_eq_lightConeTransmuteC.
10. CHMDKleinGordonCramerContinuation — kgBoundaryWave = L[masslessBoundaryWave], LightConeRegular, tendsto_kgZeroWave_boundary_four.
11. CHMDKleinGordonBoundarySingularity — exists_kgZeroWave_boundary_expansion (Φ = R/(z−p) − zR Log(z−p) + O(1)), not_meromorphicAt_kgZeroWave_four, kgZeroWave_cramer.
12. CHMDArchimedeanBoundarySingularity — sector positivity, lightConeBesselReal_nonneg (x≤0), zetaZeroConfig_carrier_infinite (Hardy dyadic), tendsto_masslessZeroWave_imag_re / tendsto_kgZeroWave_imag_re (Re → +∞ at i), *_boundary_regular_iff, *_boundary_singular_set (singular ⇔ |Re v| = log n, n=1 or Λ(n)≠0).

13. CHMDKleinGordonInverseLightCone (MUST-1539) — cos_mul_eq_inverseLightCone (mass² −2), masslessZeroWave_eq_inverseLightConeTransmuteC (Φ₀ = L⁻¹[Φ] on strip), L/L⁻¹ mutually inverse, meromorphicAt_order_eq_neg_one_of_tendsto, masslessBoundaryWave_simple_pole, kgZeroWave_inverseLightCone_cramer (continuation of L⁻¹[Φ] has order −1 poles at all ±log n ± i).

Key fact: genuine simple poles only for the massless wave Φ₀ = L⁻¹[Φ]; the KG causal wave Φ has pole + log branch and provably no meromorphic continuation.
