# ht/ folder stage-3 sweep (goal: formalize all 7 cards in 2-fully-proven/new_scientific_knowledge/ht)

## Session state 2026-08-13

### Card 1 triptic-kummer — NEARLY CLOSED (new modules this session)
Five new modules written, first four elaborate clean via `lake env lean`:
1. `HTGeometry/TripticMultiplicativeSourceClass.lean` — structure `TripticMultiplicativeSource τ σ Y Cst`
   (mero univ, finOrd, pointwise 1-periodic, `MixedConstGerm (logDeriv Y) τ σ Cst`); closure `.mul .div
   .pow .zpow`, `tripticMultiplicativeSource_one`, gamma-translate membership
   `tripticMultiplicativeSource_ellipticGammaConeTranslate` (Cst = −2πi). BUILT ok.
2. `HTGeometry/TripticSourceDivisorFinsupp.lean` — `laurentCoeff_shiftDiff_logDeriv_add_tau/_add_one`,
   `shiftOrder_add_tau_of_source`, `finiteShiftSupport_of_source` (germ-mixed versions),
   `tripticPeriodGroup τ σ : AddSubgroup ℂ` (carrier = PeriodGroupMem), `tripticChargeClass` (via
   Quotient.out, hypothesis-free), `tripticChargeClass_mk`, `exists_lattice_reduction` (floor reduction
   into closedBall 0 (1+‖τ‖)), `finite_support_tripticChargeClass`, `tripticDivisor` (Finsupp via
   ofSupportFinite), `tripticDivisor_mk`. BUILT ok.
3. `HTGeometry/TripticGammaProductRealization.lean` — charge of 1/zpow/finsetProd, translate indicator
   (`..._of_mem`/`..._of_notMem`), `periodGroupMem_sub_out_iff`, `gammaDivisorSource` (∏ translates ^ E g
   over E.support with Quotient.out reps), membership + `tripticOrbitCharge_gammaDivisorSource = E ⟦p⟧`.
   BUILT ok.
4. `HTGeometry/TripticKummerRootClassification.lean` — germ kernel variant
   `differentiallyAlgebraic_logDeriv_of_vanishing_orbitCharge_source`, forward
   `tripticOrbitCharge_eq_zero_of_differentiallyAlgebraic_source`, `HasTripticSourceRoot` (∃ Z CstZ,
   class ∧ DA(NF(logDeriv (Y/Z^m)))), `hasTripticSourceRoot_iff_dvd_charge`, `tripticSourceRoot_unique`,
   `hasTripticSourceRoot_iff_content_dvd`, `hasTripticSourceRoot_content`,
   `tripticSource_maximal_root_order`. Elaborated clean; lake build in flight at save time.
5. `HTGeometry/TripticSourceClassGroup.lean` — germ group over `Filter.codiscreteWithin univ`:
   `mem_codiscreteWithin_univ_iff`, `tripticOrbitCharge_congr` (germ invariance), `tripticDivisor_mul`,
   `tripticSourceUnit` (unit with pointwise 1/Y inverse), `tripticSourceUnitClass :
   Subgroup (Germ L ℂ)ˣ`, `tripticGermRep/Cst` (choice), `tripticDivisorHom : Additive M →+ ℤ[ℂ⧸H₃]`,
   `tripticDivisorHom_single`, `tripticSourceQuotientEquiv` (= card's M/M_DA ≅ ℤ[G] via
   sourceQuotientEquiv), `tripticSource_hasSourceRootModuloKernel_iff_content_dvd` (verbatim abstract),
   `tripticSource_root_unique_mod_kernel`, `mem_ker_tripticDivisorHom_iff` (kernel = DA). NOT YET
   CHECKED (queued behind build).
REMAINING for card 1: check module 5, wire all 5 into `GaloisForLFunctions/HTGeometry.lean` umbrella,
`#print axioms` audit via /tmp scratch, `scripts/formal_tools.py lint`, update card text, `git mv` card
to 3-formalized + companion note. Key existing assets used: TripticMultiplicativeKernel(Converse),
TripticChargeClassFunction, TripticCornerAccumulation (finite_setOf_laurentCoeff_ne_zero_orbit),
EllipticGammaConeDivisor/Order (periodPoint + notMem charges), MinimalHTCompletionArchitecture
(abstract Kummer), SourceDivisorSurjectivity (single ⟹ surjective).

### Key discoveries for other cards
- Cards 4/5 (orbifold tails): mathlib NOW HAS analytic Weierstrass ℘:
  `Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass` — `PeriodPair.weierstrassP`,
  `derivWeierstrassP`, `g₂ g₃`, ODE, lattice/basis. Corpus module
  `WeierstrassPDifferentiallyAlgebraic.lean` already consumes it. This unblocks the compact-signature
  complete-tail identification (uniformizing coordinate exists).
- Card 3 (isogeny tail): `HTGeometry/AbelianVariety.lean` (38KB, scheme-level Over (Spec K) + GrpObj)
  and `AbelianVarietyIsogenyTail.lean` exist; tail theorem is conditional on hfinite/hfiniteDimensional/
  hdegree (isogeny degree = card of kernel for [m^n]) — that degree data is the real frontier.
- Card 2 (pair-localization): parent all-depth card is at
  2-fully-proven/new_scientific_knowledge/other/all-depth-pair-face-signature-completeness.md (NOT in
  ht/). Polynomial core `PairFacePrivateSector.lean` done. Remaining: canonical carrier
  F_e = ∏_{k∉e} Δ_{τ_k} Ψ_{d−1} HT + signatures + noncompression (analytic), exact-image realization.
- Card 7 (Gevrey): large Barnes layer exists (BarnesDoubleZeta*, BarnesKernelExpansion,
  BarnesConeKernelRemainderBound, BarnesMellinRepresentation…) + NewtonPuiseux* modules. Remaining:
  Barnes derivative-compatible expansion (4)–(6) for H_s and Sibuya–Ramis exact Gevrey order.
- Build discipline: other agents run concurrent lake builds; lake serializes via lock — expect long
  waits; ONE build process at a time for me; lake env lean needs imports' oleans built first.
