# ULF-PFM-2 — Lean certification record

**Card:** `functional-equation-split-formation-lift-information-isometry-and-work-no-go.md`
**Status:** every theorem of the card is Lean-certified, unconditional and axiom-clean.

## Card result → Lean declaration

| Card | Statement | Lean |
|---|---|---|
| (FEL.1) | split formation | `splitFormation` |
| (FEL.2) | projection recovers the observer | `splitFormation_recovers_observer` |
| Thm 1.1, (FEL.3) | split formation is a KL isometry | `klDiv_splitFormation` |
| (FEL.4) | the canonical stochastic lift | `formationLiftKernel` |
| Thm 2.1, (FEL.5) | formation-action naturality | `formationLiftKernel_naturality` |
| Thm 2.1, (FEL.6) | strict composition on formed laws | `formationLiftKernel_comp_on_formation` |
| Thm 2.1, (FEL.7) | involutivity on formed laws | `formationLiftKernel_involution_on_formation` |
| Cor 2.2, (FEL.8) | the lift is information neutral | `formationLiftKernel_klDiv_isometry`, `formationJeffreys_lift_isometry` |
| (FEL.D1) | Hellinger midpoint and modular half-cocycle | `hellingerMid`, `modularHalfCocycle` |
| (FEL.D2) | invariance, oddness, and the two factorizations | `hellingerMid_reflect`, `modularHalfCocycle_reflect`, `eq_hellingerMid_mul_exp`, `reflect_eq_hellingerMid_mul_exp` |
| (FEL.D3) | the two-sheet tilted weight | `sheetWeight`, `sheetWeight_pos`, `sheetWeight_zero_one` |
| Thm 3.1, (FEL.D4) | reflection negates the tilt and toggles the sheet | `sheetWeight_reflect`, `map_sheetMeasure` |
| Thm 3.1, (FEL.D5) | same-sheet closure forces a vanishing cocycle | `modularHalfCocycle_eq_zero_of_sameSheet`, `modularHalfCocycle_eq_zero_iff` |
| Cor 3.2, (FEL.D6) | the recovery lift transports the sheet exchange and preserves KL | `formationLift_sheetMeasure`, `klDiv_formationLift_sheetMeasure` |
| (FEL.D7)–(FEL.D9) | the literal Hasse Hellinger midpoint, cocycle, and factorization | `hasseLogBase`, `hasseHellinger`, `hasseCocycle`, `hasseHellinger_eq`, `hasseCocycle_eq`, `hasseCocycle_odd`, `hasseLogBase_factor` |
| (FEL.D10) | `χ_H'(0) = 1/2 − e/(e+1) ≠ 0` | `hasDerivAt_hasseCocycle_zero`, `hasseCocycle_deriv_zero_ne`, `exists_hasseCocycle_ne_zero`, `not_hasseLogBase_even` |
| (FEL.9)–(FEL.10) | the tilt partition is the centred `Xi` at an imaginary argument and is positive | `thetaTiltMoment_zero_eq_XiC`, `XiC_imaginary_pos`, `thetaTiltMoment_zero_pos` |
| (FEL.11) | the partition is even | `thetaTiltMoment_neg`, `thetaTiltLogPartition_neg` |
| (FEL.12) | reflection carries `ν_a` to `ν_{−a}` | `map_neg_thetaTiltProb` |
| (FEL.13) | the Hasse recovery kernel on the logarithmic scale | `thetaHasseProfile`, `HasseHistoryProfile.kernel` |
| (FEL.14) | the theta-carrier packet | `thetaCarrierPacket` |
| Thm 5.1, (FEL.16) | the lift exchanges the tilts and is an involution | `thetaCarrierPacket_reflect`, `thetaCarrierPacket_reflect_involution` |
| Thm 5.1, (FEL.17) | the Hasse kernel is information sufficient | `klDiv_thetaCarrierPacket` |
| Thm 5.1, (FEL.18) | the lift is exactly information neutral | `klDiv_thetaCarrierPacket_lift_isometry` |
| (FEL.19) | `F' = E[X]`, `F'' = Var(X) > 0` | `hasDerivAt_thetaTiltLogPartition`, `hasDerivAt_thetaTiltMean`, `thetaTiltVariance_pos` |
| (FEL.20) | the reflected log-likelihood ratio is `2ax` | `llr_thetaTiltProb_reflection` |
| (FEL.21) | both directed reflected costs equal `2aF'(a)` | `toReal_klDiv_thetaTiltProb_reflection`, `toReal_klDiv_thetaTiltProb_reflection_reverse` |
| (FEL.22) | the symmetric reflected work is `4aF'(a)` | `klDiv_thetaTiltProb_jeffreys` |
| (FEL.23) | the work vanishes exactly at the centre | `thetaTiltReflectedWork_eq_zero_iff`, `klDiv_thetaTiltProb_jeffreys_eq_zero_iff`, `klDiv_thetaCarrierPacket_jeffreys_eq_zero_iff` |
| (FEL.24) | directed chirality is zero at every tilt | `thetaTiltReflectedChirality_eq_zero`, `klDiv_thetaTiltProb_chirality_zero` |
| (FEL.25)–(FEL.27) | the raw Fermi packet has no reciprocal action | `hasseTilt_reflection_forces_base`, `no_reciprocal_fermi_action` |

## Modules

| Module | Public declarations | Role |
|---|---|---|
| `HTGeometry/ConstitutiveFunctionalEquationPacketLift.lean` | pre-existing | §1–§2 and the sheet-swap core |
| `HTGeometry/ModularFormationDouble.lean` | 12 (new) | §3 at density level |
| `HTGeometry/ModularFormationDoubleMeasures.lean` | 4 (new) | §3 at measure level, Corollary 3.2 |
| `HTGeometry/HasseModularCocycle.lean` | 15 (new) | the literal Hasse cocycle and §7 |
| `RHTower/ThetaTiltReflectedWork.lean` | 26 (new) | §6: moments, cumulants, strict convexity, the work classification |
| `RHTower/ThetaCarrierHassePacket.lean` | 26 (new) | §4, §5 and the measure-level KL identities |

All wired into `GaloisForLFunctions.HTGeometry`, `GaloisForLFunctions.RHTower` and
`GaloisForLFunctions.HTGeometry.UniversalLawField`.

## Proof notes

* The tilt family is built directly on the corpus's completed theta source
  `thetaCuspFullSource`, positive and even.  Integrability of `x^k e^{ax} Φ(x)` for `|a| ≤ 1`
  follows from the two-sided majorant `|x|^k (e^x + e^{-x}) Φ(x)`, whose integrability the corpus
  already proves at each `k`, so differentiation under the integral runs on the whole open unit
  tilt interval rather than only at the Suzuki endpoint `a = 1`.
* `F'' = Var > 0` is proved by the corpus's Hankel route: the tilted measure charges the complement
  of every finite set, so `momentHankelMatrix_posDef_of_infiniteSupport` gives
  `M₀M₂ − M₁² > 0`.  No Cauchy–Schwarz equality analysis is needed.
* The Radon–Nikodym layer uses mathlib's `Measure.tilted`: `ν_a = ν_{−a}.tilted (2ax)` and the
  normalizer `∫ e^{2ax} dν_{−a}` is `1` because `M₀` is even, so `log_rnDeriv_tilted_left_self`
  gives `llr = 2ax` with no additive constant — exactly (FEL.20).
* `Measure.map (−·)` of a density measure is proved from scratch
  (`map_neg_withDensity`, and `map_withDensity_of_involution` in the abstract case): mathlib has no
  push-forward rule for `withDensity` along a measure-preserving involution.

## Verification

* `lake env lean` on all five new modules: 0 errors, 0 warnings.
* `#print axioms` over the 87 public declarations of the new modules: only `propext`,
  `Classical.choice`, `Quot.sound`.
* No `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, and no added hypotheses beyond the card's own
  admissibility conditions (`|a| ≤ 1` or `|a| < 1`, and finiteness of a sheet normalizer).

## Not claimed

The card's corrected RH-facing target — a pre-zero source law whose functional-equation lift forces
`4aF'(a)` to vanish — is future work.  The card is a no-go: it proves that information neutrality
cannot be that law.
