# ULF-FRM-2 — Lean certification record

Card: `fixed-source-formation-capital-sufficient-macro-saturation-and-theta-species-exit-law.md`
Promoted to Stage 3 on 2026-08-30.

## Modules (all new)

| Module | Card sections |
|---|---|
| `GaloisForLFunctions.HTGeometry.FixedSourceFormationCapital` | §1, §2 (Thm 2.1, Thm 2.3), §3, §4 |
| `GaloisForLFunctions.HTGeometry.FinitePacketMeasure` | §2 (Cor 2.2) and the finite-packet/measure bridge |
| `GaloisForLFunctions.HTGeometry.CommonRecoveryCapitalNeutrality` | §5 |
| `GaloisForLFunctions.HTGeometry.SufficientMacroSaturation` | §6 (Thm 6.1 items 1–3, Rényi half of item 4, item 5), §7 |
| `GaloisForLFunctions.HTGeometry.SufficientMacroRelativeEntropy` | §6, relative-entropy half of Thm 6.1 item 4 |
| `GaloisForLFunctions.HTGeometry.HellingerAffinityFactorization` | general Hellinger affinity used by §8 |
| `GaloisForLFunctions.RHTower.ThetaSufficientMacroSpeciesExit` | §8 (Thm 8.1) |

The six `HTGeometry` modules are imported by `GaloisForLFunctions.HTGeometry.UniversalLawField`,
which `GaloisForLFunctions.HTGeometry` imports; the theta module is imported by
`GaloisForLFunctions.RHTower`.

## Card result → Lean declaration

| Card | Lean |
|---|---|
| `(FCAP.1)`–`(FCAP.4)` binary experiment, exact formation array | `FiniteExperiment`, `ExactFormation` |
| `(FCAP.5)` affinity, Hellinger distance | `finitePacketAffinity`, `finitePacketHellinger` |
| `(FCAP.6)` formation depth | the `d` index of `ExactFormation` |
| **Thm 2.1**, `(FCAP.7)`, `(FCAP.9)`–`(FCAP.12)` | `ExactFormation.finitePacketAffinity_le` |
| `(FCAP.8)`, `(FCAP.10)` depth bound | `ExactFormation.depth_le` |
| **Cor 2.2**, `(FCAP.13)` | `ExactFormation.klDiv_le`, `ExactFormation.jeffreys_le` |
| **Thm 2.3**, `(FCAP.13a)`–`(FCAP.13c)` | `ExactFormation.renyiOverlap_le`, `ExactFormation.capital_le` |
| **Thm 3.1**, `(FCAP.14)`, `(FCAP.15)` | `forall_depth_formation_iff`, with both explicit constructions `neutralFormation` (via `constantKernel`) and `singularFormation` (via `separatingKernel`) |
| **Thm 3.2**, `(FCAP.16)`–`(FCAP.19)` | `approximate_properness`; ingredients `finitePacketHellinger_triangle`, `finitePacketHellinger_sq`, `finitePacketHellinger_markovDataProcessing` |
| §4, `(FCAP.20)`–`(FCAP.22)` | `LikelihoodCounterexample.srcZero/srcOne/tgtZero/tgtOne`, `no_common_kernel`, `affinity_lt` |
| §5, `(FCAP.23)`, `(FCAP.24)` | `splitRecovery`, `sum_splitRecovery_fibre`, `renyiOverlap_splitRecovery`, `finitePacketAffinity_splitRecovery`, `FiniteExperiment.splitRecovery`, `FiniteExperiment.capital_splitRecovery` |
| §5, `(FCAP.25)` | `reflectPacket`, `tensorPower_reflect`, `renyiOverlap_reflect`, `finitePacketAffinity_reflect`, `finitePacketHellinger_reflect`, `FiniteExperiment.reflect`, `FiniteExperiment.capital_reflect` |
| `(FCAP.26)`–`(FCAP.30)` exponential family, sum statistic, fibre weight, macro law, recovery kernel | `SufficientMacro.partition`, `packet`, `sumStat`, `statImage`, `MacroAlphabet`, `fibreWeight`, `macroPacket`, `recoveryWeight` |
| **Thm 6.1** item 1 | `SufficientMacro.recoveryKernel` (a `FiniteMarkovKernel`, `θ`-independent), `sum_recoveryWeight` |
| **Thm 6.1** item 2, `(FCAP.31)` | `SufficientMacro.sum_fibre_tensorPower`, `statKernel_applyReal` |
| **Thm 6.1** item 3, `(FCAP.32)` | `SufficientMacro.sum_macro_recovery`, `recoveryKernel_applyReal` |
| **Thm 6.1** item 4, `(FCAP.33)` | `SufficientMacro.renyiOverlap_macroPacket`, `finitePacketAffinity_macroPacket` |
| **Thm 6.1** item 4, `(FCAP.34)` | `SufficientMacro.klDiv_macroPacket`, `formationJeffreys_macroPacket` (with the exact-sufficiency step `klDiv_macroPacket_eq`) |
| `(FCAP.35a)` | `SufficientMacro.renyiCapital_macroPacket` |
| **Thm 6.1** item 5, `(FCAP.35)` | `SufficientMacro.fisherInfo_macroPacket`; ingredients `sum_tensorPower_mul_single`, `sum_tensorPower_mul_pair`, `sum_macroPacket_mul` |
| **Thm 7.1**, `(FCAP.36)`–`(FCAP.39)` | `SufficientMacro.partition_reflect`, `packet_reflect`, `sumStat_reflect`, `statImage_neg_mem`, `fibreWeight_reflect`, `macroPacket_reflect`, `recoveryWeight_reflect` |
| `(FCAP.40)` theta likelihood ratio | `RHTower.thetaCuspLikelihood_withDensity_ratio` (with `thetaCuspLikelihoodBaseMeasure`, `thetaCuspLikelihoodProbabilityMeasure_eq`) |
| `(FCAP.41)` sum statistic and macro law | `RHTower.thetaSumStat`, `thetaPacket`, `thetaMacroLaw` |
| `(FCAP.42)` recovery kernel | `RHTower.thetaRecoveryKernel`, `isMarkovKernel_thetaRecoveryKernel` |
| `(FCAP.45)` baseline disintegration | `RHTower.thetaJoint`, `thetaJoint_fst`, `thetaJoint_snd`, `thetaJoint_disintegration` |
| `(FCAP.46)` tensor likelihood ratio | `RHTower.thetaPacket_eq_withDensity`, `thetaJoint_eq_withDensity`, `thetaMacroLaw_eq_withDensity` |
| **Thm 8.1**, `(FCAP.43)` | `RHTower.thetaMacro_compProd_eq_thetaJoint`, `thetaPacket_eq_macro_recovery` |
| **Thm 8.1**, `(FCAP.44)` | `RHTower.klDiv_thetaMacroLaw`, `bhattacharyya_thetaMacroLaw` |
| **Thm 8.1**, species exit | `RHTower.thetaMacroLaw_two`, `thetaMacroLaw_two_singleton_six_ne_zero` |
| **Thm 8.1** capstone | `RHTower.thetaSufficientMacroFormation_certificate` |
| §10, `(FCAP.47)`, `(FCAP.48)` | `selection_of_cofinal` |

§9 lists four specializations of one law; the finite exponential-family theorem of §6 and the
theta theorem of §8 are the formal content, and no separate declaration is claimed for it.

## Infrastructure built here that mathlib lacks

* `bhattacharyya` — the Hellinger affinity of two finite measures on a general measurable space,
  with `bhattacharyya_eq_lintegral` (any common dominating measure computes it),
  `bhattacharyya_withDensity`, `bhattacharyya_pi` (multiplicativity over independent packets) and
  `bhattacharyya_map_eq_of_density_comp` (a deterministic observer through which the likelihood
  ratio factors preserves it exactly).  Mathlib has no `f`-divergence beyond `klDiv`.
* `map_withDensity_comp`, `compProd_withDensity_fst`, `prod_withDensity`, `lintegral_rnDeriv_mul'`
  — density transport under pushforward, composition product and independent product.
* `thetaCuspLikelihoodBaseMeasure` and `thetaCuspLikelihood_withDensity_ratio` — the corpus theta
  cusp likelihood exhibited as an exponential family in the seam variable, which is what makes the
  total gap a sufficient statistic.
* `SufficientMacro.klDiv_macroPacket_eq` — exact sufficiency for relative entropy on finite
  alphabets, obtained by applying the randomized data-processing inequality in both directions
  through the statistic kernel and the recovery kernel.

## Verification

* All seven modules elaborate with 0 errors and 0 warnings and build.
* `#print axioms` over every public theorem of
  `FixedSourceFormationCapital`, `SufficientMacroSaturation`, `FinitePacketMeasure`,
  `CommonRecoveryCapitalNeutrality`, `SufficientMacroRelativeEntropy`,
  `HellingerAffinityFactorization` and `ThetaSufficientMacroSpeciesExit`
  (101 declarations) reports only `propext`, `Classical.choice`, `Quot.sound`.
