# ULF-CJFM-1 — Lean certification record

Card: `titchmarsh-jordan-formation-reserve-functional-equation-and-information-blindness-law.md`
Promoted to Stage 3 on 2026-08-30.

## Modules

| Module | Role |
|---|---|
| `GaloisForLFunctions.HTGeometry.ConstitutiveCausalJordanFormation` | pre-existing abstract formation state, fusion, reflection, cancellation cocycle, reciprocal common-delay properness (Theorem 7.2) |
| `GaloisForLFunctions.HTGeometry.CausalJordanDriftWord` | **new** — §2, §3, §4, §6, §7 at the level of literal signed drift words, plus the exponential-family observer layer and the Euler-shell specialization |
| `GaloisForLFunctions.HTGeometry.CausalJordanTitchmarshSupport` | **new** — §5, the causal support law, derived without assuming the Titchmarsh convolution theorem |

All three are imported by `GaloisForLFunctions.HTGeometry.UniversalLawField`, which
`GaloisForLFunctions.HTGeometry` imports.

## Card result → Lean declaration

| Card | Lean |
|---|---|
| `(CJF.1)`–`(CJF.2)` word, `P`, `N` | `DriftWord.posLeg`, `DriftWord.negLeg` |
| `(CJF.3)` `D = P - N = Σδ` | `DriftWord.posLeg_sub_negLeg` |
| `(CJF.4)` `V = P + N = Σ|δ|` | `DriftWord.posLeg_add_negLeg` |
| `(CJF.5)` `2R = V - |D|` | `DriftWord.two_mul_reserve` |
| `(CJF.6)` `P = D⁺ + R`, `N = D⁻ + R` | `DriftWord.posLeg_eq`, `DriftWord.negLeg_eq` |
| `(CJF.7)` endpoint map `π` | `CausalJordanFormation.visible`, `DriftWord.formation_visible` |
| `(CJF.8)` fibre `π⁻¹(D)` is the half-line | `visible_eq_iff_exists_reserve` |
| `(CJF.9)` strict leg additivity | `DriftWord.posLeg_append`, `DriftWord.negLeg_append`, `DriftWord.formation_append` |
| `(CJF.10)` cancellation birth `c` | `CausalJordanFormation.cancellationBirth` (+ `cancellationBirth_nonneg`) |
| **Thm 3.1** `(CJF.11)` | `DriftWord.displacement_reserve_append` (and the strict form `DriftWord.reserve_append_lt`) |
| `(CJF.12)` `c = 0 ↔ xy ≥ 0` | `cancellationBirth_eq_zero_iff` |
| `(CJF.13)` `xy < 0 ⟹ c = min(|x|,|y|)` | `cancellationBirth_of_mul_neg` |
| `(CJF.14)` `(ℱ, ⋆)` commutative monoid | `formationStar`, `formationStar_comm`, `formationStar_assoc`, `formationStar_zero_left/right` |
| `(CJF.15)` monoid isomorphism from the cone | `formationChart`, `formationUnchart`, `formationChart_fuse`, `formationChartEquiv` |
| `(CJF.16)` associativity cocycle | `CausalJordanFormation.cancellationBirth_cocycle` |
| `(CJF.17)` reflection `w†` | `DriftWord.reflectWord` |
| **Thm 4.1** `(CJF.18)`–`(CJF.19)` | `DriftWord.formation_reflectWord`, `DriftWord.displacement_reflectWord`, `DriftWord.reserve_reflectWord`, `DriftWord.commonDelay_reflectWord`, `DriftWord.reflectWord_reflectWord`, `DriftWord.reflectWord_append`, `DriftWord.cancellationBirth_neg` |
| `(CJF.20)` event response `h_{δ,b,T}` | `eventResponse` |
| `(CJF.21)` its bilateral Laplace transform | `laplace_eventResponse` |
| `(CJF.22)`–`(CJF.23)` `h_w`, `B`, `T` | `wordProfile`, `totalDelay`, `totalWidth` |
| **Thm 5.1** `(CJF.25)` | `leftEdge_wordProfile`, `rightEdge_wordProfile` |
| `(CJF.26)` support width `T + V` | `closeEndpoint_sub_openEndpoint` |
| `(CJF.27)` causality `B ≥ P` | `openEndpoint_nonneg_iff` |
| `(CJF.28)`, `(CJF.29)` common delay | `common_causal_iff`, `commonDelay_drifts_eq`, `DriftWord.commonDelay_eq` |
| `(CJF.30)` single-event endpoints | `leftEdge_eventResponse`, `rightEdge_eventResponse` |
| **Cor 6.1** `(CJF.31)`–`(CJF.33)` | `DriftWord.closed_word_reserve`, `DriftWord.reserve_pos_of_closed` |
| `(CJF.34)`–`(CJF.35)` exponential family | `partitionResponse`, `driftTilt`, `expObserver`, `expObserver_univ` |
| `(CJF.36)` tilt composition | `expObserver_expObserver` (and the hypothesis-free `driftTilt_driftTilt`) |
| `(CJF.37)` common recovery `Q_u` | `splitFormation` (pre-existing) |
| **Thm 7.1** `(CJF.38)` | `observerWordAction_expObserver`, `splitFormation_observerWordAction`, and the unconditional `rawWordAction_eq` |
| `(CJF.39)` closed word, zero information | `closedWord_information_blind` |
| `(CJF.40)` reserve unbounded in a fibre | `DriftWord.exists_word_displacement_reserve`, `endpoint_blind_to_reserve` |
| `(CJF.41)` common-recovery KL isometry | `klDiv_splitFormation` (pre-existing) |
| `(CJF.42)` Euler-shell specialization | `weightMeasure`, `partitionResponse_weightMeasure`, `expObserver_weightMeasure_singleton`, `expObserver_eulerShell` |
| **Thm 7.2** `(CJF.42a)`–`(CJF.42d)` | `reciprocalDirectLeg`, `reciprocalReflectedLeg`, `reciprocalCommonDelay_inv`, `boundedReciprocalCommonDelay_iff` (pre-existing) |
| §8 conservation diagram `(CJF.43)` | `formationChart_fuse` + `formationChartEquiv` + `DriftWord.formation_append` + `DriftWord.formation_reflectWord` |
| capstones | `causalJordanWordFormation_certificate`, `titchmarshJordanFormation_certificate`, `causalJordanFormation_mechanism_certificate` |

## Titchmarsh input eliminated

The card cites the classical Titchmarsh convolution theorem as its load-bearing external input for
`(CJF.24)`.  The Lean certification does **not** assume it.  The elementary response `(CJF.20)` is a
nonzero constant on a right neighbourhood of its opening edge and on a left neighbourhood of its
closing edge; that *sign-definite edge* datum (`LeftEdge`, `RightEdge`) is stable under convolution
by a direct positivity argument (`LeftEdge.convolution`, `RightEdge.convolution`), which yields the
exact endpoint additivity for the concrete family the card actually uses.  The general Titchmarsh
theorem is therefore neither assumed nor needed.

## Verification

* Both new modules elaborate with 0 errors (`lake env lean`) and build
  (`lake build GaloisForLFunctions.HTGeometry.CausalJordanDriftWord
   GaloisForLFunctions.HTGeometry.CausalJordanTitchmarshSupport`).
* `#print axioms` over every public theorem of the three modules (110 + 20 declarations) reports
  only `propext`, `Classical.choice`, `Quot.sound`.
* No `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration.
* No hypothesis interface stands in for card content: the only hypotheses carried are the card's own
  data conditions (`δ ≠ 0`, `T > 0`, nonempty word, admitted exponential parameters).
