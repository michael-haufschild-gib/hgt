# Claim trace: Airy-tower Stokes rigidity

Date: 2026-08-03

Scope: every theorem advertised in `main.tex`, its source inputs, proof location, and Lean status.

## External inputs

| Input | Exact use | Primary source |
|---|---|---|
| Wild nonabelian Hodge correspondence | Context only; no new correspondence claimed | Biquard--Boalch, *Compos. Math.* 140 (2004), 179--204, DOI 10.1112/S0010437X03000010 |
| Core diagram attached to affine-line formal data | Diagram context and notation | Boalch--Yamakawa, *C. R. Math.* 358 (2020), 59--65, DOI 10.5802/crmath.11 |
| Loop formula | Equation `B_II = sum beta_i(e_{i-1}-e_i)-r^2+1` | Douçot, arXiv:2509.24861, Lemma 2.1 |
| Edge formula | Zero-common-part and common-level calculations | Douçot, arXiv:2509.24861, Lemma 2.2, equations (2.5)--(2.7), (4.6) |
| Rescaled ultrametric necessity | Necessity in recognition theorem | Douçot, arXiv:2509.24861, Theorem 4.2 |
| Fission-tree sharp classification/realization | From constructed sibling data to an irregular class; finite compatibility | Boalch--Douçot--Rembado, *PRIMS* 61 (2025), Lemma 3.21, Theorem 3.27, Corollary 3.28; DOI 10.4171/PRIMS/61-3-4 |
| Dual Puiseux/Fourier criterion/cabling direction | Fourier corollary and iterated-torus-knot interpretation | Hiroe, *Josai Math. Monogr.* 10 (2017), Theorem 3.10 and Section 4; arXiv:1406.5788 |
| Diagram loses fission data | Scope warning only | Douçot, *SIGMA* 22 (2026), 027, DOI 10.3842/SIGMA.2026.027 |
| Existing untwisted counts | Comparison only | Boalch, *J. Geom. Phys.* 214 (2025), 105512, DOI 10.1016/j.geomphys.2025.105512 |

## New theorem trace

| Paper claim | Proof | Lean declaration/status |
|---|---|---|
| Cyclic Puiseux stabilizer coarea, minimal orbit and source loop | Proposition 2.1 | `galoisTranslate_eq_iff`, `cyclicStabilizer_card`, `canonical_galoisOrbit_card`, `canonical_differenceNumerator_eq_firstBreak`, `orderedPairDifferenceNumeratorSum_eq`, `endomorphismIrregularityFromSheets_eq`, `diagonalLoopFromSheets_eq`; targeted build and axiom audit passed |
| Galois sheet-pair coarea and exact common-level/fission edge source | Theorem 2.2 | `ReducedCommonExponent.phase_eq_iff_modEq`, `commonDifferenceKernel_card`, `modEq_accumulatedCommonDenominator_iff`, `commonPairLayer_card_factored`, `commonPairIrregularityFromSheets_eq_coarea`, `commonPairEdgeFromSheets_eq_sourceFormula`, `zeroCommonPairEdgeFromSheets`, `unramifiedPairEdgeFromSheets`, `galois_sheet_pair_coarea_master_law`; targeted build and axiom audit passed |
| Gcd gap around `R+E` | Lemma 3.1 | `le_sub_of_lt_add_gcd`, `add_twice_le_of_add_lt_of_dvd`; passed `lake env lean` |
| Weighted tail bound | Lemma 3.2 | `weightedIrregularity_le_first`, `weightedIrregularity_lt_first_of_step`; passed |
| First-deviation strict signs | Lemma 3.3 | `diagonalLoop_neg_of_first_lt`, `diagonalLoop_pos_of_first_gt`; passed |
| Airy-tower sign/zero theorem | Theorem 3.4 | `diagonalLoop_eq_zero_iff_isAiryTower`, natural-number corollary; passed |
| Airy towers from strict divisor chains | Theorem 4.1 | `StrictDivisorChain.toCharacteristic`, `toCharacteristic_isAiryTower`, extraction round trip; passed |
| Ordered factorization construction and recovery | Theorem 4.1 | `OrderedFactorization.chainOfList`, `factors_chainOfList`, `toOrderedFactorization_toStrictDivisorChain`; passed |
| Prime-power and squarefree counts | Corollary 4.2 | `primePowerEquivComposition`, `card_primePower`, `airyTowerCount_primePower`; `FinSurjection.codeEquiv`, `SquarefreeMulTuple.equivPrimeBlockSurjection`, `card_squarefree`, `card_distinctPrimeProduct`, `airyTowerCount_distinctPrimeProduct`; passed `lake env lean` |
| Negative Fourier branch and converse under size condition | Theorem 4.3 | `isAiryTower_iff_negativeFourier_and_largeSteps`; passed |
| Separated-core formula | Theorem 5.1 | `separatedEdge_eq_right_mul_next_of_le`, symmetric branch; passed |
| Simultaneous separated realization | Theorem 5.2 | `Characteristic.levelNumerators`, `Characteristic.slopes_pairwise`, `Characteristic.foldl_gcd_levelNumerators`, `AiryChainFamily.simultaneousSeparatedRealization`, `pairwise_leadingSeparated`; passed `lake env lean` |
| Reciprocal-min ultrametricity | Proposition 5.3 | `separatedRescaledWeight_acuteIsosceles`; passed |
| Exact separated hidden fibre | Corollary 5.4 | `SeparatedFiberDatum.HiddenFiber`, `fullChainFamily_injective`, `realizedCoreEdge_eq_coreEdge`, `hiddenFiber_card`; passed `lake env lean` |
| Exact elementary pair spectrum | Theorem 6.2 | `nonempty_elementaryPairPresentation_iff_spectrum` plus three closed forms; passed |
| Decorated finite-fibre theorem | Theorem 7.1 | Local finite-type spine: `Characteristic.finite`, `finite_strictDivisorChain`, `finite_fixedWeightedCharacteristic`; passed. Pair-affinity/tree-compatibility completion in paper |
| Finite dendrogram lemma | Lemma 8.2 | `thresholdSetoid`, `thresholdSetoid_mono`; passed |
| Elementary recognition necessity/sufficiency | Theorem 8.1 | `nonempty_elementaryFissionEncoding_iff_certificate`; exact finite cophenetic encoding passed. Complex coefficient realization in paper |

## Anti-overclaim audit

- No classification of all twisted nonabelian Hodge graphs.
- No implication from equal core diagrams to isomorphic wild character varieties or isomonodromy systems.
- Distinct Airy tails are claimed to give distinct level data/fission trees/admissible deformation classes, not an unproved complete analytic Stokes-moduli invariant.
- Complexity claim is unit-cost `O(n^3)` rational comparisons, not bit complexity.
- Inconsequential coefficient support is excluded from fission-tree counting; only level and fission data are counted.
- Lean does not claim a new formal construction of analytic meromorphic connections. It verifies exact arithmetic and finite cophenetic statements used by the paper proof.

## Current audit status

The stronger requirement that every mathematical claim be proved unconditionally in Lean
invalidates any earlier whole-paper completion verdict.  Current unresolved formal obligations
include the first-principles analytic local-Fourier transformation theorem, global decorated finite-fibre compatibility,
coefficient-level elementary recognition and its stated complexity bound.  No hostile-review
completion claim is valid until those declarations exist and pass the final audit.

Current additions checked directly with `lake env lean` include the universal contact master law,
canonical cut construction and metric axioms, genuine interval-integral contact law, simultaneous
separated realization, exact hidden fibre, prime-power count, semantic ordered-surjection count,
and actual numeric squarefree ordered-Bell count.  Targeted dependency `.olean` builds passed where
needed.  `StokesPuiseuxSourceLaw` additionally verifies the genuine complex Galois action, exact
stabilizer coarea, minimal orbit size, ordered sheet-difference irregularity and recovered loop.
`StokesPairPuiseuxSourceLaw` closes the actual two-orbit complex phase, common-part and fission edge
source chain.
No full final build has yet been run for this stronger version.

## Superseded snapshot evidence

The following records the earlier, weaker audit and is retained only as history; it is not evidence
that the present all-claims-formalized goal is complete.

- `tectonic main.tex`: passed without warnings; final PDF has 12 pages.
- Final PDF was rendered to PNG page by page after the last mathematical revision; all pages passed
  visual inspection with no clipping, overlap, broken glyph, orphan page, or unreadable table.
- Each new Lean source passed `lake env lean <file>` during development.
- Targeted `lake build` passed for all six new modules.
- `lake build GaloisForLFunctions.HTGeometry`: passed, 13,635 targets.
- `scripts/formal_tools.py lint`: passed. Reported large-file warnings are repository-wide and do not
  concern these modules.
- `/tmp/hgt-airy-axioms.lean` `#print axioms` audit: only standard mathlib foundations (`propext`,
  `Classical.choice`, `Quot.sound` where applicable); no project axiom.
- `HOSTILE_REVIEW.md`: final recommendation is publishable at the stated renowned general-journal bar;
  no unresolved major revision.
