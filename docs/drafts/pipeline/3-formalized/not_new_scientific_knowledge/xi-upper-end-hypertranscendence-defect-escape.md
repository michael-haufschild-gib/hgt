# Xi upper-end hypertranscendence by defect escape

- **ID:** xi-upper-end-defect-escape
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Lean-corpus synthesis: `XiShiftPrimeHypertranscendence`,
  `DifferentialSemilinearAutomorphism`, `UpperEndDifferentialField`, and
  `DifferentialAlgebraicBaseChange`
- **Statement:** The actual upper-end meromorphic carriers of `xi'/xi` and `xi` are
  hypertranscendental over the genuine rational coordinate field.  Global differential
  algebraicity descends to the actual upper-end carrier of every entire function, so the completed
  xi function is unconditionally hypertranscendental.  The historical `XiFrequencyCollapse`
  proposition is equivalent to that theorem and is now discharged.

## Goal

Turn the already-formalized hypertranscendental `+2` shift defect into hypertranscendence of its
primitive.  This discharges the principal proposition interface left in
`XiHypertranscendenceChain` and closes the value-level prime-source relation back onto the actual
completed function.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorem, exact leaf checks green, ordinary-axioms audit PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach

1. Prove that the upper-end rational coordinate field is exactly the differential field generated
   by the coordinate `z`, and that every rational coordinate gauge is DA over `C`.
2. Embed the entire function `z ↦ xi(-I z)` into the upper-end analytic domain and define its
   logarithmic derivative in the fraction field.
3. Prove the exact field identity: translation by `2I` minus the identity equals the filtered von
   Mangoldt carrier plus the explicit rational correction.
4. The correction is DA over both `C` and the genuine upper-end `C(z)`.  Translation normalizes
   that rational-coordinate field and commutes with derivation, so semilinear defect escape makes
   the logarithmic derivative HT directly over `C(z)`.  The constants theorem remains as a
   scalar-restriction companion rather than an intermediate hypothesis.
5. If the xi carrier were DA, its logarithmic derivative would be DA.  Contradiction.  Map every
   hypothetical global differential equation for an entire function into the actual upper-end
   field by `reshapeJet`; specialize the resulting general law to the nonzero rotation of `xi`.

## Paper proof [PROVED HERE]

Let `L(z) = xi'(-iz)/xi(-iz)` in the upper-end meromorphic field.  The completed-zeta `+2` shift
identity gives

`T_(2i)L - L - A = V`,

where `A` is the explicit rational correction and `V` is the filtered von Mangoldt carrier.  The
formal leading-echelon theorem makes `V` hypertranscendental over the actual copy of `C(z)`.  The
correction `A` is differentially algebraic over that same field.  Translation sends the coordinate
to `z+2i`, hence maps `C(z)` onto itself, and its restricted base automorphism commutes with the
inherited derivation.  Therefore `T_(2i)L - L` is hypertranscendental and normalized-base
semilinear defect escape forces `L` itself to be hypertranscendental directly over `C(z)`.

For `X(z) = xi(-iz)`, the exact chain rule gives `X'/X = -iL`.  Differential algebraicity is closed
under logarithmic derivatives and nonzero differentially algebraic scalar multiplication, so `X`
is hypertranscendental over `C(z)`.

Finally suppose an entire function `f` satisfies a nonzero global algebraic differential equation
with polynomial coefficients.  `reshapeJet` moves the point coordinate into `Polynomial C`; its
injective map into `RatFunc C`, followed by the faithful upper-end analytic and fraction-field
embeddings, produces a nonzero differential equation for the actual upper-end carrier.  Thus
upper-end hypertranscendence of a nonzero rotation implies global hypertranscendence.  Applying this
to `xi` proves `Hypertranscendental xi`.

The premise of `XiFrequencyCollapse` is exactly a global nonzero differential equation for `xi`.
Hence hypertranscendence implies the proposition vacuously, while the existing Watson chain proves
the converse.

## Novelty audit

- **Verdict:** Not new mathematical knowledge; substantial new formal synthesis and interface
  closure.
- **Reason:** Hypertranscendence of zeta/xi is classical.  Mordykhai-Boltovskoi already treated a
  xi-type function in 1914, and Ostrowski's 1920 Dirichlet-series theorem established the general
  algebraic-differential obstruction used here.  Modern work cites these results as the classical
  solution of Hilbert's problem.
- **Primary sources:** D. D. Mordykhai-Boltovskoi, *On hypertranscendence of the function
  xi(x,s)*, Izv. Politekh. Inst. Warsaw 2 (1914), 1--16; A. Ostrowski, *Über Dirichletsche Reihen
  und algebraische Differentialgleichungen*, Math. Z. 8 (1920), 241--298, English translation
  [arXiv:2211.02088](https://arxiv.org/abs/2211.02088); L. Markus, *Differential independence of
  Gamma and zeta*, J. Dynam. Differential Equations 19 (2007), 133--154.
- **Formal contribution:** The corpus now derives the classical global theorem from its own exact
  prime-source value relation, actual meromorphic carrier, normalized-base semilinear defect law,
  rational-coordinate translation covariance, an exact differential-algebraic base-change
  matroid identity, and a reusable global-to-upper-end reflection theorem.

## Lean certificate

- General base-change law:
  `diffIndepOn_differentialAdjoin_of_differentialAlgebraicOver`,
  `diffIndepOn_differentialAdjoin_iff_of_differentialAlgebraicOver`,
  `DifferentialIndependent.extendScalarsDifferentialAdjoin`, and
  `differentialIndependent_differentialAdjoin_iff`; these cover an arbitrary set of individually
  differentially algebraic coefficients. The complete statement is
  `differentialMatroidOverDifferentialAdjoin_eq_of_differentialAlgebraicOver`: the relative and
  original differential matroids are identical, so DA contraction is deletion. The exact DA/HT
  Prop interfaces are `differentialAlgebraicOver_differentialAdjoin_iff`,
  `differentialAlgebraicOver_iteratedDifferentialAdjoin_iff`, and
  `hypertranscendentalOver_iteratedDifferentialAdjoin_iff`; the latter two remain valid after an
  arbitrary observation set is adjoined. The earlier singleton equivalence remains as the
  cross-universe specialization.
- Actual rational-coordinate identification:
  `differentialAdjoin_upperEndCoordinateMero_eq`.
- Normalized-base translation interface:
  `upperEndTranslationMeroEquiv_coordinate`,
  `upperEndRationalCoordinateField_map_translation`,
  `upperEndRationalCoordinateTranslationDifferentialSemilinearEquiv`, and
  `upperEndTranslationMeroEquiv_differentialFamilyMatroid_eq`.
- Exact normalized-base generated-field covariance:
  `DifferentialSemilinearEquiv.mapIntermediateField`,
  `DifferentialSemilinearEquiv.derivationClosed_mapIntermediateField`,
  `DifferentialSemilinearEquiv.mapIntermediateField_differentialAdjoin`, and the concrete
  `upperEndTranslationMeroEquiv_map_differentialAdjoin`.  These identify the full translated
  differential field, not only the DA/HT status or represented matroid of its generators.
- Relative generated-field DA/HT covariance:
  `DifferentialSemilinearEquiv.mem_differentialMatroid_closure_image_iff`,
  `DifferentialSemilinearEquiv.hypertranscendentalOver_differentialAdjoin_image_iff`,
  `DifferentialSemilinearEquiv.differentialAlgebraicOver_differentialAdjoin_image_iff`, and their
  concrete upper-end translation specializations.  These remove any independence requirement on
  the observation set.
- Exact value-defect law:
  `RHTower.xiLogDerivRotatedUpperEnd_translation_defect`.
- Discharged correction interfaces:
  `RHTower.xiShiftTwoRationalCorrectionUpperEndCarrier_differentialAlgebraicOver_complex` and
  `RHTower.xiShiftTwoRationalCorrectionUpperEndCarrier_differentialAlgebraicOver`.
- Upper-end capstones:
  `RHTower.xiLogDerivRotatedUpperEndCarrier_hypertranscendentalOver`,
  `RHTower.xiRotatedUpperEndCarrier_hypertranscendentalOver_ratFunc`.
- General global reflection law:
  `hypertranscendental_of_rotatedEntireUpperEnd_hypertranscendentalOver`.
- Global and proposition capstones:
  `RHTower.xi_hypertranscendental`,
  `RHTower.xiFrequencyCollapse_iff_hypertranscendental`,
  `RHTower.xiFrequencyCollapse`.
- Discharged global jet interfaces:
  `RHTower.algebraicIndependent_xi_initialJets`,
  `RHTower.algebraicIndependent_xi_iteratedDeriv`,
  `RHTower.algebraicIndependent_xi_pointInitialJets`,
  `RHTower.xi_jetEval_isolated`, and
  `RHTower.xi_not_differentiallyAlgebraicOfOrder`.
- Differentiated value bridge:
  `RHTower.xiCompletedCurvatureRotatedUpperEnd_translation_defect` and
  `RHTower.xiCompletedCurvatureRotatedUpperEndCarrier_hypertranscendentalOver`.
- Exact centered reflection bridge:
  `RHTower.xiShiftTwoPrimeDefect_reflection_cocycle`,
  `RHTower.xiCenteredShiftTwoPrimeDefect_reflection`, and
  `RHTower.xiCenteredShiftTwoPrimeDefectUpperEndCarrier_hypertranscendentalOver`.
- Validation: exact leaf checks pass.  All audited declarations use only `propext`,
  `Classical.choice`, and `Quot.sound`.

## No-go closure (mandatory when falsified)

- **Exact killing theorem/mechanism:** Not falsified.
- **Strongest positive survivor:** The unconditional global completed-xi theorem and the reusable
  entire-function upper-end reflection law are formalized.
- **New insight:** The classical Ostrowski prime source can discharge the corpus's completed-xi
  frequency-collapse interface through an automorphism defect, with no asymptotic computation.
- **Status:** Route completed; it proves hypertranscendence, not RH.  Differential-algebraic and
  shift-cohomological data remain divisor-blind and do not orient the nontrivial zeros.

## Log

- 2026-07-18 — created in 1-in-progress after the filtered-prime carrier theorem passed.
- 2026-07-18 — exact upper-end, global-reflection, and proposition-interface leaves compiled;
  ordinary-axioms audit passed; moved to 3-formalized/not-new-scientific-knowledge.
- 2026-07-18 — generalized singleton base change to arbitrary DA coefficient sets; added the
  differentiated completed-curvature law and half-cocycle-centered reflection law; exact leaf and
  ordinary-axioms checks passed.
- 2026-07-18 — instantiated the generic global jet-freeness and finite-order interfaces for xi;
  linked the centered reflection value germ to its exact analytic and meromorphic carrier.
- 2026-07-19 — generalized defect escape from coefficient-fixing to normalized-base semilinear
  differential automorphisms; proved upper-end translation covariance of the actual `C(z)` field
  and its complete family matroid; exposed the rational correction's DA interfaces; and refactored
  the Xi logarithmic-derivative capstone to escape directly over `C(z)`.
- 2026-07-20 — closed the remaining generated-field interface: normalized-base differential
  automorphisms now act invertibly on intermediate fields, preserve derivation closure, and carry
  every differential adjunction exactly to the adjunction of the transformed values.  Specialized
  this law to genuine upper-end translation.
