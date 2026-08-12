# `nad` folder — unconditional Lean formalization ledger

Working ledger for promoting every card in `2-fully-proven/nad` to `3-formalized/nad`.
A card is promoted only when its numbered statements are unconditional Lean theorems, the
modules are wired into an area umbrella, the axiom audit reports only `propext`,
`Classical.choice`, `Quot.sound`, and a `<id>-formalized.md` companion is issued.

## Ordered work plan (start here)

1. **Card 20, one line from done.** Prove `K_θ ⊆ { g·f : f ∈ ℂ[z] }` for one nowhere-zero `g`
   (Poincaré expansion (13) + Bezout gcd, §4 of the card), then apply
   `hasPolynomialFunctionalProjectiveBoundary_of_subset_mul_polynomial`.  Promotes card 20.
2. **Card 18, one interface from done.** The localization / admissible-gauge interface.  The
   algebraic layer and the physical reflection instance are already unconditional.
3. **Bottleneck 1 — Weyl-disc closed form** (10 cards).  Identify
   `LeafCauchyTransform.cauchyTransform_nevLeaf`'s Christoffel-weighted fibre sum with
   `(A(z)τ − C(z))/(B(z)τ − D(z))`.  Then build `ClassicalAnalyticNevanlinnaCarrierFamily` from
   `nevExtremalFamily`, then a term of `MaximalTranslationInputs`.
4. **Bottleneck 2 — Ritt / Becker--Bergweiler** (5 cards).  Linearizer equations → special-map
   trichotomy (Lattès / power / Chebyshev) → HT off that locus.  Step 2 has no corpus asset.
5. **Bottleneck 3 — Ritt--Kolchin / Bohr / Pontryagin** (2 cards).  Four of five foundations absent;
   inverse-limit covering dimension is begun (`HasCoverDimLE.of_refinedByStages`).
6. **The nineteen individually blocked cards.**  Each needs its own substrate; blockers are named in
   the table below.  Largest single items: prolate spheroidal theory (7), weak-Schatten
   ideals / Dixmier traces (12), LSZ / Haag--Ruelle transfer (31), ADH JAMS 2021 (16).

Before touching any card, apply the audit rules at the bottom of this file: grep for the *object*
not the theorem name; try to inhabit every witness structure trivially; resolve every `.lean` path
the card cites; and `#print axioms` the declaration list.

| # | Card | Status | Notes |
|---|---|---|---|
| 1 | `hypertranscendental-phase-infinite-topological-charge-rank` | **PROMOTED** | 6 new modules: `RealExponentialPolynomial`, `RealConstantCoefficientAnnihilator`, `AnseloneKorevaarTranslationRank`, `EntireExponentialCompositionDA`, `ActiveChargeRankHypertranscendence`, `ChargeRankDressingExamples` |
| 2 | `affine-jet-packet-collision-completeness` | AUDITED | `AffineCollisionMatroid.lean` + `AffineJetPacketCollisionCompletion.lean` are unconditional; the card itself says the analytic parents are not constructed. Open gate: multivariate entire-function, Hermite-interpolation, affine-chain-rule, and determinant-to-differential-independence parents. |
| 3 | `asymmetric-binary-tree-channel-rg-clock-hypertranscendence` | AUDITED | branch likelihoods, rational family, projective identities and derivative cross-numerator unconditional in `AsymmetricBinaryTreeRG.lean`; blocked on the real interval first-crossing theorem and the external HT classification. |
| 4 | `bethe-padic-holographic-rg-clock-hypertranscendence` | AUDITED | rational family (5), coprimality, all-temperature multiplier and cubic anchor (10) unconditional in `BetheHolographicIsingRG.lean`; blocked on the ordered fixed-point proof, Becker--Bergweiler, and the endpoint Möbius conjugacy (17). |
| 5 | `cofinal-cholesky-carrier-selection-threshold-law` | BOTTLENECK 1 | moment-fibre card: `nevExtremalFamily` and `cauchyTransform_nevLeaf` are built; blocked on the Weyl-disc closed form and then a term of `MaximalTranslationInputs`. |
| 6 | `compact-local-form-factor-hypertranscendence-forcing` | AUDITED | reuses `KolchinExchangeGaugeObstruction.lean`; card declines a new module. Open: intrinsic local form-factor profile / operator-change invariance and a connected-correlator transfer or locality inequality — no corpus asset. |
| 7 | `constrained-prolate-continuous-polar-charge-law` | AUDITED | large card; the Lean plan is explicit. Open gates: the concrete radial-PSWF/Bessel realization and `(51)` unconditionally, plus the true cofinal Weil floor (RH-bearing). mathlib has no prolate spheroidal theory. |
| 8 | `diamond-ising-da-scheme-rg-generation-hypertranscendence` | BOTTLENECK 2 | hierarchical-RG card: the rational-dynamics algebra is unconditional; blocked on Ritt / Becker--Bergweiler plus analytic Poincaré existence. |
| 9 | `diamond-ising-family-rg-generation-hypertranscendence` | BOTTLENECK 2 | hierarchical-RG card: the rational-dynamics algebra is unconditional; blocked on Ritt / Becker--Bergweiler plus analytic Poincaré existence. |
| 10 | `explicit-digamma-herglotz-universal-palette` | **PROMOTED** | new `HTGeometry/ExplicitDigammaPaletteIndependence.lean` closes joint Gamma-shift independence unconditionally (`DifferentialIndependent.of_finite` + `differentialIndependent_digammaShiftMero`); the cited Hardouin boundary is gone |
| 11 | `finite-jet-aperture-complete-germ-closure-law` | BOTTLENECK 1 | moment-fibre card: `nevExtremalFamily` and `cauchyTransform_nevLeaf` are built; blocked on the Weyl-disc closed form and then a term of `MaximalTranslationInputs`. |
| 12 | `gauss-paired-quasi-inner-channel-schatten-depth-law` | AUDITED | the card names `RHTower/GaussPairedChannelSchattenDepth.lean`, which **does not exist**. Card states no Lean file is added: the tree has no Hardy quasi-inner multipliers, weak Schatten ideals, or Dixmier traces. Substrate must be built. |
| 13 | `hausdorff-positive-higher-spin-cdd-cone` | AUDITED | `HausdorffPositiveCddCone.lean` proves necessity of complete monotonicity for atomic shell combinations. Open: the Hausdorff converse/uniqueness, the finite-measure analytic phase transform with normal convergence, extreme-ray classification, and the geometric q-ladder strict cone instance. |
| 14 | `hypertranscendental-collision-phase-complexity-production` | AUDITED | card declines Lean; no module. Open: a quantitative entanglement/circuit-complexity consequence — the card's own position is that a wrapper would not establish the physical theorem. |
| 15 | `identity-zero-componentwise-pauli-modular-nuclearity` | AUDITED | `FermionicFactorialTraceBound.lean` is an unconditional finite skeleton. Open: the uniformly `exp(O(n))`-conditioned identity-zero intertwiner and the compact-local intrinsically mixing projective-HT QFT. |
| 16 | `incommensurable-gamma-orbit-free-quasianalyticity` | AUDITED | `FiniteCommutingShiftPeeling.lean` + `GammaPhaseCompletion.lean` prove the many-shift dichotomy and alien-charge classification unconditionally; the Adamczewski--Dreyfus--Hardouin one-shift theorem and the scaled-Borel residue computation are hypotheses of `alienCharge_shiftWord_classification`. ADH (JAMS 2021) is the blocker. |
| 17 | `indeterminate-moment-fiber-maximal-translation-ht` | BOTTLENECK 1 | moment-fibre card: `nevExtremalFamily` and `cauchyTransform_nevLeaf` are built; blocked on the Weyl-disc closed form and then a term of `MaximalTranslationInputs`. |
| 18 | `kolchin-exchange-cocycle-obstruction` | IN PROGRESS | audit found the physical reflection anti-commutes with the derivation, so `DifferentialAlgEquiv` never applied to it; `AntiDifferentialAlgEquiv.lean` proves the orientation-reversing transport law unconditionally. `ReflectionAntiDifferential.lean` now packages `complexReflectionMeroEquiv c` as an `AntiDifferentialAlgEquiv ℂ (meroField Set.univ)`, and the whole obstruction chain (7)-(10) is ported to it. Algebraic layer complete. Open: the localization / admissible-gauge interface. |
| 19 | `moment-polynomial-blind-resolvent-complete-boundary-splitting` | BOTTLENECK 1 | moment-fibre card: `nevExtremalFamily` and `cauchyTransform_nevLeaf` are built; blocked on the Weyl-disc closed form and then a term of `MaximalTranslationInputs`. |
| 20 | `neutral-gamma-ratio-full-differential-boundary-depth-law` | AUDITED | `HasPolynomialFunctionalProjectiveBoundary` is a hypothesis whose only term in the tree is the empty class. `ConstantProjectiveBoundaryWitness.lean` now inhabits it with the constant-function class (nonzero data), so the chain is non-vacuous. the polynomial class is proved (`PolynomialRecessionLocallyUniform.lean` + `PolynomialProjectiveBoundaryWitness.lean`), and the interface is now known antitone (`.mono`) and stable under a common nowhere-zero factor (`.mul_left`). Only obligation left: `K_θ ⊆ g · ℂ[z]` for one nowhere-zero `g` — then `hasPolynomialFunctionalProjectiveBoundary_of_subset_mul_polynomial` finishes the card in one line. That set inclusion is the Poincaré expansion (13) plus the Bezout gcd of §4. |
| 21 | `nevanlinna-boundary-bauer-retract-maximal-ht` | BOTTLENECK 1 | moment-fibre card: `nevExtremalFamily` and `cauchyTransform_nevLeaf` are built; blocked on the Weyl-disc closed form and then a term of `MaximalTranslationInputs`. |
| 22 | `nonautonomous-kolchin-frequency-budget-law` | AUDITED | shares `KolchinFrequencyBudgetPhase.lean`; its `SingularKolchinFrequencyInput` is three naturals with two arithmetic constraints, already inhabited — carries no analysis. Real content: `HasCoverDimLE.of_refinedByStages`. |
| 23 | `one-species-hypertranscendental-elastic-saturation` | IN PROGRESS | `HTGeometry/ElasticChannelSaturation.lean` proves the saturation lemma (2)-(4), unit modulus of every geometric factor on the real rapidity axis, and pole-freedom of the physical strip. Remaining: Lechner's inverse-scattering construction and the q-difference rational-or-HT dichotomy are external analytic parents. |
| 24 | `open-family-hypertranscendental-cdd-qft` | AUDITED | card declines Lean pending an infinite analytic interface (reciprocal Jost duality derived dynamically, or a matrix-valued factorizing extension). No module. |
| 25 | `pick-defect-finite-selector-maximal-ht-phase-law` | BOTTLENECK 1 | moment-fibre card: `nevExtremalFamily` and `cauchyTransform_nevLeaf` are built; blocked on the Weyl-disc closed form and then a term of `MaximalTranslationInputs`. |
| 26 | `postselected-qubit-clock-integrability-fracture` | AUDITED | rational-dynamics algebra is unconditional in `PostselectedQubitRationalDynamics.lean`; blocked on hyperbolicity, the Lattès critical-point classification, and Ritt--Becker--Bergweiler. |
| 27 | `prime-log-jump-sonin-mellin-grade-frame` | AUDITED | open Lean gates are explicit: jump packet and Mellin normal theorem, canonical undeconvolved source-action intertwiner, closed-graph continuity of dagger and Mellin normal, positive self-adjoint Xi spectral realization. Terminal gate is RH itself. |
| 28 | `projective-constraint-topological-capacity-phase-law` | AUDITED | `HurwitzSurvivalWitnessInhabited.lean` proves both survival-witness classes inhabited by explicit integer families, so the phase theorems are non-vacuous **and** the witnesses carry no geometry. Open: construct the classical inputs. |
| 29 | `projective-hurwitz-one-over-forty-two-phase-transition` | AUDITED | arithmetic `1/42` gap, its uniqueness at `(2,3,7)`, and Riemann--Hurwitz eq. (8) are unconditional; the survival witness is content-free (see card 28). Open: `Δ(2,3,7)` as a group with torsion-free finite-index subgroups of unbounded index. |
| 30 | `q-ladder-reflectionless-reciprocal-jost-qft` | AUDITED | card declines a wrapper: `(7)`/`(13)` would duplicate existing corpus algebra. Open: reciprocal Jost map derived from common physical dynamics, and an admissible cosmological background with a phase-sensitive reporter. |
| 31 | `sectoral-kolchin-signature-quantum-fields` | AUDITED | card declines a wrapper for `(1)`--`(3)`; the finite algebraic content already exists in the corpus. Open: an LSZ/Haag--Ruelle transfer theorem and a locality/positivity inequality for the connected-sector profile. |
| 32 | `signed-archimedean-gamma-orbit-charge-phase-law` | AUDITED | headline orbit-charge dichotomy is genuinely unconditional (`hsep` is a data condition, not an imported theorem); but `(37)`'s upper bound `π(N) ≤ δ_G + 2m(n+1)` is unproved and no gate tracks it. |
| 33 | `singular-autonomous-ade-kolchin-frequency-law` | AUDITED | same numerical-input finding; blocked on five research-scale foundations (Ritt--Raudenbush, Kolchin dimension polynomial, inverse-limit covering dimension [begun], Bohr hull, Pontryagin--Takahashi), four with no corpus asset. |
| 34 | `singular-maximal-ht-schur-defect-collapse-law` | BOTTLENECK 1 | moment-fibre card: `nevExtremalFamily` and `cauchyTransform_nevLeaf` are built; blocked on the Weyl-disc closed form and then a term of `MaximalTranslationInputs`. |
| 35 | `singular-maximal-ht-toeplitz-weld-graph-saturation` | BOTTLENECK 1 | moment-fibre card: `nevExtremalFamily` and `cauchyTransform_nevLeaf` are built; blocked on the Weyl-disc closed form and then a term of `MaximalTranslationInputs`. |
| 36 | `spectral-type-stratified-moment-fiber-maximal-ht` | BOTTLENECK 1 | moment-fibre card: `nevExtremalFamily` and `cauchyTransform_nevLeaf` are built; blocked on the Weyl-disc closed form and then a term of `MaximalTranslationInputs`. |
| 37 | `two-state-fermionic-zero-intrinsic-mixing-rigidity` | AUDITED | the classification-free product-grid gauge-rigidity lemma is unconditional (both branches). The *global* theorem is not formalized; also open is the uniformly `exp(O(n))`-conditioned identity-zero braid intertwiner. |
| 38 | `wedge-pfg-four-point-exchange-carrier` | AUDITED | card declines Lean (formalizing only the affine reporter `(5)` would be wrapper bloat). Open: a compact-local derivation-preserving transfer theorem and a locality/positivity inequality controlling the HT coefficient. |
| 39 | `xi-euler-ray-two-node-response-barrier` | **PROMOTED** | four modules audited: capstones resolve, axiom-clean, reachable from the `RHTower` umbrella. Only an external novelty audit remained. |
| 40 | `xi-physical-prime-log-aperture-fusion-cross-kernel` | **PROMOTED** | all thirteen named declarations audited: resolve, axiom-clean, five modules wired. Only an external novelty audit remained. |
| 41 | `xi-schur-inverse-limit-atomic-condensation-law` | BOTTLENECK 1 | moment-fibre card: `nevExtremalFamily` and `cauchyTransform_nevLeaf` are built; blocked on the Weyl-disc closed form and then a term of `MaximalTranslationInputs`. |
| 42 | `identity-zero-componentwise-pauli-modular-nuclearity` (dup guard) | — | |

## Reusable infrastructure created here

- `HTGeometry/RealExponentialPolynomial.lean` — `expPolySpace`, `expPolySpaceC`, `polyExp`,
  `polyExpC`, first-order inhomogeneous solve, homogeneous law.
- `HTGeometry/RealConstantCoefficientAnnihilator.lean` — `smoothSubmodule`, `smoothDerivLM`,
  `realConstCoeffOp`, `Polynomial.aeval` operator calculus, both directions of the
  constant-coefficient solution space.
- `HTGeometry/AnseloneKorevaarTranslationRank.lean` — `realTranslate`, `translationSpan`,
  `exists_eval_separating`, Anselone–Korevaar.
- `HTGeometry/EntireExponentialCompositionDA.lean` — `differentiallyAlgebraic_cexp_comp`.
- `HTGeometry/ActiveChargeRankHypertranscendence.lean` — `eq_of_eqOn_real` (real-axis identity
  theorem), `differentiallyAlgebraic_of_mem_expPolySpaceC`.
- `HTGeometry/ElasticChannelSaturation.lean` — `mem_of_norm_orthogonalProjectionOnto_eq`,
  `mapsTo_of_compression_norm_eq`, `norm_geometricCDDStep_ofReal_eq_one`,
  `sinh_im_eq`, `geometricCDDStep_denom_ne_zero_of_physicalStrip`.
- `HTGeometry/ExplicitDigammaPaletteIndependence.lean` — `DifferentialIndependent.of_finite`,
  `differentialIndependent_digammaShiftMero_general`.
- `HTGeometry/HurwitzSurvivalWitnessInhabited.lean` — `natHurwitzProjectiveSurvivalWitness`,
  `natModularProjectiveSurvivalWitness` and their `Nonempty` corollaries.
- `HTGeometry/AntiDifferentialAlgEquiv.lean` — `algebraicIndependent_smul_units_iff`,
  `AntiDifferentialAlgEquiv`, `map_differentialJet` (`σ(jetₙ x) = (−1)ⁿ jetₙ(σ x)`),
  `differentialAlgebraicOver_map_iff` for orientation-reversing automorphisms, plus the ported
  Kolchin chain `AntiDAExchangeGaugeEquivalent`,
  `not_antiDAExchangeGaugeEquivalent_of_ratio_hypertranscendental`,
  `antiSection_hypertranscendental_of_exchangeLaw`,
  `antiHalfPhase_hypertranscendental_of_exchangeLaw`.
- `HTGeometry/ReflectionAntiDifferential.lean` — `reflectionAntiDifferentialAlgEquiv`,
  `differentialAlgebraicOver_complexReflectionMeroEquiv_iff`.
- `HTGeometry/ConstantProjectiveBoundaryWitness.lean` — `constantFunctionClass`,
  `hasPolynomialFunctionalProjectiveBoundary_constantFunctionClass`.
- `HTGeometry/PolynomialRecessionLocallyUniform.lean` — `polyRecessionAux`,
  `tendstoLocallyUniformly_congr_eventually`, `tendstoLocallyUniformly_of_continuous_param`
  (reusable: continuous two-variable function + parameter tending to a limit ⇒ locally uniform),
  `poly_scaled_translate_tendstoLocallyUniformly`.
- `HTGeometry/PolynomialProjectiveBoundaryWitness.lean` — `polynomialFunctionClass`,
  `TendstoLocallyUniformly.comp_tendsto`, `exists_coeff_sup_natDegree_ne_zero`,
  `hasPolynomialFunctionalProjectiveBoundary_polynomialFunctionClass`,
  `HasPolynomialFunctionalProjectiveBoundary.mono` (the interface is antitone in the coefficient
  class, so it suffices to prove it for a class *containing* the Gamma-ratio class),
  `constantFunctionClass_subset_polynomialFunctionClass`,
  `HasPolynomialFunctionalProjectiveBoundary.mul_left` (a common nowhere-zero factor is absorbed
  into the normalization — the formal content of the paper's "restoring the cleared denominator and
  the common gcd as one meromorphic functional normalization").

## Promotion heuristic that works

A card whose *only* unchecked gates are novelty / literature / specialist audits is a promotion
candidate: the formalization is done and what remains is verifying the declaration list.  Two of the
four promotions came from exactly this sweep (`xi-physical-prime-log-aperture-fusion-cross-kernel`,
`xi-euler-ray-two-node-response-barrier`).  It is not sufficient, though — of the ten cards matching
the pattern, `neutral-gamma-ratio-...` fails on a vacuous interface and
`signed-archimedean-gamma-...` fails on an untracked half-proved inequality.  Always audit the
declarations.

## The second bottleneck: Becker--Bergweiler / Ritt (unblocks five cards)

`asymmetric-binary-tree-channel-rg-clock-hypertranscendence`,
`bethe-padic-holographic-rg-clock-hypertranscendence`,
`diamond-ising-da-scheme-rg-generation-hypertranscendence`,
`diamond-ising-family-rg-generation-hypertranscendence` and
`postselected-qubit-clock-integrability-fracture` all have the *same* shape: their rational-dynamics
algebra is already unconditional in Lean
(`AsymmetricBinaryTreeRG.lean`, `BetheHolographicIsingRG.lean`,
`PostselectedQubitRationalDynamics.lean` — no conditional theorem packages an external input), and
the hypertranscendence conclusion in every case needs one external classification: the
Ritt / Becker--Bergweiler theorem that a solution of `f ∘ R = R ∘ f` for a rational `R` of degree
`≥ 2`, or of Schröder's / Böttcher's / Abel's equation, is hypertranscendental unless the map is
special (Lattès, power, Chebyshev).  Cards 3, 4, 8 and 26 additionally need one real-calculus item
each (ordered fixed point, first crossing, Poincaré existence, hyperbolicity).

Lead checked and **negative**: the `Bottcher` theorem area (361 modules) contains no
hypertranscendence statement at all — `grep -rl 'Hypertranscendental|hypertranscendent'` over
`GaloisForLFunctions/Bottcher` hits only `STATUS.md`.  Its strongest result in this direction is
`BottcherNotRational.bottcherCoord_not_rational`: the Böttcher coordinate satisfies no polynomial
identity `q·φ = p`, i.e. it is *not rational*.  Non-rationality is strictly weaker than
hypertranscendence, and the q62 capstones (`q62_independence`, `q62_phiMero_*`) are differential
*independence* statements about a specific two-map configuration, not the general classification.
So the Ritt / Becker--Bergweiler theorem has to be built; there is no shortcut through `Bottcher`.

The realistic decomposition, in dependency order: (i) the linearizer functional equations
(Schröder `φ ∘ R = λ·φ`, Böttcher `φ ∘ R = φ^k`, Abel `φ ∘ R = φ + 1`) as differential-field
statements — the `Bottcher` area supplies the analytic existence side; (ii) the special-map
trichotomy (Lattès / power / Chebyshev) as a decidable condition on `R`; (iii) the HT conclusion off
that locus.  Step (ii) is the part with no corpus asset whatsoever.

## The third bottleneck: the Ritt--Kolchin / Bohr / Pontryagin package (cards 22, 33)

Both Kolchin frequency cards route through `KolchinFrequencyBudgetPhase.lean`, whose
`SingularKolchinFrequencyInput` turns out to be a purely numerical structure — three naturals and
two inequalities, already inhabited by `singularKolchinFrequencyInput_diagonal`.  The theorem above
it is arithmetic.  The genuine obligations are the five foundations listed in card 33 §10:
Ritt--Raudenbush finite prime decomposition of radical differential ideals; the Kolchin dimension
polynomial and its eventual constancy; covering dimension of inverse limits of compact metric spaces
(**begun**: `CoveringDimension.HasCoverDimLE.of_refinedByStages`, axiom-clean); the Bohr
almost-periodic compact hull; and Pontryagin--Takahashi dimension/rank duality.  Four of the five
have no corpus asset.

## Standing audit rule discovered in this folder

Twice now a card sentence naming an external classical parent has been stale, and once a "classical
input witness" turned out to be a content-free structure.  Before attacking any card:

1. grep the corpus for the *object* the card names, not the theorem name — the parent is often
   already proved under a different heading (`digammaShiftMero`, `nevExtremalFamily`);
2. read the witness/interface `structure` field by field and try to inhabit it trivially — if you
   can, the theorems above it are non-vacuous but carry none of the card's geometry.

## Triage of the remaining cards

Reading every card's own Lean section splits them three ways.

**(A) Card declines Lean; nothing local exists.**  `hypertranscendental-collision-phase-complexity-production`,
`open-family-hypertranscendental-cdd-qft`, `q-ladder-reflectionless-reciprocal-jost-qft`,
`sectoral-kolchin-signature-quantum-fields`, `wedge-pfg-four-point-exchange-carrier`,
`compact-local-form-factor-hypertranscendence-forcing`, `postselected-qubit-clock-integrability-fracture`,
`asymmetric-binary-tree-channel-rg-clock-hypertranscendence`,
`bethe-padic-holographic-rg-clock-hypertranscendence`,
`diamond-ising-da-scheme-rg-generation-hypertranscendence`,
`diamond-ising-family-rg-generation-hypertranscendence`, `hausdorff-positive-higher-spin-cdd-cone`,
`gauss-paired-quasi-inner-channel-schatten-depth-law`, `prime-log-jump-sonin-mellin-grade-frame`,
`two-state-fermionic-zero-intrinsic-mixing-rigidity`.  These need the substrate built.

**(B) Lean exists but rests on named classical inputs (hypotheses).**
`incommensurable-gamma-orbit-free-quasianalyticity` (ADH, scaled Borel),
`neutral-gamma-ratio-full-differential-boundary-depth-law`,
`nonautonomous-kolchin-frequency-budget-law` (Bohr/Pontryagin, Ritt--Kolchin),
`singular-autonomous-ade-kolchin-frequency-law`, `moment-polynomial-blind-resolvent-...`,
`nevanlinna-boundary-bauer-retract-maximal-ht`, `pick-defect-finite-selector-...`,
`spectral-type-stratified-moment-fiber-maximal-ht`, `xi-schur-inverse-limit-...`,
`projective-constraint-topological-capacity-phase-law`,
`projective-hurwitz-one-over-forty-two-phase-transition`,
`signed-archimedean-gamma-orbit-charge-phase-law`, `indeterminate-moment-fiber-maximal-translation-ht`,
`cofinal-cholesky-carrier-selection-threshold-law`, `finite-jet-aperture-complete-germ-closure-law`,
`constrained-prolate-continuous-polar-charge-law`, `affine-jet-packet-collision-completeness`,
`identity-zero-componentwise-pauli-modular-nuclearity`,
`singular-maximal-ht-schur-defect-collapse-law`,
`singular-maximal-ht-toeplitz-weld-graph-saturation`,
`kolchin-exchange-cocycle-obstruction`, `xi-euler-ray-two-node-response-barrier`,
`xi-physical-prime-log-aperture-fusion-cross-kernel`.  These need the named inputs discharged.

**(C) Complete but for a novelty audit.**  `explicit-digamma-herglotz-universal-palette` — closed
and promoted.  The corpus already owned `digammaShiftMero` in `meroField Set.univ` together with its
shift law and the finite pairwise-incongruent independence theorem
(`ShiftedDigammaFamilyIndependence.differentialIndependent_digammaShiftMero`); the only missing
pieces were the finitary extension of `DifferentialIndependent` to an arbitrary index and the
instantiation at `alpha_n = 1/(n+2)`.  Lesson for the rest of the folder: a card sentence naming an
external classical parent is frequently stale — grep the corpus for the object first.


## The Nevanlinna bottleneck (unblocks ~10 cards)

The corpus **already constructs** the classical N-extremal Nevanlinna family unconditionally:
`NevExtremalFamily.nevExtremalFamily h h0b h0 : ClassicalNevanlinnaExtremalFamily s` for every
`PositiveMomentForm s`, `BoundedKernel s 0`, `s 0 = 1`, with
`exists_classicalNevanlinnaExtremalFamily`, `NevBauerUnconditional.*` and
`NevBauerMarkovFacesUnconditional.*` on top of it.  Every card sentence saying "the classical
Nevanlinna family remains an explicit structure input" is therefore stale for the *real-line*
matrix.

What is genuinely missing is one level up, and it is the same object for
`nevanlinna-boundary-bauer-retract-maximal-ht`, `spectral-type-stratified-moment-fiber-maximal-ht`,
`indeterminate-moment-fiber-maximal-translation-ht`, `pick-defect-finite-selector-maximal-ht-phase-law`,
`singular-maximal-ht-schur-defect-collapse-law`,
`singular-maximal-ht-toeplitz-weld-graph-saturation`,
`moment-polynomial-blind-resolvent-complete-boundary-splitting`,
`cofinal-cholesky-carrier-selection-threshold-law`,
`finite-jet-aperture-complete-germ-closure-law` and `xi-schur-inverse-limit-atomic-condensation-law`:

1. **`ClassicalAnalyticNevanlinnaCarrierFamily s` from `nevExtremalFamily`**
   (`AnalyticNevanlinnaCarrierBridge.lean`).  Needs the *entire* matrix `a,b,c,d : ℂ → ℂ`
   restricting to `nevArealInf … nevDrealInf` on `ℝ`, with `det = 1`, together with the two
   Cauchy-transform identities `∫ (x−z)⁻¹ dν_τ = (aτ+b)/(cτ+d)` and `∫ (x−z)⁻¹ dν_∞ = a/c`.
   `NevanlinnaEntire.nevanlinna_entire_unimodular` and `NevanlinnaRealMatrix.nev*_ofReal` already
   supply the entire entries and their real restrictions, and
   `LeafCauchyTransform.cauchyTransform_nevLeaf` already evaluates the leaf transform as the
   Christoffel-weighted fibre sum `∑_{ξ ∈ F_τ} λ(ξ)/(ξ − z)`.  **The single open step is the closed
   form**: identify that fibre sum with `(A(z)τ − C(z))/(B(z)τ − D(z))`.  This is the Nevanlinna
   parametrization proper — the Weyl-disc/Christoffel--Darboux limit — and it is the highest-leverage
   unproved statement in the folder.
2. **A term of `MaximalTranslationInputs`** (`NevanlinnaBoundaryFaceMaximalTranslation.lean`):
   `HasMinimalExponentialType F.c`, `∀ z, ¬(F.c z = 0 ∧ F.d z = 0)`, a zero of `F.c`, a regular
   point of `F.c`, `0 < z.im → 0 < (F.quotient z).im`, and `IsGδ {ν | MaximalTranslationDifferentialFree ν}`.
3. **Leaf/label covariance under an arbitrary normalization change**, to upgrade
   `carrierProjector_eq_of_leaf_label_covariance` to an unconditional normalization-independence
   statement.

These three are the highest-leverage remaining targets in the folder.

## Bottleneck 1 — the exact Lean statement to prove next

Everything around it exists.  Write this, in a new module importing `LeafCauchyTransform` and
`NevanlinnaRealMatrix`:

```text
theorem cauchyTransform_nevLeaf_eq_fraction
    (h : PositiveMomentForm s) (h0b : BoundedKernel s 0) (h0 : s 0 = 1)
    (tau : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    (∫ x, ((x : ℂ) - z)⁻¹ ∂(nevLeaf h h0b h0 tau : Measure ℝ))
      = (nevAentire s z * tau - nevCentire s z) / (nevBentire s z * tau - nevDentire s z)
```

with the `∞` companion `… = nevAentire s z / nevCentire s z`.  The left side is already evaluated as
the Christoffel-weighted fibre sum by `LeafCauchyTransform.cauchyTransform_nevLeaf`; the entire
entries and their real restrictions are `NevanlinnaEntire.nevanlinna_entire_unimodular` and
`NevanlinnaRealMatrix.nev*_ofReal`.  The classical proof is the Weyl-disc limit: the finite-`n`
Cauchy transforms of the quasi-orthogonal quadrature measures are the linear fractional images of
the Nevanlinna matrix truncations, and the discs nest to a point because the problem is
indeterminate.  `GaussQuadrature.lean`, `QuasiQuadrature.lean`, `SecondKindGlobal.lean` and
`ChristoffelLimitFormula.lean` are the finite-`n` side.

**First brick laid.**  `HTGeometry/AtomicCauchyTransformRational.lean` (axiom-clean, wired) proves
the finite-stage algebra the Weyl-disc argument runs on:

```text
sum_div_eq_atomicCauchy_ratio
  -- ∑ₖ wₖ/(xₖ − z) = (∑ₖ wₖ ∏_{j≠k}(x_j − z)) / ∏_j (x_j − z)
weights_eq_zero_of_atomicCauchyNumerator_eq_zero
  -- distinct nodes: the cleared numerator vanishes identically only if every weight does
```

**Correction to the route, checked.**  `cauchyTransform_nevLeaf` produces a `tsum` over
`↥((nevMatrixDataInf h h0b).finiteDenominatorFiber tau)`, and that fibre is *countable discrete*,
not finite — `FiberFinite.finite_finiteDenominatorFiber_inter` only gives finiteness on bounded
intervals.  So the closed form cannot be obtained by clearing denominators directly on the fibre;
`sum_div_eq_atomicCauchy_ratio` applies to **finite truncations**.

The correct route is the classical one, and **the finite stage is now done**:

- `AtomicCauchyTransformRational.sum_div_eq_atomicCauchy_ratioOn` — a weighted Cauchy sum over an
  explicit finite node set is an explicit numerator/denominator ratio;
- `GaussNodeDenominator.eval_monicOrtho_eq_prod_gaussNodes` — the denominator *is* the orthogonal
  polynomial: `p_{n+1}(z) = ∏_{x ∈ gaussNodes s n} (z − x)`;
- `GaussNodeDenominator.gaussSum_cauchy_eq_secondKind_ratio` — **the finite-stage closed form**

  ```text
  ∑_{x ∈ gaussNodes s n} χ(x)/(x − z)  =  −(s₀ · q_{n+1}(z)) / p_{n+1}(z)      (p_{n+1}(z) ≠ 0)
  ```

  proved from `momentFunctional_eq_gaussSum` applied to `firstKindDividedDiff s (n+1) z`, whose
  moment functional is `s₀·q_{n+1}(z)` (`momentFunctional_firstKindDividedDiff`) and whose value at
  a node `x` is `−p_{n+1}(z)/(x − z)` (`mul_firstKindDividedDiff` + `mem_gaussNodes_iff`).

All axiom-clean and wired.  **What is left of Bottleneck 1 is the limit, and its precise missing
link is now identified.**  The corpus already has the truncated Nevanlinna entries
`EntryComplexLimit.nevAtruncC / nevBtruncC / nevCtruncC / nevDtruncC` and their locally uniform
convergence (`EntryUniformLimit.tendstoUniformlyOn_nevB_series`, `…_nevD_series`,
`tendstoUniformlyOn_bilinearLimit`), plus `NodeConvergence` and `ChristoffelLimitFormula` for the
measure side.

**Correction, checked.**  The truncated entries are *not* series in orthonormal polynomials — they
are already in the same `monicOrtho`/`secondKind` family as the finite-stage closed form.  Reading
`NevanlinnaPluecker.bilinearPartialSum`:

```text
bilinearPartialSum s f G N z = ∑_{k < N} f k · G z k / ‖monicOrtho s k‖²
nevAtruncC s n z = ‖p₀‖² · z · bilinearPartialSum s (q_k(0)) (q_k(·)) (n+1) z
nevBtruncC s n z = −1 + ‖p₀‖² · z · bilinearPartialSum s (q_k(0)) (p_k(·)) (n+1) z
```

(and `C`, `D` with `p_k(0)` in the first slot), where `p_k = monicOrthoC`, `q_k = secondKindC`.

So no normalization dictionary is needed.  The real remaining identity is the **convergent
identification**: `A_n/B_n` and `C_n/D_n` are consecutive convergents of the J-fraction, and the
finite-stage closed form `−s₀·q_{n+1}(z)/p_{n+1}(z)` is one of them.  `NevBDWronskian.nevBD_wronskian`
supplies the determinant relation between the pairs.  Once the convergent is identified, the limit is
a direct application of `EntryUniformLimit.tendstoUniformlyOn_nevB_series` and its companions.
Two further facts checked, both load-bearing for planning:

* `nevAtruncC / nevBtruncC / nevCtruncC / nevDtruncC` have **no downstream consumer** — they occur
  only in `EntryComplexLimit.lean`.  The objects actually feeding `nevMatrixDataInf` are the real
  entries `NevanlinnaRealMatrix.nevArealInf … nevDrealInf`.  So two links are needed, not one:
  (a) trunc → real entries, which is what `EntryUniformLimit` is for, and
  (b) trunc → J-fraction convergent, which is new.
* There is **no convergent / J-fraction / continued-fraction machinery anywhere in `HTGeometry`**
  (searched: `convergent`, `Jfraction`, `continuedFraction`).  Link (b) must be built from the
  three-term recurrence — `monicOrtho` and `secondKind` satisfy the same recursion with different
  initial data, which is exactly `NevBDWronskian.nevBD_wronskian`'s content.

**Link (b) is DONE.**  `HTGeometry/NevTruncConvergent.lean` (wired, axiom-clean) proves all four:

```text
A_n(z) = −h₀·(R_{n+1}(0)R_n(z) − R_n(0)R_{n+1}(z))/h_n
B_n(z) =  h₀·(Q_{n+1}(z)R_n(0) − Q_n(z)R_{n+1}(0))/h_n
C_n(z) = −h₀·(Q_{n+1}(0)R_n(z) − Q_n(0)R_{n+1}(z))/h_n
D_n(z) = −h₀·(Q_{n+1}(0)Q_n(z) − Q_n(0)Q_{n+1}(z))/h_n
```

The `±1` in `B`, `C` is cancelled exactly by the `1/h₀` constant of the *mixed* CD identity, which
the pure ones do not carry.

**The finite-stage assembly, derived by hand and ready to type.**  Put
`τ_n := Q_{n+1}(0)/R_{n+1}(0)`.  In `(A_n τ − C_n)/(B_n τ − D_n)` the factor `h₀/h_n` cancels, and:

* coefficient of `Q_n(z)` in the denominator is `−R_{n+1}(0)τ + Q_{n+1}(0) = 0`;
* coefficient of `R_n(z)` in the numerator is `−(R_{n+1}(0)τ − Q_{n+1}(0)) = 0`;
* the surviving coefficient in both is `R_n(0)τ − Q_n(0) = (Q_{n+1}(0)R_n(0) − Q_n(0)R_{n+1}(0))/R_{n+1}(0)`,
  which by `momentWronskian_eq` evaluated at `0` equals `(−h_n/h₀)/R_{n+1}(0)`.

Both factors cancel, leaving

```text
(A_n τ_n − C_n)/(B_n τ_n − D_n) = R_{n+1}(z)/Q_{n+1}(z),
```

which is the finite-stage transform up to the `toCarrierMatrix` sign convention
`(a,b,c,d) = (−A,C,B,−D)`, `carrierFraction = −stieltjesFraction`, and `h₀ = s₀`.
`NevDenominatorFactor.lean` already evaluates `momentWronskian_eq` at `0`, so that input is present.

Type this, then apply the existing uniform limits and Bottleneck 1 is closed.

**Attempted and backed out.**  I wrote `nevTrunc_moebius_eq_convergent` with the two key steps as

```text
A_n·τ_n − C_n = −R_{n+1}(z)/R_{n+1}(0)
B_n·τ_n − D_n = −Q_{n+1}(z)/R_{n+1}(0)
```

and both reduce correctly by hand (group the bracket over `R_{n+1}(0)`; the `R_n(z)` / `Q_n(z)`
terms cancel and the Wronskian `monicOrthoC_wronskian h n 0 = −h_n/h₀` collapses the constants).
The Lean attempt failed only on `linear_combination` coefficient bookkeeping after `field_simp`.
**Next time do not use `field_simp` here** — clear `R_{n+1}(0)` by hand, group the bracket as
`R_n(z)·(Q_{n+1}(0) − R_{n+1}(0)τ) + R_{n+1}(z)·(R_n(0)τ − Q_n(0))`, kill the first factor by the
definition of `τ_n`, and rewrite the second with `monicOrthoC_wronskian`.  The block was removed so
the module stays green; the four convergent forms it depends on are proved and wired.

**Historical note.**  Link (b) was largely already written — in `NevanlinnaPluecker.lean`.**  I started building a mixed
Christoffel--Darboux identity and Lean rejected the declaration as already existing.  The corpus has
`christoffelDarboux`, `secondKindChristoffelDarboux`, `mixedChristoffelDarboux` **and their complex
versions** `christoffelDarbouxC`, `secondKindChristoffelDarbouxC`, `mixedChristoffelDarbouxC`.

More: `NevanlinnaPluecker.lean` lines ~95–135 already performs the exact conversion link (b) needs.
Its `F1`–`F4` rewrite the four `bilinearPartialSum`s at arguments `(z, 0)` into the bilinear
combinations of `Q_{n+1}, Q_n, R_{n+1}, R_n`:

```text
F3 : Q_{n+1}(z)·R_n(0) − Q_n(z)·R_{n+1}(0)
       = h_n · ( z · Σ_{k≤n} Q_k(z)R_k(0)/h_k  −  1/h₀ )
```

and `F1`, `F2`, `F4` are the other three corners.  Since `nevAtruncC … nevDtruncC` are exactly
`±1 + h₀·z·(those sums)`, `F1`–`F4` *are* the dictionary from the truncations to the convergent data
`(Q_{n+1}, Q_n, R_{n+1}, R_n)`.

So link (b) reduces to reading `nevBtruncC`/`nevAtruncC` off `F1`–`F4` and comparing with
`gaussCauchy_polynomial_identity`.  Nothing further has to be invented.

**Earlier inventory (still valid).**  `SecondKindMomentPolynomials.lean` has the
whole J-fraction structure:

```text
monicOrtho_succ_succ  : Q_{n+2} = (X − a_n)·Q_{n+1} − b_n·Q_n
secondKind_succ_succ  : R_{n+2} = (X − a_n)·R_{n+1} − b_n·R_n      (R₀ = 0, R₁ = 1)
momentWronskian s n   := Q_{n+1}·R_n − Q_n·R_{n+1}
```

i.e. `monicOrtho` and `secondKind` are the two solutions of one three-term recurrence with the two
standard initial conditions — so `R_{n+1}/Q_{n+1}` *is* the (n+1)-st J-fraction convergent by
construction, and the finite-stage closed form already proved says the stage-`n` Cauchy transform is
`−s₀` times it.  Link (b) is therefore: express `nevAtruncC … nevDtruncC` (which are
`bilinearPartialSum`s over the same two families) in terms of `Q`, `R` via the recurrence, and read
off that `A_n/B_n` and `C_n/D_n` are consecutive convergents.  `momentWronskian` and
`NevBDWronskian.nevBD_wronskian` give the normalisation — and `momentWronskian_eq` is **already
proved**, with `OrthonormalWronskian.lean` stating it in terms of
`momentInner s (monicOrtho s 0) (monicOrtho s 0)`, which is precisely the `‖p₀‖²` prefactor
appearing in `nevAtruncC … nevDtruncC`.  `OrthonormalWronskian.lean` is therefore the natural home
for link (b); start there, not from scratch.

Other starting points, located: the **three-term recurrence** is in
`OrthogonalMomentPolynomials.lean` around line 381 (`X * monicOrtho s (n+1) − monicOrtho s (n+2)`
expanded in the lower basis), and the **Christoffel--Darboux formula** is a whole module,
`ChristoffelDarboux.lean`.  Together with `NevBDWronskian.nevBD_wronskian` these are the three
inputs the convergent identification needs; nothing else has to be built from scratch for link (b).

Do not attempt the infinite-fibre shortcut.

Once this holds, `ClassicalAnalyticNevanlinnaCarrierFamily` is a structure instance, and the ten
moment-fibre cards reduce to producing a term of `MaximalTranslationInputs`
(`NevanlinnaBoundaryFaceMaximalTranslation.lean`, six named analytic fields).

## BOTTLENECK 1, ITEM 1 IS CLOSED — the Weyl-disc closed form is proved `[PROVED]`

The statement this file called "the highest-leverage unproved statement in the folder" is now an
unconditional theorem, and `ClassicalAnalyticNevanlinnaCarrierFamily` is constructed.

Three new modules, all axiom-clean (`propext`, `Classical.choice`, `Quot.sound`), all wired into
`GaloisForLFunctions.HTGeometry`, all under the standing hypotheses `PositiveMomentForm s`,
`BoundedKernel s 0`, `s 0 = 1` and nothing else.

### `HTGeometry/NevLeafCauchyMoebius.lean`

- `nevTrunc_cauchy_identity` — the finite stage, cleared of denominators:

  ```text
  (Bₙ(z)·τ − Dₙ(z)) · ∫(x − z)⁻¹ dμₙ = −s₀·(Aₙ(z)·τ − Cₙ(z)),
  μₙ = quasiMeasure s n (nevBeta s n τ / nevAlpha s n τ).
  ```

  Multiply `quasiMeasure_cauchy_identity_of_im_ne_zero` by the common factor `(h₀/hₙ)·nevAlpha`
  supplied by `nevTruncNumeratorC_eq_quasi` and `nevTruncDenominatorC_eq_quasi`.
- `nevInf_cauchy_identity` — the limit `(B(z)·τ − D(z))·∫(x − z)⁻¹ dν_τ = −(A(z)·τ − C(z))`.
  `exists_tendsto_quasiProbMeasure_nevLeaf` gives weak convergence of the selected quadrature
  levels; `tendsto_cauchyTransform_of_tendsto` carries the transform; `tendsto_nev{A,B,C,D}truncC`
  composed with `Tendsto (goodLevel h τ ∘ φ) atTop atTop` carries the entries;
  `tendsto_nhds_unique` closes it.
- `nevInf_denominator_ne_zero` — `B·τ − D ≠ 0` off the real axis.  A vanishing denominator forces a
  vanishing numerator, and then `A D − B C = 0`, contradicting the determinant identity
  (available at every complex point through `boundedKernel_global`).
- **`cauchyTransform_nevLeaf_eq_moebius`** — the Weyl-disc closed form

  ```text
  ∫(x − z)⁻¹ dν_τ = −(A(z)·τ − C(z)) / (B(z)·τ − D(z)).
  ```

### `HTGeometry/NevLeafInfinityCauchyMoebius.lean`

The same at the parameter `∞`, where the denominator degenerates to `B` alone:
`nevLeaf_infinity_eq_fiberMeasure`, `exists_tendsto_quasiProbMeasure_nevLeafInf`,
`ofReal_nevAlphaInf`, `ofReal_nevBetaInf`, `nevAtruncC_closedInf`, `nevBtruncC_closedInf`,
`nevAtruncC_eq_quasiInf`, `nevBtruncC_eq_quasiInf`, `nevTruncInf_cauchy_identity`,
`nevInf_cauchy_identity_infty`, `nevBinf_ne_zero`, and
**`cauchyTransform_nevLeafInf_eq_ratio`**: `∫(x − z)⁻¹ dν_∞ = −A(z)/B(z)`.

### `HTGeometry/AnalyticNevanlinnaCarrierConstruction.lean`

**`analyticNevCarrierFamily h h0b h0 : ClassicalAnalyticNevanlinnaCarrierFamily s`** and
`exists_classicalAnalyticNevanlinnaCarrierFamily`.  Carrier convention
`(a, b, c, d) = (−A, C, B, −D)`, so `det = A D − B C = 1`, the real restrictions are exactly
`toCarrierMatrix`, and the two Cauchy fields are the two closed forms above.

### `HTGeometry/NevanlinnaCarrierDenominatorRow.lean`

Three of the six `MaximalTranslationInputs` fields, for the constructed family:
`nevInf_no_common_zero` / `analyticNevCarrierFamily_noCommonZero`;
`exists_nevBrealInf_eq_zero` and `exists_nevBinf_eq_zero` / `analyticNevCarrierFamily_exists_zero`
(the leaf at infinity is a probability measure carried by the zero set of `B`, so that set is
nonempty); `nevBinf_I_ne_zero` / `analyticNevCarrierFamily_regular`.  Also
`analyticNevCarrierFamily_quotient : F.quotient z = D(z)/B(z)`.

### Two corrections to this ledger

- `nevTrunc_moebius_eq_convergent` is **present and proved** in `NevTruncConvergent.lean`; the note
  saying it was backed out is stale.
- `NevTruncCauchyTransform.quasiSum_cauchy_eq_nevTruncC` already carried the finite-stage Weyl-disc
  form.

## BOTTLENECK 1, ITEM 2 IS BLOCKED BY A SIGN ERROR IN THE INTERFACE `[DISPROVED FIELD]`

`MaximalTranslationInputs` (in `NevanlinnaBoundaryFaceMaximalTranslation.lean`) demands

```text
upperMap : ∀ z, 0 < z.im → 0 < (F.quotient z).im,   F.quotient z = −F.d z / F.c z = D(z)/B(z).
```

`F.quotient z` is the pole of the Möbius map `τ ↦ (a τ + b)/(c τ + d)`.  That map sends
`ℝ ∪ {∞}` into the **open upper half-plane**, because every image is `∫(x − z)⁻¹ dν_τ`, a Cauchy
transform of a probability measure at `Im z > 0`.  A Möbius transformation carries one open
half-plane onto the disc bounded by that circle and the other onto its exterior, and the pole goes
to `∞`, which is exterior.  The closed upper half-plane maps into the disc, so **the pole lies in
the open lower half-plane**:

```text
0 < z.im  ⟹  (F.quotient z).im < 0.
```

Two independent confirmations.

1. Algebraic.  Writing `Im f(τ) = Q(τ)/|Bτ − D|²` with
   `Q(τ) = −Im(A B̄)|τ|² + Im((A D̄ − C̄ B) τ) − Im(C D̄)`, a direct computation gives `Q(D/B) = 0`
   identically, while `Q > 0` on `ℝ`.  With `q = q₁ + i q₂`, subtracting `Q(q₁)` gives
   `q₂ (α q₂ + Re β) = −Q(q₁) < 0`, where `α = −Im(A B̄) > 0` and `β = A D̄ − C̄ B`.  Hence
   `Re β ≠ 0`; and `β = G(z, z̄)` for `G(z, w) = A(z)D(w) − C(w)B(z)` with `G(z, z) = 1`, so
   `Re β → 1` as `z → ℝ`.  `Re β` is continuous and nonvanishing on the connected upper half-plane,
   so `Re β > 0`, so `q₂ < 0`.
2. A model of the same shape: `f(τ) = i + ε(τ − i)/(τ + i)` maps `ℝ` onto a small circle about `i`
   inside the upper half-plane and has its pole at `−i`.

So `MaximalTranslationInputs` is **uninhabitable** for the canonical family, and
`boundaryCarrierFace_maximalTranslationPhase_dense_residual` is presently vacuous.

**Repair.**  The deepest layer already needs only `≠ 0`
(`projectiveNevanlinnaValueLinftyControl` takes `hq : (F.quotient z).im ≠ 0`;
`continuous_projectiveCauchyPower` takes `q.im ≠ 0`).  Two hypothesis families have to move:

* the evaluation points of the Cauchy transform, `0 < z.im`, need only `z.im ≠ 0`;
* the jet poles `F.quotient (z i)` must stay strictly on **one** side of the real axis — the
  `Sum.elim x (star ∘ x)` injectivity step in `NormalizedProjectiveCauchyDensityControl` genuinely
  uses that, so `≠ 0` alone is not enough there.

The consistent repair is therefore to run the packets in the **lower** half-plane in `z`: replace
`0 < z.im` on evaluation nodes by `z.im < 0`, keep `0 < (F.quotient (z i)).im`, and restate
`upperMap` as `∀ z, z.im < 0 → 0 < (F.quotient z).im`.  Nineteen modules mention the positivity
form: `CompactNevanlinnaUniformProbe`, `AnalyticNevanlinnaCarrierRelationFree`,
`SingularContinuousFullTranslationFamilyFreenessUniversalityLaw`,
`NevanlinnaNoncriticalProjectiveCompactPatch`, `ConstrainedCauchyJetControllability`,
`NevanlinnaTranslatedExpandedEvaluationCompactPatch`, `NevanlinnaBoundaryFaceMaximalTranslation`,
`ProjectiveCauchyDensityControl`, `ProjectiveNevanlinnaGenericity`,
`AnalyticNevanlinnaCarrierBridge`, `BoundaryCarrierTranslationFreeness`, `NevanlinnaJetTriangular`,
`CarrierHerglotzPresentationFree`, `ProjectiveNevanlinnaPolynomialEscape`,
`NormalizedProjectiveCauchyDensityControl`, `NevanlinnaExpandedEvaluationCompactPatch`,
`SingularContinuousHerglotzMaximalFreenessUniversalityLaw`, and two `RHTower` universality laws.

## What Bottleneck 1 still needs after this

1. the interface repair just described;
2. **M. Riesz's theorem**: `HasMinimalExponentialType (nevBinf s)`.  The corpus's Gronwall bound
   (`SecondKindGlobal.boundedKernel_global`) gives only `exp(C‖z‖²)` — order two — so it is useless
   here.  The classical route runs through `∑ 1/|xₖ| < ∞` over the zeros of `B` and a genus-zero
   Hadamard product (for each `A > 0`, split off the finitely many zeros with `|xₖ| ≤ R` and bound
   the tail by `exp(A‖z‖)`).  Hadamard factorization is not in mathlib.
3. `phase_isGδ : IsGδ {ν | MaximalTranslationDifferentialFree ν}`;
4. leaf/label covariance under an arbitrary normalization change, to upgrade
   `carrierProjector_eq_of_leaf_label_covariance` to an unconditional statement.

Items 2 and 3 are the only genuinely analytic ones left; the three easy fields are done.

## The `upperMap` sign error is now a Lean theorem, not an argument `[PROVED]`

`HTGeometry/NevanlinnaWeylDiscPole.lean` proves the sign outright, so the diagnosis above no longer
rests on a pen-and-paper argument.

- `im_cauchyTransform_pos` — the Cauchy transform of a probability measure on `ℝ` has strictly
  positive imaginary part at every point of the upper half-plane.
- `weylForm s z t = Im((−A t + C)·conj(B t − D))`, with `weylForm_expand` identifying it as the real
  quadratic `weylLead·normSq t + p·Re t + weylTilt·Im t + c`, and
  `weylForm_eq_im_mul_normSq` identifying it with `Im(Möbius image)·‖B t − D‖²`.
- `weylForm_pos_ofReal` — positive at every real parameter (each Möbius image is a leaf transform).
- `weylLead_pos` — `weylLead = Im(−A·conj B) > 0`, from the parameter at infinity.
- `weylTilt_ofReal` — `weylTilt = Re(A·conj D − C·conj B)` equals `1` on the real axis, by the
  determinant identity; `continuous_weylTilt`; `weylTilt_ne_zero` on the upper half-plane;
  `weylTilt_pos` by connectedness of the half-plane (`convex_halfSpace_im_gt`) and the intermediate
  value theorem.
- **`nevInf_quotient_im_neg`** — `0 < z.im ⟹ (D(z)/B(z)).im < 0`.
- **`analyticNevCarrierFamily_quotient_im_neg`** — the same for the constructed carrier family, i.e.
  `MaximalTranslationInputs.upperMap` is refuted for it.

All axiom-clean, wired into the umbrella.

So the repair described above is mandatory: the jet-pole half-plane in the transversality chain has
to be the **lower** one.  A survey of the genuine uses found:

* `NormalizedProjectiveCauchyDensityControl` uses positivity only to separate the poles from their
  own conjugates and from the real axis; both survive a uniform sign flip;
* everywhere else `0 < (x i).im` is consumed as `(hupper i).ne'`, i.e. only as `(x i).im ≠ 0`;
* the one quantitative use is `AnalyticNevanlinnaCarrierBridge`'s
  `compact_finite_strictPositive_uniformLowerBound`, which produces `η₀ ≤ (F.quotient (node)).im`
  with `0 < η₀` and feeds `projectiveNevanlinnaJetExpansionSmoothControl_coordinate_eq_singleton_last`;
  under the flip this becomes `(F.quotient (node)).im ≤ −η₀`, so `NevanlinnaJetTriangular` and
  `LocalNevanlinnaJetTriangular` have to move with it.

An alternative that avoids editing the abstract layer is a conjugation transport: for real `t`,
`((t − conj q)⁻¹)^{k+1} = conj (((t − q)⁻¹)^{k+1})`, so a full-rank witness at the conjugated poles
is the entrywise conjugate of the one at the original poles, and injectivity of a matrix's `mulVec`
is preserved by entrywise conjugation.  Instantiating the abstract lemmas at `conj ∘ F.quotient`
(which does lie in the upper half-plane) and conjugating the conclusion back would leave the
abstract modules untouched.  Deciding between the two is the next step on this bottleneck.

## M. Riesz is now a single named hypothesis `[REDUCTION PROVED]`

`HTGeometry/NevanlinnaEntryMinimalType.lean` (axiom-clean, wired) completes the size-bound layer the
corpus had begun (`norm_nevAinf_le`, `norm_nevDinf_le`) and turns it into a reduction.

- `norm_nevBinf_le`, `norm_nevCinf_le` — the two entries carrying an additive constant:
  `‖B(z)‖ ≤ 1 + h₀‖z‖·(S_z·P_0)` and `‖C(z)‖ ≤ 1 + h₀‖z‖·(S_0·P_z)`, from `norm_tsum_weighted_le`.
- `KernelMinimalExponentialType s` — the property that for every `A > 0` there is `C ≥ 1` with
  `kernelRoot s (monicOrthoC s · z) n ≤ C·exp(A‖z‖)` and the same for `secondKindC`, uniformly in
  the truncation `n`.
- `norm_mul_exp_half_le`, `entry_bound_absorb` — `r·exp(A r/2) ≤ (2/A)·exp(A r)`, so the extra
  linear factor in the entry bounds is absorbed by running the hypothesis at half the exponent.
- **`hasMinimalExponentialType_nevAinf` / `…nevBinf` / `…nevCinf` / `…nevDinf`** — all four entries
  have minimal exponential type as soon as `KernelMinimalExponentialType s` holds.

So the only analytic input still missing for the `minimalExponentialType` field of
`MaximalTranslationInputs` is `KernelMinimalExponentialType s`, i.e. M. Riesz's theorem in its
kernel form.

**Route audit for that theorem (checked, so it is not re-attempted).**  The Volterra/Gronwall
machinery the corpus already owns (`SecondKindGlobal`) cannot give it.  The comparison identity is a
Volterra equation whose kernel is Hilbert–Schmidt, and the sharp bound for iterates of a
Hilbert–Schmidt Volterra operator is `‖V^m‖ ≤ ‖V‖_HS^m/√(m!)`, whose generating function is
`exp(c‖z‖²)` — order two, not order one.  Splitting off a small Hilbert–Schmidt tail improves the
constant but not the order: the tail bound is only valid on `‖z‖ < 1/(2ε)`, and iterating past that
radius reintroduces `exp(ε²‖z‖²)`.  Minimal type is therefore not reachable from the recurrence
alone; it needs the entire-function side — the zeros of `B` are real and satisfy `∑ 1/|x_k| < ∞`, and
a genus-zero Hadamard product then gives minimal type because for each `A > 0` the finitely many
zeros with `|x_k| ≤ R` contribute a polynomial and the remaining tail contributes `exp(A‖z‖)`.
Mathlib has Jensen's formula and the `ValueDistribution` package but **no Weierstrass/Hadamard
factorization**, so that has to be built.

## Hausdorff's moment theorem is proved `[PROVED]` — card 13's classical gate is closed

Mathlib has no Hausdorff moment theorem.  It is now in the tree, axiom-clean and wired, in five
modules.

- `HTGeometry/HausdorffQuadratureWeights.lean` — `hausdorffCoeff`, `hausdorffWeight`, the
  **refinement identity** `T(N,k) = T(N+1,k) + T(N+1,k+1)`, `sum_hausdorffWeight` (every level has
  mass `b 0`), `hausdorffCoeff_shift`, `choose_mul_descFactorial_shift`, and
  `sum_hausdorffWeight_descFactorial` (the exact falling-factorial moment identity).  The refinement
  identity turns both into inductions and avoids the triangle reindexing mathlib lacks.
- `HTGeometry/HausdorffQuadratureMeasure.lean` — `integral_finsetWeightedDirac_general`,
  `hausdorffNode`, `hausdorffQuadrature` with its finiteness instance, `integral_hausdorffQuadrature`,
  `hausdorffQuadrature_mass`, `hausdorffMoment_hausdorffQuadrature`.
- `HTGeometry/HausdorffNodeComparison.lean` — `pow_sub_pow_le_nsmul_sub`,
  `cast_descFactorial_eq_prod`, `descFactorial_ratio_eq_prod`, and **`abs_node_pow_sub_ratio_le`**:
  `|(k/N)^m − (k)_m/(N)_m| ≤ m²/N`.
- `HTGeometry/HausdorffMomentTheorem.lean` — `sum_hausdorffWeight_ratio`,
  `abs_hausdorffMoment_hausdorffQuadrature_sub_le`, `tendsto_hausdorffMoment_hausdorffQuadrature`,
  `hausdorffTest`, `eq_of_clusterPt_of_tendsto`, and
  **`exists_hausdorffSource_of_completelyMonotone`**,
  **`hausdorffCompletelyMonotone_iff_exists_source`**,
  **`existsUnique_hausdorffSource_of_completelyMonotone`**,
  `hausdorffMoment_strict_completelyMonotone`.
- `HTGeometry/HausdorffStrictCddCone.lean` — `geometricCombination_strict_completelyMonotone`,
  `cddCoupling_strict_completelyMonotone`.

The limit step needs no metrizability: `ProbabilityMeasure ↥(Icc 0 1)` is a compact space, and a
cluster point of the normalised quadrature sequence has the right moments because integrating a
bounded continuous test function is continuous and a cluster point of a convergent sequence is its
limit.

Card 13 is not yet promotable: `(11) = (13)`, the extreme-ray classification, and the q-ladder
instance remain.  But its named classical blocker is gone, and Theorem A is unconditional in both
directions with uniqueness.
