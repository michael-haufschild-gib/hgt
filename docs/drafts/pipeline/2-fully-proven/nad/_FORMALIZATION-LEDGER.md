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

Once this holds, `ClassicalAnalyticNevanlinnaCarrierFamily` is a structure instance, and the ten
moment-fibre cards reduce to producing a term of `MaximalTranslationInputs`
(`NevanlinnaBoundaryFaceMaximalTranslation.lean`, six named analytic fields).
