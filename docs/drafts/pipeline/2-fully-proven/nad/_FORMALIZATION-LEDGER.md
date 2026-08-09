# `nad` folder — unconditional Lean formalization ledger

Working ledger for promoting every card in `2-fully-proven/nad` to `3-formalized/nad`.
A card is promoted only when its numbered statements are unconditional Lean theorems, the
modules are wired into an area umbrella, the axiom audit reports only `propext`,
`Classical.choice`, `Quot.sound`, and a `<id>-formalized.md` companion is issued.

| # | Card | Status | Notes |
|---|---|---|---|
| 1 | `hypertranscendental-phase-infinite-topological-charge-rank` | **PROMOTED** | 6 new modules: `RealExponentialPolynomial`, `RealConstantCoefficientAnnihilator`, `AnseloneKorevaarTranslationRank`, `EntireExponentialCompositionDA`, `ActiveChargeRankHypertranscendence`, `ChargeRankDressingExamples` |
| 2 | `affine-jet-packet-collision-completeness` | TODO | |
| 3 | `asymmetric-binary-tree-channel-rg-clock-hypertranscendence` | TODO | |
| 4 | `bethe-padic-holographic-rg-clock-hypertranscendence` | TODO | |
| 5 | `cofinal-cholesky-carrier-selection-threshold-law` | TODO | |
| 6 | `compact-local-form-factor-hypertranscendence-forcing` | TODO | |
| 7 | `constrained-prolate-continuous-polar-charge-law` | TODO | |
| 8 | `diamond-ising-da-scheme-rg-generation-hypertranscendence` | TODO | |
| 9 | `diamond-ising-family-rg-generation-hypertranscendence` | TODO | |
| 10 | `explicit-digamma-herglotz-universal-palette` | **PROMOTED** | new `HTGeometry/ExplicitDigammaPaletteIndependence.lean` closes joint Gamma-shift independence unconditionally (`DifferentialIndependent.of_finite` + `differentialIndependent_digammaShiftMero`); the cited Hardouin boundary is gone |
| 11 | `finite-jet-aperture-complete-germ-closure-law` | TODO | |
| 12 | `gauss-paired-quasi-inner-channel-schatten-depth-law` | TODO | |
| 13 | `hausdorff-positive-higher-spin-cdd-cone` | TODO | |
| 14 | `hypertranscendental-collision-phase-complexity-production` | TODO | |
| 15 | `identity-zero-componentwise-pauli-modular-nuclearity` | TODO | |
| 16 | `incommensurable-gamma-orbit-free-quasianalyticity` | TODO | |
| 17 | `indeterminate-moment-fiber-maximal-translation-ht` | TODO | |
| 18 | `kolchin-exchange-cocycle-obstruction` | IN PROGRESS | audit found the physical reflection anti-commutes with the derivation, so `DifferentialAlgEquiv` never applied to it; `AntiDifferentialAlgEquiv.lean` proves the orientation-reversing transport law unconditionally. `ReflectionAntiDifferential.lean` now packages `complexReflectionMeroEquiv c` as an `AntiDifferentialAlgEquiv ℂ (meroField Set.univ)`, and the whole obstruction chain (7)-(10) is ported to it. Algebraic layer complete. Open: the localization / admissible-gauge interface. |
| 19 | `moment-polynomial-blind-resolvent-complete-boundary-splitting` | TODO | |
| 20 | `neutral-gamma-ratio-full-differential-boundary-depth-law` | TODO | |
| 21 | `nevanlinna-boundary-bauer-retract-maximal-ht` | TODO | |
| 22 | `nonautonomous-kolchin-frequency-budget-law` | TODO | |
| 23 | `one-species-hypertranscendental-elastic-saturation` | IN PROGRESS | `HTGeometry/ElasticChannelSaturation.lean` proves the saturation lemma (2)-(4), unit modulus of every geometric factor on the real rapidity axis, and pole-freedom of the physical strip. Remaining: Lechner's inverse-scattering construction and the q-difference rational-or-HT dichotomy are external analytic parents. |
| 24 | `open-family-hypertranscendental-cdd-qft` | TODO | |
| 25 | `pick-defect-finite-selector-maximal-ht-phase-law` | TODO | |
| 26 | `postselected-qubit-clock-integrability-fracture` | TODO | |
| 27 | `prime-log-jump-sonin-mellin-grade-frame` | TODO | |
| 28 | `projective-constraint-topological-capacity-phase-law` | AUDITED | `HurwitzSurvivalWitnessInhabited.lean` proves both survival-witness classes inhabited by explicit integer families, so the phase theorems are non-vacuous **and** the witnesses carry no geometry. Open: construct the classical inputs. |
| 29 | `projective-hurwitz-one-over-forty-two-phase-transition` | AUDITED | arithmetic `1/42` gap, its uniqueness at `(2,3,7)`, and Riemann--Hurwitz eq. (8) are unconditional; the survival witness is content-free (see card 28). Open: `Δ(2,3,7)` as a group with torsion-free finite-index subgroups of unbounded index. |
| 30 | `q-ladder-reflectionless-reciprocal-jost-qft` | TODO | |
| 31 | `sectoral-kolchin-signature-quantum-fields` | TODO | |
| 32 | `signed-archimedean-gamma-orbit-charge-phase-law` | TODO | |
| 33 | `singular-autonomous-ade-kolchin-frequency-law` | TODO | |
| 34 | `singular-maximal-ht-schur-defect-collapse-law` | TODO | |
| 35 | `singular-maximal-ht-toeplitz-weld-graph-saturation` | TODO | |
| 36 | `spectral-type-stratified-moment-fiber-maximal-ht` | TODO | |
| 37 | `two-state-fermionic-zero-intrinsic-mixing-rigidity` | TODO | |
| 38 | `wedge-pfg-four-point-exchange-carrier` | TODO | |
| 39 | `xi-euler-ray-two-node-response-barrier` | **PROMOTED** | four modules audited: capstones resolve, axiom-clean, reachable from the `RHTower` umbrella. Only an external novelty audit remained. |
| 40 | `xi-physical-prime-log-aperture-fusion-cross-kernel` | **PROMOTED** | all thirteen named declarations audited: resolve, axiom-clean, five modules wired. Only an external novelty audit remained. |
| 41 | `xi-schur-inverse-limit-atomic-condensation-law` | TODO | |
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
