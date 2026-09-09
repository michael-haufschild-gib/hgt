# Selberg cycle46 — exact phase mass and full-gradient identities

NEWEST CONTINUATION: read `mem:selberg/character-seam-phase-flux-2026-09-09` first. Cycle47 adds29 fully audited positive declarations: exact mismatch/loss decomposition, actual source derivative and paired character flux, exact polar energy with angular remainder, literal projected-mass derivative, and uniform16/3 bound for original paired outward normal current on modular core arc. Both final builds, axioms, index/wiring/API coverage, and repository lint passed; no owned worker remains. Full Selberg still active/unproved; next integrated characterwise core–cusp comparison.

Latest continuation of `mem:selberg/inversion-gram-fibres-2026-09-09`. Full unbudgeted Selberg1/4 objective remains ACTIVE / UNPROVED. Previous turn classified PROGRESS; this turn also proved new original-source mathematics. Do not mark complete or blocked.

## Authoritative completed sources

1. `formal/GaloisForLFunctions/RHTower/SelbergMaassInversionPhaseEnergy.lean`,350lines,24 public declarations plus local gammaNormal instance; matching namespace. Imports audited InversionGram.
- `tripleMotion`: actual weight chi(r*b-s*(a+c)) times actual regular three-block motion. Norm1 action proved.
- `transferGram_eq_average`, `transfer_inner_average`, `triple_displacement_energy`: actual full normalized triple squared displacement `(L^-3/2)*sum_abc ||v-W_abc v||² = ||v||²-||C_rs v||²`.
- `characterProjection_loss`, `lowerProjection_transfer_norm`, `transfer_loss_decomposition`: exact loss = ||v-P_s v||² + ||P_s v-Q_-r P_s v||².
- `blockMotion N p r b v = stdAddChar(-(r*b)) • U_(p b) v`; actual norm, projector-average, correlation, and `block_displacement_energy`: `(L^-1/2)*sum_b ||v-M_r,b v||²=||v-P_r v||²`.
- `coefficient_transfer_loss`, `coefficient_triple_energy_eq_block`: original a_n lies in P_(n mod L), so its full triple loss reduces exactly to the lower-block loss.
- `coefficientVector_mass_hasSum`, `coefficient_transfer_loss_hasSum`, `source_triple_displacement_hasSum`: original full vector and missing-channel physical masses, complete integer convergence.
- `coefficientVector_horizontal_hasSum`: actual summed original horizontal derivative Parseval.
- `coefficient_transfer_loss_le`, `weighted_phase_loss_summable`, `weighted_phase_loss_le_horizontal`: complete source frequency weight (2*pi*n/L)^2, convergent loss bounded by original horizontal derivative energy.
- `source_complement_mass_eq`, `source_block_displacement_hasSum` at line338: mass loss is the literal normalized integral of ||source-Q_r source||², exactly the complete block phase-displacement sum.

2. `formal/GaloisForLFunctions/RHTower/SelbergMaassCharacterGradient.lean`,398lines,23 public declarations plus local instance; matching namespace. Imports InversionPhaseEnergy.
- `sourceVector_contDiffOn`: actual source vector retains C² real-chart regularity.
- `readout_contDiffOn`, `readout_periodic`, `readout_horizontal_hasSum`: every actual continuous linear source readout retains regularity, periodicity and its exact frequency-weighted gradient Parseval law. No added analytic endpoint premise.
- `complementField N f r q`: literal coordinate difference of source and lower Q_r source; `complementReadout`, `complementReadout_apply` identifies actual continuous linear map.
- `complement_horizontal_hasSum`, `character_horizontal_hasSum`, `horizontal_energy_split` at152: exact missing and retained horizontal derivative energies and their sum=original energy.
- `source_phase_horizontal_hasSum`, `source_triple_horizontal_hasSum`: actual single-block/triple phase energies are precisely the missing-channel horizontal derivative energy after source frequency weighting.
- `coefficientHeightVector`: literal finite vector of deriv(original translated coefficient) at y. `coefficientVector_hasDerivAt` proves it differentiates the original vector.
- `coefficientHeight_upperProjection`: differentiation preserves exact upper residue eigenspace on every positive-height neighborhood.
- `coefficient_readout_vertical`, `readout_vertical_hasSum`: actual derivative coefficient is readout of the height vector, full vertical Parseval.
- `complement_vertical_hasSum`, `character_vertical_hasSum`, `coefficientVector_vertical_hasSum`, `vertical_energy_split` at345: complete original vertical energy splits exactly.
- `coefficientHeight_triple_energy_eq_block`: same actual triple-to-block reduction applies to the source height derivative vector.
- CAPSTONE `source_full_gradient_phase_hasSum` at380: for every original source, lower character r and positive height y, sum over every n of `(2*pi*n/L)^2 * phaseLoss(a_n) + phaseLoss(a_n')` equals normalized physical missing-channel horizontal derivative integral PLUS vertical derivative integral. Both are actual derivatives of complementField. This is a fixed-height full-gradient identity, not the still-missing full-domain coefficient-four bound.

## Proof-loop / corpus evidence

Revalidated both cycle45 hashes unchanged. Explicit OR twisted-displacement/phase-defect/norm-subtraction/Dirichlet-form query:180 declarations/52 modules, `/tmp/selberg_phase48_corpus.json`. Inspected finite Reynolds energy, WeightedGraphSpectralGap.dirichlet_self_eq polarization, CoherentHistoryMechanics.coherentHistory_energy_decomposition. Their abstract spectral-gap or fibre-response premises are not assumed for Maass.
Explicit OR twisted-derivative/magnetic-energy/covariant-derivative/Fourier-derivative query:89/37, `/tmp/selberg_phase48_gradient_corpus.json`. Read CoordinateCutoffCovariance.normSq_twistedBumpDeriv; its real-amplitude cancellation is not imposed on the complex Maass source. Exact source C²/periodicity and actual linear readout derivative laws supply the new proof instead.
Conjecture->proof progression: full triple displacement; source Fourier single-block reduction; physical complement-mass convergence; frequency-weighted gradient upper bound; stronger exact horizontal identity and splitting; forced vertical extension and exact full-gradient phase identity. No numerical experiments or negative wrappers.

## Completed audit

Both complete scratch files passed with no warnings: `/tmp/selberg_phase48_energy.lean`, `/tmp/selberg_phase48_gradient.lean`. Exact source checks passed. Only first module olean was emitted as needed import before final builds. Serialized final single-module builds rebuilt exactly their named target: InversionPhaseEnergy14s, CharacterGradient8.8s. Both replay existing EvenL2LogUnitary informational suggestion, no new module warning. All47 public declarations passed post-build /tmp axiom audit: only propext, Classical.choice, Quot.sound. Both source hashes unchanged. All47 searchable and verified under exact module API rows;49 indexed entries including2local instances. Both modules wired once into RHTower.
Index refresh passed. Initial lint exit1 on unrelated concurrent `ThetaCuspHawkingBMCausalRiemannKernel` missing umbrella import. Read-only revalidation later found its import added externally; justified final lint rerun passed with existing large-file warnings. Final scoped whitespace, every link in3 updated research cards, hashes and imports passed. No matching owned Lean/Lake processes; every owned handle terminal. No full/umbrella build, numerical experiment, commit or push.
PROCESS INCIDENT: source attempt81641 briefly overlapped live scratch59009; immediately interrupted source exit130, waited scratch exit0, verified both terminal, then resumed source check serially (85311 exit0). Interrupted attempt excluded from audit. User was informed in commentary and card records incident. Do not repeat: write_stdin may return live session after observation; NEVER start a second owned Lean process until previous reports terminal. No other agent process touched.
Artifacts `/tmp/selberg_phase48_manifest.json`, `_audit.json`, `_axioms.lean`, `_axioms.log`, `_energy_source.log`, `_gradient_source.log`, `_energy_build.log`, `_gradient_build.log`, `_coverage.json`, `_index.log`, `_lint.log`, `_lint_final.log` (prefix /tmp/selberg_phase48). Manifest has exact47names and both hashes. Final auditJSON includes process/whitespace/link results.

Card MOVED to `docs/drafts/pipeline/3-formalized/selberg-inversion-phase-energy.md`; old1-in-progress path absent. Parent `selberg-quarter-conjecturing-loop.md` has cycle46 and newest verification entry. `selberg-original-source-conserved-currents.md` frontier updated.

## Actual next target

The exact original phase mass and full-gradient slice measures now exist. Use them jointly with original inversion gluing across the modular core and cusp to derive the LEVEL-INDEPENDENT full-domain original mass <=4 physical gradient comparison. That estimate, then actual full-cell energy identity, is still needed for Selberg. Do not repeat already proved phase/polarization/Parseval identities; use corpus searches for a concrete quantitative gluing/uncertainty mechanism. Low frequencies, the actual curved core/cusp seam, and all character/composite fibres must remain. No scalar curvature shortcut or assumed spectral endpoint is permitted. Full goal unproved and active.

## Lean lessons THIS toolchain

`inner_smul_real_left` rewrite may not match concrete Complex cast; use `inner_smul_left` and `simp only [Complex.conj_ofReal,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,sum_inner,Complex.re_sum]`. Plain simp expands inverse real casts and leaves complex normSq denominators. `norm_sub_sq (𝕜:=ℂ)` then `characterProjection_inner_left` and `inner_self_eq_norm_sq` works; don't change .re before matching RCLike.re theorem. For actual quotientForm integrals, simplification exposes semireducible subtype mismatch; explicitly `change` both h and finite-integral identity into source `field` form before rw. Function.comp_def only where necessary. `hasDerivAt_pi.mpr` exists, `HasDerivAt.pi` does not. Use `(PiLp.continuousLinearEquiv 2 ℝ ...).symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt` for actual vector derivative. Before rewriting eventual derivative equality, `change HasDerivAt (fun t=>P(a_n t)) (P a_n') y at hp` (likewise readout) to eliminate composition/restrictScalars syntax mismatch. `contDiffOn_piLp 2`, `ContinuousLinearMap.restrictScalars`, `readout C²`, `HasSum.unique` all verified. `HasSum.sum_le` does not exist; Summable.of_nonneg_of_le and Summable.tsum_le_tsum verified.

Persistent rules: corpus script from repo root, spaces AND (--any OR). Lean cwd formal. Every Lean check uses lake env lean; final lake build one module only. All axioms in /tmp. Preserve dirty shared tree/other agents. User wants positive corpus-derived conjecture/proof/pivot loops. No goal completion around smaller results.
