# Actual inversion phase energy and original Fourier reduction

- **Stage:** 3-formalized
- **Type:** POSITIVE SOURCE PHASE ENERGY LAW
- **Goal:** Identify the actual inversion loss as explicit phase-weighted displacements, reduce it using the original Fourier eigenspace constraint, and connect it to physical source energy.

## Conjecture and dependency-closed paper proof

The audited cycle45 kernel is the normalized average of actual unitary deck motions `W_abc = chi(r*b-s*(a+c))*U_(U(a)L(b)U(c))`. Its Gram form is `||C_rs v||²`. Expanding each `||v-W_abc v||²`, unitarity makes both squared terms `||v||²`; the complete normalized cross term is the actual Gram form. Thus the triple average divided by two equals `||v||²-||C_rs v||²`.

Stronger conjecture: the loss splits exactly into the missing upper character energy `||v-P_s v||²` and the missing lower character energy `||P_s v-Q_-r P_s v||²`. This follows from orthogonal projection and the proved inversion conjugacy. For each original Fourier coefficient `a_n(y)`, the already proved relation `P_(n mod L) a_n=a_n` removes the first term. The remaining loss is exactly the normalized average of `||a_n-chi(r*b)*U_L(b) a_n||²/2`. Summation should identify this with the original slice mass minus the physical lower-character slice mass; convergence must come from the original Parseval identities.

These identities introduce no phase or spectral endpoint hypothesis. The final full-domain mass comparison with four times physical gradient remains a target, not an input.

## Corpus evidence

Revalidated both cycle45 source hashes unchanged. Explicit OR search for twisted displacement, phase defect, norm subtraction, and Dirichlet form reached180 declarations in52 modules (`/tmp/selberg_phase48_corpus.json`). Read the actual finite regular Reynolds energy proof and character projection self-adjointness/completeness; inspect graph Dirichlet polarization and coherent-history fibre energy as cross-topic mechanisms. Their abstract spectral-gap or fibre-response premises are not Maass inputs and will not be assumed.

## Gates

- [x] Source revalidation, explicit OR corpus discovery, and paper conjectures.
- [x] Full actual triple phase-displacement identity.
- [x] Exact projection-loss decomposition and original Fourier single-block reduction.
- [x] Original physical mass/convergence identification and full gradient phase identity.
- [x] Scratch/source checks, targeted final audits, complete axiom/index/wiring/lint checks.

## Positive strengthening under proof

Full scratch now proves the original physical complement-mass integral, absolute convergence of the frequency-weighted phase loss, and its upper bound by the exact original horizontal gradient slice. The source frequency weight is `(2*pi*n/L)^2`, not a freely chosen rate. Stronger conjecture: equality with the literal horizontal derivative energy of the missing character field. Its paper proof applies the original derivative coefficient law to each actual continuous linear coordinate readout of `I-Q_r`, then sums Parseval over the finite deck coordinates. Source C² regularity and periodicity supply every analytic hypothesis.

Gradient-mechanism OR discovery returned89 declarations in37 modules (`/tmp/selberg_phase48_gradient_corpus.json`). Inspected `CoordinateCutoffCovariance.normSq_twistedBumpDeriv`: a phase twist separates amplitude and frequency derivative costs for its actual real bump. The present complex Maass source retains the full derivative term; no real-amplitude simplification or cancellation is assumed.

## Process audit note

One source-olean check was prematurely started while its scratch check was still live. The new source check was immediately interrupted (exit130), the scratch check then completed successfully, and process inspection confirmed both terminal before the serialized source check resumed. The interrupted attempt is excluded from verification. No other agent's process was touched.

The strengthened horizontal equality now passes scratch checking, together with the exact retained/missing horizontal-energy split. The next forced strengthening is the full physical gradient: differentiate the actual source coefficient vector in height, prove that its fixed residue eigenspace survives differentiation, and apply the same phase law to that derivative vector. Actual linear-readout C² regularity and the proved coefficient differentiation theorem justify vertical Parseval. Combining horizontal and vertical terms should identify the full phase energy without dropping either derivative.

## Full physical gradient identity: paper proof and scratch result

The actual coefficient height vector is the finite vector of derivatives of the original translated Maass coefficients. Coordinate differentiation and the finite Euclidean-space equivalence prove this is the derivative of the original vector. Differentiating the already proved upper-character identity on the positive-height neighborhood shows that the height vector retains precisely the same residue eigenspace.

For each actual linear readout, the source coefficient derivative is its readout of this height vector. Original C² regularity supplies the local derivative theorem and continuous derivative slices; Parseval then proves the complete vertical-energy sum. Apply this to each coordinate of `I-Q_r` and of `Q_r`. Orthogonal projection splitting at every coefficient, followed by uniqueness of the convergent sums, proves the exact retained/missing splits for both horizontal and vertical physical derivative energies.

Consequently the full missing-channel gradient is the sum over every original integer mode of `(2*pi*n/L)^2` times its exact block phase-displacement energy, plus the same phase-displacement energy of its actual height derivative vector. The full triple phases reduce to those block phases for both vectors. No derivative, low mode, character phase, or composite-level fibre is discarded. Both complete scratch files passed without warnings; final source/build and axiom audits remain below.

Sources: `SelbergMaassInversionPhaseEnergy.lean`24 public declarations; `SelbergMaassCharacterGradient.lean`23 public declarations. The second module's final capstone is `source_full_gradient_phase_hasSum`; the first gives the exact complementary physical mass in `source_block_displacement_hasSum`.

The next quantitative target is to combine these exact mass/gradient phase measures with original inversion gluing across the modular core and cusp, and prove the coefficient-four full-domain comparison. The identities supply the actual measures to estimate; they do not yet establish that comparison.

## Final source and proof audit — 2026-09-09

Complete scratch checks and exact source checks passed. The successful final builds were serialized and rebuilt exactly their named target: `SelbergMaassInversionPhaseEnergy`14s and `SelbergMaassCharacterGradient`8.8s. Both replayed the existing `EvenL2LogUnitary` informational message; neither new module has warnings. All47 public declarations passed post-build scratch axiom checks using only `propext`, `Classical.choice`, and `Quot.sound`. Source hashes stayed unchanged, both area-umbrella imports occur exactly once, and all47 declarations have exact-module API and search coverage. Index refresh passed. The interrupted source attempt described above is excluded.

Initial repository lint failed one unrelated concurrent umbrella-reachability error: `RHTower.ThetaCuspHawkingBMCausalRiemannKernel`. Later authoritative inspection found its new area-umbrella import, added outside this task, so the final lint audit reran against that changed state. No source code outside the two new modules and their two umbrella import lines was edited by this task.

Final repository lint passed after that external import appeared; the final log supersedes the initial failure. Existing large-file warnings remain. The exact phase/mass and phase/full-gradient identities are proved and audited. The level-independent full-domain coefficient-four comparison remains unproved, and the full Selberg goal remains active.

Artifacts: `/tmp/selberg_phase48_manifest.json`, `/tmp/selberg_phase48_audit.json`, `/tmp/selberg_phase48_axioms.log`, `/tmp/selberg_phase48_energy_build.log`, `/tmp/selberg_phase48_gradient_build.log`, `/tmp/selberg_phase48_coverage.json`, `/tmp/selberg_phase48_index.log`, `/tmp/selberg_phase48_lint.log`, and `/tmp/selberg_phase48_lint_final.log`.

Final scoped source/card/umbrella whitespace, every link in the updated research cards, source hashes, and exact umbrella imports passed. Process inspection found no matching task-owned Lean/Lake process; every owned tool handle is terminal. No full or umbrella build, numerical experiment, commit, or push ran.
