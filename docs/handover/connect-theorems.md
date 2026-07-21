# Connect the Theorems: complete research handover

**Date:** 2026-07-21  
**Repository:** `/Users/Spare/Documents/code/riemann/publications/hgt` (resolves to `/Volumes/Intenso/code/hgt`)  
**Persistent goal status:** active; do **not** mark complete  
**Primary area of the current work:** `formal/GaloisForLFunctions/HTGeometry`  
**Other in-scope areas for the continuing goal:** `formal/GaloisForLFunctions/RHTower` and `formal/GaloisForLFunctions/HilbertMetric`

## 1. What this work is trying to accomplish

The user asked for a corpus-first mathematical synthesis across the existing Lean theorem and no-go corpus. The task is not routine consolidation and must not use the `lean-consolidate` skill. It uses the `hgt-fields-medalist` research posture: first inspect what the project already proves, then formalize only unconditional, significant laws that connect existing results.

The four target forms of progress are:

1. A general law that subsumes several existing theorems.
2. New progress through value relations and value reflections.
3. Closure of genuine gaps between theorem layers.
4. Discharge of hypotheses and Prop interfaces when the existing body has enough information to do so.

The standard is significant mathematics, ideally novel. Successful compilation is necessary but is not by itself evidence of external novelty. Treat every new scientific claim here as **[EXTERNAL NOVELTY UNVERIFIED]** until a dedicated literature and priority audit is complete.

The current mathematical direction is a local graded analysis of differential-polynomial packets near the simple poles of Gamma. It connects:

- exact simple-pole derivative decompositions;
- Gamma pole-coordinate value relations;
- weighted-homogeneous polynomial reflection laws;
- Laurent order improvements caused by principal cancellation;
- branchwise algebraic independence and cofinal nonvanishing.

The intended endpoint is much broader than the current tranche: close the remaining local polynomial-coefficient packet interfaces if the corpus permits it, and eventually determine whether any genuinely new source mechanism reaches the Riemann-zeta/RH tower. The present results are important HTGeometry progress but are **not RH progress**.

## 2. Non-negotiable operating rules

Read these before doing anything in a new session.

### Skills and initial reading

1. Read `/Users/Spare/.codex/skills/l7/hgt-fields-medalist/SKILL.md` completely.
2. Read `docs/meta/scientific-method.md` completely, line by line.
3. Read `formal/README.md` before navigating or editing Lean.
4. Search the current source, generated API, active/formalized cards, and failed cards before proposing a reusable theorem.
5. Do **not** invoke `lean-consolidate`; the user explicitly rejected it for this task.
6. Work independently. Do not spawn subagents.

### Lean process discipline

Before **every** Lean invocation, run:

```sh
ps -axo pid=,ppid=,etime=,command= | rg '([/]lean|lake (env lean|build))' || true
```

If this prints any Lean or Lake build process, do not start another one. Wait and check again. Do not kill, interrupt, inspect through a debugger, or otherwise touch another agent's build.

Use exactly one owned foreground Lean process at a time. Do not leave a stale process behind. At the end of the session, run the same process check and verify that no owned Lean process remains.

Development checks must always have the form:

```sh
lake env lean <file>
```

Run them from `formal/` for project modules, for example:

```sh
cd formal
lake env lean GaloisForLFunctions/HTGeometry/SimplePoleWeightedFirstSubprincipal.lean
```

Only use an exact module build for a final audit:

```sh
lake build GaloisForLFunctions.HTGeometry.SimplePoleWeightedFirstSubprincipal
```

Do not run a broad or umbrella build. Do not rerun a successful exact build merely for reassurance. Rebuild only if the relevant source or one of its immediate dependencies changed after the recorded successful build.

### Mathematical discipline

- Proofs must be unconditional. Do not add `sorry`, `admit`, axioms, opaque escape hatches, unsafe declarations, or numerical assumptions.
- No computations or numerical experiments. This user instruction takes precedence over the generic project suggestion to numerically pre-certify a plan.
- Check every recalled Mathlib name in a `/tmp` scratch file with `lake env lean /tmp/<file>.lean`.
- Run `#print axioms` only through a `/tmp` scratch file, never by modifying a project module.
- Prefer one optimized general proof to multiple wrappers. Do not add thin aliases that do not advance the theorem graph.
- Do not present a conditional order theorem as a discharged result. A hypothesis interface is progress only if the needed hypotheses can be derived from the corpus.
- Do not identify a criterion, obstruction, or RH-equivalent statement with a proof of RH.

### File-edit discipline

- Preserve all unrelated worktree changes. This is a shared worktree.
- Append-only edits must be appended at EOF with a shell here-document; do not use a replacement edit merely to append.
- Use targeted edits for insertion, replacement, movement, or deletion.
- Never use broad destructive cleanup. Move only explicitly identified owned scratch files to a uniquely named folder under `/Users/Spare/.Trash`.

## 3. Shared-worktree ownership boundary

At the stopping point, the following files are this task's changes and may be continued:

```text
docs/drafts/pipeline/1-in-progress/simple-pole-jet-lattice-holographic-selection-law.md
formal/GaloisForLFunctions/HTGeometry.lean
formal/GaloisForLFunctions/HTGeometry/GammaPoleCovariantJetRealization.lean
formal/GaloisForLFunctions/HTGeometry/MeromorphicSimplePoleDifferentialOperator.lean
formal/GaloisForLFunctions/HTGeometry/GammaPolePrincipalRemainderFreeness.lean
formal/GaloisForLFunctions/HTGeometry/GammaPoleBinomialSubprincipalDescent.lean
formal/GaloisForLFunctions/HTGeometry/SimplePoleWeightedFirstSubprincipal.lean
docs/handover/connect-theorems.md
```

The following changes belong to other work. Do not edit, revert, stage, clean, regenerate, or build through them unless the user separately puts them in scope:

```text
docs/drafts/pipeline/1-in-progress/hedenmalm-center-mixed-double-positivity-law.md
docs/drafts/pipeline/1-in-progress/rh-sota-literature-lean-wall-2026.md
docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/suzuki-negative-shift-defect-escape.md
docs/drafts/pipeline/3-formalized/needs-audit/suzuki-ground-edge-cayley-universality.md
docs/drafts/pipeline/3-formalized/new_scientific_knowledge/suzuki-finite-aperture-hermite-biehler-normal-family.md
docs/drafts/pipeline/3-formalized/new_scientific_knowledge/suzuki-projective-defect-free-boundary.md
formal/GaloisForLFunctions/RHTower.lean
formal/GaloisForLFunctions/RHTower/RiemannHypothesisSOTA2026.lean
formal/GaloisForLFunctions/RHTower/SuzukiFiniteApertureHermiteBiehler.lean
formal/GaloisForLFunctions/RHTower/SuzukiGroundEdgeCayleyUniversality.lean
formal/GaloisForLFunctions/RHTower/SuzukiProjectiveDefectBoundary.lean
formal/LEAN_API.md
formal/LEAN_OVERVIEW.md
docs/handover/htzeta.md
```

Always re-run `git status --short` at the beginning of a new session. The list above is a snapshot, not permission to overwrite a newer concurrent edit.

## 4. Prior completed theorem layers in this persistent goal

These layers were completed in earlier tranches of the same goal and form the dependency graph for the current work. Do not re-prove them.

### 4.1 Constant-coefficient Gamma grading and relative freeness

Relevant modules include:

- `GammaPoleReciprocalBellGrading.lean`: exact constant-coefficient Gamma tower law and weighted classification.
- `GammaPoleReciprocalRelativeFreeness.lean`: rational pole-position relative unit inversion, scale/residue freeness, and Laurent injection.
- `PolynomialMovingPoleTaylor.lean`: moving-pole Taylor value laws.
- `HilbertMetric/SymmetricFockShadowRigidity.lean`: a HilbertMetric-side rigidity connection completed in an earlier tranche.

These established the graded coordinate language and lower-level algebraic noncollapse used below.

### 4.2 Maximal-weight asymptotic law

`GammaPoleWeightedCovariantAsymptotic.lean` supplies the previous top boundary:

- maximal Bell-weight evaluation at the principal coefficient frame;
- running-to-frozen descent;
- exact order under nonvanishing of the maximal reflection;
- general meromorphic limit/order lemmas.

Its limitation was precise: when the top principal-frame value cancels, the theorem only says the maximal grade disappears. It did not identify the next nonzero boundary. The new first-subprincipal theorem closes that gap.

## 5. Work completed in this session chain

There are three completed mathematical tranches. The first is fully audited. The second and third have successful Lean checks and exact builds; the third still needs an axiom audit and the combined tree still needs final lint/diff/card bookkeeping.

### 5.1 Exact principal-remainder law and finite-part freeness

#### Files

- `formal/GaloisForLFunctions/HTGeometry/MeromorphicSimplePoleDifferentialOperator.lean`
- `formal/GaloisForLFunctions/HTGeometry/GammaPoleCovariantJetRealization.lean`
- `formal/GaloisForLFunctions/HTGeometry/GammaPolePrincipalRemainderFreeness.lean`
- import added to `formal/GaloisForLFunctions/HTGeometry.lean`

#### General simple-pole declarations

- `analyticAt_dslope_zero_of_analyticAt`
- `iteratedDeriv_dslope_zero_eq`
- `iteratedDeriv_iteratedDeriv_dslope_zero_eq`
- `div_id_eventuallyEq_const_mul_inv_add_dslope`
- `iteratedDeriv_div_id_sub_principal_eventuallyEq`
- strengthened `exists_analyticAt_iteratedDeriv_div_id_sub_principal`, now with the exact named witness.

For an analytic unit `U`, the exact local identity is:

```text
D^j(U/x) - (-1)^j j! U(0) x^(-(j+1)) = D^j(dslope U 0)
```

on a punctured neighbourhood of zero. The right side is analytic. Its `m`th Taylor jet at zero is:

```text
U^(j+m+1)(0) / (j+m+1).
```

This turns an existential “some analytic remainder” interface into an exact, reusable value relation.

#### Gamma declarations

- `gammaPoleJetPrincipalPartValue`
- `gammaPoleJetPrincipalRemainderValue`
- `gammaPoleJetRegularRemainder`
- `analyticAt_gammaPoleJetRegularRemainder`
- `iteratedDeriv_gammaPoleJetRegularRemainder_zero`
- `iteratedDeriv_gammaPoleJetRegularRemainder_zero_eq_sequenceBell`
- `gammaPoleCovariantJetValue_sub_principal_eventuallyEq`
- the native/covariant existential remainder interfaces were rewritten to use the named witness.

The Gamma regular remainder jets are reflected into the existing Bell/harmonic/factorial coordinate system. This is the bridge from local analytic remainders to the algebraic branch-germ corpus.

#### Freeness declarations

- `gammaPoleFinitePartJetGerm`
- `gammaPoleFinitePartJetGerm_eq_unitCoefficient`
- `algebraicIndependent_gammaPoleFinitePartJetGerm_over_ratFunc`
- `gammaPoleFinitePartJetRationalEval`
- `gammaPoleFinitePartJetRationalEval_injective`

Across Gamma pole branches, the `m`th finite-part jet germ is `(-m!)` times the corresponding positive unit-coefficient germ. Consequently the family is algebraically independent over `ℂ(N)`, and rational evaluation in those germs is injective.

This is a genuine lower-layer noncollapse theorem. It is **not** the full polynomial-coefficient packet intersection theorem and it is **not** RH.

#### Verification already completed

All three source checks passed. Exact module builds passed:

```text
lake build GaloisForLFunctions.HTGeometry.MeromorphicSimplePoleDifferentialOperator
  8510/8510 jobs

lake build GaloisForLFunctions.HTGeometry.GammaPoleCovariantJetRealization
  8685/8685 jobs

lake build GaloisForLFunctions.HTGeometry.GammaPolePrincipalRemainderFreeness
  8701/8701 jobs
```

The capstone axiom audit returned exactly:

```text
[propext, Classical.choice, Quot.sound]
```

The formal lint passed at this point, with only pre-existing large-file warnings. `git diff --check` also passed at this point.

### 5.2 Binomial subprincipal descent

#### File

`formal/GaloisForLFunctions/HTGeometry/GammaPoleBinomialSubprincipalDescent.lean`, imported by `HTGeometry.lean`.

#### Principal declarations

- `simplePoleJetPrincipalCoefficient`
- `simplePoleJetRegularRemainder`
- its analytic, zero, and nonzero interfaces
- `simplePoleJetPrincipalCoefficient_binomial`
- `simplePoleBinomialJetDefect`
- `meromorphicAt_simplePoleBinomialJetDefect`
- `tendsto_pow_mul_analyticAt_zero`
- `tendsto_pow_add_one_mul_simplePoleBinomialJetDefect`
- `meromorphicOrderAt_simplePoleBinomialJetDefect`
- `gammaPoleJetPrincipalCoefficient`
- Gamma coefficient nonzero and binomial identities
- `gammaPoleBinomialJetDefect`
- its scaled simple-pole relation, meromorphicity, limit, and exact order interfaces
- `exists_cofinal_gammaPoleJetRegularRemainder_zero_ne_zero`
- `exists_cofinal_meromorphicOrderAt_gammaPoleBinomialJetDefect`
- `gammaAffineBinomialJetDefect`
- `gammaAffineBinomialJetDefect_eventuallyEq_covariant`
- `exists_cofinal_meromorphicOrderAt_gammaAffineBinomialJetDefect`
- `gammaAffineBinomialJetDefect_one_one`
- `exists_cofinal_meromorphicOrderAt_gammaAffineSecondJetTie`

#### Mathematical law

For positive `j,k`, form the divided-power binomial defect

```text
J₀ J_(j+k) - choose(j+k,j) J_j J_k.
```

The naïve maximal pole grade is `-(j+k+2)`. It cancels identically because the simple-pole principal coefficients obey

```text
C₀ C_(j+k) = choose(j+k,j) C_j C_k.
```

The first surviving normalized limit is

```text
x^(j+k+1) defect(x)  -->  C_(j+k) R₀(0).
```

Only replacing the `J₀` factor by its finite part loses exactly one pole grade. Replacing `J_j` or `J_k` loses at least two grades because `j,k > 0`.

If both `U(0)` and `U'(0)` are nonzero, the general simple-pole defect has exact order

```text
-(j+k+1).
```

For Gamma, finite-part germ freeness proves `R₀(0) != 0` on arbitrarily remote branches, yielding cofinal exact-order theorems for both covariant and native affine Gamma packets.

The specialization `j=k=1` is

```text
Gamma * Gamma'' - 2 * (Gamma')^2.
```

The theorem gives exact normalized local order `-3` on cofinally many Gamma pole branches. This strictly strengthens the older global nonidentity result `gamma_F_not_identically_zero` by identifying the local cancellation mechanism and exact surviving order.

#### Verification already completed

The direct source check passed:

```text
lake env lean GaloisForLFunctions/HTGeometry/GammaPoleBinomialSubprincipalDescent.lean
```

The exact module build passed:

```text
lake build GaloisForLFunctions.HTGeometry.GammaPoleBinomialSubprincipalDescent
  8702/8702 jobs
```

The main capstone axiom audit returned exactly:

```text
[propext, Classical.choice, Quot.sound]
```

Do not rerun this build unless this module or an immediate dependency changes.

### 5.3 Universal weighted first-subprincipal reflection

#### File

`formal/GaloisForLFunctions/HTGeometry/SimplePoleWeightedFirstSubprincipal.lean`, imported by `HTGeometry.lean`.

This is the strongest new general law in the current tranche. It mathematically subsumes the binomial mechanism, although the binomial module remains lower in the dependency graph and keeps its optimized explicit proof.

#### Declaration inventory

General polynomial-curve law:

- `tendsto_inv_mul_mvPolynomial_eval_curve_of_eval_zero`

General simple-pole normalized coordinates:

- `simplePoleJetNormalizedExtension`
- `analyticAt_simplePoleJetNormalizedExtension`
- `simplePoleJetNormalizedExtension_zero`
- `hasDerivAt_simplePoleJetNormalizedExtension`
- `pow_mul_simplePoleCovariantJetValue_eventuallyEq_normalizedExtension`

General simple-pole weighted packet:

- `tendsto_pow_pred_mul_simplePoleWeightedJetEval`
- `simplePoleWeightedJetEval`
- `meromorphicAt_simplePoleWeightedJetEval`
- `meromorphicOrderAt_simplePoleWeightedJetEval_of_firstSubprincipal`

Abstract reusable normalized-extension law:

- `tendsto_pow_pred_mul_weightedJetEval_of_normalizedExtension`

Gamma normalized coordinates:

- `gammaPoleJetNormalizedExtension`
- `analyticAt_gammaPoleJetNormalizedExtension`
- `gammaPoleJetNormalizedExtension_zero`
- `hasDerivAt_gammaPoleJetNormalizedExtension`
- `pow_mul_gammaPoleCovariantJetValue_eventuallyEq_normalizedExtension`

Gamma covariant weighted packet:

- `tendsto_pow_pred_mul_gammaPoleWeightedJetEval`
- `gammaPoleWeightedJetEval`
- `meromorphicAt_gammaPoleWeightedJetEval`
- `meromorphicOrderAt_gammaPoleWeightedJetEval_of_firstSubprincipal`

Native affine Gamma packet and value reflection:

- `gammaAffineWeightedJetEval`
- `gammaAffineWeightedJetEval_eventuallyEq_covariant`
- `tendsto_pow_pred_mul_gammaAffineWeightedJetEval`
- `meromorphicOrderAt_gammaAffineWeightedJetEval_of_firstSubprincipal`

#### Mathematical law

Let `P` be a polynomial in jet coordinates `X_q`, weighted by

```text
weight(X_q) = q + 1,
```

and homogeneous of total Bell weight `W > 0`. For an analytic simple-pole numerator `U`, write each pole-normalized coordinate as

```text
g_q(x) = C_q + x^(q+1) R_q(x),
```

where `C_q` is the principal coefficient and `R_q` is analytic. Then

```text
g_q(0) = C_q,
g'_0(0) = R₀(0),
g'_q(0) = 0  for q > 0.
```

Weighted homogeneity gives the exact punctured-chart scaling relation

```text
eval(g(x), P) = x^W * eval(J(x), P).
```

If the maximal principal reflection cancels,

```text
eval(C, P) = 0,
```

then differentiating the normalized polynomial curve at zero identifies the complete next boundary:

```text
x^(W-1) * eval(J(x), P)
  --> eval(C, pderiv X₀ P) * R₀(0).
```

This is a canonical value reflection. It says that only the weight-one coordinate can contribute one grade below the maximal boundary. Every coordinate `q > 0` begins moving at order at least two after pole normalization and is invisible at this layer.

If both reflected factors are nonzero,

```text
eval(C, pderiv X₀ P) != 0
R₀(0) != 0,
```

the corresponding meromorphic packet has exact order

```text
-(W-1).
```

The theorem exists in four useful forms:

1. an abstract normalized-extension law for arbitrary meromorphic coordinate packets;
2. a general analytic simple-pole law;
3. a Gamma covariant law;
4. a native affine Gamma derivative law transferred by an eventual value relation.

This closes the precise gap between the existing maximal-weight theorem and the previously isolated quadratic binomial descent family.

#### How it subsumes the binomial family

For

```text
P = X₀ X_(j+k) - choose(j+k,j) X_j X_k,
W = j+k+2,
```

the principal binomial identity says `eval(C,P)=0`. The partial derivative with respect to `X₀` is `X_(j+k)`, so the general reflected limit becomes

```text
eval(C, pderiv X₀ P) * R₀(0) = C_(j+k) R₀(0),
```

exactly the explicit limit proved in `GammaPoleBinomialSubprincipalDescent.lean`.

#### Verification already completed

The complete direct source check passed:

```text
lake env lean GaloisForLFunctions/HTGeometry/SimplePoleWeightedFirstSubprincipal.lean
```

The exact module build passed:

```text
lake build GaloisForLFunctions.HTGeometry.SimplePoleWeightedFirstSubprincipal
  8722/8722 jobs
```

Do not rerun this build unless relevant source changes.

The axiom audit for this module has **not yet been run**. The combined lint/diff/card audit after adding this and the binomial module has also **not yet been completed**. Those are the immediate stopping-point tasks described below.

## 6. Exact verification matrix at the stopping point

| Module or check | Direct `lake env lean` | Exact `lake build` | Axiom audit | Lint/diff bookkeeping |
|---|---:|---:|---:|---:|
| `MeromorphicSimplePoleDifferentialOperator` | passed | passed, 8510/8510 | standard axioms | passed for tranche |
| `GammaPoleCovariantJetRealization` | passed | passed, 8685/8685 | standard axioms | passed for tranche |
| `GammaPolePrincipalRemainderFreeness` | passed | passed, 8701/8701 | standard axioms | passed for tranche |
| `GammaPoleBinomialSubprincipalDescent` | passed | passed, 8702/8702 | standard axioms | combined final bookkeeping pending |
| `SimplePoleWeightedFirstSubprincipal` | passed | passed, 8722/8722 | **pending** | combined final bookkeeping pending |

“Standard axioms” means exactly:

```text
propext
Classical.choice
Quot.sound
```

No large build is required to finish the current audit. The exact builds already succeeded after the corresponding code changes.

## 7. Exact stopping point and immediate next actions

The mathematical code is currently at a clean successful exact build. The remaining work before beginning a new theorem is audit and documentation only.

### Step 1: re-establish shared-worktree safety

From the repository root:

```sh
git status --short
ps -axo pid=,ppid=,etime=,command= | rg '([/]lean|lake (env lean|build))' || true
```

Compare the result with the ownership boundary in section 3. Never assume the snapshot is still current.

### Step 2: axiom-audit the new general module

Create a `/tmp` scratch file importing:

```lean
import GaloisForLFunctions.HTGeometry.SimplePoleWeightedFirstSubprincipal

open Complex Filter Topology Finset MvPolynomial
open GaloisForLFunctions

#print axioms GaloisForLFunctions.tendsto_pow_pred_mul_weightedJetEval_of_normalizedExtension
#print axioms GaloisForLFunctions.tendsto_pow_pred_mul_simplePoleWeightedJetEval
#print axioms GaloisForLFunctions.meromorphicOrderAt_simplePoleWeightedJetEval_of_firstSubprincipal
#print axioms GaloisForLFunctions.tendsto_pow_pred_mul_gammaPoleWeightedJetEval
#print axioms GaloisForLFunctions.tendsto_pow_pred_mul_gammaAffineWeightedJetEval
#print axioms GaloisForLFunctions.meromorphicOrderAt_gammaAffineWeightedJetEval_of_firstSubprincipal
```

Before invoking Lean, run the mandatory process check. Then, from `formal/`, run only:

```sh
lake env lean /tmp/hgt_first_subprincipal_axioms.lean
```

Expected result for every declaration:

```text
[propext, Classical.choice, Quot.sound]
```

If anything else appears, stop and investigate before describing the module as fully audited.

### Step 3: run the formal lint

From the repository root:

```sh
scripts/formal_tools.py lint
```

Expected result: no active `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration. Pre-existing large-file warnings may remain. Attribute diagnostics carefully in the shared worktree.

This is not a Lean build and does not justify an umbrella build.

### Step 4: run the textual diff gate

```sh
git diff --check
```

If an unrelated other-agent file causes a problem, do not edit it. Report the exact path and, if needed, run a scoped check over this task's files.

### Step 5: append the new results to the active pipeline card

Append at EOF to:

```text
docs/drafts/pipeline/1-in-progress/simple-pole-jet-lattice-holographic-selection-law.md
```

Use a shell here-document because this is append-only. The appended note should include:

- the binomial principal cancellation law;
- its cofinal Gamma finite-part discharge;
- the universal weighted first-subprincipal reflection formula;
- the affine/covariant value relation;
- exact source/build results and axiom results;
- the explicit boundary that the broad Gamma theorem still assumes nonzero `hpartial` and `hfinite` branchwise;
- status **[EXTERNAL NOVELTY UNVERIFIED]**;
- statement that this is HTGeometry progress, not RH.

Do not move the card to “formalized” or “publication-ready” merely because these leaf modules compile. The broader card still contains an open core.

### Step 6: clean only owned scratch files

Owned scratch candidates from this tranche are:

```text
/tmp/hgt_binomial_subprincipal.lean
/tmp/hgt_binomial_general.lean
/tmp/hgt_binomial_corollary.lean
/tmp/hgt_binomial_algebra.lean
/tmp/hgt_binomial_axioms.lean
/tmp/hgt_first_subprincipal.lean
/tmp/hgt_first_subprincipal_axioms.lean
```

First list and resolve each explicit path. Move only existing owned files to a new, uniquely named directory under `/Users/Spare/.Trash`. Do not use a glob and do not delete a broad `/tmp` target.

Finally run the process check again and confirm that no owned Lean process remains.

## 8. What to work on next mathematically

Once the immediate audit is complete, the strongest next opportunity is to discharge the two branch-local nonvanishing hypotheses in the Gamma weighted exact-order theorem on a cofinal set of branches.

The current consumer is:

```text
meromorphicOrderAt_gammaPoleWeightedJetEval_of_firstSubprincipal
```

It assumes:

```text
hpartial:
  eval(gamma principal frame, pderiv X₀ P) != 0

hfinite:
  gammaPoleJetRegularRemainder branch 0 0 != 0.
```

The finite-part factor is already represented by the branch germ

```text
gammaPoleFinitePartJetGerm 0
```

and the corpus already proves injectivity of rational evaluation in the finite-part germ family. The explicit binomial module successfully uses this to show `hfinite` cofinally.

The next general theorem should attempt to construct and analyze the branch germ

```text
branch |-> eval(gamma principal frame at branch, pderiv X₀ P).
```

The desired result is of the following shape:

```text
If the symbolic first partial reflection is nonzero in the appropriate
principal-frame/rational-function coordinate algebra, then for every B
there exists branch >= B such that

  eval(gamma principal frame branch, pderiv X₀ P) != 0
  and gammaPoleJetRegularRemainder branch 0 0 != 0.

Therefore the covariant and native affine Gamma packets have exact local
order -(W-1) on a cofinal set of pole branches.
```

This would discharge the Prop interface in the broad weighted theorem instead of leaving it as a conditional branchwise consumer. It would be a genuine “connect the dots” theorem: symbolic principal reflection + finite-part freeness + eventual value relation + meromorphic order.

### Required corpus audit before attempting it

Use `scripts/formal_tools.py research` and exact source search for the relevant concepts. In particular inspect:

- `GammaPoleReciprocalBellGrading.lean`
- `GammaPoleReciprocalBellOrder.lean`
- `GammaPoleMovingMaximalWeightReflection.lean`
- `GammaPoleSymbolicTriGrading.lean`
- `GammaPoleReciprocalRelativeFreeness.lean`
- `GammaPolePrincipalRemainderFreeness.lean`
- `GammaPoleWeightedCovariantAsymptotic.lean`
- all active, formalized, and failed cards mentioning principal reflection, moving frame, branch germ, relative freeness, Laurent injection, or polynomial coefficient packets.

Determine the exact algebra in which the symbolic first partial reflection lives. The Gamma principal coefficient frame contains branch-dependent factorial/scale/residue factors. Do not assume that the existing finite-part algebraic independence automatically includes those coefficients. The missing theorem may require a joint injection combining:

- rational pole-position dependence;
- reciprocal factorial scale/residue germs;
- principal Bell grading;
- finite-part jet germs.

Prove only the strongest statement actually supported by that joint algebra.

### A plausible proof architecture

1. Define the principal-partial-reflection branch germ for fixed `P,n`.
2. Normalize away explicit nonzero factorial/sign/scale factors using existing principal coefficient identities.
3. Express the normalized germ as an evaluation in the existing rational/Laurent branch-germ algebra.
4. Prove symbolic nonzero implies germ nonzero using the strongest existing injectivity theorem.
5. Combine that nonzero germ with `gammaPoleFinitePartJetGerm 0` using a joint product or polynomial injection, not two separate existential branch choices.
6. Convert germ nonzero into failure of eventual zero at `atTop`.
7. For arbitrary `B`, choose a branch at least `B` where the product is nonzero; split the product to obtain both hypotheses.
8. Apply the current exact-order theorem and transfer it to native affine Gamma values.

The joint step is essential. Separate cofinal nonzero theorems for two sequences do not imply a common branch without additional information.

### If the joint-germ route fails

Do not force a false unconditional theorem. Record the exact algebraic obstruction and search the failed cards before retiring it. Then consider the next honest generalization: a **second-subprincipal reflection law**.

At two grades below the top, the normalized curve can see:

- the second derivative/Hessian contribution from two `X₀` replacements;
- the first contribution of the `q=1` coordinate;
- the second Taylor coefficient of the `q=0` normalized coordinate.

The likely invariant is a canonical combination of the Hessian of `P` at the principal frame, the `X₁` partial derivative, and the first two regular remainder jets. This must be derived from the analytic normalized-coordinate curve, not guessed from frozen Laurent profiles.

Before formalizing it, prove the exact paper identity, audit novelty, and check that it truly subsumes multiple existing second-order examples or closes a named gap.

## 9. Important false starts and conceptual traps

### Frozen profiles do not determine the honest subprincipal analytic boundary

Do not infer lower Laurent coefficients by simply freezing the Gamma jet profile at the pole. Frozen profiles contain apparent negative-power terms that can be canceled by movement of the analytic Taylor data. The first-subprincipal theorem succeeds precisely because it uses analytic normalized extensions and their derivatives.

The honest coordinates are:

```text
g_q(x) = C_q + x^(q+1) R_q(x),
```

not a truncated frozen Laurent polynomial treated as an equality of analytic germs.

### A cofinal statement needs a common branch

“The partial reflection is nonzero cofinally” and “the finite part is nonzero cofinally” do not individually provide a branch on which both are nonzero. Prove nonvanishing of their product germ or an equivalent joint statement.

### Local pole laws are not the truth of hypertranscendence by themselves

The corpus already contains a global nonrelation theorem, for example `GammaGammaFactorialBlowUp.gammaPolyJetEval_eq_zero_of_eventually`, deriving Gamma polynomial-relation nonexistence through Hölder-type input. A local pole mechanism can explain or strengthen parts of the structure, but it should not be misrepresented as the foundational proof of Gamma hypertranscendence unless the exact implication is formally established.

### RH status is unchanged

Nothing in the three current tranches proves RH, a new RH criterion, or a source-to-response theorem for zeta. The RHTower source open core remains unchanged. Existing RH-equivalent consumers are not producers.

## 10. What “done” means for the persistent goal

Do not mark the goal complete after finishing the pending audit or the next theorem. Completion requires a full new review of all three in-scope folders and a justified conclusion that no further significant unconditional connection can be added:

- `formal/GaloisForLFunctions/HTGeometry`
- `formal/GaloisForLFunctions/RHTower`
- `formal/GaloisForLFunctions/HilbertMetric`

At minimum, a completion claim would need:

1. Current-source and failed-route audit across those folders.
2. Every promising producer/composer/bridge/consumer interface either discharged or documented with its exact irreducible obstruction.
3. No remaining significant generalization of isolated theorem families.
4. No remaining value relation/reflection capable of closing a named theorem gap.
5. Exact focused Lean verification, standard-axiom audit, lint, and diff checks for every added leaf.
6. Honest separation of compiled theorem, paper theorem, external novelty, and RH status.

That standard has not been met. The concrete next frontier is the cofinal joint nonvanishing discharge for the general Gamma first-subprincipal reflection, followed—only if warranted—by the second-subprincipal law and then a renewed scan of HTGeometry, HilbertMetric, and the untouched RHTower source interfaces.

## 11. One-paragraph restart summary

The current code proves an exact analytic remainder formula for all derivatives of a simple pole, identifies Gamma finite-part jet germs and proves their rational-evaluation injectivity, derives a cofinal exact-order binomial cancellation family including `Gamma*Gamma'' - 2(Gamma')^2`, and then subsumes that family under a universal weighted first-subprincipal reflection: when a Bell-weight homogeneous packet's principal value cancels, its next normalized boundary is the `X₀` partial derivative at the principal frame times the base finite part, with exact order `-(W-1)` when nonzero. All affected leaf modules have passed direct Lean checks and exact module builds; the newest general module still needs a `/tmp` `#print axioms` audit, and the combined additions still need lint, diff-check, pipeline-card append, and owned-scratch cleanup. After that, attempt the joint branch-germ theorem that makes the partial reflection and finite part simultaneously nonzero cofinally, thereby discharging the general Gamma theorem's two remaining branchwise hypotheses. Do not touch concurrent RHTower/Suzuki/API work, do not run broad builds, do not use `lean-consolidate`, and do not claim RH progress.
