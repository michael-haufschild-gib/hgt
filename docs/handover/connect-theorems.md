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

## 12. Continuation completed after this handover

The pending first-subprincipal axiom audit passed with exactly `propext`, `Classical.choice`, and
`Quot.sound`; formal lint and `git diff --check` passed.  The active card was updated with the
binomial and universal first-subprincipal results.

The proposed common-branch theorem is now formalized in
`formal/GaloisForLFunctions/HTGeometry/GammaPoleWeightedFirstSubprincipalCofinal.lean` and imported
by `HTGeometry.lean`.  It reuses the existing injective Laurent evaluation for the factorial scale
and positive Gamma-unit derivatives.  The exact symbolic source is the principal reflection of
`pderiv X₀ P` multiplied by the finite-part generator.  Its nonzero image yields, beyond every
branch bound, one branch where principal cancellation, partial-reflection nonvanishing, and
finite-part nonvanishing all hold simultaneously.  The capstone
`exists_cofinal_meromorphicOrderAt_gammaWeightedJetEval_of_firstSubprincipal` then gives exact order
`-(W-1)` for both covariant and native affine packets on that same branch.

Verification completed:

```text
lake env lean GaloisForLFunctions/HTGeometry/GammaPoleWeightedFirstSubprincipalCofinal.lean
lake build GaloisForLFunctions.HTGeometry.GammaPoleWeightedFirstSubprincipalCofinal
  8723/8723
```

The five new audited declarations use exactly the standard axioms.  This is a **[BRIDGE]
[LEAN-PROVED]** result, not an external novelty or RH claim.  The next honest local layer is the
second-subprincipal reflection for packets whose symbolic principal reflection and first partial
both vanish.  Derive its complete normalized-curve second-derivative identity on paper before
adding Lean infrastructure.  The persistent goal remains active.

## 13. Exact second-subprincipal reflection completed

The next analytic layer is now paper-proved and Lean-proved in
`formal/GaloisForLFunctions/HTGeometry/SimplePoleWeightedSecondSubprincipal.lean`, imported by
`HTGeometry.lean`.  For an analytic polynomial curve `F(x)=P(g(x))` with `F(0)=F'(0)=0`, the new
generic theorem proves

```text
F(x)/x^2 -> (1/2) * F''(0),

F''(0) =
  sum_i (partial_i P)(C) g_i''(0)
    + sum_i sum_j (partial_j partial_i P)(C) g_j'(0) g_i'(0).
```

For honest normalized simple-pole coordinates

```text
g_q(x) = C_q + x^(q+1) R_q(x),
```

the exact second boundary is

```text
(partial_0 P)(C) R_0'(0)
  + (partial_1 P)(C) R_1(0)
  + (1/2) (partial_0 partial_0 P)(C) R_0(0)^2.
```

Do not remove the first term under only the product cancellation
`(partial_0 P)(C) R_0(0)=0`: `R_0(0)` may vanish while `R_0'(0)` does not.  A two-term form needs
the stronger symbolic condition `(partial_0 P)(C)=0`.

For Bell weight `W >= 2`, nonzero second boundary gives exact order `-(W-2)`.  This is formalized
for general simple-pole packets, Gamma covariant packets, and native affine Gamma packets.  Key
declarations are:

- `HTGeometry.iteratedDeriv_two_mvPolynomial_eval_curve_complex`;
- `HTGeometry.tendsto_inv_sq_mul_mvPolynomial_eval_curve`;
- `tendsto_pow_sub_two_mul_weightedJetEval_of_normalizedExtension`;
- `simplePoleSecondSubprincipalBoundary`;
- `meromorphicOrderAt_simplePoleWeightedJetEval_of_secondSubprincipal`;
- `gammaPoleSecondSubprincipalBoundary`;
- `meromorphicOrderAt_gammaAffineWeightedJetEval_of_secondSubprincipal`.

Verification completed:

```text
lake env lean GaloisForLFunctions/HTGeometry/SimplePoleWeightedSecondSubprincipal.lean
lake build GaloisForLFunctions.HTGeometry.SimplePoleWeightedSecondSubprincipal
  8723/8723
```

Seven audited capstones use exactly `propext`, `Classical.choice`, and `Quot.sound`.  Formal lint
and `git diff --check` passed after the documentation and import updates.

Scientific classification: **[BRIDGE] [LEAN-PROVED]**.  Multivariate Taylor/Faa di Bruno is
classical parent theory; no external novelty or RH claim is made.  The strongest immediate next
frontier is a cofinal Gamma discharge at this second layer: represent the complete second-boundary
combination in the existing joint scale/unit-derivative Laurent algebra, then prove symbolic
nonzero implies one common remote branch with principal cancellation, first-boundary cancellation,
and nonzero complete second boundary.  Do not replace that joint statement by separate cofinal
existentials.  After this local frontier, resume the required fresh producer/consumer scan across
HTGeometry, RHTower, and HilbertMetric.  Persistent goal remains active.

## 14. Cofinal Gamma second-subprincipal discharge completed

The common-branch second layer is now Lean-proved in
`formal/GaloisForLFunctions/HTGeometry/GammaPoleWeightedSecondSubprincipalCofinal.lean` and imported
by `HTGeometry.lean`.  It defines exact Laurent symbols

```text
R_0'(0)  <->  -(1/2) C(X_1),
R_1(0)   <->   T^(-1) (1/2) C(X_1),
R_0(0)   <->  -C(X_0)                 (existing),
```

then combines them with the principal reflections of `pderiv X_0 P`, `pderiv X_1 P`, and
`pderiv X_0 (pderiv X_0 P)` into one complete second-boundary source.  Its evaluation is exactly
the actual branchwise three-term boundary germ.  Existing joint Laurent injectivity proves that a
nonzero source has nonzero boundary germ.

If the symbolic principal reflections of `P` and `pderiv X_0 P` vanish and the complete symbolic
second boundary is nonzero, then for every bound there is one later Gamma branch where both
cancellations and boundary nonvanishing hold simultaneously.  The capstone
`exists_cofinal_meromorphicOrderAt_gammaWeightedJetEval_of_secondSubprincipal` gives exact order
`-(W-2)` there for both covariant and native affine packets when `W >= 2`.

Verification completed:

```text
lake env lean GaloisForLFunctions/HTGeometry/GammaPoleWeightedSecondSubprincipalCofinal.lean
lake build GaloisForLFunctions.HTGeometry.GammaPoleWeightedSecondSubprincipalCofinal
  8725/8725
```

Six audited declarations depend on exactly `propext`, `Classical.choice`, and `Quot.sound`.
Scientific classification: **[BRIDGE] [LEAN-PROVED]**.  No new freeness axiom, computation,
external novelty claim, or RH claim is involved.  Resume the required fresh producer/consumer scan
across HTGeometry, RHTower, and HilbertMetric.  For this Gamma hierarchy, a higher-order layer is
honest only after deriving the full normalized-curve boundary and identifying a reusable named
gap; do not extrapolate by dropping moving-remainder terms.  Persistent goal remains active.

## 15. Opaque second-boundary hypothesis eliminated

The same cofinal module now contains an exact nonvanishing classification.  Principal reflections
live in the pure factorial-scale Laurent subring.  Specializing all positive unit-derivative
variables therefore cannot kill a nonzero principal reflection: re-inclusion is a proved left
inverse on that subring.

Selecting only `X₁` isolates the `pderiv X₁ P` first-jet channel after `pderiv X₀ P` cancels;
selecting only `X₀` isolates the repeated-base Hessian channel.  These projections prove

```text
gammaPoleSecondSubprincipalBoundarySymbol n P != 0
  <-> principalReflection(pderiv X_1 P) != 0
       or principalReflection(pderiv X_0 (pderiv X_0 P)) != 0
```

under the existing first-partial cancellation.  The forward implication is exact because if both
channels vanish, the original three-term source is zero.  The reverse implication uses the
nonzero scalar `1/2` and Laurent unit `T^(-1)`.

Use
`exists_cofinal_meromorphicOrderAt_gammaWeightedJetEval_of_secondSubprincipal_channels` as the
strongest current capstone: it replaces the opaque complete-boundary hypothesis by the explicit
channel disjunction and returns exact order `-(W-2)` for covariant and native affine Gamma packets
on one arbitrarily remote common branch.  Classification remains **[BRIDGE] [LEAN-PROVED]** and
does not change RH status.  Persistent goal remains active; next work is the cross-folder scan, not
automatic extrapolation to third order.

The exact module rebuild passed `8725/8725`.  Seven classification and channel-capstone
declarations were axiom-audited; each depends on exactly `propext`, `Classical.choice`, and
`Quot.sound`.

## 16. HilbertMetric-to-RHTower strict mixture connector completed

Fresh cross-folder audit found a genuine producer/consumer duplication.  The terminal
`HilbertMetric/FourthCurvatureMixture.lean` advertised use by the theta tower, but
`RHTower/HedenmalmCenterMixedFourthJetCuspClosure.lean` independently carried the full quadratic-
form integration proof.

The general leaf now proves `integral_twoByTwo_det_pos`: if integrable real fields `p0,p2,p4`
satisfy `0 < integral p0` and their `2 x 2` Hankel determinant is strictly positive almost
everywhere with `p0>0`, then

```text
0 < integral(p0) * integral(p4) - integral(p2)^2.
```

The proof evaluates each pointwise positive matrix on the nonzero vector
`(-integral(p2), integral(p0))`; its integrated quadratic form is exactly the first mass times the
mixed determinant.  No uniform determinant gap is required.

The theta closure now invokes this generic Hilbert theorem directly and discharges its assumptions
using existing integrability, positive center mass, and full-source reflection-Hankel positivity.
The source determinant is multiplied by the positive square `(r*sinh(a*r))^2`.  More than a hundred
lines of duplicated source-specific quadratic/integral algebra were removed while preserving the
same unconditional fourth-Hankel and coalesced-cusp capstones.

Verification:

```text
lake env lean GaloisForLFunctions/HilbertMetric/FourthCurvatureMixture.lean
lake build GaloisForLFunctions.HilbertMetric.FourthCurvatureMixture
  8476/8476
lake env lean GaloisForLFunctions/RHTower/HedenmalmCenterMixedFourthJetCuspClosure.lean
lake build GaloisForLFunctions.RHTower.HedenmalmCenterMixedFourthJetCuspClosure
  8822/8822
```

All four audited generic/source capstones use exactly `propext`, `Classical.choice`, and
`Quot.sound`.  Classification: **[REDISCOVERED] [BRIDGE] [LEAN-PROVED]**.  This is classical strict
positive-cone integration, not external novelty and not RH progress.  Continue scanning RHTower
for other source-specific reproofs or conditional consumers whose hypotheses are already available.
Persistent goal remains active.

## 17. HTGeometry-to-RHTower affine-Gamma curvature connector completed

RHTower audit first rejected a tempting but invalid Thue--Morse/Perron splice.  The proved
square-integrable completed carrier is `Gamma * LSeries`, while the aggregate strip-mass consumer
requires the carrier itself to equal `LSeries` on the right half-plane.  Cancelling Gamma would
discard the available flank control.  The existing balanced third-charge theorem is therefore the
correct positive survivor; no false strip interface was added.

The same scan found a genuine duplication in
`RHTower/PrimeArchThetaGaussianApertureCurvatureFlow.lean`.  That source module independently
derived its normalized-ratio Riccati law and expanded its parabolic-reaction identity, although
`HTGeometry/AffineGammaMomentCurvature.lean` already proves the universal shifted-moment theorem
and the exact affine-weight curvature law.  The pipeline card explicitly states that the completed
theta flow is its `alpha=1/2`, `h=1` specialization, but the Lean dependency graph did not realize
that statement.

The RHTower module now imports the generic leaf.  Its source ratio derivative is proved by
`HTGeometry.hasDerivAt_normalizedMomentRatio`, after discharging the literal moment-shift and
nonvanishing facts.  The new stronger theorem

```text
hasDerivAt_thetaCuspGaussianApertureRatioCurvature_affineGamma
```

specializes `hasDerivAt_normalizedMomentRatioCurvature_of_affineWeights` at weights
`a_j=j+1/2`.  It returns the full `HasDerivAt` identity: square production, transport from the next
curvature coordinate, and reaction by the current curvature.  The old derivative equality is now
its immediate `.deriv` corollary, and all existing forward-barrier, entrance-cascade, GABTC, and
finite-section consumers keep their unconditional signatures.

Verification:

```text
lake env lean GaloisForLFunctions/RHTower/PrimeArchThetaGaussianApertureCurvatureFlow.lean
lake build GaloisForLFunctions.RHTower.PrimeArchThetaGaussianApertureCurvatureFlow
  8809/8809
lake env lean GaloisForLFunctions/RHTower/PrimeArchThetaGaussianApertureFiniteSectionMaximum.lean
```

Six generic, source, derivative, and downstream capstones were axiom-audited; each uses exactly
`propext`, `Classical.choice`, and `Quot.sound`.  Formal lint passed.  Classification of this new
edge: **[BRIDGE] [LEAN-PROVED]**.  It realizes the already audited affine-Gamma theorem in the
literal theta source; it is not an additional novelty claim and does not establish the missing
large-degree curvature boundary or RH.  Persistent goal remains active.

## 18. HilbertMetric-to-RHTower fourth-reflection jet connector completed

Umbrella-excluded endpoint audit found `HilbertMetric/ReflectionFourthJet.lean` was imported only
by the HilbertMetric umbrella, while
`RHTower/ThetaCuspFullReflectionFourthTuran.lean` independently expanded the same fourth Bell-jet
determinant with a source-local `ring` proof.

The Hilbert leaf now exposes two exact identities.  In Bell-logarithmic coordinates

```text
f₁ = f₀ ℓ₁,
f₂ = f₀ (ℓ₁² + ℓ₂),
f₃ = f₀ (ℓ₁³ + 3ℓ₁ℓ₂ + ℓ₃),
f₄ = f₀ (ℓ₁⁴ + 6ℓ₁²ℓ₂ + 3ℓ₂² + 4ℓ₁ℓ₃ + ℓ₄),
```

`reflectionFourthCurvatureJet_of_logJets` cancels the first and third channels exactly and returns
`ℓ₄ + 4ℓ₂²`.  `reflectedProduct_fourthHankel_of_logJets` composes that result with the
generic reflected-product determinant law:

```text
f₀² R₄ - R₂² = 2 f₀⁴ (ℓ₄ + 4ℓ₂²).
```

The theta module now imports this generic leaf and publishes the source specialization
`thetaCuspSourceReflectionFourthHankel_eq_logFactors`.  Its existing strict positivity theorem
uses this exact equality plus the already proved theta logarithmic fourth-Turán margin; the large
source-specific polynomial expansion is gone.

Verification:

```text
lake env lean GaloisForLFunctions/HilbertMetric/ReflectionFourthJet.lean
lake build GaloisForLFunctions.HilbertMetric.ReflectionFourthJet
  8475/8475
lake env lean GaloisForLFunctions/RHTower/ThetaCuspFullReflectionFourthTuran.lean
lake build GaloisForLFunctions.RHTower.ThetaCuspFullReflectionFourthTuran
  8814/8814
```

The two generic identities, exact theta specialization, and strict source capstone each use
exactly `propext`, `Classical.choice`, and `Quot.sound`.  Classification:
**[REDISCOVERED] [BRIDGE] [LEAN-PROVED]**.  This strengthens theorem graph and removes duplicate
algebra; it is not a new external novelty or RH claim.  Persistent goal remains active for the
remaining umbrella-excluded endpoint scan.

## 19. Canonical prime-aperture-to-Kolchin budget connector completed

The endpoint audit compared `HTGeometry/KolchinFrequencyBudgetPhase.lean` with the independent
finite prime-torus source `HTGeometry/GammaProjectivePrimeTorusCarrier.lean`.  The former required
callers to supply

```text
finrank_Q(V) = π(N)
```

to obtain its nonautonomous arithmetic-complement and Gamma-coefficient capacity bounds.  The
latter already proves this equality unconditionally for the canonical source
`primeApertureCharacterModule N = span_Q {log p : p <= N}`.

`KolchinFrequencyBudgetPhase.lean` now imports that source and exposes two specializations.  At
`V = top` inside the canonical aperture module,
`primeAperture_nonautonomous_primeComplement_budget` invokes the existing general complement
theorem after discharging its rank premise with `primeApertureCharacterModule_finrank`.
`primeAperture_nonautonomous_gammaCoefficient_capacity_floor` then derives the exact residual
half-rank floor

```text
(π(N) - rInfinity + 1) / 2 <= kappa
```

from only the relative-state and coefficient-rank bounds.  No caller must duplicate the
unique-factorization rank certificate, and no analytic Bohr/Pontryagin or Ritt--Kolchin input is
claimed.

Classification: **[REDISCOVERED] [BRIDGE] [LEAN-PROVED]**.  This is a theorem-graph connection
between two already formalized finite-rank results, not a new external novelty or RH claim.

Verification:

```text
lake env lean GaloisForLFunctions/HTGeometry/KolchinFrequencyBudgetPhase.lean
lake build GaloisForLFunctions.HTGeometry.KolchinFrequencyBudgetPhase
  8484/8484
```

Both new source-facing theorems use exactly `propext`, `Classical.choice`, and `Quot.sound`.
Formal lint and targeted diff checks passed.  Persistent goal remains active for remaining
high-signal endpoint exclusions.

## 20. Quantum-Fisher clock-line-to-Sonin connector completed

Cross-folder audit found `HTGeometry/QuantumFisherClockReparametrization.lean` terminal despite its
formalized card stating that the coordinate-free finite-clock line law applies directly to
existing moment and Sonin clock identities.  `RHTower/SoninLogClockQuantumFisher.lean` exposed only
raw QFI/variance, commutator, and dephasing equalities.

The Sonin module now imports the reparameterization leaf and proves

```text
soninLogClock_erasedQuantumFisherClockLineValue_eq_observabilityLineValue
```

for every normalized physical Sonin state, self-adjoint observable, and real clock increment.
Physicality supplies the fixed-vector premise for the involutive logarithmic Fourier-scattering
clock; the proof then invokes the generic
`finiteClock_erasedQuantumFisherClockLineValue_eq_observabilityLineValue` theorem at period two.
The result identifies the hidden-tangent Fisher line with four times the static Kadison variance
times the squared coordinate increment, making the existing source relation explicitly invariant
under the already formalized reciprocal clock reparameterization.

Verification:

```text
lake env lean GaloisForLFunctions/RHTower/SoninLogClockQuantumFisher.lean
lake build GaloisForLFunctions.RHTower.SoninLogClockQuantumFisher
  8517/8517
```

The new source specialization uses exactly `propext`, `Classical.choice`, and `Quot.sound`.
Classification: **[REDISCOVERED] [BRIDGE] [LEAN-PROVED]**.  It is a coordinate-free reformulation
of existing static observability, not a dynamical-time premise, novelty claim, or RH advance.
Persistent goal remains active for remaining endpoint audit.

## 21. Affine folded-germ-to-moving prime--Gamma Hankel connector completed

Declaration-vocabulary dependency audit exposed a full duplicated proof chain.
`HTGeometry/ReflectionFoldedMomentGerm.lean` already proves, for any affine anti-invariant source,
that its centered relative trace anti-reflects, its normalized divided-difference germ reflects,
and every germ jet acquires the expected parity.  Nevertheless,
`RHTower/CompletedPrimeGammaMovingHankelReflection.lean` independently rederived all three steps
for `logDeriv xi` from the functional equation.

The RHTower module now imports the generic folded-germ leaf.  Lean definition unfolding gives the
literal adapters

```text
completedMovingRelativeTrace sigma
  = affineRelativeTrace (logDeriv xi) sigma,
completedMovingMomentGerm sigma
  = reflectionFoldedMomentGerm (logDeriv xi) sigma.
```

The existing source theorems `completedMovingRelativeTrace_one_sub`,
`completedMovingMomentGerm_one_sub`, and
`iteratedDeriv_completedMovingMomentGerm_one_sub` now invoke the corresponding generic theorems
with `kappa=1`; `logDeriv_xi_reciprocity` discharges their only source premise.  Existing real
even-moment, matrix, determinant, and complex-Hankel consumers retain unchanged signatures.

Verification:

```text
lake env lean GaloisForLFunctions/RHTower/CompletedPrimeGammaMovingHankelReflection.lean
lake build GaloisForLFunctions.RHTower.CompletedPrimeGammaMovingHankelReflection
  8739/8739
lake env lean GaloisForLFunctions/RHTower/CompletedPrimeGammaMovingComplexHankel.lean
```

The three refactored source declarations and determinant capstone use exactly `propext`,
`Classical.choice`, and `Quot.sound`.  Classification:
**[REDISCOVERED] [BRIDGE] [LEAN-PROVED]**.  This removes source-local reflection algebra and makes
the general/source dependency explicit; it neither supplies determinant positivity nor advances
RH.  Persistent goal remains active for remaining unmatched high-score pairs.

## 22. Finite reporter-network-to-Xi Gram connector completed

The source-facing audit found `HTGeometry/FiniteReporterNetworkFusion.lean` proved the exact
singular-information alternative for an arbitrary finite dependent family of Hilbert-valued
reporters, while `RHTower/XiLogDerivReporterGramFisher.lean` specialized only the older
single-reporter theorem.

The RHTower module now imports the network leaf and exposes two unconditional source theorems:

```text
xiLogDeriv_reporterGram_family_det_eq_zero_iff_exists_commonBlindPacket
xiLogDeriv_add_finiteGibbs_reporterGram_family_det_eq_zero_iff_exists_commonBlindPacket
```

For the bare and finite-Gibbs-dressed Xi logarithmic derivative, respectively, the determinant of
the fused finite-jet Gram matrix vanishes exactly when one nonzero synthesized derivative packet
is erased by every reporter in the network.  The first proof derives constant-coefficient
differential transcendence from the existing actual simple Xi pole.  The second reuses the
existing theorem that finite Gibbs dressing preserves that property.  No transcendence or RH
hypothesis remains at either source interface.

Verification:

```text
lake env lean GaloisForLFunctions/RHTower/XiLogDerivReporterGramFisher.lean
lake build GaloisForLFunctions.RHTower.XiLogDerivReporterGramFisher
  8708/8708
```

Both new source theorems use exactly `propext`, `Classical.choice`, and `Quot.sound`.

Classification: **[REDISCOVERED] [BRIDGE] [LEAN-PROVED]**.  This connects the generic positive
network-fusion law to its canonical RHTower source and strengthens finite-source observability;
it is not a new external novelty or RH criterion.  Persistent goal remains active pending final
hostile audit.

## 23. Thermal finite-action boundary-to-Xi connector completed

`HTGeometry/ThermalMassClockObservability.lean` already proves that a hypertranscendental response
cannot equal any finite complex mass-action signal

```text
sum_(i in S) amplitude_i * exp(-action_i * mass).
```

The endpoint scan found that this generic boundary had no canonical RHTower consumer despite the
existing unconditional theorem `xi_hypertranscendental`.
`RHTower/XiHypertranscendenceUnconditional.lean` now imports the thermal mass-clock leaf and proves
`xi_ne_finiteMassClockSignal` for every finite index set, amplitude family, and complex-action
family.  The proof is a literal specialization of the generic no-go and has no RH premise.

Verification:

```text
lake env lean GaloisForLFunctions/RHTower/XiHypertranscendenceUnconditional.lean
lake build GaloisForLFunctions.RHTower.XiHypertranscendenceUnconditional
  8931/8931
```

The source theorem uses exactly `propext`, `Classical.choice`, and `Quot.sound`.  Targeted diff
checks passed.  Repository-wide formal lint is currently blocked only by unrelated concurrent
module `RHTower.SuzukiCompactifiedPhaseProfile` not yet being reachable from the RHTower umbrella.

Classification: **[REDISCOVERED] [BRIDGE] [LEAN-PROVED]**.  It excludes an exact finite-action
representation of completed Xi; it neither asserts that Xi is physically a probe-mass response
nor constructs the positive infinite-action alternative.  Persistent goal remains active pending
final hostile audit.

## 24. Prime coherence-tail-to-Euler lifting connector completed

`HTGeometry/PrimeCoherenceTailReconstruction.lean` characterized finite-boundary one-endedness by
faithful recovery of projective prime-orientation tail dependence from finite-defect edge
coherences.  Independently, `RHTower/PrimeEulerOrientationNorm.lean` identified that dependence
with exactly two Euler lifts: same-sheet finite-gauge equivalence or opposite-sheet
cyclotomic-norm complementarity.

The RHTower module now imports the coherence leaf and publishes

```text
finiteBoundaryOneEnded_iff_primeEulerCoherenceTail_faithful
primeEulerCoherenceTail_faithful_boxProd.
```

The first theorem says graph one-endedness is exactly the absence of any third Euler lifting mode
for coherently observed prime orientations.  The second discharges that condition for Cartesian
products of two infinite preconnected indexing graphs.  Both are unconditional and retain the
finite-defect/projective scope of their inputs; they do not identify an analytic Euler product or
prove RH.

Verification:

```text
lake env lean GaloisForLFunctions/RHTower/PrimeEulerOrientationNorm.lean
lake build GaloisForLFunctions.RHTower.PrimeEulerOrientationNorm
  8520/8520
```

Both connector theorems use exactly `propext`, `Classical.choice`, and `Quot.sound`.  Targeted diff
checks passed.  Repository-wide formal lint reached only an unrelated concurrent-worktree error:
`RHTower.SuzukiFiniteShiftProjectiveHolonomy` is not yet reachable from the RHTower umbrella.

Classification: **[REDISCOVERED] [BRIDGE] [LEAN-PROVED]**.  Persistent goal remains active pending
final hostile audit.

## 25. Finite observable jet-capacity-to-Xi connector completed

`HTGeometry/FiniteObservableKoopmanBoundary.lean` previously proved only that an
HT derivative-observable tower eventually escapes every finite-dimensional dictionary.  The
finite-rank argument actually gives an exact capacity law under the weaker
constant-coefficient-differential-transcendence premise: for every finite set `S` of derivative
orders captured by `V`,

```text
card(S) <= finrank_C(V).
```

The module now exposes this law as
`iteratedDeriv_mem_finset_card_le_finrank_of_constantCoefficientDifferentiallyTranscendental`.
Choosing the first `finrank(V)+1` orders yields
`exists_iteratedDeriv_not_mem_le_finrank_of_constantCoefficientDifferentiallyTranscendental`:
some derivative of order at most `finrank(V)` already escapes.  The older unbounded existential
theorem now derives from this stronger statement.

`RHTower/XiJetFreeness.lean` imports the generic boundary and publishes the unconditional source
specializations `xi_iteratedDeriv_mem_finset_card_le_finrank` and
`exists_xi_iteratedDeriv_not_mem_le_finrank`, using the existing completed-Xi
hypertranscendence theorem.  No invariant-model, approximation, or RH premise is introduced.

Verification:

```text
lake env lean GaloisForLFunctions/HTGeometry/FiniteObservableKoopmanBoundary.lean
lake build GaloisForLFunctions.HTGeometry.FiniteObservableKoopmanBoundary
  8518/8518
lake env lean GaloisForLFunctions/RHTower/XiJetFreeness.lean
lake build GaloisForLFunctions.RHTower.XiJetFreeness
  8942/8942
```

All five affected generic/source theorems use exactly `propext`, `Classical.choice`, and
`Quot.sound`.  Repository-wide formal lint and targeted diff checks passed.

Classification: **[REDISCOVERED] [BRIDGE] [LEAN-PROVED]**.  This is the sharp finite-rank capacity
form of an existing Koopman/observable no-go, not a quantitative norm-residual estimate or RH
advance.  Persistent goal remains active.

## 26. Finite-generator escape-to-centered-zeta clock connector completed

`HTGeometry/FiniteGeneratorDifferentialEscape.lean` proves the maximal positive survivor of the
failed bounded-innovation programme: if a finite rational generator packet contains an HT
observable, at least one chosen generator derivative leaves the generated field.  The existing
centered-zeta clock module exposed three unconditional meromorphic HT sources but consumed only the
weaker negative finite-state predicate.

`RHTower/ZetaChiHypertranscendentalClock.lean` now imports that positive boundary and publishes

```text
exists_generator_deriv_escape_of_centeredZetaGammaReflectionMero
exists_generator_deriv_escape_of_centeredZetaChiMero
exists_generator_deriv_escape_of_inv_centeredZetaChiMero.
```

For the reflected Gamma clock, complete exponential-dressed archimedean clock, and its reciprocal,
respectively, every finite rational generator packet containing the source has some generator
whose derivative is outside the packet.  These statements are unconditional and source-specific;
they do not claim that bounded per-depth innovation stabilizes, couple the clock to prime data, or
change RH status.

Verification:

```text
lake env lean GaloisForLFunctions/RHTower/ZetaChiHypertranscendentalClock.lean
lake build GaloisForLFunctions.RHTower.ZetaChiHypertranscendentalClock
  8684/8684
```

All three source theorems use exactly `propext`, `Classical.choice`, and `Quot.sound`.
Repository-wide formal lint and targeted diff checks passed.

Classification: **[REDISCOVERED] [BRIDGE] [LEAN-PROVED]**.  This discharges canonical source
interfaces of the existing positive differential-state boundary; it is not new external science
or an RH result.  Persistent goal remains active.

## 27. Centered-zeta phase/current finite-generator connector completed

The section-26 source audit extends through the complete observation-channel classification in
`RHTower/ZetaGammaPhaseIntensityObservability.lean`.  The module already proved that centered zeta
Gamma intensity is exactly `1`, while orientation-sensitive phase and Wigner--Smith logarithmic
current remain hypertranscendental.  Only circuit non-recovery was exposed at those two surviving
channels.

The module now directly publishes

```text
exists_generator_deriv_escape_of_centeredZetaGammaPhaseObservationMero
exists_generator_deriv_escape_of_centeredZetaGammaWignerSmithLogClockMero.
```

Thus every finite rational generator packet containing either HT observation has an explicit
failed differential-closure edge: some chosen generator derivative leaves the packet.  Intensity
is correctly excluded, since the existing exact identity makes it differential-algebraic.  The
proofs reuse the generic positive escape theorem and existing source HT results verbatim.

Verification:

```text
lake env lean GaloisForLFunctions/RHTower/ZetaGammaPhaseIntensityObservability.lean
lake build GaloisForLFunctions.RHTower.ZetaGammaPhaseIntensityObservability
  8690/8690
```

Both source theorems use exactly `propext`, `Classical.choice`, and `Quot.sound`.
Repository-wide formal lint and targeted diff checks passed.

Classification: **[REDISCOVERED] [BRIDGE] [LEAN-PROVED]**.  This completes the positive
finite-generator boundary for the centered-zeta archimedean observation channels; it does not
couple them to primes or alter RH status.  Persistent goal remains active.

## 28. Zeta intensity/calibration finite-generator connector completed

A systematic declaration inventory found only two unconditional RHTower meromorphic
`hypertranscendentalOver_*` sources still lacking the positive finite-generator consumer, both in
`RHTower/ZetaHorizonGammaIntensitySeparation.lean`: the quarter-shifted Gamma intensity core and
the oriented-clock/intensity quotient.

The module now publishes

```text
exists_generator_deriv_escape_of_centeredZetaGammaIntensityCoreMero
exists_generator_deriv_escape_of_centeredZetaGammaReflection_div_intensity.
```

Every finite rational generator packet containing either source has a chosen generator derivative
outside the generated field.  Together with sections 26--27, this closes every unconditional
RHTower theorem whose declaration name begins `hypertranscendentalOver_`; conditional family
classifications and the differential-algebraic unit-intensity channel are not silently included.

Verification:

```text
lake env lean GaloisForLFunctions/RHTower/ZetaHorizonGammaIntensitySeparation.lean
lake build GaloisForLFunctions.RHTower.ZetaHorizonGammaIntensitySeparation
  8691/8691
```

Both source theorems use exactly `propext`, `Classical.choice`, and `Quot.sound`.
Repository-wide formal lint and targeted diff checks passed.

Classification: **[REDISCOVERED] [BRIDGE] [LEAN-PROVED]**.  This completes a source-interface
class rather than sampling another corollary.  It provides no prime coupling or RH conclusion.
Persistent goal remains active for the broader HTGeometry/HilbertMetric endpoint audit.

## 29. Finite observable jet-capacity-to-zeta connector completed

`HTGeometry/ZetaJetFreeness.lean` already specialized unconditional Riemann-zeta
hypertranscendence to algebraic independence of every derivative function.  It did not consume the
stronger exact finite-rank capacity theorem added in section 25.

The module now imports `FiniteObservableKoopmanBoundary` and publishes

```text
riemannZeta_iteratedDeriv_mem_finset_card_le_finrank
exists_riemannZeta_iteratedDeriv_not_mem_le_finrank.
```

For every finite-dimensional complex function space `V`, any finite set of zeta derivative orders
captured by `V` has cardinality at most `finrank V`; consequently, some derivative of order at most
`finrank V` already lies outside `V`.  This is the exact Riemann-zeta twin of the completed-Xi
connector, not merely an unbounded eventual-escape corollary.

Verification:

```text
lake env lean GaloisForLFunctions/HTGeometry/ZetaJetFreeness.lean
lake build GaloisForLFunctions.HTGeometry.ZetaJetFreeness
  8523/8523
```

Both source theorems use exactly `propext`, `Classical.choice`, and `Quot.sound`.
Repository-wide formal lint and targeted diff checks passed.

Classification: **[REDISCOVERED] [BRIDGE] [LEAN-PROVED]**.  Sections 25 and 29 now cover both
unconditional actual-function HT sources in RHTower (`xi` and `riemannZeta`).  The result is
divisor-blind and makes no RH claim.  Persistent goal remains active.

## 30. Finite reporter-network-to-zeta connector completed

After section 29, `HTGeometry/ZetaJetFreeness.lean` had the source independence and exact
finite-dictionary capacity laws but no consumer of the stronger finite reporter-network theorem.
The generic fusion theorem is strictly preferable to a separate single-panel wrapper: it handles
an arbitrary finite dependent family of heterogeneous Hilbert output spaces.

The zeta leaf now publishes

```text
riemannZeta_reporterGram_family_det_eq_zero_iff_exists_commonBlindPacket.
```

For every finite reporter family and jet resolution, the fused zeta information determinant
vanishes exactly when one common coefficient packet is erased by every reporter while its
synthesized zeta derivative function remains nonzero.  Existing unconditional zeta
hypertranscendence discharges the only source premise.

Verification:

```text
lake env lean GaloisForLFunctions/HTGeometry/ZetaJetFreeness.lean
lake build GaloisForLFunctions.HTGeometry.ZetaJetFreeness
  8528/8528
```

The source theorem uses exactly `propext`, `Classical.choice`, and `Quot.sound`.

Classification: **[REDISCOVERED] [BRIDGE] [LEAN-PROVED]**.  This is the strongest existing finite
reporter fusion law at the Riemann-zeta source, not an RH criterion or a claim that reporting
creates dynamics.  Persistent goal remains active.

## 31. Generic reporter data-processing collapse and zeta connector completed

The source-local proof in `RHTower/XiLogDerivReporterDataProcessing.lean` contained a generic law
that had not been named: finite reporter dimension forces one derivative order which is new before
reporting but redundant both in the original reporter and after every downstream linear decoder.
Keeping the same witness order across all clauses is stronger than separate zero-existence
corollaries.

`HTGeometry/FiniteReporterDataProcessing.lean` now publishes

```text
exists_finiteDerivativeReporterConditionalInformation_dataProcessing_collapse.
```

The Xi theorem is refactored to specialize this generic capstone.  `HTGeometry/ZetaJetFreeness.lean`
adds the unconditional parallel source theorem

```text
exists_riemannZeta_finiteReporterConditionalInformation_dataProcessing_collapse.
```

For both sources, one `k` no larger than reporter dimension has zero conditional information before
and after decoding, lies in both corresponding previous-reading spans after reporting, and remains
outside the span of preceding derivative functions at the source.

Verification:

```text
lake env lean GaloisForLFunctions/HTGeometry/FiniteReporterDataProcessing.lean
lake build GaloisForLFunctions.HTGeometry.FiniteReporterDataProcessing
  8525/8525
lake env lean GaloisForLFunctions/RHTower/XiLogDerivReporterDataProcessing.lean
lake build GaloisForLFunctions.RHTower.XiLogDerivReporterDataProcessing
  8685/8685
lake env lean GaloisForLFunctions/HTGeometry/ZetaJetFreeness.lean
lake build GaloisForLFunctions.HTGeometry.ZetaJetFreeness
  8531/8531
```

The generic theorem and both source theorems use exactly `propext`, `Classical.choice`, and
`Quot.sound`.  Repository-wide formal lint and targeted diff checks passed.

Classification: **[REDISCOVERED] [BRIDGE] [LEAN-PROVED]**.  This removes source-local proof
duplication, narrows the Xi module to its exact simple-pole dependency, and connects zeta to the
strongest existing downstream no-recovery statement.  It is static observability, not an RH
criterion.  Persistent goal remains active.
