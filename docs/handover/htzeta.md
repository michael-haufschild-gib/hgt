# HT--Zeta new-paper handover

**Date:** 2026-07-21  
**Repository:** `/Users/Spare/Documents/code/riemann/publications/hgt`  
**Research lane:** hypertranscendental functions first; the Riemann hypothesis is a downstream
pressure test only  
**Intended paper type:** theoretical mathematics paper for a strong general mathematics journal  
**Current verdict:** the strongest paper is a new rank-three localization paper, not an update of
the cofinal-Cholesky manuscript

## 1. Mission for the new session

Develop, complete, formalize, and then write a standalone paper whose central result is the
**rank-three localization and noncompression law for mixed hypertranscendence**.

The paper must not be a survey or a collection of results. Its narrative is:

> Arbitrary-depth compatible translation constraints appear to create genuinely higher-order
> differential-algebraic obstructions. In fact, under rational independence, their entire
> nonlinear Kolchin geometry localizes to rank-three pair faces. Triple compatibility is the only
> gluing law, every pair face is necessary, and the multiple elliptic gamma hierarchy is a
> universal cyclic carrier. As a consequence, the generic non-rational regime of the multiple
> elliptic gamma differential-algebraicity problem is resolved and its complete finite
> arbitrary-translation differential matroid is computed.

The exact proposed title is:

> **Rank-Three Localization of Hypertranscendence and the Differential Matroid of Multiple
> Elliptic Gamma Functions**

The paper authors, when the manuscript is created, are exactly:

> Michael Haufschild, GPT 5.6 Sol, Fable 5, Grok 4.5

Do not mention Lean in the paper. Lean is the internal correctness gate, not part of the scientific
narrative. Formal status, build evidence, and axiom audits belong in internal cards and handovers.

## 2. Required initialization

Before changing mathematics or prose, read completely:

1. `AGENTS.md`;
2. `docs/meta/scientific-method.md`;
3. `/Users/Spare/.codex/skills/l7/hgt-fields-medalist/SKILL.md`;
4. `/Users/Spare/.codex/skills/write/scientific-writing/SKILL.md`;
5. `formal/README.md`.

Then inspect the live versions of every card and Lean module named below. The repository is active
and may have advanced after this handover. Current source always outranks this document.

## 3. Non-negotiable research and proof rules

### 3.1 Pipeline semantics

- `1-in-progress`: conjecture or proof with an open core.
- `2-fully-proven`: complete unconditional paper proof.
- `3-formalized`: the exact claimed theorem is unconditionally formalized and verified in Lean.
- `4-publication-ready`: complete journal manuscript, after mathematical and formal gates.
- `5-failed`: failed route with its positive survivor recorded.

Do not infer proof from polished prose, a card location, a PDF, theorem-shaped Lean source, or a
cached build from an older version.

The user permits established classical theorems from the literature to be cited without
reformalizing them. Every original contribution of this project must nevertheless be formalized
unconditionally from the point where those classical inputs enter.

### 3.2 Anti-theatre standard

A result is not new because its terminology, code, or combination is new to this repository.
Novelty is against the literature. The paper must contain a theorem that changes the external
scientific frontier.

Do not count as progress:

- another equivalent RH criterion;
- a repackaging of Stanley--Reisner algebra;
- a restatement of orbital residues;
- a named geometry with no new analytic consequence;
- a collection of unrelated HT, Hilbert, and zeta facts;
- a formal wrapper around an unproved analytic interface;
- an analogy to physics, information theory, or coherence without a transferred theorem.

### 3.3 Lean and machine discipline

- Do not run computations or numerical experiments.
- Never run a full Lean build.
- Use at most one foreground Lean process owned by this task.
- Do not launch Lean checks in parallel with one another.
- Use `lake env lean path/to/File.lean` for ordinary verification.
- Use `lake build Exact.Module.Name` only for the final targeted audit or when an immediate `.olean`
  is genuinely missing.
- Before a build, check for existing Lean/lake processes. Do not kill another agent's process.
- After a build, make sure this task has left no stale process.
- Batch a substantial source change before rebuilding; do not edit/build cycle after tiny changes.
- Preserve the dirty worktree and unrelated changes made by the user or other agents.

This handover was produced by source inspection. No fresh Lean build was run for it.

## 4. Executive mathematical verdict

The strongest candidate is not the cofinal-Cholesky carrier-selection law, the bare HT
constraint-spectrum universality theorem, the Gamma pole grading, a Gaussian Hilbert curvature
law, or an RH criterion.

It is the following theorem package.

> **Rank-three localization and noncompression law.** For every rationally independent finite
> mixed-translation constraint class, the complete nonlinear differential-algebraic matroid is
> determined by compatible rank-three pair faces. Every nonlinear differential dependence
> becomes a constant-coefficient differential-linear dependence after applying the pair-face
> signature. Triple compatibility is necessary and sufficient for gluing. Every pair carries a
> nonzero private sector, so no proper deletion of pair coordinates remains complete.

This theorem is universal inside a natural analytic class, not universal for every HT function.
That distinction is essential: the corpus separately proves that bare HT can realize essentially
arbitrary finite constraint spectra.

## 5. Mathematical setup

Fix `d >= 2` and complex numbers

```text
1, tau_1, ..., tau_d
```

that are linearly independent over `Q`. Let

```text
Delta_tau F(z) = F(z + tau) - F(z).
```

Define the mixed-constraint class

```text
Q_d = {F in Mer(C) :
       F(z+1)=F(z),
       product_(i=1)^d Delta_(tau_i) F is constant}.
```

For an unordered pair `e={i,j}`, define

```text
H_e = Z + Z tau_i + Z tau_j,
A_e = C[delta][C/H_e],
W_e(F) = product_(k notin e) Delta_(tau_k) F.
```

The function `W_e(F)` is a depth-two or triptic face. Let `S_e(F)` be its complete triptic
orbit-residue divisor in `A_e`. The pair-face signature is

```text
PF_d(F) = (S_e(F))_(|e|=2).
```

For every triple `{i,j,k}`, the three pair components have a common pushforward to the quotient by

```text
Z + Z tau_i + Z tau_j + Z tau_k.
```

Let `Comp_d` be the module of finite pair-divisor families satisfying precisely these triple
compatibility conditions.

## 6. The intended master theorem

The paper should prove the following as one integrated theorem, not as unrelated propositions.

### 6.1 Exact pair-face quotient

The pair-face map induces a differential-translation module isomorphism

```text
Q_d / (Q_d intersect Mer_DA)  ~=  Comp_d.                       (A)
```

Consequently,

```text
F is DA over C(z)  iff  PF_d(F)=0.                              (B)
```

This asserts both completeness and exact realization. It is stronger than merely embedding the
quotient into a residue space.

### 6.2 Complete nonlinear differential matroid

For every finite family `F_1,...,F_m in Q_d`, prove

```text
dtrdeg_(C(z)) C(z)<F_1,...,F_m>_delta
  = dim_(C(delta)) span{PF_d(F_1),...,PF_d(F_m)}.                (C)
```

This is the central scientific theorem. It says that all nonlinear differential dependence
linearizes on the compatible pair-face boundary.

Do not infer `(C)` merely from `(A)`. An additive module quotient does not rule out nonlinear
differential relations between elements with linearly independent images. The relative
independence/gluing argument is indispensable.

### 6.3 Universal cyclic carrier

Let

```text
B = C[delta][C]
```

be the finite-support group algebra of arbitrary complex translations. Let

```text
pi_e : B -> A_e,
I_d = intersection_(|e|=2) ker pi_e.
```

For the order-`d-1` multiple elliptic gamma logarithmic derivative `Psi_(d-1)`, prove

```text
Comp_d = B . PF_d(Psi_(d-1)) ~= B/I_d.                         (D)
```

Therefore, for arbitrary finite translation-differential operators `P_1,...,P_m in B`,

```text
dtrdeg(P_1 Psi_(d-1),...,P_m Psi_(d-1))
  = dim_(C(delta)) span{Pbar_1,...,Pbar_m in B/I_d}.             (E)
```

This is the arbitrary-complex-translation theorem. It strictly strengthens the previously
paper-proved structural-translation theorem.

### 6.4 Orbitwise Stanley--Reisner normal form

Let

```text
L = sum_i Z tau_i in C/Z.
```

Decompose `B` into its `L`-orbits. On every orbit,

```text
R_c ~= C[delta][t_1^(+-1),...,t_d^(+-1)],
x_i = t_i - 1.
```

Then

```text
I_d intersect R_c
  = intersection_(i<j)(x_i,x_j)
  = (x_J : |J|=d-1).                                          (F)
```

Thus each orbit quotient is the localization of the Stanley--Reisner ring of the
`(d-2)`-skeleton. This algebra is a mechanism and normal form, not by itself the novelty claim.

### 6.5 Noncompression and exact private depth

For every pair `e`, define its private sector by intersecting all pushforward kernels toward
adjacent triples. Prove

```text
Priv_e = (product_(k notin e)(t_(tau_k)-1)) A_e.                (G)
```

It is nonzero, has exact transverse order `d-2`, and is invisible on every other pair. Canonical
private witnesses over all pairs are independent and span a space of dimension

```text
choose(d,2).                                                   (H)
```

Therefore every pair coordinate is necessary. No terminal residue, spanning tree, selected atlas,
or proper pair-face deletion classifies all of `Q_d/DA`.

The positive statement is not “compression fails.” It is:

> The complete compatible two-skeleton is the unique minimal information boundary, with locality
> dimension two, gluing dimension three, and private concealment depth `d-2`.

### 6.6 Multiple elliptic gamma consequence

For generic periods satisfying rational independence:

1. every multiple elliptic gamma function of positive order is hypertranscendental;
2. its finite arbitrary-translation family has the exact differential matroid `(E)`;
3. finite products and quotients of translates are DA exactly when their operator class lies in
   `I_d`;
4. structural mixed differences are DA exactly at the squarefree transverse-support threshold.

This resolves the fully rationally independent, hence generic, part of Kato's published
non-rational-period question. Do **not** claim all non-rational tuples: partially dependent
non-rational period vectors remain outside the theorem.

## 7. Why this theorem matters

The paper has four mutually reinforcing contributions.

1. **Local-to-global classification.** Arbitrary constraint depth creates no new invisible HT
   obstruction beyond rank-three faces.
2. **Nonlinear-to-linear collapse.** The entire Kolchin matroid becomes linear algebra on compatible
   pair residues.
3. **Minimality.** The complete two-skeleton is not only sufficient; every pair coordinate is
   independently necessary.
4. **Open special-function problem.** The generic non-rational multiple elliptic gamma regime is
   settled and strengthened to a full translation-family classification.

If correct and independently verified, this is suitable for a strong general mathematics journal.
It is not a Nature/Science-style result and should not be marketed as one.

## 8. Internal paper-level sources

Read these cards in full and reconcile any stale status text against the current Lean tree.

### Primary theorem cards

- `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/`
  `all-depth-compatible-pair-face-differential-matroid.md`
- `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/`
  `all-depth-pair-face-signature-completeness.md`
- `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/`
  `hypertranscendental-pair-localization-noncompression.md`
- `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/`
  `all-order-multiple-elliptic-gamma-structural-differential-matroid.md`
- `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/`
  `multiple-elliptic-gamma-transverse-constraint-depth.md`
- `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/`
  `irrational-elliptic-gamma-hypertranscendence-matroid.md`
- `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/`
  `elliptic-gamma-rank-three-da-spectrum.md`

### Ambient universality result

- `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/`
  `hypertranscendental-constraint-spectrum-universality.md`

Use the ambient universality result only to explain why rank-two locality is source-selected and
not a law of bare HT. Do not make it a second main theorem of the paper.

## 9. Current Lean theorem surface

The following source declarations were inspected during the audit. No fresh build was run, so the
new session must verify current compile status before applying `[LEAN-PROVED]`.

### 9.1 Genuine order-one elliptic gamma

- `formal/GaloisForLFunctions/HTGeometry/MeromorphicEllipticGamma.lean`
- `formal/GaloisForLFunctions/HTGeometry/EllipticGammaProduct.lean`
- `formal/GaloisForLFunctions/HTGeometry/EllipticGammaPairedIncrement.lean`
- `formal/GaloisForLFunctions/HTGeometry/EllipticGammaMixedFace.lean`

These construct the actual meromorphic elliptic gamma product and its logarithmic derivative. Do
not replace the real special function by an abstract surrogate in the final capstone.

### 9.2 Order-one HT and defect matroid

- `EllipticGammaExternalDefectOstrowski.lean`
  - `ellipticGammaExternalDefectFamily_differentialIndependent`
- `EllipticGammaStructuralGeneratorSpectrum.lean`
  - `differentialAlgebraicOver_ellipticGammaExternalLogDerivDefectMero_iff_resonant`
- `EllipticGammaPeriodCosetMatroid.lean`
  - `ellipticGammaExternalDefectFamily_differentialMatroid_eq_periodCosetPartitionMatroid`
  - `ellipticGammaExternalDefectFamily_eRk_eq_nonzeroPeriodClass_encard`
- `EllipticGammaPairwiseCommonModeSpectrum.lean`
  - exact relative closure and circuit statements
- `EllipticGammaQuotientPeriodCosetMatroid.lean`
  - `differentialAlgebraicOver_ellipticGammaExternalQuotientMero_iff_resonant`
  - quotient/defect matroid transport
- `EllipticGammaRationalBaseMatroid.lean`
  - `ellipticGammaExternalDefectFamily_differentialIndependent_rationalBase`
  - `hypertranscendentalOver_ellipticGammaMero_rationalBase`

Important base-field distinction:

- the exact pointed partition matroid is present over the paired elliptic compositum;
- separated nonresonant families and source HT are present over the embedded rational field
  `C(z)`;
- transporting every resonant/relative pointed-matroid statement to `C(z)` still requires the
  concrete elliptic-compositum DA foundation or a precise classical input boundary.

Do not silently identify the paired elliptic compositum with `C(z)`.

### 9.3 Actual all-order hierarchy

- `MultipleEllipticGammaProduct.lean`
- `MeromorphicMultipleEllipticGamma.lean`
- `MultipleEllipticGammaFieldHierarchy.lean`
- `MultipleEllipticGammaFaceHierarchy.lean`
  - `multipleEllipticGammaLogDerivFaceMero_addTranslation_sub`

The last theorem says that translating a genuine face in any surviving structural direction and
taking its defect deletes exactly that period. It supplies the actual analytic coface system.

### 9.4 Abstract differential-matroid and Stanley--Reisner engine

- `DifferentialOperatorMatroid.lean`
- `DifferentialMatroidGluing.lean`
  - `Rank.uniformFace_nestedStar_indep`
- `LocalizedStanleyReisnerDifferentialMatroid.lean`
  - `differentialIndependent_stanleyReisnerLaurentRows_iff`
- `LocalizedStanleyReisnerMatroidRank.lean`
  - `stanleyReisnerLaurentMatroid_indep_iff`
  - exact row-span rank statements
- `SquarefreeVeroneseIdeal.lean`
- `SquarefreeVeronesePairDetection.lean`
  - `mem_veroneseIdeal_iff_every_pair_meets_support`
  - `exists_pair_disjoint_support_of_not_mem_veroneseIdeal`
  - `monomial_mem_veroneseIdeal_iff`
- `FreeShiftOneSliceNonsummability.lean`
- `DifferentialIndependentOneSliceNonsummability.lean`

These formalize the algebraic and abstract rank mechanisms. They do not by themselves identify the
actual multiple elliptic gamma hierarchy with the abstract row family.

### 9.5 Pair-private minimality

- `TelescopeIdeal.lean`
  - `iInf_span_singleton_eq_span_prod`
  - `iInf_span_singleton_eq_span_prod_of_primes`
- `PairFacePrivateSector.lean`
  - `pairPrivateWitness_exact`
  - `pairPrivateWitness_coordinates`
  - `pairPrivateWitness_linearIndependent`
  - `pairFaceIndex_card`
  - `pairPrivateWitness_span_finrank`

This is the unconditional algebraic core of noncompression. The remaining analytic statement is
that these coordinates are realized by actual meromorphic HT classes.

## 10. Exact open core

The paper is not ready merely because its components exist. The central capstone is not yet one
verified Lean theorem.

### Open core A: concrete pair-face invariant

Define in Lean, for the actual meromorphic mixed-constraint class:

- triptic orbit-residue divisors on every unordered pair;
- pushforward to every triple;
- the compatible equalizer `Comp_d`;
- the pair-face map and its differential/translation equivariance.

Reuse existing orbit-residue, principal-part, difference-differential, and actual elliptic-gamma
modules. Do not create an abstract interface that assumes exact realization.

### Open core B: all-depth exact image

Formalize the complete proof of

```text
Q_d / DA ~= Comp_d.
```

The proof architecture in the card is:

1. define the bottom charge in one surviving direction;
2. identify every pair involving that direction as a pushforward of the bottom charge;
3. use multi-telescoping to show vanishing pushes make the charge one full transverse coboundary;
4. remove the coboundary by a DA theta layer;
5. descend from depth `d` to `d-1`;
6. prove triple compatibility is sufficient for simultaneous divisor lifting;
7. prove every compatible family is realized by an operator on the top multiple-gamma carrier.

The meromorphic principal-part realization and its exact DA boundary must be explicit. A finite
Laurent ideal identity is not a substitute.

### Open core C: relative nonlinear independence

Formalize the theorem that independent bottom charges contribute full differential-transcendence
rank over the field generated by kernel combinations and proper faces.

The current paper proof uses:

- the several-automorphism Ostrowski theorem;
- joint fixed-field collapse from the periods `1,tau_q,tau_u`;
- one-slice nonsummability in a differentially independent bilateral shift field;
- descent through face depth.

This is the step that prevents the module-isomorphism fallacy.

### Open core D: discharge the gluing interfaces

For the actual hierarchy, prove the concrete hypotheses consumed by
`Rank.uniformFace_nestedStar_indep`:

1. **star differential independence**;
2. **integer orbit-height/free translates** on every enlarged star;
3. **off-star packetwise DA**, supplying `CrossNeutral`;
4. stability of every intermediate differential field under the two translations used for joint
   constant collapse.

The abstract gluing theorem already exists. Do not duplicate it.

### Open core E: hierarchy-to-row and arbitrary cosets

Prove that the full arbitrary-coset face decomposition of the genuine carrier is exactly the
localized Stanley--Reisner row model, including:

- injectivity of the external-coset labels;
- finite-support orbit decomposition;
- Laurent denominator clearing;
- independence across different pair faces;
- the final differential-linear rank formula for arbitrary dependent row packets.

Then state one final capstone theorem whose conclusion is `(C)` and whose special-function
corollary is `(E)`.

## 11. Hostile proof audit

Before formalization or manuscript drafting, attack the paper proof against each item below.

### 11.1 Module-isomorphism fallacy

`Q_d/DA ~= Comp_d` does not imply the differential-transcendence rank formula. Locate the exact
relative-independence proof for every induction step.

### 11.2 Nonlinear closure counterexamples

Try to construct `F,G in Q_d` with `G` differentially algebraic over `F` but independent pair-face
images. Operations such as `F^2`, `1/F`, composition, and algebraic substitution usually leave the
additive mixed-constraint class, but this must be proved rather than assumed.

### 11.3 Cross-face circuits

Atomicity on each pair separately does not imply joint independence across different elliptic
curves. Triple compatibility creates real linear coupling. Prove that it creates no additional
nonlinear circuit.

### 11.4 Base-field comparison

Track exactly whether every statement is over:

- `C`;
- `C(z)`;
- one elliptic function field;
- the paired elliptic compositum;
- the field of all periodic DA meromorphic functions;
- a field generated by deeper face families.

Do not use field inclusion where only a common differential-algebraic compositum exists.

### 11.5 Joint constants

Every Ostrowski/Picard--Vessiot application must prove that the joint fixed field is exactly `C`.
The mechanism is the nondiscrete period group generated by `1,tau_q,tau_u`; check that every
intermediate field consists of global meromorphic `1`-periodic functions and is stable under the
relevant translations.

### 11.6 Cyclicity

Exact realization of compatible divisors does not automatically prove every class is one finite
translation-differential operator applied to `Psi_(d-1)`. Check the induction proving that every
lower-depth correction remains an operator on the same top carrier.

### 11.7 Infinite quotient bookkeeping

`C/L` has uncountably many cosets. All operators and divisors have finite support, so every proof
must reduce to finitely many orbit components. Do not introduce an unjustified completion or
infinite sum.

### 11.8 Period dependence boundary

Rational independence is structural, not cosmetic. It supplies:

- free structural lattices;
- infinite transverse orbits;
- injective external-coset labeling;
- distinct private witness support;
- joint constant collapse.

Do not extend the theorem to partially dependent non-rational periods without new analysis.

### 11.9 Actual-function test

Every elliptic-gamma corollary must use the genuine product and its global meromorphic logarithmic
derivative. An abstract compatible primitive is insufficient for the open-problem claim.

### 11.10 Minimality test

Prove both sufficiency and irredundancy. The pair-face signature is not a minimal boundary merely
because it is complete; private realized HT sectors must show that deleting any pair loses
information.

## 12. External literature baseline

Refresh the search before making a novelty claim. At the time of this handover, the following were
the strongest located parents.

### 12.1 Explicit open problem

Masaki Kato, *Differential Algebraicity of the Multiple Elliptic Gamma Function for a Rational
Period*, Funkcialaj Ekvacioj 64 (2021), 225--235.

- DOI: `https://doi.org/10.1619/fesi.64.225`
- PDF: `https://www.jstage.jst.go.jp/article/fesi/64/2/64_225/_pdf`
- Theorem 1.1 proves DA for rational period tuples.
- Remark 1.2 says the non-rational case is unknown and suggests general DA should fail.

The paper may claim resolution only of the fully rationally independent generic regime.

### 12.2 One-curve elliptic summability

Carlos E. Arreche and Matthew W. Babbitt, *Panorbital residues and elliptic summability*.

- `https://arxiv.org/abs/2508.18247`

This gives a complete obstruction for one non-torsion translation on one elliptic curve. It does
not join several noncommensurable elliptic curves, produce a compatible two-skeleton, or compute an
all-depth nonlinear differential matroid.

### 12.3 Elliptic difference hypertranscendence

Ehud de Shalit, Charlotte Hardouin, Julien Roques et al., *Hypertranscendence and q-difference
equations over elliptic function fields*.

- `https://arxiv.org/abs/2409.10092`

This concerns multiplication endomorphisms of an elliptic curve and an integrability
classification over one elliptic function field, not the paired additive-translation hierarchy.

Carlos E. Arreche, Thomas Dreyfus, and Julien Roques, *Differential transcendence criteria for
second-order linear difference equations and elliptic hypergeometric functions*.

- `https://www.numdam.org/articles/10.5802/jep.143/`

This proves HT for broad elliptic-hypergeometric equations, not elliptic gamma or its exact shift
matroid.

### 12.4 Elliptic gamma geometry

Giovanni Felder and Alexander Varchenko, *The elliptic gamma function and `SL(3,Z) x Z^3`*.

- `https://arxiv.org/abs/math/9907061`

This supplies functional equations, automorphic structure, and the rank-three geometric parent,
not a differential-algebraic spectrum.

Also inspect:

- Felder--Henriques--Rossi--Zhu, the elliptic-gamma gerbe;
- Narukawa, multiple elliptic gamma hierarchy and modular identities;
- Nishizawa, multiple elliptic gamma definitions and recursion;
- Winding, multiple elliptic gamma functions associated to cones;
- Hardouin--Singer, parameterized difference Galois theory for several automorphisms;
- Cassidy, differential algebraic subgroups of the additive group;
- multivariate rational summability and mixed-shift residue literature.

### 12.5 Required novelty search

Search exact, equivalent, stronger, mechanism, and older terminology for:

- multiple elliptic gamma differential transcendence;
- differential algebraic independence of elliptic-gamma translates;
- several-translation elliptic residues;
- compatible pair-face or two-skeleton residue classification;
- local-to-global differential algebra for commuting translations;
- differential matroids of special-function translation modules;
- Stanley--Reisner annihilators in parameterized difference Galois theory;
- arbitrary-translation rank formulas for multiple gamma hierarchies.

Absence from keyword search is not proof of novelty. A specialist in difference algebra and a
specialist in elliptic special functions must independently review priority.

## 13. Paper architecture

Do not start the LaTeX manuscript until the master theorem and its exact scope are stable. When the
proof is ready, use this structure.

### 13.1 Introduction

1. State Kato's rational/non-rational boundary.
2. Ask the broader question: can higher-depth compatible difference constraints contain genuinely
   higher differential-algebraic obstructions invisible on all rank-three faces?
3. State the rank-three localization theorem and rank formula.
4. State noncompression and the multiple-gamma application.
5. Explain that the contribution is the analytic/differential-algebraic conjunction, not the
   individual residue, Galois, or Stanley--Reisner ingredients.

### 13.2 Preliminaries

- differential algebra and differential transcendence degree;
- finite-support translation group algebras;
- elliptic orbital residues;
- several-automorphism Ostrowski theorem;
- actual multiple elliptic gamma hierarchy.

Use established literature theorems explicitly and state their hypotheses exactly.

### 13.3 Rank-three pair-face invariant

- define `Q_d`, `A_e`, pair faces, pushforwards, and `Comp_d`;
- prove necessity of triple compatibility;
- prove the depth-two base theorem.

### 13.4 Exact-image and localization theorem

- simultaneous finite-divisor lifting;
- bottom-charge exact sequence;
- DA theta-layer removal;
- induction on depth;
- exact quotient `(A)`.

### 13.5 Nonlinear matroid theorem

- arbitrary-coset orbit decomposition;
- bottom-layer atomicity;
- nested-star gluing;
- descending face lifting;
- differential-linear rank lemma;
- rank formula `(C)`.

This is the technical center of the paper.

### 13.6 Minimality and private sectors

- telescope ideal identity;
- private-sector formula `(G)`;
- canonical realized private carriers;
- exact `choose(d,2)` rank;
- deletion noninjectivity.

### 13.7 Universal multiple-gamma carrier

- cyclicity `(D)`;
- localized Stanley--Reisner normal form `(F)`;
- arbitrary translation-family matroid `(E)`;
- multiplicative products and quotients.

### 13.8 Kato-regime corollary and boundaries

- generic irrational HT at every order;
- exact scope of rational independence;
- no assertion for every partially dependent non-rational vector;
- concise comparison with parent literature.

### 13.9 No separate RH section

At most include one short outlook paragraph saying that rank-three localization can test finite
mixed-translation proof architectures. Do not include RHTower criteria, Hilbert curvature results,
physics analogies, or an RH theorem in the main paper.

## 14. Claims allowed and forbidden

### Allowed only after proof closure

- “The compatible rank-three two-skeleton is a complete invariant modulo DA.”
- “Every nonlinear differential dependence is detected by a linear pair-face relation.”
- “Every pair face is indispensable.”
- “The multiple elliptic gamma hierarchy is a universal cyclic carrier for `Comp_d`.”
- “The generic rationally independent non-rational regime is hypertranscendental.”
- “The exact arbitrary-translation differential matroid is `B/I_d`.”

### Forbidden overclaims

- “All non-rational multiple elliptic gamma functions are HT.”
- “This proves or advances RH.”
- “Rank-three localization is a law of every HT function.”
- “The module isomorphism automatically proves the nonlinear matroid.”
- “No literature search found the phrase, therefore the theorem is novel.”
- “The paper is publication-ready because its components exist in Lean.”
- “Stanley--Reisner algebra itself is the new result.”
- “A physical interpretation supplies evidence for the theorem.”

## 15. Why the other strong corpus results are not the main paper

### 15.1 Bare constraint-spectrum universality

The corpus formalizes realization of arbitrary finite simplicial HT constraint spectra. This is a
strong ambient no-go: bare HT alone forces no fixed locality, purity, or duality law. It does not
solve the special-function open problem and should appear only as motivation for why the
multiple-gamma codimension-two stratum is source-selected.

### 15.2 Gamma pole valuation and grading

The newest Gamma modules prove deep local statements, including:

- canonical reciprocal-Bell pole degree;
- cofinal exact pole order for every constant-coefficient Gamma jet polynomial;
- classification of at-most-simple packets as exactly `a+b Gamma`;
- first-subprincipal and binomial descent laws.

Key module:

- `formal/GaloisForLFunctions/HTGeometry/GammaPoleReciprocalBellGrading.lean`
  - `gammaAffineJetTowerAtMostSimple_iff_affine_undifferentiated`

This is a serious second-paper candidate. It presently does not resolve the global joint
Gamma--zeta differential-independence problem, so it does not outrank the pair-face theorem for
the current goal.

### 15.3 HilbertMetric laws

The Gaussian dimension--curvature--rigidity and Fock-shadow results are elegant universal Hilbert
theorems. They currently do not close a comparably explicit external open problem. Do not splice
them into this paper.

### 15.4 RHTower

`RHTower/RiemannHypothesisSOTA2026.lean` is the current typed ledger of RH routes. It shows that the
Hedenmalm, Suzuki, Connes, Weil, Li, Möbius, Salem, and other routes still have named source-side
walls. Their formal criteria are consumers or equivalences, not an RH proof.

## 16. RH pressure test

The research remains HT-first. The precise possible RH relevance is:

> If an RH proof route is genuinely expressible through a finite rationally independent
> mixed-translation constraint system modulo DA, then every obstruction in that architecture must
> be visible on a rank-three face; no higher-depth hidden obstruction can appear only after all
> pair faces vanish.

This does not presently apply to zeta. The Euler product introduces infinite arithmetic assembly,
and the known RH routes require positivity, polarization, continuation, or noncompact limiting
information absent from the bare pair-face module.

A real RH application would require a new theorem constructing a faithful map from the
Euler--Gamma--theta source into a pair-face constraint class and proving that the required
positivity or spectral structure is conservative under that map. No such bridge is currently
proved. Do not place one into the paper as speculation.

## 17. Recommended execution order for the new agent

### Phase 1: refresh the live frontier

1. Read every primary card and module above.
2. Search the current tree for newer pair-face, multiple-gamma, orbit-height, `CrossNeutral`, and
   hierarchy-to-row theorems.
3. Correct stale card descriptions if they understate or overstate the live Lean surface.
4. Refresh the literature search through the current date.

### Phase 2: re-audit the complete paper proof

1. Normalize the theorem statement and all base fields.
2. Write the dependency graph from the depth-two theorem to `(C)`.
3. Attack every item in Section 11.
4. If any implication is not dependency-closed, return the card to Stage 1 and name the exact open
   core. Do not begin new Lean infrastructure until the paper proof closes again.

### Phase 3: formalize one coherent capstone batch

1. Reuse the existing exact-image, residue, hierarchy, one-slice, gluing, and row-rank modules.
2. Add only helpers required by Open cores A--E.
3. Batch source edits before the first Lean check.
4. Run one exact leaf check at a time.
5. Run the exact final module build and axiom audit once the batch is mature.
6. Move the exact theorem card to Stage 3 only after the final capstone compiles unconditionally.

### Phase 4: write the paper

Create a new directory, not an update to the Cholesky paper. Suggested path:

```text
docs/drafts/pipeline/4-publication-ready/
  rank-three-localization-hypertranscendence/
```

Required outputs:

```text
main.tex
main.pdf
```

The manuscript must use the exact author list above, contain no mention of Lean, cite primary
literature, and distinguish the generic rationally independent theorem from the unresolved
partially dependent boundary.

### Phase 5: antagonistic publication audit

Before calling the paper publication-ready, obtain:

1. a proof audit by a difference-algebra specialist;
2. a proof and convention audit by an elliptic-special-function specialist;
3. a priority search by someone not involved in generating the theorem;
4. a manuscript review focused on whether the nonlinear matroid theorem is truly established and
   whether the Kato comparison uses exactly the same function convention and period hypotheses.

## 18. Success criteria

The task is complete only when all of the following hold.

- The exact rank-three localization theorem has a dependency-closed paper proof.
- The exact theorem, including the nonlinear rank formula and actual multiple-gamma carrier, is
  unconditionally formalized and verified.
- Pair-face minimality is realized by actual meromorphic HT classes, not only polynomial witnesses.
- The generic non-rational Kato corollary follows for the actual special function over `C(z)`.
- The literature audit finds no equivalent or stronger theorem and records its limitations.
- The paper has one theorem-driven narrative and no unrelated Hilbert/RH result collection.
- The manuscript states all hypotheses, base fields, and boundaries honestly.
- `main.tex` and a visually checked `main.pdf` exist in the new publication-ready subfolder.

## 19. Honest current assessment

At the time of this handover:

- theorem novelty potential: approximately `90/100`;
- mathematical significance potential: approximately `85/100`;
- actual submission readiness: approximately `50/100`;
- order-one generic elliptic-gamma HT: substantially formalized in the real analytic model;
- actual all-order hierarchy: substantially formalized;
- algebraic pair-face and Stanley--Reisner engines: formalized;
- central all-depth exact-image and nonlinear-matroid capstone: still not one verified Lean theorem;
- external priority: promising but provisional;
- RH consequence: none currently.

The next mathematical delta is not another narrative, analogy, or paper draft. It is closure of the
concrete all-depth pair-face exact-image and relative nonlinear-independence capstone.
