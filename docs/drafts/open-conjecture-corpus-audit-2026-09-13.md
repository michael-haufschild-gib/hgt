# Open-conjecture audit of the Lean corpus

**Cutoff:** 13 September 2026  
**Question:** Does the corpus already settle a nontrivial problem that remains open in the external literature, independently of its RH objective?  
**Build policy:** No build, Lean invocation, or test command was run for this audit.

## Executive verdict

Yes, with qualifications.

| External problem | Corpus result | Verdict | Confidence |
|---|---|---|---|
| Kato's 2021 question about differential algebraicity of multiple elliptic gamma functions at non-rational periods | Exact rational-affine/rank-three dichotomy, including an explicit non-rational differentially algebraic example | **Strongest affirmative case** | High that the Lean theorem says this; medium-high that no prior public resolution exists |
| Kotowski--Oszmaniec's 2026 open direction on deterministic recurrence for mixed states and observable expectation values | Finite Hermitian mixed-state/Born escape--return theorem with a visible-sector certificate deadline | **Affirmative for one stated open direction, not all recurrence questions in the paper** | High on formal scope; medium-high on external novelty |
| Planat's 2026 polynomial-gauge Painleve III--Xi Bridge Conjecture | No entire differentially algebraic carrier times any polynomial exponential gauge can equal completed Xi | **Negative resolution/refutation, but hybrid Lean + paper reduction** | High on the abstract Lean obstruction; medium on the Painleve application |
| Joint Hurwitz-zeta shift-variable differential independence | Exact finite-family differential-matroid classification by residues modulo `Z` | **Likely new theorem, but no matching pre-existing conjecture found** | High on corpus claim; insufficient basis to call it a conjecture resolution |

The conservative count is therefore:

- **one strong likely resolution of a literature-open problem** (Kato);
- **one partial resolution of an explicit 2026 open-problem programme** (mixed-state/observable recurrence);
- **one stronger-than-stated refutation of a 2026 conjecture**, with the final Painleve specialization not itself encoded in Lean;
- several apparently novel results that should not be marketed as conjecture resolutions without a matching external statement.

## Standard used

I counted a result only when:

1. an external source explicitly states a conjecture, question, or open direction;
2. a corpus theorem matches its mathematical objects closely enough to imply an answer, rather than proving a finite toy analogue or a conditional interface;
3. the relevant Lean leaf is dependency-closed according to existing project audits and contains no visible `sorry`, `admit`, new `axiom`, `opaque`, or `unsafe` declaration in the inspected core files; and
4. targeted searches through the cutoff did not locate an earlier public resolution.

Criterion 4 is a priority search, not proof of priority. MathSciNet/Zentralblatt and specialist review remain necessary before a publication claim.

## 1. Kato's non-rational-period multiple elliptic gamma problem

### External status

Masaki Kato proved differential algebraicity for a rational-period regime and stated that the non-rational-period case was unknown, while suggesting that the rational result should not extend generically and that exceptional cases might exist. See [Kato, *Differential Algebraicity of the Multiple Elliptic Gamma Function for a Rational Period*](https://doi.org/10.1619/fesi.64.225) and the [publisher PDF](https://www.jstage.jst.go.jp/article/fesi/64/2/64_225/_pdf).

Targeted searches for later work using the exact differential-algebraicity and hypertranscendence terminology found no public classification or answer through the cutoff. Recent adjacent papers on multiple elliptic gamma functions include [Morain I](https://arxiv.org/abs/2510.16515), [Morain II](https://arxiv.org/abs/2602.06561), and [Lei--Li](https://arxiv.org/abs/2608.24083), but the surfaced records do not resolve Kato's differential-algebraicity problem.

### Corpus result

The theorem
[`multipleEllipticGamma_exactPeriodRankDichotomy`](../../formal/GaloisForLFunctions/HTGeometry/MultipleEllipticGammaPeriodRankDichotomy.lean#L976)
states, for every finite nonempty family of upper-half-plane periods, an exact dichotomy:

- augmented rational period rank `2` iff both the multiple elliptic gamma function and its logarithmic derivative are differentially algebraic over `C(z)`; and
- augmented rank at least `3` iff both are hypertranscendental.

The same file gives:

- a cardinality-free finite-section law in
  [`multipleEllipticGamma_everyPeriodFamily_exactFiniteSectionLaw`](../../formal/GaloisForLFunctions/HTGeometry/MultipleEllipticGammaPeriodRankDichotomy.lean#L818); and
- the explicit period tuple `(i, 1+i)`, proved not to satisfy Kato's rational-ray condition but nevertheless differentially algebraic, in
  [`multipleEllipticGammaNonRationalDAExample_differentialAlgebraic`](../../formal/GaloisForLFunctions/HTGeometry/MultipleEllipticGammaPeriodRankDichotomy.lean#L912).

This does more than produce one exceptional non-rational example: it classifies the full finite parameter space by rational-affine rank. The functions are the corpus's analytic infinite-product constructions, not uninterpreted stand-ins.

### Assessment

**Best answer to the user's question.** The external paper says the non-rational regime is unknown; the corpus supplies both the expected generic hypertranscendence and the anticipated exceptional differentially algebraic cases, with an exact boundary.

Before claiming priority publicly, two tasks remain:

1. specialist review that the corpus normalization agrees exactly with Kato's multiple elliptic gamma normalization; and
2. repair/reconcile the current publication package: its cover material describes the Kato theorem, but its `main.tex` presently contains unrelated recurrence/system-clock material. That is a packaging defect, not evidence against the Lean statement.

## 2. Mixed-state and observable-expectation quantum recurrence

### External status

Kotowski and Oszmaniec explicitly list generalization of deterministic recurrence bounds to mixed quantum states and expectation values of observables as an open direction in the current version of [*Tight Bounds on Recurrence Time in Closed Quantum Systems*](https://arxiv.org/abs/2601.10409), published in [Physical Review Letters](https://doi.org/10.1103/crwj-qfw5). Their open list also includes other tasks, such as tight local noncommuting-Hamiltonian bounds and inverse speed limits.

### Corpus result

The corpus proves, for arbitrary finite-dimensional Hermitian Hamiltonians and finite families of weighted expectation records, that every positive tolerance has the following alternative:

- records never exit the tolerance; or
- an observed exit is followed strictly later by a return within tolerance, before a least graph-resolution certificate deadline visible to those records.

The matrix-expectation theorem is
[`finiteHermitianQuantumExpectation_positiveTarget_optimal_neverExits_or_postExit`](../../formal/GaloisForLFunctions/RHTower/FiniteHermitianExpectationPostExitRecurrenceLaw.lean#L266).
The physical density-matrix/quantum-effect specialization is
[`finiteHermitianBorn_positiveTarget_optimal_neverExits_or_postExit`](../../formal/GaloisForLFunctions/RHTower/FiniteHermitianBornPostExitRecurrenceLaw.lean#L120).

### Assessment

This is a credible answer to the paper's **mixed-state/expectation-value deterministic-recurrence direction**. It does not settle every open question in that paragraph: it is finite-dimensional, supplies an upper/certificate return law rather than a tight lower bound or inverse speed limit, and does not solve the thermodynamic, open-system, or local noncommuting many-body versions.

Marketing it as “the Kotowski--Oszmaniec conjecture” would be inaccurate: the source states a research direction, not a single named conjecture. “Resolution of the finite mixed-state/observable recurrence direction” is defensible.

## 3. Planat's Painleve III--Xi Bridge Conjecture

### External status

Planat's 2026 preprint formulates Conjecture 3: completed Xi should equal a pulled-back `PIII(D6)` object times an exponential polynomial gauge of degree at most two. The paper reports a contradiction for a more direct constant-normalization form, but still presents the polynomial-gauge statement as the conjecture. See [Planat, preprint DOI](https://doi.org/10.20944/preprints202604.0442.v1) and the [current manuscript page](https://www.preprints.org/manuscript/202604.0442).

### Corpus result

[`xi_expPolynomialGauge_hypertranscendental`](../../formal/GaloisForLFunctions/RHTower/XiPainleveTauGaugeNoGo.lean#L38)
shows that multiplying Xi by the exponential of **any** complex polynomial cannot place it in the differential-algebraic class.

[`no_entire_differentiallyAlgebraic_expPolynomialBridge_to_xi`](../../formal/GaloisForLFunctions/RHTower/XiPainleveTauGaugeNoGo.lean#L57)
rules out an identity

`xi(s) = exp(Q(s)) E(s)`

for every polynomial `Q` and every entire differentially algebraic `E`.

### Assessment

The Lean result is a stronger abstract obstruction than the conjecture's degree-two gauge. However, the leaf intentionally does not formalize Painleve tau functions or the irregular Riemann--Hilbert data. Its application uses a paper argument that a fixed-monodromy finite-dimensional `PIII(D6)` tau carrier remains differentially algebraic after the algebraic pullback.

Therefore this is **not yet a completely Lean-encoded refutation of a Painleve theorem**. It is a Lean-closed differential-algebraic obstruction plus an informal/ordinary-mathematics specialization. It belongs in the answer, but below Kato in confidence and importance.

## 4. Joint Hurwitz-zeta result: probably novel, not a conjecture match

The corpus proves finite-family joint hypertranscendence in the shift variable in
[`joint_hzeta_hypertranscendental_in_shift`](../../formal/GaloisForLFunctions/Hurwitz/JointHypertranscendence.lean#L46),
and an exact differential-matroid classification for continued Hurwitz functions in
[`continued_hurwitz_intrinsic_residue_differentialMatroid_law`](../../formal/GaloisForLFunctions/Hurwitz/IntegerTranslationDifferentialMatroid.lean#L339).

For finite nonintegral exponent families, differential independence is equivalent to injectivity of `exp(-2 pi i s)`, hence to pairwise incongruence modulo the integers. This appears stronger and more structural than standard individual hypertranscendence results. Relevant surrounding literature includes [Adamczewski--Dreyfus--Hardouin](https://doi.org/10.1090/jams/960) and [Lagarias--Li](https://arxiv.org/abs/1506.06161).

No external source located in this audit poses this exact classification as an open conjecture. It should be presented as a likely new theorem, not counted as a solved conjecture.

## Explicit exclusions

- **Markus's conjecture:** the corpus has an exact theorem, but external literature already proved the conjecture in 2024; see [*Differential and difference independence of zeta and Gamma*](https://doi.org/10.1016/j.jde.2024.08.068). It is not open as of the cutoff.
- **Nguyen's Böttcher Question 6.2:** the repository contains a paper-proof card for the quadratic `n = 2` case, but the card says Lean formalization has not started. Conditional/formal interfaces do not count as a Lean-corpus solution. Source: [Nguyen](https://arxiv.org/abs/1310.2329).
- **Artin holomorphy, Schanuel for `n >= 2`, Selberg normality/orthogonality, Lindelöf/divisor/exponent-pair problems:** inspected project ledgers describe reductions, prerequisite theorems, or conditional interfaces rather than unconditional Lean proofs of these open statements.
- **Confocal-envelope, Bernstein-inversion, and real-corona families:** some may be genuinely new and formalized, but this audit found no independent external conjecture matching them closely enough to count.

## Verification limits

No build was run, as requested. Evidence used here consists of source-level theorem inspection, existing project proof/audit cards, absence of prohibited placeholders in the inspected core files, and previously generated `.olean` artifacts whose timestamps postdate the corresponding source files. Those artifacts improve confidence but are not a substitute for a fresh reproducible build.

The literature search used exact theorem terminology, cited-paper follow-up searches, author/topic searches, arXiv, publisher pages, and DOI records. Failure to find a paper is not a proof that none exists. Before making a public priority claim, obtain an independent specialist literature review and a clean build/audit in a controlled release snapshot.

## Bottom line

The multiple elliptic gamma dichotomy is the corpus's clearest non-RH candidate for a first publication: it appears to answer a precise 2021 open problem, gives an exact classification rather than an isolated case, and is fully represented at the Lean theorem surface. The finite mixed-state recurrence theorem is a second defensible contribution to an explicit 2026 open direction. The Painleve--Xi result is a plausible conjecture refutation, but should be labeled hybrid until the Painleve-to-differential-algebraic reduction is formalized.
