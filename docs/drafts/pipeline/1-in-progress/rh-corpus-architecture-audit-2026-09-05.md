# Corpus-wide search for an arithmetic proof architecture

- **ID:** RH-CORPUS-20260905
- **Stage:** 1-in-progress
- **Type:** CANDIDATE SEARCH; no RH implication or novelty claim established
- **Source:** `scripts/formal_tools.py research`; current frontier map; audited Lean declarations; primary literature.
- **Statement:** Find a source-derived operation whose exact arithmetic constraints can distinguish horizontal displacement without importing an RH-equivalent estimate or selecting the desired zeros in its definition.

**Current result: NO QUALIFYING ARCHITECTURE FOUND.** The theta/Volterra/unequal-time branch below was rejected by the user as outside the requested scope. Do not continue it or formalize its auxiliary Gaussian-rank statement. No new Lean module was written in this audit.

## Binding research scope

Use `scripts/formal_tools.py research` together with `rg` on definitions and proof bodies. The user explicitly excludes Suzuki, Hedenmalm, Weil positivity (typed “weyl positivity”), Connes, Burnol, Hilbert–Pólya, all spectral approaches, Gamma, and other usual RH routes, including relabelled versions. A new subsidiary object with an old decisive open step does not qualify. The intended output is a new mechanism, not more retrieval, generic obstruction lemmas, or a familiar criterion in new vocabulary. Early ideas need not yet imply RH, but must be explicit enough to conjecture about and falsify.

These exclusions are user instructions, not mathematical impossibility theorems. They belong here, not in the factual `STATUS.md` ledger.

## Goal and scope

Search the full indexed corpus, including the non-RH theorem areas. Ranked search is discovery, not a proof-body audit of every declaration. Record coverage and inspect the exact hypotheses and proofs of candidates before using them. Literature searches can establish ancestry and collisions, but cannot certify absence from all literature.

## Work plan

1. Inventory corpus and existing frontier; search independent mathematical mechanisms across all areas.
2. Select a concrete source operation; write falsifiable conjectures and test both its arithmetic realization and its claimed consequence.
3. Prove, reject, or pivot. Distinguish established identities from proposed RH bridges. Extract the strongest meaningful positive survivor of any retired realization.
4. Formalize only closed proved statements, using scratch checks, foreground single-process Lean runs, narrow leaf builds, umbrella wiring, and axiom/lint audits.
5. Record route-independent consequences in `universal-law-field/STATUS.md` only if new and supported. Keep technical attempts here.

## Current evidence

- Existing source/receiver boundaries forbid treating an RH equivalence as a producer.
- The earlier normalized rank-one theta sewing realization has zero tangent already at first order; it supplies no selective nonlinear obstruction. The arithmetic formal-deformation obstruction still lacks an independently constructed Xi-linked source satisfying its bounds.
- Existing working-tree changes predate this audit and are preserved.

## Open obligations

No RH-producing candidate has passed the gates. The working pivot below is a source-construction question, not an asserted RH criterion.

## Conjecture / failure / pivot

**C1: ordinary products of theta resonant responses retain the same source. Rejected.** The corpus equation is `u_alpha' = -i alpha u_alpha - i k`. Consequently `(u_alpha u_beta)' = -i(alpha+beta)u_alpha u_beta - i k(u_alpha+u_beta)`. The forcing changes; causal/anti-causal agreement of the factors does not make `alpha+beta` another zero of the original transform. The positive survivor is the exact response-dependent forcing law. This is an immediate product-rule consequence of `HedenmalmThetaEigenODE`, not a novel mathematical principle or a retired general nonlinear route.

**C2: the ordinary Volterra product algebra itself is radically new. Rejected by literature.** Guo–Gustavson–Li, *An algebraic study of Volterra integral equations and their operator linearity*, Journal of Algebra 595 (2022), [arXiv:2008.06756v2](https://arxiv.org/abs/2008.06756), treats matching twisted Rota–Baxter identities and reduction to iterated integrals for separable kernels. Hedenmalm's actual source spectral architecture is itself published: [arXiv:2606.17494](https://arxiv.org/abs/2606.17494). Neither is new merely because combined.

**C3: the equal-time rank-one sewing algebra also closes unequal-time histories. Abandoned by the research-scope correction.** The elementary exponent observation was

`t(i+j+2a)^2 + u(i-j)^2 = (t+u)(i^2+j^2) + 2(t-u)ij + 4ta(i+j) + 4ta^2`.

Here `a=0` and `a=1/2` are the two parity sectors; `t,u` absorb pi. A Gaussian/Vandermonde minor classification was considered. Only mathlib API names were checked in `/tmp/hgt-rh-audit-20260905/Api.lean`; no rank theorem was written or checked. This would remain auxiliary standard mathematics, not the requested architecture.

## Rejected proposal: ordered unequal-time lattice responses

Retain independent integration times, parity sectors, and integer labels in products of the *fixed* theta source's causal/anti-causal responses. Apply lattice reindexing before integrating or projecting to a single source channel. The new research object would be the resulting hierarchy of ordered, coupled-lattice response integrals. It differs from changing normalized rank-one theta amplitudes, and from assuming products stay in the original one-source equation.

The proposed residual operation was never constructed. Its ancestry and intended starting point violate the user's scope. Do not treat the absence of a literal search match for the combined description as novelty.

## Discrete and exact-algebra audit after the correction

| Seed | Exact evidence inspected | Assessment |
|---|---|---|
| Word rewriting | `HTGeometry/ConstitutiveCriticalCompletionMechanics.lean`, lines 1–215: each rule decreases the number of `a` letters; each finite rulebook has an explicit nonjoining critical pair; the next joining rule is already an old semantic equality. | Separates execution from equivalence. No literal integer-arithmetic construction or RH consequence. Repeating this toy is not a new architecture. |
| Sequential repair | `HTGeometry/ConstitutiveSequentialRepairHeredity.lean`, lines 1–210: Arens topology has two sequential-closure layers while ordinary closure is stationary. | Known topological mechanism. No arithmetic realization selected. |
| Primitive execution | `HTGeometry/ConstitutivePrimitiveExecutionGenesis.lean`, lines 1–200: positive locally admitted laws decompose by induction on degree; bounded grammar completeness is equivalent to a bound on indecomposable degrees. | Exact abstract resource theorem. The required arithmetic family and its primitive structure were not constructed. |
| Carry identities | `research` plus `rg` in `ConstraintFrameRelativity/WittCarryBoolean.lean`, `ConstitutiveExchangeCentralPromotion.lean`, and `ConstitutiveCoefficientLiftTransgression.lean`. The inspected Boolean carry is intersection; the integer identity separates a squared gcd factor. | Neither Boolean addition nor a central carry can silently stand for the full addition/multiplication of integers. No qualifying synthesis produced. |
| Arithmetic differential curvature | Exact-phrase corpus queries for Fermat quotient, p-derivation, delta ring, Wieferich, and arithmetic curvature, followed by `rg` of candidate source files. | Search misses did not establish novelty. Barrett–Buium already construct curvature from Fermat quotient operations: [arXiv:1512.02525](https://arxiv.org/abs/1512.02525). Rejected as a new field claim. |
| Second-kind arithmetic cohomology | Primary abstract of Efimov, [arXiv:1506.00257](https://arxiv.org/abs/1506.00257). | This is published mathematics. Its displayed all-localization nontriviality condition is equivalent to infinitude of Wieferich primes, so assuming that condition would introduce another unresolved arithmetic question. No such premise adopted. |

## Coverage and verification

- Index snapshot: 32,233 files, 392,125 declarations, 3,855 gap markers. All-index search scope is not a proof-body audit of all declarations.
- 98 saved numbered corpus queries. Query wording and hit counts are in the adjacent search manifest. Search terms are OR-ed; ranked results can omit relevant low-ranked declarations. Exact `rg` searches supplied definition and proof-body checks. No absence or completeness theorem follows from search misses.
- The only Lean invocation created by this audit checked mathlib API names in the scratch file above and exited 0. No theorem implementation, leaf build, umbrella edit, full build, or computational proof was performed. No owned Lean process remains running.
- No numerical experiment was justified; Runpod was not used. Retrieval/metadata processing is not numerical mathematical evidence.
- No new significant mathematical fact was established for `universal-law-field/STATUS.md`. Its existing facts and other working-tree changes were preserved.
- The goal remains active. Novel architecture, decisive conjecture, paper proof, and unconditional RH formalization remain unachieved. None of the rejected branches is an approved continuation.
