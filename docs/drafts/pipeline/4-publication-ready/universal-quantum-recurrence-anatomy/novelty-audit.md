# Novelty audit

Manuscript programme: **universal quantum recurrence**  
Cutoff: 1 August 2026

## Priority gate

No theorem construction is allowed merely because a convenient package of
known ingredients has not appeared under one title.  Each atomic mathematical
claim must pass this sequence before it receives proof effort:

1. state the exact theorem, model class, quantifiers and physical consequence;
2. identify the nearest published theorem for every component;
3. record exact overlap, not only verbal similarity;
4. identify a primary source that explicitly leaves the residue open, or give
   comparably strong evidence that the residue is unresolved;
5. test whether the residue remains important after all known pieces are
   removed;
6. only then design the paper proof and formal proof.

Search absence is not novelty.  Joining known facts is not novelty unless the
joint statement creates a non-obvious consequence that is itself new and
important.

## Claims killed by literature

| Candidate claim | Nearest prior result | Verdict |
|---|---|---|
| Rational independence gives full-torus time averaging and exact all-order spectral-form-factor moments | Campos Venuti, Odavić and Hamma, [arXiv:2505.05199](https://arxiv.org/abs/2505.05199), especially Theorem 4 and Appendices A, D and E | **KILLED.** Their paper states the torus averaging, proves all-order nondegeneracy iff rational independence, and gives exact arbitrary moments. |
| The plateau floor is attained exactly by an independent spectrum | Same source; also Riddell and Bertini, [Phys. Rev. E 110, 064101 (2024)](https://arxiv.org/abs/2404.12100) for all higher moments in rationally independent free fermions | **KILLED.** Repackaging the moment count as a plateau--Haar equivalence is not a discovery. |
| Absolutely continuous random-matrix spectra are rationally independent almost surely | Campos Venuti, Odavić and Hamma, Appendix A | **KILLED.** A finite-`N` matrix-model application supplies no new theorem. |
| Generic geometrically local Hamiltonians have nondegenerate gaps | Huang, [arXiv:2104.02053](https://arxiv.org/abs/2104.02053) | **KILLED outside the translation-invariant restriction.** Huang proves the condition almost everywhere in geometrically local Hamiltonian space. |
| Rationally independent local free-fermion spectra and their recurrence/SFF consequences | Riddell and Bertini, [arXiv:2404.12100](https://arxiv.org/abs/2404.12100) | **KILLED as a headline.** Explicit local models and all higher SFF moments are already published. |
| Generic spectra imply concentration and doubly-exponential average recurrence scales | Riddell, Pagliaroli and Alhambra, [arXiv:2206.07541](https://arxiv.org/abs/2206.07541) | **KILLED.** Their all-order generic-spectrum condition, concentration bounds and average-recurrence consequences predate this programme. A local theorem can receive credit only for discharging their spectral premise in a genuinely physical interacting family. |
| Dimension--resolution scaling of first quantum recurrence for unrestricted or random Hamiltonians | Kotowski and Oszmaniec, [arXiv:2601.10409v2](https://arxiv.org/abs/2601.10409) | **KILLED outside the local-interacting restriction.** They prove deterministic upper bounds for all finite Hamiltonians, matching random-Hamiltonian lower bounds, effective-support refinements and the failure of inverse purity to control first recurrence. |
| Continuous-time uniform system-recurrence upper exponent $d-2$ for $d$ distinct energies | Gupta and Short, [Phys. Rev. A 114, 012208 (2026)](https://arxiv.org/abs/2604.14995) | **KILLED as a universal exponent or upper-bound claim.** They prove simultaneous recurrence of every state by time $O(\varepsilon^{-(d-2)})$, with improved constants, for every finite Hamiltonian. A new theorem must prove physical-family sharpness or a structural law for the effective spectral dimension. |
| A late-time plateau requires discrete/nonperturbative spectral input | Saad, Shenker and Stanford, [arXiv:1806.06840](https://arxiv.org/abs/1806.06840) and [arXiv:1903.11115](https://arxiv.org/abs/1903.11115), with subsequent nonperturbative saddle work | **KILLED as a black-hole discovery.** Ramp, plateau, discreteness and nonperturbative completion are established themes. |
| Arbitrarily weak perturbations can remain close on bounded times yet alter exact infinite-time recurrence | Duhamel stability plus elementary arithmetic detuning | **REJECTED FOR SIGNIFICANCE.** Even if the exact coupling-ray formulation is absent, a hostile editor can fairly read the conclusion as a dressed butterfly-effect/discontinuous-limit observation. |
| `Rel(E+gW)=Rel(E)\cap Rel(W)` outside a countable coupling set | Elementary one-variable affine detuning; no exact prior formulation located | **NOT ENOUGH.** Possible technical novelty does not answer a major scientific question and cannot support a Nature claim. |
| Generic all-order nonresonance in translation- and reflection-invariant rings | Dabelow, Eidecker-Dunkel and Reimann, [Phys. Rev. B 113, 094311 (2026)](https://arxiv.org/abs/2603.23058) | **IMPOSSIBLE GLOBALLY.** They prove that translation plus reflection forces degeneracy for the overwhelming majority of levels. Any live family must break reflection explicitly. |

The formal plateau module and protected-relation modules remain reusable proof
infrastructure.  They receive no novelty credit.

## Bridge target: interaction-graph first-recurrence law

Gupta and Short already prove the continuous-time uniform system-recurrence
upper exponent $d-2$ for every finite Hamiltonian with $d$ distinct
energies. Kotowski and Oszmaniec prove generic sharpness for random diagonal
Hamiltonians and explicitly leave tight recurrence bounds for physical
dynamics generated by local non-commuting Hamiltonians open. The exponent
alone is therefore known; the live residue is physical-family sharpness and
the structural dimension selected by locality.

Let $G$ be any finite interaction graph, with local dimensions $q_v\geq2$.
For each connected component $C$, put
\[
D_C=\prod_{v\in C}q_v,
\qquad
r_G=\sum_{C\in\pi_0(G)}(D_C-1).
\]
The strongest current bridge candidate is:

> For Lebesgue-almost every Hamiltonian with arbitrary one-site terms and
> arbitrary two-site terms on the edges of $G$, the first non-trivial
> continuous time at which every state returns within trace distance
> $\varepsilon$ satisfies
> \[
> \lim_{\varepsilon\downarrow0}
> \frac{\log t_{\rm rec}(\varepsilon)}
>      {\log(1/\varepsilon)}
> =r_G-1.
> \]

Thus a connected graph has exponent $\prod_vq_v-2$. Joining components
$A$ and $B$ changes the exponent by $(D_A-1)(D_B-1)$.

The proposed bridge content is not that recurrence is slow. It is that
interaction connectivity selects the exact Diophantine dimension of quantum
return, and one continuous time direction removes exactly one dimension from
the corresponding first-hit exponent.

### Exact overlap matrix for graph-local first recurrence

| Source | Proven there | Missing relative to candidate |
|---|---|---|
| Gupta--Short 2026 | uniform recurrence of every state by time $O(\varepsilon^{-(d-2)})$ for every finite Hamiltonian | matching lower exponent; local-interaction sharpness; graph-selected effective dimension |
| Kotowski--Oszmaniec 2026 | deterministic individual-state upper bounds; matching random-diagonal lower exponent; effective-support refinements | arbitrary geometrically local non-commuting families; connected/disconnected interaction law |
| Riddell--Pagliaroli--Alhambra 2022/2023 | all-order generic-spectrum concentration and average recurrence bounds | first return; local spectral premise; interaction-graph formula |
| Huang 2021 | nondegenerate gaps almost everywhere in nearest-neighbour local chains | all balanced relations; arbitrary graphs; Diophantine extremality; sharp first return |
| Kleinbock--Margulis 1998 | extremality of analytic nondegenerate manifolds | construction and nondegeneracy of local many-body spectral manifolds; quantum and graph interpretation |

### Unclosed obligations

1. Audit arbitrary-graph spectral induction, especially qubit leaf and
   disconnected-component steps.
2. Prove metric nondegeneracy on the component spectral quotient rather than
   infer it from rational independence.
3. Replace the current product of labelled derivative minors by a symmetric
   sum-of-squares certificate and audit the algebraic clearing step.
4. Prove local equivalence between projective operator recurrence and
   Gupta--Short trace-distance system recurrence after exit.
5. Formalize Kleinbock--Margulis extremality or an unconditional replacement.
6. Do not infer fixed-accuracy system-size scaling from an
   accuracy-asymptotic exponent with uncontrolled size-dependent constants.
7. Give black-hole relevance no claim status without a gravitational
   spectral model.

Current status: **BRIDGE; NOVELTY UNVERIFIED; NATURE-LEVEL SIGNIFICANCE FAILS
AFTER SUBTRACTING KNOWN DIOPHANTINE AND RECURRENCE RESULTS; NO PROOF OR LEAN
BUILD AUTHORIZED.** Even a complete proof would presently answer the explicit
local-noncommuting open problem only at specialist level. It cannot be promoted
as the universal-law headline unless a separate, literature-first conjecture
forces it as one shadow and also produces a new major physical consequence.

## Superseded chain-only target

Kotowski and Oszmaniec do not merely supply nearby prior art.  In their
conclusion they explicitly leave open tight recurrence bounds for physical
dynamics generated by local non-commuting Hamiltonians.  This is the correct
external question against which the corpus must be tested.

The strongest current candidate is:

> Fix $n\geq2$ and local dimension $q\geq2$.  For Lebesgue-almost every
> traceless Hamiltonian on the open chain with arbitrary one-site and
> nearest-neighbour two-site terms, a pure state with full spectral support
> has trace-distance first-recurrence exponent $q^n-2$:
> \[
> \lim_{\varepsilon\downarrow0}
> \frac{\log t_{\rm rec}(\varepsilon)}{\log(1/\varepsilon)}
> =q^n-2.
> \]
> More generally, the proposed support-resolved law replaces $q^n$ by the
> number of occupied energy levels.

This would transfer the sharp random-spectrum exponent to a bounded-degree,
finite-range, time-independent interacting family and identify exact spectral
support, rather than Hilbert-space dimension or inverse purity alone, as the
generic recurrence exponent.  It would answer the explicit 2026 local
non-commuting open problem rather than inventing a niche after the proof.

### Exact overlap matrix for first recurrence

| Source | Proven there | Missing relative to candidate |
|---|---|---|
| Kotowski--Oszmaniec 2026 | deterministic first-recurrence upper bound for every finite Hamiltonian; matching exponent for random diagonal spectra; effective-support upper bound | matching almost-sure lower exponent in a geometrically local non-commuting family |
| Riddell--Pagliaroli--Alhambra 2022/2023 | all-order generic-spectrum concentration and average recurrence bounds | first-return exponent; proof that an interacting local family supplies the spectral arithmetic |
| Huang 2021 | nondegenerate gaps almost everywhere in nearest-neighbour local chains | all balanced relations; Diophantine extremality; sharp first return |
| Kleinbock--Margulis 1998 | extremality of analytic nondegenerate manifolds | construction and nondegeneracy of the local many-body spectral manifold; quantum recurrence interpretation |

### Why this is not yet a manuscript claim

The corpus has a paper proof in
`local-chain-metric-recurrence-exponents.md`, built on the paper-proved
nearest-neighbour projective spectral-maximality theorem.  It is not yet
eligible for the manuscript:

1. the nearest-neighbour spectral theorem has not passed final specialist and
   external exact-object audits;
2. the support-resolved strengthening has not been audited branch by branch;
3. the metric step imports Kleinbock--Margulis extremality, which is not yet
   proved in Lean;
4. no claim of a fixed-accuracy double-exponential system-size law follows
   from an accuracy-asymptotic exponent with uncontrolled size-dependent
   constants;
5. solving the mathematical open problem would still require a separate
   Nature-level significance test.  Black-hole relevance cannot be inferred
   without a gravitational model.

### Kill tests for first-recurrence target

This target is killed or narrowed immediately if:

1. prior work already proves the same almost-everywhere exponent for finite-
   range non-commuting chains;
2. the local spectral map fails the nondegeneracy required by metric
   extremality;
3. the proposed first-return definition does not match trace-distance state
   recurrence after the exit time;
4. the support-resolved exponent fails for any occupied spectral subset;
5. the metric theorem cannot be formalized unconditionally or replaced by a
   formally provable argument.

Current status:

`[EXTERNALLY ANCHORED OPEN QUESTION; EXACT THEOREM PRIORITY STILL UNDER AUDIT; NO LEAN BUILD AUTHORIZED]`

## Secondary target: translation-invariant all-order resonance removal

### All-order interaction removal of spectral resonances

Candidate theorem, deliberately stronger than the open two-gap question:

> For every finite ring size, within one fixed finite-range, chiral
> translation-invariant interacting qubit Hamiltonian family, the parameters
> whose distinct energy levels satisfy any non-trivial balanced integer
> relation form a Lebesgue-null and meagre set.  Equivalently, a generic member
> has maximal projective rational rank, hence satisfies every finite-order
> no-resonance condition simultaneously.

This is not yet a claim of the manuscript.  It is a research target.

### Why this target is externally motivated

Pilatowsky-Cameo and Choi, [Nature Communications 17, 75
(2026)](https://doi.org/10.1038/s41467-025-66777-7), prove high-temperature
thermalization for translation-invariant local qubit systems subject to
nondegenerate energy gaps.  In their Discussion they explicitly state that
genericity of this gap condition for translation-invariant Hamiltonians at
every system size remains conjectural and unproved.

Riddell and Bertini explicitly identify the interplay between rational
independence and interacting perturbations as a future problem.  Their theorem
constructs rationally independent *one-particle* spectra for free fermions;
their many-body spectrum necessarily retains exponentially many additive
relations.

The candidate would therefore do more than restate the known generic-gap
theorem:

1. preserve translation invariance and finite-range locality;
2. break reflection by a fixed chiral local term, as the 2026 degeneracy
   obstruction requires;
3. cover interacting many-body spectra rather than free one-particle spectra;
4. prove all balanced integer relations absent generically, not only repeated
   two-level gaps;
5. imply every finite-order no-resonance condition and maximal projective
   recurrence geometry at once.

### Nearest-theorem matrix

| Source | Proven there | Missing relative to candidate |
|---|---|---|
| Huang 2021 | nondegenerate gaps almost everywhere for geometrically local Hamiltonians | translation-invariant subspace; all balanced relations |
| Pilatowsky-Cameo--Choi 2026 | thermalization assuming nondegenerate gaps; explicit statement that translation-invariant genericity is open for every size | proof of genericity; all orders |
| Riddell--Bertini 2024 | local free-fermion construction with rationally independent one-particle energies; higher SFF moments | interacting many-body spectrum; generic translation-invariant family; removal of many-body relations |
| Riddell--Pagliaroli 2024 | statistics and consequences of fixed-order no-resonance conditions in chaotic models | theorem proving generic all-order no-resonance in a local interacting family |
| Campos Venuti--Odavić--Hamma 2026 | consequences of independent spectra, exact SFF moments, numerical tests in non-integrable XXZ/SYK models | proof that physical translation-invariant interacting families have independent spectra |
| Dabelow--Eidecker-Dunkel--Reimann 2026 | translation plus reflection forces extensive energy degeneracy | reflection-breaking chiral family; generic all-order result after obstruction is removed |

## Kill tests for live candidate

The lane is killed immediately if any of the following occurs:

1. a prior theorem proves generic nondegenerate gaps for the same
   translation-invariant local family for every system size;
2. a prior theorem proves generic all-order balanced rational independence in
   any comparably physical translation-invariant interacting family;
3. translation symmetry alone, even after explicit reflection breaking, forces
   an unavoidable balanced relation at some ring size;
4. the only witness uses interaction range, local dimension or parameter count
   growing with system size;
5. the proof reduces to unrestricted random-matrix absolute continuity and
   therefore does not address locality plus translation invariance;
6. the theorem cannot be connected to a new unconditional recurrence or
   thermalization consequence without importing an unformalized physical
   assumption.

## Current verdict

`[NO PRIMARY CONJECTURE IS PRIORITY-CLEARED; GRAPH FIRST RECURRENCE IS A BRIDGE; NO THEOREM BUILD AUTHORIZED]`

Required before any new conjecture is frozen:

- citation chase through papers citing Huang 2021, Riddell--Bertini 2024 and
  Pilatowsky-Cameo--Choi 2026, plus the June 2026 Kotowski--Oszmaniec revision;
- exact comparison of state, projective-unitary and reporter recurrence metrics;
- exact-object search for local non-commuting first-recurrence exponents;
- model-level feasibility analysis for fixed-range translation-invariant qubit
  rings at every size;
- exact statement deciding whether symmetries are resolved sector-by-sector or
  globally;
- hostile significance test after reducing every claim to its genuinely new
  residue;
- an external theorem-and-open-question map completed before proof design,
  including citation ancestry and descendancy through the August 2026 cutoff;
- one ontological reversal, three independent shadow maps, and one risky
  physical consequence unavailable from the parent theories separately.
