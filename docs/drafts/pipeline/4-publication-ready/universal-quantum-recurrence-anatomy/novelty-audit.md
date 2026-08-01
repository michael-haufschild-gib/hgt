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
| A late-time plateau requires discrete/nonperturbative spectral input | Saad, Shenker and Stanford, [arXiv:1806.06840](https://arxiv.org/abs/1806.06840) and [arXiv:1903.11115](https://arxiv.org/abs/1903.11115), with subsequent nonperturbative saddle work | **KILLED as a black-hole discovery.** Ramp, plateau, discreteness and nonperturbative completion are established themes. |
| Arbitrarily weak perturbations can remain close on bounded times yet alter exact infinite-time recurrence | Duhamel stability plus elementary arithmetic detuning | **REJECTED FOR SIGNIFICANCE.** Even if the exact coupling-ray formulation is absent, a hostile editor can fairly read the conclusion as a dressed butterfly-effect/discontinuous-limit observation. |
| `Rel(E+gW)=Rel(E)\cap Rel(W)` outside a countable coupling set | Elementary one-variable affine detuning; no exact prior formulation located | **NOT ENOUGH.** Possible technical novelty does not answer a major scientific question and cannot support a Nature claim. |
| Generic all-order nonresonance in translation- and reflection-invariant rings | Dabelow, Eidecker-Dunkel and Reimann, [Phys. Rev. B 113, 094311 (2026)](https://arxiv.org/abs/2603.23058) | **IMPOSSIBLE GLOBALLY.** They prove that translation plus reflection forces degeneracy for the overwhelming majority of levels. Any live family must break reflection explicitly. |

The formal plateau module and protected-relation modules remain reusable proof
infrastructure.  They receive no novelty credit.

## One live candidate

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

`[LIVE OPEN-PROBLEM CANDIDATE; NOT YET PRIORITY-CLEARED; NO THEOREM BUILD AUTHORIZED]`

Required before proof work:

- citation chase through papers citing Huang 2021, Riddell--Bertini 2024 and
  Pilatowsky-Cameo--Choi 2026;
- model-level feasibility analysis for fixed-range translation-invariant qubit
  rings at every size;
- exact statement deciding whether symmetries are resolved sector-by-sector or
  globally;
- hostile significance test after reducing the claim to its genuinely new
  residue.
