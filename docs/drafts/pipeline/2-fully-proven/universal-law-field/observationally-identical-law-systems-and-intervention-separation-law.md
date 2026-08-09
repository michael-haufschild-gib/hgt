# Observationally identical law systems and intervention separation law

- **ID:** ULF-CFL-1
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** universal-law-field speculative tournament
- **Statement:** Complete passive endpoint data can fail to determine law direction even when one elementary intervention separates the systems exactly.

## Goal

Test whether proof routes should sometimes be interpreted as interventions on a latent source law
rather than as gauges or passive observers.

## Gates

- [x] 0 → 1: explicit finite counterfactual systems
- [x] 1 → 2: exact observational and intervention computation
- [ ] 2 → 3: no Lean formalization
- [ ] 3 → 4: no publication/priority claim

## Theorem

Let (U\) be a fair bit. Consider two deterministic structural law systems on observed bits
((X,Y)):

\[
\mathsf A:\quad X:=U,\quad Y:=X,
\tag{1}
\]

\[
\mathsf B:\quad Y:=U,\quad X:=Y.
\tag{2}
\]

Then:

1. The complete passive joint law is identical in both systems:
   \[
   \Pr(X=0,Y=0)=\Pr(X=1,Y=1)=\frac12,
   \qquad
   \Pr(X\ne Y)=0.
   \tag{3}
   \]
   Consequently every passive statistic (f(X,Y)), every moment, every positive expectation, and
   every event probability agrees.
2. Under the intervention (\operatorname{do}(X=0)), the systems separate:
   \[
   \mathsf A:\quad \Pr(Y=0\mid\operatorname{do}(X=0))=1,
   \tag{4}
   \]
   \[
   \mathsf B:\quad \Pr(Y=0\mid\operatorname{do}(X=0))=\frac12.
   \tag{5}
   \]
3. Symmetrically, (\operatorname{do}(Y=0)) separates them in the opposite direction.

Therefore no reconstruction rule from the entire passive endpoint law can determine the directed
constitutive mechanism. Intervention data are strictly stronger.

### Proof

In either system (X=Y=U) before intervention, which proves (3) and equality of all passive
statistics. In (\mathsf A), replacing the structural equation for (X) by (X:=0) forces
(Y:=X=0). In (\mathsf B), the intervention replaces only (X:=Y); the equation (Y:=U)
remains, so (Y) is still fair. This proves (4)--(5). The (Y)-intervention is symmetric. ∎

## Exact consequence for a law field

Calling all routes "gauges" is too restrictive. If two route operations replace different source
relations, their comparison is counterfactual. A universal theory that retains only endpoint objects,
their full positive state, or even their full passive joint law can still miss direction of law
production.

The primitive required by this theorem is a marked intervention calculus:

- structural assignments or generative arrows;
- legal replacements of individual assignments;
- observer functors after intervention;
- compatibility for serial and parallel interventions.

## Hostile scope

This is the elementary causal-identifiability counterexample, not new causal inference. It supports a
field reinterpretation only if multiple proof routes can be constructed as interventions on one literal
source before their target endpoints are known. Relabeling arbitrary route differences as
interventions is theatre.

## Log

- 2026-08-09 — exact passive-equivalence/intervention-separation theorem recorded; no Lean.
