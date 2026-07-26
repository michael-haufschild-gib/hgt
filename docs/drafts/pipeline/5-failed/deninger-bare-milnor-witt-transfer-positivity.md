# Bare Milnor--Witt transfer positivity

- **ID:** `deninger-bare-milnor-witt-transfer-positivity`
- **Stage:** 5-failed
- **Type:** NO-GO WITH POSITIVE SURVIVOR
- **Parent:** `deninger-milnor-witt-hodge-realization`
- **Source:** Déglise, *Notes on Milnor--Witt K-theory*, §2.2.18; Deninger program

## Failed claim

The canonical Milnor--Witt transfer of a degree-\(p\) power correspondence is itself a
positive-definite real quadratic form of rank \(p\), and therefore directly supplies Deninger's
positive Hodge metric.

## Exact obstruction

The quadratic multiplicity of a positive integer \(n\) is
\[
 n_\epsilon=\sum_{i=0}^{n-1}\langle-1\rangle^i
 =
 \begin{cases}
   m(\langle1\rangle+\langle-1\rangle),&n=2m,\\
   m(\langle1\rangle+\langle-1\rangle)+\langle1\rangle,&n=2m+1.
 \end{cases}
\]
Over \(\mathbb R\), its rank is \(n\), while its signature is \(0\) for even \(n\) and \(1\)
for odd \(n\).  Hence for every \(n>1\), \(n_\epsilon\) has a nonzero negative index and is not
positive definite.  In particular this applies to every prime degree.

This is not a defect of a chosen presentation.  Quadratic multiplicity is the canonical
Milnor--Witt refinement of ordinary degree, and the displayed real inertia is invariant under
isometry.

## Positive survivor

`[POSITIVE SURVIVOR] [DAC_POLARIZATION_SEPARATION]`

Milnor--Witt or hermitian motivic data can still supply:

1. the Steinberg relation at chain/cohomology level;
2. dualizing-line twists and quadratic finite transfers;
3. an indefinite, nondegenerate source Poincare pairing;
4. rank \(p\), which is the correct unpolarized degree entering half-density normalization.

It cannot supply positivity without an additional polarization.  The archimedean Gamma boundary
must construct a compatible complex/quaternionic operator \(J_\infty\) such that
\[
 J_\infty^2=-1,\qquad
 (x,y)_H=\operatorname{tr}(x\smile J_\infty y)>0
\]
on nonzero odd classes.  Centered power transfers must then be proved unitary for this metric.
This separates algebraic Poincare duality from analytic Hodge positivity and prevents the latter
from being smuggled in as a property of a Grothendieck--Witt class.

## Closure status

- Negative statement: dependency-closed paper proof above.
- Positive survivor: exact statement extracted; active on
  `deninger-milnor-witt-hodge-realization`.
- Lean: pending a faithful real quadratic-form inertia formalization; no toy Grothendieck--Witt
  encoding will be counted as formalization.
- Re-attempt condition: only with an independently constructed archimedean polarization.

## References

- Frédéric Déglise, *Notes on Milnor--Witt K-theory* (2023), §2.2.18:
  https://deglise.perso.math.cnrs.fr/docs/2023/KMW.pdf

## Log

- 2026-07-26 — bare-transfer positivity retired; polarization separation retained.
