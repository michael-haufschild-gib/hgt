# Arithmetic formation--recurrence descent fusion law

Status: fully proved and formalized in Lean 4.

Lean module:
`GaloisForLFunctions.RHTower.ArithmeticFormationRecurrenceDescentFusion`.

Axiom audit: `propext`, `Classical.choice`, `Quot.sound` only.

## Higher-law interpretation

Singular completion and compact recurrence expose the same obstruction in opposite forms.  A
completed Xi boundary is born beyond finite arithmetic formation exactly when its recovered real
prime-history character cannot descend continuously through the faithful compact prime-circle
completion.  Thus completion birth is not merely analogous to open lifted history: it is its exact
arithmetic complement.

## Corpus inputs

Fresh `scripts/formal_tools.py research` searches locate:

- `deningerGammaSixCofinalXiGreenVerticalBoundary_mem_formationCompletionBoundary_iff`;
- `thetaXiPrimeModularCompactRecurrenceDescent_iff`;
- `xiArithmeticFormationCompletionBoundaryFree_iff_riemannHypothesis`;
- `forall_thetaXiPrimeModularCompactRecurrenceDescent_iff_riemannHypothesis`.

## Theorem

For every multiplicity-labelled Xi zero copy `q`, the following are equivalent:

1. its completed Meyer--Tate Xi Green boundary belongs to the arithmetic
   formation--completion boundary;
2. its recovered theta-source real prime-modular character fails exact continuous descent through
   the faithful dense compact prime-circle recurrence formation.

Consequently, universal absence of arithmetic completion birth is equivalent to universal compact
recurrence descent.  Both are equivalent to RH.

## Proof

The arithmetic boundary theorem identifies (1) with `Re(q) != 1/2`.  The compact-recurrence theorem
identifies successful descent with `Re(q) = 1/2`; negating it gives (2).  Pointwise equivalence and
the two existing global RH equivalences give the global statement.  No RH premise, critical-line
premise, or additional axiom is used.

## Exact RH use

This theorem does not assert compact descent.  It shows that the remaining producer has two
strictly equivalent source formulations: finite effectivity of the completed Meyer--Tate boundary,
or continuous descent of the recovered real prime-history character through compact recurrence.
Any independent arithmetic theorem proving either formulation for every Xi copy proves RH.
