# External formalization handoff: remaining classical bridge

## Scope

The project-local tail geometry is already present.  Do not rebuild the finite-range recurring-
pattern theorem, the abstract shift--jet tail theorem, the projective two-orientation
classification, the positivity fibre laws, or the reflection-folding laws.  The remaining task is
to connect that theorem surface to the classical Dirichlet-series machinery and close the exact
analytic capstone used by the manuscript.

The live abstract boundary is

```lean
FactorClockFiberIndependent factor clock m
```

in `formal/GaloisForLFunctions/HTGeometry/FiniteRangeProjectiveTail.lean`.  A repository search on
2026-07-14 found no concrete theorem instantiating this predicate for prime powers and logarithmic
clocks, and no implementation of the Shapiro--Sparer/Pong Jacobian transfer.

## Task 1: prime exponential--polynomial fibre rigidity

Build a theorem that discharges `FactorClockFiberIndependent` for the actual prime-Dirichlet
columns

```text
factor(a,p) = exp(-alpha(a) * log p),
clock(p)    = log p,
```

where the finite shifts `alpha(a)` have pairwise distinct real parts.  The theorem must work on
every infinite subset of the primes and at every finite jet order.

The proof should expose the classical dominance argument cleanly:

1. an infinite set of primes is unbounded;
2. after ordering shifts by real part and dividing by the least-decaying exponential, all other
   shift blocks decay exponentially relative to every polynomial in `log p`;
3. the surviving polynomial block vanishes on an unbounded set and is therefore zero;
4. iterate over the finite shift set.

If arbitrary complex shifts make the first implementation disproportionately expensive, first
land the nonnegative-integer-shift theorem used by the canonical palette, but do not present that
as completion of the manuscript theorem.  Completion requires pairwise distinct real parts.

Expected endpoint: a theorem directly consumable by
`completeShiftJetTailIndependent_iff_of_finiteRange`, with no new rigidity hypothesis left at the
call site.

## Task 2: Shapiro--Sparer arithmetic-function Jacobian theorem

Formalize the classical algebraic-independence transfer at exactly the strength needed here.
Use arithmetic functions with Dirichlet convolution, basic prime derivations, and the logarithmic
derivation.  The required statement is:

> if a finite family of coefficient columns admits a square packet of primes with invertible
> evaluation matrix, then the corresponding arithmetic functions are algebraically independent
> over the common kernel of those prime derivations.

The existing theorem

```lean
TailCoefficientIndependent.exists_fullRank_evaluation_packet
```

already supplies the finite invertible packet.  Reuse it.  The new work is the Jacobian criterion,
the action of the basic prime derivations on the selected columns, and the exact base-ring/kernel
bookkeeping.  Do not replace this with an assumption named after Shapiro--Sparer or Pong: the final
capstone must not retain that assumption.

Acceptance criteria:

- the theorem handles an arbitrary finite source--shift--jet rectangle;
- coefficients supported on finitely many primes are annihilated after choosing the packet away
  from their joint support;
- algebraic independence is obtained over the fraction field of the finite-prime coefficient
  algebra, not only over `C`;
- all denominator clearing is explicit.

## Task 3: analytic Dirichlet-series transfer and capstone

Connect the arithmetic-function result to actual analytic prime Dirichlet series on a common right
half-plane.  The package must include, or reuse with exact citations in code, the following facts:

1. injectivity/uniqueness of a convergent Dirichlet series on a right half-plane;
2. multiplication by `n^(-a)` corresponds to translation by `a`;
3. the logarithmic coefficient derivation corresponds to `-d/ds`, including all iterates used by
   the jet rectangle;
4. polynomial coefficients in `s` cannot create a spurious relation (polynomial-weighted
   Dirichlet uniqueness);
5. finite-prime coefficients and their denominators are removed before selecting the Jacobian
   packet.

Then state the unconditional analytic capstone matching the manuscript:

> for every finite bounded prime-coefficient family and every finite shift set with distinct real
> parts, differential algebraic independence of the complete shifted carriers over the
> finite-prime Dirichlet field is equivalent to independence of every operator-tail rectangle;
> for finite joint coefficient range this is equivalent to linear independence of the coefficient
> tail classes.

The Boolean corollary must recover eventual equality or eventual opposition as the exact
two-source field-equality boundary.

## Required verification

Before reporting completion:

1. import the final capstone in a scratch file and run `#print axioms` on the three bridge theorems
   and the capstone;
2. show that no project-defined hypothesis representing exponential rigidity, Jacobian transfer,
   Dirichlet uniqueness, or analytic transfer remains in the capstone signature;
3. run narrow builds for every new module and its import closure;
4. run `scripts/formal_tools.py lint` and report any failure as either introduced or pre-existing;
5. provide the exact declaration names and file paths, not only a prose status update.

## Not part of this assignment

- the old Szegő/Nevanlinna compact-patch route;
- parametric transversality and Whitney stratification;
- the Herglotz residue cone, tail-cone fibre, signed-value defect, Stanley--Reisner localization,
  or reflection-folding additions;
- novelty claims.  These are handled in the mathematical and literature audit, not by the
  classical bridge formalization.

