# Fully tempered fixed-completion entry rigidity

- **ID:** fully-tempered-fixed-completion-entry-rigidity
- **Stage:** 5-failed
- **Type:** `[RETIRED: REDUCES TO KNOWN OPEN RIGIDITY; CONNECTED-SET FORM OVERSTATED]`
- **Source:** `../2-fully-proven/not_new_scientific_knowledge/11-rh-zero-divisor-geometry/symmetric-shift-entry-temperedness-boundary.md`

## Terminal verdict

This route does not clear the novelty gate.  For paths in a Selberg-class interpretation of the
target, the proposed rigidity is a fixed-archimedean specialization of Sarnak's rigidity
conjecture.  Kaczorowski--Perelli formulate that conjecture as: every continuous one-parameter
family in the Selberg class is a product of continuously shifted fixed primitive functions.  They
prove it assuming Selberg orthonormality and essential countability; Vorhauer--Wirsing prove the
same conditional rigidity independently.

- J. Kaczorowski and A. Perelli, *On the structure of the Selberg class, III: Sarnak's rigidity
  conjecture*, Duke Math. J. **101** (2000), 529--554,
  [doi:10.1215/S0012-7094-00-10137-8](https://doi.org/10.1215/S0012-7094-00-10137-8).
- U. M. A. Vorhauer and E. Wirsing, *On Sarnak's Rigidity Conjecture*, J. Reine Angew. Math.
  **531** (2001), 35--47,
  [doi:10.1515/crll.2001.008](https://doi.org/10.1515/crll.2001.008).

Fixing the complete gamma product removes the shifts allowed by that parent conjecture.  Thus a
proof of the corrected path statement would either be a corollary of Sarnak rigidity or would prove
a special case of that already named open rigidity problem.  Rephrasing it as a prohibition on a
zero entering the critical line does not create a new constraint.

If `normalized finite-order meromorphic Euler product` is intended to describe a class broader than
the Selberg class, the former card does not specify enough uniform analytic axioms to define that
class or to support the normal-family step below.  That reading is under-specified rather than a
second theorem target.

## Exact reduction

Work in the Selberg-class slice with:

```text
degree at most D + unitary polynomial local roots + fixed conductor
+ fixed gamma product + fixed root number + fixed finite pole divisor.
```

Let `t -> F_t` be continuous in the coefficientwise local-factor topology.

### 1. Coefficientwise continuity supplies right-half-plane continuity

Every Dirichlet coefficient `a_t(n)` depends on only finitely many local-factor coefficients, so it
is continuous in `t`.  Full temperedness and the degree bound give the uniform majorant

```text
|a_t(n)| <= d_D(n).
```

Consequently the Dirichlet series converge locally uniformly, uniformly in `t`, on every closed
half-plane `Re s >= 1+epsilon`.  Hence `t -> F_t(s)` is continuous there.

### 2. The fixed functional equation makes the family normal everywhere

Choose a fixed polynomial `P` cancelling the fixed pole divisor.  On `Re s=1+epsilon`, the Euler
majorant gives a bound for `P(s)F_t(s)` independent of `t`.  On `Re s=-epsilon`, the fixed functional
equation transfers that bound from `1-conj(s)`; Stirling's formula for the fixed gamma quotient adds
only a fixed polynomial in `|Im s|`.

After division by one fixed nonvanishing polynomial weight, the finite-order function
`P(s)F_t(s)` is bounded on both edges of the strip.  The Phragmen--Lindelof principle for a strip
therefore gives bounds on compact subsets independent of `t`.  Montel's theorem now applies.  If
`t_n -> t`, every locally convergent subsequence agrees with `F_t` on `Re s>1`, by Step 1, and hence
agrees everywhere by the identity theorem.  Therefore

```text
coefficientwise local-factor continuity
    => locally uniform meromorphic continuity away from the fixed poles.
```

This is exactly the continuity required in Kaczorowski--Perelli's formulation.  The bridge is a
standard normal-family argument, not significant new scientific knowledge.

### 3. A literally fixed gamma product freezes a shifted family

Suppose Sarnak rigidity writes the family as

```text
F_t(s) = product_(j=1)^k F_j(s+i h_j(t)).
```

Under a literal fixed-completion hypothesis, a gamma factor
`Gamma(lambda s+mu)` belonging to `F_j` becomes
`Gamma(lambda s+mu+i lambda h_j(t))`.  Its pole progression has the fixed imaginary level

```text
-Im(mu)/lambda - h_j(t).
```

The pole divisor of the fixed finite gamma product has only finitely many such levels.  A continuous
`h_j` taking values in this finite set is constant.  Permutations or collisions of equal gamma
factors do not alter the conclusion for the product.  In the primitive case the usual Selberg shift
invariant already gives the same conclusion immediately.  Hence conditional Sarnak rigidity makes
every fixed-completion path constant, which is stronger than divisor constancy.

## The topological overstatement

The former card asserted both

```text
every connected subset has constant divisor
```

and, "equivalently," that no coefficientwise-continuous path can move an off-line pair onto the
critical line.  These are not equivalent.  A subspace of a countable product of local tori can be
connected without being path connected.  No local path-connectedness theorem is available for the
fixed-completion locus.  Kaczorowski--Perelli address one-parameter continuous families, not
arbitrary connected subsets.

The connected-subset statement is therefore a strictly stronger topological conjecture with no
mechanism supplied by the route.  Retaining it would merely hide an additional open problem inside
the word `connected`.

## Why this is retired rather than promoted

1. The corrected path theorem is already the fixed-gamma slice of Sarnak rigidity.
2. Its known proof is conditional on the established parent conjectures, not a new unconditional
   constraint on zeros.
3. The coefficientwise-to-meromorphic bridge is rigorous but standard and not significant enough
   to pass the dual novelty/significance gate.
4. The arbitrary-connected-subset version was not equivalent to the path problem and has no
   independent evidence or attack.
5. Zero collisions, divisor discriminants, and derivative conditions remain consequences of a
   deformation; they do not supply the missing Selberg-class rigidity.

## Do not re-attempt

- Do not present fixed-completion path rigidity as a new zero-entry theorem without first surpassing
  Sarnak rigidity.
- Do not replace `path connected` by `connected` without proving local path connectedness or a
  direct component theorem for the moduli locus.
- Do not count the normal-family topology bridge as new scientific knowledge.
- Do not weaken the gamma hypothesis to fixed degree or fixed shift invariant: opposite vertical
  shifts survive those weaker data.

## Possible heir

A scientifically live heir would have to isolate an arithmetic hypothesis strictly weaker than the
Selberg orthonormality/countability package and nevertheless prove rigidity for a nonclassified
fixed-gamma primitive family.  That is a special-case attack on Sarnak rigidity and must be named as
such.  This card supplies no such hypothesis or mechanism.
