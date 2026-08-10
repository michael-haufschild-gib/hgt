# Nonnegative Möbius-irreducible overlap

- **ID:** ULF-FKT-MOBIUS-NOGO
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** positive-overlap-defect calculus programme, higher-law attack A
- **Statement:** Boolean Möbius inversion of raw multiway overlap defects is not universally
  nonnegative.
- **Status:** [EXACT COUNTERTHEOREM] [POSITIVE SURVIVOR EXTRACTED]
  [COUNTEREXAMPLE LEAN-PENDING] [POSITIVE TWO-LEVEL SURVIVOR LEAN-PROVED]

## Goal

Test whether binary false-overlap mechanics extends to a scalar nonnegative irreducible defect at
every arity by ordinary subset-lattice Möbius inversion.

## Exact killing theorem

Fix `r >= 2`.  Let the source be `X={1,...,r}`, let the observer be constant, and take the `r`
probability profiles

\[
  u_i=\delta_i.
\]

For a nonempty subset `S` of profile labels, define the raw overlap defect

\[
  D(S)=\bigwedge_{i\in S} f_!u_i
       -f_!\!\left(\bigwedge_{i\in S}u_i\right).
\]

For singletons, both terms equal unit mass and `D(S)=0`.  For `|S|>=2`, the source profiles have
zero common meet while every pushforward is unit mass, hence `D(S)=1`.  The top Boolean Möbius
coefficient is therefore

\[
  I_r=\sum_{\varnothing\ne S\subseteq[r]}(-1)^{r-|S|}D(S)
     =\sum_{k=2}^r(-1)^{r-k}{r\choose k}
     =(-1)^r(r-1).
\]

The last equality follows from
`sum_{k=0}^r (-1)^(r-k) choose(r,k)=0`: the omitted `k=0` term is `(-1)^r` and the omitted `k=1`
term is `r(-1)^(r-1)`.  Thus `I_r<0` for every odd `r>=3`.  Reversing the global sign merely moves
the failure to even arity.

## No-go closure

- **Exact killing mechanism:** scalar Möbius inversion is alternating and does not preserve the
  positive cone, even for disjoint Dirac profiles and the simplest deterministic observer.
- **Strongest positive survivor:** replace scalar irreducible coefficients by a positive witness
  space.  For a chain of nested observers, all pairwise agreement capacities admit a simultaneous
  maximal coupling.  The maximizers form an exposed face, and successive face strata have the
  nonnegative masses `A_j-A_{j-1}`.
- **New insight:** positivity does not live in an alternating scalar coefficient.  It lives in a
  refinement-compatible witness whose positive strata are later scalarized.  The appropriate
  higher mechanism is consensus-face geometry, not scalar higher curvature.
- **Status:** finite survivor proved on paper in
  `nested-observer-hierarchical-maximal-coupling-face-law.md`; its first nontrivial two-level case is
  Lean-certified.  The arbitrary finite chain and the scalar counterexample itself remain
  Lean-pending.

## Parent mathematics and scope

The counterexample is elementary.  It is compatible with classical Möbius inversion and with the
need for enriched/orthogonal Möbius values when positivity is desired.  It does not refute signed
interaction invariants, orthogonal decompositions, persistence modules, or multi-distribution
divergences with different axioms.

## Log

- 2026-08-10 — conjecture falsified at every odd arity; hierarchical coupling face extracted as
  positive survivor.
