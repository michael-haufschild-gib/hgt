# Two-column Cauchy flow and graph descent

- **ID:** `deninger-two-column-cauchy-flow-graph-descent`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Label:** `DAC_TWO_COLUMN_CAUCHY_FLOW_GRAPH_DESCENT`
- **Parent:** `deninger-tate-graph-green-prime-sector`
- **Scientific status:** `[NEW SOURCE-ASSEMBLY THEOREM; ANALYTIC INPUTS EXPOSED]`
- **Statement:** componentwise Cauchy restrictions commuting with the five
  two-column/signature flow generators assemble to a flow-equivariant
  three-term chain map, descend equivariantly to all three cohomology
  groups, and preserve every common graph domain for which the component
  restrictions satisfy the corresponding bounded partial-operator
  intertwining laws.

## Exact theorem

Let (C_A,C_B) be the three-term totalizations of two
Rost--Schmid/signature columns.  Write


\[
 \Theta_A^0=\theta_{A,00},\qquad
 \Theta_A^1=\theta_{A,10}\oplus\theta_{A,01},\qquad
 \Theta_A^2=\theta_{A,11}\oplus\theta_{A,S},                 \tag{1}
\]

and similarly for (B).  Let the five component restrictions be

\[
 r_{00},r_{10},r_{01},r_{11},r_S,                            \tag{2}
\]

and assume the six already-required Rost--Schmid/signature chain
naturality squares.  Assume in addition the five flow squares

\[
 r_j\theta_{A,j}=\theta_{B,j}r_j
 \quad(j=00,10,01,11,S).                                    \tag{3}
\]

Then:

1. the assembled Cauchy chain map (R:C_A\to C_B) satisfies
   
   \[
    R^q\Theta_A^q=\Theta_B^qR^q\qquad(q=0,1,2);              \tag{4}
   \]
2. its induced cohomology maps satisfy
   
   \[
    H^q(R)\Theta_{A,H^q}=\Theta_{B,H^q}H^q(R)
    \qquad(q=0,1,2);                                        \tag{5}
   \]
3. more generally, let (P_i:E\to E) and (Q_i:F\to F) be
   partially defined linear graph monomials and (T:E\to F) a
   linear map.  If
   
   \[
    T(\operatorname{Dom}P_i)\subseteq\operatorname{Dom}Q_i,
    \qquad Q_iTx=TP_ix,                                     \tag{6}
   \]
   
   for every (i), then (T) maps
   (igcap_i\operatorname{Dom}P_i) into
   (igcap_i\operatorname{Dom}Q_i).  If also
   
   \[
    \|Ty\|\le c\|y\|,                                      \tag{7}
   \]
   
   then on the common graph cores
   
   \[
    \|Q_iTx\|\le c\|P_ix\|.                               \tag{8}
   \]

## Proof

For degree zero, `(4)` is the (j=00) instance of `(3)`.  In degree
one the two sides applied to ((x_{10},x_{01})) are

\[
 (r_{10}\theta_{A,10}x_{10},
   r_{01}\theta_{A,01}x_{01})
\]

and

\[
 (\theta_{B,10}r_{10}x_{10},
   \theta_{B,01}r_{01}x_{01}),
\]

which agree componentwise by `(3)`.  Degree two is identical with
((11,S)).  This proves `(4)`.

Every (Theta_A^q) preserves cocycles and boundaries because it
commutes with the two differentials.  Every (R^q) preserves them
because (R) is a chain map.  Equality `(4)` therefore restricts to
cocycles and passes through the boundary quotient.  In degrees zero
and two this is respectively subtype restriction and quotient
functoriality; degree one applies both operations.  This proves `(5)`
without any splitting or closed-range hypothesis.

For `(6)`, if (x) belongs to every source monomial domain, the first
part of `(6)` puts (Tx) in every target monomial domain.  Hence it
belongs to the target common graph core.  On that core, the second
part of `(6)` and `(7)` give

\[
 \|Q_iTx\|=\|TP_ix\|\le c\|P_ix\|,
\]

which is `(8)`.

## Hostile audit and exact scope

- The theorem uses actual two-column/signature totalization maps, not
  an anonymous complex alone.  Exactly five new flow squares are
  required in addition to six existing differential/signature squares.
- Quotient equivariance is unconditional and does not assume a chosen
  complement, harmonic representative, closed range, or Xi divisor.
- Graph descent is not inferred from algebraic commutation.  Domain
  preservation and an ambient bound remain explicit analytic premises.
- The theorem does **not** prove those premises for genuine
  residue/corestriction, real orientation, Milnor attaching, or Meyer
  Cauchy maps.  It identifies their complete local obligation and the
  exact conclusion obtained once proved.
- Conservativity after quotient is also separate: it requires the
  already-isolated boundary-classification theorem for the family of
  Cauchy restrictions.  Equivariance alone cannot detect a class.
- Thus this result is infrastructure needed by
  `DAC_TATE_GRAPH_DOMAIN_ARITHMETIC_DESCENT`, not a claim that the broad
  conjecture is closed.

## Novelty audit

Functoriality of cohomology and graph norms is standard separately.
Targeted corpus search found no theorem coupling the concrete
two-column Rost--Schmid/signature assembler, its five flow components,
all three induced cohomological generators, and cross-space partial
graph cores.  New content is this exact source assembly and dependency
classification, not the parent categorical facts.

## Next exact claim

`[CONJECTURE] [DAC_ROST_SCHMID_TATE_GRAPH_LOCAL_NATURALITY]`

On every finite pro-Stein arithmetic chart, construct the
Tate-normalized graph monomials and prove `(6)`--`(7)` for the literal
finite-prime residues/corestrictions, real orientation map, and each
relative Sullivan/Milnor attaching map.  Determine whether Steinberg
and higher syzygy maps are uniformly bounded in the all-place
((\log p)^2)-weighted graph system.  A failure of uniformity is a
genuine obstruction to strict nuclear descent.

## Gates

- [x] source maps and exact statement frozen
- [x] internal collision audit
- [x] complete paper proof
- [x] hostile scope audit
- [ ] Lean formalization
- [ ] arithmetic local naturality estimates

## Log

- 2026-08-01 — Proved component-to-totalization and
  chain-to-cohomology flow descent, plus the cross-space graph-core
  preservation theorem; isolated actual domain and boundedness debts.
