# Route E terminal-leg and multilinear antiscale resonance

- **ID:** `ROUTE-E-TERMINAL-LEG-MULTILINEAR-RESONANCE-001`
- **Stage:** 3-formalized
- **Type:** THEOREM / SOURCE-CLASS NO-GO / POSITIVE DESIGN LAW
- **Parent:** `../../1-in-progress/route-e-cofinal-parity-energy-covariance-accumulation.md`
- **Source:** `OPEN-SOURCE-001`
- **RH used:** no
- **Computation used:** no
- **Lean:** `RHTower/RouteETerminalLegMultilinearResonance.lean`

## Statement

For (Y>1), (etage0), put (t_Y=pi/log Y) and call a prime terminal when

\[
 0\le \log Y-\log p\le \eta\log Y.
\]

Let (K^{(Y)}_{pq}) be any complex entrywise absolutely summable kernel such that every nonzero
entry has at least one terminal coordinate.  Then

\[
 \boxed{
 \left|\sum_{p,q}K^{(Y)}_{pq}(1+p^{it_Y})
        \overline{(1+q^{it_Y})}\right|
 \le 2\pi\eta\sum_{p,q}|K^{(Y)}_{pq}|.
 }
 \tag{1}
\]

No restriction is placed on the nonterminal coordinate.  Thus genuinely cross-scale
terminal-by-remote coupling is still inverse-linearly resonant.

More generally, let (I) be any finite leg set, let (a) index arbitrary signed monomials, and
write

\[
 T_a(t)=K_a\prod_{j\in I}(1+p_{a,j}^{it}).
 \tag{2}
\]

If each nonzero (K_a) comes with one source-selected terminal leg, then

\[
 \left|\sum_aT_a(t_Y)\right|
 \le \pi\eta,2^{|I|}\sum_a|K_a|.
 \tag{3}
\]

If every leg of every nonzero monomial is terminal, then the sharper inverse-degree law holds:

\[
 \boxed{
 \left|\sum_aT_a(t_Y)\right|
 \le (\pi\eta)^{|I|}\sum_a|K_a|.
 }
 \tag{4}
\]

All sums are complete `tsum`s.  Coefficients may be complex, indefinite, aperture-dependent, and
non-Hermitian.

## Proof

For a terminal prime, the unit-circle chord estimate already proved in the parent module gives

\[
 |1+p^{it_Y}|\le \pi\eta.
 \tag{5}
\]

For every prime at every scale,

\[
 |1+p^{it_Y}|\le2.
 \tag{6}
\]

For `(1)`, use `(5)` on whichever of the two coordinates is terminal and `(6)` on the other.
This bounds each summand by (2\pi\eta|K^{(Y)}_{pq}|).  Absolute summability permits the triangle
inequality through the complete `tsum`.

For `(3)`, remove the selected terminal leg from the finite product.  Apply `(5)` to that factor
and `(6)` to every remaining factor.  The proof uses the safe ceiling (2^{|I|}); replacing it by
(2^{|I|-1}) changes no resonance exponent.  Sum against (|K_a|).

For `(4)`, apply `(5)` independently to every leg, multiply the inequalities over the finite leg
set, and sum.  No cancellation or positivity is used at any point.

## Fixed-ratio consequence

For the terminal interval ((Y/C,Y]),

\[
 \eta={\log C\over\log Y}.
\]

Hence a uniformly coercive terminal-by-remote quadratic source must have entrywise mass

\[
 \sum_{p,q}|K^{(Y)}_{pq}|\gg_C\log Y,
 \tag{7}
\]

while a fixed (d)-linear all-terminal source must have mass

\[
 \sum_a|K_a|\gg_C(\log Y)^d.
 \tag{8}
\]

This is the positive design law exposed by the obstruction: one may survive through canonical
mass divergence/renormalization, a component with no terminal leg, arity growing with aperture,
or cancellation occurring before reduction to an entrywise-ℓ1 monomial sum.

## Route E consequence and hostile audit

The earlier theorem left “cross-scale” and “signed/nonquadratic” as overly broad survivors.
Equations `(1)`--`(4)` remove that ambiguity:

- cross-scale coupling does not escape if every entry still touches the physical terminal band;
- fixed-arity signed nonquadratic terminal shells do not escape entrywise-ℓ1 resonance;
- all-terminal higher arity is suppressed more strongly, not less;
- an aperture-dependent remote-by-remote component is not yet a boundary source and needs an
  independent connector back to the literal cutoff;
- growing-arity relation-valued cubes, canonically renormalized mass-divergent kernels, and
  noncompact migrating integer-index sources remain outside the theorem.

The co-moving diffuse Fisher codiagonal is not falsely excluded: its mass migrates in ordinary
integer index as the Euler parameter approaches criticality and its formula has no prime terminal
seam.  Existing corpus theorems show that every fixed finite divisor window and every compact
synthesis lose this mass.  What remains absent is a signed co-moving cutoff theorem carrying that
noncompact score into Route E's (D_{\rm anti}) or within-parity variation at physical-power
strength.

The grade-recurrent entropy-spread cube also survives only in the legitimate growing-arity,
relation-valued class.  Its exact unresolved content remains physical cross-anchor co-degree,
interval Hall expansion, and weighted endpoint flux; row admission and reciprocal allocation
normalization do not imply these.

Thus this theorem moves the frontier but does not prove `OPEN-SOURCE-001`, Route E, or RH.

## Formal audit

`RHTower/RouteETerminalLegMultilinearResonance.lean` proves `(1)`--`(4)` for arbitrary index types
with summable coefficient norms.  It imports the previously formalized physical chord bound, is
wired into `RHTower.lean`, and contains no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe`
declaration.  Targeted module build passes `9722/9722`.  `#print axioms` for all three complete
`tsum` theorems reports only `propext`, `Classical.choice`, and `Quot.sound`.
