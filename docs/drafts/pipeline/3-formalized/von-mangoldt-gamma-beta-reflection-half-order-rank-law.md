# Von Mangoldt–Gamma/Beta half-order repair-rank law

- **Status:** Formalized in Lean 4
- **Lane:** Connes–Consani–Moscovici source positivity
- **Verdict scope:** Canonical cofinal factorial/Beta-reflected source
- **No hypotheses:** Yes

## Frontier

The previous four-order theorem proved two negative directions and excluded one
positive boundary channel. It did not answer the infinite-order objection:
repair rank could grow with truncation, and a fixed higher finite rank had not
been excluded.

## Universal law

Let

\[
H_n(i,j)=\frac1{(i+j+1)!},\qquad 0\le i,j<n.
\]

For each leading block, take the last column of its inverse and extend it by
zero. These columns form an invertible upper-triangular flag matrix \(Q_n\).
Lean proves the exact all-order congruence

\[
Q_n^T H_nQ_n=\operatorname{diag}(d_0,\dots,d_{n-1}),
\]

where \(d_j=(H_{j+1}^{-1})_{j,j}\). The determinant signs of consecutive
leading blocks give

\[
j\ \text{odd}\quad\Longrightarrow\quad d_j<0.
\]

Thus \(H_{2m}\) has an explicit injective \(m\)-column negative frame. Its
negative inertia is at least \(m\), for every \(m\), so negative inertia is
unbounded along the tower.

## Transfer to actual CCM source

After scaling by \(2^{x+1}\), first-prime dominance gives the cofinal
von Mangoldt–Gamma factorial/Beta source limit

\[
L_n(i,j)=
\frac{(\log 2)^{i+j+2}}{(i+j+1)!}
=(\log 2)^2D_nH_nD_n,
\quad D_n(i,i)=(\log 2)^i.
\]

The frame \(D_{2m}^{-1}Q_{2m}\), restricted to odd flag columns, compresses
this limit to the strictly negative diagonal

\[
(\log 2)^2\operatorname{diag}(d_1,d_3,\dots,d_{2m-1}).
\]

Entrywise cofinal convergence makes the same fixed \(m\)-plane negative
definite for every sufficiently large displacement.

Consequently, if \(k<m\), then eventually no repair

\[
A_x+\sum_{a<k}v_av_a^*
\]

is positive semidefinite on the order-\(2m\) packet. Equivalently, positive
repair rank must grow at least linearly:

\[
\operatorname{repairRank}(2m)\ge m.
\]

In particular, every fixed finite repair rank fails cofinally.

## What this closes

- Closes all fixed finite-channel completions of canonical factorial/Beta
  reflection.
- Replaces the four-order/rank-one obstruction by an infinite all-order law.
- Proves any surviving completion must use genuinely unbounded channel rank or
  change the reflected source kernel.

## What remains

This does not identify every conceivable CCM source transport with factorial/
Beta reflection. A singular completion whose internal repair rank grows without
bound is not excluded. Killing that survivor requires a theorem forcing
finite-rank/cofinal approximability, or a direct contradiction for the singular
infinite lift.

## Formal sources

- `formal/GaloisForLFunctions/HTGeometry/ReciprocalFactorialHankelInertia.lean`
- `formal/GaloisForLFunctions/RHTower/VonMangoldtGammaBetaReflectionFiniteRankRepairNoGo.lean`

Principal theorems:

- `inverseFlagFrame_congruence`
- `reciprocalFactorialHankel_unbounded_negative_inertia`
- `betaFactorialAllOrderNegativeFrame_compresses_limit`
- `betaFactorialAllOrderComplexGram_eventually_not_posSemidef_add_rank_lt_half`
- `betaFactorialAllOrderComplexGram_eventually_not_posSemidef_add_finiteRank`

## Novelty status

The reciprocal-factorial determinant/inverse algebra has classical antecedents.
No novelty is claimed for that isolated matrix identity. Candidate new content
is the exact flag-inertia formulation and its unconditional cofinal CCM
consequence: repair rank for the canonical reflected source grows at least as
half the Borel order. External literature novelty audit remains required before
publication.
