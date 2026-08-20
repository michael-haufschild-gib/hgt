# Joint Hurwitz exponent half-plane removal

- **ID:** `joint-hurwitz-exponent-half-plane-removal`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Scientific status:** `[PROVED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** The joint differential-algebraic-independence theorem for
  $a\mapsto\zeta(s_j,a)$ holds for every finite family for which
  $1,(s_j)_j$ is linearly independent over $\mathbb Q$, with no restriction
  $\operatorname{Re}(s_j)>1$.

## Theorem

Let $I$ be finite and let $s_j\in\mathbb C$ for $j\in I$.  Assume that the augmented family

\[
1,(s_j)_{j\in I}
\]

is linearly independent over $\mathbb Q$.  Then the classical analytically continued Hurwitz
functions

\[
a\longmapsto \zeta(s_j,a),\qquad j\in I,
\]

on the upper half-plane are differentially algebraically independent over $\mathbb C(a)$.

Equivalently, every finite family of their differential jets is algebraically independent over
$\mathbb C(a)$.

## Proof

For each $j\in I$, choose $m_j\in\mathbb N$ such that

\[
\operatorname{Re}(s_j+m_j)>1.
\]

Put $t_j=s_j+m_j$.  Adding integers to the exponents preserves augmented rational linear
independence: a relation

\[
q_0+\sum_jq_jt_j=0
\]

is the relation

\[
\left(q_0+\sum_jq_jm_j\right)+\sum_jq_js_j=0,
\]

so every coefficient is zero.  The monodromy-character theorem in the convergence chamber
therefore gives differential algebraic independence of

\[
a\longmapsto\zeta(t_j,a),\qquad j\in I.
\]

The Hurwitz derivative identity, valid by analytic continuation on the upper half-plane, is

\[
\partial_a^{m_j}\zeta(s_j,a)
=(-1)^{m_j}(s_j)_{m_j}\zeta(t_j,a).
\]

The scalar $(s_j)_{m_j}$ is nonzero.  Indeed, its vanishing would make $s_j$ an integer, which
is excluded by rational independence of $1$ and $s_j$.  Hence the family of shifted jets

\[
\left(\partial_a^{m_j}\zeta(s_j,a)\right)_{j\in I}
\]

is differentially algebraically independent.

It remains to use the standard derivative-tail lemma.  In a differential field extension, if
$(D^{m_j}x_j)_j$ is differentially algebraically independent over the base field, then
$(x_j)_j$ is differentially algebraically independent.  To prove it, let

\[
G=K\langle D^{m_j}x_j:j\in I\rangle,
\qquad
F=K\langle x_j:j\in I\rangle.
\]

Then $G\subseteq F$, and each $x_j$ is differentially algebraic over $G$, since it satisfies
the differential polynomial

\[
D^{m_j}Y-D^{m_j}x_j=0
\]

with coefficients in $G$.  Thus $F/G$ is differentially algebraic, so

\[
\operatorname{dtrdeg}_K F=\operatorname{dtrdeg}_K G=|I|.
\]

Therefore the original family is differentially algebraically independent.  Applying this lemma
to $x_j(a)=\zeta(s_j,a)$ proves the theorem.
□

## Constraint form

No new monodromy flow has to be constructed outside $\operatorname{Re}(s)>1$.  The
arbitrary-exponent function is used only through the static highest-jet constraint

\[
D^{m_j}x_j=(-1)^{m_j}(s_j)_{m_j}\zeta(s_j+m_j,\cdot).
\]

The lower integration constants lie in a differential-algebraic extension and cannot destroy the
differential transcendence rank fixed by the upper-end constraint.

## Boundary

This is a standard differential-algebraic reduction from the already proved upper-end theorem.  It
does not create an RH implication, and it does not make differential independence sensitive to a
zero divisor or to critical-line orientation.

## Gates

- [x] unrestricted exponent theorem stated
- [x] complete reduction to the published upper-end monodromy-character theorem
- [x] nonzero Pochhammer factor justified
- [x] derivative-tail differential-algebra lemma proved
- [ ] Lean formalization of the derivative-tail lemma and unrestricted analytic Hurwitz carrier

## Lean formalization (2026-08-21) — COMPLETE

Both remaining gate items are unconditional Lean theorems, axiom-audited to
`propext, Classical.choice, Quot.sound`.

1. **The card's theorem — unrestricted analytic Hurwitz carrier.**
   `HurwitzJointLadder.continued_joint_hzeta_upperEnd_differentialIndependent_finite`
   (`formal/GaloisForLFunctions/Hurwitz/ContinuedJointUpperEndDifferentialIndependence.lean:238`):

   for every `Fintype ι` and `s : ι → ℂ` with `LinearIndependent ℚ (exponentFamily s)` — i.e. the
   augmented family `1, (s_j)_j` rationally independent, with **no** restriction `Re s_j > 1` —
   the analytically continued Hurwitz elements `fun j => continuedHzetaUpperEndMero (s j)` are
   `DifferentialIndependent (RatFunc ℂ)` in the upper-end meromorphic differential field.

   The carrier is the genuine classical continuation: `continuedHzeta` is built by the canonical
   finite Taylor subtraction (`Hurwitz/AnalyticContinuation.lean`), agrees with the convergent
   Hurwitz series on `Re s > 1` (`continuedHzeta_eq_hzeta`), is analytic on the whole upper
   half-plane (`continuedHzeta_analyticOnNhd`), and satisfies the unrestricted shift-derivative law
   `∂ₐ ζ(s,a) = -s ζ(s+1,a)` (`continuedHzeta_hasDerivAt`) — the Lean form of the card's
   `∂_a^{m} ζ(s,a) = (-1)^m (s)_m ζ(s+m,a)` identity, packaged as
   `continuedHzetaUpperEndAnalyticJet_eq`.

2. **The derivative-tail differential-algebra lemma.**  New module
   `formal/GaloisForLFunctions/HTGeometry/DerivativeTailDifferentialIndependence.lean`:

   - `GaloisForLFunctions.differentialIndependent_of_jetShift` — for a finite nonempty index type,
     if `fun j => differentialJet (m j) (x j)` is differentially independent over `F`, then `x` is.
     This is exactly the card's lemma "`(D^{m_j} x_j)_j` differentially independent ⇒ `(x_j)_j`
     differentially independent", proved by the differential-transcendence-degree count the card
     describes: the shifted family lives in `K = F⟨x⟩` and certifies
     `#ι ≤ dtrdeg_F K`, while `x` generates `K`, so the spanning family of that size is a
     differential transcendence basis
     (`differentialIndependent_of_spanning_of_cardinalMk_le`).
   - `GaloisForLFunctions.injective_of_differentialIndependent_jetShift` — the injectivity input,
     from `differentialJet (m j) (differentialJet (m i) (x i)) =
     differentialJet (m i) (differentialJet (m j) (x j))` when `x i = x j`.
   - `GaloisForLFunctions.differentialIndependent_coe_of_subfield` — the converse of
     `differentialIndependent_subfield`, needed to read the certificate back in the ambient field.

Wired into `GaloisForLFunctions.HTGeometry`.

## Gates

- [x] Lean formalization of the derivative-tail lemma and unrestricted analytic Hurwitz carrier
