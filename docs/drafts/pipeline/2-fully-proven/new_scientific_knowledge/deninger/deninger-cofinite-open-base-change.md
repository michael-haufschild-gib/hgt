# Deninger cofinite-open base change

- **ID:** `deninger-cofinite-open-base-change`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Label:** `DAC_DENINGER_COFINITE_OPEN_BASE_CHANGE`
- **Parent:** `deninger-arithmetic-projection-leray-rost-schmid-resolution`
- **Statement:** Deninger's character space, Frobenius colimit,
  suspension, and degreewise coarse invariant coefficient restrict
  canonically to every cofinite arithmetic open.

## Goal

Separate a topological and sheaf-theoretic fact from the open analytic
comparison.  This theorem identifies the source object over
\[
 U_N=\operatorname{Spec}\mathbb Z[1/N]
\]
without commuting derived sections with invariants and without
replacing Deninger's coarse quotient by a quotient stack.

## Setup

Put \(S=\operatorname{Spec}\mathbb Z\).  Use the same Frobenius monoid
\(\mathbb N_{>0}\) for \(S\) and every \(U_N\); this is allowed because
Deninger only requires its set of prime generators to contain the
residue characteristics of the arithmetic scheme.

Write
\[
 \dot S(\mathbb C),\qquad
 \check S(\mathbb C)=
 \mathop{\mathrm{colim}}_{\nu\in\mathbb N_{>0},F_\nu}
 \dot S(\mathbb C)
\]
for Deninger's character space and Frobenius colimit.  Let
\[
 Y_S=\check S(\mathbb C)\times\mathbb R_{>0},\qquad
 X_S=Y_S/\mathbb Q_{>0},
\]
where
\[
 q\cdot(P,u)=(F_qP,q^{-1}u).
\]
The arithmetic projection is
\[
 a_S:X_S\longrightarrow S,\qquad [P,u]\longmapsto\operatorname{pr}(P).
                                                               \tag{1}
\]
The same notation with \(U_N\) in place of \(S\) denotes the
construction performed on the arithmetic open.

Let \(\widetilde{\mathscr A}^{\bullet}_S\) be any
\(\mathbb Q_{>0}\)-equivariant cover coefficient on \(Y_S\), and put
\[
 \mathscr E^\bullet_S
 =
 (\pi_{S,*}\widetilde{\mathscr A}^{\bullet}_S)
 ^{\mathbb Q_{>0}}.                                             \tag{2}
\]
For the final comparison one takes the Tate--Milnor coefficient of
`DAC_LEAFWISE_KUMMER_SHEAF_AMALGAMATION_EXISTENCE`.

## Theorem

`[PROVED HERE] [DAC_DENINGER_COFINITE_OPEN_BASE_CHANGE]`

For every nonzero \(N\):

1. \(\dot U_N(\mathbb C)\) is canonically the open subspace
   \[
   \operatorname{pr}^{-1}(U_N)\subset\dot S(\mathbb C).
                                                               \tag{3}
   \]
2. The induced map
   \[
   \check U_N(\mathbb C)\longrightarrow\check S(\mathbb C)
   \]
   is an open embedding with image
   \(\check{\operatorname{pr}}^{-1}(U_N)\).  Its image is invariant
   under every \(F_q\), under the Galois action before Galois descent,
   and under \(\mathbb Q_{>0}\).
3. The suspension made from \(U_N\) is canonically homeomorphic to
   the saturated open subspace
   \[
   X_{U_N}\ \xrightarrow{\sim}\ a_S^{-1}(U_N)\subset X_S.        \tag{4}
   \]
4. If
   \(Y_{U_N}=\pi_S^{-1}(a_S^{-1}U_N)\), then restriction of `(2)`
   satisfies, degreewise,
   \[
   \left.\mathscr E^\bullet_S\right|_{a_S^{-1}U_N}
   \cong
   \left(
      \pi_{U_N,*}
      \left.\widetilde{\mathscr A}^{\bullet}_S\right|_{Y_{U_N}}
   \right)^{\mathbb Q_{>0}}.                                    \tag{5}
   \]
   The isomorphism is functorial under \(U_M\subseteq U_N\), is
   compatible with the differential and product, and commutes with
   every equivariant source operation.

Equation `(5)` is underived.  Applying ordinary derived global
sections only after `(5)` gives
\[
 R\Gamma\!\left(a_S^{-1}U_N,\mathscr E^\bullet_S\right)
 =
 R\Gamma\!\left(
   X_{U_N},
   \left(
     \pi_{U_N,*}
     \widetilde{\mathscr A}^{\bullet}_S|_{Y_{U_N}}
   \right)^{\mathbb Q_{>0}}
 \right).                                                       \tag{6}
\]
No invariants have been moved through \(R\Gamma\).

## Proof

### Character space

Deninger's Lemma 7.1 identifies the inverse image of an arithmetic
open under the character-space projection.  Lemma 7.2 proves that
for every open immersion \(U\hookrightarrow S\), the induced
\(\dot U(\mathbb C)\hookrightarrow\dot S(\mathbb C)\) is an open
embedding.  These statements give `(3)`.

The Frobenius maps preserve the underlying scheme point:
\[
 F_\nu(x,P^\times)=(x,F_\nu P^\times).                           \tag{7}
\]
Consequently the embeddings in `(3)` commute with the common
Frobenius diagram.  Under the inductive-limit topology,
\(\check U_N(\mathbb C)\) is therefore exactly
\(\check{\operatorname{pr}}^{-1}(U_N)\).  For every Frobenius chart
its intersection is the open subspace `(3)`, so it is open.
Deninger's Proposition 7.4 makes every \(F_q\) a homeomorphism on
the colimit.  Equation `(7)` proves invariance under \(F_q\); the
Galois action also preserves \(x\)'s image in \(S\).  This proves
clause 2.

### Quotient and suspension

We use the following elementary quotient lemma.  If a group \(G\)
acts by homeomorphisms on \(Y\), \(V\subseteq Y\) is open and
\(G\)-invariant, and \(q:Y\to Y/G\) is the quotient map, then
\[
 V/G\longrightarrow q(V)
\]
is a homeomorphism and \(q(V)\) is open.  Indeed,
\[
 q^{-1}q(V)=V,\qquad
 q^{-1}q(O)=\bigcup_{g\in G}gO
                                                               \tag{8}
\]
for \(O\subseteq Y\).  The second set is open whenever \(O\) is
open, so \(q\) is open; applying the quotient criterion to the
restriction proves the homeomorphism.

Apply the lemma first to Galois descent, when present, and then to
the diagonal \(\mathbb Q_{>0}\)-action on
\(\check S(\mathbb C)\times\mathbb R_{>0}\).  The open from clause 2
times \(\mathbb R_{>0}\) is saturated because the rational-power
action preserves the arithmetic projection.  Its quotient is
precisely `(4)`, proving clause 3.

### Invariant coefficient

Let \(W\subseteq a_S^{-1}U_N\) be open.  Direct image and restriction
give the literal equality
\[
 \begin{aligned}
 \left(\pi_{S,*}\widetilde{\mathscr A}^n_S\right)(W)
 &=
 \widetilde{\mathscr A}^n_S(\pi_S^{-1}W)\\
 &=
 \left(\pi_{U_N,*}
   \widetilde{\mathscr A}^n_S|_{Y_{U_N}}\right)(W).              \tag{9}
 \end{aligned}
\]
Both \(\mathbb Q_{>0}\)-actions in `(9)` are restrictions of the same
action.  Taking their equalizers sectionwise gives `(5)`.
Differential, multiplication, restriction in \(N\), and every
commuting operation are unchanged under `(9)`.  This proves clause 4
and `(6)`.

## Exact boundary of the theorem

The theorem proves source localization, not the desired arithmetic
amplitude.  It does **not** prove:

- acyclicity or Steinness of \(a_S^{-1}U_N\);
- a Cartier/Kummer description of any prime packet;
- a two-row model for `(6)`;
- commutation of invariants with cohomology;
- exactness of the Rost--Schmid residue sequence.

Those assertions remain in
`DAC_COFINITE_COARSE_ANALYTIC_DIVISOR_COMPARISON`.

## Hostile audit

- Using a smaller Frobenius monoid for \(U_N\) would make the two
  colimits different diagrams.  The theorem fixes one common monoid.
- Openness before the Frobenius colimit alone is insufficient;
  compatibility `(7)` and the inductive-limit topology are both used.
- A quotient of an arbitrary open need not be its subspace quotient.
  Saturation and the open-quotient lemma are essential.
- Equation `(5)` concerns degreewise fixed sections.  It supplies no
  group-cohomology or homotopy-quotient comparison.
- The proof uses no zeta zero, RH statement, spectral realization, or
  numerical computation.

## Gates

- [x] 0 → 1 in-progress: precise source-local statement
- [x] 1 → 2 fully-proven: topological and equalizer proof complete
- [ ] 2 → 3 formalized: quotient-open and invariant-restriction
  lemmas remain to be encoded in Lean
- [ ] 3 → 4 publication-ready: integrate with analytic purity proof

## References

- Christopher Deninger, *Dynamical systems for arithmetic schemes*,
  Lemmas 7.1--7.3 and Proposition 7.4:
  https://arxiv.org/abs/1807.06400
- `DAC_COARSE_INVARIANT_SHEAF_EXISTENCE`
- `DAC_COFINITE_DIVISOR_SPLIT_STRICTNESS`

## Log

- 2026-07-27 — isolated and proved exact compatibility of Deninger's
  source space and underived invariant coefficient with cofinite
  arithmetic opens.
