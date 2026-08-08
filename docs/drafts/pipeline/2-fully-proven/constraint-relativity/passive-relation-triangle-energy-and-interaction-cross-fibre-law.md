# Passive relation triangles and interaction cross-fibres

- **ID:** `passive-relation-triangle-energy-interaction-cross-fibre`
- **Stage:** 2-fully-proven
- **Type:** THEOREM / CONSTRAINT RELATIVITY / QUANTUM MODEL
- **Scientific status:** `[PAPER-PROVED] [NO LEAN WRITTEN OR BUILT] [NOT RH]`
- **Novelty status:** orthogonal projection identities and local-Lie-algebra normalizers have
  classical parents. Candidate-new content is the joint relation-leak/holonomy/energy law and its
  placement beside the universal interaction cross-fibre. External priority remains open.
- **Parent:**
  `../../1-in-progress/constraint-relativity/constraint-relativity-and-relation-completion-spacetime.md`.

## 1. Purpose

This card proves two exact local laws for Constraint Relativity.

1. A raw-flat reversible triangle becomes curved after each observer removes its own relation
   subspace. The selected holonomy is exactly the transported sum of those losses, and its energy
   is the total norm lost at the three observer boundaries.
2. A joint finite quantum system contains a canonical cross-fibre invisible to both boundary
   partial traces. A Hamiltonian is local exactly when it never drives a local reporter into this
   cross-fibre at first order.

Together they provide a non-zeta model of relation-generated geometry and a precise mathematical
candidate for the hidden fibre in a relation bridge. They do not establish a gravitational
wormhole.

## 2. Passive relation triangle

Let `H_0,H_1,H_2` be complex Hilbert spaces. Let

\[
 U_0:H_0\to H_1,
 \qquad U_1:H_1\to H_2,
 \qquad U_2:H_2\to H_0
 \tag{2.1}
\]

be unitary maps satisfying the raw-flat cycle law

\[
 U_2U_1U_0=I_{H_0}.
 \tag{2.2}
\]

For `i=0,1,2`, let `P_i` be an orthogonal projection on `H_i`. Its range is the freedom retained
by observer `i`; its kernel is the relation/loss sector removed at that frame.

Define the selected cycle operator

\[
 \mathsf H=P_0U_2P_2U_1P_1U_0P_0:H_0\to H_0.
 \tag{2.3}
\]

Fix `x in ran P_0`. Define successive leaks

\[
 \begin{aligned}
 a&=(I-P_1)U_0x,\\
 b&=(I-P_2)U_1P_1U_0x,\\
 c&=(I-P_0)U_2P_2U_1P_1U_0x,
 \end{aligned}
 \tag{2.4}
\]

selected holonomy defect

\[
 \Omega x=x-\mathsf Hx,
 \tag{2.5}
\]

and total relation-leak energy

\[
\mathsf W(x)=\|a\|^2+\|b\|^2+\|c\|^2.
 \tag{2.6}
\]

### Proposition 2.1 — frame covariance and cyclic spectrum

Suppose unitaries `g_i:H_i->H_i'` carry `P_i` to `P_i'` and
`U_i'=g_(i+1)U_i g_i^(-1)`. Then selected holonomy transforms by

\[
 \mathsf H'=g_0\mathsf H g_0^{-1},
 \tag{2.7}
\]

and all leakage norms and `mathsf W` are invariant.

If the freedom spaces are finite-dimensional, the three selected holonomies based at the three
vertices have the same nonzero eigenvalues with algebraic multiplicity. They may differ only by
additional zero eigenvalues when freedom dimensions differ.

#### Proof

`P_i'=g_iP_ig_i^(-1)`; substituting into the selected product cancels adjacent gauge factors and
gives `(2.7)`. Each leakage vector is carried by the corresponding unitary `g_i`, so norms are
unchanged. For cyclic spectra, apply the identity

\[
 \det(I-tAB)=\det(I-tBA)
\]

successively to the rectangular selected edge maps. QED.

## 3. Relation-leak Gauss law

### Theorem 3.1 — exact holonomy and energy identities

For every `x in ran P_0`,

\[
 \boxed{\Omega x=U_2U_1a+U_2b+c,}
 \tag{3.1}
\]

\[
 \boxed{\mathsf W(x)=\|x\|^2-\|\mathsf Hx\|^2,}
 \tag{3.2}
\]

and

\[
 \boxed{
 \mathsf W(x)
 =2\operatorname{Re}\langle x,\Omega x\rangle-\|\Omega x\|^2.}
 \tag{3.3}
\]

Consequently,

\[
 \boxed{\|\Omega x\|^2\le3\mathsf W(x).}
 \tag{3.4}
\]

The selected cycle is flat on `x` if and only if all three leaks vanish.

### Proof

Since `P_1U_0x=U_0x-a`,

\[
 U_1U_0x=U_1P_1U_0x+U_1a.
 \tag{3.5}
\]

Since `P_2U_1P_1U_0x=U_1P_1U_0x-b`,

\[
 U_2U_1P_1U_0x
 =U_2P_2U_1P_1U_0x+U_2b.
 \tag{3.6}
\]

Finally,

\[
 U_2P_2U_1P_1U_0x=\mathsf Hx+c,
 \tag{3.7}
\]

because `P_0x=x`. Combining `(2.2)` and `(3.5)`--`(3.7)` gives

\[
 x=\mathsf Hx+c+U_2b+U_2U_1a,
\]

which is `(3.1)`.

Orthogonality gives a Pythagorean identity at each projection:

\[
 \begin{aligned}
 \|x\|^2
 &=\|P_1U_0x\|^2+\|a\|^2,\\
 \|P_1U_0x\|^2
 &=\|P_2U_1P_1U_0x\|^2+\|b\|^2,\\
 \|P_2U_1P_1U_0x\|^2
 &=\|\mathsf Hx\|^2+\|c\|^2.
 \end{aligned}
 \tag{3.8}
\]

Unitary invariance of norm is used between the displayed stages. Adding `(3.8)` proves `(3.2)`.
Since `mathsf Hx=x-Omega x`, expansion of `||x-Omega x||^2` in `(3.2)` proves `(3.3)`.

By `(3.1)`, unitarity, and Cauchy--Schwarz,

\[
 \|\Omega x\|^2
 \le(\|a\|+\|b\|+\|c\|)^2
 \le3(\|a\|^2+\|b\|^2+\|c\|^2),
\]

which is `(3.4)`. If all leaks vanish, `(3.1)` gives flatness. Conversely, if `Omega x=0`, then
`(3.2)` gives `mathsf W(x)=0`, so each leak vanishes. QED.

### Corollary 3.2 — positive energy is a shadow, not an independent selector

The positive scalar `mathsf W(x)` records total relation loss. It is determined by contraction of
the selected holonomy through `(3.3)`, but it does not retain the ordered triple `(a,b,c)` or tell
which frame lost the relation. Thus a positive metric can detect observer curvature while erasing
its provenance and orientation.

### Corollary 3.3 — cofinal singularity

For a sequence of passive triangles, if `a_n,b_n,c_n -> 0` in norm, then `Omega_n x_n ->0` whenever
the `x_n` are normalized. Hence persistent selected holonomy cannot survive uniformly vanishing
relation leaks in a raw-flat passive unitary model. A cofinal survivor must use nonuniform norms,
unbounded/nonunitary transport, nonclosed limiting projections, or a missing common selection
triangle.

### Corollary 3.4 — one-port case

If the total leak operator has rank one on a selected sector, then every positive observer built
only from `mathsf W` sees one exceptional square, while the unsquared holonomy still retains an
oriented vector. This is the abstract passive origin of a “positive part minus one physical-rank
square” pattern; the theorem does not assert that any particular RH Stokes form is this model.

### Theorem 3.5 — positive leakage does not determine phase

There exist two raw-flat passive triangles with identical three leakage energies, identical total
work, and opposite selected-holonomy phases.

#### Proof

Take `H_0=H_1=H_2=C^2`, all raw transports equal to the identity, and let the freedom projections
have ranges spanned by

\[
 u_0=(1,0),
 \qquad
 u_1={1\over\sqrt2}(1,1),
 \qquad
 u_2^\pm={1\over\sqrt2}(1,\pm i).
 \tag{3.9}
\]

Start with `x=u_0`. Direct projection gives, for both signs,

\[
 \|a\|^2={1\over2},
 \qquad
 \|b\|^2={1\over4},
 \qquad
 \|c\|^2={1\over8},
 \qquad
 \mathsf W={7\over8}.
 \tag{3.10}
\]

On the one-dimensional space `C u_0`, however, selected holonomies are multiplication by

\[
 \langle u_0,u_2^\pm\rangle
 \langle u_2^\pm,u_1\rangle
 \langle u_1,u_0\rangle
 ={1\mp i\over4}.
 \tag{3.11}
\]

Their phases are opposite. A complex-linear gauge change conjugates a scalar to itself, so these
triangles are not oriented-gauge equivalent. Antiunitary conjugation interchanges them only by
forgetting orientation. QED.

This theorem is a closed obstruction to reconstructing constraint phase from pairwise angles,
singular values, or positive work alone.

## 4. Joint systems and the canonical cross-fibre

Let `A,B` be finite-dimensional complex Hilbert spaces of dimensions at least two. Write
`Herm(A)` for real vector space of Hermitian operators and `Herm_0(A)` for its traceless subspace.

Let

\[
 \mathcal J=\operatorname{Herm}_0(A\otimes B)
 \tag{4.1}
\]

and define normalized boundary map

\[
 \pi:\mathcal J\to
 \operatorname{Herm}_0(A)\oplus\operatorname{Herm}_0(B)
 \tag{4.2}
\]

by

\[
 \pi(X)=\left(
 {1\over\dim B}\operatorname{Tr}_B X,
 {1\over\dim A}\operatorname{Tr}_A X
 \right).
 \tag{4.3}
\]

Embed boundary reporters as

\[
 \mathcal L=
 \bigl(\operatorname{Herm}_0(A)\otimes I_B\bigr)
 \oplus
 \bigl(I_A\otimes\operatorname{Herm}_0(B)\bigr).
 \tag{4.4}
\]

## 5. Cross-fibre and locality theorem

### Theorem 5.1 — exact boundary/cross decomposition

There is an orthogonal direct sum for Hilbert--Schmidt inner product,

\[
 \boxed{
 \mathcal J=\mathcal L\oplus\mathcal C,
 \qquad
 \mathcal C=operatorname{Herm}_0(A)\otimes_{\mathbb R}
             \operatorname{Herm}_0(B),}
 \tag{5.1}
\]

and

\[
 \boxed{\ker\pi=\mathcal C.}
 \tag{5.2}
\]

Consequently,

\[
 \dim_{\mathbb R}\mathcal C
 =\bigl((\dim A)^2-1\bigr)\bigl((\dim B)^2-1\bigr).
 \tag{5.3}
\]

### Proof

Choose Hilbert--Schmidt orthogonal Hermitian bases

\[
 \{I_A,A_1,\dots,A_{d_A^2-1}\},
 \qquad
 \{I_B,B_1,\dots,B_{d_B^2-1}\},
\]

with every `A_i,B_j` traceless. Their tensor products form an orthogonal real basis of
`Herm(A tensor B)`. Removing `I_A tensor I_B` gives exactly the three summands in `(5.1)`. Partial
trace recovers the two local summands and kills every `A_i tensor B_j`, proving `(5.2)`. Counting
basis vectors proves `(5.3)`. QED.

### Theorem 5.2 — first-order locality classifier

Let `H in Herm(A tensor B)`. Then

\[
 i[H,L]\in\mathcal L
 \quad\text{for every }L\in\mathcal L
 \tag{5.4}
\]

if and only if

\[
 \boxed{
 H=H_A\otimes I_B+I_A\otimes H_B+cI_{A\otimes B}}
 \tag{5.5}
\]

for Hermitian `H_A,H_B` and real `c`.

Equivalently, every genuinely nonlocal interaction drives at least one local reporter into the
hidden cross-fibre `mathcal C` at first order.

### Proof

Every operator `(5.5)` preserves `mathcal L` under commutator, so sufficiency is immediate.

Conversely decompose `H=H_loc+H_cross+cI` by `(5.1)`. Local and scalar parts preserve `mathcal L`.
For `X in Herm_0(A)`,

\[
 i[H_{\rm cross},X\otimes I_B]\in\mathcal C,
 \tag{5.6}
\]

because commutation changes only the traceless `A` factor of every cross basis tensor. Hypothesis
`(5.4)` and directness of `(5.1)` force `(5.6)` to vanish for every `X`. Thus `H_cross` commutes
with the full matrix algebra on `A` and belongs to `I_A tensor Herm(B)`. But it also lies in
`mathcal C=ker pi`; taking partial trace over `A` forces it to vanish. Hence `H` has form `(5.5)`.
QED.

### Corollary 5.3 — two-qubit exact exposure

For Pauli matrices and `H=Z tensor Z`,

\[
 e^{itH}(X\otimes I)e^{-itH}
 =\cos(2t)X\otimes I-\sin(2t)Y\otimes Z.
 \tag{5.7}
\]

The first term is boundary-visible; the second lies in `mathcal C` and is killed by both normalized
partial traces. Thus boundary data see only `cos(2t)`, while the joint completion retains the
oriented cross component `-sin(2t)Y tensor Z`.

### Proof

`H` anticommutes with `X tensor I` and satisfies `H^2=I`. Expanding conjugation, or solving the
two-dimensional commutator system, gives `(5.7)`. Both Pauli factors in the second term are
traceless, so Theorem 5.1 places it in `mathcal C`. QED.

## 6. Constraint-relativistic interpretation

Theorem 3.1 is a local field law:

```text
raw reversible transport + observer relation projections
  -> ordered leaks
  -> selected holonomy
  -> positive norm-loss energy.
```

Theorems 5.1--5.2 identify a canonical interaction fibre:

```text
joint reporter space
  = boundary-A reporters + boundary-B reporters + cross reporters;
genuine interaction
  = first-order transport from boundary into cross fibre.
```

This is stronger than dimension numerology. The cross-fibre is the exact kernel of boundary
reporting, and locality is characterized by failure to enter it.

## 7. Brown--Susskind and holographic scope

The results support, but do not prove, a physical program:

1. local boundary observers can miss an oriented joint sector generated by interaction;
2. a complexity metric on joint unitary evolution can assign length to motion in this sector;
3. if a holographic model identifies that length with interior volume or action, `mathcal C` is a
   candidate infinitesimal interior fibre;
4. recurrence of the joint unitary returns the cross coordinate even when boundary scalar data
   lose its sign.

No result here identifies `mathcal C` with an AdS wormhole, black-hole interior, entanglement
wedge, ER bridge, or gravitational degree of freedom.

## 8. Hostile audit and falsifiers

### What is new corpus knowledge

1. exact relation-leak decomposition `(3.1)`;
2. equality of total leak energy, selected norm loss, and the holonomy quadratic `(3.2)`--`(3.3)`;
3. universal holonomy bound `(3.4)`;
4. exact cross-fibre/locality classifier `(5.1)`--`(5.5)` placed in the same relation-completion
   field.

### What is classical or demoted

- Pythagoras for projections;
- contraction defect identities;
- tensor decomposition of matrix algebras;
- normalizer of the local Lie algebra;
- Pauli conjugation.

### Falsifiers

1. a raw-flat unitary triangle violating `(3.1)`--`(3.4)`;
2. a nonzero cross operator surviving either partial trace;
3. a genuinely nonlocal Hamiltonian satisfying `(5.4)`;
4. a claimed wormhole interpretation without an independently defined gravitational realization.

## 9. Future Lean notes — no action

Potential later formalization uses orthogonal projections, unitary norm preservation, finite tensor
matrix bases, partial traces, and commutants. Exact corpus declarations must be researched then.
No Lean code was written or built in this turn.
