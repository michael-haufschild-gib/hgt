# Polarized exactness horizon and relative Connes phase law

- **ID:** `ngd-polarized-exactness-horizon-relative-connes-phase`
- **Stage:** 2 — fully proved on paper
- **Type:** UNCONDITIONAL STRUCTURE / NO-GO / CROSS-COEFFICIENT BRIDGE
- **Status:** `[PAPER PROOF DEPENDENCY-CLOSED] [NOT RH] [NO LEAN WRITTEN]`
  `[CLASSICAL INGREDIENTS ALLOWED] [LIVE-OBSTRUCTION LEVERAGE]`
- **Statement:** A reduced oriented law horizon and its positive doubled singularity are
  complementary, not interchangeable.  The reduced equation has trivial finite matrix-
  factorization theory; its square has nontrivial singularity theory but forgets the sign/phase
  of the conormal generator.  In a paracyclic realization, target monodromy is already Connes-
  null-homotopic; the genuine source obstruction is the relative class of that null-homotopy.

## 1. Public meaning

Exactness has an amplitude and an energy.  The amplitude remembers which side and which phase;
the energy creates a visible singularity by squaring the amplitude, but destroys that orientation.
The missing arithmetic theorem therefore cannot be produced by an unframed positive or
singularity invariant, nor by target-side null-homology.  It must be a source-normal lift of the
phase-bearing exactness trivialization.

## 2. Local polarized horizon

Let `k` be a field with `char(k) != 2` and let `R=k[[a]]`. Put

\[
 H=\operatorname{Spec}R/(a),\qquad
 H^{(2)}=\operatorname{Spec}R/(a^2),\qquad
 N^*_{H/R}=(a)/(a^2).
\tag{2.1}
\]

The class `e=[a]` is an oriented amplitude coordinate.  Its positive/unoriented energy coordinate
is `e^2`.

### Theorem 2.1 — orientation--singularity complementarity

The following statements hold.

1. `H` is regular and its singularity category is zero.
2. Every finite free matrix factorization of the potential `a` over `R` is a direct sum of
   contractible rank-one factorizations.
3. `H^(2)` is singular.  The factorization `(a,a)` of `a^2` is noncontractible, and the residue
   module `k` is a nonzero object of `D_sg(R/(a^2))`.
4. The involution

   \[
     \iota:R/(a^2)\longrightarrow R/(a^2),\qquad a\longmapsto-a
   \tag{2.2}
   \]

   fixes the doubled equation `a^2=0` but acts by `-1` on `N^*_(H/R)`.
5. Consequently the unframed doubled horizon canonically retains the conormal **line**, but it
   has no automorphism-natural nonzero conormal generator.  Every such generator is a
   `mu_2`-torsor choice.

#### Proof

`R/(a)=k` is a field, hence regular; every bounded coherent complex over it is perfect, proving
the first assertion.

For the second, let

\[
 P_0\mathop{\rightleftarrows}^{\phi}_{\psi}P_1,
 \qquad \psi\phi=a\,\mathrm{id}_{P_0},\quad
 \phi\psi=a\,\mathrm{id}_{P_1}
\tag{2.3}
\]

be a finite free factorization.  After adding no summands, the two free modules have equal rank:
both maps become inverse up to the nonzero scalar `a` over `Frac(R)`.  Smith normal form diagonalizes
`phi` with diagonal entries `u_i a^(m_i)`.  Absorbing the units into bases and using
`psi phi=a id` forces `m_i` to be either `0` or `1`; `psi` has the complementary entry
`a^(1-m_i)`.  Thus `(2.3)` is a direct sum of `(1,a)` and `(a,1)`.  Each contains an invertible
differential and is contractible.

Let `S=R/(a^2)`.  It is a nonfield Artinian local ring with nonzero nilpotent maximal ideal
`(a)`, hence is not regular.  The periodic sequence

\[
 \cdots\xrightarrow{a}S\xrightarrow{a}S\xrightarrow{a}S
 \longrightarrow k\longrightarrow0
\tag{2.4}
\]

is exact because `ker(a:S->S)=aS=im(a:S->S)`.  Its first syzygy is again `k`, so the resolution
does not terminate.  Equivalently, `k` is not projective: a finite projective over the local ring
`S` is free, while `length_S(k)=1` and `length_S(S)=2`.  Hence `k` is nonzero in `D_sg(S)`, and
the factorization `(a,a)`, whose cokernel is `k`, is noncontractible.

Finally `(2.2)` is an automorphism because `(-a)^2=0`.  It fixes the defining doubled equation and
sends `[a]` to `-[a]` in `(a)/(a^2)`.  An automorphism-natural vector would have to be fixed by
`iota`; since `2` is invertible, the only fixed vector in the weight-one conormal line is zero.
This proves all claims. `QED`

### Corollary 2.2 — power/phase uncertainty

For `m>=2` with `char(k)` prime to `m`, the thick horizon `R/(a^m)` is invariant under
`a -> zeta a` for every `m`-th root of unity `zeta in k`, while its conormal generator has weight
one.
Thus an unframed `m`-th-power observer loses a `mu_m` phase torsor.  The case `m=2` is the precise
orientation/positive-energy uncertainty used below.

#### Proof

The automorphism fixes `a^m` and acts by `zeta` on `(a)/(a^2)`.  A natural generator would be
fixed by all such automorphisms and therefore cannot be nonzero. `QED`

## 3. Quantum phase analogue

Let `V` be a complex Hilbert space and

\[
 \pi:V\setminus\{0\}\longrightarrow\operatorname{End}(V),
 \qquad \pi(\psi)=|\psi\rangle\langle\psi|.
\tag{3.1}
\]

### Theorem 3.1 — positive rank-one observation loses exactly phase

For nonzero `psi`:

1. `pi(phi)=pi(psi)` iff `phi=e^(i theta) psi` for some real `theta`;
2. as a real differential,

   \[
    \ker(d\pi_\psi)=\mathbb R\,i\psi;
   \tag{3.2}
   \]

3. a nonconstant path `e^(i theta(t)) psi` has constant positive observer `(3.1)` but nonzero
   executed phase length whenever `theta` is nonconstant.

#### Proof

Equality of the rank-one operators gives equality of their one-dimensional ranges, so
`phi=lambda psi`.  Equality of operators then gives `|lambda|=1`.  For the differential,

\[
 d\pi_\psi(v)=|v\rangle\langle\psi|+|\psi\rangle\langle v|.
\tag{3.3}
\]

Write `v=alpha psi+w` with `w` orthogonal to `psi`.  The off-diagonal blocks of `(3.3)` force
`w=0`; the remaining scalar block forces `Re(alpha)=0`.  This proves `(3.2)`.  The path statement
is immediate. `QED`

Theorem 3.1 is the smooth phase-fibre version of Theorem 2.1: positive observation retains a ray
or energy while losing its phase generator.  It also explains why exact state recurrence does not
determine executed history.

## 4. Paracyclic uncurving and the secondary source class

A parachain complex consists here of operators `(b,B,T)` with

\[
 b^2=B^2=0,\qquad bB+Bb=1-T,
\tag{4.1}
\]

with `T` commuting with the structure.  A cyclic mixed complex is the case `T=1`.

Let `(C,b,B,T)` and `(C',b',B',T')` be parachain complexes, and let
`f:C->C'` be a morphism of the underlying `b`-complexes.  Define its Connes comparison

\[
 H_f=B'f-fB
\tag{4.2}
\]

and monodromy defect

\[
 E_f=T'f-fT.
\tag{4.3}
\]

### Theorem 4.1 — target monodromy is already Connes-null-homotopic

One has the exact identity

\[
 \boxed{\ b'H_f+H_fb=-E_f.\ }
\tag{4.4}
\]

Hence vanishing of the target homotopy class of `E_f` is automatic for every underlying
`b`-chain map.  It cannot be an arithmetic selection law.

#### Proof

Using `b'f=fb`, expand:

\[
\begin{aligned}
 b'H_f+H_fb
 &= (b'B'+B'b')f-f(bB+Bb)\\
 &= (1-T')f-f(1-T)\\
 &=-(T'f-fT).
\end{aligned}
\]

This is `(4.4)`. `QED`

### Theorem 4.2 — relative Connes-lift obstruction

Let `M` be the operator complex containing `H_f`, let `A_src` be a declared subcomplex of
source-realizable homotopies, and suppose `E_f` lies in `A_src`.  Since `dH_f=-E_f`, the image
`bar(H_f)` is a cycle in `M/A_src`.  The connecting morphism for

\[
 0\longrightarrow A_{src}\longrightarrow M\longrightarrow M/A_{src}
 \longrightarrow0
\tag{4.5}
\]

satisfies

\[
 \boxed{\ \partial[\bar H_f]=-[E_f].\ }
\tag{4.6}
\]

If `[bar(H_f)]=0`, then `E_f` is a boundary produced by a source-realizable homotopy.  Target
null-homotopy alone proves no such statement.

#### Proof

Equation `(4.4)` says precisely that a lift of the quotient cycle `bar(H_f)` has differential
`-E_f` in the subcomplex.  This is the definition of the connecting morphism, proving `(4.6)`.
If `bar(H_f)=d bar(K)`, write `H_f-dK=A` with `A` a representative in `A_src`; then
`E_f=-dA`, so the boundary is source-realizable. `QED`

The relative class `[bar(H_f)]`, not the primary target defect, is the first genuinely secondary
selection datum.

## 5. Exact Riemann-source specialization

Work in the completed local ring

\[
 R=\mathbb C[[a]],\qquad q=1+a.
\tag{5.1}
\]

The physical two-leg rotation and source swap satisfy

\[
 T_q^2=q\,\mathrm{id},\qquad \tau^2=\mathrm{id},
\tag{5.2}
\]

and the landed equivariance defect obeys

\[
 T_qD+D\tau=(q-1)L.
\tag{5.3}
\]

The literal source residue on the ordinary-prime atom is

\[
 \operatorname{Res}(D u_p)=(q-1)c\,
 \varepsilon_0^{(1)}(u_p)=(q-1)c,
\qquad c\ne0.
\tag{5.4}
\]

The reflected positive Stokes energy is

\[
 E(q)=q+q^{-1}-2={(q-1)^2\over q},
 \qquad (E)=(a^2).
\tag{5.5}
\]

### Corollary 5.1 — exact source/energy/phase trichotomy

At the identity horizon `q=1`:

1. the literal cyclic source retains the weight-one conormal amplitude `[q-1]` and one absolute
   orientation line;
2. the Stokes/Witt/Fitting observer sees its squared doubled horizon `(q-1)^2`;
3. finite matrix factorizations of the unsquared potential are contractible;
4. the doubled energy has nontrivial singularity theory but cannot canonically recover the
   source coorientation;
5. paracyclic target monodromy admits a canonical Connes null-homotopy, so the live arithmetic
   datum is the relative source-lift class `(4.6)` whose boundary is `(5.4)`.

#### Proof

Items 1--2 are `(5.4)`--`(5.5)` and the cyclic anti-diagonal quotient.  Local completion at
`q=1` identifies `a=q-1` with a DVR uniformizer.  Theorems 2.1 and 4.1--4.2 give Items 3--5.
Reflection `q->q^(-1)` sends `a` to `-a` modulo `a^2` and fixes `(5.5)`, exactly matching the
involution in Theorem 2.1. `QED`

### Consequence for the live RH obstruction

This result does **not** prove `(5.4)` vanishes.  It removes three false producer classes:

1. a matrix-factorization/singularity theory of the unsquared defect is locally trivial;
2. a theory of the positive doubled defect is phase-even and cannot recover source coorientation;
3. target paracyclic null-homology is automatic and therefore cannot select a divisor.

The exact remaining object is a pre-divisor, source-normal vanishing or lift theorem for the
relative Connes class `[bar(H_f)]`, retaining the trace-one prime atom and multiplicity filtration.
Its connecting image is the already measured physical residue.  This is strictly more typed than
the phrase “make the target defect null-homologous.”

## 6. Conjecture/proof/fail ledger

1. **Curved DG/matrix factorization of the unsquared amplitude will carry selection.**
   **Failed by Theorem 2.1(2):** the horizon is smooth and every finite factorization is
   contractible.
2. **Square the amplitude and use the resulting singularity category.**
   **Failed as selector by Theorem 2.1(4)--(5):** squaring creates singularity but loses the
   `mu_2` phase/coorientation.
3. **Target paracyclic null-homology is the missing theorem.**
   **Failed by Theorem 4.1:** Connes uncurving supplies it for every target monodromy.
4. **The conormal line itself selects its support.**
   **Failed by existing internal-support preservation:** a class supported on the horizon cannot
   force an ambient section onto that horizon.
5. **A metaplectic/phase lift alone forces radial neutrality.**
   **Failed by nonunitary phase-torsor countermodels:** a phase lift can carry radial holonomy.
6. **Survivor.** Selection must be a global, source-normal compatibility of phase/exactness
   trivializations across polarizations.  Locally it is measured by `(4.6)`; globally it must be
   constrained by an independent Euler--Poisson--Gamma source identity.

## 7. Literature and scope

- Getzler's paracyclic Dold--Kan theorem identifies cyclicity with identity Dwyer--Kan monodromy
  and makes parachain normalization current: <https://arxiv.org/abs/2602.08158>.
- Curved DG modules and matrix factorizations are established parent mathematics; a current
  noncommutative treatment is <https://arxiv.org/abs/2606.10146>.
- Cyclic filtered curved `A_infinity` categories and equality-of-potential conditions occur in
  current Floer theory: <https://arxiv.org/abs/2606.12257>.

No ingredient-level novelty is claimed or required.  The result needed here is the exact joint
interpretation of the literal Riemann source residue, positive Stokes/Fitting energy, smooth versus
doubled singular horizon, and relative Connes lift.  It is an unconditional restriction on the
kind of field law that can attack the live source-dagger obstruction.

## 8. Lean-return note

No Lean code was written or built.  Later formalization could use the existing source-dagger,
Cartier/Fitting, and paracyclic modules.  First formal targets would be the DVR Smith-normal-form
factorization theorem and the abstract identity `(4.4)`; declaration names must be researched
against the local corpus before writing anything.
