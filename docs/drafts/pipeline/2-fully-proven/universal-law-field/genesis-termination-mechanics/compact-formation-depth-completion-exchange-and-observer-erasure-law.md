# Compact formation depth, completion exchange, and observer erasure

- **ID:** ULF-GTM-3
- **Stage:** 2-fully-proven
- **Type:** UNIVERSAL LAW-FIELD MECHANISM THEOREM
- **Status:** [PAPER-PROVED] [DEPENDENCY-CLOSED] [MECHANISM NOT OBJECT]
  [FINITE-FORMATION/COMPLETION EXCHANGE] [PRESENTATION-COARSE]
  [OBSERVER ERASURE] [NOT RH] [LEAN-FORMALIZED]

## 1. Why this theorem is needed

ULF-GTM-2 proves that arbitrary finite compositions of finitary formations remain finitary.
It leaves one live genesis mechanism: a completion may contain a law that no finite formation
history produces.  Bare compactness escape does not explain why the source history must become
long.  The theorem below identifies the exact resource and the exact exchange failure.

The primitive is a mechanism, not a route object.  A finite family of continuous formations acts
on one compact law space.  Completion commutes with every bounded formation depth.  Therefore any
failure at saturation is forced into the unbounded-depth tail.

## 2. Formation action and depth

Let \(X\) be a compact Hausdorff space, let \(I\) be finite, and let

\[
  \Phi=(\phi_i:X\to X)_{i\in I}
\]

be continuous self-maps.  For a word \(w=i_1\cdots i_k\in I^*\), write
\(\phi_w=\phi_{i_k}\circ\cdots\circ\phi_{i_1}\); the empty word acts as the identity.
For \(A\subseteq X\), define

\[
  R_d^\Phi(A)
    =\bigcup_{|w|\le d}\phi_w(A),
  \qquad
  R_\infty^\Phi(A)
    =\bigcup_{d<\infty}R_d^\Phi(A).
\tag{GTM3.1}
\]

The completed-law boundary is

\[
  \Delta_\Phi(A)
   =\overline{R_\infty^\Phi(A)}
      \setminus R_\infty^\Phi(\overline A).
\tag{GTM3.2}
\]

It compares `form then complete` with `complete the input then form finitely many times`.

## 3. Main theorem

### Theorem 3.1 — finite-depth formation/completion exchange

For every \(A\subseteq X\) and every \(d\in\mathbb N\),

\[
  \boxed{
  \overline{R_d^\Phi(A)}=R_d^\Phi(\overline A).}
\tag{GTM3.3}
\]

In particular, no law is born by completion at any bounded formation depth.

#### Proof

There are finitely many words of length at most \(d\).  Every \(\phi_w\) is continuous.  For each
word, continuity gives

\[
  \phi_w(\overline A)\subseteq\overline{\phi_w(A)}.
\]

Conversely \(\phi_w(\overline A)\) is compact and therefore closed in the Hausdorff space \(X\);
since it contains \(\phi_w(A)\), it contains \(\overline{\phi_w(A)}\).  Thus

\[
  \overline{\phi_w(A)}=\phi_w(\overline A).
\]

Closure commutes with a finite union, so taking the union over all words of length at most \(d\)
proves (GTM3.3).  \(\square\)

### Theorem 3.2 — least closed executable law space

The set

\[
  C_\Phi(A)=\overline{R_\infty^\Phi(A)}
\tag{GTM3.4}
\]

is the least closed subset of \(X\) that contains \(A\) and is invariant under every \(\phi_i\).

#### Proof

It is closed and contains \(A\).  For each \(i\), compactness and continuity give

\[
  \phi_i(C_\Phi(A))
   =\phi_i(\overline{R_\infty^\Phi(A)})
   =\overline{\phi_i(R_\infty^\Phi(A))}
   \subseteq C_\Phi(A),
\]

because applying one more generator preserves \(R_\infty^\Phi(A)\).  Every closed invariant set
containing \(A\) contains every finite word image and hence its closure.  \(\square\)

### Theorem 3.3 — exact infinite-depth boundary formula

The completed-law boundary is exactly

\[
  \boxed{
  \Delta_\Phi(A)
   =\overline{\bigcup_dR_d^\Phi(A)}
      \setminus\bigcup_d\overline{R_d^\Phi(A)}.}
\tag{GTM3.5}
\]

Thus completion can create a new law only by failing to commute with the filtered union over
formation depth.

#### Proof

By Theorem 3.1,

\[
  R_\infty^\Phi(\overline A)
   =\bigcup_dR_d^\Phi(\overline A)
   =\bigcup_d\overline{R_d^\Phi(A)}.
\]

Substitute this identity into (GTM3.2).  \(\square\)

### Theorem 3.4 — depth divergence near every new completed law

Let \(x\in\Delta_\Phi(A)\).  For every neighbourhood \(U\) of \(x\) and every finite depth \(d\),

\[
  \boxed{
  U\cap\bigl(R_\infty^\Phi(A)\setminus R_d^\Phi(A)\bigr)\ne\varnothing.}
\tag{GTM3.6}
\]

If \(X\) is metrizable, there is a sequence \(x_d\to x\) with
\(x_d\in R_\infty^\Phi(A)\setminus R_d^\Phi(A)\).

#### Proof

Suppose some neighbourhood \(U\) and depth \(d\) violate (GTM3.6).  Then
\(U\cap R_\infty^\Phi(A)\subseteq R_d^\Phi(A)\).  Since
\(x\in\overline{R_\infty^\Phi(A)}\), every neighbourhood of \(x\), after intersecting with
\(U\), meets \(R_d^\Phi(A)\).  Hence

\[
  x\in\overline{R_d^\Phi(A)}=R_d^\Phi(\overline A)
  \subseteq R_\infty^\Phi(\overline A),
\]

contrary to \(x\in\Delta_\Phi(A)\).  In a metric space choose \(x_d\) in (GTM3.6) inside the
ball of radius \(1/(d+1)\).  \(\square\)

### Corollary 3.5 — bounded-depth saturation forbids completed-law birth

If \(R_\infty^\Phi(A)=R_D^\Phi(A)\) for some finite \(D\), then

\[
  \Delta_\Phi(A)=\varnothing.
\tag{GTM3.7}
\]

#### Proof

Theorem 3.1 gives

\[
  \overline{R_\infty^\Phi(A)}
   =\overline{R_D^\Phi(A)}
   =R_D^\Phi(\overline A)
   \subseteq R_\infty^\Phi(\overline A).
\]

The reverse containment follows from Theorem 3.2 because
\(\overline{R_\infty^\Phi(A)}\) is closed, invariant, and contains \(\overline A\).  \(\square\)

## 4. Presentation invariance

Raw word depth depends on generators.  The boundary and divergence law do not.

Let \(\Psi=(\psi_j)_{j\in J}\) be another finite continuous generating family on \(X\).  Suppose
each \(\phi_i\) is a \(\Psi\)-word of length at most \(a\), and each \(\psi_j\) is a
\(\Phi\)-word of length at most \(b\), with \(a,b\ge1\).

### Theorem 4.1 — bounded-dictionary quasi-isometry

For every \(A\subseteq X\) and \(d\in\mathbb N\),

\[
  R_d^\Phi(A)\subseteq R_{ad}^\Psi(A),
  \qquad
  R_d^\Psi(A)\subseteq R_{bd}^\Phi(A).
\tag{GTM3.8}
\]

Consequently

\[
  R_\infty^\Phi(A)=R_\infty^\Psi(A),
  \qquad
  \boxed{\Delta_\Phi(A)=\Delta_\Psi(A).}
\tag{GTM3.9}
\]

If \(y\) is finitely reachable and \(\delta_\Phi(y;A)\), \(\delta_\Psi(y;A)\) are its minimal
word depths, then

\[
  \delta_\Psi(y;A)\le a\,\delta_\Phi(y;A),
  \qquad
  \delta_\Phi(y;A)\le b\,\delta_\Psi(y;A).
\tag{GTM3.10}
\]

#### Proof

Replace every letter of a \(\Phi\)-word by its chosen \(\Psi\)-word.  Length grows by at most the
factor \(a\), proving the first inclusion; the reverse substitution proves the second.  Taking
unions over \(d\) proves equality of reachable sets, hence equality of their closures and of
(GTM3.2).  Apply the two inclusions at minimal depth to obtain (GTM3.10).  \(\square\)

If the two finite families generate the same transformation monoid, bounded dictionaries exist
automatically: choose one word for each generator and take the maximum of finitely many lengths.
Therefore the boundary depends on the generated formation monoid, while depth divergence is a
coarse invariant of any finite generating presentation.

## 5. Observer law

Let \((Y,\Psi)\) be another compact Hausdorff formation system with the same finite index set, and
let \(q:X\to Y\) be continuous with

\[
  q\circ\phi_i=\psi_i\circ q
  \qquad(i\in I).
\tag{GTM3.11}
\]

### Theorem 5.1 — observers can erase but cannot create completion boundaries

For every \(d\) and \(A\subseteq X\),

\[
  q(R_d^\Phi(A))=R_d^\Psi(q(A)),
\tag{GTM3.12}
\]

and

\[
  q\bigl(\overline{R_\infty^\Phi(A)}\bigr)
   =\overline{R_\infty^\Psi(q(A))},
  \qquad
  q\bigl(R_\infty^\Phi(\overline A)\bigr)
   =R_\infty^\Psi(\overline{q(A)}).
\tag{GTM3.13}
\]

Hence

\[
  \boxed{
  \Delta_\Psi(q(A))\subseteq q(\Delta_\Phi(A)).}
\tag{GTM3.14}
\]

If \(q\) is injective, equality holds in (GTM3.14).  A noninjective observer may erase the whole
boundary; the constant map to a one-point system does so.

#### Proof

Equation (GTM3.12) follows by induction on word length from (GTM3.11).  A continuous map from a
compact space to a Hausdorff space sends compact sets to closed sets.  As in Theorem 3.1, this gives
\(q(\overline S)=\overline{q(S)}\) for every \(S\subseteq X\), and (GTM3.13) follows.

Write \(C=\overline{R_\infty^\Phi(A)}\) and
\(D=R_\infty^\Phi(\overline A)\).  Then the target boundary is \(q(C)\setminus q(D)\).  If
\(y\in q(C)\setminus q(D)\), some \(x\in C\) maps to \(y\), and no such \(x\) lies in \(D\);
therefore \(y\in q(C\setminus D)\).  If \(q\) is injective, it preserves set difference and the
inclusion is equality.  \(\square\)

## 6. Exact calibrations and hostile boundaries

### 6.1 Compact finite system with nonempty boundary

Let \(X=S^1\), let \(\phi(z)=e^{2\pi i\alpha}z\) for irrational \(\alpha\), and let \(A=\{1\}\).
Kronecker density gives

\[
  \overline{R_\infty(A)}=S^1,
  \qquad
  R_\infty(\overline A)=R_\infty(A).
\]

Thus \(\Delta(A)=S^1\setminus R_\infty(A)\), and every new completed phase requires unbounded
word depth.  A constant or phase-blind observer erases it.

### 6.2 Finite signature is load-bearing

Take \(X=\{0\}\cup\{1/n:n\ge1\}\), \(A=\{1\}\), and infinitely many continuous constant maps
\(\phi_n(x)=1/n\).  Then \(R_1(A)\) contains every \(1/n\), so its closure contains \(0\), while
\(R_1(\overline A)\) does not.  Finite-depth exchange fails at depth one.

### 6.3 Compactness is load-bearing

Take \(X=\mathbb R\), \(A=\{1,2,3,\ldots\}\), and
\(\phi(x)=1/(1+x^2)\).  The set \(A\) is closed, but \(0\) lies in
\(\overline{R_1(A)}\setminus R_1(\overline A)\).

### 6.4 Continuity is load-bearing

On \([0,1]\), let \(A=\{1/(n+2):n\ge0\}\), set \(\phi(0)=1\), and set \(\phi(x)=0\) for
\(x>0\).  Then \(1\in\phi(\overline A)\) but \(1\notin\overline{\phi(A)}\).

### 6.5 Unbounded depth is necessary, not sufficient

On \(X=\{0\}\cup\{1/n:n\ge1\}\), let \(\phi(0)=0\) and
\(\phi(1/n)=1/(n+1)\).  From \(A=\{0,1\}\), new points occur at every finite depth, but
\(R_\infty(A)=X\) is already closed, so \(\Delta(A)=\varnothing\).

These countermodels exclude five false strengthenings: arbitrary signatures, noncompact carriers,
discontinuous formations, presentation-exact numerical depth, and the converse
`unbounded depth implies nonempty boundary`.

## 7. Field-law consequence

The theorem turns one speculative rabbit hole of Law-Formation Mechanics into an exact law:

> **Finite-depth exchange / infinite-history birth law.** For finite continuous formations on a
> compact law space, formation and completion commute at every bounded word depth.  A genuinely
> completion-born law is precisely a filtered-union exchange residue and forces formation depth to
> diverge in every effective approximation.  Its existence is invariant under finite changes of
> generators.  Equivariant observation may erase this residue but cannot create one.

This law classifies, rather than identifies, the five wall types in the current frontier:

| wall mechanism | theorem-level diagnosis |
|---|---|
| singular descent | continuity or admission needed for finite-depth exchange fails |
| all-prime/cofinal transport | effective histories leave every bounded formation depth, or the generator family is not finite/compact |
| adaptive orientation | the formation family changes with the current state or null flag, so one fixed action monoid is inadequate |
| whole-space coercivity | the completion boundary exists but its depth/cost sublevels are not proper |
| positive carrier/observer | a noninjective positive observer can erase a source boundary and cannot reconstruct it downstream |

This is not an RH theorem and does not merge proof routes.  It gives a route-independent falsifier:
any proposed completed-law producer built from one compact carrier, finitely many continuous
formations, and uniformly bounded formation depth has empty completion boundary.  A live producer
must exhibit unbounded history, an infinite/noncompact signature, discontinuity or admission loss,
a state-dependent formation law, or a genuinely different completion.

## 8. Parent mathematics and exact residue

The ingredients belong to established mathematics:

- compact semigroup actions and orbit closures;
- topological universal algebra over finite or compact signatures;
- algebraic/finitary closure operators and Scott-continuous consequence;
- word metrics under finite changes of generators.

Relevant parents include Schneider--Zumbrägel,
*Profinite algebras and affine boundedness*, arXiv:1506.00212; Kilpack,
*The lattice of algebraic closure operators*, arXiv:1411.6497; and Carvalho--Rodrigues--Varandas,
*Quantitative recurrence for free semigroup actions*, arXiv:1612.07082.

The field contribution sought here is their mechanism-level conjunction: finite formation depth is
the exact exchange-safe sector; completion birth is an infinite-history residue; finite-generator
changes preserve its coarse depth; and observer kernels can only erase it.  No priority claim is
made for the individual ingredients.

## 9. Lean certification

`GaloisForLFunctions.HTGeometry.ConstitutiveFormationCompletionExchange` certifies, without
project axioms:

1. bounded-depth reach for a finite family of continuous self-maps;
2. finite-depth closure exchange on compact Hausdorff spaces;
3. exact boundary formula and depth-divergence theorem;
4. bounded-saturation no-birth corollary;
5. bounded-dictionary reach inclusions and boundary invariance;
6. equivariant-observer boundary inclusion and injective equality;
7. the finite-signature sharp countermodel on the one-point compactification of `ℕ`.

Direct foreground elaboration, forbidden-token lint, axiom audit, and the final Universal Law
Field umbrella build all pass. Every audited capstone depends only on `propext`,
`Classical.choice`, and `Quot.sound`. Declaration-level certificate is recorded in matching
Stage-3 card.

## Log

- 2026-08-09 — compactness-escape alone rejected as an already-formalized RBD/Kőnig law.
- 2026-08-09 — stronger finite-depth exchange, presentation invariance, and observer-erasure
  mechanism proved on paper.
