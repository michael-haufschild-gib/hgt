# Irreversible event coupling is square-zero and vanishes in the symmetry quotient

- **ID:** `event-square-zero-unification-boundary`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / NONSEMISIMPLE UNIFICATION BOUNDARY
- **Parent:** `../../1-in-progress/actuality-fracture-weak-gravity-law.md`
- **Scientific status:** `[PAPER-PROVED] [REDISCOVERED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** Upper-triangular event couplings form a square-zero ideal. Quotienting them out
  leaves the direct product of endpoint symmetry algebras; their only nontrivial first-order role
  is the bimodule action linking the two diagonal sectors.

## Goal

Test whether the noninvertible event interface supplies the precise nonsemisimple loophole left by
the McGlinn--O'Raifeartaigh--Coleman--Mandula boundary.

The theorem is ordinary block algebra. Its value is diagnostic: it identifies exactly where
non-product coupling can live and exactly what is lost when one retains only invertible
semisimple symmetry.

## Setup

Let \(R\) be a commutative ring and let \(K,I\) be \(R\)-modules. For

\[
a\in\operatorname{End}_R(K),\qquad
d\in\operatorname{End}_R(I),\qquad
b\in\operatorname{Hom}_R(I,K),
\]

define

\[
D_{a,d}(k,i)=(ak,di),\qquad
N_b(k,i)=(bi,0),\qquad
U_{a,b,d}=D_{a,d}+N_b.                                             \tag{1}
\]

The \(U_{a,b,d}\) are precisely the upper-triangular endomorphisms of \(K\oplus I\).

## Theorem A: square-zero event ideal

For all \(b,c:I\to K\),

\[
N_bN_c=0.                                                          \tag{2}
\]

Moreover,

\[
D_{a,d}N_b=N_{ab},\qquad
N_bD_{a,d}=N_{bd}.                                                  \tag{3}
\]

Hence

\[
\mathcal N:=\{N_b:b\in\operatorname{Hom}_R(I,K)\}
\]

is a square-zero two-sided ideal in the algebra

\[
\mathcal U:=\{U_{a,b,d}\}.
\]

### Proof `[PROVED HERE]`

For \((k,i)\in K\oplus I\),

\[
N_bN_c(k,i)=N_b(ci,0)=(b0,0)=(0,0),
\]

proving `(2)`. Likewise,

\[
D_{a,d}N_b(k,i)=D_{a,d}(bi,0)=(abi,0)=N_{ab}(k,i),
\]

and

\[
N_bD_{a,d}(k,i)=N_b(ak,di)=(bdi,0)=N_{bd}(k,i).
\]

Every product with one factor in \(\mathcal N\) therefore remains in \(\mathcal N\), while every
product of two elements of \(\mathcal N\) is zero. \(\square\)

## Theorem B: exact multiplication and commutator laws

For two upper event maps,

\[
U_{a,b,d}U_{a',b',d'}
=U_{aa',\,ab'+bd',\,dd'}.                                         \tag{4}
\]

Consequently,

\[
[U_{a,b,d},U_{a',b',d'}]
=U_{[a,a'],\,ab'+bd'-a'b-b'd,\,[d,d']}.                            \tag{5}
\]

In particular,

\[
[U_{a,b,d},N_c]=N_{ac-cd},\qquad [N_b,N_c]=0.                      \tag{6}
\]

### Proof `[PROVED HERE]`

Using `(1)`--`(3)` and \(D_{a,d}D_{a',d'}=D_{aa',dd'}\),

\[
\begin{aligned}
U_{a,b,d}U_{a',b',d'}
&=(D_{a,d}+N_b)(D_{a',d'}+N_{b'})\\
&=D_{aa',dd'}+N_{ab'}+N_{bd'}+0,
\end{aligned}
\]

which is `(4)`. Subtracting the formula with primed and unprimed variables exchanged gives `(5)`.
Setting the appropriate diagonal or off-diagonal terms to zero gives `(6)`. \(\square\)

## Theorem C: the symmetry quotient splits exactly

Define

\[
\pi:\mathcal U\longrightarrow
\operatorname{End}_R(K)\times\operatorname{End}_R(I),
\qquad
\pi(U_{a,b,d})=(a,d).                                               \tag{7}
\]

Then \(\pi\) is a surjective algebra homomorphism with

\[
\ker\pi=\mathcal N.                                                 \tag{8}
\]

Therefore

\[
\mathcal U/\mathcal N
\cong \operatorname{End}_R(K)\times\operatorname{End}_R(I).         \tag{9}
\]

### Proof `[PROVED HERE]`

Formula `(4)` shows multiplicativity; addition and scalar compatibility are componentwise.
Surjectivity follows from \((a,d)=\pi(U_{a,0,d})\). Equation `(7)` vanishes exactly when
\(a=d=0\), in which case \(U_{a,b,d}=N_b\). The algebraic first isomorphism theorem gives `(9)`.
\(\square\)

## Lower-triangular companion and quadratic survivor

For the split event

\[
T:K\oplus I\longrightarrow C\oplus I,\qquad T(k,i)=(0,i),
\]

parallel block maps contain:

- the source upper channel \(b:I\to K\); and
- the target lower channel \(r:C\to I\).

Each channel, extended by zero on its own two-block carrier, is square-zero by the same proof.
They live on opposite sides of the noninvertible event and therefore do not multiply as
endomorphisms of one fixed carrier. Their typed length-two composite

\[
C\xrightarrow{r}I\xrightarrow{b}K,\qquad \eta=br,                  \tag{10}
\]

need not vanish. The previously formalized cancellation law shows that the intermediate
connection cancels from the covariant defect of `(10)`.

Thus first-order nonsemisimple coupling and second-order endpoint soldering are distinct:

```text
one off-diagonal event channel
  -> square-zero radical direction

oppositely typed channels across one noninvertible event
  -> potentially nonzero quadratic endpoint bridge.
```

## External frontier

`[LITERATURE]` Coleman--Mandula proves local direct-product symmetry under its connected
S-matrix, particle-spectrum, analyticity, nontrivial-scattering, and regularity hypotheses.
It does not classify arbitrary gauge redundancies, noninvertible processes, curved backgrounds,
or event categories.

`[LITERATURE]` O'Raifeartaigh's finite-dimensional Lie-algebra analysis uses Levi decomposition
to constrain extensions of the Poincaré algebra.

`[LITERATURE]` László exhibits conservative extensions in which a noncompact nilpotent internal
part permits an indecomposable bosonic extension while the compact gauge symmetry remains in the
Levi factor. Thus “every bosonic extension splits” is false without a compactness or
semisimplicity restriction on the complete internal kernel.

`[LITERATURE]` Nesti--Percacci graviweak models use enlarged and broken gauge structure to relate
chiral Lorentz and weak sectors.

The present block theorem is standard mathematics and is not a new loophole. It shows that the HGT
event interface lands exactly in the already known nonsemisimple class.

## Exact physical boundary

The theorem kills two claims:

1. the event interface unifies forces merely because one upper-triangular algebra contains both
   diagonal sectors; after quotient by its square-zero ideal, they are an exact product;
2. the off-diagonal event channel is itself another ordinary force curvature; its self-bracket is
   identically zero.

The strongest positive survivor is:

> Any genuine coupling supplied by the noninvertible event must live in the square-zero
> first-order bimodule action or in a typed quadratic composite across the event. It cannot be
> read from the semisimple symmetry quotient.

This yields a sharper representation lesson:

> **If actuality unifies forces, the unification lives in irreversible nonunits erased by the
> symmetry group, not in a larger invertible symmetry.**

That sentence is a derived bridge, not the frozen physical conjecture.

## No-go closure

- **Exact killing theorem/mechanism:** the diagonal reporter has square-zero kernel and exact
  direct-product quotient.
- **Strongest positive survivor:** the radical is a nontrivial bimodule under both endpoint
  algebras, and oppositely typed event channels can form a nonzero quadratic bridge.
- **New insight:** invertible symmetry sees separated forces; the candidate unified datum is the
  noninvertible event and its second-order soldering, not an exceptional group containing several
  subgroups.
- **Status:** dependency-closed paper proof; parent block algebra; unconditional Lean
  formalization of `(2)`--`(9)` completed and audited. Existing
  `EventSecondOrderSoldering.lean` proves the typed quadratic cancellation law.

## What this does not prove

Nothing here selects the event map, exceptional representation, Lorentzian signature,
\(S(U(2)\times U(3))\), quantum amplitudes, a manifold, a connection, Einstein dynamics, or a
finite prediction. Calling \(\mathcal N\) “actuality” would be relabelling unless a physical
principle derives it.

## Sources

- S. Coleman and J. Mandula, *All Possible Symmetries of the S Matrix*, Physical Review **159**
  (1967), 1251--1256, DOI: 10.1103/PhysRev.159.1251.
- L. O'Raifeartaigh, *Lorentz Invariance and Internal Symmetry*, Physical Review **139** (1965),
  B1052, DOI: 10.1103/PhysRev.139.B1052.
- A. László, *Unification mechanism for gauge and spacetime symmetries*, Journal of Physics A
  **50** (2017), 115401, arXiv:1512.03328.
- A. László, *Possible alternative mechanism to SUSY: conservative extensions of the Poincaré
  group*, in *Quantum Theory and Symmetries* (2018), arXiv:1801.03463.
- F. Nesti and R. Percacci, *Graviweak Unification*, Journal of Physics A **41** (2008), 075405,
  arXiv:0706.3307.

## Gates

- [x] 0 → 1: exact ordinary-extension discriminator stated
- [x] 1 → 2: complete block-algebra proof and literature boundary
- [x] 2 → 3: square-zero, multiplication, commutator, and bimodule laws Lean-proved
- [ ] 3 → 4: not a publication target; parent-theory bridge only

## Log

- 2026-07-29 — Coleman--Mandula audit replaced the false blanket splitting claim with the exact
  nonsemisimple loophole. The split-event interface supplies square-zero off-diagonal directions;
  the symmetry quotient splits, while typed quadratic soldering survives outside it.
