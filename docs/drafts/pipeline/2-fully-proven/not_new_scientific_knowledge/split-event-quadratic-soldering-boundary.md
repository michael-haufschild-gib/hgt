# A split event has no canonical soldering; its first endpoint bridge is quadratic

- **ID:** `split-event-quadratic-soldering-boundary`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Status:** `[PAPER-PROVED] [LEAN-PROVEN] [REDISCOVERED] [BRIDGE]`
- **Parent conjecture:**
  `../../1-in-progress/actuality-fracture-weak-gravity-law.md`
- **Statement:** For the split event
  \(T:K\oplus I\to C\oplus I\), \(T(k,i)=(0,i)\), parallel source and target
  endomorphisms have exactly two unconstrained one-way off-diagonal channels
  \(b:I\to K\) and \(r:C\to I\). The bare event selects no nonzero map
  \(C\to K\), but the channels compose to \(\eta=br:C\to K\), and the
  intermediate \(I\)-connection cancels exactly from the covariant defect of
  \(\eta\).

## Theorem

Let \(R\) be a commutative ring and let \(K,I,C\) be \(R\)-modules. Define
\[
T:K\oplus I\longrightarrow C\oplus I,\qquad T(k,i)=(0,i).
\tag{1}
\]
Write arbitrary endomorphisms of the source and target in blocks:
\[
A=
\begin{pmatrix}
a&b\\
c&d
\end{pmatrix},
\qquad
B=
\begin{pmatrix}
p&q\\
r&s
\end{pmatrix},
\tag{2}
\]
where
\[
\begin{aligned}
&a:K\to K,\quad b:I\to K,\quad c:K\to I,\quad d:I\to I,\\
&p:C\to C,\quad q:I\to C,\quad r:C\to I,\quad s:I\to I.
\end{aligned}
\]
Then:

1. \(BT=TA\) if and only if
   \[
   c=0,\qquad q=0,\qquad s=d.
   \tag{3}
   \]
   Thus \(a,p,d,b,r\) are arbitrary. The event transmits \(d\), leaves the
   endpoint endomorphisms \(a,p\) independent, and permits exactly the
   off-diagonal arrows
   \[
   C\xrightarrow{\,r\,}I\xrightarrow{\,b\,}K.
   \tag{4}
   \]
2. The bare split event does not canonically select a nonzero direct endpoint
   soldering. Precisely, if \(\eta:C\to K\) satisfies
   \[
   a\eta=\eta p
   \tag{5}
   \]
   for every independent pair \(a\in\operatorname{End}(K)\) and
   \(p\in\operatorname{End}(C)\), then \(\eta=0\).
3. Given the two arrows in (4), define their quadratic endpoint bridge
   \[
   \eta=br:C\to K.
   \tag{6}
   \]
   For endpoint and intermediate endomorphisms \(a,d,p\), define
   \[
   \nabla b=ab-bd,\qquad
   \nabla r=dr-rp.
   \tag{7}
   \]
   Then the exact cancellation law is
   \[
   (\nabla b)r+b(\nabla r)
   =a(br)-(br)p.
   \tag{8}
   \]
   In particular, the intermediate endomorphism \(d\) cancels from the
   covariant defect of the composite.
4. If both arrows are covariantly constant,
   \[
   ab=bd,\qquad dr=rp,
   \tag{9}
   \]
   then \(a\eta=\eta p\). If \(\eta\) is invertible, the independent endpoint
   endomorphisms are locked by conjugacy:
   \[
   a=\eta p\eta^{-1}.
   \tag{10}
   \]

## Proof

For \((k,i)\in K\oplus I\),
\[
BT(k,i)=B(0,i)=(qi,si),
\tag{11}
\]
whereas
\[
TA(k,i)=T(ak+bi,ck+di)=(0,ck+di).
\tag{12}
\]
If \(BT=TA\), comparison at \((0,i)\) gives \(q=0\) and \(s=d\);
comparison at \((k,0)\) gives \(c=0\). Conversely these three equations make
(11) and (12) equal for every \((k,i)\). No equation contains \(a,p,b\), or
\(r\), proving part 1.

For part 2, apply (5) to the allowed independent pair \(a=0\) and
\(p=\operatorname{id}_C\). It gives \(0=\eta\).

For part 3, associativity and distributivity of composition give
\[
\begin{aligned}
(\nabla b)r+b(\nabla r)
&=(ab-bd)r+b(dr-rp)\\
&=abr-bdr+bdr-brp\\
&=a(br)-(br)p.
\end{aligned}
\tag{13}
\]
The two occurrences of the intermediate action \(d\) cancel with opposite
signs. This proves (8).

Under (9), the left side of (8) vanishes, so \(a\eta=\eta p\). If \(\eta\)
is invertible, right composition by \(\eta^{-1}\) gives (10). This proves
part 4. \(\square\)

## Hostile novelty audit

`[NOT NEW MATHEMATICS]`

The classification is elementary block algebra for a two-term split complex.
Elgueta computes the much richer 2-group of self-equivalences and chain
homotopies of arbitrary split chain complexes and proves that its equivalence
class depends only on homology:
<https://arxiv.org/abs/1012.1964>.

Equation (8) is the standard covariant Leibniz rule for a composite of bundle
maps. The same general mechanism underlies quiver connections and
superconnections. It must not be advertised as a new mathematical law.

The physical surroundings are occupied too. Krasnov derives gravity and
Yang--Mills sectors from spontaneous symmetry breaking of one gauge
connection:
<https://arxiv.org/abs/1112.5097>. Złośnik, Urban, Marzola, and Koivisto
construct a pre-geometric Lorentz gauge theory in which a spacetime metric
exists only in the broken phase:
<https://arxiv.org/abs/1807.01100>.

## Positive survivor for the open physics core

The theorem gives a strict boundary, not a gravity theory:

1. Kernel and cokernel dimensions do not themselves produce a tetrad,
   solder form, or metric.
2. A nonzero direct \(C\to K\) identification must be extra dynamical data or
   arise from additional event channels; it cannot be canonical under the
   independent endpoint symmetries.
3. With no extra carrier, the first type-correct endpoint bridge made from the
   event's invisible off-diagonal data is the length-two composite \(br\), so
   it is quadratic in those channels.
4. The common transmitted connection cancels from the endpoint covariant
   defect. A nondegenerate \(br\) would lock the endpoint symmetries; a
   degenerate \(br\) would leave an explicitly classifiable residual
   symmetry.

This sharpens the parent conjecture's open core. Any proposed
actuality-to-gravity derivation must explain why nature supplies \(b\) and
\(r\), why \(br\) becomes nondegenerate with Lorentzian reality, how such
local composites glue, and why their gluing defect obeys Einstein dynamics.
None follows from this theorem.

## Formalization

The exact targets are now unconditionally Lean-proven in
`../../../../../formal/GaloisForLFunctions/HTGeometry/EventSecondOrderSoldering.lean`:

1. the block classification (3);
2. the universal-soldering no-go (5);
3. the cancellation identity (8);
4. the conjugacy corollary (10).

No statement about actuality, weak isospin, spacetime, gravity, dynamics, or
physical novelty is part of the formal theorem. The stage-3 certificate is
`../../3-formalized/split-event-quadratic-soldering-boundary.md`.

## Gates

- [x] 0 → 1: exact source-independent theorem extracted from the fracture
  obstruction
- [x] 1 → 2: dependency-closed proof written
- [x] hostile audit classifies theorem as rediscovered bridge mathematics
- [x] 2 → 3: exact theorem formalized unconditionally in Lean
- [ ] physical parent derives the channels, Lorentzian soldering, dynamics,
  and a finite prediction

## Log

- 2026-07-29 — classified all parallel block endomorphisms, proved the
  no-canonical-soldering boundary, and extracted the quadratic
  transmitted-channel cancellation law.
- 2026-07-29 — formalized the exact classification, no-go, cancellation, and
  conjugacy corollary in Lean without custom axioms.
