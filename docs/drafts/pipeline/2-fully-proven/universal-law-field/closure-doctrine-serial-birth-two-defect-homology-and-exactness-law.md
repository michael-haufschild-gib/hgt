# Closure-doctrine serial birth, two-defect homology, and exactness law

- **ID:** ULF-CHM-1
- **Stage:** 2-fully-proven
- **Type:** ROUTE-INDEPENDENT MECHANISM THEOREM
- **Statement:** Every enlargement doctrine turns serial law birth into a canonical complex whose
  source and target homology are independent; exactness survives exactly when both vanish.
- **Status:** [PAPER-PROVED] [DEPENDENCY-CLOSED] [MECHANISM NOT OBJECT]
  [TWO-DEFECT HOMOLOGY] [EXACT CONVERSE] [INDEPENDENCE CELLS] [LEAN-CERTIFIED]
  [AXIOM-AUDITED] [UMBRELLA-BUILT] [NOT RH]

## 1. Doctrine-layered setup

Let \(\Bbbk\) be a field, \(T:K\to A\) a linear carrier, and let

\[
R\subseteq K,\qquad P\subseteq Q\subseteq A
\]

be subspaces satisfying

\[
R\subseteq T^{-1}P,qquad \operatorname{im}T\subseteq Q.
\tag{CHM.1}
\]

Interpret \(R,P,Q\) as the layers discarded by an enlargement, admission, completion, or
coarse-observation doctrine. Define

\[
i:K/R\longrightarrow A/P,\quad i([k])=[Tk],
\qquad
p:A/P\longrightarrow A/Q,\quad p([a])=[a].
\tag{CHM.2}
\]

Both maps are well-defined by (CHM.1), and \(p\circ i=0\).

## 2. Two-defect completion-homology theorem

### Theorem 2.1

The complex (CHM.2) obeys:

1. its source homology is

   \[
   \boxed{\ker i=\frac{T^{-1}P}{R};}
   \tag{CHM.3}
   \]

2. the primary transition \(p\) is surjective;
3. exactness at the middle term holds exactly when

   \[
   \boxed{Q=\operatorname{im}T+P;}
   \tag{CHM.4}
   \]

4. its target homology is therefore canonically represented by

   \[
   \boxed{H_{\mathrm{tgt}}=
      \frac{Q}{\operatorname{im}T+P};}
   \tag{CHM.5}
   \]

5. the sequence is short exact iff both defect identities hold:

   \[
   \boxed{
   T^{-1}P=R,qquad Q=\operatorname{im}T+P.}
   \tag{CHM.6}
   \]

### Proof

A quotient class \([k]\in K/R\) lies in \(\ker i\) iff \(Tk\in P\), exactly the image of
\(T^{-1}P\) in \(K/R\). Thus \(i\) is injective iff \(T^{-1}P=R\).

Surjectivity of \(p\) is immediate from quotient representatives. Since
\(\operatorname{im}T\subseteq Q\), \(\operatorname{im}i\subseteq\ker p\). Conversely, let
\([a]\in\ker p\). Then \(a\in Q\). It is in \(\operatorname{im}i\) precisely when

\[
a=Tk+u
\]

for some \(k\in K\) and \(u\in P\). Hence every kernel class is attained precisely when
\(Q\subseteq\operatorname{im}T+P\). The reverse inclusion follows from
\(\operatorname{im}T\subseteq Q\) and \(P\subseteq Q\), proving (CHM.4). Quotienting the two
middle layers gives (CHM.5), and conjunction with source injectivity proves (CHM.6).
\(\square\)

## 3. Topological closure specialization

Let \(E,K,A\) be seminormed vector spaces and let

\[
E\xrightarrow{S}K\xrightarrow{T}A
\tag{CHM.7}
\]

be continuous linear maps. Put

\[
R=\overline{\operatorname{im}S+\ker T},\qquad
P=\overline{\operatorname{im}(TS)},\qquad
Q=\overline{\operatorname{im}T}.
\tag{CHM.8}
\]

### Theorem 3.1

The containments (CHM.1) hold, so (CHM.2) is canonical. Its Hausdorff-separated serial sequence is
short exact iff

\[
\boxed{
T^{-1}\overline{\operatorname{im}(TS)}
=\overline{\operatorname{im}S+\ker T}}
\tag{CHM.9}
\]

and

\[
\boxed{
\overline{\operatorname{im}T}
=\operatorname{im}T+\overline{\operatorname{im}(TS)}.}
\tag{CHM.10}
\]

### Proof

The second and third containments follow from
\(\operatorname{im}(TS)\subseteq\operatorname{im}T\) and extensivity of closure. For the first,
\(\operatorname{im}S+\ker T\) lies in
\(T^{-1}\overline{\operatorname{im}(TS)}\). The latter is closed because \(T\) is continuous,
so it contains the closure of the former. Apply Theorem 2.1. \(\square\)

## 4. Mechanism interpretation

Define

\[
H_{\mathrm{src}}
=\frac{T^{-1}\overline{\operatorname{im}(TS)}}
       {\overline{\operatorname{im}S+\ker T}},
\qquad
H_{\mathrm{tgt}}
=\frac{\overline{\operatorname{im}T}}
       {\operatorname{im}T+\overline{\operatorname{im}(TS)}}.
\tag{CHM.11}
\]

- \(H_{\mathrm{src}}\) records **ghost secondary laws**: nonzero after inner completion but killed
  after composite observation.
- \(H_{\mathrm{tgt}}\) records **unattained limit laws**: visible in the closed outer kernel but
  not produced by an actual carrier modulo the completed composite layer.

These are not two signs of one scalar curvature. They occur at different objects of the complex
and require opposite repairs.

## 5. Independence laboratories

The two identities in (CHM.6) are logically independent even in finite-dimensional linear cells.

### Cell A: source defect only

Let \(T=\mathrm{id}_{\mathbb R^2}\), let \(R\) be the horizontal axis, and let
\(P=Q=\mathbb R^2\). Then

\[
T^{-1}P=\mathbb R^2\ne R,
\]

while \(Q=\operatorname{im}T+P\). Source homology is nonzero and target homology vanishes.

### Cell B: target defect only

Let \(T:\mathbb R\to\mathbb R^2\) be \(T(x)=(x,0)\), let \(R=P=0\), and let
\(Q=\mathbb R^2\). Then

\[
T^{-1}P=0=R,
\]

but \(Q\ne\operatorname{im}T+P\). Source homology vanishes and target homology is nonzero.

These are doctrine-layer cells: they prove independence of the two mechanism identities, not that
every such layer triple is generated by norm closure.

### Genuine topological target defect

The certified Gamma radial reporter on \(\ell^2\) is continuous, compact, injective, has dense
proper range, and is not surjective. Take \(S=0\). Then

\[
R=0,qquad P=0,qquad Q=\ell^2.
\]

Thus (CHM.9) holds while (CHM.10) fails. This is a literal completion-created unattained-limit
sector, not only an abstract layer assignment.

## 6. Consequences for the field

1. **Completion has homology.** It does not merely turn equality into approximation.
2. **Serial exactness needs two exchange laws.** Closedness of one range is not a complete answer.
3. **Source and target failures are independent.** One scalar defect cannot classify them.
4. **Nonstrictness is located.** Source nonstrictness is a kernel of the first map; target
   nonstrictness is homology at the middle object.
5. **Algebraic ULF-PSB-1 is the zero-homology chamber.** Taking raw layers makes both identities
   tautological.

## 7. Relation to existing mathematics

Ingredients are standard quotient exactness, strict/non-strict morphisms in quasi-abelian
analysis, and closure of subspaces. Field content is the two-location interpretation as law-birth
homology and its exact converse. No priority or novelty claim is required.

## 8. Sharp scope

This theorem does not yet prove:

- a source-generated topology or closure doctrine;
- completeness or continuity of the induced quotient maps;
- that either homology group vanishes in a particular RH route;
- a nonlinear, torsorial, or higher-categorical replacement;
- a law for three or more serial stages.

## 9. Falsifiers

The theorem is falsified by any doctrine-layered carrier for which:

1. \(\ker i\ne T^{-1}P/R\);
2. \(p\) is not surjective;
3. middle exactness holds while \(Q\ne\operatorname{im}T+P\), or conversely;
4. both identities in (CHM.6) hold but the sequence is not short exact;
5. one of the finite independence cells fails.

The proof and Lean certificate exclude all five.

## 10. Lean certificate

Module `HTGeometry.ConstitutiveClosureDoctrineHomology` certifies the doctrine maps, source-kernel
formula, complex identity, exact-middle converse, short-exactness equivalence, topological closure
specialization, independent finite cells, and the Gamma target-defect realization. Direct
foreground elaboration passes. Source-level axiom prints on all headline declarations report only
`propext`, `Classical.choice`, and `Quot.sound`. Final Universal Law Field umbrella build succeeds
with `11,545` jobs.
