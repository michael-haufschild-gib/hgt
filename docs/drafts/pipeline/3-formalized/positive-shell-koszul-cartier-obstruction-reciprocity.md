# Positive shell Koszul--Cartier obstruction algebra

- **ID:** `positive-shell-koszul-cartier-obstruction-reciprocity`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / SOURCE-CONORMAL BRIDGE
- **Source:** `positive-hypertranscendental-riemann-divisor-frame`
- **Scientific status:** `[PAPER-PROVED] [SOURCE-SPECIFIC APPLICATION]`
  `[PARENT KOSZUL ALGEBRA] [NOT RH] [LEAN-FORMALIZED] [KERNEL-AUDITED]`
- **Statement:** Any finite family of high positive exponent shells defines a derived common zero
  locus whose Koszul homology is the exterior algebra of shell-presentation relations over the
  Riemann divisor sheaf; two shells recover the principal conormal line in degree one.

## Goal

Construct the Riemann Cartier support and principal conormal as homology of positive
coefficient-disjoint shell channels before selecting or enumerating a zero.

This supplies the first exact finite seed for
`riemann-autogenic-obstruction-operation-purity-law`: one source-derived object appears
simultaneously as an analytic fact in degree zero and as a fusion obstruction in degree one.

## Setup

Let
\[
 U=\{s\in\mathbb C:\Re s>1/2\}\setminus\{1\}
\]
and let \(\mathcal O_U\) be its holomorphic structure sheaf. For \(m\geq12\), the positive shell
continuation satisfies
\[
 S_m=\zeta H_m
\tag{1}
\]
on \(U\), where \(H_m\in\mathcal O_U^\times\) is holomorphic and zero-free.

Fix distinct \(m,n\geq12\). Form the two-generator Koszul complex
\[
 K_{m,n}:\qquad
 0\longrightarrow\mathcal O_U
 \xrightarrow{d_2}
 \mathcal O_U^2
 \xrightarrow{d_1}
 \mathcal O_U
 \longrightarrow0,
\tag{2}
\]
with
\[
 d_2(t)=(-tS_n,tS_m),\qquad
 d_1(x,y)=xS_m+yS_n.
\tag{3}
\]

Let \(D\subset U\) be the principal zeta divisor, with ideal
\(\mathcal I_D=\zeta\mathcal O_U\).

## Theorem `[PROVED HERE]`

There are shell-pair-trivialized isomorphisms
\[
 \boxed{
 \mathcal H_0(K_{m,n})\simeq\mathcal O_D,\qquad
 \mathcal H_1(K_{m,n})\simeq\mathcal O_D
 \simeq\mathcal I_D/\mathcal I_D^2,\qquad
 \mathcal H_2(K_{m,n})=0.
 }
\tag{4}
\]

The degree-one class is represented by the source syzygy
\[
 \eta_{m,n}:=(H_n,-H_m),
\qquad
 H_nS_m-H_mS_n=0.
\tag{5}
\]
Under `(4)`, \(t\bmod\zeta\) maps to the class of
\(t\eta_{m,n}\).

Equivalently, the derived common zero locus of two coefficient-disjoint positive shells has one
unit of excess intersection supported exactly on the Riemann divisor.

## Proof

The statement is local on \(U\). Work in a holomorphic local ring \(R\). Put
\[
 z=\zeta,\qquad a=H_m,\qquad b=H_n.
\]
Then \(a,b\in R^\times\), \(S_m=za\), and \(S_n=zb\). The local ring is a domain, so \(z\) is a
non-zero-divisor.

For degree zero,
\[
 (S_m,S_n)=(za,zb)=(z),
\]
because \(a\) and \(b\) are units. Therefore
\[
 H_0(K_{m,n})=R/(S_m,S_n)=R/(z).
\tag{6}
\]

For degree one, suppose \((x,y)\in\ker d_1\). Then
\[
 0=xza+yzb=z(ax+by).
\]
Since \(z\) is a non-zero-divisor,
\[
 ax+by=0.
\]
Writing \(t=xb^{-1}\) gives
\[
 (x,y)=t(b,-a).
\]
Thus
\[
 \ker d_1=R(b,-a).
\tag{7}
\]
On the other hand,
\[
 \operatorname{im}d_2
 =R(-zb,za)
 =zR(b,-a).
\tag{8}
\]
Quotienting `(7)` by `(8)` gives
\[
 H_1(K_{m,n})\simeq R/(z),
\tag{9}
\]
with the stated generator.

For degree two, \(d_2(t)=0\) implies \(tzb=0\). Since \(z\) is a non-zero-divisor and \(b\) is a
unit, \(t=0\). Hence
\[
 H_2(K_{m,n})=0.
\tag{10}
\]

Finally, for the principal Cartier ideal \(I=(z)\), the map
\[
 R/(z)\longrightarrow I/I^2,\qquad
 t\bmod z\longmapsto zt\bmod z^2
\tag{11}
\]
is an isomorphism. Equations `(6)`, `(9)`, and `(11)` prove `(4)`.

## Finite-family strengthening `[PROVED HERE]`

Let \(F\subset\{12,13,\ldots\}\) be nonempty and finite. Put
\[
 A_F=\mathcal O_U^{F},
\qquad
 h_F:A_F\longrightarrow\mathcal O_U,
\qquad
 h_F((x_m))=\sum_{m\in F}H_mx_m,
\tag{12}
\]
and let
\[
 E_F=\ker h_F.
\tag{13}
\]
Because every \(H_m\) is a unit, \(h_F\) is split surjective and \(E_F\) is locally free of rank
\(|F|-1\).

Let \(K_F=K((S_m)_{m\in F})\) be the full Koszul differential graded algebra of the shell family.
Then
\[
 \boxed{
 \mathcal H_\bullet(K_F)
 \simeq
 \mathcal O_D\otimes_{\mathcal O_U}\bigwedge\nolimits^\bullet E_F
 }
\tag{14}
\]
as graded-commutative \(\mathcal O_D\)-algebras. In particular,
\[
 \mathcal H_k(K_F)
 \simeq
 \mathcal O_D^{\binom{|F|-1}{k}}
\qquad(0\leq k\leq |F|-1),
\tag{15}
\]
and all higher homology vanishes.

### Proof

The Koszul differential is contraction by the covector
\[
 (S_m)_{m\in F}
 =\zeta(H_m)_{m\in F}
 =z h_F.
\tag{16}
\]
Choose \(m_0\in F\). Since \(H_{m_0}\) is a unit, the vector
\[
 v=H_{m_0}^{-1}e_{m_0}
\]
satisfies \(h_F(v)=1\), giving a split decomposition
\[
 A_F=\mathcal O_Uv\oplus E_F.
\tag{17}
\]
Exterior algebra turns `(17)` into
\[
 \bigwedge\nolimits^\bullet A_F
 \simeq
 \bigwedge\nolimits^\bullet(\mathcal O_Uv)
 \otimes
 \bigwedge\nolimits^\bullet E_F.
\tag{18}
\]
Under `(18)`, contraction by \(zh_F\) is the ordinary one-element Koszul differential for \(z\)
on the first tensor factor and zero on \(\bigwedge^\bullet E_F\). Hence
\[
 K_F\simeq K(z)\otimes(\bigwedge\nolimits^\bullet E_F,0).
\tag{19}
\]
Since \(z=\zeta\) is a non-zero-divisor,
\[
 \mathcal H_0(K(z))=\mathcal O_U/(z)=\mathcal O_D,
\qquad
 \mathcal H_1(K(z))=0.
\tag{20}
\]
Taking homology in `(19)` proves `(14)` and `(15)`, including compatibility with exterior
multiplication.

## Countable infinity consequence

Let
\[
 A_\infty=\bigoplus_{m\geq12}\mathcal O_Ue_m,
\qquad
 E_\infty=\ker\left[
 A_\infty\xrightarrow{\ (x_m)\mapsto\sum H_mx_m\ }\mathcal O_U
 \right].
\tag{21}
\]
The sum is finite on every section of \(A_\infty\). Fixing one base shell \(m_0\), the vectors
\[
 e_m-H_mH_{m_0}^{-1}e_{m_0},
\qquad m\ne m_0,
\tag{22}
\]
form a countable basis of \(E_\infty\).

Define the countable shell Koszul object as the filtered colimit over finite shell apertures.
The compatible splittings above give
\[
 \boxed{
 \mathcal H_\bullet(K_\infty)
 \simeq
 \mathcal O_D\otimes
 \bigwedge\nolimits^\bullet E_\infty.
 }
\tag{23}
\]

Thus infinity does not create countably many Riemann divisors. It creates one Riemann divisor
carrying a countably generated exterior algebra of presentation obstructions. Every finite
homological degree is born at a finite shell aperture, while no finite aperture contains the
complete obstruction algebra.

## Source-first form

The construction need not define \(D\) by naming zeta. Define instead the underived common shell
locus
\[
 D_{m,n}=V(S_m,S_n)
\tag{24}
\]
and its derived enhancement by `(2)`. The theorem then compares source to target:

1. the ideal \((S_m,S_n)\) equals the principal zeta ideal;
2. the truncation of the source-derived common locus is exactly the Riemann divisor;
3. its excess degree-one homology is exactly the principal conormal line.

No zero ordinate, zero multiplicity list, or zero-indexed vector space appears.

## Interpretation

The two shell equations are analytically redundant but arithmetically independent in coefficient
support. Their failure to form a regular sequence is not noise. It is the divisor:

```text
degree 0:
  the common zero is an analytic event;

degree 1:
  the same event is the nontrivial shell-fusion syzygy modulo trivial Koszul relations;

principal conormal:
  the infinitesimal form of that same obstruction.
```

This is an exact finite shadow of obstruction--law reciprocity. It does not yet turn the
degree-one class into a reciprocal prime operation.

## What this advances

1. It removes one source-landing ambiguity: the algebraic principal conormal can be constructed as
   homology of positive shell channels before point specialization.
2. It corrects the failed infinite-copy interpretation. Different shells are not orthogonal
   divisor copies; they are source trivializations of one excess-intersection class.
3. It gives a concrete finite object on which MW, co-Poisson, Gamma, reflection, and prime-transfer
   compatibility can be tested.
4. The full family proves that repeated positive presentations create higher exterior
   obstruction operations rather than independent divisor copies.
5. It isolates the next theorem: prove that the source power correspondence acts on
   \(\mathcal H_1(K_F)\) by the centered character and that Gamma reflection supplies its positive
   reciprocal operation before localizing at a zero, compatibly with the exterior algebra.

## Hostile audit

1. The Koszul computation is standard commutative algebra. Novelty can attach only to the
   source-specific shell application and later operation-generation theorem.
2. Equation `(1)` uses analytic continuation and the common zeta factor. It does not construct
   Deninger's arithmetic cohomology or a determinant from purely algebraic integer incidence.
3. \(\mathcal H_1\simeq\mathcal O_D\) is algebraic. It supplies no Hausdorff topology, positive
   metric, bounded evaluation, or reciprocal transfer.
4. Every hypothetical off-line zero appears in `(4)` exactly like a critical-line zero. The
   theorem does not select the line.
5. Two shells already suffice for the divisor and principal conormal. Countable relative
   Hypertranscendence is not used to calculate `(23)`; it matters when ruling out finite
   differential-algebraic horizontalization of the countable presentation algebra.
6. Calling the Koszul differential the desired “new law” would be theatre. It is a supplied
   differential. The open operation-generation theorem must identify the arithmetic prime/Gamma
   successor action.

## Literature and novelty boundary

Koszul homology, syzygies, derived intersections, excess conormal bundles, and `(4)` for two unit
multiples of one non-zero-divisor are standard. Targeted searches found no prior application to the
positive exponent-shell zeta frame, but no broad novelty claim is made.

The candidate frontier is the next source theorem:

```text
positive shell excess-conormal class
  -> source-generated reciprocal prime/Gamma operation
  -> persistent determinant character
  -> critical-line purity.
```

## Lean formalization

Source-specific formalization is complete in
`formal/GaloisForLFunctions/RHTower/PositiveShellKoszulCartierObstruction.lean`, supported by
`formal/GaloisForLFunctions/HTGeometry/CommonFactorKoszulHomology.lean`.

The checked declarations include the genuine punctured right-half-plane analytic carrier, actual
zeta germ, actual zero-free shell-multiplier units, two-shell differentials and homology quotients,
principal conormal identification, arbitrary finite split families with exact exterior ranks and
higher vanishing, and the complete countable `Finsupp` family with explicit nonbase-shell basis,
degreewise cycle/boundary classification, finite-aperture birth, and unbounded total basis.

Verification completed with direct `lake env lean` checks, target-only module builds, and
`#print axioms` audits. Capstones depend only on Lean kernel foundations `propext`,
`Classical.choice`, and `Quot.sound`; no project axiom, `sorry`, `admit`, `opaque`, or `unsafe`
declaration is used.

## Gates

- [x] 1 → 2: complete local-ring proof
- [x] source-defined common-locus formulation
- [x] exact Cartier conormal identification
- [x] off-line and parent-algebra limitations stated
- [x] preliminary corpus and literature collision search
- [ ] define source power correspondence on the shell Koszul complex
- [ ] prove Gamma-reflected reciprocal action on degree-one homology
- [ ] prove positive topological completion preserves the class
- [x] instantiate source-specific theorem in Lean

## Log

- 2026-07-30 — Computed the two-shell derived common zero locus. The positive shell pair produces
  the Riemann divisor in degree zero and the same divisor/conormal as its unique excess
  degree-one Koszul obstruction.
- 2026-07-30 — Extended the computation to every finite aperture and the countable filtered
  colimit. One divisor carries the exterior algebra of the shell-presentation kernel; the
  countable family creates unbounded derived law directions, not duplicate divisor points.
