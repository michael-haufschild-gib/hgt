# Source-Framed Polarized Law-Kernel Geometry

- **ID:** `source-framed-polarized-law-kernel-geometry`
- **Stage:** 1-in-progress
- **Working name:** **Polarized Law-Kernel Geometry (PLKG)**
- **Umbrella field:** **Constraint Relativity**
- **Core field:** `source-soldering-bivariant-law-geometry.md`
- **Role:** polarized/operator sector joining duality, directional response, phase, topology, and time
- **Type:** SECTOR OF BIVARIANT LAW GEOMETRY / HIGHER PHYSICAL CHART
- **Status:** `[CONJECTURAL SECTOR] [MULTIPLE EXACT LOCAL LAWS]`
  `[DIRECT EXTENSION-PHYSICS TRANSFER FALSIFIED] [GLOBAL SOLDERING EQUATION OPEN]`
  `[NO RH CLAIM] [NO LEAN WRITTEN]`
- **Exact paper anchors:**
  `../../2-fully-proven/constraint-relativity/gorenstein-trace-kahler-monogenic-equivalence-and-corank-two-splitting-law.md`,
  `../../2-fully-proven/constraint-relativity/congruence-order-trace-kahler-exterior-square-nonmetricity-law.md`,
  `../../2-fully-proven/constraint-relativity/finite-prime-gibbs-modular-phase-realization.md`,
  `../../2-fully-proven/constraint-relativity/half-sided-modular-conormal-persistence-and-bounded-dilation-no-go.md`.

## Sector principle

> **Mathematical law is not one equation or one representation object. It is source-framed relation
> between duality, directional response, polarization, completion filtration, and transport. What
> appears as arithmetic/spectral/geometric incompatibility is failure of these fields to admit one
> source-equivariant soldering.**

Newtonian proof mechanics fixes ambient category and assumes global law can be represented by one
module/operator/scalar. Monogenic source orders are exact algebraic model of this regime: trace
duality and cotangent response collapse to same cyclic module.

General law geometry must permit independent fields:

- trace/duality field: what observer can pair and conserve;
- cotangent/response field: how source changes directionally;
- polarization field: how visible and dual sectors glue or pair;
- completion filtration: which depths remain observable;
- transport generator: how source history moves these data.

This extends Curved Bivariant Law Geometry when semisimple/operator charts erase extension classes
but retain pairing, generator, and filtration. Metric-affine language is motivation only: no
connection, metric, or Levi-Civita object is assumed. Compatibility must be proved from source.

## 1. Primitive polarized law chart

A finite perfect algebraic chart begins with

\[
 \boxed{
 \mathfrak K_{mathrm{alg}}
 =\left(
 A\subset O,
 \mathbb L_{A/R},
 \det\mathbb L_{A/R},
 \omega_{A/R},\tau,
 C=O/A,
 \mathcal F_\bullet
 \right),}
 \tag{PL.1}
\]

where `A subset O` is finite split and generically etale, and:

1. `A subset O` is source/observer chart before scalarization;
2. `mathbb L_(A/R)` is perfect full cotangent complex, not only `H_0=Omega`; determinant is
   omitted outside perfect charts;
3. `omega_(A/R)=A^sharp` uses trace identification inside split generically-etale total quotient;
4. `tau:A->omega` is trace-pairing morphism, not section in bundle sense;
5. `C` is observer defect;
6. `F_bullet` is source-normal filtration/Smith/persistence data.

Trace-law middle is

\[
 L_{A,O}=\operatorname{coker}\tau=A^\sharp/A,
 \tag{PL.2}
\]

but it is one shadow, not entire law.

Operator/physical chart provisionally needs larger tuple

\[
 \boxed{
 \mathfrak K_{mathrm{op}}
 =(C\to K\to DC;\ \varpi,\ \mathcal H,\ \mathcal F_\lambda,\ s),}
 \tag{PL.3}
\]

where exact polarization may split, `varpi` is duality/symplectic pairing, `H` is Hamiltonian or
modular generator, `F_lambda` is completion/conormal filtration, and `s` is source frame. Category,
dual `D`, exactness, and morphisms of `(PL.3)` remain to be constructed; tuple is research target,
not current definition. Phase is intended isomorphism class of full tuple, not `Ext^1` alone.

## 2. Exact determinant--direction complementarity hierarchy

Paper theorems establish four strict levels.

### Level 0: general order

Dualizing lattice `omega=A^sharp` and full cotangent complex `mathbb L` are independent. There may
be no comparison identifying their finite shadows.

### Level 1: relative Gorenstein

`omega` becomes line over `A`, so duality scalarizes. Directional cotangent response need not.

### Level 2: finite-flat lci

`mathbb L` becomes two-term perfect and Kähler/Dedekind different can agree. This aligns determinant,
support, and total length only. Codimension-two tensor-square example has

\[
 L\cong R/(a^2)^2\oplus R/(a^4),
 \qquad
 \Omega\cong R/(a^2)^4.
 \tag{PL.4}
\]

Both length `8`; directional partitions differ.

### Level 3: monogenic

Under split relative-Gorenstein DVR hypotheses with infinite residue field,

\[
 \boxed{
 L\cong_A\Omega_{A/R}
 \iff
 \Omega_{A/R}\text{ cyclic}
 \iff
 A\text{ monogenic}.}
 \tag{PL.5}
\]

Thus monogenicity is exact rank-one locus where duality and response collapse.
It is not generic geometry.

## 3. Exact soldering obstruction: mathematical uncertainty law

For diagonal congruence order

\[
 A=R\mathbf1+aR^N,
 \qquad C=R^N/A\cong k^{N-1},
 \tag{PL.6}
\]

paper theorem gives

\[
 L\cong(R/(a^2))^{N-1},
 \tag{PL.7}
\]

\[
 \Omega_{A/R}
 \cong(R/(a^2))^{N-1}
 \oplus(R/(a))^{\binom{N-1}{2}},
 \tag{PL.8}
\]

and canonical horizon response

\[
 \Omega/a\Omega\cong C\oplus\bigwedge^2C.
 \tag{PL.9}
\]

Stronger: for `N>=3` in characteristic zero, every source-linear attempted soldering

\[
 \phi:\Omega_{A/R}\to L
\]

satisfies

\[
 \boxed{\operatorname{im}\phi\subset aL,}
 \qquad
 \boxed{\operatorname{gr}^0(\phi)=0.}
 \tag{PL.10}
\]

At `N=3`, Kähler and Dedekind differents are both `a^2O`; determinant and support agree, yet
tangent-head soldering remains impossible. This is exact form of corpus “making one face precise
blocks another”: scalar agreement coexists with categorical zero comparison at directional head.

Equation `(PL.10)`, not an uncertainty metaphor, is first source--observer complementarity theorem.

## 4. Polarization: extension is one chart, not universal phase

Nonsemisimple DVR monogenic chart has genuine extension

\[
 0\to C\to L\to C^\dagger\to0
 \tag{PL.11}
\]

whose Smith partition carries phase information invisible to determinant.

But finite complex vector spaces and Hilbert spaces have split exact sequences; `Ext^1=0`. Expected
von Neumann inclusions split as operator spaces, while physical gluing may remain nonzero in
symplectic cross-term or Hamiltonian. Therefore

\[
 \boxed{
 \text{phase}
 =\text{polarized, framed, transported law kernel},
 \quad\text{not extension class alone}.}
 \tag{PL.12}
\]

Arithmetic phase may live partly in extension/Smith depth; semisimple physical phase must live in
pairing, generator, and filtration.

## 5. Time as filtered law transport

Schematic target dynamics for `(PL.3)` is

\[
 U_t\mathcal F_\lambda K
 =\mathcal F_{\Phi_t(\lambda)}K,
 \qquad
 U_t^*\varpi=\varpi,
 \qquad
 \nabla_t\tau=\mathcal J_{\mathrm{src}}.
 \tag{PL.13}
\]

Connection symbols in `(PL.13)` are not yet typed until category of `(PL.3)` is constructed.
`J_src` must be constructed before target divisor/desired wall. Half-sided modular chart proves
filtration equation with

\[
 \Phi_t(a)=e^{2\pi t}a.
 \tag{PL.14}
\]

It does not by itself construct or preserve unspecified `varpi`; pairing invariance is extra chart
hypothesis.

Finite prime Gibbs chart gives elliptic solution

\[
 z_p(t)=(\log p)e^{it\log p}
 \tag{PL.15}
\]

and framed quadratic reader exactly equal to phase subdiscriminant `H_2`. Explicit prime triple
approaches wall arbitrarily closely, but no nonsemisimple law event follows.

Half-sided horizon chart instead gives hyperbolic filtration transport and unbounded generator.
Bounded exact implementation collapses to zero. Therefore transition finite recurrence -> horizon
time requires topology/type change, not smooth parameter adjustment inside one finite chart.

## 6. BLG field equation in polarized charts

Kinematics above explains obstacles but does not select law. Bivariant Law Geometry supplies typed
source transports

\[
 K_f:f_!K_A\to K_B,
 \qquad
 T_f:f_!T_A\to T_B,
 \tag{PL.16}
\]

and source-derived constitutive groupoids/torsors `mathscr S_A -> Hom(K_A,T_A)`, with local
solderings `s_A in mathscr S_A`. Their exact transport defect is

\[
 \boxed{
 Q_f=T_f f_!(s_A)-s_BK_f=J_f,}
 \tag{PL.17}
\]

with polarized conservation `U_t^*varpi=varpi` and filtration transport as additional chart data.
Curved Bianchi theorem forces `J` to obey same identity as `Q`, including intrinsic transport
curvatures `F^K,F^T`; arbitrary source current is inadmissible. Congruence theorem shows local
soldering can be forced to vanish on tangent head even when determinant shadows agree. Thus source
equation cannot be manufactured from Fitting equality.

Unconstrained `s=J=0` is tautological. Physical polarization, orientation, or prescribed nonzero
head symbol must define `mathscr S_A` before `(PL.17)` carries content.

For RH, required theorem is literal rational-Witt/Milnor/Cartier source construction of
`K,T,s,J` whose image compares with actual Route-L curvature and physical paracyclic residue.
No critical-line coordinate or Xi-zero condition may enter definition. Vanishing desired only as
derived conclusion.

## 7. Shadow dictionary

| Corpus face | PLKG field/shadow | Exact status |
|---|---|---|
| arithmetic | source order/history, dualizing section `tau` | constructed finite charts |
| spectral/Fourier | observer quotient/diagonalization `C` | constructed |
| geometric | cotangent complex `mathbb L`, not only support | constructed |
| topology | Smith/conormal persistence `F` | exact local laws |
| positivity | norm square/determinant shadow of polarization | exact but nonselective |
| phase | extension + pairing + frame + generator | exact chart dependence |
| time | filtration transport `Phi_t` | exact elliptic/hyperbolic models |
| hypertranscendence | nonstabilizing cotangent/resolution history | transfer open |
| holography | split polarized boundary/interior kernel | operator transfer open |
| RH obstruction | absent source soldering/current theorem | genuinely open |

## 8. Predictions

1. Three sheets, hence two independent observer-defect directions, are first possible
   antisymmetric cotangent pair sector; two-sheet scalar models cannot see it.
2. Equal discriminant, support, and total defect do not imply directional compatibility; tangent
   soldering may be zero.
3. Complex phase can redistribute cotangent Smith depths while trace/observer determinant stays
   fixed.
4. Finite modular prime clock can approach scalar law wall without law transition.
5. Exact horizon modular dilation cannot be bounded/finite-dimensional; global-norm finite models
   must fail or change topology.
6. Physical gluing may be nonzero with split extension; any universal `phase=Ext^1` prediction is
   false.
7. Successful RH theory must output source soldering map/current and explain why its relevant
   curvature vanishes; another faithful carrier or positive detector is insufficient.

## 9. Conjecture--attack loops

1. **One law module unifies all faces.** False by trace--Kähler discrepancy.
2. **Gorenstein/lci makes law unique.** False by corank-two equal-energy Smith split.
3. **Determinant equality supplies comparison.** False by three-sheet head-soldering zero theorem.
4. **Phase is extension class.** False in semisimple/operator charts.
5. **Finite modular recurrence realizes horizon time.** False by bounded-dilation no-go.
6. **Exterior square is already physical curvature.** False; it is cotangent pair sector until
   connection/control-space realization is sourced.
7. **PLKG proves RH.** False. Literal arithmetic instantiation of `(PL.16)--(PL.17)` is open.
8. **Surviving conjecture:** RH/HT/physical obstructions are shadows of failure—or singular
   existence—of one source-equivariant soldering across duality, response, polarization, and
   completion fields.

## 10. Physics gate

Direct unframed DDPG transfer is falsified. Any black-hole/wormhole claim must:

1. construct boundary defect and dual independently;
2. specify symplectic/duality pairing;
3. specify modular/Hamiltonian generator;
4. specify conormal/completion filtration;
5. prove comparison to arithmetic source chart;
6. identify measurable quantity and regime;
7. survive finite saturation versus unbounded dilation no-go.

Without all seven, resemblance to holography is metaphor only.

## 11. Novelty boundary

Every parent ingredient is occupied: Grothendieck duality, cotangent complexes, determinant/fundamental
classes, Gorenstein/lci/monogenic geometry, metric-affine ideas, exact categories with duality,
Frobenius/Q-systems, symplectic reduction, modular theory, half-sided inclusions, and persistence.

Potentially unoccupied residue is conjunction plus source comparison:

> source-framed dualizing and cotangent fields; exact determinant--direction hierarchy; categorical
> head-soldering obstruction despite scalar equality; phase represented differently in
> nonsemisimple and semisimple charts; and one covariant transport equation across arithmetic,
> spectral, geometric, topological, and operator completions.

This is candidate physical sector, not independent new discipline. Exact local theorems are
significant evidence; global comparison and dynamics remain open.

Primary literature boundary includes:

- https://arxiv.org/abs/math/9909192
- https://arxiv.org/abs/1212.0531
- https://arxiv.org/abs/2205.04620
- https://arxiv.org/abs/2503.04125
- https://arxiv.org/abs/2601.07915
- https://arxiv.org/abs/2604.01992
- https://arxiv.org/abs/2606.10924

## Lean-return note

No Lean work authorized. Later Step 3 should start only after paper cards pass hostile audit.
Likely first targets: explicit congruence order, trace-dual basis, cotangent module presentation,
head-soldering zero, finite modular matrix identity. Operator HSMI should wait.

## Gates

- [x] exact duality/response mismatch theorem
- [x] determinant-equal but directional-incompatible theorem
- [x] monogenic equality classification
- [x] semisimple extension-phase no-go
- [x] exact finite modular clock and hyperbolic persistence models
- [ ] define invariant category of polarized law charts
- [ ] prove source-derived soldering current in literal arithmetic corpus
- [ ] construct infinite/Tate completion preserving required fields
- [ ] prove operator/arithmetic comparison functor
- [ ] specialist priority review

## Log

- 2026-08-08 -- opened after hostile audits forced separation of trace law, cotangent response,
  extension phase, symplectic gluing, and modular filtration. Exact head-soldering zero theorem
  supplied first mathematical uncertainty law.
