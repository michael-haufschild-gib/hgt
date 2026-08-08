# Bivariant Law Geometry

- **ID:** `source-soldering-bivariant-law-geometry`
- **Stage:** 1-in-progress
- **Working field name:** **Curved Bivariant Law Geometry (CBLG)**
- **Umbrella field:** **Constraint Relativity**
- **Role:** core dynamics of trace/deformation law transport across source histories
- **Type:** CANDIDATE NEW MATHEMATICAL FIELD / SOURCE-SOLDERING PROGRAM
- **Status:** `[BOLD CONJECTURAL FIELD] [EXACT COCYCLE LAW]`
  `[EXACT FIRST-INFINITESIMAL OBSTRUCTION] [EXACT RELATIVE-OBSERVER DUALITY]`
  `[LITERAL RH SOURCE COMPARISON OPEN]`
  `[CLASSICAL PARENTS] [NOVELTY UNVERIFIED] [NO LEAN WRITTEN]`
- **Paper anchors:**
  `../../2-fully-proven/constraint-relativity/source-soldering-transport-defect-cocycle-and-law-symbol.md`,
  `../../2-fully-proven/constraint-relativity/constitutive-soldering-intertwiner-energy-law.md`,
  `../../2-fully-proven/constraint-relativity/route-r-raw-resolved-relative-cone-character-law.md`,
  `../../2-fully-proven/constraint-relativity/relative-law-observer-descent-duality.md`,
  `../../2-fully-proven/constraint-relativity/factor-framed-tensor-jacobian-defect-law.md`,
  `../../2-fully-proven/constraint-relativity/congruence-order-trace-kahler-exterior-square-nonmetricity-law.md`,
  `../../2-fully-proven/constraint-relativity/gorenstein-trace-kahler-monogenic-equivalence-and-corank-two-splitting-law.md`.
- **Polarized/physical sector:** `source-framed-polarized-law-kernel-geometry.md`.

## Founding principle

> **A mathematical law has two independently functorial aspects: deformation response and
> trace/duality response. Geometry is obstruction to soldering them naturally along source history.**

This is stronger and narrower than saying “two metrics.” `Omega` and `A^sharp/A` are not metrics.
They are different law functors. Their comparison must be natural under source changes. Scalar
discriminant equality is only decategorified shadow.

Monogenic mathematics is flat one-coordinate locus where two laws coincide. Relative Gorenstein
and lci hypotheses align progressively weaker shadows but do not supply directional equivalence.

## 1. Bivariant source-history object

Let `Src` initially be category of finite perfect, generically separable, trace-oriented source
presentations over `R`, with history arrows for which required duality transport is constructed. To
each source `A`, attach

\[
 \boxed{
 K_A=\mathbb L_{A/R}
 \quad\text{(deformation law)},
 \qquad
 T_A=\operatorname{cofib}
 \left(A\xrightarrow{\tau_A}\mathbf R\operatorname{Hom}_R(A,R)\right)
 \quad\text{(trace law)}.}
 \tag{BL.1}
\]

Here `tau_A` is trace-pairing morphism. For finite split order, `H_0(T_A)=A^sharp/A`. For
admissible source arrow `f:A->B`, data must include
typed transports

\[
 K_f:f_!K_A\to K_B,
 \qquad
 T_f:f_!T_A\to T_B,
 \tag{BL.2}
\]

with declared composite transports. Flat charts require composition compatibility; full theory
retains their failure as intrinsic two-curvature. Not every ring map is automatically admissible;
trace transport and source topology must be constructed.

Local law soldering is morphism

\[
 s_A:K_A\to T_A.
 \tag{BL.3}
\]

Source must also prescribe constitutive groupoid/torsor

\[
 \mathscr S_A\longrightarrow\operatorname{Hom}(K_A,T_A),
 \tag{BL.3a}
\]

such as lifts of fixed nonzero head symbol, orientation-normalized comparisons,
quasi-isomorphisms, or adjoints of nondegenerate polarization. Solderings must lie in
`mathscr S_A`. Without `(BL.3a)`, `s_A=0` is always natural and every curvature claim is vacuous.
Existence at isolated object is insufficient. Field question is whether source-admissible `s_A`
can be chosen naturally along entire source history.

## 2. Exact edge defect and two-curvature

Define

\[
 \boxed{
 Q_f
 =T_f\circ f_!(s_A)-s_B\circ K_f.}
 \tag{BL.4}
\]

Under strict composition, paper theorem proves twisted cocycle law for `A-f->B-g->C`:

\[
 \boxed{
 Q_{gf}
 =T_g\circ g_!(Q_f)+Q_g\circ g_!(K_f).}
 \tag{BL.5}
\]

Whenever two admissible solderings differ additively by `h`, edge defect changes by

\[
 Q_f' - Q_f
 =T_f f_!(h_A)-h_BK_f.
 \tag{BL.6}
\]

An actual obstruction class requires specified admissible gauge morphisms of `mathscr S`; arbitrary
subsets of Hom do not define cohomology. Curvature interpretation is meaningful only after
`(BL.3a)` is fixed.

More importantly, corpus transports need not compose strictly. Define intrinsic law curvatures

\[
 F^K_{g,f}=K_g g_!(K_f)-K_{gf},
 \qquad
 F^T_{g,f}=T_g g_!(T_f)-T_{gf}.
 \tag{BL.6a}
\]

Paper theorem proves curved Bianchi/transgression law

\[
 \boxed{
 T_g g_!(Q_f)+Q_g g_!(K_f)-Q_{gf}
 =F^T_{g,f}(gf)_!(s_A)-s_CF^K_{g,f}.}
 \tag{BL.6b}
\]

Strict cocycle `(BL.5)` is flat special case. Route R supplies literal nonzero `F^K`: at prime
`2` and depths `0,1,2`, infinitesimal triangle curvature is `-log(2)/8`. This exact corpus theorem
forces BLG to be bivariant two-geometry, not flat natural-transformation cohomology.

When `Q=0` and constitutive soldering is invertible, `(BL.6b)` becomes curvature compatibility

\[
 \boxed{F^T_{g,f}(gf)_!(s_A)=s_CF^K_{g,f}.}
 \tag{BL.6c}
\]

This is constraint-equivalence principle: two law fields need not have zero curvature, but their
curvatures must be transported into one another by source-admissible constitutive identification.

## 3. First-order law symbol

For a local `k`-algebra source `(A,mathfrak m,k)` with chosen coefficient field and law module `M`
killed by `mathfrak m^2`, define

\[
 W=\mathfrak m/\mathfrak m^2,
 \quad
 H_M=M/\mathfrak mM,
 \quad
 S_M=\mathfrak mM.
 \tag{BL.7}
\]

Multiplication is canonical law symbol

\[
 \sigma_M:W\otimes_kH_M\to S_M.
 \tag{BL.8}
\]

Head soldering `f:H_K->H_T` lifts through first square-zero thickening iff there is
`g:S_K->S_T` with

\[
 g\sigma_K=\sigma_T(1\otimes f).
 \tag{BL.9}
\]

Obstruction tensor is class

\[
 \boxed{
 \mathcal N(f)
 =[\sigma_T(1\otimes f)]
 \in\operatorname{coker}
 \left[
 \operatorname{Hom}_k(S_K,S_T)
 \to\operatorname{Hom}_k(W\otimes H_K,S_T)
 \right].}
 \tag{BL.10}
\]

Unlike difference of lengths, `(BL.10)` is coordinate-free and tests actual lift.

## 4. Exact maximal first-order obstruction

For congruence/star order

\[
 A=R\mathbf1+aR^N,
 \qquad N\ge3,
 \tag{BL.11}
\]

take `K=Omega_(A/R)` and `T=A^sharp/A`. Both factor through `A/mathfrak m^2`. Paper theorem gives

\[
 \operatorname{Hom}_A(K,T)\cong\operatorname{Mat}_{N-1}(k),
 \tag{BL.12}
\]

yet head reduction

\[
 \operatorname{Hom}_A(K,T)
 \to\operatorname{Hom}_k(H_K,H_T)
 \tag{BL.13}
\]

is zero. Therefore every nonzero head map has nonzero `mathcal N(f)`. For `N=3`, Kähler and
Dedekind differents agree exactly, so discriminant/different geometry is flat while directional law
soldering is maximally obstructed.

This is precise form of corpus uncertainty: making both scalar shadows exact does not merely leave
unknown comparison; source action forces every first-order comparison to vanish.

## 5. Determinant--direction hierarchy

Tensor composition supplies second exact family beyond congruence orders. For
`A_d=bigotimes_(i=1)^d R[f_i]/(f_i^2-a^2)`, every factor has exact monogenic soldering, but
factor-compatible tensor soldering has

\[
 \operatorname{coker}s_d
 \cong
 \bigoplus_{t=0}^{d-2}
 \left(R/(a^{2(d-1-t)})\right)^{\binom dt},
 \tag{BL.13a}
\]

with kernel of same length

\[
 \operatorname{length}\ker s_d
 =\operatorname{length}\operatorname{coker}s_d
 =2^d(d-2)+2.
 \tag{BL.13b}
\]

Thus individually exact law identifications fail under source composition, and mixed obstruction
grows exponentially. This is factor-framed Jacobian defect, not yet categorical cross-effect.
Factor-compatible
soldering is gradient derivation of multiplicative trace different `F=prod_i f_i`; its cokernel is
relative critical/Jacobian algebra

\[
 A_d/(F,\nabla F),
 \tag{BL.13c}
\]

with horizon dimension `2^d-d-1`. Thus composition of individually flat laws creates joint
critical locus. Same module is persistent face object of `(d-1)`-simplex: every face `T` below
facets has Smith depth twice excess codimension `2(d-1-|T|)`, and closed fibre is commutative
squarefree face algebra with square-zero vertices on `(d-3)`-skeleton. Arithmetic tensor factors,
topology, Smith spectrum, and critical geometry are
four exact shadows of one mixed composition object.

For unequal contact depths `r_i`, face with missing set `M` has exact bar depth

\[
 \boxed{2\left(\sum_{i\in M}r_i-\max_{i\in M}r_i\right).}
 \tag{BL.13d}
\]

Thus one missing direction is absorbable while every additional missing depth survives in joint
critical law. This is weighted, falsifiable version of corpus uncertainty; it remains within one
quadratic algebraic doctrine.

At closed horizon over `C`, same face algebra has faithful quantum chart on truncated hard-core
Fock space `span{|T>:|T|<=d-2}`. Compressed creators realize vertices, and Hamiltonian
`H=sum_i(log p_i)N_i` transports face `T` by phase `exp(it sum_(i in T)log p_i)`. This is exact
arithmetic--topology--quantum recurrence bridge, but finite type-I chart supplies no black-hole or
wormhole identification.

Exact classification:

1. general finite order: trace and deformation laws independent;
2. relative Gorenstein: trace law becomes line/cyclic shadow;
3. lci: determinant/different align, directional modules may differ;
4. monogenic: under split DVR/infinite-residue hypotheses,

   \[
   A^\sharp/A\cong_A\Omega_{A/R}
   \iff\Omega_{A/R}\text{ cyclic}
   \iff A\text{ monogenic}.
   \tag{BL.14}
   \]

This identifies monogenic routes as corank-one law-equivalence charts, not universal foundation.

## 6. Field equation and admissible source current

Proposed dynamics is

\[
 \boxed{Q_f=J_f,}
 \tag{BL.15}
\]

where `J_f` must be constructed from source operations independently of target obstruction. Curved
Bianchi theorem forces consistency

\[
 \boxed{
 T_g g_!(J_f)+J_g g_!(K_f)-J_{gf}
 =F^T_{g,f}(gf)_!(s_A)-s_CF^K_{g,f}.}
 \tag{BL.16}
\]

Any proposed current failing `(BL.16)` is rejected before application. Any current defined using
critical line, Xi-zero displacement, or desired vanishing is circular.

Equation `(BL.15)` is otherwise tautological: `s=J=0` solves it. Valid instantiation must first
construct nonzero constitutive data `(BL.3a)` and prove it is preserved or obstructed by source
transport.

For RH, decisive advance would instantiate `Src,K,T,Q,J` from literal rational-Witt/Milnor/Cartier
source and prove comparison with actual Route-L completion curvature and Route-R physical
paracyclic residue. Those objects are not Kähler `Omega`; typed comparison theorem is required.

## 7. Obstruction-transgression hierarchy

Corpus forces stronger universal principle than trace/cotangent mismatch:

> **A source constraint obstruction is not tied to one representation. Under admissible transport,
> exactification, completion, and polarization, it changes degree or carrier. Apparent removal in
> one chart must be audited as transgression into another.**

Current exact and conjectural layers are:

| degree/carrier | obstruction shadow | status |
|---|---|---|
| object, first infinitesimal | law symbol `mathcal N(f)` | exact congruence theorem |
| edge | constitutive mismatch `Q_f` | exact definition/law |
| triangle | intrinsic `F^K,F^T` | exact Bianchi; literal Route-R instance |
| global cohomology | retained Stokes/admission period | exact relative-observer pairing in Route R |
| completion | radical, nonclosed range, multivalued relation, ideal grade | exact corpus objects; universal functor open |
| polarization | sign, inertia, one-negative-port square, norm energy | exact local laws; source comparison open |
| HT tail | nonstabilizing resolution/cotangent history | conjectural pro-object |

This hierarchy explains corpus uncertainty without a numerical Heisenberg product. Improving one
chart can move obstruction out of its visible degree instead of solving it. Theory fails if it
labels every mismatch same object: typed transgression maps must be constructed case by case.

### Exact relative-observer law

Route R now supplies first dependency-closed three-doctrine merger. For strict comparison
`Phi:C->X`, let `f=H^n(Phi)`. Paper theorem gives canonical identities

\[
 \mathcal R_f
 =H^{n-1}(\operatorname{Cone}\Phi)/\operatorname{im}H^{n-1}(X)
 \cong\ker f,
 \tag{BL.17a}
\]

\[
 \mathcal O_f(V)
 =\operatorname{coker}\bigl[f^*:\operatorname{Hom}(H^nX,V)
 \to\operatorname{Hom}(H^nC,V)\bigr]
 \cong\operatorname{Hom}(\ker f,V).
 \tag{BL.17b}
\]

Hence relative law and non-descending observer have canonical evaluation pairing. In literal Route
R:

\[
 \underbrace{[\eta_p]}_{\text{arithmetic kernel law}}
 \quad\leftrightarrow\quad
 \underbrace{[(L_p,\eta_p)]}_{\text{geometric cone lift}}
 \quad\leftrightarrow\quad
 \underbrace{[P_{t,\rho}]}_{\text{spectral/physical covector}},
 \tag{BL.17c}
\]

and their exact pairing is `c_rho[F_(-t)]`, with reflected value `c_rho[F_t]`. This proves that
three faces need not share one carrier: their merger is kernel--relative-lift--dual-observer
pairing.

The companion distinction is equally exact. Raw scalar reporter has `D^2 ne 0` off centre;
resolved exactification makes `[eta_p]` a boundary; every ordinary cochain character of resolved
**absolute** complex kills it; physical quotient retains it in at least one orientation. Relative
mapping cone nevertheless carries an ordinary character with exact physical value. Therefore
forced organ is absolute/relative observer distinction, not a genuinely secondary operation.
Curvature-corrected stabilization can also encode raw reporter in enlarged ordinary complex, so
no unrestricted anti-complex claim survives.

## 8. Route-completeness audit

- Route L square `ZP_Gamma-G_Gamma D` has exact edge-defect pattern, but no theorem identifies its
  objects with trace/cotangent `K,T`.
- Route R depth triangle is literal intrinsic two-curvature and falsifies strict transport.
- Retained period-one Stokes class becomes nonzero relative cone law after resolved exactification.
- Singular Cartier comparison is exact observer-descent covector on that relative law, but
  simultaneous nonvanishing of two fixed-orientation evaluations on distinguished retained class
  still lacks source producer.
- Unaugmented raw reporter is curved, but enlarged ordinary stabilization exists. Missing
  mathematical content is source-natural/minimal compatibility, not mere existence of complex.
- Physical Cartier character fails to descend through resolved absolute cohomology but is exact
  ordinary character of relative cone.
- Hedenmalm nonclosability and maximal verticality require relations and topology, not morphisms
  alone.
- Stokes--Cartan one-negative-port law requires polarization/inertia, not additive defect alone.

Thus CBLG is exact algebraic core of Constraint Relativity, not yet route-complete field.

## 9. Relation to polarized phase and physics

BLG is core algebraic dynamics. Physical/semisimple charts require Polarized Law-Kernel Geometry:
pairing, frame, Hamiltonian/modular generator, and persistence filtration. Operator audit proves
extension class alone collapses (`Ext^1=0`) while gluing/dynamics may remain.

Finite Gibbs prime clock realizes scalar phase trajectory; half-sided modular inclusion realizes
hyperbolic conormal persistence. Neither supplies literal arithmetic soldering.

## 10. Hypertranscendence

HT source should use full nonstabilizing cotangent/resolution history, not only finite `Omega`.
Exterior-square sector in star order is first-layer theorem, not universal tower. For square-zero
algebra `B=k+V`, higher relation execution obeys

\[
 \operatorname{Tor}^B_r(k,k)\cong V^{\otimes r},
 \tag{BL.17}
\]

so dimensions grow as `(dim V)^r`; universal exterior-power continuation is false. BLG must allow
tensor/exponential complexity and completion-dependent stabilization.

## 11. Predictions and falsifiers

1. Scalar/determinant agreement cannot imply law equivalence.
2. Nonzero tangent frames can fail at first square-zero thickening, before completion.
3. Proposed source currents must obey cocycle `(BL.16)`.
4. Monogenic proofs cannot generalize by adding more coordinates while retaining `L=Omega`.
5. Higher relation execution need not be exterior; `(BL.17)` falsifies that extrapolation.
6. Any Route-L identification `Omega_(mu,Gamma)=Omega_(A/R)` without comparison theorem is invalid.
7. New field claim fails unless second non-star family and nontrivial source-arrow `Q_f` are computed.
8. Any formulation permitting unconstrained zero soldering is vacuous and is rejected as field
   theory.
9. Any formulation imposing strict transport composition is falsified by Route-R depth triangle;
   intrinsic `F^K,F^T` must be retained.
10. Any formulation demanding arithmetic, geometric, and spectral faces occupy one carrier is
    falsified by relative-observer theorem; canonical pairing is sufficient and generally
    incompatible with descent.
11. Any chain-map model factoring physical Cartier character through resolved absolute complex is
    falsified because it kills boundary `delta L_p`; relative cone character is valid and exact.

## 12. Novelty boundary

Natural-transformation defects, category cohomology, cotangent complexes, differents, duality,
Loewy symbols, deformation lifting, and bivariant theories are classical. “Soldering” also has
established geometry/physics meanings. Working name therefore emphasizes bivariant law coupling,
not invention of solder forms.

Potential new residue:

> exact trace--cotangent source coupling; determinant-equal but maximal first-order lift
> obstruction; curved transport cocycle; and literal arithmetic-kernel/geometric-relative/
> spectral-observer pairing whose physical character provably cannot descend through resolved
> absolute exactification but evaluates canonically on relative cone law.

Current status is viable field program plus first exact three-doctrine bridge, not Newton-to-GR
transition yet. Threshold now requires functorial curved/relative/observer category beyond one
route, cofinal topological realization, and source law forcing simultaneous two-orientation
nonvanishing on distinguished retained classes without assuming RH.

Primary adjacent sources:

- https://arxiv.org/abs/1005.4328
- https://arxiv.org/abs/1202.4367
- https://arxiv.org/abs/1008.1712
- https://arxiv.org/abs/1606.00619
- https://arxiv.org/abs/math/9909192
- https://arxiv.org/abs/2205.04620
- https://arxiv.org/abs/2602.07353
- https://arxiv.org/abs/2604.01992
- https://arxiv.org/abs/hep-th/9805109
- https://arxiv.org/abs/hep-th/9806005

## Lean-return note

No Lean work authorized. Later formal targets: typed strict-transport cocycle, square-zero law
symbol, explicit congruence-order action, head-reduction zero. Search existing category/cotangent
corpus before edits.

## Gates

- [x] exact local comparison obstruction
- [x] coordinate-free first-order invariant
- [x] transport cocycle and gauge law
- [x] curved Bianchi law and literal Route-R two-curvature
- [x] source-current Bianchi constraint
- [x] zero-soldering vacuity exposed; constitutive constraint added
- [x] second non-star tensor-composition family
- [x] nontrivial Route-R scalar source-history `Q/F` computation
- [x] unaugmented raw/resolved-absolute unification no-go and ordinary relative-cone repair
- [x] exact arithmetic--geometric--spectral relative-observer pairing
- [ ] typed trace--cotangent source-history `Q/F` computation
- [ ] literal Route L/R comparison
- [ ] infinite HT/prime topology
- [ ] specialist priority review

## Log

- 2026-08-08 -- founded after scalar-different equality was shown compatible with maximal
  first-order trace/cotangent soldering obstruction; transport defect obeys exact cocycle law.
