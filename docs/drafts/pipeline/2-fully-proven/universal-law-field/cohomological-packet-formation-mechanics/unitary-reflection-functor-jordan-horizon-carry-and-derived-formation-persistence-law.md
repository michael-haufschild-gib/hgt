# Unitary-reflection functor, Jordan horizon carry, and derived formation persistence law

- **ID:** ULF-CPFM-5
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / NEW-FIELD FUSION LAW
- **Status:** `[PAPER-PROVED] [LEAN-FORMALIZED] [ROUTE-INDEPENDENT]`
  `[POSITIVE OBSERVER DERIVED] [NON-LEFT-EXACTNESS COMPUTED]`
  `[COHOMOLOGY + POSITIVITY + PROLONGATION + PROPERNESS] [NOT RH]`
- **Statement:** Finite-unipotent formation has a functorial maximal quotient seen by positive
  unitary reporters.  This quotient is right exact but not left exact.  In the canonical Jordan
  extension, every old visible head becomes the boundary of the new primitive, and the connecting
  homology map recovers it exactly.  Cofinal repetition produces zero persistent positive state or
  unbounded source action.

## 1. Why this is a higher-level pivot

Derived observer-formation mechanics already proves that a nonexact observer can create or erase
formation homology.  It does not identify a canonical observer arising from positivity.  The
previous unitary-formation-radical theorem proves that every positive-unitary reporter kills
finite Jordan displacement, but it treats each source separately.

This card closes the missing fusion:

1. positive-unitary erasure is functorial under every formation intertwiner;
2. its quotient maps compose exactly;
3. failure to preserve an inclusion is a typed formation charge;
4. that charge is the connecting class in the cyclic-action homology sequence;
5. prolonging one formation stage does not destroy the charge but moves it from visible degree
   zero to derived degree one;
6. source depth properness prevents indefinite rebirth at finite action.

The mechanism is therefore not “curvature.”  It is

> **derived nonexactness of a source-formed positive observer, coupled to a proper formation
> grading.**

This is classical coinvariant/group-homology machinery in a new corpus-wide role.  No novelty
criterion is used.

## 2. Formation category and forced unitary quotient

Let `k=R`.  A formation module is a pair `(V,T)` where `V` is a real vector space and
`T:V -> V` is a linear automorphism.  Write

\[
 \Delta_T=T-I,
 \qquad
 F_T=\bigcup_{n\ge 0}\ker \Delta_T^n,
 \qquad
 R_T=\Delta_T(F_T).
 \tag{URP.1}
\]

`F_T` is the finite-unipotent part and `R_T` is the unitary-formation radical.  Define the forced
positive quotient

\[
 Q(V,T)=V/R_T.
 \tag{URP.2}
\]

A morphism

\[
 f:(V,T)\longrightarrow(W,S)
 \tag{URP.3}
\]

is a linear map satisfying `fT=Sf`.

### Theorem 2.1 -- functoriality

Every formation morphism satisfies

\[
 f(F_T)\subseteq F_S,
 \qquad
 f(R_T)\subseteq R_S.
 \tag{URP.4}
\]

Consequently it induces a unique linear map

\[
 Q(f):Q(V,T)\longrightarrow Q(W,S),
 \qquad
 Q(f)[v]=[f(v)].
 \tag{URP.5}
\]

These maps obey

\[
 Q(\operatorname{id})=\operatorname{id},
 \qquad
 Q(gf)=Q(g)Q(f).
 \tag{URP.6}
\]

#### Proof

Intertwining gives, for every `n`,

\[
 f\Delta_T^n=\Delta_S^n f.
 \tag{URP.7}
\]

If `v in F_T`, some `n` has `Delta_T^n v=0`; hence
`Delta_S^n f(v)=f(Delta_T^n v)=0`, so `f(v) in F_S`.  Also

\[
 f(\Delta_Tv)=\Delta_Sf(v),
 \tag{URP.8}
\]

which proves radical transport.  Formula `(URP.5)` is therefore well-defined.  Identity and
composition follow on quotient generators.  QED.

### Theorem 2.2 -- universal positive erasure

Let `H` be a real Hilbert space, let `U` be a linear isometry of `H`, and let
`r:V -> H` satisfy

\[
 rT=Ur.
 \tag{URP.9}
\]

Then

\[
 R_T\subseteq\ker r,
 \tag{URP.10}
\]

and `r` factors uniquely through `Q(V,T)`.

#### Proof

For `v in F_T`, some iterated displacement `Delta_T^n v` is zero.  Intertwining transports this
to `(U-I)^n r(v)=0`.  A positive isometry has no nontrivial finite Jordan chain at eigenvalue one,
so `Ur(v)=r(v)`.  Therefore

\[
 r(\Delta_Tv)=(U-I)r(v)=0.
 \]

Linear quotient universality gives the unique factor.  QED.

When `F_T=V`, the induced action on `Q(V,T)` is the identity because
`[Tv]-[v]=[Delta_Tv]=0`.  In finite dimension, choose any positive inner product on the quotient.
Thus on finite-unipotent formation modules `Q` is the maximal trivial/unitary quotient.  This is
the coinvariant reflector for the cyclic formation action.

### Corollary 2.3 -- exact criterion for a migrating horizon

If `f:(V,T)->(W,S)` and there is `v` with

\[
 v\notin R_T,
 \qquad
 f(v)\in R_S,
 \tag{URP.11}
\]

then `Q(f)` is not injective.  Indeed `[v]` is nonzero while `Q(f)[v]=0`.

This is the smallest typed positive-observer formation charge: a class visible at one stage becomes
unitary-forced boundary after legal formation extension.

## 3. Canonical Jordan extension

Define

\[
 J_2=\mathbb R^2,
 \qquad
 T_2(x,y)=(x+y,y),
 \tag{URP.12}
\]

and

\[
 J_3=\mathbb R^2\times\mathbb R,
 \qquad
 T_3((x,y),z)=((x+y,y+z),z).
 \tag{URP.13}
\]

Let

\[
 i:J_2\longrightarrow J_3,
 \qquad
 i(x,y)=((x,y),0).
 \tag{URP.14}
\]

Then `iT_2=T_3i`.  The displacements are

\[
 \Delta_2(x,y)=(y,0),
 \qquad
 \Delta_3((x,y),z)=((y,z),0).
 \tag{URP.15}
\]

Hence `Delta_2^2=0` and `Delta_3^3=0`, so every vector is finite-unipotent.

Define head reporters

\[
 h_2(x,y)=y,
 \qquad
 h_3((x,y),z)=z.
 \tag{URP.16}
\]

They are formation-invariant:

\[
 h_2T_2=h_2,
 \qquad
 h_3T_3=h_3.
 \tag{URP.17}
\]

### Theorem 3.1 -- exact positive quotients and non-left-exactness

One has

\[
 R_{T_2}=\mathbb R\times\{0\}=\ker h_2,
 \qquad
 R_{T_3}=\mathbb R^2\times\{0\}=\ker h_3.
 \tag{URP.18}
\]

Therefore

\[
 Q(J_2,T_2)\simeq\mathbb R,
 \qquad
 Q(J_3,T_3)\simeq\mathbb R,
 \tag{URP.19}
\]

through `h_2,h_3`, while

\[
 Q(i)=0.
 \tag{URP.20}
\]

#### Proof

Equation `(URP.15)` shows the displayed images are contained in the radicals.  Conversely every
`(x,0)` is `Delta_2(0,x)`, and every `((x,y),0)` is
`Delta_3((0,x),y)`.  This proves `(URP.18)`.  The heads are surjective, so they induce the
isomorphisms `(URP.19)`.  Finally `h_3 i=0`; equivalently every `i(x,y)` lies in `R_{T_3}`, giving
`(URP.20)`.  QED.

Thus the positive quotient functor preserves the quotient/epimorphic part of this cell but destroys
its monomorphic part.  Positivity is not merely “phase-blind”; it is a right-exact formation
reflector with a computable left-exactness defect.

### Theorem 3.2 -- unit horizon conservation

Set

\[
 e_{\rm old}=(0,1)\in J_2,
 \qquad
 p_{\rm new}=((0,0),1)\in J_3.
 \tag{URP.21}
\]

Then

\[
 i(e_{\rm old})=\Delta_3p_{\rm new},
 \tag{URP.22}
\]

and

\[
 h_2(e_{\rm old})=1,
 \qquad
 h_3(i(e_{\rm old}))=0,
 \qquad
 h_3(p_{\rm new})=1.
 \tag{URP.23}
\]

Every positive-unitary reporter on `J_3` kills `i(e_old)`.

#### Proof

All identities follow directly from `(URP.14)--(URP.16)`.  The last statement follows from
`i(e_old) in R_T3` and Theorem 2.2.  QED.

The old unit does not disappear.  It becomes the exact boundary of the next primitive, while the
primitive supplies the new unit head.  This is the formation conservation law.

## 4. Derived connecting law

The Jordan cell is a short exact sequence of cyclic-action modules:

\[
 0\longrightarrow J_2\xrightarrow{i}J_3\xrightarrow{h_3}\mathbb R
 \longrightarrow0,
 \tag{URP.24}
\]

where the last `R` carries the trivial action.

For a cyclic action generated by `T`, write

\[
 H_0(T;V)=V/(T-I)V,
 \qquad
 H_1(T;V)=\ker(T-I).
 \tag{URP.25}
\]

In this finite-unipotent chart, `H_0=Q`.  The long exact sequence of `(URP.24)` contains

\[
 H_1(J_3)\longrightarrow H_1(\mathbb R)
 \xrightarrow{\partial}H_0(J_2)
 \xrightarrow{H_0(i)}H_0(J_3)
 \xrightarrow{H_0(h_3)}H_0(\mathbb R)\longrightarrow0.
 \tag{URP.26}
\]

### Theorem 4.1 -- exact derived carry

Under the head identifications, `(URP.26)` is

\[
 \mathbb R\xrightarrow{0}\mathbb R
 \xrightarrow{\cong}\mathbb R
 \xrightarrow{0}\mathbb R
 \xrightarrow{\cong}\mathbb R\longrightarrow0,
 \tag{URP.27}
\]

and

\[
 \partial(1)=[e_{\rm old}].
 \tag{URP.28}
\]

#### Proof

The fixed vectors in `J_3` have the form `((x,0),0)` and map to zero under `h_3`; hence the first
map in `(URP.27)` is zero.  To compute the connecting map, lift `1 in R` to `p_new`.  Its
displacement is `Delta_3p_new=i(e_old)` by `(URP.22)`.  The standard connecting construction sends
`1` to `[e_old]`.  That class is the unit under `h_2`, so the connecting map is an isomorphism.
The next map is `H_0(i)=Q(i)=0` by Theorem 3.1.  Finally `h_3` induces the head isomorphism on
coinvariants.  QED.

This is the exact identity missing from a scalar “erasure” story:

\[
 \boxed{\text{old visible head}=\text{new degree-one connecting carry}.}
 \tag{URP.29}
\]

Formation conserves the law by changing its grade.

## 5. Arbitrary Jordan depth and persistence

Let

\[
 A_n=\mathbb R[\varepsilon]/(\varepsilon^n),
 \qquad
 T_n=1+\varepsilon.
 \tag{URP.30}
\]

Multiplication by `epsilon` gives a short exact sequence

\[
 0\longrightarrow A_n\xrightarrow{\varepsilon}A_{n+1}
 \longrightarrow\mathbb R\longrightarrow0.
 \tag{URP.31}
\]

### Theorem 5.1 -- one-step lifetime law

For every `n>=1`,

\[
 H_0(A_n)\simeq\mathbb R,
 \qquad
 H_0(A_n)\longrightarrow H_0(A_{n+1})=0,
 \tag{URP.32}
\]

and the connecting map

\[
 H_1(\mathbb R)\xrightarrow{\cong}H_0(A_n)
 \tag{URP.33}
\]

is an isomorphism.

#### Proof

`H_0(A_n)=A_n/epsilon A_n`, hence is the constant-coefficient line.  The inclusion in
`(URP.31)` multiplies by `epsilon`, so it induces zero on constant-coefficient quotients.  Lifting
`1` in the last `R` to `1 in A_(n+1)` gives displacement `epsilon`, which is the image of the unit
of `A_n`; therefore the connecting map sends unit to unit.  QED.

The persistence module of finite positive heads is consequently

\[
 \mathbb R\xrightarrow{0}\mathbb R\xrightarrow{0}\mathbb R\xrightarrow{0}\cdots.
 \tag{URP.34}
\]

Every finite head has lifetime one and the direct limit is zero.  A cofinal class can survive only
by retaining its marked derived history rather than by pretending that finite heads form one
compatible positive state.

## 6. Fourth-organ theorem: polynomial translation and finite recurrence

Let `a != 0` and let

\[
 F_n(X)=\prod_{j<n}(X-ja)
 \tag{URP.35}
\]

be the falling-factorial basis.  Translation by `a` has difference

\[
 \Delta_aP(X)=P(X+a)-P(X).
 \tag{URP.36}
\]

The corpus already proves

\[
 \Delta_aF_{n+1}=((n+1)a)F_n.
 \tag{URP.37}
\]

### Theorem 6.1 -- finite-recurrence successor migration

For every `n`, `F_n` has nonzero unit leading coefficient at formation depth `n`, but after the
degree-`n+1` prolongation it is an exact translation boundary:

\[
 [F_n]_{H_0(\mathcal P_{\le n})}\ne0,
 \qquad
 [F_n]_{H_0(\mathcal P_{\le n+1})}=0.
 \tag{URP.38}
\]

More precisely,

\[
 F_n=\Delta_a\left(((n+1)a)^{-1}F_{n+1}\right).
 \tag{URP.39}
\]

#### Proof

`F_n` is monic of degree `n`, while `Delta_a` lowers degree by one on the falling-factorial basis.
Thus no difference of a degree-at-most-`n` polynomial has an `F_n` component, proving the first
claim.  Equation `(URP.39)` follows from `(URP.37)` and places it in the next-stage difference
range.  QED.

This theorem was predicted by `(URP.29)` before using polynomial coordinates.  It applies to any
finite constant-recurrence/Hankel realization whose prolongation contains one cyclic Jordan block:
the first unseen affine successor is a derived carry, not a stable positive coordinate.

## 7. Properness fusion

The earlier formation-depth theorem supplies normalized horizon histories `h_N` with exact source
gauge

\[
 \Phi(h_N)=1+2N.
 \tag{URP.40}
\]

### Theorem 7.1 -- persistent-head extinction or escape

In a cofinal Jordan/prolongation tower satisfying `(URP.40)`, a nonzero positive head at every
arbitrarily large depth cannot be represented by a family contained in one bounded source-action
sublevel.  Therefore a uniformly finite-action coherent state has zero persistent positive head.

#### Proof

By Theorem 5.1, a positive head at depth `N` dies at the next stage and can be retained only by its
marked primitive/connecting history.  Any such marked representative has gauge at least
`1+2N`.  If nonzero heads occur at unbounded depths, these gauges are unbounded.  Conversely a
bounded gauge admits only finitely many depths, so no nonzero cofinal head survives.  QED.

The result joins four structurally different organs through one mechanism:

| organ | exact role |
|---|---|
| cohomological formation | connecting map carries old head |
| positive/unitary recurrence | `H_0=Q` is maximal forced visible quotient |
| prolongation/finite recurrence | next stage turns current head into boundary |
| source properness | marked repeated rebirth escapes every bounded sublevel |

## 8. Functional equation and selection architecture

An invertible functional-equation action commuting with `T` transports `F_T`, `R_T`, `H_0`,
`H_1`, and the connecting map.  It may reverse or conjugate the packet but cannot change
`(URP.27)`.  This matches the already formalized information-neutral lift through the common
recovery kernel.

The selection architecture is now exact:

1. finite nilpotent lineage is moved into derived carry and erased from the positive head;
2. off-unit semisimple scale modes are erased by the algebraic unitary radical;
3. joint source reconstruction therefore requires a marked exact-history leg;
4. cofinal properness forbids nonzero marked history at uniformly finite action;
5. only unit-modulus semisimple formation can survive both doctrines.

For the physical prime-radial multiplier

\[
 \lambda_p(\rho)=p^{2\operatorname{Re}\rho-1},
 \tag{URP.41}
\]

unit modulus is equivalent to `Re rho=1/2`.  This does **not** prove RH.  The missing theorem is a
single pre-zero, coefficient-faithful Xi packet whose positive leg is the unitary quotient, whose
history leg is the proper source grading, and whose joint recovery is proved before specializing
at a zero.  Once such a packet is constructed and its physical class has uniformly finite action,
the selection step is immediate.

## 9. Hostile boundaries

1. **Not every positive map is this reflector.**  The theorem concerns equivariant linear
   reporters into isometric actions.
2. **The quotient need not itself carry a canonical metric.**  In the finite-unipotent chart its
   action is trivial and any positive metric works; the quotient is canonical, the metric is not.
3. **Infinite-dimensional coinvariants may be non-Hausdorff.**  Completion and reduced homology
   remain separate observer doctrines.
4. **Hypertranscendence is not noncompactness.**  It appears here as failure of finite formation
   depth/stabilization.  Compact recurrent positive orbits can coexist with unbounded derived
   history.
5. **Functional equation does not select.**  It is a chain automorphism and is information-neutral.
6. **No scalar determinant replaces the graded sequence.**  The visible head is zero after
   prolongation while its derived connecting class is nonzero.
7. **No RH landing is asserted.**  Equation `(URP.41)` becomes useful only after the literal joint
   packet and finite-action admission are constructed.

## 10. External parentage

The components are classical:

- coinvariants and their derived group homology;
- Jordan modules and long exact homology sequences;
- persistence modules;
- positive-unitary semisimplicity;
- proper actions.

Current Jacobs--de Leeuw--Glicksberg theory likewise separates reversible unitary and stable parts
of suitable Banach representations:
[Barthmann--Farhangi--Kuznetsova, 2025](https://arxiv.org/abs/2509.24003).
Classical spectral synthesis reconstructs translation-invariant spaces from exponential monomials
on the real line, with higher-dimensional failures:
[Szekelyhidi, 2025 revision](https://arxiv.org/abs/2306.17438).
Vector-valued finite-translate/exponential-polynomial synthesis has its own sharp finite-rank
boundaries:
[Laczkovich, 2020](https://arxiv.org/abs/2004.08936).

These parents classify reversible or spectrally synthesized pieces.  The corpus-wide synthesis
here adds a specific law interpretation:

> positive observation is a derived formation functor; no-go classes are its connecting carries;
> prolongation transports rather than destroys them; source properness is the selection law.

## 11. Lean certificate

Formal module:

`GaloisForLFunctions.HTGeometry.ConstitutiveUnitaryReflectionPersistence`

The module proves:

- `map_finiteUnipotentFormationSubmodule_le`;
- `map_unitaryFormationRadical_le`;
- `unitaryFormationReflectionMap` and generator formula;
- identity and composition laws;
- general migrating-horizon noninjectivity criterion;
- explicit `J_2 -> J_3` formation cell;
- exact radical/head-kernel identities;
- quotient-head linear equivalences;
- old/new unit-head conservation;
- migrated-horizon annihilation for every unitary reporter;
- `Q(i)=0` and noninjectivity;
- polynomial old-head/next-boundary migration.

The pre-existing modules supply the positive-unitary radical theorem and exact affine source-depth
gauge.

## Gates

- [x] 0 -> 1: functorial quotient, exact Jordan cell, source-independent statement
- [x] 1 -> 2: full proofs of functoriality, derived carry, arbitrary-depth persistence, polynomial
  prediction, and properness fusion
- [x] 2 -> 3: scratch check and direct file check passed; leaf target
  `GaloisForLFunctions.HTGeometry.ConstitutiveUnitaryReflectionPersistence` built; key declarations
  use only `propext`, `Classical.choice`, and `Quot.sound`; umbrella import wired without building
  umbrella
- [ ] 3 -> 4: literal jointly recoverable Xi packet and unconditional finite-action admission

## Log

- 2026-08-18 -- spectral-synthesis/JdLG audit rejected reversible/stable classification as field
  core.  Pivoted to derived nonexactness of the positive quotient.
- 2026-08-18 -- proved functorial forced quotient, exact Jordan non-left-exactness, connecting carry,
  arbitrary one-step lifetime, polynomial successor migration, and properness extinction law.
