# Derived selection geometry of noncommuting reductions

- **ID:** `derived-selection-geometry-noncommuting-reductions`
- **Stage:** 1-in-progress
- **Type:** NEW MATHEMATICAL FIELD CANDIDATE / RH-HGT META-THEORY
- **Scientific status:** `[KINEMATICS PARTLY PROVED] [DYNAMICS OPEN] [NOT RH]`
- **Paper theorem:**
  `../../2-fully-proven/derived-selection-geometry/universal-monodromy-cartier-torsion-fitting-energy-law.md`
- **Supersedes:** representation-first Source--Observer Relativity v1 in
  `../noncommuting-exactification-geometry/source-observer-relativity-and-all-route-field-law.md`.

## 0. Hostile status

The representation-first conjecture is false as a frontier description.  The Stage-4 corpus
already constructs literal arithmetic sources, multiplicity-faithful divisor landings,
Gamma/co-Poisson comparisons, Green/Hodge geometry, singular residues, and one-port Stokes
polarizations.  The unresolved problem is **selection after representation**, not failure to place
the three mathematical faces in one carrier.

The candidate higher field is therefore not a new ambient space.  It studies how exactification,
completion, quotienting, reflection, and specialization fail to commute, and treats the surviving
derived class as the geometric object.

Call it **Derived Selection Geometry (`DSG`)**.

This name is provisional.  Derived algebraic geometry, Fitting ideals, cyclic homology,
quasi-abelian completion, boundary relations, and singular transgression are established parent
theories.  `DSG` earns separate status only if it proves an essential-image/selection theorem
which none of those parents supplies and which has faithful realizations across the audited RH and
hypertranscendental routes.

## 1. The Newton-to-GR change of ontology

The unsuccessful “Newtonian” ontology is:

```text
one function or operator in one ambient category
  + several constraints imposed on its points/spectrum
  -> select the physical solution.
```

That ontology makes arithmetic, Fourier/spectral, and geometric/Hodge precision compete for one
completion.  It encourages new carriers, positive forms, or topologies even after all those organs
have been constructed.

The proposed relativistic ontology is:

```text
arithmetic exactification ----- observer completion
          |                            |
          |                            |
divisor specialization ------ physical reduction

geometry = derived defect of this square;
metric   = Fitting/discriminant shadow of that defect;
dynamics = source-pure law deciding whether the defect class is null.
```

Objects do not have an observer-independent “completed constraint.”  What is invariant is the
base-change cone comparing orders of reduction.  A regular observer sees its degree-zero quotient;
a singular observer sees its `Tor`, `Ext`, Bockstein, residue, or relative Green class.  Different
RH routes are candidate realization functors from the same derived selection object, not partial
representations of an unknown point set.

## 2. Typed fundamental object

A **selection field** consists of the following typed data.

### 2.1 Arithmetic source

1. A source algebra or exact category `A_src` independent of any divisor point.
2. A source complex `(C,b)` with literal coefficients, prime/depth labels, multiplicity grading,
   reflection, and a distinguished detector.
3. When available, a contraction `s` with `bs+sb=1`.  Such a contraction is evidence against
   source homology, not evidence for it.

### 2.2 Reduction parameter

1. A parameter scheme or analytic base `X` of comparison characters.
2. A selected Cartier wall `H=V(I)` defined before pulling back along a target divisor.
3. A reflection `sigma` preserving `H` and reversing its conormal orientation.

For the constructed two-leg arithmetic comparison,

\[
 X=\mathbb G_m,\qquad I=(q-1),\qquad \sigma(q)=q^{-1}.
\tag{2.1}
\]

### 2.3 Competing reductions

Two functorial paths from the source into a physical category:

\[
                       F,G:C\longrightarrow V_X.
\tag{2.2}
\]

Their unsquared comparison defect is

\[
                              \Delta=F-G.
\tag{2.3}
\]

A physical symmetry/transport `T` determines the smallest stable boundary

\[
 B_{\min}=\sum_{j\geq0}\operatorname{im}(T^j\Delta),
\tag{2.4}
\]

whenever this sum is defined.  The **incompatibility sheaf** is

\[
                              \mathcal Q=V_X/B_{\min}.
\tag{2.5}
\]

### 2.4 Derived selection tensor

Let `Comp` denote observer completion/reduction and `Sp` specialization to a physical or divisor
fibre.  The candidate universal tensor is the cone of the base-change comparison

\[
 \mathfrak C_{\rm sel}
 =\operatorname{Cone}\!\left(
   \operatorname{Comp}\,\operatorname{Sp}
   \longrightarrow
   \operatorname{Sp}\,\operatorname{Comp}
  \right).
\tag{2.6}
\]

Its possible shadows are:

\[
 H^0(\mathfrak C_{\rm sel})\quad\text{ordinary comparison defect},
\]

\[
 H^{-1}(\mathfrak C_{\rm sel})\quad\text{attainment/Tor defect},
\]

\[
 \mathbf R\!\operatorname{Hom}(\mathcal Q,\mathcal O_X)
 \quad\text{singular dual/Bockstein defect}.
\tag{2.7}
\]

Equation `(2.6)` is a research definition, not yet a constructed all-prime arithmetic object.
The universal monodromy theorem proves its exact local model for the already constructed two-leg
family.

### 2.5 Metric shadow

The ordinary positive/Hodge observer does not receive `mathcal Q` itself.  Its canonical scalar
shadow is the Fitting support

\[
                     \operatorname{Fitt}_0(\mathcal Q).
\tag{2.8}
\]

This separates three logically different statements:

1. the defect exists;
2. a positive scalar detects its support;
3. arithmetic dynamics forces the defect class to be null.

The corpus has many theorems of types 1 and 2.  RH needs type 3.

## 3. First exact local field law

The paper theorem proves that the universal physical two-leg family has

\[
 R=k[q,q^{-1}],\qquad
 \mathcal Q\cong(R/(q-1))^2,
\tag{3.1}
\]

The literal cyclic source already carries an anti-diagonal boundary.  After scalar extension to
`R`, its invariant trace and source-pointed landing give the smaller quotient

\[
 \mathcal Q_{\rm src}\cong R/(q-1),
\tag{3.1a}
\]

with exact sequence

\[
 0\longrightarrow (R/(q-1))(1,-1)
 \longrightarrow\mathcal Q
 \longrightarrow\mathcal Q_{\rm src}\longrightarrow0.
\tag{3.1b}
\]

Thus the physical identity fibre has two reflected legs, while literal cyclic incidence leaves one
absolute orientation line.

and

\[
 \operatorname{Hom}_R(\mathcal Q,P)=0
 \quad\text{for every }(q-1)\text{-torsion-free }P,
\tag{3.2}
\]

while

\[
 \operatorname{Ext}^1_R(\mathcal Q,R)\cong\mathcal Q,
 \qquad
 \operatorname{Tor}_1^R(\mathcal Q,R/(q-1))\cong k^2.
\tag{3.3}
\]

For the source orientation line, the corresponding `Ext^1` and `Tor_1` are each one-dimensional.

Reflection reverses the conormal `I/I^2`, but the positive energy is

\[
 q+q^{-1}-2={(q-1)^2\over q},
\]

so

\[
 \boxed{
 (q+q^{-1}-2)=\operatorname{Fitt}_0(\mathcal Q)=(q-1)^2.
 }
\tag{3.4}
\]

Equivalently,

\[
 \operatorname{Fitt}_0(\mathcal Q)
 =\operatorname{Fitt}_0(\mathcal Q_{\rm src})^2.
\tag{3.5}
\]

This is the first non-metaphorical DSG field law:

> literal source orientation is one Cartier-relative line; the physical two-leg family doubles it;
> regular positive energy is the square of its Fitting ideal.

It explains why positivity can detect horizontal displacement exactly yet provide no independent
source annihilation: it is a determinant of the obstruction, not the equation that kills it.

The live source--reporter ambidexterity curvature is

\[
 K(q)=q-q^{-1}={(q-1)(q+1)\over q}.
\tag{3.6}
\]

Locally at `q=1`, `(K)=Fitt_0(mathcal Q_src)`, and

\[
 K^2={(q+1)^2\over q}\,(q+q^{-1}-2).
\tag{3.7}
\]

The multiplier is a unit at the critical wall.  Hence categorical ambidexterity curvature is an
unsquared source-conormal generator, while Stokes energy is its squared metric shadow.  This is an
exact cross-route factorization, not inference from a shared radical.

### 3.1 Selection coframe geometry

Let `e=[q-1]` generate the conormal line `I/I^2`.  The normal-cone algebra is

\[
 \operatorname{gr}_I R\cong k[e].
\tag{3.8}
\]

The Pipeline-2 theorem proves

\[
 \sigma(e)=-e,
 \qquad
 \operatorname{in}_I(K)=2e,
 \qquad
 \operatorname{in}_I(E)=e^2.
\tag{3.9}
\]

At physical rank `M`, the coframe and metric scale as

\[
                         e\longmapsto Me,
 \qquad
                         e^2\longmapsto M^2e^2.
\tag{3.10}
\]

This is the exact sense in which DSG is closer to general relativity than the old observer-field
metaphor.  Arithmetic/source data provide an oriented coframe; reflection and Hodge/Stokes
polarization build a metric from it.  A metric determines squared normal distance but not the
coframe orientation or its source equation.  The missing dynamics must therefore be stated on the
source coframe/derived class before metric formation.

## 4. Source primitive-transgression law

There is a second dependency-closed bridge.  Suppose `(C,b)` has a contraction `s`, `(H,d)` is a
target complex, and `A:C -> H` is a comparison with chain defect

\[
                             \Omega=Ab-dA.
\tag{4.1}
\]

Then

\[
 \boxed{A=dAs+\Omega s+Asb.}
\tag{4.2}
\]

For every source cycle `z`,

\[
 Az=d(Asz)+\Omega(sz).
\tag{4.3}
\]

Hence any target class surviving from a contractible source is represented by the comparison
defect evaluated on the source primitive.  Two-replica polarization is only the Gram shadow of
`Omega s`, not the first source invariant.

### Proof

Use `1=bs+sb`:

\[
 A=A(bs+sb)=Abs+Asb=(dA+\Omega)s+Asb.
\]

If `bz=0`, equation `(4.3)` follows. `QED`

### Consequence

The strictly contracted Deninger height-bar and first Sullivan sources cannot acquire decisive
homology merely by taking replicas or positive completions which preserve the contraction.  A
surviving class must come from:

1. failure to transport the primitive;
2. a nonflat specialization/base change;
3. a non-strict completion;
4. a later genuine multiplicative syzygy; or
5. a nonzero comparison defect `Omega`.

This kills the conjecture that balanced-bar homology can directly supply the Stage-4 arithmetic
source-null-homology theorem.

## 5. The three mathematical faces in DSG

| Face | DSG organ | What it contributes | What it cannot contribute alone |
|---|---|---|---|
| Arithmetic | source complex, coefficient ring, prime/depth incidence, literal boundary | provenance, integrality, multiplicity, candidate null-homology | analytic admission, positive metric |
| Fourier/spectral | comparison and observer functor, completion, divisor specialization | transform, continuation, physical jet, asymptotic reader | source-pure selection if completion is nonexact |
| Geometric/Hodge | support of `mathcal Q`, normal/conormal, `Ext/Tor`, Fitting form, one-port inertia | topology of failure, singular relative class, positive metric shadow | arithmetic reason that class vanishes |

They do not merge as three coordinate systems on one object.  They compose as three functors whose
order matters.  Their joint invariant is the derived failure of interchange.

## 6. Why precision in one face destroys another

The user-observed “Heisenberg” phenomenon becomes an exact order-of-operations law.

### 6.1 Exactification versus completion

If completion preserves a source contraction continuously, completed source remains contractible.
If a physical class appears, either contraction does not extend, completion is non-strict, or the
comparison has curvature.  Making exactness topologically strict can therefore erase the class.

### 6.2 Regular observation versus Cartier support

The incompatibility sheaf is torsion on `H`.  A torsion-free vector-bundle or regular Hilbert
reader has no nonzero `Hom` from it.  Making observer regular erases the selection datum; retaining
it forces a singular/derived reader.

### 6.3 Positivity versus orientation

Reflection sends the normal coordinate to its negative.  Fitting energy squares it.  Making the
metric positive and reflection-invariant erases the unsquared side.  Orientation must be retained
before Hermitian squaring.

### 6.4 Breadth versus boundedness

A response equal to one nonzero coefficient on `N` orthogonal source labels has norm proportional
to `sqrt(N)` and is nonclosable at infinite breadth.  Making the all-prime reader bounded erases
coefficient-faithful unit response.

### 6.5 Depth versus finite Rees order

Off-neutral reflected prime-valuation sectors have growth beyond every finite Rees grade.  Making
depth comparison finite-order erases modular orientation.  DSG records this as a failure of the
comparison to lie in a regular finite-order essential image.

These are separate theorems, not one numerical uncertainty inequality.  Their conjunction says a
successful selector must be simultaneously source-pointed, singular in breadth, derived at the
Cartier wall, beyond finite depth order, and unsquared before scalarization.

## 7. Route atlas under hostile labels

| Route/family | Constructed DSG shadow | Exact unresolved source law | Status |
|---|---|---|---|
| Arithmetic cyclic-to-paracyclic dagger | physical `mathcal Q=(R/(q-1))^2`; source quotient `mathcal Q_src=R/(q-1)` after anti-diagonal cyclic boundary; residue `(q-1)c epsilon` | literal arithmetic cyclic boundary or independent zero-residue identity | exact local DSG model; dynamics open and RH-bearing |
| Stokes/microlocal Witt | positive coarea minus one rank square; same rank is determinant exponent | source law on unique central port | Fitting shadow identified by `(3.4)` |
| Source orientation/Green | one absolute orientation line; all extra data are relative primitive escape | singular source-pointed Green transport | regular quotient classification complete |
| Source--reporter ambidexterity | framed nonflat curvature `K=q-q^{-1}` and finite top-conormal transfer | strict coefficient-faithful transport into completed Xi boundary | `K` generates source Cartier ideal locally; dynamics still open |
| Deninger Route L | strict height source, balanced bar, first Sullivan primitive, Möbius--Fourier commutator | identify commutator as physical boundary of strict cofinal Euler--Gamma differential; unsquared Green--Stokes annihilation | primitive-transgression architecture; comparison still open |
| Burnol Route R | coefficient-faithful singular Bockstein and two reflected residues | source-derived odd Cartier trace orientation/dissipativity; separately uniform inverse-domain admission | `Ext/Bockstein` shadow plausible; exact chain map unproved |
| Route E | literal Gibbs source, odd cube, moving seam, analytic antiscale frame | source-predeclared moving flux/Carleson law at physical scale | predicts nonseparable higher incidence, not scalar Fitting alone |
| Mass--Xi | true-prime heat comparison and complete filtered Turan detector | coherent filtered-Turan determinant from literal prime--Gamma source | two-replica metric shadow; not source class |
| Suzuki two-angle route | arithmetic tangent, torque, partial matching | real-axis return coherence and source-derived cofinal schedule | attainment/base-change aspect plausible; not identified |
| Hedenmalm/Nyman | divisor-faithful dense nonclosed radical | source-selected singular boundary condition | regular completion excluded |
| HT source geometry | exact differential matroids, finite/infinite annihilator horizons, dense gauge leaves | none by itself; must couple to selection tensor | controls source complexity, not divisor selection |

No row is called a DSG realization until an explicit chain-level or module-level map is proved.
Common vanishing radicals do not establish equality of classes.

## 8. Hypertranscendence reinterpreted

Hypertranscendence is not the force that selects `q=1`.  The corpus contains positive,
divisor-faithful, and off-line-compatible hypertranscendental systems.  DSG assigns it a different
role:

1. HT measures failure of a uniform finite differential chart on source space.
2. Bounded annihilator order is compact; genuine inverse-limit HT requires order escape.
3. Source breadth/depth determines how singular a faithful realization must be.
4. Selection is a separate horizontal question: whether an arithmetic comparison class is
   supported or null on the Cartier wall.

Thus HT supplies the infinite-dimensional matter/provenance sector; `mathcal Q_src` supplies the
oriented source defect; `mathcal Q` supplies the physical two-leg defect; the Fitting form supplies
the observer metric.  Conflating them explains why
large differential-independence theorems did not locate zeros.

## 9. New predictions

### P1. Regular-Hom exclusion

Any proposed selector which factors through a locally free/torsion-free family over the monodromy
base is blind to the universal two-leg incompatibility class.  A nonzero such map falsifies the
Cartier model.

### P2. Fitting-shadow test

Any positive reflected energy built solely from the two ordered defects must generate the square
of the Cartier ideal locally.  If it distinguishes orientation or supplies source null-homology,
it contains extra unsquared arithmetic data.

### P3. Bockstein location

The first coefficient-faithful selector must occur as a connecting morphism, residue, `Ext^1`,
`Tor_1`, or equivalent relative class.  A bounded interior germ reader cannot be first.

### P4. Rank-powered isogeny

Replacing `q` by `q^M` does not create a transverse selector near `q=1`.  It preserves Cartier
support, scales conormal orientation by `M`, and leaves the Fitting order two.  This predicts that
central determinant rank, scalar anomaly towers, and same-prime monodromy tests are locally
isogenous and have the same radical.

### P5. Multiplicity is not Cartier thickening

The constructed physical residue separates analytic multiplicity grade through `c_rho`, while
the monodromy ideal remains first order `(q-1)`.  A model identifying zero multiplicity with
`(q-1)^r`-thickening conflates two filtrations unless it constructs a new source map between them.

### P6. Disconnected multiport law

If a Stokes interaction graph has `b` connected components, DSG predicts `b` central Cartier
ports and a direct sum of two-leg torsion modules, one for each component.  Fusion to one port must
be an explicit relation, not an assumption.

### P7. Unsquared-before-positive

Every route that squares before applying its source primitive or relative boundary loses the odd
conormal.  A successful diagonal one-body proof would falsify the claimed universality.

### P8. Source-purity target

A real advance must construct, before Xi specialization, a morphism from the literal arithmetic
cyclic source into the derived dual of `mathcal Q` and prove a boundary identity there.  Merely
pulling back `mathcal Q` along `q=delta_n(rho)` restates RH.

## 10. Conjecture loop ledger

### Loop A — representation field

**Conjecture:** source, spectral, and geometric faces cannot coexist and require a larger carrier.

**Failure:** Stage 4 constructs all three simultaneously.  Problem is selection.  SOR v1 retired.

### Loop B — curvature-work energy

**Conjecture:** a source Gauss--Hodge identity plus nonpositive curvature work supplies leverage.

**Failure:** identity is correct, but sign is not source-produced; in Route R it renames the open
odd Bockstein inequality.  DSG demotes energy to a metric shadow.

### Loop C — bar contraction supplies null-homology

**Conjecture:** strict balanced-bar/first-Sullivan contraction transports to the physical
arithmetic cyclic defect.

**Failure:** sources differ; transport would erase the trace-one prime cycle.  Existing para-`S`
merger also collapses to an already constructed counterboundary with the same radical.

### Loop D — modular boost/end holonomy

**Conjecture:** off-line displacement is asymptotic boost holonomy invisible at finite depth.

**Partial survivor:** rapidity and finite gauge-cost geometry are exact but already present in
Lorentz/Hurwitz and Rees cards.  It does not explain positive-squared versus singular-unsquared
readers.

### Loop E — universal Cartier incompatibility

**Conjecture:** fibrewise zero/full boundary is specialization of a torsion sheaf; reflected
energy is its discriminant.

**Proof:** Theorems 3.1--5.1 in the Pipeline-2 paper prove

\[
 \mathcal Q=(R/(q-1))^2,
 \qquad
 \mathcal Q_{\rm src}=R/(q-1),
 \qquad
 \operatorname{Fitt}_0(\mathcal Q)=(q+q^{-1}-2).
\]

**Status:** survives internal hostile audit as new corpus consequence; external priority open.

### Loop F — derived arithmetic purity

**Conjecture:** literal arithmetic source has a canonical class in
`Ext^1_R(mathcal Q_src,R)` whose cyclic boundary forces physical defect null-homology.

**Status:** `[OPEN]`.  This is the first DSG dynamics, not kinematics.  It may still be RH itself.
The next attack must construct the map before specializing at any zero and test it on the
ordinary-prime trace-one cycle.

### Loop G — the derived class selects its own support

**Conjecture:** a canonical `Ext/Tor` generator of the Cartier selection sheaf forces every Xi
point onto `q=1`.

**Attack:** at a field point `q=\lambda`, the derived source fibre is
`[k\xrightarrow{\lambda-1}k]`.  It is zero for `\lambda\ne1` and `k\oplus k[1]` for
`\lambda=1`.  Every construction internal to the thick category generated by the source sheaf is
supported on `q=1`; all its identities hold vacuously off support.

**Failure:** nonvanishing of that fibre is equivalent to `\lambda=1`.  At Xi points this is RH.
The derived class cannot select its own support.

**Positive survivor:** dynamics must act before quotienting, on the ambient monodromy family or
literal arithmetic source complex, and must preserve an independently nonzero source witness.
This is paper-proved in Stage 2, Theorems 8A.1--8A.2.

## 11. Relation to black-hole/wormhole language

There is one precise mathematical analogy and no established physical identification.

```text
generic monodromy fibres q != 1      regular exterior region
Cartier wall H: q = 1                horizon/collision locus
reflected branches q and q^{-1}      two oriented sides
Tor/Ext supported on H               boundary-stored relative information
Fitting energy                        orientation-even observer shadow
```

Calling `H` a holographic surface is acceptable only as intuition for support on a boundary.
No theorem connects this object to black-hole entropy, spacetime wormholes, quantum gravity, or a
physical time coordinate.  Such claims remain outside the mathematics.

## 12. External collision boundary

Broad literature audit finds mature parents for every generic ingredient:

- cyclic/paracyclic strictification and coefficient-induced cyclicity;
- quasi-abelian and derived repair of non-strict exactness;
- relation-valued boundary systems and passive Pontryagin realizations;
- contextual/global-section obstructions;
- Lorentzian/Hodge one-negative-direction theorems;
- singular Green/Fourier--Laplace transgression;
- Hankel/Turan determinant hierarchies.
- Laurent-ring Alexander/monodromy torsion, Fitting characteristic varieties, and tangent cones at
  the identity;
- coframe formulations in which a coframe is prior to the induced metric.

Therefore none of those nouns establishes novelty.  Candidate-new residue is the exact
Riemann-source conjunction:

1. one complete regular orientation quotient;
2. one Stokes coarea/determinant rank port;
3. one explicit arithmetic paracyclic residue;
4. one source Cartier line `mathcal Q_src` and its two-leg physical extension `mathcal Q`;
5. equality of reflected energy with `Fitt_0(mathcal Q)=Fitt_0(mathcal Q_src)^2`;
6. proof that regular readers have zero `Hom` while derived readers retain `Ext/Tor`.

The missing source-only selector remains unproved.  External absence is not a priority proof.

The closest priority collisions are Cohen--Suciu
([arXiv:math/9801048](https://arxiv.org/abs/math/9801048)), where Fitting ideals of Alexander
invariants define characteristic subvarieties in an algebraic torus and the tangent cone at the
identity is a resonance variety; Dimca--Nemethi
([arXiv:math/0201291](https://arxiv.org/abs/math/0201291)), where torsion invariants of multiple
fibres factor through a universal monodromy module; Budur--Liu--Wang
([arXiv:1609.06478](https://arxiv.org/abs/1609.06478)), where torsion homology is a Laurent-ring
monodromy module; and Itin ([arXiv:0711.4209](https://arxiv.org/abs/0711.4209)), where a coframe is
the primary field and metric/connection structures are induced from it.  These precedents kill a
broad novelty claim for Sections 2--3.  They do not state the exact arithmetic source quotient,
two-leg extension, `K^2=\text{unit}\cdot E`, or the Riemann/Stokes support-selection no-go.

## 13. Promotion and kill gates

### Already closed on paper

- [x] universal monodromy family and minimal stable boundary;
- [x] Cartier torsion presentation;
- [x] literal cyclic anti-diagonal quotient and unique source orientation line;
- [x] annihilator and zeroth Fitting ideal;
- [x] regular-reader `Hom` exclusion;
- [x] `Ext^1` and identity-fibre `Tor_1` computation;
- [x] reflection-odd conormal and reflection-even energy identity;
- [x] rank-powered local isogeny;
- [x] finite-port exterior fracture and breadth nonclosability;
- [x] primitive-transgression factorization;
- [x] exact Riemann/Stokes pullback without RH inference.
- [x] derived point-fibre computation and proof that the selection sheaf cannot select its own
  support.

### Required before claiming a new field

- [ ] construct all-prime arithmetic completion--specialization square;
- [ ] prove source-presentation/Morita invariance of `mathfrak C_sel`;
- [ ] prove explicit realization maps into Route L and one of Route R/E/Mass--Xi;
- [ ] prove one non-zeta HT example where DSG predicts a new theorem;
- [ ] classify allowable singular readers without collapsing to arbitrary `Ext` packaging;
- [ ] establish an essential-image condition excluding fitted target torsion modules;
- [ ] complete external specialist priority review.

### RH dynamics gate

- [ ] construct a pre-divisor arithmetic `Ext^1` or mapping-cone class;
- [ ] prove its boundary/null-homology independently of Xi zero location;
- [ ] preserve ordinary-prime trace one and multiplicity grading;
- [ ] show its physical realization is the existing `(q-1)c epsilon` residue;
- [ ] only then infer `q=1` at divisor fibres.

### Immediate kill conditions

Retire DSG as a claimed new field if:

1. every natural model is merely a standard derived base-change computation with no new
   essential-image theorem;
2. no explicit all-prime arithmetic comparison cone can be constructed;
3. route correspondences remain common-radical analogies without chain maps;
4. the singular class can be chosen arbitrarily after seeing the target divisor;
5. a regular source-faithful scalar observer detects the claimed torsion class;
6. the purported dynamics reduces to assuming `q=1`, Fitting-energy zero, source-null-homology,
   or another RH-equivalent statement.
