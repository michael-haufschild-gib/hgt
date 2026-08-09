# Pro-valuated source-Grushin event geometry and determinantal shadow conjecture

- **ID:** `cmr-pro-valuated-source-grushin-event-geometry`
- **Stage:** 1 — in progress
- **Type:** FROZEN FIELD-DYNAMICS CONJECTURE / HIGHER PIVOT
- **Field:** Constraint-Motive Relativity (CMR)
- **Status:** `[CONJECTURE] [OPEN CORE] [FRANKENSTEIN SYNTHESIS ALLOWED]`
  `[PRE-XI PRODUCER PARTIAL] [WHOLE-CORPUS FIELD NOT CLAIMED] [NOT RH]`
  `[NO LEAN WRITTEN OR BUILT]`
- **Exact bridge seeds:**
  `../../2-fully-proven/constraint-motive-relativity/valuation-coframe-operation-defect-rank-and-determinant-line-law.md`;
  `../../2-fully-proven/constraint-motive-relativity/helson-coefficient-fredholm-crossing-response-law.md`;
  `../../2-fully-proven/constraint-motive-relativity/prime-gamma-bockstein-rees-event-germ-and-cofinal-normal-nonuniformity-law.md`.
- **Exact source-Grushin seed:**
  `../../2-fully-proven/new_scientific_knowledge/hedenmalm/hedenmalm-theta-source-compressed-inverse-determinant.md`;
  `../../../../../formal/GaloisForLFunctions/HTGeometry/SourceGrushinInverse.lean`;
  `../../../../../formal/GaloisForLFunctions/RHTower/HedenmalmThetaCompactDivisorEigenmode.lean`.
- **Arithmetic parent:**
  `../../2-fully-proven/constraint-relativity/prime-valuation-cyclic-coframe-and-diagonal-dagger-defect-law.md`.
- **Field parent:** `stratified-source-response-and-law-event-geometry.md`.

## 1. Public sentence

> A source law defines a filtered comparison complex. Law events are failures of invertibility;
> Fitting and Rees data retain their order and normal direction, while determinant lines provide
> oriented one-port shadows.

The earlier determinant-first version was too small. Finite determinant orientations can all be
positive while comparison scales collapse to zero cofinally. The primary object must retain the
comparison complex, its discriminant filtration, its valued normal direction, and its completion
doctrine.

“Holography” is used only for the exact mathematical passage from a high-rank anomaly to a
one-dimensional determinant/orientation shadow. No black-hole, wormhole, entropy, or
bulk/boundary identity is asserted.

## 2. Field hierarchy

The proposed local event geometry has five noninterchangeable layers:

\[
 \boxed{
 \text{source comparison complex}
 \longrightarrow
 \text{Fitting discriminant}
 \longrightarrow
 \text{Rees/valuated normal}
 \longrightarrow
 \text{Fredholm determinant section}
 \longrightarrow
 \text{real crossing orientation}.}
\tag{PVG.1}
\]

1. **Source comparison complex.** A source-augmented Grushin or chain comparison is defined before
   its event locus.
2. **Fitting discriminant.** Failure of invertibility is recorded with rank and determinantal
   filtration, not only as a zero set.
3. **Rees/valuated normal.** Contact order, transverse direction, and conditioning are retained.
4. **Fredholm determinant section.** In an admitted infinite-dimensional completion, the
   discriminant is represented by a determinant section.
5. **Crossing orientation.** At a regular real wall, the derivative of that section defines an
   oriented one-port receiver.

Three determinant notions must remain distinct:

- determinant **holonomy** may be nonzero and vary without any event;
- determinant **section** may vanish on the noninvertibility discriminant;
- determinant **orientation line** carries the transverse crossing sign at a regular zero.

The corpus proves common arithmetic central holonomy can change while structural Stokes contact,
gap, and inertia remain fixed. Treating these three notions as one object is therefore false.

## 3. Exact evidence already available

### 3.1 Raw reporter-rank budget

For `N` independently coframed source classes, a chain event killing all `N` has coframe-transport
anomaly rank `N`. No rank-one linear port factors that raw anomaly. Its top exterior power is a
canonical determinant-line isomorphism after matched finite-cutoff bases, but loses singular
values, filtration, contact order, and cofinal conditioning.

### 3.2 Source-Grushin spectral event

An invertible source-augmented map `G_0` and compact injection `J` canonically give

\[
 B=JG_0^{-1},\qquad
 G_zG_0^{-1}=I+zB,
\tag{PVG.2}
\]

and, for `z!=0`,

\[
 \ker G_z\ne0
 \quad\Longleftrightarrow\quad
 -z^{-1}\in\sigma_p(B).
\tag{PVG.3}
\]

The theta specialization constructs `B` solely from the completed source density. This is a
literal pre-zero Fredholm event mechanism. Global determinant identification still needs its
stated trace/multiplicity bridge.

### 3.3 Coefficient-faithful global receiver

For `a in ell^1_d`, the Helson operator `K_a(j,k)=a_(jk)` is trace class and coefficient faithful.
At a simple real wall its crossing covector is

\[
 h\longmapsto-\sum_nh_n\sum_{jk=n}\overline{u_j}u_k.
\tag{PVG.4}
\]

This proves exact source-coefficient response can reach a scalar Fredholm wall before Xi
specialization. The threshold and eigenline are not yet selected by the arithmetic source.

### 3.4 Primewise valued normal comparison

The Gamma determinant-transgression coordinate `beta_p(t)` and adjacent-depth Rees coordinate
`w_p(t)` satisfy the analytic event-germ identity

\[
 \beta_p(t)=-\widetilde g_p(t)w_p(t),
 \qquad
 \widetilde g_p(0)=L_p
 =\frac{4p^3(\log p)^2}{(p+1)^2(p-1)(2p-1)}>0.
\tag{PVG.5}
\]

Thus, after removing the explicit reflection-odd minus, local coorientations and transverse
derivatives agree through a positive valued slope. Raw `beta_p` and `w_p` have opposite
coorientation. But

\[
 L_p\sim\frac{2(\log p)^2}{p}\longrightarrow0.
\tag{PVG.6}
\]

The diagonal slope map has no bounded inverse on the unweighted all-prime `ell^2`, `c0`, or
`ell^infinity` models. Primewise line orientation is therefore insufficient; the cofinal geometry
must retain valuations and topology.

## 4. Frozen conjecture

Let `P_src` be the pre-divisor rational-adelic source presentation equipped with its full
ordinary-prime valuation coframe. There exists a source-normal **pro-valuated comparison object**

\[
 \mathfrak G_{\rm ar}
 \quad\text{over finite prime apertures and the archimedean source port},
\tag{PVG.7}
\]

constructed without a Xi zero, satisfying the following clauses.

1. **Source-augmented complexes.** For every finite aperture `F`, `G_F(z)` is a source-derived
   Grushin/chain comparison complex; the base operator, injection, and intervention law are fixed
   before its discriminant is inspected.
2. **Full finite reporter anomaly.** Its coframe transport defect on the prime span has the rank
   required by the valuation-coframe theorem. The anomaly is not assumed to vanish and is not
   replaced by a scalar port.
3. **Fitting filtration.** The determinantal ideals of `G_F(z)` define a compatible discriminant
   filtration recording rank loss and contact order.
4. **Valued Rees normal.** The first noninvertible Fitting layer has a source-normal Rees
   deformation. Primewise normal comparisons recover `(PVG.5)`, including the slopes `L_p`.
5. **Pro topology.** Aperture enlargement carries source-selected weights/lattices or a
   pro-bornological topology in which the slope correspondence is a typed morphism. Whether its
   inverse is admitted, unbounded, or Tate is a theorem of the topology, not a choice hidden by
   scalar orientation.
6. **Global Fredholm realization.** An admitted completion sends the comparison complex to a
   source-augmented Fredholm family. The determinant section detects its noninvertibility
   discriminant. The theta source-Grushin and Helson constructions are test charts, not mandated
   as the unique realization.
7. **Local boundary realization.** A local Gamma/Voronoi--Hankel, co-Poisson, epsilon, or Stokes
   realization sends the same valued normal object to a boundary event line.
8. **Response compatibility.** At an independently defined non-RH regular wall, global Fredholm
   response and local boundary response are images of the same valued normal section. At prime
   `p`, the comparison carries transverse derivatives as
   `partial_t beta_p(0)=-L_p partial_t w_p(0)`.
9. **Orientation shadow.** Only after clauses 1--8 does the top determinant/orientation line
   supply a one-port holographic shadow. Its positive norm square may be a phase-blind energy; its
   unsquared line retains coorientation.

This is the frozen higher jump. It does not assert that every corpus organ is determinantal. It is
the proposed arithmetic--spectral--Stokes event sector inside the broader polydual CMR field.

## 5. Why this can explain genuine obstructions

The hierarchy predicts why familiar routes become mutually precise only one face at a time.

| Observed obstruction | Proposed higher explanation |
|---|---|
| full prime coframe versus one physical port | raw anomaly is high rank; one port is later determinant orientation |
| same zero radical but no chain nullhomology | zero set forgets reporter transport and Fitting depth |
| positive energy detects displacement but does not select it | norm square forgets unsquared valued normal orientation |
| finite primewise comparison but failed all-prime completion | slopes `L_p` collapse; topology is part of event geometry |
| common arithmetic twist changes determinant but not inertia | holonomy is horizontal; structural contact is a different event layer |
| source-Grushin spectralization without local landing | Fredholm discriminant exists before global-to-local normal compatibility |
| scalar Helson response with fitted threshold risk | receiver exists, but source selection and upstream reporter determinant are missing |
| finite exterior powers do not stabilize | cofinal object needs valued lattice/pro/Tate transition data |

This table covers one major cross-route obstruction complex. It does not yet derive Route-E
capacity, Mass affine successor, HT differential rank, or recurrence history cost. CMR retains
those as native organs; forcing them into `(PVG.1)` would be a new tunnel view.

## 6. Risky predictions

1. No rank-one **linear factorization of the full coframe exactification anomaly** can kill two or
   more independently coframed prime classes.
2. Every global comparison identifying the literal Gamma `beta_p` and adjacent-depth Rees `w_p`
   normalizations must expose a weight/topology compensating for `L_p->0`; an unweighted bounded
   equivalence between those coordinates is impossible. A different source-native normalization
   is not ruled out.
3. A determinant holonomy change alone has zero structural contact/inertia response in the
   present Stokes chart.
4. Any scalar Fredholm wall may exist independently, but it cannot claim full source
   coefficient-faithful exactification without the upstream rank/Fitting data.
5. Two global/local scalar functions with matching zeros can still have inequivalent valued
   normals. Equality of zero loci is not a field comparison.
6. If global source-Grushin/Helson response and local Gamma--Rees/Stokes response disagree on one
   source-fixed nonzero intervention after valued-normal transport, `(PVG.7)` is false.
7. Hypertranscendence forces non-finite-type source filtration, not automatically a determinant
   gerbe. A gerbe becomes available only after Fredholm/Tate admissibility, polarization, and
   transition valuations are constructed.
8. Any physical horizon application must derive the comparison complex, valued edge normal,
   determinant line, connection, and conjugate charge from the physical source. A one-port
   analogy alone does not count.

## 7. Falsifiers

The conjecture fails if:

1. `G_ar` is defined using Xi zeros, a chosen zero neighbourhood, or desired physical residue;
2. finite-cutoff reporter anomaly rank is smaller than the admitted valuation-coframe rank;
3. the determinant line is substituted for the Fitting filtration or valued normal;
4. cofinal compatibility is asserted from positive finite determinants while ignoring
   `L_p->0`;
5. weights/topology are chosen after comparing target coordinates;
6. the Fredholm threshold or eigenbranch is selected after inspecting the desired wall;
7. Gamma/Stokes data are appended as an unrelated factor rather than realized from the same
   comparison complex;
8. compatibility is checked only after independently scalarizing two real lines;
9. central determinant holonomy is claimed to change Puiseux contact or inertia in the existing
   common-twist chart;
10. “determinant gerbe” or “Tate” is used without aperture transition maps, valuations, and a
    source-selected polarization.

An independently defined non-RH generalized-prime family satisfying the clauses is a required
universality test, not a falsifier. It falsifies only an illicit claim that the geometry itself
selects the critical line.

## 8. Exact open core

`[OPEN CORE] [PRE_XI_PRO_VALUATED_GLOBAL_TO_LOCAL_EVENT_COMPARISON]`

1. Construct an explicit pre-Xi finite--infinity source comparison complex with its full
   prime-valuation transport matrix.
2. Compute its Fitting filtration and finite-aperture Rees normals.
3. Construct a weighted/pro-valued source normal topology and specify the slope map's image,
   strictness/closedness, dual reporter continuity, and aperture transitions. Determine whether
   `e_p -> L_p e_p` is a topological embedding, has an admitted unbounded inverse, or defines a
   legitimate Tate morphism. Mere continuity is insufficient and already holds in the unweighted
   models.
4. Realize the same comparison complex as a source-selected Fredholm family and a local
   Gamma--Stokes boundary family.
5. Prove response equality on one source-fixed nonzero intervention before Xi specialization.
6. Compare the valued normal lines first; only then compare their real determinant-orientation
   torsors.

## 9. Relation to physical time and holography

The exact mathematics suggests a disciplined physical hypothesis, not a theorem:

- closed boundary recurrence may be determinant holonomy after phase projection;
- open lifted history may live in the pro-valuated comparison complex before projection;
- an event horizon may carry an orientation/edge line derived from a singular normal comparison;
- a conjugate interior-time or length variable would have to pair with that line in a sourced
  symplectic/relative-duality structure.

No corpus theorem identifies `L_p`, the Fredholm determinant, or the Stokes line with black-hole
area, wormhole length, Brown--Susskind complexity, or physical time. A valid physics realization
must construct those operators and their pairing from the physical source.

## 10. Literature boundary

Grushin problems, Fitting ideals, deformation to the normal cone, Rees modules, Fredholm
determinants, determinant functors, Tate determinant gerbes, Helson matrices, epsilon lines,
irregular Riemann--Hilbert theory, spectral flow, and valued/pro categories are parent mathematics.

The open conjunction is source-specific: one rational-adelic comparison complex whose Fitting
normal, primewise Gamma--Rees slopes, admitted global Fredholm determinant, and local boundary
orientation are functorially compatible before Xi specialization. No novelty claim for the parent
machinery is needed.

## Gates

- [x] finite coframe-rank obstruction isolated
- [x] determinant-line finite positive survivor isolated
- [x] source-Grushin pre-zero Fredholm event exists
- [x] coefficient-faithful Helson crossing receiver constructed at paper level
- [x] primewise Gamma--Rees analytic event germ proved
- [x] cofinal slope collapse and unweighted inverse obstruction proved
- [x] determinant holonomy/section/orientation separated
- [x] generalized-prime test and target-fitting falsifiers stated
- [ ] construct literal finite--infinity comparison complex
- [ ] compute its Fitting filtration and valued Rees normals
- [ ] construct source-selected weighted/pro topology
- [ ] derive source-selected global Fredholm response
- [ ] derive local Gamma--Stokes response from same complex
- [ ] prove valued-normal and line-level response compatibility
- [ ] realize one non-RH generalized-prime test family
- [ ] no Lean until the open core closes on paper

## Log

- 2026-08-09 — determinant-first conjecture frozen from coframe-rank and scalar Fredholm evidence.
- 2026-08-09 — hostile audit falsified determinant-first ontology: finite positive determinant
  orientations coexist with cofinal slope collapse. Pivoted to pro-valuated source-Grushin event
  geometry; determinant retained only as fourth/fifth-layer shadow.
