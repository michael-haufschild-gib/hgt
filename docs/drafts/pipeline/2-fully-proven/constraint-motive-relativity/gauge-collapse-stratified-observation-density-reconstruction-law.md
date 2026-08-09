# Gauge collapse and stratified observation-density reconstruction law

- **ID:** `cmr-gauge-collapse-stratified-observation-density-reconstruction`
- **Stage:** 2 — fully proven on paper
- **Type:** THEOREM (paper)
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [GLOBAL ANTI-THEATRE LAW]`
  `[STRATIFIED OBSERVATION NERVE] [NOT RH]`
  `[NO LEAN WRITTEN OR BUILT]`
- **Parent field:**
  `../../1-in-progress/constraint-motive-relativity/polarized-constraint-duality-geometry.md`.
- **Statement:** A theory in which every doctrine transition is a gauge necessarily makes every
  transition an equivalence. Any genuinely information-losing route map therefore rules out a
  single-carrier gauge unification. A canonical directed replacement is a stratified category with
  source probes; those probes reconstruct global objects precisely when their restricted Yoneda
  observation nerve is fully faithful.

## 1. Setup

Let `D` be a category of observer doctrines and let

\[
 \mathcal F:D\longrightarrow\mathbf{Cat}
\tag{GOD.1}
\]

be a pseudofunctor. Its fibre `F_d` is the category native to doctrine `d`; for an arrow
`u:d->e`, the functor `F(u):F_d->F_e` is the declared doctrine change.

A **single-carrier gauge unification** consists of a category `C`, equivalences

\[
 \phi_d:\mathcal C\simeq\mathcal F_d,
\tag{GOD.2}
\]

and invertible pseudonaturality cells

\[
 \eta_u:\mathcal F(u)\phi_d\xRightarrow{\sim}\phi_e
\tag{GOD.3}
\]

for every doctrine arrow.

## 2. Gauge-collapse theorem

### Theorem 2.1

If `(GOD.2)--(GOD.3)` exist, every doctrine transition `F(u)` is an equivalence. Consequently:

1. a transition that is not an equivalence rules out single-carrier gauge unification;
2. a transition that identifies two nonisomorphic objects cannot be a gauge;
3. a transition that sends a noninvertible morphism to an isomorphism cannot be a gauge.

### Proof

Choose a quasi-inverse `psi_d:F_d->C` for every `phi_d`. Equation `(GOD.3)` gives

\[
 \mathcal F(u)\simeq\phi_e\psi_d.
\tag{GOD.4}
\]

The right side is a composite of equivalences, hence an equivalence. Equivalences preserve and
reflect object isomorphism and morphism invertibility, proving all consequences.

### Corollary 2.2 — localization erases the lost datum

Let

\[
 \pi:\int_D\mathcal F\longrightarrow D
\tag{GOD.5}
\]

be the Grothendieck construction and let

\[
 c_{u,X}:(d,X)\longrightarrow(e,\mathcal F(u)X)
\tag{GOD.6}
\]

be the cocartesian doctrine-change arrow. Suppose `F(u)X isomorphic F(u)Y` while
`X` and `Y` are not isomorphic in `F_d`. In every localization of `integral_D F` that inverts all
`c_(u,Z)`, the images of `(d,X)` and `(d,Y)` become isomorphic.

Indeed,

\[
 (d,X)\xrightarrow{\sim}(e,\mathcal F(u)X)
 \xrightarrow{\sim}(e,\mathcal F(u)Y)
 \xleftarrow{\sim}(d,Y).
\tag{GOD.7}
\]

Thus forcing this lossy doctrine change to be gauge does not repair it. It necessarily erases at
least the exhibited distinction between `X` and `Y`; the localization may erase more.

## 3. Stratified observation nerve

A canonical directed replacement for the chosen pseudofunctor retains doctrine changes. Put

\[
 \mathcal E=\int_D\mathcal F.
\tag{GOD.8}
\]

Let `P_src` be a small category of declared source probes and let

\[
 J:\mathcal P_{\rm src}\longrightarrow\mathcal E
\tag{GOD.9}
\]

be their realization. Define the observation nerve

\[
 N_J:\mathcal E\longrightarrow
 \operatorname{PSh}(\mathcal P_{\rm src}),
 \qquad
 N_J(X)(p)=\operatorname{Hom}_{\mathcal E}(Jp,X).
\tag{GOD.10}
\]

This keeps fibre type and doctrine-change history to the extent encoded in `D`, the coherence
cells of `F`, and the total category. If the doctrine category has already identified two path
composites, the Grothendieck construction does not restore their lost history. It does not assert
that different fibres are equivalent.

## 4. Density reconstruction theorem

Assume `E` is locally small and has the colimits below. For `X in E`, let `El(N_JX)` be the
category of elements: objects are pairs `(p,f:Jp->X)`, and arrows are probe morphisms compatible
with `f`. There is a canonical cocone and comparison

\[
 \kappa_X:
 \operatorname*{colim}_{(p,f)\in\operatorname{El}(N_JX)}Jp
 \longrightarrow X.
\tag{GOD.11}
\]

### Theorem 4.1 — exact source-observer reconstruction

The following are equivalent:

1. the observation nerve `N_J` is fully faithful;
2. every comparison `kappa_X` in `(GOD.11)` is an isomorphism;
3. every object has the density presentation

   \[
   X\cong
   \int^{p\in\mathcal P_{\rm src}}
   \operatorname{Hom}_{\mathcal E}(Jp,X)\cdot Jp,
   \tag{GOD.12}
   \]

   whenever the displayed copowers/coend are used to express the same colimit.

Under these conditions `J` is dense. Hence two objects with naturally isomorphic total probe
nerves are isomorphic.

### Proof

For any `Y in E`, the universal property of the category-of-elements colimit gives

\[
 \operatorname{Hom}_{\mathcal E}
 \left(\operatorname*{colim}_{(p,f)\in\operatorname{El}(N_JX)}Jp,Y\right)
 \cong
 \operatorname{Nat}(N_JX,N_JY).
\tag{GOD.13}
\]

If `N_J` is fully faithful, the right side is naturally
`Hom_E(X,Y)`. Yoneda then makes `kappa_X` an isomorphism. Conversely, if every `kappa_X` is an
isomorphism, `(GOD.13)` becomes

\[
 \operatorname{Nat}(N_JX,N_JY)\cong\operatorname{Hom}_{\mathcal E}(X,Y),
\]

naturally in `X,Y`, so `N_J` is fully faithful. The category-of-elements colimit and coend in
`(GOD.12)` are the standard two presentations of the same weighted colimit, proving the third
equivalence.

### Theorem 4.2 — dense-source non-descent

Assume the equivalent conditions of Theorem 4.1. Let `A` be a category and let

\[
 L:\mathcal E\longrightarrow\mathcal A
\tag{GOD.13a}
\]

be a doctrine realization. If there are a functor
`B:A->PSh(P_src)` and a natural isomorphism

\[
 N_J\cong B\circ L,
\tag{GOD.13b}
\]

then `L` is faithful, reflects isomorphisms, and reflects object isomorphism:

\[
 LX\cong LY\quad\Longrightarrow\quad X\cong Y.
\tag{GOD.13c}
\]

Consequently, if `L` identifies two distinct parallel morphisms, sends a nonisomorphism to an isomorphism,
or sends nonisomorphic objects to isomorphic objects, the complete dense source nerve cannot
descend through `L`.

For serial realizations

\[
 \mathcal E\xrightarrow{L}\mathcal A\xrightarrow{M}\mathcal G,
\tag{GOD.13d}
\]

descent of `N_J` through `ML` implies descent through `L`. A later observer therefore cannot
repair complete source-nerve information already lost by an earlier exit. For a small parallel
family `(L_i)` for which the product codomain is formed, descent through the product functor can
occur only if the combined functor is faithful, reflects isomorphisms, and reflects object
isomorphism; different legs may jointly repair losses that each leg has separately.

### Proof

If `Lf=Lg`, then `(B L)f=(B L)g`. Via `(GOD.13b)`, `N_Jf=N_Jg`, and faithfulness of the fully
faithful `N_J` gives `f=g`. Thus `L` is faithful.

If `Lf` is invertible, then `B(Lf)` and hence `N_Jf` are invertible. A fully faithful functor
reflects invertibility: fullness lifts the inverse of `N_Jf`, and faithfulness proves the two
inverse equations. Therefore `f` is invertible.

If `LX` and `LY` are isomorphic, applying `B` and `(GOD.13b)` gives `N_JX\cong N_JY`. Fullness
lifts this natural isomorphism and its inverse to arrows `X->Y` and `Y->X`; faithfulness proves
their composites are identities. Hence `X\cong Y`.

If `N_J\cong CML`, then `N_J\cong(CM)L`, proving the serial statement. Applying the first part to
the product functor proves the parallel statement. QED.

## 5. Exact higher interpretation

Theorem 2.1 proves that a lossy doctrine transition itself cannot be a gauge and that complete
route fibres cannot all be simultaneous gauges of one constant conservative carrier. Conservative
subcategories or genuine overlaps may still be related by equivalences. The directed structure is:

- **gauge:** invertible comparison inside the maximal equivalence subgroupoid;
- **directed exit:** noninvertible completion, scalarization, endpoint projection, positivity,
  realification, or forgetting;
- **curvature candidate:** a noninvertible Beck--Chevalley mate between two constructed path
  composites;
- **admission failure:** a required path, composite, or mate does not exist;
- **global reconstruction:** joint density of literal source probes, not equivalence of fibres.

These distinctions are categorical invariants. They cannot be removed by changing notation.

## 6. Corpus calibration and scope

Existing exact countermodels already provide doctrine changes that identify distinct data:

| Native datum | Lossy doctrine change |
|---|---|
| Mass affine successor | restriction to current Hankel face |
| integral recurrence lattice | realification to unmarked real kernel |
| differential prolongation rank | forgetting to ordinary killed-law kernel |
| algebraic reporter | Hausdorff continuous realization |
| relation multivalued fibre | quotient `Y->Y/mul R`, yielding the induced single-valued graph |
| marked history/path cost | endpoint or return projection |
| orientation/root | norm, square, or positive scalarization |

Each row rules out treating that transition as a gauge. The table does not yet construct one
common `E` containing the literal source objects and morphisms for every row.

Theorem 4.2 adds a conditional but route-independent prediction. Once any row is realized as a
literal functor in one source category, its displayed object or morphism collapse proves that the
complete dense source nerve does not descend through that exit. This spans affine, integral,
differential, topological, relational, history, and positive losses without identifying their
native defect types or replacing them by one scalar curvature.

## 7. Bold field conjecture: source observer density

Construct before Xi-zero specialization a literal category `E_HGT` and a source-generated probe
category `P_src` containing arithmetic, spectral, affine-successor, character, jet, ordered,
completion, and history probes. The conjecture is:

\[
 J:\mathcal P_{\rm src}\to\mathcal E_{\rm HGT}
 \quad\text{is dense, while no individual route subcategory is dense.}
\tag{GOD.14}
\]

This is falsifiable. A pair of nonisomorphic literal source systems with naturally isomorphic
total probe nerves kills it. Taking `P_src=E_HGT`, using all representables, or adding a custom
probe that names each target object is forbidden: those choices make density tautological.

## 8. Conjecture/proof/failure loops

### Loop A — every route is a gauge

**Failed by Theorem 2.1.** Non-equivalent doctrine transitions cannot be conjugate to identities.

**Survivor.** Gauges form only maximal equivalence subgroupoids inside the stratification.

### Loop B — Grothendieck construction alone is the field

**Failed as theatre.** Every diagram has one; it merely repackages the route list.

**Survivor.** Specify literal pre-target probes and prove their joint density.

### Loop C — full Yoneda solves reconstruction

**Failed as theatre.** Taking every object as a probe makes density automatic.

**Survivor.** Probe generation must be source-native, boundedly described, and independent of the
target theorem.

### Loop D — every no-go is curvature

**Failed.** A dense radical, absent domain, missing comparison, affine ambiguity, or history loss
need not be the mate of a square.

**Survivor.** Only a constructed comparison mate qualifies as curvature; the other failures remain
distinct directed strata or admission defects.

### Loop E — density proves RH

**Failed.** Density would reconstruct a global source object from probes. It does not by itself
impose the missing source equation or locate Xi zeros.

## 9. Predictions and falsifiers

1. Any proposed all-gauge model of the seven lossy rows in Section 6 is false.
2. Localizing all doctrine-change arrows necessarily identifies at least one pair distinguished by
   native affine, integral, differential, topological, orientation, or history data.
3. If a proposed finite source-probe family is dense, every natural endomorphism of its observation
   nerve comes from a unique endomorphism of the global object.
4. A candidate global geometry with two nonisomorphic objects sharing the complete declared probe
   nerve has failed its reconstruction gate.
5. Path dependence is curvature only after both path composites and their typed comparison mate
   exist.
6. Once a literal source nerve is proved dense, no serial observer applied after a lossy exit can
   restore the complete source geometry; only a jointly conservative parallel family can avoid
   the non-descent obstruction.

## 10. No-go closure

- **Failed conjecture:** one conservative carrier makes every proof route a local gauge.
- **Exact killing mechanism:** conjugacy to one carrier forces every transition to be an
  equivalence. For every object-identifying transition in Corollary 2.2, localization erases the
  exhibited object distinction; a morphism-inverting transition analogously erases its exhibited
  invertibility distinction.
- **Strongest positive survivor:** directed stratification plus dense source-observation nerve gives
  an exact reconstruction criterion, and Theorem 4.2 proves complete source information cannot
  descend through or be repaired after a lossy exit.
- **Open gate:** construct literal `E_HGT` and bounded source-probe generators, then prove or
  falsify `(GOD.14)`.
- **Status:** dependency-closed categorical theorem; no Lean written or built; no RH claim.

## Log

- 2026-08-09 — proved gauge-collapse and localization-erasure laws.
- 2026-08-09 — proved density reconstruction equivalence.
- 2026-08-09 — proved dense-source non-descent, serial irreversibility, and parallel joint-repair
  criteria.
- 2026-08-09 — replaced impossible all-route gauge slogan by directed stratified observation
  geometry.
