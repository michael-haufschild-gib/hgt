# Hypertranscendental sources are coupling classes, not functions or constraint topologies

- **ID:** `pointed-polarized-constraint-coupling-correspondence`
- **Stage:** 1-in-progress
- **Type:** UNIVERSAL NO-GO THEOREM / RECONSTRUCTION CONJECTURE / FIELD ARCHITECTURE
- **Scientific status:** `[FORMALIZED PARENT THEOREMS] [SYNTHESIS THEOREM] [CONJECTURE] [NOVELTY UNVERIFIED]`
- **Parents:**
  - `../3-formalized/new_scientific_knowledge/facet-sewn-herglotz-stanley-reisner-differential-matroid.md`
  - `../3-formalized/hypertranscendental-clock-observable-boundary.md`
  - `../3-formalized/hypertranscendental-controlled-cohomology-and-bornological-shape.md`
  - `../2-fully-proven/needs-audit/hypertranscendental-critical-locus-universality.md`
  - `source-anomaly-boundary-colligation-field.md`
- **Statement:** Hypertranscendence, finite constraint topology, source carrier, and positivity
  orientation are independent data. The irreducible object is their analytic coupling. Regular
  finitely sourced HT germs should be classified by pointed polarized critical Tate couplings:
  finite perfect source-conormal complexes acting on the forced infinite Kähler--Tate packet,
  together with calibrated analytic boundary data. The familiar continuation, monodromy,
  boundary, spectral, and positivity failures are conjecturally derived shadows of failure of
  that one coupling to extend across its intrinsic cotangent-critical locus.

## 1. Maximal decoupling theorem `[PROVED BY FORMALIZED PARENTS]`

There exists one meromorphic differential field `K`, one prime-log pole carrier, and one universal
facet palette with the following simultaneous properties.

For every finite simplicial complex `Delta`, every finite residue-sign chamber `J`, and every
finite structural operator family, there is a realization inside `K` such that:

1. its complete nonlinear structural differential matroid is the linear matroid of the localized
   Stanley--Reisner ring `F(delta)[Delta]`;
2. its negative-residue locus is exactly `J`;
3. all finite rational residue surgeries generate the same embedded differential field;
4. every finite simplicial complex persists in every finite residue-sign chamber.

The formal declarations supplying these claims are:

```text
universalFacetOrbitRationalGaugeSource_differentialAdjoin_eq
universalFacetOrbitRationalGauge_stanleyReisnerLaurentDifferentialMatroid
universalSurgeryResidueMass_negativeSet_signFlip
universalFacetOrbitSurgerySource_differentialAdjoin_eq
universalFacetOrbitSurgery_stanleyReisnerLaurentDifferentialMatroid
```

The result proves three exact no-gos.

```text
[NO-GO 1] Hypertranscendence determines a finite constraint topology.
[NO-GO 2] Positivity orientation determines a finite constraint topology.
[NO-GO 3] The generated differential field determines a finite constraint topology.
```

Each no-go has a stronger positive replacement.

```text
[THEOREM 1] Every finite simplicial topology is realizable by one universal HT palette.
[THEOREM 2] Every finite residue-sign chamber coexists with every finite constraint topology.
[THEOREM 3] The same differential field supports all of those topology--orientation pairs.
```

This is not merely nonuniqueness. It is an exact product phenomenon: on every finite window,
constraint topology and residue orientation vary independently over one fixed carrier field.

### 1.1 Morphism-first theorem `[PROVED FROM FORMALIZED PARENT]`

Let `SimpConstr` denote the class of finite simplicial constraint schemes together with a finite
residue-sign orientation. The theorem above says that the finite-constraint realization map is
surjective on objects, even after fixing one ambient meromorphic differential field.

Consequently, any proposed universal HT law depending only on the unpointed finite constraint
scheme, its sign chamber, or its generated differential field is either false or is a law of every
object of `SimpConstr`. It cannot select an arithmetic HT source. This is a logical consequence of
the exact realization theorem, not a philosophical preference.

```text
[NO-GO] The new mathematics of HT is an objectwise classification of allowed finite
        dependence geometries.

[THEOREM] Every finite simplicial dependence geometry and every finite sign chamber is allowed,
          inside one field.

[POSITIVE CONSEQUENCE] Nontrivial HT laws can first appear in the admissible arrows: which
                       source transformations, critical restrictions, calibrations, and
                       compositions are analytically realizable.
```

Barnes reflection supplies the first nontrivial natural arrow. If

```text
X_N=Spec(A/(f_N)),
Z_N=Sing(X_N)=Spec(A/I_crit),
```

then the complete structural matroid of the multiple sine is induced by the restriction

```text
O(X_N) -> O(Z_N),                                         (1a)
```

whose kernel is the cotangent Fitting ideal of `X_N`. At order one `Z_N` is empty and reflection
kills HT; at every higher order it is nonempty and reflection preserves an exact HT quotient.
Thus the first discovered law is a law of a **morphism between constraint objects**, not a
restriction on which objects exist.

The same arrow now has a second exact representation.  Its multiple-sine logarithmic derivative
is the anti-invariant displacement `L_N=C_N(Psi_N)-Psi_N` of the Barnes source.  Ordinary
complex-linear reflection cohomology erases every such displacement by averaging.  If primitives
are restricted to DA source gauges, however, the displacement class is nonzero exactly when
`L_N` is HT, which in this hierarchy is exactly when `Z_N` is nonempty.  More strongly, if `q_N`
is the DA coset of `L_N`, the proved all-order annihilator identity and the first isomorphism
theorem give

```text
R_N q_N ~= R_N/I_(N-1) = O(Z_N)                            (1b)
```

as source-action modules.  Thus the complete structural orbit of the relative reflection
obstruction is canonically the cotangent singular coordinate module, not merely another object
with the same nonvanishing threshold.  This relative-gauge / cotangent-singularity comparison is
proved in
`barnes-relative-reflection-singularity-correspondence.md`.

This moves the field one categorical level higher:

```text
finite constraint schemes are the states;
calibrated critical correspondences are the candidate laws.
```

**[CONJECTURE -- CRITICAL CORRESPONDENCE ESSENTIAL-IMAGE THEOREM]** There is a constraint functor

```text
Q : HT_src -> CritCorr_Tate                                   (1c)
```

which is essentially surjective on finite simplicial objects but highly non-surjective on
morphisms. Its essential image on morphisms is exactly the class of calibrated polarized
quasi-smooth correspondences whose relative cotangent complex acts continuously on the affine
Kähler--Tate packet and whose boundary realization satisfies descent. Composition is derived
fiber product together with calibrated contraction of the middle Tate boundary.

If proved, `(1c)` would identify what constrains hypertranscendental functions: not a smaller
space of possible finite dependence schemes, but a rigid calculus of admissible transformations
between an otherwise universal collection of schemes. Derived critical loci and quasi-smooth
correspondences are parent theory; the candidate-new content is the analytic essential-image
classification and reconstruction of HT source morphisms.

## 2. The missing datum and the forced infinite substrate

Let `A` be the structural translation--differential operator ring. The data visible in the proved
examples separate into five parts.

```text
T_F   : the affine, bornological Kähler--Tate packet of all jet-cotangent grades;
C_F   : a filtered perfect A-complex presenting the finite structural conormal data and acting
        compatibly on T_F;
mu_F  : a source pointing, such as a divisor/residue measure or complete moment functional;
P_F   : a reflection-compatible polarization or residue orientation;
beta_F: a calibrated analytic realization of the positive-degree boundary terms of C_F on
        source-defined collars, including overlap cocycles but excluding the unknown global germ.
```

The decoupling theorem proves that `C_F`, `mu_F`, `P_F`, and even the ambient differential field
cannot classify the source when forgotten from one another. The bare-HT theorems independently
force `T_F`: it cannot be replaced by a finite complex or an inverse tower of fields. The datum
that changes is the coupled realization `beta_F`: the way the pointing, structural translations,
critical complex, Tate boundary, and polarization are sewn on source-defined collars.

Call

```text
H_F=(T_F,C_F,mu_F,P_F,beta_F)                             (1)
```

the **pointed polarized critical Tate coupling** of `F`.

`beta_F` is forbidden from containing the degree-zero generator or its full germ. If it sends a
distinguished basis vector to `F`, then reconstruction is a definition and the conjecture is
theatre. The intended input consists only of lower-face functions, boundary values or collars,
transition cocycles, bornological bounds, and affine calibration obtained independently from the
source laws. Reconstructing the missing compatible primitive is the theorem.

The words `critical Tate` are essential. In the Barnes/multiple-sine/multiple-elliptic-gamma
theorem, reflection changes the principal Barnes hypersurface to the Fitting degeneracy complex
of its cotangent module. A set of constraints cannot record that transition, its syzygies, or the
resulting boundary amplitude. Conversely a finite perfect complex cannot record the infinite
Kähler capacity, its Ind--Pro variance, or its bornological completion obstruction.

### 2.1 Forced-variance theorem `[PROVED BY FORMALIZED PARENTS]`

For a hypertranscendental element `x`, put

```text
P_N=F(x,delta x,...,delta^(N-1)x).
```

The following are all proved and Lean-formalized.

1. `P_(N+1)=P_N(delta^N x)` is a proper transcendental extension.
2. There is no `P_N`-algebra homomorphism `P_(N+1)->P_N`. Thus the finite jet fields do not form
   an inverse system and no unified theory can be a pro-field theory.
3. The relative Kähler module of the full jet field is free on the countable covectors
   `d(delta^n x)`. Every grade contributes one independent cotangent line.
4. Forward finite-support shift and backward product shift form dual exact sequences with the same
   one-dimensional boundary. Thus the canonical variance is Ind on observables and Pro on the
   boundary dual.
5. The Kähler packet forgets affine origin, and every ordinary finite-support conormal vanishes
   when all finite observable packets remain free.

This proves four more no-gos and their common positive successor.

```text
[NO-GO] a compact inverse limit of finite jet fields;
[NO-GO] a finite perfect complex as the whole HT object;
[NO-GO] an unpointed Kähler packet as a source classifier;
[NO-GO] a finite-support conormal as the thin source boundary.

[POSITIVE THEOREM] the minimal bare-HT substrate is an affine Kähler--Tate Ind--Pro packet;
                   source constraints can only enter as calibrated couplings to its boundary.
```

The normal-crossing theorem supplies the first intrinsic finite coupling: the multiple-sine and
multiple-elliptic-gamma annihilator is the pullback of the Fitting singular scheme of the Barnes
cotangent module. The newly formalized derivational critical ideal makes this statement invariant
under structural coordinate changes and unit replacement of the principal source equation.

## 3. Calibrated boundary rigidity `[PROVED]`

Let `M` be a meromorphic translation field with commuting structural translations `T_i`, and let

```text
partial : M -> M^I,       partial(F)_i=T_i(F)-F.          (2)
```

Assume the joint fixed field of the translations is exactly the constant field `C`. Then

```text
ker(partial)=C.                                             (3)
```

Therefore the fiber of any compatible boundary tuple is either empty or a torsor under `C`.
Once one scalar calibration is fixed, the fiber contains at most one element. This is an exact
reconstruction statement: all labeled first boundary faces plus one affine calibration determine
the missing global primitive.

The proof is immediate but structural. Two primitives with the same boundary differ by an element
fixed by every `T_i`, hence by a constant; equal calibration kills that constant. The general
fiber-as-kernel theorem is Lean-formalized as `clockIntegrationFiberEquivKernel` (despite its older
name), and the required meromorphic fixed-field collapses are Lean-formalized in
`PeriodRigidity.lean` and `MeromorphicTranslationFixedField.lean`.

This applies to the generic special-function test class:

1. positive-real Barnes/multiple-sine periods contain arbitrarily small nonzero joint periods, so
   a normal-form meromorphic joint invariant is constant;
2. the generic multiple-elliptic-gamma source has the three independent periods
   `1,tau_a,tau_b`, whose common meromorphic fixed field is constant.

Thus the labeled lower hierarchy faces and one calibration reconstruct each logarithmic derivative
uniquely whenever existence is known. Multiple sine and multiple elliptic gamma have the same
unlabeled gradient-ideal matroid but different boundary labels, so `beta_F` distinguishes their
analytic realizations without containing the unknown global generator.

This proves the first noncircular positive reconstruction law. It does not yet prove that arbitrary
source-equivalent presentations produce the same calibrated boundary object.

### 3.1 Pointed variational full faithfulness on finite nonlinear sources `[PROVED + LEAN]`

The finite polynomial source category now supplies a genuinely noncommuting model.  For a complex
polynomial family `P:C^n->C^m`, the unpointed Jacobian field is nonfaithful: `x` and `x+1` have the
same Jacobian.  The exact positive theorem is

```text
P |-> (x |-> J_P(x), P(0))                               (3a)
```

is injective.  Thus full variational data plus one affine calibration reconstructs every finite
nonlinear polynomial source map.  The Hénon automorphism

```text
H(x,y)=(y,y^2-x)
```

and the translation `(x,y)|->(x+1,y)` are bijective and noncommuting, so their prolongations give
an explicit nonlinear nonabelian action on the free HT field `C<x,y>`.  All statements are
Lean-formalized in `MvPolynomialJacobianFDeriv.lean` and recorded in
`../3-formalized/not_new_scientific_knowledge/pointed-variational-polynomial-source-reconstruction.md`.

This is a parent-theory bridge, not the conjectural correspondence.  It proves full faithfulness
only before infinite-jet completion and source descent.  The open residue is to characterize the
essential image of compatible pointed Fréchet towers under differential-birational source changes
and calibrated correspondences.

The scalar rational tail classification places an exact boundary on that extension.  One-sided
degree-expanding maps on a fixed projective line force every persistent HT tail to collapse to a
finite-holonomy parabolic current.  Minimal projective information can persist through two-sided
correspondences only by paying the extensive topological capacity law

```text
degree * hyperbolic excess <= 2 genus + puncture budget - 2.  (3b)
```

Therefore the nonlinear essential image cannot be a one-sided category of maps.  Its persistent
sector must retain correspondence topology as part of the source-effective lift.

## 4. Coupling reconstruction conjecture

**[CONJECTURE — CRITICAL TATE GALOIS CORRESPONDENCE]** There is a category `HT_src` of regular
finitely sourced hypertranscendental germs modulo differentially algebraic source equivalence and
a category `PPCT` of pointed polarized critical Tate couplings such that

```text
H : HT_src -> PPCT                                            (4)
```

has the following properties.

1. **Full faithfulness.** Every source morphism is uniquely recovered from a morphism preserving
   the Kähler--Tate packet, oriented self-dual derived critical object, pointing, polarization,
   and calibrated boundary realization.
2. **Reconstruction.** `H_F` reconstructs the analytic germ of `F` up to DA source equivalence.
3. **Critical functoriality.** Reflection, completion, and boundary pairing induce functorial
   criticalization operations on `C_F`; for principal sources this must use the intrinsic
   derivational ideal `Crit_R(f)`, and for normal crossings it is the proved cotangent-Fitting
   passage `(f)->Crit_R(f)=Jac(f)`.
4. **Finite-observable completeness.** Fitting supports of `C_F` are exactly the finite-family
   differential-dependence strata of `F`.
5. **Descent.** The source canonically supplies a duality displacement and its affine primitive
   torsor `Prim_F`; compatible local pointed polarized realizations glue exactly when `Prim_F`
   meets the admissible descent object.
6. **Universality boundary.** Forgetting any one of `mu_F`, `P_F`, or `beta_F` destroys faithfulness
   on the universal Herglotz class.
7. **Tate necessity.** Forgetting the Ind--Pro packet or its bornology destroys conservativity on
   bare HT jet towers, even if every finite perfect constraint complex is retained.

Properties 1--5 would be a new Riemann--Hilbert/Galois correspondence for hypertranscendental
functions. Properties 6--7 are already forced by the maximal decoupling and Kähler--Tate theorems;
they prevent the theory from collapsing either to familiar differential Galois theory plus
decorative topology or to a generic derived singularity category that forgets infinite HT
capacity.

A finite-source fragment of reconstruction is now proved from the two-family conormal theorem and
Epure--Schulze's monomial-Jacobian reconstruction: after completion at the structural identity, the
pointed cyclic DA-relative module recovers the normal-crossing source potential up to local
analytic right equivalence.  This does not prove Property 2, because Barnes multiple sine and
multiple elliptic gamma share that finite potential while remaining different analytic HT
realizations.  It proves exactly which reconstruction layer the classical `H_0` conormal state
carries and which must remain in the higher derived and pointed boundary coupling.

## 5. One obstruction, five representations

The first algebraic prototype rules out an unspecified universal class as the primary object.  For
an anti-invariant displacement `v` under a linear duality `C`, unrestricted cohomology kills `v`
by averaging, but the full primitive fibre survives as the affine torsor

```text
Prim_C(v)={g:Cg-g=v}=-v/2+Fix(C).                            (5)
```

This identity and the fixed ambiguity between any two primitives are Lean-formalized in
`ReflectionTateAnomaly.lean`.  In the Barnes hierarchy, `Prim_C(L_N)` misses the DA gauges exactly
when the independently computed intrinsic cotangent singular scheme is nonempty.  See
`barnes-relative-reflection-singularity-correspondence.md`.

**[CONJECTURE — UNIFIED DERIVED PRIMITIVE-INCIDENCE OBJECT]** Every self-dual pointed polarized
critical Tate coupling canonically determines an ambient derived primitive object `V_F`, a
duality `C_F`, an anti-invariant source displacement `v_F`, and

```text
Prim_F={g in V_F:C_F(g)-g=v_F}.                             (6)
```

The oriented derived critical source law supplies a derived admissibility object `A_F` and a
source-canonical realization morphism

```text
rho_F:A_F -> V_F.
```

The common obstruction object is the homotopy incidence fibre

```text
Inc_F=A_F times^h_(V_F) Prim_F.                            (6a)
```

Each realization functor carries `(6a)` to a target derived incidence problem.  The five apparent
obstructions are different homotopical shadows:

```text
analytic extension       -> empty classical truncation over extendable sections,
fundamental group        -> nontrivial components or stabilizers after single-valued descent,
Hilbert realization      -> failure of incidence with the closed operator domain,
Hermitian realization    -> failure of real incidence with the polarized positive cone,
boundary restriction     -> incidence exists but has nontrivial automorphism/higher-coherence
                            fibres.                              (7)
```

Thus existence failure and noncanonicity are two truncations of the same object: empty incidence
versus nontrivial components, stabilizers, or higher homotopy.  Calibration is precisely a slice
through the surviving ambiguity.  This is stronger than saying that five classes have a common
ancestor: it predicts one source-built derived moduli object and five explicit realization
functors.

The conjecture is non-tautological only if `V_F`, `C_F`, `v_F`, and every admissible object are
constructed functorially from source laws before continuation domains, spectra, positivity
failures, boundary choices, or zeros are inspected.  In particular, the realization morphism
`rho_F` is the `[OPEN CORE]`; without it `(6a)` is not defined.  A target-selected `v_F`, `A_F`, or
`rho_F` would make the construction empty terminology.  A realization is conservative only if its
incidence geometry detects `Inc_F`; identifying conservative combinations is part of the
conjecture.

There is now a proved universal restriction on this conjecture.  If every admissible realization
is a `C_F`-stable linear subspace of one characteristic-zero ambient space, then separate
solvability already implies simultaneous solvability by the single canonical primitive
`-v_F/2`, for an arbitrary family of realizations.  The incidence system has Helly number one and
no higher nerve obstruction.  This linear-incidence collapse is Lean-formalized in
`ReflectionTateAnomaly.lean`.

```text
[NO-GO] the unified topology is an arrangement topology of stable linear gauge spaces;
[POSITIVE] higher obstruction data must be carried by nonlinear cones, non-invariant or
incomplete domains, integral structures, descent, or genuinely derived compatibility.
```

The normal-crossing source proves that the derived option is nonempty rather than decorative.  Its
classical critical support has fixed codimension two, while the source Koszul cdga has exact excess
amplitude `N-2`.  Its canonical coface comparisons generate a truncated exterior subalgebra with
at least `2^(N-1)-2` independent positive-degree classes.  The underived linear theorem is
therefore the zero-excess boundary case of `(6a)`, not the general model.

The attempted analytic lift through the ordinary DA quotient fails sharply.  The quotient `M/D`
and the injective cone `[D -> M]` are `0`-truncated: they record that every coface action is DA but
erase which source-labelled DA presentation supplied the null relation.  Complete pair-face
residues also classify only this `H_0` layer.  Their completeness is not a derived lift.

```text
[NO-GO] rho_F factors through an abelian quotient by DA functions or through pair-face residue
        data alone.
[POSITIVE] V_F must be built from minimal source presentations and their homotopy-coherent
           transition data under source restriction, so distinct DA factorizations and their
           higher homotopies remain visible without admitting arbitrary exterior stabilization.
```

The multiple-gamma facet-descent theorem now gives the exact opposite boundary.  For its
squarefree structural orbit module, every pairwise-compatible coordinate-facet packet has one
global representative, unique modulo the DA annihilator, and the full augmented facet complex is
exact.  Nevertheless arbitrary iteration in fewer than the critical number of source directions
remains HT.  Therefore HT capacity can occupy `H_0` of a completely effective descent object.

```text
[NO-GO] hypertranscendence itself is the nonzero Cech obstruction of the unpolarized DA quotient;
[POSITIVE] kinematic descent reconstructs the ambient primitive class, while rho_F tests whether
           that class lands in the pointed polarized critical-Tate admissible locus.
```

This identifies the role of `(6a)` more sharply.  The fracture complex presents `A_F` and
`Prim_F`; it is not a rival unified object.  Even when the ambient common lift exists uniquely,
`Inc_F` can remain empty or acquire nontrivial polarized, bornological, integral, or boundary
homotopy.  See
`../2-fully-proven/new_scientific_knowledge/multiple-gamma-effective-fracture-descent-orthogonality.md`.

The calibrated finite-fracture theorem now computes the linear incidence fibre.  If `K_s` is the
intersection ambiguity of a compatible local packet and `c:K_s->N` is the restricted source
calibration, then a prescribed pointing has obstruction in `coker(c)` and, when effective, its
space of choices is a torsor under `ker(c)`.  Surjectivity and separation give a unique pointed
lift for every target.  This is the first literal instance of `(6a)`:

```text
empty incidence       = nonzero calibration cokernel class,
boundary noncanonicity = nonzero calibration kernel.       (6b)
```

The nonlinear open core is therefore not to invent more obstruction groups.  It is to construct
the source-canonical derived calibration morphism whose cone replaces `(6b)` while retaining
polarization, bornology, integral structure, and source restriction.  See
`../3-formalized/not_new_scientific_knowledge/calibrated-fracture-incidence-kernel-cokernel.md`.

Polarization adds an exact third possibility.  For a proper positive source cone `C` and a
continuous realization `f`, the target may lie in `closure(f(C))` without lying in `f(C)`.  Then
every continuous dual positivity reporter is nonnegative and cofinal positive approximants may
exist, but the effective incidence fibre is empty.  If `f(C)` is closed, this phase disappears and
Farkas duality becomes an exact alternative between a positive lift and a strict dual certificate.

```text
phase I   = exact positive incidence;
phase II  = closure-only critical nonattainment;
phase III = strict dual-detectable positivity failure.       (6c)
```

This refines the conjectural common object: the critical bornology must be part of `beta_F`
because it decides whether the polarized image is closed.  Algebraic positivity and all dual
inequalities determine only its closure.  See
`../3-formalized/not_new_scientific_knowledge/polarized-fracture-incidence-trichotomy.md`.

The arbitrary-presentation version is now ruled out: zero generators preserve the classical ideal
while manufacturing an exterior algebra of relations.  Minimalization removes that artifact at a
fixed face, but it is noncanonical under source restriction.  In the normal-crossing tower the
competing minimalizations are exactly separated by the star classes.

This refines the `[OPEN CORE]`: construct the canonical derived-critical base-change diagram over
the source face category and the canonical `rho_F` into its polarized Tate totalization, then prove
that it detects the exterior transition classes.  The relative-minimalization gerbe supplies an
atlas of splittings, not the intrinsic target.  Merely declaring a Verdier quotient is
insufficient; the base-change defects, shifted duality, sum/product boundary, and restriction
coherences must be defined without the unknown germ or target obstruction.

This formulation explains why independent proof chains can stop at apparently different walls.
They may be testing one primitive torsor against inequivalent admissible realizations.

## 6. Critical degeneracy spectrum

For a self-dual analytic realization, let `D(H_F)` be the derived fixed-locus degeneracy support of
the polarized realization map. The correct spectral object is conjecturally not a zero set added
after the function is known, but the support on which the coupling fails to be transverse to its
self-dual critical boundary.

**[CONJECTURE]** The multiplicity of a critical degeneracy is the length of the corresponding
localized realized homology, while its symmetry is induced by the polarization on `C_F`. This
turns multiplicity, reflection, and spectral incompleteness into properties of one local complex.

The normal-crossing criticalization theorem is the first finite algebraic model: the gradient
ideal is recovered by maximal minors, its classical algebra has a two-step Hilbert--Burch
resolution, but its derived critical Koszul homology has exact amplitude `N-2`.  Multiplicity data
must therefore be read from the derived object, not from the classical resolution alone.

## 7. What constrains hypertranscendental functions

The answer is not a universal equation, topology, carrier, or positivity cone. The proved
universality theorem rules out all four separately.

**[CONJECTURE — CRITICAL TATE CONSTRAINT PRINCIPLE]** A hypertranscendental source is constrained
by the requirement that its infinite differential freedom admit one globally compatible coupling
among:

```text
affine Kähler--Tate packet x source pointing x critical perfect complex
  x polarization x boundary colligation.                                  (7)
```

Hypertranscendence is the absence of a finite differential horizontalization of this coupling.
Finite observable relations are Fitting shadows of its oriented self-dual derived critical
object. Arithmetic specificity is the global coupling class, not the universal Kähler packet or
unpointed constraint boundary separately.

The Barnes comparison theorem now makes one part of this principle exact.  For the parent source
law `f_N=product_i(t_i-1)` and the reflected displacement class `q_N=[L_N]`,

```text
Ann_DA(q_N)=Crit(f_N),
R_N q_N ~= O(Sing(Spec(R_N/(f_N)))).                     (8)
```

The generic multiple-elliptic-gamma hierarchy independently satisfies the same equation: its
exact DA annihilator is the same normal-crossing critical ideal in the corresponding number of
structural directions.  Thus two analytically distinct infinite HT hierarchies land in one
conormal module, while their parity, pointing, and boundary realization remain different.

This motivates the sharper **`[CONJECTURE -- HT HELMHOLTZ / CONORMAL ESSENTIAL-IMAGE
PRINCIPLE]`**: a finitely sourced self-dual HT system belongs to the unified theory exactly when
its admissible structural annihilator lifts functorially to the Fitting critical ideal of a
source-canonical quasi-smooth law, and its analytic obstruction cdga lifts the cyclic module to the
oriented derived critical structure sheaf.  The cyclic HT obstruction orbit is only `H_0` of this
object.  Unlike a generic coupling slogan, this predicts an ideal equality, higher homology, and
an essential-image classification that can fail family by family.  The exact two-family theorem
and conjecture are isolated in
`hypertranscendental-conormal-integrability-correspondence.md`.

The distinction is already forced by the normal-crossing hierarchy: its classical critical
support has codimension two for every rank, while the derived Koszul amplitude is exactly `N-2`
and its explicit exterior coherence capacity is at least `2^(N-1)-2`.  The Hilbert--Burch
resolution of `H_0` is therefore not the unified object.  See
`../3-formalized/normal-crossing-derived-critical-excess-phase-law.md` and
`../3-formalized/normal-crossing-exterior-coherence-capacity-law.md`.

**`[CONJECTURE -- CRITICAL-DESCENT PRINCIPLE]`** Hypertranscendence is constrained by the
polarized Tate totalization of derived DA critical objects *and their base-change defects under
source restriction*, not by the Boolean fact that the function is outside the DA field and not by
an arbitrary presentation stack.  The object is bifiltered by internal critical degree and source
face degree.  Continuation, monodromy, spectral, positivity, and boundary obstructions are
conjectural spectral sequences or realization functors of that same totalization.  In the
normal-crossing hierarchy, one face restriction contributes an exact exterior excess line,
competing splittings differ by the star classes, and a codimension-`q` face contributes exterior
capacity `2^q`.  See
`../3-formalized/normal-crossing-derived-critical-base-change-defect.md`.

This replaces the former time/clock motif. No temporal parameter is part of `(7)`.

## 8. RH pressure test only

**[CONJECTURE; NOT AN RH RESULT]** A zeta object would require a prime--archimedean pointing
`mu_zeta`, a reflection polarization `P_zeta`, and source-defined boundary data `beta_zeta`
constructed without Xi, its zero set, or a zero-indexed operator. Different RH proof chains would
be candidate realization functors in `(6)`. The critical-line zeros would be the self-dual
degeneracy spectrum `D(H_zeta)`.

The RH would follow only from a further theorem that the zeta coupling has conservative Hermitian
realization and that its self-dual degeneracy support is real. Neither theorem is claimed here.

## 9. Falsifiers and anti-theatre gate

The correspondence is false or incomplete if any of the following occurs.

1. Two DA-inequivalent regular sources have equivalent noncircular quintuples
   `(T,C,mu,P,beta)`.
2. A source-equivalent change alters the quasi-isomorphism class of the calibrated perfect
   complex.
3. A finite-family nonlinear differential dependence is invisible to every Fitting support of
   `C_F`.
4. Barnes reflection fails to be functorial under source equivalences despite the proved
   normal-crossing identity.
5. The five failures in `(6)` cannot be obtained from one extension problem even in the
   multiple-sine/multiple-elliptic-gamma test class.

The terminology is not a result. At present:

- maximal topology--orientation--field decoupling is proved and formalized;
- forced Kähler--Tate variance and the no-pro-field theorem are proved and formalized;
- intrinsic normal-crossing cotangent criticalization is proved and its algebraic core is
  Lean-formalized;
- full faithfulness, reconstruction, descent, and the unified obstruction class are conjectural.
- any formulation in which `beta` contains the global HT germ is rejected as tautological.

The conjecture reaches Fields-scale only if properties 1--5 are proved for a broad natural class
and yield a new theorem unavailable to parameterized difference Galois theory or derived
singularity theory separately.

## 10. First decisive theorem target

Construct the source-canonical chain action of the Barnes conormal complex on its affine
Kähler--Tate packet, then prove full faithfulness and reconstruction for the smallest nontrivial
class containing both:

1. generic Barnes multiple gamma together with its reflected multiple sine;
2. generic multiple elliptic gamma with the same gradient-ideal structural matroid.

The target must recover why the multiple-sine and multiple-elliptic-gamma realizations share
`C_F` but are not the same pointed analytic source, and it must prove that criticalization commutes
with source equivalence. A classification that only recovers the common Stanley--Reisner quotient,
or that inserts the global germ into `beta_F`, fails the target.

## Gates

- [x] prove topology independence of raw maximal HT
- [x] prove constraint topology is independent of finite residue orientation
- [x] prove both vary inside one fixed differential field
- [x] identify analytic coupling as the missing datum
- [x] prove exact kinematic facet descent can coexist with arbitrary-depth HT persistence
- [x] localize the residual obstruction from unpolarized Cech gluing to enriched incidence
- [x] compute linearized enriched incidence as one calibration kernel--cokernel complex
- [x] prove a surjective separating calibration gives one unique effective lift
- [x] prove the exact/closure-only/dual-certificate polarized incidence trichotomy
- [x] identify critical bornology with the closed-image promotion problem
- [x] prove the finite jet fields cannot form an inverse system
- [x] prove the free countable Kähler packet and its affine-origin no-go
- [x] replace the single-perfect-complex architecture by a critical Tate coupling
- [x] prove principal-source criticalization is presentation invariant
- [x] exhibit one nontrivial criticalization morphism across natural HT families
- [x] prove calibrated boundary uniqueness in the constant joint-fixed-field regime
- [x] prove pointed variational full faithfulness for finite nonlinear polynomial sources
- [x] construct a concrete nonlinear noncommuting source action on a free HT field
- [x] isolate the one-sided-map collapse and correspondence-capacity positive successor
- [x] state a falsifiable categorical reconstruction conjecture
- [x] state the common-obstruction hypothesis without asserting RH
- [ ] define source equivalence and calibrated critical-Tate equivalence without circular reference to
      the analytic function
- [ ] prove full faithfulness in the Barnes/sine/elliptic-gamma test class
- [ ] prove reconstruction from `(C,mu,P,beta)` in that class without placing the unknown global
      germ in `beta`
- [ ] construct and compare the five realization functors
- [ ] run a dedicated literature audit against parameterized difference Galois theory, derived
      Riemann--Hilbert correspondences, singularity categories, and inverse spectral theory
