# Interfinity geometry

- **ID:** `interfinity-geometry`
- **Stage:** 1-in-progress
- **Type:** TERMINAL-EXACTNESS GEOMETRY / FILTERED SIMPLICIAL TOPOLOGY OF SOURCE TIME
- **Scientific status:** `[NEW CANDIDATE GEOMETRY] [CORE PAPER-PROVED]`
  `[EXTERNAL PRIORITY UNVERIFIED] [NOT RH] [NO LEAN AUTHORIZED]`
- **Source:** failure of ordinary weak, Hilbert, projective, product, cohomological, and
  distributional completions to distinguish algebraic trivializers from forward-stable endpoint
  formation, and pairwise comparison from one joint source experiment
- **Exact prime model:**
  `../../2-fully-proven/new_scientific_knowledge/other/prime-valuation-dyadic-fermion-normal-cone-law.md`
- **Demoted precursor:** `cofinal-prime-horizon-blowup-geometry.md`

## New primitive

Ordinary geometry starts with points and asks how nearby points compare.  Here points are too
early.  A source-time cocycle may be algebraically trivial in a distribution space yet have no
forward-stable primitive and hence no endpoint; several individually visible endpoints may have
pairwise comparison charts which do not fill one source-synchronous simplex.

Reverse the order:

> An **interfinity** is the observer-indexed record of when source-time cocycles become stably
> exact, which finite families admit one synchronized representation, where non-dying classes
> concentrate, and what cyclic phase survives.  Endpoints are deaths of obstruction classes, not
> primitive points.

Topology must change with observer strength.  A boundary object may be one point for bounded
observers, split into two points for distributional observers, and split further for Stokes or
resurgent observers.  No single topology is declared fundamental.

The completed representation object is `(I.134)`: a Scott space of stable-solvability profiles,
all-degree stable-primitive persistence, a Gram-labelled simplicial set, a projective fixed-residue
face, and the cyclic phase derived on its nondegenerate two-simplices.  Source-generated Kolmogorov
quotients and normalization stalks are derived shadows.  Basic topology is exactness-cut topology:
the frontier where an affine-time equation first admits a forward-stable primitive.

## 1. Observer tower

An **observer tower** is data

\[
 \mathfrak O=(I,\tau,\{H_i\},\{\Omega_i\},
 \{\mathcal T^m,\jmath_i^m,\mathcal R^m\}_{m\in M},\mathbf 1)
\tag{I.1}
\]

with:

1. a directed cofinal scale set `I` with a source clock
   `tau:I->[1,infinity)` tending to infinity;
2. Hilbert spaces `H_i` and normalized source states `Omega_i(gamma_i)` for admissible parameter
   germs `gamma=(gamma_i)`;
3. a nested tower of source test spaces

   \[
   \mathcal T^0\supset\mathcal T^1\supset\mathcal T^2\supset\cdots,
   \qquad
   (\mathcal T^0)'\subset(\mathcal T^1)'\subset(\mathcal T^2)'\subset\cdots;
   \tag{I.2}
   \]

4. compatible realization maps `j_i^m:T^m->H_i` (or into a common algebraic antidual when no
   Hilbert realization exists);
5. nested, multiplicatively saturated classes `R^m` of positive source-clock renormalizers;
6. a distinguished source test `1` present at every grade and preserved by every realization.

Grade zero contains bounded finite-source observations and `R^0={1}`.  Later grades may impose
smoother tests and admit larger renormalizer classes, hence more singular dual boundary
functionals.  The index set `M` need not be the natural numbers; Rees, Gevrey, logarithmic, and
Stokes grades may form a partially ordered monoid.  Renormalizers are part of the observer, not
chosen after inspecting one endpoint.  This prevents fitted gauges from manufacturing a boundary
distinction.

An equivalence of observer towers must preserve the source pointing, be cofinal in `I`, induce
continuous mutually inverse maps on every test grade and every renormalizer class, and preserve
the source clock asymptotically: after pullback, `tau'/tau -> 1`.  Arbitrary time changes are not
equivalences; they change the normalization geometry.  Arbitrarily adjoining a label that names an
end is also not an equivalence: separation must be produced by source observations.

## 2. Normalization stalks

For a cofinal germ `gamma`, define its grade-`m` **normalization stalk**

\[
 \mathfrak N^m_\gamma
 =\left\{
 [r_i,T]:
 r\in\mathcal R^m,\quad
 r_i\langle\jmath_i^m(f),\Omega_i(\gamma_i)\rangle\longrightarrow T(f)
 \ \forall f\in\mathcal T^m,\quad
 T\in(\mathcal T^m)',\quad
 T\ne0,\quad T(\mathbf1)\ne0
 \right\}/\sim .
\tag{I.3}
\]

Here `r_i>0` belongs to the predeclared observer class, convergence is weak on `T^m`, and two pairs are equivalent when their renormalizers
have ratio tending to a finite positive constant and their limits differ by that constant.  The
condition `T(1)!=0` forbids fitted boundary functionals invisible to the source point.

Define:

\[
 \operatorname{grade}(\gamma)
 =\inf\{m:\mathfrak N^m_\gamma\ne\varnothing\},
\tag{I.4}
\]

and, when the first stalk is one-dimensional, its positive asymptotic class

\[
 \operatorname{normchar}(\gamma)=[r_i].
\tag{I.5}
\]

`grade` records what kind of observer can see the infinity.  `normchar` records how strongly that
observer must amplify it.  These are local topological data, not a metric placed on an existing
boundary.

## 3. Source-generated topology filtration

Put

\[
 \widehat{\mathbb C}_\bot
 =\widehat{\mathbb C}\sqcup\{\bot\},
\tag{I.6b}
\]

where `bottom` is an isolated symbol meaning that the net has no limit.  For `k<=m`,
`r in R^k`, and `f in T^k`, retain the extended limit in the Riemann sphere of

\[
 r_i\langle\jmath_i^k(f),\Omega_i(\gamma_i)\rangle,
\tag{I.6a}
\]

when it exists and retain `bottom` otherwise.  The cumulative grade-`m` signature
`Sigma_m(gamma)` is therefore a point of the product of copies of
`C-hat_bottom` indexed by all source-clock-labelled triples `(k,r,f)` with `k<=m`.
Declare `gamma~_m eta` exactly when their signatures agree.  Let

\[
 X_m=\{\text{cofinal germs}\}/\!\sim_m
\tag{I.6}
\]

with the subspace topology induced by the signature map into that product.  Because signatures
are cumulative, there are refinement maps

\[
 X_0\longleftarrow X_1\longleftarrow X_2\longleftarrow\cdots.
\tag{I.7}
\]

The **interfinity topology** is the structured pro-space

\[
 \mathbf X_{\mathfrak O}=\{X_m\}_{m\in M},
\tag{I.8}
\]

not its inverse limit and not any chosen stage.

For two germs define the **separation spectrum**

\[
 \operatorname{sep}(\gamma,\eta)
 =\inf\{m:\gamma,\eta\text{ have distinct images in }X_m\}.
\tag{I.9}
\]

This permits topology to have phase transitions: one observer sees one point, a stronger observer
sees two, and a still stronger observer may resolve a family of Stokes directions inside one of
them.  Ordinary topology has no invariant corresponding to `(I.9)` because its set of points is
fixed before observation.

The raw inverse system `{X_m}` is a pro-topological object and is not claimed as a new ingredient.
New geometry is the source-clock-labelled package

\[
 (\{X_m\},\{\mathfrak N_\gamma^m\},\operatorname{Trans}(\mathfrak O)),
\tag{I.9a}
\]

because the quotient tower alone forgets amplification rates and common-scale transition
simplices.  Section 14 below proves that this extra structure is not recoverable from the
pro-topology.

## 4. Transition simplices

Endpoint stalks do not determine the geometry between them.  Let
`gamma^a=(gamma_i^a)` be finitely many cofinal germs that use one common scale.  If, after diagonal
source-phase gauges, their Gram matrices converge,

\[
 \left[\langle\Omega_i(\gamma_i^a),\Omega_i(\gamma_i^b)\rangle\right]_{a,b}
 \longrightarrow [K(a,b)]_{a,b},
\tag{I.10}
\]

call the finite family a **transition simplex** and retain the projective positive matrix `K` as
its label.  Common-scale joint convergence is essential: unrelated pairwise subsequences do not
form a simplex.

Transition simplices form a source-labelled simplicial object `Trans(O)`.  A parameter domain `U`
is an **interfinity chart** when every finite subset of `U` is a transition simplex and the kernel
`K_U` is continuous and nondegenerate.  Its reproducing-kernel Hilbert space is the chart carrier.

An **interfinity** between endpoint germs `gamma_-` and `gamma_+` is an interfinity chart `U`
together with two escape filters in `U` whose images at every fixed observer scale tend toward the
two endpoint germs, even when the endpoints lie in disjoint limiting representations.

This definition makes an interior a representation object.  It is not inferred from a picture and
does not require either endpoint to be a point of the same completion.

## 5. Throats, horizons, and topology change

These words receive definitions only after `(I.1)`--`(I.10)`.

- A **throat** is the fixed locus inside an interfinity chart of a source involution exchanging its
  two escape filters.
- A **horizon at grade m** is a locus where the quotient map `X_(m+1)->X_m` ceases to be locally
  injective.  It is where a stronger observer splits a weaker observer's point.
- A **terminal horizon** is an endpoint with no source-pointed normalization stalk at any admitted
  finite grade.
- A **holographic stratum** is the new fibre created by one quotient refinement.  It stores exactly
  the distinctions erased at the preceding grade.

Thus a horizon is not where a metric coefficient vanishes.  It is where point identity itself is
observer-grade dependent.  A wormhole-like interior can exist as a transition chart even when no
finite-grade observer represents both ends as ordinary states.

## 6. First no-go theorem: bounded observers cannot separate weakly null ends

`[PAPER-PROVED ABSTRACT CORE]`

Let `psi_u` be normalized vectors in a Hilbert space and suppose

\[
 \psi_u\rightharpoonup0\quad(u\to-\infty),
 \qquad
 \psi_u\rightharpoonup0\quad(u\to+\infty).
\tag{I.11}
\]

Then every topology generated only by bounded matrix coefficients against fixed test vectors gives
the same limiting observation at both ends.  Its Kolmogorov quotient cannot contain two distinct
source-generated endpoint points.

### Proof

Every generating function has the form `u -> <v,psi_u>` or a finite continuous combination of
such functions.  By `(I.11)` every generator has the same two endpoint limits.  Hence the two end
filters define the same character on the generating observation algebra and are identified by its
Kolmogorov quotient. `QED`

This does not say that one cannot attach two labels by hand.  It says no bounded observation in the
given source representation generates their separation.  The distinction must enter through a
new normalization grade.

## 7. Exact prime interfinity

The prime-valuation normal-cone theorem supplies

\[
 \mathfrak h=L^2((0,1),dt/t),\qquad
 F_u(t)=e^{ut}-1,
\tag{I.12}
\]

and normalized exponential vectors

\[
 \psi_u=\operatorname{Exp}(F_u)\in\Gamma_s(\mathfrak h),
 \qquad
 \langle\psi_u,\psi_v\rangle
 =\exp\!\left(-\tfrac12\|F_u-F_v\|^2\right).
\tag{I.13}
\]

The source proof shows that `u=c log X` is forced by the prime cutoff, and that `(I.13)` is the
joint limit of actual finite-prime geometric states.  Both ends are weakly zero:

\[
 \psi_u\rightharpoonup0\qquad(|u|\to\infty).
\tag{I.14}
\]

Therefore grade-zero bounded observers identify the two ends by the no-go theorem.

Let

\[
 \Phi_1=\{f\in C^\infty[0,1]:f(0)=0\}
\subset\mathfrak h,
\tag{I.15}
\]

and use the exponential test algebra in `Gamma_s(Phi_1)` as grade one.  At the negative end,
writing `u=-V`, the parent theorem gives

\[
 e^{\|F_{-V}\|^2/2}\psi_{-V}=e(F_{-V})
 \longrightarrow e^{\ell_-},
 \qquad
 \ell_-(f)=-\int_0^1f(t){dt\over t}.
\tag{I.16}
\]

Moreover

\[
 e^{\|F_{-V}\|^2/2}
 \sim\sqrt{e^\gamma V/2}.
\tag{I.17}
\]

The source vacuum coefficient proves uniqueness of the normalization character: if
`r_V psi_(-V)` has a finite nonzero value on the vacuum, then

\[
 r_V e^{-\|F_{-V}\|^2/2}\longrightarrow c\in(0,\infty),
\tag{I.18}
\]

so `r_V` is equivalent to `(I.17)`.

At the positive end, no source-pointed grade-one scalar normalization exists.  Indeed a nonzero
finite vacuum value again forces `r_V` to be equivalent to `e^(||F_V||^2/2)`.  Pairing the resulting
unnormalized exponential vector with the fixed test `e(t)` gives

\[
 \exp\langle F_V,t\rangle\longrightarrow+\infty.
\tag{I.19}
\]

Hence there is no weak limit on the grade-one exponential test algebra.

Consequently the prime model has the exact observer spectrum

\[
 \operatorname{sep}(-\infty,+\infty)=1,
\tag{I.20}
\]

with

\[
 \operatorname{grade}(-\infty)=1,
 \quad
 \operatorname{normchar}(-\infty)=[\sqrt V],
 \quad
 \operatorname{grade}(+\infty)>1
\tag{I.21}
\]

relative to the displayed observer tower.  The positive grade is not guessed; it remains open
until an actual enhanced test category constructs it.

This is the first exact interfinity: a positive Fock transition interior connects two bounded-
observer-indistinguishable infinities whose minimal source normalizations have different grades.

## 8. Complex phase and reflection are secondary structure

Complexifying the critical scale produces the kernel and phase--radial metric on
`cofinal-prime-horizon-blowup-geometry.md`.  Reflection pairs `z` with `-conj(z)`, so the two-mouth
quantum metric adds while Berry curvature subtracts.  This yields a transversely folded Berry form,
a strict metric--Berry gap, and a reflection-fixed negative-curvature seam.

Those are geometric fields on one interfinity chart.  They are not the definition of interfinity
geometry.  The new topology is already forced by `(I.14)`--`(I.21)` before any metric, complex
structure, Berry connection, black-hole analogy, or divisor is chosen.

## 9. New invariants

For an observer tower and a transition chart, retain:

1. **separation spectrum** `sep(gamma,eta)` from `(I.9)`;
2. **normalization character** at every one-dimensional stalk;
3. **transition dimension**, the minimal real/complex dimension of a nondegenerate kernel chart
   joining chosen escape filters;
4. **simplex defect**, the first degree in which pairwise transition germs fail common-scale joint
   Gram convergence;
5. **phase rank**, the rank of the gauge-invariant curvature of the projective transition kernel;
6. **source-vanishing rank**, inherited from the HGT atlas after quotienting isogenous reporters;
7. **terminal grade**, finite or infinite, of every boundary face.

These data distinguish spaces that are homeomorphic after endpoint labels are attached but differ
in what their source observers can actually resolve.

## 10. Equivalence principle

The proposed analogue of Einstein's equivalence principle is:

> No observer-independent point set exists at a cofinal sector wall.  What is invariant is the
> transition simplicial object plus its normalization stalks.  Spacetime-like points, horizons,
> and interiors are representations of that invariant at a chosen observer grade.

This predicts a precise failure mode for every ordinary geometric RH proposal: if it starts by
putting all source, reflected, and completed states in one fixed Hausdorff space, it has already
chosen an observer grade and may have identified the two infinities before the arithmetic phase or
source normalization is read.

## 11. Fatal tests

Retire or radically revise the proposal if any of the following holds.

1. `(I.3)`--`(I.9)` reduce, with no loss, to a standard named pro-topology, approach space,
   convergence space, Fell topology, Martin boundary, or tangent groupoid carrying the same
   normalization-stalk invariant.
2. `sep` changes under cofinal reindexing or source-pointed equivalence of test towers.
3. The prime positive end admits a grade-one source-pointed distributional normalization, killing
   `(I.19)`.
4. The negative normalization character is not unique up to asymptotic positive scalar.
5. Transition simplices contain no information beyond an ordinary RKHS on a predeclared point set.
6. No example outside the prime model exhibits observer-grade point splitting.
7. The construction cannot define composition or restriction of interfinity charts.
8. The only usable claims are the already-known Fock kernel and rigged boundary asymmetry.

## 12. Immediate theorem program

1. `[DONE]` Prove source-clock covariance and bounded-observer collapse.
2. `[DONE]` Separate ordinary coboundaries from forward-stable primitives; prove the exact horizon
   sequence and endpoint criterion.
3. `[DONE]` Compute continuous exactness cuts, fixed-ray residues, and phase--cut locking in a
   non-arithmetic spectral family.
4. `[DONE]` Prove the coherent/Fock source functor and the Gram-labelled terminal nerve laws.
5. `[DONE]` Extend from one semigroup to a source-operation monoid and identify residual curvature
   as a terminal commutator limit.
6. `[DONE]` Instantiate the degree-two stable-boundary quotient on noncoherent arithmetic HGT
   source data and identify its prime--depth, Sonin, and BV--Wold charts.
7. `[DONE]` Represent exactness topology as the Scott pullback of stable-coboundary subspaces and
   identify its `T_0` solvability points.
8. `[DONE]` Complete internal hostile truth/priority/significance review; external specialist
   priority confirmation remains outside this paper-proof turn.

## Gates

- [x] primitive changed from points to transition experiments
- [x] topology changed from one point set to a source-generated refinement pro-space
- [x] new local objects: normalization stalk and transition simplex
- [x] new invariants: separation spectrum, normalization character, simplex defect
- [x] abstract bounded-observer no-go paper-proved
- [x] exact prime realization of asymmetric endpoint grades
- [x] no RH claim and no zero-selected definition
- [x] parent-theory collision search after freezing
- [x] invariance theorem
- [x] chart composition theorem and nontrivial simplex-defect example
- [x] second non-arithmetic realization
- [x] false ordinary-cohomology conjecture explicitly killed by finite-part counterexample
- [x] terminal-cohomology exact sequence and endpoint criterion
- [x] continuous exactness-cut topology and metric reconstruction
- [x] fixed-ray horizon residue and complex-time phase locking
- [x] abstract coherent/Fock source functor
- [x] Gram-labelled persistent simplicial set with genuine horn obstruction
- [x] terminal transgression theorem for noncentral source monoids
- [x] covariance theorem and observer-calibration caveat
- [x] all-degree stable-primitive exact sequence and exactness topology
- [x] Scott/Sierpinski representation and `T_0` solvability quotient
- [x] noncoherent arithmetic realization with three exact source charts
- [x] hostile significance review
- [ ] external specialist priority confirmation
- [x] no Lean written or built

## Log

- 2026-08-08 — frozen after the user rejected folded/Fock phase geometry as insufficiently new.
  The already-known real normal cone was used only as exact source data.  New primitive is the
  observer-grade splitting of infinity and the transition experiment that exists before either
  endpoint is representable in one completion.
- 2026-08-08 — hostile finite-part test falsified “distributional coboundary grade.”  Replaced it
  by forward-stable primitive and proved Theorems X--XII.
- 2026-08-08 — froze final candidate object `(I.134)`, then repaired its higher incidence from an
  invalid existence complex to a Gram-labelled simplicial set.  Proved coherent source functor,
  phase--cut locking, covariance, and terminal transgression through Theorem XVII.
- 2026-08-08 — hostile free-source test killed predictive universality.  Added source-relation
  rigidity, curved flux, polyhedral multi-time horizons, all-degree exactness topology, and the
  source-pure degree-two arithmetic quotient.  The latter identifies mixed Stokes density, Sonin
  torsion slope, and BV--Wold triangle holonomy as one stable-boundary coordinate.
- 2026-08-08 — final hostile pass represented observers as Scott points of solvable equations,
  proved the higher nerve is not reconstructible even from its full labelled one-skeleton, and
  demoted Bargmann phase from independent structure to a derived Gram observable.  Extracted six
  dependency-closed theorem cards into the matching pipeline-2 subfolder.

## 13. Source-clock invariance theorem

`[PAPER-PROVED]`

The word equivalence in Section 1 can be made exact.  A **source-clock cofinal morphism** from
`O` to `O'` consists of:

1. a cofinal map `a:I'->I` with `tau(a(j))/tau'(j)->1`;
2. an order isomorphism `theta:M->M'`;
3. compatible topological isomorphisms
   `U_m:T^m->T'^(theta(m))` carrying `1` to `1`;
4. bijections between asymptotic renormalizer classes, induced by pullback along `a`;
5. a correspondence of admissible germs for which, for every corresponding `gamma,gamma'`,
   every admitted `r,f`, and the corresponding `r'`, the chordal distance in the Riemann sphere
   between

   \[
   r_{a(j)}\langle\jmath_{a(j)}^m(f),\Omega_{a(j)}(\gamma_{a(j)})\rangle
   \quad\hbox{and}\quad
   r'_j\langle\jmath_j'^{\theta(m)}(U_mf),\Omega'_j(\gamma'_j)\rangle
   \tag{I.22}
   \]

   tends to zero;
6. the analogous condition for every finite source Gram matrix.

A **source-clock cofinal equivalence** is a pair of such morphisms whose composites agree
eventually on clocks, tests, renormalizer classes, germs, and finite Gram data.

### Theorem I (invariance)

Source-clock cofinal equivalence induces:

\[
 X_m\simeq X'_{\theta(m)},\qquad
 \mathfrak N^m_\gamma\simeq
 \mathfrak N'^{\theta(m)}_{\gamma'},\qquad
 \operatorname{Trans}(\mathfrak O)\simeq
 \operatorname{Trans}(\mathfrak O').
\tag{I.23}
\]

It preserves `grade`, transports `sep` through `theta`, and pulls every one-dimensional
normalization character to the corresponding character.  In particular a source-clock exponent
cannot be removed by a cofinal relabelling.

### Proof

Cofinality alone preserves a known limit but does not reflect convergence of an arbitrary subnet.
What reflects convergence here is the pair of morphisms whose composites are eventual tail
identities.  Together with `(I.22)`, that tail equivalence identifies every cumulative
observational signature, including existence or nonexistence of an extended limit.  It descends to
mutually inverse maps of the quotient sets.  The same coefficient
functions generate the two initial topologies, so these maps are homeomorphisms and commute with
refinement.

If `([r],T)` lies in `N^m_gamma`, equation `(I.22)` and continuity of `U_m` give

\[
 ([r'],T\circ U_m^{-1})\in
 \mathfrak N'^{\theta(m)}_{\gamma'}.
\tag{I.24}
\]

The inverse cofinal morphism proves bijectivity.  It also preserves nonzero source value because
`U_m(1)=1`, and preserves asymptotic renormalizer classes by item 4.  Thus first nonempty grade and
normalization character are invariant.  Equality of cumulative signatures proves invariance of
`sep`.  Finally item 6 carries common-scale convergent Gram matrices, restrictions, and phase
gauges in both directions, giving the simplicial isomorphism.  `QED`

The clock clause is necessary.  Without it the reindexing `tau |-> tau^q` changes every power-law
normalization exponent.  A geometry that quotients by arbitrary cofinal time change has deliberately
forgotten the datum this construction is designed to retain.

## 14. Continuum interfinities and pro-topological non-recoverability

`[PAPER-PROVED] [NON-ARITHMETIC REALIZATION]`

Fix `alpha>0` and let

\[
 \mathfrak h=L^2((0,1),dt/t),\qquad
 F_u^{(\alpha)}(t)=e^{u t^\alpha}-1,qquad
 \psi_u^{(\alpha)}=\operatorname{Exp}(F_u^{(\alpha)}).
\tag{I.25}
\]

This is a scale-invariant bosonic bath, defined without primes, zeta, divisors, or an RH carrier.
Take source clock `tau(V)=V`.  At grade one admit smooth one-particle tests vanishing at zero and
all regularly varying power renormalizers.

### Theorem II (continuum interfinity family)

For every `alpha>0`:

1. `psi_u^(alpha)` tends weakly to zero as `u->+/-infinity`;
2. bounded observers identify the two endpoint filters;
3. the negative endpoint has a unique source-pointed grade-one normalization character

   \[
   \operatorname{normchar}_\alpha(-\infty)
   =[V^{1/(2\alpha)}];
   \tag{I.26}
   \]

4. the positive endpoint has no source-pointed grade-one scalar normalization;
5. the transition chart has kernel

   \[
   K_\alpha(u,v)=
   \exp\!\left[-{1\over2\alpha}
   \int_0^1{(e^{us}-e^{vs})^2\over s}\,ds\right]
   =K_1(u,v)^{1/\alpha}.
   \tag{I.27}
   \]

Hence all `alpha` have the same two-stage endpoint quotient tower--one point at grade zero and two
points at grade one--but different normalization characters and different source-labelled
transition kernels.  Distinct `alpha` are inequivalent under source-clock cofinal equivalence.

### Proof

Substitution `s=Vt^alpha` gives

\[
 \|F_{-V}^{(\alpha)}\|^2
 ={1\over\alpha}\int_0^V{(1-e^{-s})^2\over s}\,ds.
\tag{I.28}
\]

Using

\[
 (1-e^{-s})^2=2(1-e^{-s})-(1-e^{-2s})
\tag{I.29}
\]

and the standard exponential-integral identity yields the exact asymptotic

\[
 \|F_{-V}^{(\alpha)}\|^2
 ={1\over\alpha}(\log V+\gamma-\log2)+o(1).
\tag{I.30}
\]

Both endpoint one-particle norms diverge.  For every fixed exponential vector `e(g)`,
Cauchy--Schwarz gives

\[
 |\langle e(g),\psi_u^{(\alpha)}\rangle|
 \le C_g\exp\!\left(-{1\over2}\|F_u^{(\alpha)}\|^2
       +\|g\|\|F_u^{(\alpha)}\|\right)\longrightarrow0.
\tag{I.31}
\]

Exponential vectors are dense and the states are normalized, proving weak convergence to zero at
both ends.  Theorem 6 identifies them at grade zero.

Multiplying the negative state by the reciprocal vacuum coefficient gives the unnormalized
exponential vector.  For every smooth `f` vanishing at zero, dominated convergence gives

\[
 \langle f,F_{-V}^{(\alpha)}\rangle
 \longrightarrow-\int_0^1 f(t){dt\over t}.
\tag{I.32}
\]

Thus the grade-one limit exists.  Equation `(I.30)` gives

\[
 e^{\|F_{-V}^{(\alpha)}\|^2/2}
 \sim (e^\gamma/2)^{1/(2\alpha)}V^{1/(2\alpha)}.
\tag{I.33}
\]

Any source-pointed limit has a finite nonzero vacuum value, so its renormalizer divided by
`(I.33)` tends to a finite positive constant.  This proves existence and uniqueness of `(I.26)`.

At the positive end the same vacuum argument forces the reciprocal-vacuum normalization.  Against
the fixed smooth grade-one test `f(t)=t`, however,

\[
 \langle f,F_V^{(\alpha)}\rangle
 =\int_0^1(e^{Vt^\alpha}-1)\,dt
 \ge {1\over2}(e^{V2^{-\alpha}}-1)
 \longrightarrow+\infty.
\tag{I.34}
\]

The corresponding exponential-vector coefficient diverges, so no scalar normalization has a
grade-one weak limit.  Finally `s=t^alpha` in the norm difference proves `(I.27)`.

The endpoint quotient claim follows from grade-zero collapse and the grade-one vacuum coefficient:
the gauge `V^(1/(2alpha))` has nonzero negative limit and zero positive limit.  If two distinct
parameters were source-clock equivalent, Theorem I would identify `(I.26)`, forcing
`1/(2alpha)=1/(2beta)`.  Therefore `alpha=beta`.  `QED`

### Corollary (ordinary pro-topology is incomplete)

The forgetful map

\[
 (\{X_m\},\{\mathfrak N^m\},\operatorname{Trans})
 \longmapsto \{X_m\}
\tag{I.35}
\]

is not injective on source-clock equivalence classes.  In fact one fixed two-stage endpoint
pro-space has a continuum of inequivalent lifts indexed by `alpha>0`.  Thus interfinity geometry
is not merely a new name for its filtered topology.  Its first genuinely extra modulus is the
**temporal codimension**

\[
 \delta={1\over2\alpha},
\tag{I.36}
\]

the source-clock exponent required to turn an invisible infinity into a nonzero boundary
functional.

## 15. Common-scale composition and a genuine simplex obstruction

`[PAPER-PROVED]`

Chart restriction is kernel restriction.  Two charts are **source-synchronous** when their kernels
agree on the overlap and every finite mixed subset has one common-scale Gram limit.  Their
composition is the union chart with that common kernel.

### Theorem III (partial composition)

Source-synchronous composition is unique and associative whenever all finite subsets of the total
union have common-scale limits.  Pairwise composability does not imply triple composability, even
when the proposed pairwise limits form a strictly positive Gram matrix.

### Proof

Uniqueness follows because a kernel is determined on every pair.  Positivity of every finite mixed
Gram limit makes the union a positive kernel; continuity is checked chartwise when the overlap is
closed under the chosen atlas gluing.  For three charts satisfying the total common-scale
condition, both parenthesizations restrict to the same pairwise kernel on the same union, so they
agree.

For failure of pairwise-to-triple gluing, take `I=N`, `H=C^3`, and an orthonormal basis
`e_1,e_2,e_3`.  Put

\[
 A_n=e_1,
\tag{I.37}
\]

and, on even `n`,

\[
 B_n={1\over2}e_1+{\sqrt3\over2}e_2,
 \qquad C_n=e_3,
\tag{I.38}
\]

while on odd `n`, put

\[
 B_n=e_3,
 \qquad C_n={1\over2}e_1+{\sqrt3\over2}e_2.
\tag{I.39}
\]

Along the even cofinal scale the `AB` overlap is `1/2`; along the odd cofinal scale the `AC`
overlap is `1/2`; and `BC` has overlap zero at every scale.  The proposed pairwise labels form

\[
 G=\begin{pmatrix}
 1&1/2&1/2\\
 1/2&1&0\\
 1/2&0&1
 \end{pmatrix},
 \qquad \det G={1\over2}>0.
\tag{I.40}
\]

So ordinary positive-kernel compatibility does not obstruct the triple.  But any subnet on which
`<A_n,B_n>->1/2` is eventually even, because this overlap takes only the values `0,1/2`.
Any subnet on which `<A_n,C_n>->1/2` is eventually odd.  No subnet can do both.  Hence no common-
scale transition 2-simplex realizes `G`.  `QED`

The obstruction is not a fitted associator.  It is absence of a joint experiment behind mutually
compatible pairwise shadows.  Define the **simplex defect** as the least dimension in which this
happens.  Example `(I.37)`--`(I.40)` has defect two.  A fixed-point RKHS sees only the positive
matrix `G` and therefore misses the obstruction completely.

## 16. Hostile status after first theorem cycle

The first conjecture--that a new metric/Berry fold supplied the missing geometry--failed by corpus
collision.  The second conjecture--that a filtered endpoint topology alone was new--also failed:
it is a pro-topological construction.  Positive survivor is narrower and harder:

> interfinity geometry is a source-clock enrichment of a filtered topology by normalization
> stalks and a non-complete common-scale transition simplicial object.

Theorems I--III establish three non-vacuous facts: invariance under the declared equivalence,
continuum many inequivalent geometries over one endpoint pro-space, and a higher gluing obstruction
invisible to pairwise positive kernels.  They do not establish priority, a canonical category for
all HGT routes, or relevance to RH.  Those remain hostile gates.

## 17. Phase-time holography: boundary normalization from interior collapse

`[PAPER-PROVED] [NEW BRIDGE, PRIORITY UNCHECKED]`

Complexify the continuum chart by

\[
 F_z^{(\alpha)}(t)=e^{z t^\alpha}-1,
 \qquad z=u+i\vartheta.
\tag{I.41}
\]

The pullback of the Fock quantum metric is Kähler and has coefficient

\[
 g_\alpha(u)\,dz\,d\bar z,
 \qquad
 g_\alpha(u)=\|\partial_zF_z^{(\alpha)}\|^2
 ={1\over\alpha}\int_0^1s e^{2us}\,ds.
\tag{I.42}
\]

Here `u` is radial source time and `vartheta` is its conjugate phase time.  Neither is called
physical spacetime.  They are the two directions of the transition experiment.

### Theorem IV (normalization--phase collapse law)

At the distributionally visible end `u=-V`, let `delta_alpha` be the temporal codimension from
`(I.36)`.  Then

\[
 \boxed{
 \delta_\alpha
 =2\lim_{V\to\infty}V^2g_\alpha(-V).
 }
\tag{I.43}
\]

Equivalently, the power needed to amplify the invisible boundary state is determined by the
second-order collapse coefficient of the interior radial/phase metric.  The endpoint stalk and
the transition chart are therefore not independent decorations in this family.

### Proof

Substitution `s=t^alpha` in the Fock metric gives `(I.42)`.  At `u=-V`, another substitution
`y=2Vs` gives

\[
 V^2g_\alpha(-V)
 ={1\over4\alpha}\int_0^{2V}y e^{-y}\,dy
 \longrightarrow {1\over4\alpha}.
\tag{I.44}
\]

Theorem II gives `delta_alpha=1/(2alpha)`.  Combining the two identities proves `(I.43)`. `QED`

This is the first exact holographic statement in the proposal: an invariant of how an endpoint
exists is readable from asymptotic geometry strictly inside the transition chart.  It is not yet a
general holographic principle.  A serious extension must characterize the class of charts for
which a boundary normalization character is reconstructible from an interior phase metric, and
must produce counterexamples when it is not.

The law also separates interfinity geometry from the earlier folded-Berry proposal.  Berry
curvature is optional and may vanish; `(I.43)` uses the phase direction through the positive
quantum metric and remains nontrivial.  What survives is not a wormhole picture but a quantitative
bulk--boundary recovery law for source-clock visibility.

## 18. Exact dyadic bulk--boundary reconstruction

`[PAPER-PROVED] [FROZEN BEFORE PARENT SEARCH]`

The preceding law is not special to `t^alpha`.  Let `mu` be a positive Borel measure on `(0,1]`
such that

\[
 \int_0^1s^2\,d\mu(s)<\infty,
\tag{I.45}
\]

and define a coherent Laplace interfinity by

\[
 F_{-V}(s)=e^{-Vs}-1\in L^2(\mu),
 \qquad \psi_{-V}=\operatorname{Exp}(F_{-V}).
\tag{I.46}
\]

Retain two observable functions:

\[
 B(V)=-\log|\langle0,\psi_{-V}\rangle|
 ={1\over2}\int_0^1(1-e^{-Vs})^2d\mu(s),
\tag{I.47}
\]

the boundary normalization action, and

\[
 g(V)=\|\partial_VF_{-V}\|^2
 =\int_0^1s^2e^{-2Vs}d\mu(s),
\tag{I.48}
\]

the radial/phase quantum-metric coefficient inside the chart.

### Theorem V (dyadic holographic reconstruction)

For every `V>=0`,

\[
 \boxed{B''(V)=2g(V)-g(V/2).}
\tag{I.49}
\]

Consequently each field determines the other:

\[
 \boxed{
 g(V)=\sum_{k=0}^{\infty}2^{-k-1}B''(V/2^k),
 }
\tag{I.50}
\]

and

\[
 \boxed{
 B(V)=\int_0^V(V-t)\,[2g(t)-g(t/2)]\,dt.
 }
\tag{I.51}
\]

Thus the full interior phase metric is a dyadic multiscale reconstruction from boundary
normalization acceleration.  Conversely the complete approach-to-boundary action is fixed by the
interior metric.  No endpoint label, curvature ansatz, or gravitational field equation enters.

### Proof

Condition `(I.45)` permits two differentiations under the integral in `(I.47)`.  Directly,

\[
 B''(V)
 =\int_0^1[-s^2e^{-Vs}+2s^2e^{-2Vs}]\,d\mu(s)
 =-g(V/2)+2g(V),
\tag{I.52}
\]

which proves `(I.49)`.  Rearranging and iterating gives

\[
 g(V)=\sum_{k=0}^{n-1}2^{-k-1}B''(V/2^k)
      +2^{-n}g(V/2^n).
\tag{I.53}
\]

The function `g` is bounded near zero by `(I.45)`, so the remainder tends to zero.  This proves
`(I.50)` and its convergence.  Finally `B(0)=B'(0)=0`; integrating `(I.49)` twice proves
`(I.51)`. `QED`

### Corollary (logarithmic spectral universality)

Suppose

\[
 d\mu(s)=c\,{ds\over s}+d\nu(s),
 \qquad c>0,
\tag{I.54}
\]

where `nu` is a finite signed measure and the total `mu` is positive.  Then

\[
 B(V)={c\over2}\log V+O(1),
 \qquad
 g(V)\sim{c\over4V^2},
\tag{I.55}
\]

and hence

\[
 \lim_{V\to\infty}{B(V)\over\log V}
 =2\lim_{V\to\infty}V^2g(V)={c\over2}.
\tag{I.56}
\]

For the absolutely continuous term, `(I.55)` is `(I.30)` and `(I.44)` with coefficient `c`.
Dominated convergence makes the finite-measure contribution to `B` bounded.  For the metric,
split the finite measure at `1/V` and then at a fixed small `epsilon`; boundedness of
`(Vs)^2e^{-2Vs}` and finiteness of `nu` show
`V^2 int s^2e^(-2Vs)dnu -> 0`.  This proves the corollary.

The corollary says finite spectral detail changes the boundary normalization constant but not its
temporal codimension.  The singular coefficient of `ds/s` is simultaneously:

1. twice the boundary amplification exponent;
2. four times the phase-metric cusp coefficient;
3. the scale-invariant density of transition modes.

This three-way equality is a candidate universal conservation law for logarithmic interfinities.
Theorem V is stronger: it reconstructs non-asymptotic geometry even when no limiting codimension
exists.

## 19. Parent collision audit and demarcation

`[BROAD SEARCH COMPLETED 2026-08-08] [NO PRIORITY CLAIM]`

The following ingredients and slogans are occupied parent territory:

1. Kolmogorov quotients, inverse systems of spaces, pro-objects, convergence spaces, approach
   spaces, and filtered topologies.  Therefore `{X_m}` alone is not new.
2. Rigged Hilbert spaces and distributional boundary vectors.  Therefore existence of a
   normalization limit outside one Hilbert space is not new.
3. Le Cam limits/local asymptotic normality and coherent-state limiting experiments.  Therefore a
   positive limiting kernel by itself is not new.
4. Inequivalent coherent representations in quantum field/gravity models; see Kegeles--Oriti--
   Tomlin, arXiv:1709.00161.
5. Observer-dependent causal frames and observer-dependent black-hole Hilbert spaces; see
   Guerin--Brukner, arXiv:1805.12429, Goto--Kazama, arXiv:1803.01672, and Abdalla--Antonini--
   Iliesiu--Levine, arXiv:2501.02632.
6. Filtering boundary observables to obtain a surviving wormhole Hilbert sector is now explicit in
   Wu, arXiv:2605.28748v2.  Consequently **"observer filtration creates a wormhole" is retired as
   a novelty claim**.
7. Holographic entanglement propagation through a wormhole after a local projection-like insertion
   appears in Doi--Li--Nguyen--Takayanagi, arXiv:2601.21604.  Therefore transition amplitudes across
   a wormhole are also not a novelty claim.
8. Fidelity susceptibility, quantum metrics, orthogonality catastrophes, and relations between
   response spectra and information geometry are established parent mechanisms.

Broad arXiv searches used observer-dependent topology, asymptotic experiments, rigged boundary
states, coherent inequivalent representations, orthogonality catastrophe, fidelity geometry,
Laplace spectral densities, dyadic reconstruction, black-hole observer algebras, and 2025--2026
wormhole/holography terms.  They returned many irrelevant papers, as intended.  No result found in
that audit packages the following four requirements:

\[
 \begin{gathered}
 \text{observer-grade point splitting generated by predeclared source amplifications},\\
 \text{clock-valued normalization stalks},\\
 \text{common-scale transition simplices not determined by pairwise kernels},\\
 \text{exact reconstruction of boundary normalization from interior phase metric}.
 \end{gathered}
\tag{I.57}
\]

Absence from search is not evidence of priority.  Candidate new content is the conjunction
`(I.57)` and Theorems I--V, not any parent ingredient or gravitational interpretation.  A category
theorist may still identify `(I.57)` as a standard decorated pro-object or a known simplicial
filter construction.  That is the leading novelty risk and requires specialist review.

### Internal-corpus collision

`temporal-completion-covariance-conjecture.md` already states that no observer-independent infinite
future exists and that completions form a comparison groupoid.  That ontology is a direct parent,
not a new result here.  Interfinity geometry advances it only where it supplies closed mathematics:

1. a source-clock equivalence with proved invariants;
2. one pro-space with continuum many inequivalent normalization/transition lifts;
3. a strictly positive pairwise Gram datum with no joint source-scale simplex;
4. the reconstruction law `(I.49)`--`(I.51)`.

The internal source-clock scale-rigidity theorem is another parent: it proves faithful HT grading
forces a scale of carriers.  It does not define observer-grade boundary identity or the
normalization/transition package.  The finite-observable conormal corona is likewise a parent for
rigged grades, not a collision with the present invariants.

The internal full-prime-nerve work is a stronger collision.  It already proves a strict
linearization obstruction for all finite-prime squares, describes nonzero two-curvature, and
formulates rank-three gluing as the missing source coherence.  Therefore **"pairwise data need a
higher simplex" is not new even inside this corpus**.  Theorem III remains a clean model and
independence witness, not a novelty headline.  Candidate novelty must couple that jointness defect
to source-clock normalization and cohomological visibility in the same invariant object.

Affine Hilbert 1-cocycles, growth of cocycles, contraction semigroups, and semigroup
representations on rigged Hilbert spaces are also parent mathematics; relevant broad-search
anchors include de Cornulier--Tessera--Valette, arXiv:math/0509527, and Wickramasekara--Bohm,
arXiv:math-ph/0302019.  Theorem IX does not claim those notions.  Its candidate delta is the exact
identification of observer grade with the minimal dual in which a non-Hilbert time cocycle becomes
a pointed coboundary, together with the topology--metric threshold in Theorem VII.

## 20. One-ray reconstruction of the entire complex interfinity

`[PAPER-PROVED] [REPRESENTATION THEOREM] [BERNSTEIN PARENT]`

Theorem V reconstructs `B` from `g`, but apparently only along one real escape ray.  In the coherent
Laplace class that one-dimensional datum is rigid enough to recover the full complex transition
experiment.

For a measure satisfying `(I.45)`, define on the whole complex plane

\[
 Q_\mu(z,w)=\int_0^1
 (e^{\bar z s}-1)(e^{ws}-1)\,d\mu(s)
\tag{I.58}
\]

and the normalized coherent kernel

\[
 K_\mu(z,w)=
 \exp\!\left(
 Q_\mu(z,w)-{1\over2}Q_\mu(z,z)-{1\over2}Q_\mu(w,w)
 \right).
\tag{I.59}
\]

The imaginary part of `(I.58)` retains phase, so `(I.59)` is stronger than a radial fidelity.

### Theorem VI (one-ray holographic rigidity)

The assignment

\[
 \mu\longmapsto
 g_\mu(V)=\int_0^1s^2e^{-2Vs}\,d\mu(s)
\tag{I.60}
\]

is injective on positive measures satisfying `(I.45)`.  Its image is exactly the completely
monotone functions `g` on `[0,infinity)` whose unique Bernstein measure is finite, supported in
`(0,2]`, and has no atom at zero.  From `g` one uniquely reconstructs:

1. the spectral measure `mu`;
2. the whole Hermitian form `Q_mu` on the complex plane;
3. the full complex transition kernel `K_mu`, including its projective phase;
4. the boundary vacuum action `B` by `(I.51)`;
5. every temporal codimension and normalization character that exists along the negative ray.

Thus the phase-metric coefficient observed on one real ray is a complete representation invariant
for coherent Laplace interfinities.

### Proof

Let `lambda` be the finite measure on `(0,1]` defined by

\[
 d\lambda(s)=s^2d\mu(s),
\tag{I.61}
\]

and let `rho` be its pushforward under `s|->2s`.  Then

\[
 g_\mu(V)=\int_{(0,2]}e^{-Vx}\,d\rho(x).
\tag{I.62}
\]

Bernstein's theorem makes `g_mu` completely monotone and makes `rho` the unique representing
measure.  Hence `g_mu=g_nu` implies equality of the pushforward measures, equality of `lambda`,
and then

\[
 d\mu(s)=s^{-2}d\lambda(s)=d\nu(s).
\tag{I.63}
\]

This proves injectivity.

Conversely, let `g` have the stated Bernstein measure `rho`.  Pull `rho` back by `x=2s` to a
finite measure `lambda` on `(0,1]` and define `mu` by `(I.63)`.  Then
`int s^2 dmu=lambda((0,1])<infinity`, and `(I.62)` recovers `g`.  This proves the image
classification.

For arbitrary fixed complex `z,w`, the estimate

\[
 |e^{zs}-1|\le |z|s e^{|z|s}
\tag{I.64}
\]

and `(I.45)` make `(I.58)` absolutely convergent.  Since `mu` is unique, so are `Q_mu` and
`K_mu`.  Formula `(I.51)` recovers `B`.  A source-pointed normalization must invert the vacuum
coefficient `e^{-B(V)}`, so its full asymptotic class and any power exponent are also fixed.
`QED`

### Consequence for the phase-time hunch

Within this exact class, a codimension-one record `g(V)` on an observer surface determines a
two-real-dimensional complex phase-time interior and its escaping boundary action.  Calling that
surface "holographic" is now mathematically defensible in the limited reconstruction sense: the
lower-dimensional response is complete for the higher-dimensional transition representation.
No claim is made that an actual black-hole boundary has a completely monotone response or that its
spectral measure is arithmetic.  Those become falsifiable realization questions.

### Anti-theatre verdict

Bernstein uniqueness is classical, coherent kernels are classical, and the proof is short.  The
new candidate is their role inside the point-reversing topology: the same one-ray field both
reconstructs the transition interior and, through Theorem V, determines how an endpoint first
exists for stronger observers.  If no non-coherent or non-Laplace extension preserves a comparable
rigidity theorem, this remains an elegant model rather than a new geometry of broad significance.

## 21. Spectral topology--metric trichotomy

`[PAPER-PROVED] [NONTRIVIAL TOPOLOGY/METRIC LINK]`

Fix `c>0` and `beta>-2`, and take

\[
 d\mu_\beta(s)=c s^{\beta-1}ds
 \qquad(0<s\le1).
\tag{I.65}
\]

Condition `(I.45)` holds exactly in the displayed range.  Let `B_beta`, `g_beta`, and
`psi_{-V}^{(beta)}` be the boundary action, phase metric, and coherent state from
`(I.46)`--`(I.48)`.

### Theorem VII (spectral endpoint trichotomy)

The following three regimes are exact.

#### Subcritical finite boundary: `beta>0`

\[
 B_\beta(V)\longrightarrow {c\over2\beta},
 \qquad
 \int_1^\infty\sqrt{g_\beta(V)}\,dV<\infty,
\tag{I.66}
\]

and `psi_{-V}^{(beta)}` converges strongly to the ordinary coherent state
`Exp(-1)` in the same Fock representation.

#### Critical interfinity: `beta=0`

\[
 B_0(V)={c\over2}\log V+O(1),
 \qquad
 g_0(V)\sim{c\over4V^2},
\tag{I.67}
\]

so the endpoint is weakly zero, lies at infinite phase-metric distance, and its source-pointed
vacuum normalization is power-law:

\[
 r(V)=e^{B_0(V)}\asymp V^{c/2}.
\tag{I.68}
\]

#### Supercritical interfinity: `-2<beta<0`

Put

\[
 I_\beta=\int_0^\infty(1-e^{-y})^2y^{\beta-1}dy
 =\Gamma(\beta)(2^{-\beta}-2)>0,
\tag{I.69}
\]

with the removable value `I_(-1)=2 log 2`.  Then

\[
 B_\beta(V)\sim {cI_\beta\over2}V^{-\beta},
 \qquad
 g_\beta(V)\sim
 {c\Gamma(\beta+2)\over(2V)^{\beta+2}}.
\tag{I.70}
\]

The endpoint is weakly zero and at infinite phase-metric distance, but its vacuum normalization is
stretched exponential:

\[
 r(V)=
 \exp\!\left[{cI_\beta\over2}V^{-\beta}(1+o(1))\right].
\tag{I.71}
\]

Consequently, in this family the three conditions

\[
 \begin{aligned}
 &\text{ordinary endpoint exists in the original Hilbert representation},\\
 &\text{boundary action remains finite},\\
 &\text{endpoint is at finite phase-metric distance}
 \end{aligned}
\tag{I.72}
\]

are equivalent, and hold exactly when `beta>0`.  Criticality `beta=0` is not chosen by analogy:
it is the unique threshold at which point existence, metric completeness, and normalization type
change together.

### Proof

For `beta>0`, the measure `mu_beta` is finite.  Dominated convergence gives

\[
 \|F_{-V}+1\|^2
 =c\int_0^1e^{-2Vs}s^{\beta-1}ds\longrightarrow0,
\tag{I.73}
\]

so coherent-state continuity gives strong convergence.  The same argument in `(I.47)` gives the
first limit in `(I.66)`.

For `beta<=0`, the measure has infinite total mass and monotone convergence makes
`||F_(-V)||->infinity`.  The dense exponential-vector estimate `(I.31)` then gives weak convergence
to zero.

For `-2<beta<0`, substitution `y=Vs` in `(I.47)` gives

\[
 B_\beta(V)
 ={c\over2}V^{-\beta}
 \int_0^V(1-e^{-y})^2y^{\beta-1}dy.
\tag{I.74}
\]

The limiting integral is finite at zero because `beta>-2` and at infinity because `beta<0`.
For `beta!=-1`, two integrations by parts are legitimate because the boundary terms are
`O(y^(beta+2))` at zero and `O(y^beta)` at infinity.  They give

\[
 I_\beta={1\over\beta(\beta+1)}
 \int_0^\infty[-2e^{-y}+4e^{-2y}]y^{\beta+1}dy
 =\Gamma(\beta)(2^{-\beta}-2).
\tag{I.74a}
\]

Taking the removable limit at `beta=-1` gives `2 log 2`.  Positivity is manifest from the
original integral.  This proves the first asymptotic in `(I.70)`.
The case `beta=0` is `(I.55)`.

For every `beta>-2`, substitution `y=2Vs` in `(I.48)` gives

\[
 g_\beta(V)
 ={c\over(2V)^{\beta+2}}
 \int_0^{2V}y^{\beta+1}e^{-y}dy
 \sim {c\Gamma(\beta+2)\over(2V)^{\beta+2}}.
\tag{I.75}
\]

Therefore `sqrt(g_beta(V))` is asymptotic to a positive constant times
`V^(-(beta+2)/2)`.  Its tail integral converges exactly when `(beta+2)/2>1`, namely when
`beta>0`.  Equations `(I.67)`--`(I.71)` and equivalence `(I.72)` follow. `QED`

### New topological invariant: visibility type

Observer grade alone records where an end first appears, but not how.  The theorem forces a
three-valued refinement:

\[
 \operatorname{vis}(-\infty)=
 \begin{cases}
 \text{finite},&\beta>0,\\
 \text{power},&\beta=0,\\
 \text{stretched exponential of order }-\beta,&-2<\beta<0.
 \end{cases}
\tag{I.76}
\]

This is stable under finite spectral perturbations in the critical case by `(I.54)`--`(I.56)`.
It separates interfinities whose endpoint quotient topology and first observer grade agree but
whose temporal approach type is inequivalent.

## 22. Three diagnostic failures and the later Gram correction

`[PAPER-PROVED INDEPENDENCE] [UNIVERSAL PRINCIPLE CONJECTURAL]`

The accumulated failures suggest that "find the right space" is the wrong problem.  Before the
full Hermitian Gram label is retained, a source representation can fail in three different
directions:

1. **Visibility (`V`)**: an endpoint has no source-pointed stalk in the admitted observer tower.
2. **Jointness (`J`)**: compatible lower-dimensional transition faces have no common-scale higher
   simplex.
3. **Orientation (`O`)**: quotient or intensity data erase a gauge-invariant cyclic phase.

The provisional representation object at this stage was

\[
 \mathfrak I=(\mathbf X_{\mathfrak O},\mathfrak N,
              \operatorname{Trans}(\mathfrak O),\operatorname{Barg})
\tag{I.77}
\]

where `Barg` retains the cyclic Bargmann phases of transition simplices.  The first two entries
control whether ends exist; the last two control whether comparisons exist and retain orientation.
Section 29 later corrects this precursor: once `Trans` is replaced by a simplicial set carrying the
full Hermitian Gram matrix, `Barg` becomes derived rather than independent data.

### Theorem VIII (three-face independence)

No one of `V`, `J`, and `O` is forced by the other two.  More precisely, there are explicit source
systems with exactly one defective face and the other two nondefective.

### Proof

#### Visibility defect with trivial jointness and orientation

Use the positive endpoint of Theorem II as a one-germ source system.  Its grade-one
source-pointed stalk is empty by `(I.34)`.  A one-vertex transition object has jointness
vacuously, and all displayed data are real, so it has no phase-orientation defect.  Thus `V` can
fail while `J` and `O` do not.

#### Jointness defect with ordinary visibility and real orientation

Use the finite-dimensional real vectors `(I.37)`--`(I.39)`.  Every vector is an ordinary grade-zero
state, so visibility holds.  All overlaps are real, so no hidden cyclic complex phase is involved.
Nevertheless the pairwise faces labelled by `(I.40)` have no common-scale 2-simplex.  Thus `J`
can fail while `V` and `O` do not.

#### Orientation defect with ordinary visibility and complete jointness

In `C^2`, put

\[
 A=e_1,\qquad
 B={e_1+e_2\over\sqrt2},\qquad
 C_\pm={e_1\pm i e_2\over\sqrt2}.
\tag{I.78}
\]

These are fixed grade-zero vectors, so visibility holds and every finite Gram matrix is already a
common-scale simplex.  The two labelled triangles have identical pairwise intensities:

\[
 |\langle A,B\rangle|
 =|\langle A,C_\pm\rangle|
 =|\langle B,C_\pm\rangle|={1\over\sqrt2}.
\tag{I.79}
\]

But their gauge-invariant Bargmann products are

\[
 \langle A,B\rangle\langle B,C_\pm\rangle
 \langle C_\pm,A\rangle={1\pm i\over4}.
\tag{I.80}
\]

Independent phase changes of `A,B,C` cancel from this cyclic product.  Hence an intensity-only
observer identifies two triangles that the oriented transition object separates.  Thus `O` can
fail while `V` and `J` do not. `QED`

### Interfinity completeness principle

The proposed higher universal principle is:

> A source problem is representationally closed only when every required infinity is visible in a
> source-generated stalk, every required family of comparisons is a joint common-scale simplex,
> and every cyclic phase orientation survives the chosen quotient.

This is stronger than asking for a Hilbert space, topology, cohomology theory, or spectral
operator.  Any of those may close two faces and still fail on the third.  Theorem VIII proves the
three *diagnostic failures* cannot be inferred from intensity-only data.  It does not prove three
independent components of the corrected object `(I.134)`: full complex Gram labels absorb the
orientation diagnostic.

### HGT obstruction reinterpretation `[CONJECTURAL CROSS-CORPUS MAP]`

The current evidence maps as follows:

| Corpus obstruction | Face | Exact evidence already available |
|---|---:|---|
| cofinal product sectors become mutually singular | `V` | prime/Fock weak-null ends and asymmetric normalization stalks |
| finite packets and pairwise reporter matches do not produce one global source object | `J` | common-scale simplex obstruction `(I.37)`--`(I.40)` models the missing lift |
| projectivization loses absolute source scaling | `O`/`V` | Suzuki quotient blindness versus determinant-line density |
| Gamma intensity is DA while oriented phase/delay is HT | `O` | formalized finite-differential non-recovery of phase and Wigner--Smith clock |
| rank-one common radicals recur across scalar routes | `J` | candidate shadow of a missing higher transition simplex, not yet proved |
| Burnol finite head exports to a dyadic boundary ladder | `V` | candidate source realization of the reconstruction recursion `(I.50)`, not yet proved |

Only the first, third, and fourth rows have direct theorem-level instantiations.  The other rows are
research conjectures.  The next hard task is to construct one source functor carrying at least
three distinct HGT routes into the same object `(I.77)` and prove that their terminal obstructions
are exactly its three face defects.  Without that functor, the table is interpretation rather than
new knowledge.

## 23. Cohomological horizons: infinity as a missing trivializer

`[PAPER-PROVED] [NEW REPRESENTATION INTERPRETATION]`

The coherent Laplace chart has more structure than a curve.  On
`H_beta=L^2((0,1),mu_beta)`, let

\[
 (T_Vf)(s)=e^{-Vs}f(s),\qquad V\ge0.
\tag{I.81}
\]

The formal constant `xi(s)=1` need not lie in `H_beta`, but

\[
 b_V=T_V\xi-\xi=e^{-Vs}-1
\tag{I.82}
\]

lies in `H_beta` for every finite `V` exactly when `beta>-2`.

### Failed conjecture IX.0 (ordinary cohomology detects the horizon)

The first formulation claimed that `b` became a coboundary in `Phi_m'` exactly when
`m+beta>0`.  This is false.  If `2m+beta>0` but `m+beta<=0`, the Hadamard finite-part functional

\[
 \eta_m^{\rm fp}(s^mh)
 =c\,\operatorname {Fp}\!\int_0^1h(s)s^{m+\beta-1}\,ds
\tag{I.83}
\]

is continuous on `Phi_m` and satisfies

\[
 T_V\eta_m^{\rm fp}-\eta_m^{\rm fp}=b_V.
\tag{I.84}
\]

Indeed, at every such admissible lower grade one necessarily has `m=1` and
`-1<m+beta<=0`; multiplication by `e^{-Vs}-1=O(s)` makes the finite-part integral in `(I.83)`
an ordinary convergent integral.  Thus ordinary distributional cohomology declares the cocycle
trivial before a boundary exists.  The missing condition is not existence of a trivializer.  It is
decay of that trivializer under source time.

For a Hausdorff topological semigroup representation `T` on `E`, call

\[
 \mathsf S(E)=\{\eta\in E:T_V\eta\longrightarrow0\text{ in }E\}
\tag{I.85}
\]

the **stable subspace**.  A cocycle is a **terminal coboundary** in `E` when it has the form
`b_V=T_Veta-eta` for some `eta in S(E)`.  Only a terminal coboundary has the forced endpoint
`b_V -> -eta`.

### Theorem IX (terminal-cohomological horizon classification)

For `beta>-2`:

1. `b` is an affine semigroup 1-cocycle:

   \[
   b_{V+W}=b_V+T_Vb_W.
   \tag{I.86}
   \]

2. `b` is a coboundary in `H_beta` if and only if `beta>0`.
3. At every admissible test grade `Phi_m`, equip `Phi_m'` with its weak-star topology.  Then `b` is
   an ordinary coboundary in `Phi_m'`.  It is a
   terminal coboundary there if and only if `m+beta>0`.
4. Let the integer test grades be

   \[
   \Phi_m=s^mC^\infty[0,1]\subset H_\beta
   \quad\hbox{whenever }2m+\beta>0,
   \tag{I.87}
   \]

   where the topology is transported from `C^infty[0,1]` by `h -> s^m h`.  The minimal dual grade
   at which a stable trivializer exists is

   \[
   m_\beta=\min\{m\in\mathbb N:m+\beta>0\}
   =\lfloor-\beta\rfloor+1
   \qquad(-2<\beta\le0).
   \tag{I.88}
   \]

5. Among admissible integer grades, the reciprocal-vacuum-normalized Fock boundary has a nonzero
   source-pointed limit on the exponential algebra over `Phi_m` exactly when `m>=m_beta`.

Thus observer grade is the first degree in which affine source time acquires a *stable*
trivializer.  A **terminal-cohomological horizon** is a locus where ordinary cohomology vanishes
but terminal cohomology does not.  This distinction is forced by the failed conjecture IX.0.

### Proof

Equation `(I.86)` is direct:

\[
 (e^{-Vs}-1)+e^{-Vs}(e^{-Ws}-1)=e^{-(V+W)s}-1.
\tag{I.89}
\]

If `beta>0`, the constant `xi=1` belongs to `H_beta`, so `(I.82)` is a Hilbert coboundary.
Conversely, suppose `b_V=T_Veta-eta` for some `eta in H_beta` and one `V>0`.  Then

\[
 (e^{-Vs}-1)(\eta(s)-1)=0
\tag{I.90}
\]

almost everywhere.  The first factor never vanishes on `(0,1]`; hence `eta=1` almost everywhere.
This belongs to `H_beta` exactly when

\[
 c\int_0^1s^{\beta-1}ds<\infty,
\tag{I.91}
\]

namely exactly when `beta>0`.  This proves item 2.

On `Phi_m`, the source-integral candidate is

\[
 \xi_m(f)=c\int_0^1f(s)s^{\beta-1}ds.
\tag{I.92}
\]

For `f=s^mh(s)`, this is finite and continuous exactly when `m+beta>0`.  In that case dominated
convergence gives `T_Vxi_m -> 0` and hence `b_V -> -xi_m` weakly on `Phi_m`; thus `xi_m` is a stable
trivializer.  If `m+beta<=0`, the fixed test `s^m` gives

\[
 \langle s^m,b_V\rangle
 =c\int_0^1(e^{-Vs}-1)s^{m+\beta-1}\,ds,
\tag{I.93}
\]

which tends to `-infinity`: logarithmically when `m+beta=0`, and as a positive constant times
`-V^{-(m+beta)}` when `-1<m+beta<0`.  Hence `b_V` has no weak limit in `Phi_m'`.  Any stable
trivializer would force such a limit, so none exists.  Nevertheless `(I.83)--(I.84)` give an
ordinary finite-part trivializer.  This proves item 3 and `(I.88)`.

Finally, reciprocal vacuum normalization changes the normalized coherent state into the
unnormalized exponential `e(b_V)`.  For every exponential test `e(f)`,

\[
 \langle e(f),e(b_V)\rangle=e^{\langle f,b_V\rangle}.
\tag{I.94}
\]

When `m+beta>0`, the exponent converges to `-xi_m(f)`, giving the nonzero functional
`e^(-xi_m)`.  When `m+beta<=0`, choosing the sign of `f=s^m` makes `(I.94)` diverge, while the
vacuum coefficient fixes the scalar normalization.  Hence no source-pointed Fock limit exists at
that grade. `QED`

### Representation jump

Ordinary geometry asks where the endpoint point should be added.  Terminal-cohomological
interfinity asks for a trivializer whose orbit dies under affine time, and records the observer
grade at which such a stable representative first exists.  The endpoint is derived from orbital
stability; neither a point nor an algebraic trivializer is primitive.

This reframes the critical power law.  At `beta=0` the source cocycle is nontrivial in Hilbert
space, already trivial by a finite-part distribution, but not terminally trivial until the first
source-integrable grade.  Metric completeness and power visibility detect the latter threshold,
not ordinary cohomology.

## 24. Terminal cohomology and the exact horizon sequence

`[PAPER-PROVED] [ABSTRACT REPRESENTATION THEOREM]`

The failed conjecture IX.0 exposes an invariant that ordinary semigroup cohomology forgets.  Let
`H -> E` be a continuous injection into a Hausdorff topological vector space.  Let `(T_V)_{V>=0}`
act continuously on `E`, preserve `H`, and be strongly stable on `H`:

\[
 T_Vh\longrightarrow0\quad(h\in H).
\tag{I.95}
\]

Define

\[
 \begin{aligned}
 E_H&=\{\xi\in E:(T_V-I)\xi\in H\text{ for every }V\ge0\},\\
 F_E&=\{\xi\in E:T_V\xi=\xi\text{ for every }V\ge0\},\\
 S_H&=\{\xi\in E_H:T_V\xi\longrightarrow0\text{ in }E\},\\
 (\delta\xi)_V&=(T_V-I)\xi,\qquad
 C_E=\delta(E_H).
 \end{aligned}
\tag{I.96}
\]

Elements of `C_E` are `H`-valued cocycles which are coboundaries only after enlargement to `E`.
The new quotient

\[
 \mathcal H^1_\infty(T;H\subset E)
 :=C_E/\delta(S_H)
\tag{I.97}
\]

is **terminal cohomology**.  It does not ask whether a cocycle can be solved.  It asks whether it
can be solved by a vector which disappears under forward source time.

### Theorem X (exact horizon sequence and endpoint criterion)

Under `(I.95)--(I.96)`:

1. There are canonical vector-space isomorphisms

   \[
   C_E/\delta(H)\cong E_H/(H+F_E),
   \qquad
   \mathcal H^1_\infty(T;H\subset E)\cong E_H/(S_H+F_E).
   \tag{I.98}
   \]

2. There is a canonical short exact sequence

   \[
   0\longrightarrow {S_H+F_E\over H+F_E}
   \longrightarrow {E_H\over H+F_E}
   \longrightarrow \mathcal H^1_\infty(T;H\subset E)
   \longrightarrow0.
   \tag{I.99}
   \]

3. For `b in C_E`, the following are equivalent:

   - `[b]=0` in terminal cohomology;
   - `b=delta eta` for a stable `eta in S_H`;
   - the orbit `b_V` converges in `E` as `V -> infinity`.

   When they hold, the stable trivializer and endpoint are forced:

   \[
   \eta=-\lim_{V\to\infty}b_V.
   \tag{I.100}
   \]

4. Suppose `E_0 -> E_1 -> ...` is an observer filtration by continuous intertwining maps which
   carry the embedded `H` consistently and carry stable vectors to stable vectors.  Then every
   cocycle defines a persistence trajectory

   \[
   [b]_0\longmapsto[b]_1\longmapsto\cdots,
   \qquad [b]_m\in\mathcal H^1_\infty(T;H\subset E_m).
   \tag{I.101}
   \]

   Once this trajectory vanishes it stays zero.  Its first vanishing grade is exactly the first
   observer grade at which the endpoint exists.

### Proof

The kernel of `delta:E_H -> C_E` is exactly `F_E`.  Since `H subset E_H`, the elementary
isomorphism theorem gives

\[
 {C_E\over\delta(H)}
 ={\delta(E_H)\over\delta(H)}
 \cong {E_H\over H+F_E}.
\tag{I.102}
\]

The same argument with `S_H` in place of `H` gives the second isomorphism in `(I.98)`.  Condition
`(I.95)` implies `H subset S_H`, so `H+F_E subset S_H+F_E`; the quotient map between the two
right-hand sides of `(I.98)` has kernel `(S_H+F_E)/(H+F_E)`.  This proves `(I.99)`.

The first two conditions in item 3 are the definition of the quotient.  If `b=delta eta` with
`eta` stable, then

\[
 b_V=T_V\eta-\eta\longrightarrow-\eta.
\tag{I.103}
\]

Conversely, suppose `b_V -> ell` in `E`.  The cocycle law and continuity of each `T_W` give, for
every fixed `W>=0`,

\[
 \ell=\lim_{V\to\infty}b_{V+W}
 =b_W+T_W\ell.
\tag{I.104}
\]

Thus `eta=-ell` satisfies `b_W=T_Weta-eta`.  It belongs to `E_H`, and
`T_Veta=b_V+eta -> 0`, so `eta in S_H`.  If two stable trivializers existed, their difference
would be both fixed and stable.  A fixed vector converging to zero in a Hausdorff space is zero.
This proves uniqueness and `(I.100)`.

Finally, an intertwining map sends `delta eta` to `delta` of the image and sends a stable vector
to a stable vector.  Hence it induces the arrows in `(I.101)`.  Zero is preserved, while item 3
identifies its first occurrence with endpoint convergence. `QED`

### Exact recovery of Theorem IX

Take `E_m=Phi_m'`.  At every admissible grade, the finite-part source `(I.83)` puts `b` in
`delta(E_m)`, so ordinary external cohomology is already zero.  For `m<m_beta`, equation `(I.93)`
shows that `[b]_m` is nonzero in terminal cohomology.  For `m>=m_beta`, the source integral
`xi_m` is stable, so `[b]_m=0`.  Therefore

\[
 m_\beta=\min\{m:[b]_m=0\text{ in }\mathcal H^1_\infty(T;H_\beta\subset\Phi_m')\}.
\tag{I.105}
\]

Within the declared integer observer tower, `m_beta` is now the death time of a precisely defined
obstruction class.  It is still a discretization-dependent ceiling.  Section 27 replaces it by a
continuous horizon cut.

### Geometry created by the theorem

The primitive object is no longer a set of points.  It is the filtered terminal-cohomology section

\[
 \mathbf{Hor}(b)=\bigl(\mathcal H^1_{\infty,m},[b]_m\bigr)_{m\ge0}.
\tag{I.106}
\]

An ordinary endpoint is the *death event* of this section.  An infinite-distance horizon is a
class which survives Hilbert grade but dies at a later observer grade.  A terminal horizon is a
class which never dies.  The topology of an interfinity is therefore a topology of exactness
failures: incidence means simultaneous death under one common-scale enlargement, and phase is the
cyclic obstruction to choosing those simultaneous stable trivializers coherently.

This is the conceptual jump forced by the proofs:

> space is the record of which affine-time equations become stably solvable under which observers.

Theorem X makes the one-point version exact.  The existing transition simplices and Bargmann face
in `(I.77)` supply the multi-point jointness and orientation data.  A representation object for the
whole geometry is therefore

\[
 \mathfrak G_\infty
 =\bigl(\{\mathbf{Hor}(b^a)\}_a,\operatorname{Trans},\operatorname{Barg}\bigr),
\tag{I.107}
\]

with `Trans` formed only from common-scale stable deaths.  This is stronger than the earlier
prospace: it remembers *why* a point exists and distinguishes finite-part algebraic solutions from
genuine terminal points.

## 25. Hostile parent audit for terminal cohomology

`[SEARCHED 2026-08-08] [NOVELTY STILL UNVERIFIED]`

Broad searches for semigroup cohomology, stable coboundaries, asymptotic cohomology, persistent
cohomology, and rigged-Hilbert semigroups found six close parent families:

1. ordinary and reduced first cohomology of unitary representations, including harmonic cocycle
   representatives (Bekka, arXiv:1612.08944);
2. asymptotic cohomology for almost-representations and Ulam stability (Glebsky--Lubotzky--Monod--
   Rangarajan, arXiv:2301.00476);
3. persistent equivariant cohomology of filtered group spaces (Adams--Lagoda--Moy--Sadovek--De
   Saha, arXiv:2408.17331);
4. semigroup decay and generalized spectral vectors in rigged Hilbert spaces (Chiba,
   arXiv:1107.5858; Colbrook--Horning--Xie, arXiv:2410.08343).
5. sharp Sobolev regularity thresholds and distributional obstructions for cohomological equations
   (Forni, arXiv:0707.0940);
6. poset-indexed persistence modules, including a 2026 continuum of tensor products and Kunneth
   exact sequences (Milicevic, arXiv:2604.20004).
7. persistent sheaf cohomology with simultaneous algebraic and topological filtration directions
   (Russold, arXiv:2204.13446).
8. filtered spaces and persistence Spanier--Whitehead categories in stable homotopy (Miller,
   arXiv:2505.02772).
9. Scott and Vietoris topologies on inclusion lattices (Chen--Kou--Lyu, arXiv:2103.15139).
10. differential complexes whose geometric positivity hypotheses imply global solvability and
    Sobolev regularity (Ji--Yao, arXiv:2507.18341v3, revised 2026).
11. exact differential forms which define nonzero bounded-cohomology classes because bounded
    cohomology restricts the admissible primitives (Battista--Francaviglia--Moraschini--Sarti--
    Savini, arXiv:2211.16125).
12. multiparameter persistence and its large-scale quotient by negligible regions (Botnan--
    Lesnick, arXiv:2203.14289; Frankland--Stanley, arXiv:2211.05981v4, revised 2026).

These own the words `cohomology`, `asymptotic`, `persistence`, `stable subspace`, and `rigged
semigroup`.  They do not by themselves establish priority for `(I.97)--(I.105)`.  In particular:

- reduced cohomology closes the space of ordinary coboundaries; `(I.97)` instead restricts
  primitives to vectors whose forward orbit tends to zero;
- published asymptotic cohomology above controls defects of sequences of almost-representations,
  not terminal limits of one semigroup cocycle;
- persistent equivariant cohomology filters spaces and then applies Borel cohomology, whereas
  `(I.101)` filters coefficient environments and records when a dynamical primitive becomes
  stable;
- rigged spectral theory supplies the ambient dual spaces and decay technology, not the exact
  horizon quotient or the endpoint criterion.
- Forni's work owns the principle that solvability and obstruction spaces jump across a continuous
  regularity scale.  Section 27's weighted regularity cut is therefore not new by itself.
- interval deaths, joins, and tensor behavior are standard persistence-module territory.  The
  maximum-cut statement in Theorem XII is bookkeeping, not a novelty claim.
- the Scott/Sierpinski proof in Theorem XXVIII is standard domain theory once the stable-coboundary
  subspaces are supplied.  Its candidate delta is the source-equation representation and its
  strict separation from common-clock higher incidence, not Scott topology itself.
- the broad mechanism “ordinary-exact data remain nontrivial when primitives obey an extra
  boundedness condition” is occupied by bounded cohomology.  Stable-primitive cohomology cannot
  claim that slogan; its narrower candidate delta is forward-time disappearance, endpoint
  equivalence, observer persistence, and the arithmetic three-chart realization.

The internal corpus has an important philosophical parent: `adjoint-duality-cauchy-nerve-purity-
law.md` already says that a globally chosen bounded trivialization is only a coboundary and that
content lives in descent and sewing.  `source-transgression-field.md` also studies obstruction
classes across finite clocks.  Neither file defines the stable-primitive quotient, proves the
finite-part counterexample IX.0, or gives `(I.99)--(I.105)`.  This is a candidate delta, not a
priority claim.  A specialist in semigroup cohomology could still identify `(I.97)` as an unnamed
relative quotient already used elsewhere.

## 26. A non-dying endpoint concentrates into a fixed horizon ray

`[PAPER-PROVED] [NEW INVARIANT INSIDE THE PACKAGE]`

The lower-grade failure in Theorem IX is more rigid than nonconvergence.  Put `a=m+beta` and use
the identification `Phi_m congruent C^infty[0,1]`, `s^m h <-> h`.  Let

\[
 \delta_0(s^mh)=h(0).
\tag{I.108}
\]

When `-1<a<0`, choose the finite-part trivializer

\[
 \eta_a(s^mh)
 =c\left\{\int_0^1(h(s)-h(0))s^{a-1}\,ds+{h(0)\over a}\right\}.
\tag{I.109}
\]

At `a=0`, choose

\[
 \eta_0(s^mh)=c\int_0^1{h(s)-h(0)\over s}\,ds.
\tag{I.110}
\]

### Theorem XI (fixed-ray horizon concentration)

For the multiplication semigroup on `Phi_m'`:

1. its fixed subspace is exactly `C delta_0`;
2. if `-1<a<0`, then weak-star in `Phi_m'`,

   \[
   V^aT_V\eta_a\longrightarrow c\Gamma(a)\delta_0;
   \tag{I.111}
   \]

3. if `a=0`, then

   \[
   {1\over\log V}T_V\eta_0\longrightarrow-c\delta_0;
   \tag{I.112}
   \]

4. the same scaled limits hold with `b_V=T_Veta_a-eta_a` in place of `T_Veta_a`.  They are
   independent of the choice of finite-part extension.

Consequently a terminal-cohomology class which fails to die at the last deficient grade has a
canonical **horizon residue**: a projective ray in the fixed space together with a power or
logarithmic growth character.  It is not an added endpoint.  It is the direction into which failed
endpoint formation concentrates.

### Proof

If `u` is fixed, then `(e^{-Vs}-1)u=0`.  The smooth function
`(e^{-Vs}-1)/s` extends to a nowhere-zero function on `[0,1]`; hence `su=0`.  Every
`h in C^infty[0,1]` is `h(0)+sr`, so a functional killed by `s` is a multiple of `delta_0`.
Conversely `delta_0` is fixed.  This proves item 1.

For `-1<a<0`, splitting `h=h(0)+sr` in `(I.109)` gives

\[
 (T_V\eta_a)(s^mh)
 =c\,h(0)V^{-a}\gamma(a,V)
   +c\int_0^1e^{-Vs}r(s)s^a\,ds,
\tag{I.113}
\]

where the first term is the analytic-continuation identity for the lower incomplete gamma
function.  Since `gamma(a,V)->Gamma(a)` and

\[
 \left|\int_0^1e^{-Vs}r(s)s^a\,ds\right|
 \le\lVert r\rVert_\infty\Gamma(a+1)V^{-a-1},
\tag{I.114}
\]

multiplication by `V^a` proves `(I.111)`.

For `a=0`, `(I.110)` gives

\[
 (T_V\eta_0)(s^mh)
 =c\,h(0)\int_0^V{e^{-t}-1\over t}\,dt
   +c\int_0^1e^{-Vs}r(s)\,ds.
\tag{I.115}
\]

The first integral is `-log V-gamma+o(1)` and the second is `O(V^{-1})`, proving `(I.112)`.
The fixed `eta_a` is negligible after either scaling, so the result also holds for
`b_V=T_Veta_a-eta_a`.

Finally, two continuous extensions of the ordinary source integral from the codimension-one
subspace `h(0)=0` differ by a multiple of `delta_0`.  Such a difference is fixed, leaves `b`
unchanged, and is negligible relative to the divergent power or logarithm.  The horizon residue is
therefore finite-part-gauge invariant. `QED`

### Big-picture reinterpretation

The traditional picture offers two choices: add a point at infinity or declare divergence.  The
new geometry has a third state.  Time can compress an unsolved affine equation onto a fixed ray,
with a scale character measuring the compression.  A black-hole-style `holographic surface` is,
in this mathematical model, the fixed representation face receiving those residues.  A
`wormhole` would be a common-scale relation between residues of distinct source times, not a tube
inserted between pre-existing points.  This is a mathematical metaphor and a construction target,
not a claim about gravitational physics.

## 27. Exactness-cut topology: the horizon is not a point

`[PAPER-PROVED] [CONTINUOUS OBSERVER GEOMETRY]`

Integer grades conceal the topology.  For real `rho`, define

\[
 \Phi_\rho=s^\rho C^\infty[0,1]
\tag{I.116}
\]

with the topology transported from `C^infty[0,1]`.  It embeds continuously in `H_beta` exactly
when

\[
 2\rho+\beta>0.
\tag{I.117}
\]

The admissible observer line is therefore

\[
 \mathcal O_\beta=(\mathfrak a_\beta,\infty),
 \qquad \mathfrak a_\beta=-{\beta\over2}.
\tag{I.118}
\]

Order it by observer strength and give it the upper Alexandrov topology.  For a cocycle `b`, its
**death open** is

\[
 D(b)=\{\rho\in\mathcal O_\beta:[b]_\rho=0
 \text{ in terminal cohomology}\}.
\tag{I.119}
\]

### Theorem XII (horizon-cut trichotomy)

For the spectral family of Theorems VII and IX, with `beta>-2`:

1. `b` is an ordinary finite-part coboundary at every admissible `rho`.
2. It is a terminal coboundary exactly when

   \[
   \rho+\beta>0.
   \tag{I.120}
   \]

3. Its death open and terminal cut are

   \[
   D_\beta=(\mathfrak d_\beta,\infty),\qquad
   \mathfrak d_\beta=\max\left(-{\beta\over2},-\beta\right),
   \tag{I.121}
   \]

   where `(d_beta,infinity)` is read as all of `O_beta` when `d_beta=a_beta`.
4. With `rho` calibrated by spectral vanishing order, the **horizon width**

   \[
   w_\beta=\mathfrak d_\beta-\mathfrak a_\beta
   =\max\left(0,-{\beta\over2}\right)
   \tag{I.122}
   \]

   is reconstructed from the interior phase metric by

   \[
   w_\beta
   =\max\left(0,
      1+{1\over2}\lim_{V\to\infty}{\log g_\beta(V)\over\log V}
     \right).
   \tag{I.123}
   \]

5. For a finite direct sum of independent spectral channels, the common terminal cut is the
   maximum of their cuts.

The three regimes are now topological:

- `beta>0`: **filled** -- the Hilbert cocycle is already trivial and `w_beta=0`;
- `beta=0`: **contact horizon** -- the Hilbert class is nonzero, but it dies in every admissible
  positive dual grade; the death cut touches the admissibility cut and is not attained;
- `-2<beta<0`: **gapped horizon** -- a nonempty interval of admissible observers still sees a
  nonzero terminal class, of width `-beta/2`.

### Proof

For `f=s^rho h`,

\[
 \lVert f\rVert_{H_\beta}^2
 =c\int_0^1|h(s)|^2s^{2\rho+\beta-1}\,ds.
\tag{I.124}
\]

This is finite for every smooth `h` exactly under `(I.117)`.  Put `a=rho+beta`.  Because
`beta>-2`, admissibility implies `a>beta/2>-1`.  Hence the finite-part constructions
`(I.109)--(I.110)` give an ordinary dual trivializer whenever `a<=0`; for `a>0` the ordinary source
integral does so.

The source integral is stable exactly when `a>0`, by dominated convergence.  For `-1<a<=0`,
Theorem XI shows that its finite-part extension has a nonzero fixed-ray asymptotic and is not
stable.  Equivalently, `(I.93)` has no weak-star limit, so Theorem X rules out every alternative
stable trivializer.  This proves `(I.120)`.  Intersecting `rho>-beta` with the admissible line
`rho>-beta/2` gives `(I.121)` and subtraction gives `(I.122)`.

Theorem VII gives

\[
 \lim_{V\to\infty}{\log g_\beta(V)\over\log V}=-(\beta+2),
\tag{I.125}
\]

and substitution proves `(I.123)`.  Finally, a vector in a finite direct sum is stable if and only
if every component is stable.  The intersection of the channel death opens is therefore the upper
ray beginning at the maximum cut. `QED`

### New topology, stated without metaphor

The exactness-cut topology lives on observer capability, not on an assumed ambient set of spatial
points.  A horizon is the frontier of the open set on which a source equation has a stable
primitive.  A point at infinity is derived only after crossing that frontier.  For several source
times, their first possible common throat is the join of their cuts; any later joint cut is a
measurable **synchrony excess** caused by transition-simplex failure.

This construction explains why ordinary completions kept failing.  They ask whether sequences
converge after one topology is chosen.  Exactness-cut topology instead makes the *poset of
topologies* into space and marks where an affine-time obstruction dies.  Criticality is tangency
of two cuts: admissibility of an observer and stable solvability of time meet without a minimal
dual observer.

## 28. Terminal cohomology is exactly the coherent-boundary obstruction

`[PAPER-PROVED] [ABSTRACT SOURCE FUNCTOR]`

Let

\[
 \Phi\hookrightarrow H\hookrightarrow\Phi'
\tag{I.126}
\]

be a complex test--Hilbert--dual triple, with `Phi` Frechet and `Phi'` carrying the weak-star
topology.  Suppose the semigroup and an `H`-valued cocycle `b` satisfy Theorem X.  Write
`epsilon(h)` for the bosonic exponential vector and

\[
 \psi_V=e^{-\lVert b_V\rVert^2/2}\epsilon(b_V).
\tag{I.127}
\]

Its vacuum coefficient is `e^(-||b_V||^2/2)`, so source-pointed normalization gives

\[
 \widetilde\psi_V
 ={\psi_V\over\langle\Omega,\psi_V\rangle}
 =\epsilon(b_V),
 \qquad
 S_V(f):=\langle\epsilon(f),\widetilde\psi_V\rangle
 =e^{\langle f,b_V\rangle}.
\tag{I.128}
\]

Call a **coherent boundary on `Phi`** a limit `S_infinity(f)=e^{L(f)}` with `L in Phi'`, where
`S_V` converges locally uniformly on every finite-dimensional complex subspace of `Phi`.

### Theorem XIII (Fock--terminal equivalence)

The following are equivalent:

1. `[b]=0` in `H^1_infinity(T;H subset Phi')`;
2. `b_V` converges weak-star in `Phi'`;
3. the reciprocal-vacuum-normalized coherent curve has a coherent boundary on `Phi`.

When these hold, all data are forced by one stable trivializer:

\[
 \eta=-\lim_{V\to\infty}b_V,
 \qquad
 S_\infty(f)=e^{-\eta(f)}.
\tag{I.129}
\]

Thus terminal cohomology is not merely analogous to the earlier normalization stalk.  On every
coherent chart it is exactly the obstruction represented by that stalk.

### Proof

Theorem X proves `1 iff 2` and `(I.129)` at the one-particle level.  If `b_V -> ell` weak-star,
then on a finite-dimensional subspace with basis `f_1,...,f_n`, all coordinates
`<f_j,b_V>` converge.  The linear forms therefore converge uniformly on compact subsets, and so do
their exponentials.  This gives `S_infinity(f)=e^{ell(f)}=e^{-eta(f)}` and proves `2 implies 3`.

Conversely, fix `f in Phi` and restrict `(I.128)` to the complex line `tf`.  Local uniform
convergence of the holomorphic functions

\[
 t\longmapsto e^{t\langle f,b_V\rangle}
\tag{I.130}
\]

allows differentiation at `t=0`.  Hence

\[
 \langle f,b_V\rangle
 =\left.{d\over dt}S_V(tf)\right|_{t=0}
 \longrightarrow
 \left.{d\over dt}e^{tL(f)}\right|_{t=0}=L(f).
\tag{I.131}
\]

This is weak-star convergence to `L`, proving `3 implies 2`. `QED`

### What this unifies, and what it does not

The theorem gives one source functor for the prime Fock normal cone, every spectral family in
Section 21, and any future coherent realization: send a source-time curve to its cocycle, then to
its terminal-cohomology section.  Weak-zero collapse of normalized Fock states, distributional
boundary recovery, and observer grade are now three images of one exact obstruction.

The coherent-state formula and generalized coherent functionals have large parent literatures.
Novelty cannot be claimed for `(I.128)` itself.  Candidate new content is the factorization through
the stable-primitive quotient, its horizon-cut filtration, and its combination with common-scale
transition and cyclic orientation faces.  Non-coherent HGT routes still lack a proved source
functor.

## 29. The new geometry: a filtered terminal nerve with a fixed residue face

`[DEFINITION FROZEN] [STRUCTURE LAWS PAPER-PROVED]`

The preceding pieces now determine a geometry rather than a list of analogies.  Let `A` label
source-time experiments.  At observer `o`, experiment `a` has an `H`-valued cocycle `b^a` and a
clocked normalized representation vector `v_i^a`.  A `k`-simplex at `o` is an ordered label tuple
`(a_0,...,a_k)` together with a specified Hermitian matrix `G=(g_rs)` such that

1. every full declared-clock cocycle `b^(a_r)` has zero terminal class in `E_o`; and
2. one allowed common source synchronization makes the entire finite Gram matrix

   \[
   G_i=(\langle v_i^{a_r},v_i^{a_s}\rangle)_{0\le r,s\le k}
   \tag{I.132}
   \]

   converge to the *specified* matrix `G`.

The synchronization in item 2 is comparison data only.  It is not allowed to manufacture a
vertex by selecting a convergent subnet of a nonterminal cocycle.

Write `N_o[k]` for these data.  Face maps delete one label and the corresponding row and column;
degeneracy maps repeat them.  Retaining `G` is essential: different cofinal synchronizations of
the same labels can define different simplices.  For a non-dying but regularly varying class,
Theorem XI attaches its horizon residue in the fixed face `P(F_E)`.  On every joint triangle whose
limiting overlaps `g_ac` are nonzero, put

\[
 \Omega(a,c,d)
 ={g_{ac}g_{cd}g_{da}\over|g_{ac}g_{cd}g_{da}|}\in U(1).
\tag{I.133}
\]

The **interfinity exactness geometry** is

\[
 \mathfrak X_\infty
 =\left(
   (\mathcal O,\tau_{\rm ex},\{\kappa_n\}_{n\ge1}),
   \{\mathbb H^n_{\infty,o}\}_{n\ge1,o},
   \{\mathcal H^1_{\infty,o}\}_o,
   \{N_o\}_o,
   \operatorname{Res}_\infty
  \right).
\tag{I.134}
\]

Here `mathbb H` denotes the all-degree stable-primitive tower introduced in Section 40, while the
earlier calligraphic `H` is its degree-one external endpoint kernel.  The forward reference records
the final corrected object.  Section 43 identifies `tau_ex` as the pullback Scott topology under
the stable-coboundary profile maps `kappa_n`.  The function `Omega` in `(I.133)` is derived from a
simplex's Hermitian Gram label, so hostile review removes it as an independent component.

This is not a manifold whose points were chosen first.  Its zero-simplices are endpoint equations
that become stably exact; its higher simplices say which endpoints can coexist under one source
clock; its fixed face receives classes that concentrate instead of dying; and every nondegenerate
filled two-face carries a derived `U(1)` orientation invisible to intensities.

### Theorem XIV (terminal-nerve laws)

Assume observer-strengthening maps are continuous, intertwine source time, preserve the embedded
Hilbert vectors, and preserve common source clocks.  Then:

1. each `N_o` is a simplicial set;
2. `o<=o'` induces a simplicial map `N_o -> N_o'`, so the nerves form a persistence object;
3. for a proposed Gram-labelled simplex `sigma=(a_0,...,a_k;G)`, its joint death region and, when
   `O` is a calibrated linearly ordered subset of the extended reals, its numerical death cut are

   \[
   \mathcal D(\sigma)=\{o:\sigma\in N_o[k]\},
   \qquad
   \mathfrak d(\sigma)=\inf\mathcal D(\sigma).
   \tag{I.135}
   \]

   The region is an upper set and is face-monotone:
   `D(sigma) subset D(tau)` for every face `tau`; consequently
   `d(tau)<=d(sigma)` whenever the numerical cuts are defined;
4. the **synchrony excess**

   \[
   \kappa(\sigma)
   =\mathfrak d(\sigma)-sup_{\tau\subsetneq\sigma}\mathfrak d(\tau)
   \tag{I.136}
   \]

   for positive-dimensional `sigma` in the calibrated numerical case, whenever this extended-real
   difference is defined.  It is nonnegative and can be infinite even when every proper-face cut
   is finite;
5. `Omega` is invariant under independent phase gauges `v^a -> e^(i theta_a)v^a` and obeys the
   tetrahedral Bianchi identity

   \[
   \Omega(1,2,3)\Omega(0,2,3)^{-1}
   \Omega(0,1,3)\Omega(0,1,2)^{-1}=1
   \tag{I.137}
   \]

   wherever all six limiting edge overlaps are nonzero.

### Proof

Deleting or repeating rows and columns of a convergent Gram matrix uses the same common
synchronization.  The usual deletion and repetition operations obey the simplicial identities, so
item 1 follows.  Continuous intertwining observer maps preserve zero terminal classes and carry a
specified Gram limit with its synchronization forward, proving item 2 and upward closure of
`D(sigma)`.  A realization of `sigma` realizes every specified principal face, so
`D(sigma) subset D(tau)`.  Taking infima in the calibrated numerical case proves the cut inequality
and hence item 4.

Give the parity construction in Theorem III the zero cocycle at every vertex.  All vertices are
therefore terminal under their full clocks.  Choose the three edge simplices with

\[
 g_{AB}=1/2,\qquad g_{AC}=1/2,\qquad g_{BC}=0.
\tag{I.138}
\]

Each is realized on its stated cofinal synchronization.  Their proposed full Gram matrix is even
strictly positive definite, but no common synchronization realizes all three specified entries.
Thus the specified boundary has no filler; already the two-edge horn consisting of the `AB` and
`AC` charts has none.  Other triangle simplices on the same three labels may exist; they do not
fill this horn because their edge data differ.  The obstruction
is therefore genuinely simplicial and chart-sensitive, not failure of an underlying flag complex.

For item 5, write `u_ac=g_ac/|g_ac|`, so `u_ca=u_ac^{-1}` and
`Omega(a,c,d)=u_ac u_cd u_da`.  Vertex gauge phases cancel in this product.  Expanding the four
oriented face products in `(I.137)` cancels every `u_ac` with `u_ca`, proving the identity. `QED`

### Axioms visible in the construction

The geometry has four structural laws and one derived face law:

1. **observer covariance:** cofinal changes do not alter terminal classes or joint simplices;
2. **terminal exactness:** a point exists exactly when a cocycle has a forward-stable primitive;
3. **common-clock locality:** higher incidence requires one source subnet, not assembled pairwise
   limits;
4. **residue completion:** a regularly varying non-dying class lands on a fixed projective face;
5. **derived phase orientation:** the Hermitian Gram label induces cyclic phase on joint two-faces
   and it satisfies `(I.137)`; it is not extra primitive data.

In the black-hole metaphor suggested at the start, `P(F_E)` is the holographic face, an edge of
`N_o` is a throat, `kappa` is obstruction to filling a multi-mouth chamber, and `Omega` is phase of
time around a filled chamber.  Mathematically, all four objects are defined without spacetime or
gravity.  No claim is made that a physical black hole realizes them.

### Anti-theatre boundary

Simplicial sets, persistence modules, projective fixed spaces, and Bargmann phases
are established parents.  Theorem XIV's formal laws are correspondingly elementary.  Candidate
novelty of `(I.134)` is the *specific gluing rule*: vertices are deaths in stable-primitive
cohomology, the residue face records the failure of those deaths, and higher incidence is restricted
by source-synchronous Gram convergence.  Significance requires this object to compress distinct HGT
obstacles and generate a theorem unavailable in their original representations.  Theorem XIII does
this for all coherent routes; the non-coherent compression remains open.

## 30. Phase of complex time measures distance to the exactness cut

`[PAPER-PROVED] [PHASE--TOPOLOGY LOCKING]`

Complexify decay time inside the right half-plane:

\[
 T_zf(s)=e^{-zs}f(s),\qquad \Re z>0.
\tag{I.139}
\]

Put `a=rho+beta>-1`.  The source is ordinary for `a>0`, finite-part for `a<0`, and logarithmic at
`a=0`.  Its fixed-ray coefficient carries both radial growth and angular phase; exactness-cut
distance enters in the deficient range.

### Theorem XV (sectorial radial--phase locking)

Fix `epsilon>0` and let `z=R e^(i theta)` with
`|theta|<=pi/2-epsilon`.

1. If `-1<a<infinity` and `a!=0`, uniformly on compact theta intervals,

   \[
   R^aT_{Re^{i\theta}}\eta_a
   \longrightarrow c\Gamma(a)e^{-ia\theta}\delta_0.
   \tag{I.140}
   \]

   Hence for the nonzero leading fixed-ray coefficient `q_a(R,theta)`, the first two limits below
   equal `-a`; at a deficient observer (`a<0`) they also equal cut distance:

   \[
   \lim_{R\to\infty}\partial_{\log R}\log|q_a|
   =\lim_{R\to\infty}\partial_\theta\arg q_a
   =-a,
   \qquad
   a<0\Longrightarrow -a=\mathfrak d_\beta-\rho.
   \tag{I.141}
   \]

2. At `a=0`, on the principal right-half-plane branch,

   \[
   T_z\eta_0=-c(\log z+\gamma)\delta_0+o(1),
   \tag{I.142}
   \]

   weak-star.  Thus the multiplicative phase charge vanishes at the contact cut, but radial and
   angular derivatives retain the same additive coefficient:

   \[
   \partial_{\log R}\Re q_0
   =\partial_\theta\Im q_0=-c+o(1).
   \tag{I.143}
   \]

Therefore complex-time phase gives an operational coordinate on exactness-cut topology: its slope
is precisely the remaining observer distance to terminal solvability.

### Proof

Analytic continuation of `(I.113)` into every closed subsector of the right half-plane gives

\[
 (T_z\eta_a)(s^mh)
 =c\,h(0)z^{-a}\gamma(a,z)
  +c\int_0^1e^{-zs}r(s)s^a\,ds.
\tag{I.144}
\]

The upper incomplete-gamma remainder is exponentially small there, so
`gamma(a,z)->Gamma(a)`.  Also `Re z>=R sin(epsilon)`, and the second term is
`O(R^(-a-1))` uniformly for `h` in a fixed test direction.  Since
`z^(-a)=R^(-a)e^(-ia theta)`, this proves `(I.140)`.  Logarithmic radial and angular
differentiation of `(I.144)` gives the same estimates with one derivative (the extra factor of
`s` improves the remainder), so the leading regularly varying term gives the first two quantities in
`(I.141)`.  In the deficient interval, Theorem XII has `d_beta=-beta`; hence
`-a=-(rho+beta)=d_beta-rho`.

For `a=0`, the complex version of `(I.115)` uses

\[
 \int_0^1{e^{-zs}-1\over s}\,ds=-\log z-\gamma+o(1)
\tag{I.145}
\]

uniformly in the same sectors, while the `r`-term is `O(R^-1)`.  This proves `(I.142)` and direct
differentiation gives `(I.143)`. `QED`

### Physical metaphor, sharply limited

Equation `(I.141)`, not a spacetime picture, is the precise surviving content of the initial
phase-time hunch.  The `holographic face` is the fixed ray receiving the asymptotic coefficient;
rotation of complex source time turns radial divergence into phase at a rate equal to observer-cut
deficit.  No closed loop lies wholly in the decay half-plane, so this theorem does **not** claim a
black-hole holonomy or physical wormhole.  Watson asymptotics, Mellin powers, and the
Cauchy--Riemann locking are classical parents.  Candidate new content is their exact identification
with terminal-cohomology cut distance.

## 31. Covariance of the completed geometry

`[PAPER-PROVED]`

A terminal source-clock equivalence consists of the equivalence in Theorem I together with, at
every observer `o`, a topological linear isomorphism

\[
 U_o:E_o\longrightarrow E'_{\theta(o)}
\tag{I.146}
\]

which carries `H` onto `H'`, intertwines the full source semigroups under their tail-identical clock
identification, and is unitary on the Hilbert representation vectors used for Gram data.

### Theorem XVI (interfinity covariance)

Such an equivalence induces canonical isomorphisms

\[
 \mathcal H^1_{\infty,o}(T;H\subset E_o)
 \cong
 \mathcal H^1_{\infty,\theta(o)}(T';H'\subset E'_{\theta(o)})
\tag{I.147}
\]

and a simplicial isomorphism `N_o congruent N'_(theta(o))`.  It carries terminal endpoints,
projective horizon residues, and `Omega` to their primed counterparts.  Death opens and cuts are
transported order-theoretically by `theta`.

Numerical cut widths are invariant only when the observer scale has a declared calibration
preserved by `theta`.  Without that calibration, `filled/contact/gapped`, incidence, and cut order
remain invariant, but a numerical width can be changed by reparametrizing observer strength.

### Proof

Intertwining gives

\[
 U_o((T_V-I)\xi)=(T'_V-I)U_o\xi.
\tag{I.148}
\]

Thus `U_o` maps `E_H`, fixed vectors, and external cocycles bijectively to their primed versions.
Because both `U_o` and its inverse are continuous and the clock identification is a tail
equivalence, `T_Vxi->0` if and only if `T'_VU_oxi->0`.  Hence it maps `S_H` bijectively to `S'_H`
and descends to `(I.147)`.  The endpoint formula `(I.100)` commutes with `U_o`.

Unitary preservation of every clocked Hilbert vector carries each specified limiting Gram matrix,
with its source synchronization, in both directions.  Therefore it gives a simplicial isomorphism.
Fixed spaces map to fixed spaces, so Theorem XI's projective residue does also; Gram preservation
keeps `(I.133)` unchanged.  The statements about death opens and cuts follow.  Finally an arbitrary
order isomorphism preserves an upper cut but not a chosen Euclidean difference between its
endpoints, proving the calibration caveat. `QED`

## 32. Terminal transgression: curvature left after time becomes exact

`[PAPER-PROVED] [NON-COHERENT EXTENSION]`

Let `M` be a topological monoid represented by continuous linear maps `pi(g)` on `E`, preserving
`H`.  Let `r:R_+ -> M` be a source-time semigroup ray,

\[
 r(V+W)=r(V)r(W),
\tag{I.149}
\]

and suppose `pi(r(V))h -> 0` for every `h in H`.  Let `b:M -> H` be a continuous 1-cocycle:

\[
 b(gh)=b(g)+\pi(g)b(h).
\tag{I.150}
\]

Assume only that the radial cocycle converges in `E`,

\[
 b(r(V))\longrightarrow\ell.
\tag{I.151}
\]

Put `eta=-ell` and define the **terminal transgression residue**

\[
 \mathfrak R_b(g)
 =b(g)-(\pi(g)\eta-\eta)\in E.
\tag{I.152}
\]

### Theorem XVII (central-time descent and commutator residue)

Under `(I.149)--(I.151)`:

1. `eta` is the unique stable primitive of the restricted time cocycle:

   \[
   b(r(V))=\pi(r(V))\eta-\eta,
   \qquad \pi(r(V))\eta\longrightarrow0.
   \tag{I.153}
   \]

2. `R_b` is an `E`-valued 1-cocycle and vanishes on the time ray.
3. For every `g in M`,

   \[
   \mathfrak R_b(g)
   =-\lim_{V\to\infty}
      \bigl(b(r(V)g)-b(gr(V))\bigr).
   \tag{I.154}
   \]

4. The radial endpoint extends to one stable primitive for the whole source monoid if and only if
   all limits in `(I.154)` vanish.  In particular, this extension is forced whenever the time ray
   is central in `M`.

### Proof

Apply Theorem X to the restricted ray to obtain item 1.  Both `b` and
`g -> pi(g)eta-eta` satisfy `(I.150)`, so their difference is a cocycle.  Item 1 makes that
difference zero on every `r(V)`, proving item 2.

Expanding the commutator difference by `(I.150)` gives

\[
 \begin{aligned}
 b(r(V)g)-b(gr(V))
 &=b(r(V))+\pi(r(V))b(g)\\
 &\quad-b(g)-\pi(g)b(r(V)).
 \end{aligned}
\tag{I.155}
\]

The second term tends to zero because `b(g) in H`; the other terms converge by `(I.151)` and
continuity of `pi(g)`.  The limit is

\[
 \ell-b(g)-\pi(g)\ell=-\mathfrak R_b(g),
\tag{I.156}
\]

which proves item 3.  By definition, `R_b=0` exactly when the same `eta` trivializes `b` on all of
`M`; it is already stable along the source ray.  If the ray is central, the expression inside the
limit in `(I.154)` is identically zero. `QED`

### Corollary (left--right terminal chirality)

For every source operation `g`,

\[
 \mathfrak R_b(gr(V))=\mathfrak R_b(g),
 \qquad
 \mathfrak R_b(r(V)g)=\pi(r(V))\mathfrak R_b(g).
\tag{I.157}
\]

Apply the cocycle law for `R_b` and use `R_b(r(V))=0`.  If `R_b(g)` lies in `H`, the first
ordering preserves the residue for all future time while the second drives it to zero.  This is an
exact causal asymmetry, not a chosen orientation convention.  It disappears when time is central,
because then the two products agree and strong stability forces the `H`-valued residue to vanish.

### Universal principle exposed

Terminal exactness separates time from geometry:

\[
 \text{radial source time}
 \xrightarrow{\text{stable primitive}}
 \text{endpoint}
 \quad+\quad
 \text{time--constraint noncommutation}
 \xrightarrow{(I.154)}
 \text{residual curvature}.
\tag{I.158}
\]

This gives a precise non-coherent extension of `(I.134)`: attach `R_b` as the source-curvature
face.  The finite-clock mismatch
`p_N T_(N+1)-T_N p_N` in `source-transgression-field.md` is structurally the same kind of
time--constraint commutator.  Theorem XVII does not prove that its actual HGT tower satisfies the
limit and representation hypotheses; it proves what the limit would mean and why a central clock
would kill it.

The failed `space-is-the-connected-part-of-time-conjecture.md` forbids claiming that temporal data
alone reconstruct physical space: subsystem composition is independent input.  Nothing here
evades that no-go.  `M`, its representation, and its source operations are supplied.  The valid new
statement is narrower: after those data are supplied, every residual failure of a convergent time
cocycle to trivialize globally is exactly a terminal commutator limit.

The algebra in `(I.155)` is elementary cocycle calculus and is not a novelty claim by itself.  Its
candidate significance is compression: coherent endpoint obstruction and noncommutative source
transgression become two faces of one terminal-exactness geometry.

## 33. A nonzero terminal-transgression cell in dimension two

`[PAPER-PROVED] [NON-COHERENT NONVACUITY MODEL]`

Let `M=R_+ * C_2` be the free product of the additive time monoid with the order-two generator `g`.
On `H=E=C^2`, put

\[
 \pi(r(t))=
 \begin{pmatrix}e^{-t}&0\\0&e^{-2t}\end{pmatrix},
 \qquad
 \pi(g)=
 \begin{pmatrix}0&1\\1&0\end{pmatrix}.
\tag{I.159}
\]

Let `e_1,e_2` be the standard basis.  Define a cocycle on the two free factors by

\[
 b(r(t))=(e^{-t}-1)e_1,
 \qquad b(g)=0,
\tag{I.160}
\]

and extend it to `M` by the cocycle law.

### Theorem XVIII (chiral terminal cell)

The data `(I.159)--(I.160)` define a valid `H`-valued cocycle.  Its time restriction has stable
primitive `eta=e_1`, but its terminal transgression is nonzero:

\[
 \mathfrak R_b(g)=e_1-e_2.
\tag{I.161}
\]

Moreover

\[
 \begin{aligned}
 b(r(t)g)-b(gr(t))
   &=(e^{-t}-1)(e_1-e_2)
     \longrightarrow-(e_1-e_2),\\
 \mathfrak R_b(gr(t))&=e_1-e_2,\\
 \mathfrak R_b(r(t)g)&=e^{-t}e_1-e^{-2t}e_2\longrightarrow0.
 \end{aligned}
\tag{I.162}
\]

### Proof

On the time factor,

\[
 (e^{-(t+s)}-1)e_1
 =(e^{-t}-1)e_1+\pi(r(t))(e^{-s}-1)e_1,
\tag{I.163}
\]

so `(I.160)` is a cocycle there.  On `C_2`, the only relation is `g^2=1`, and
`b(g)+pi(g)b(g)=0`; hence the free-product universal property extends the two factor cocycles
uniquely.

The radial limit is `-e_1`, so `eta=e_1`.  Since

\[
 \pi(g)\eta-\eta=e_2-e_1,
\tag{I.164}
\]

definition `(I.152)` gives `(I.161)`.  Expanding the two word orders gives the first line of
`(I.162)`, and the remaining lines are `(I.158)` evaluated using `(I.159)`. `QED`

This model proves that terminal transgression and its chirality are not forced to vanish, even in
finite dimension and even though `b(g)=0` before the time endpoint is used.  Noncommutation of the
anisotropic time representation with reflection creates the residue.  It is not an arithmetic
model; it is a minimal falsifier of the claim that Theorem XVII merely renames a coboundary.

## 34. Failed significance conjecture: terminal geometry alone is predictive

`[FALSIFIED] [POSITIVE SURVIVOR: SOURCE RELATIONS ARE ESSENTIAL]`

One might hope that the terminal residue and phase faces by themselves severely restrict possible
geometry.  They do not.

### Theorem XIX (free-source universality no-go)

Let `H` be any finite-dimensional complex Hilbert space, let `h_1,...,h_n in H` be arbitrary, and
let `eta in H`.  There exists a source monoid, a strongly stable representation, and an `H`-valued
cocycle whose radial stable primitive is `eta` and whose terminal transgression residues at
distinguished source generators are exactly the `h_j`.

Consequently every finite positive Gram configuration (after choosing `dim H` at least its rank)
and every Bargmann phase configuration realized by nonzero vectors can occur in terminal exactness
geometry before source relations are imposed.

### Proof

Let

\[
 M=\mathbb R_+*\mathbb F_n^+
\tag{I.165}
\]

be the free product of source time with the free monoid on generators `x_1,...,x_n`.  Represent it
on `H` by

\[
 \pi(r(t))=e^{-t}I,
 \qquad \pi(x_j)=I.
\tag{I.166}
\]

Define an auxiliary cocycle on the free factors by

\[
 R(r(t))=0,
 \qquad R(x_j)=h_j,
\tag{I.167}
\]

and extend uniquely over the free product.  Put

\[
 b(g)=\pi(g)\eta-\eta+R(g).
\tag{I.168}
\]

Then `b` is a cocycle,
`b(r(t))=(e^{-t}-1)eta -> -eta`, and `(I.152)` gives
`R_b(x_j)=h_j`.  Choosing the `h_j` to realize any prescribed finite Gram matrix gives its
pairwise overlaps and Bargmann products. `QED`

### No-go closure

- **Killed claim:** novelty of the representation object does not make arbitrary residue or phase
  data arithmetically restrictive.
- **Exact mechanism:** a free source monoid realizes every finite configuration.
- **Positive survivor:** predictive content can only come from relations already forced by the
  arithmetic source monoid, positivity/duality of its representation, and common-clock descent.
- **Research consequence:** never infer RH relevance from a beautiful terminal residue, horn, or
  phase alone.  Prove that source relations exclude the free realization.

Theorem XIX is why `(I.134)` is a geometry, not a solution.  Its value is to place previously
incomparable obstructions in one representation object and expose the exact missing source
relation.  It cannot manufacture that relation.

## 35. Cofinal-normalizer rigidity: which source relations kill geometry

`[PAPER-PROVED] [SOURCE-SELECTIVITY THEOREM]`

Let the hypotheses of Theorem XVII hold.  Fix `g in M` and any map
`phi:R_+ -> R_+` with `phi(V)->infinity`.

### Theorem XX (cofinal-normalizer rigidity)

The terminal residue obeys the reparametrized commutator formula

\[
 \mathfrak R_b(g)
 =-\lim_{V\to\infty}
 \left(b(r(V)g)-b(gr(\phi(V)))\right).
\tag{I.169}
\]

Consequently, if `g` cofinally normalizes future time,

\[
 r(V)g=gr(\phi(V))
 \quad\text{for all sufficiently large }V,
\tag{I.170}
\]

then `R_b(g)=0`.  The same conclusion holds if equality in `(I.170)` is weakened to convergence
of the cocycle difference in `(I.169)` to zero.

### Proof

The cocycle law gives

\[
 \begin{aligned}
 b(r(V)g)-b(gr(\phi(V)))
 &=b(r(V))+\pi(r(V))b(g)\\
 &\quad-b(g)-\pi(g)b(r(\phi(V))).
 \end{aligned}
\tag{I.171}
\]

The second term tends to zero by strong stability on `H`.  Both radial cocycle terms tend to
`ell`, the second because `phi(V)->infinity`.  The limit is therefore
`ell-b(g)-pi(g)ell=-R_b(g)`, proving `(I.169)` and both consequences. `QED`

### Exact survival criterion

A nonzero source-curvature face cannot be supported on an operation that merely rescales,
translates, or otherwise cofinally reparametrizes the same future ray.  It requires at least one of:

1. future time is sent to a different sector (reflection, another cusp, or another representation);
2. no cofinal normalizing relation exists;
3. the relation exists only with a nonzero asymptotic cocycle defect, which is exactly `-R_b(g)`.

This theorem explains several corpus failures without claiming a new arithmetic result.  The
orbitwise first-prime transport is a coboundary over an abelian translation action, so it lies in
the zero-residue regime.  Centered power transfers which genuinely normalize one future flow are
also terminally flat.  Candidate nonzero geometry must occur at source operations that exchange
inequivalent completions or leave a proved transgression defect.  This sharply reduces where an
arithmetic instantiation should be sought.

## 36. Curved terminal transgression: bulk two-curvature becomes boundary residue

`[PAPER-PROVED] [HIGHER UNIVERSAL PRINCIPLE]`

Theorem XX is too flat for several strongest corpus objects.  Let `b:M -> H` now be an arbitrary
continuous normalized one-cochain and define its curvature

\[
 \omega_b(g,h)
 =b(gh)-b(g)-\pi(g)b(h).
\tag{I.172}
\]

Associativity forces the Bianchi identity

\[
 \omega_b(g,h)+\omega_b(gh,k)
 =\pi(g)\omega_b(h,k)+\omega_b(g,hk).
\tag{I.173}
\]

Assume the time ray itself is flat,

\[
 \omega_b(r(V),r(W))=0,
\tag{I.174}
\]

and retain strong stability on `H` and radial convergence `b(r(V))->ell`.  As before put
`eta=-ell` and

\[
 \mathfrak R_b(g)=b(g)-(\pi(g)\eta-\eta).
\tag{I.175}
\]

### Theorem XXI (terminal curvature-flux law)

1. `eta` is the unique stable primitive on the time ray.
2. Subtracting that primitive does not change curvature:

   \[
   \omega_{\mathfrak R_b}=\omega_b,
   \qquad \mathfrak R_b(r(V))=0.
   \tag{I.176}
   \]

3. Let `phi(V)->infinity`.  If the indicated curvature difference has a limit in `E`, then

   \[
   \begin{aligned}
   \mathfrak R_b(g)
   &=-\lim_{V\to\infty}
      \bigl(b(r(V)g)-b(gr(\phi(V)))\bigr)\\
   &\quad+\lim_{V\to\infty}
      \bigl(\omega_b(r(V),g)-\omega_b(g,r(\phi(V)))\bigr).
   \end{aligned}
   \tag{I.177}
   \]

4. In particular, if `g` cofinally normalizes time as in `(I.170)`, then

   \[
   \mathfrak R_b(g)
   =\lim_{V\to\infty}
      \bigl(\omega_b(r(V),g)-\omega_b(g,r(\phi(V)))\bigr).
   \tag{I.178}
   \]

Thus a flat cofinal normalizer has zero terminal geometry, while a curved one exports exactly its
oriented bulk two-curvature imbalance to the terminal face.

### Proof

Expanding `b(ghk)` first as `(gh)k` and then as `g(hk)` proves `(I.173)` by cancellation.
Assumptions `(I.174)` and radial convergence give item 1 by the proof of Theorem X.  A
coboundary has zero curvature, so replacing `b` by `b-delta eta` preserves `(I.172)` and makes the
time restriction zero.  This proves item 2.

For item 3, use `(I.172)` twice:

\[
 \begin{aligned}
 b(r(V)g)-b(gr(\phi(V)))
 &=b(r(V))+\pi(r(V))b(g)+\omega_b(r(V),g)\\
 &\quad-b(g)-\pi(g)b(r(\phi(V)))
       -\omega_b(g,r(\phi(V))).
 \end{aligned}
\tag{I.179}
\]

The four non-curvature terms have limit `-R_b(g)` exactly as in Theorem XX.  Moving the curvature
limit to the other side gives `(I.177)`.  Under the monoid relation `(I.170)`, the first limit in
`(I.177)` is zero, proving `(I.178)`. `QED`

### Why this is the higher principle rather than another analogy

Equation `(I.178)` is a dependency-closed bulk--boundary theorem.  It says which part of curved
source data survives completion: not arbitrary connection coefficients, and not curvature declared
to vanish, but the oriented difference between pushing the constraint through future time on the
two sides.

It exactly extends the flat hierarchy:

\[
 \begin{array}{c|c}
 \omega_b=0 & \text{cofinal normalizer forces }\mathfrak R_b=0\\
 \omega_b\ne0 & \text{terminal residue equals curvature flux `(I.178)`}
 \end{array}
\tag{I.180}
\]

The Route-R prime/depth differential has a proved nonzero two-simplex curvature and the full-prime
conditioning nerve has proved higher curvature.  Theorem XXI supplies their correct target type.
An actual arithmetic instantiation still requires constructing `M,pi,b,r` and proving the cofinal
limit in `(I.178)` from those source objects.  Declaring the finite witness itself to be that limit
would be theatre.

This also sharpens the holographic metaphor: the fixed terminal face is not assumed to encode the
bulk.  When `(I.178)` holds, its residue is *proved* to be the boundary value of an oriented bulk
curvature flux.

## 37. Full stable-primitive cohomology and the obstruction ladder

`[PAPER-PROVED] [HOSTILE DEFINITION CORRECTION]`

Definition `(I.97)` deliberately used only externally trivial cocycles `C_E=delta(E_H)`.  Calling
that quotient the whole terminal cohomology was too broad.  It is the **external terminal kernel**.
The full degree-one object is as follows.

Let `C^bullet(M,E)` be the inhomogeneous bar complex, let `Z^1=ker d`, let
`B^1=dE`, let `F=ker(d:E->C^1)`, and let

\[
 S=\{\eta\in E:\pi(r(V))\eta\longrightarrow0\}.
\tag{I.181}
\]

Define **stable-primitive cohomology** by

\[
 \mathbb H^1_\infty(M,E;r)=Z^1/dS.
\tag{I.182}
\]

### Theorem XXII (stable-primitive exact sequence)

There is a canonical short exact sequence

\[
 0\longrightarrow {E\over S+F}
 \xrightarrow{\ \bar d\ }
 \mathbb H^1_\infty(M,E;r)
 \longrightarrow H^1(M,E)
 \longrightarrow0.
\tag{I.183}
\]

For any one-cochain `b`, a forward-stable primitive `eta in S` with `b=d eta` exists if and only
if all three successive obstructions vanish:

1. **curvature gate:** `db=0`;
2. **cohomology gate:** `[b]=0` in ordinary `H^1(M,E)`;
3. **terminal gate:** for one, hence every, primitive `xi` with `b=d xi`,

   \[
   [\xi]=0\quad\text{in }E/(S+F).
   \tag{I.184}
   \]

### Proof

The natural quotient map `Z^1/dS -> Z^1/dE=H^1(M,E)` is surjective.  Its kernel is `dE/dS`.
The map

\[
 E/(S+F)\longrightarrow dE/dS,
 \qquad [\xi]\longmapsto[d\xi]
\tag{I.185}
\]

is well-defined and surjective.  Its kernel is zero: if `d xi=d eta` for some `eta in S`, then
`xi-eta in F`, so `xi in S+F`.  This proves `(I.183)`.

If `b=d eta` with `eta` stable, all three conditions are immediate.  Conversely, gate 1 makes
`b` a cocycle, gate 2 supplies `xi` with `b=d xi`, and gate 3 writes `xi=eta+f` with `eta in S`
and `f in F`.  Then `b=d eta`.  If `xi'` is another primitive, `xi'-xi in F`, so `(I.184)` is
independent of the choice. `QED`

### Exact placement of the preceding theorems

- Theorem XXI's curved source differential fails gate 1; its positive survivor is curvature flux.
- A genuine nonzero affine cohomology class passes gate 1 but fails gate 2.
- Failed conjecture IX.0 passes gates 1 and 2 in every distributional grade but fails gate 3 until
  the exactness cut is crossed.
- The quotient `(I.97)` is the gate-3 kernel `dE/dS`, with the additional requirement that
  coboundaries take values in the declared Hilbert core.

This correction produces a representation object capable of distinguishing three obstructions
which ordinary cohomology conflates or discards.  After all three vanish, the terminal nerve adds
the independent common-clock horn gate.  On a filled two-face, `Omega` is then a derived
orientation observable rather than another vanishing gate.  The complete obstruction ladder is
therefore

\[
 \boxed{\text{curvature}}
 \longrightarrow
 \boxed{H^1\text{ class}}
 \longrightarrow
 \boxed{\text{stable-primitive class}}
 \longrightarrow
 \boxed{\text{synchrony horn}}
 \dashrightarrow
 \boxed{\text{derived phase on a filler}}.
\tag{I.186}
\]

This is the current higher universal principle: repeated HGT failures occur at different gates of
one exactness geometry, so forcing all of them into positivity, a Hilbert completion, or ordinary
cohomology necessarily erases the information carried by the later gates.

The exact sequence `(I.183)` is elementary relative-cohomology algebra; no novelty is claimed for
the quotient argument.  Candidate new knowledge is the forward-stable choice of allowed
primitives, its equivalence with endpoint formation, and the placement of source curvature,
observer cuts, synchronized Gram horns, and phase in one obstruction ladder.

## 38. Minimal nonzero curvature-flux cell

`[PAPER-PROVED] [CURVED NONVACUITY MODEL]`

Let `M=R_+ x C_2`, with central involution `g`, and let `H=E=C`.  Represent

\[
 \pi(r(t))=e^{-t},
 \qquad \pi(g)=-1.
\tag{I.187}
\]

Define the normalized one-cochain on the two connected components by

\[
 b(r(t))=e^{-t}-1,
 \qquad b(r(t)g)=0.
\tag{I.188}
\]

### Theorem XXIII (central curved residue)

The time restriction of `b` is flat and has stable primitive `eta=1`.  Although time and `g`
commute in `M`,

\[
 \mathfrak R_b(g)=2.
\tag{I.189}
\]

The two oriented curvature faces are

\[
 \omega_b(r(t),g)=1-e^{-t},
 \qquad
 \omega_b(g,r(t))=e^{-t}-1,
\tag{I.190}
\]

and therefore

\[
 \mathfrak R_b(g)
 =\lim_{t\to\infty}
   \left(\omega_b(r(t),g)-\omega_b(g,r(t))\right)=2.
\tag{I.191}
\]

### Proof

The radial identity

\[
 e^{-(t+s)}-1=(e^{-t}-1)+e^{-t}(e^{-s}-1)
\tag{I.192}
\]

proves flatness and the limit is `-1`.  Since `b(g)=0` and
`pi(g)eta-eta=-2`, definition `(I.175)` gives `(I.189)`.  Substitution into `(I.172)` gives
`(I.190)`, and `(I.191)` follows. `QED`

This cell separates the flat and curved theories with no analytic distraction.  Centrality kills
terminal transgression only after gate 1 has passed.  When curvature is present, the terminal face
records its oriented flux exactly as Theorem XXI states.

## 39. Cone-time geometry: polyhedral horizons and holographic corner faces

`[PAPER-PROVED] [MULTI-TIME GEOMETRY]`

A single future ray cannot model a prime--depth or place--scale source.  Let `d>=1`, let
`beta_j>-2`, and put

\[
 H_{\boldsymbol\beta}
 =L^2\!\left((0,1)^d,
   c\prod_{j=1}^d s_j^{\beta_j-1}\,d\mathbf s\right).
\tag{I.193}
\]

Let the commuting source times act by

\[
 (T^{(j)}_{V_j}f)(\mathbf s)=e^{-V_js_j}f(\mathbf s).
\tag{I.194}
\]

For the formal source `xi=1`, its degree-`d` cubical coboundary is

\[
 b_{\mathbf V}
 =\prod_{j=1}^d(T^{(j)}_{V_j}-I)\xi
 =\prod_{j=1}^d(e^{-V_js_j}-1).
\tag{I.195}
\]

For `rho in R^d`, use the observer

\[
 \Phi_{\boldsymbol\rho}
 =\left(\prod_{j=1}^d s_j^{\rho_j}\right)C^\infty([0,1]^d),
\tag{I.196}
\]

with transported smooth topology.  Call a primitive **face-stable** when every nonempty partial
product of its time semigroups tends to zero as the corresponding coordinates tend cofinally to
infinity.  This is the multi-time condition needed for all faces of `(I.195)` to have one endpoint.

### Theorem XXIV (cubical exactness-cut law)

1. `b_V` belongs to `H_beta` for every finite `V`.
2. The admissible observer region and terminal death region are the open polyhedra

   \[
   \begin{aligned}
   \mathcal O_{\boldsymbol\beta}
   &=\{\boldsymbol\rho:2\rho_j+\beta_j>0\ \forall j\},\\
   D_{\boldsymbol\beta}
   &=\{\boldsymbol\rho\in\mathcal O_{\boldsymbol\beta}:
        \rho_j+\beta_j>0\ \forall j\}.
   \end{aligned}
   \tag{I.197}
   \]

   At every admissible observer the corner cochain is an iterated finite-part coboundary.  It has
   a face-stable primitive exactly on `D_beta`.
3. For a subset `J subset {1,...,d}`, the common fixed face of the times in `J` is

   \[
   F_J
   =\delta_{\{s_j=0:j\in J\}}
      \widehat\otimes
      \mathcal D'([0,1]^{J^c}).
   \tag{I.198}
   \]

   Thus fixed faces form the Boolean face lattice of a `d`-corner; the deepest holographic stratum
   is the line `C delta_0` at `s_1=...=s_d=0`.
4. Let `a_j=rho_j+beta_j`, assume `a_j in (-1,infinity)\{0}`, and define, under the identifications
   `f=(prod_j s_j^rho_j)h`,

   \[
   \eta_{\mathbf a}
   =c\bigotimes_{j=1}^d\operatorname {Fp}(s_j^{a_j-1}),
   \]

   where `Fp` is the coefficient-one ordinary integral for `a_j>0` and the coefficient-one version
   of extension `(I.109)` for `-1<a_j<0`.
   For complex times
   `z_j=R_j e^(i theta_j)` in closed decay subsectors,

   \[
   \left(\prod_{j=1}^dR_j^{a_j}\right)
   T_{\mathbf z}\eta_{\mathbf a}
   \longrightarrow
   c\left(\prod_{j=1}^d\Gamma(a_j)e^{-ia_j\theta_j}\right)\delta_0.
   \tag{I.199}
   \]

   On every deficient coordinate, the angular phase covector is the inward conormal distance to
   the corresponding death face:

   \[
   \partial_{\theta_j}\arg q_{\mathbf a}
   =-a_j=\mathfrak d_{\beta_j}-\rho_j.
   \tag{I.200}
   \]

   A coordinate with `a_j=0` has the logarithmic contact law `(I.142)` instead.

### Proof

The squared norm of `(I.195)` factorizes into `d` one-dimensional integrals

\[
 \lVert b_{\mathbf V}\rVert^2
 =c\prod_{j=1}^d
   \int_0^1|e^{-V_js}-1|^2s^{\beta_j-1}\,ds,
\tag{I.201}
\]

each finite exactly because `beta_j>-2`.  This proves item 1.

For `f=(prod s_j^rho_j)h`, boundedness of `h` and Fubini show `f in H_beta` for every smooth `h`
exactly when each exponent `2rho_j+beta_j-1` is greater than `-1`; necessity follows by choosing a
product test supported away from every other coordinate face.  This proves the first line of
`(I.197)`.

Put `a_j=rho_j+beta_j`.  Admissibility and `beta_j>-2` imply `a_j>-1`.  The explicitly normalized
tensor distribution above is continuous and is a primitive of `(I.195)`: multiplication by every
`e^{-V_js_j}-1=O(s_j)` turns the corresponding finite-part factor into an ordinary integral.  If
every `a_j>0`, then for each nonempty `J` the partial orbit
`(prod_(j in J)T^(j)_(V_j))eta_a` tends to zero, by one-dimensional dominated convergence in any
one factor and equicontinuity of the remaining tensor factors.

Conversely, suppose `a_k<=0`.  Face stability includes the singleton face `J={k}`.  Choose a
factorized test whose factors away from `k` pair nontrivially with their fixed source distributions
and are supported away from every other coordinate face; take the `k`-th factor to be the constant
test in the transported `C^infty` chart.  Its pairing with `T^(k)_(V_k)eta_a` is a nonzero fixed
scalar times the power or logarithmic coefficient in `(I.111)--(I.112)`, and therefore diverges.

This divergence is primitive-independent.  If `eta'` is another primitive, then for one fixed
positive time tuple the difference `u=eta'-eta_a` is killed by
`prod_j(e^(-V_js_j)-1)`, hence by `prod_j s_j`, because the quotient is smooth and nowhere zero.
On the support of the chosen test all `s_j` with `j!=k` are invertible, so `s_k u=0` there.  Thus
`T^(k)_(V_k)u=u` on that test: it contributes a constant and cannot cancel the divergent
coefficient.  Hence no primitive of `(I.195)` is face-stable.  This proves item 2.

If a distribution `u` is fixed by `T^(j)` for all times, the invertibility argument in Theorem XI
gives `s_j u=0`.  A distribution killed by multiplication by `s_j` is a delta in that coordinate
with an arbitrary distribution in the others.  Iterating over `J` proves `(I.198)`.

Finally the source distribution and semigroup are tensor products.  Applying the uniform
one-dimensional sectorial asymptotic `(I.140)` in each coordinate proves `(I.199)`.  Its phase is
`-sum_j a_j theta_j` up to a constant.  In a deficient coordinate
`d_(beta_j)=-beta_j`, giving `(I.200)`. `QED`

### Geometry produced

Exactness-cut topology is now genuinely higher-dimensional.  Horizons are polyhedral frontiers in
observer capability; intersections of their faces are fixed distributional strata; complex-time
phase is a conormal covector to those fronts.  A throat between source sectors is a synchronized
simplex crossing several faces, not a curve between pre-existing boundary points.

Product measures, tensor-product distributions, cubical coboundaries, and orthant persistence are
standard parents.  Candidate new content is their integration with stable-primitive endpoint
geometry and the phase--conormal identity `(I.200)`.  The exact prime--depth Stokes density in
`source-localization-modular-defect-conservation-law.md` is a strong internal parent: it already
proves that a locally exact bilinear primitive can exit the critical bornology and leave a mixed
cofinal boundary record.  Theorem XXIV generalizes the *type* of that phenomenon; it does not claim
priority over the arithmetic example or identify its density with `(I.199)` without a source map.

## 40. Stable-primitive geometry in every cohomological degree

`[PAPER-PROVED] [GRADED ALGEBRAIC ENVELOPE]`

Let `(C^bullet,d)` be any cochain complex carrying the source representation.  At observer `o`, let
`S_o^(n-1) subset C^(n-1)` be the declared subspace of primitives which vanish cofinally on every
required source face.  Define

\[
 \mathbb H^n_{\infty,o}(C)
 ={Z^n(C)\over dS_o^{n-1}},
 \qquad Z^n(C)=\ker(d:C^n\to C^{n+1}).
\tag{I.202}
\]

### Theorem XXV (stable-primitive exact sequence)

For every `n>=1`, there is a canonical short exact sequence

\[
 0\longrightarrow
 {C^{n-1}\over S_o^{n-1}+Z^{n-1}}
 \xrightarrow{\ \bar d\ }
 \mathbb H^n_{\infty,o}(C)
 \longrightarrow H^n(C)
 \longrightarrow0.
\tag{I.203}
\]

An `n`-cochain `c` has a stable `(n-1)`-primitive exactly when the following gates vanish in order:

\[
 dc=0,
 \qquad [c]_{H^n}=0,
 \qquad [a]=0\text{ in }C^{n-1}/(S_o^{n-1}+Z^{n-1}),
\tag{I.204}
\]

where `c=da` after the second gate.

### Proof

The quotient map `Z^n/dS -> Z^n/dC^(n-1)=H^n(C)` is surjective and has kernel
`dC^(n-1)/dS`.  The map

\[
 C^{n-1}/(S+Z^{n-1})\longrightarrow dC^{n-1}/dS,
 \qquad[a]\longmapsto[da]
\tag{I.205}
\]

is an isomorphism by the same kernel calculation as `(I.185)`.  This proves `(I.203)`.
The three-gate statement follows exactly as in Theorem XXII. `QED`

### Why degree matters

This theorem separates two objects that the corpus repeatedly warns not to confuse:

1. a genuine nonzero `H^2` curvature class, which fails the ordinary cohomology gate;
2. a locally exact two-cochain whose primitive exits the critical observer bornology, which passes
   ordinary `H^2` but survives in the left kernel of `(I.203)`.

The exact mixed prime--depth Stokes density is of the second *type*; the full-prime conditioning
nerve curvature can be of the first.  A source construction must decide which by specifying
`C^bullet` and `S_o^bullet`.  Merely naming both `curvature` loses the distinction.

The graded algebraic spine of interfinity geometry is therefore the observer-filtered tower

\[
 \left\{\mathbb H^n_{\infty,o}(C)\right\}_{n\ge1,\ o\in\mathcal O},
\tag{I.206}
\]

augmented by the Gram-labelled terminal nerve and fixed-face residues; phase orientation is derived
from nondegenerate Gram-labelled two-faces.  The exact sequences are standard homological algebra.
New candidate is the geometric choice of
cofinally stable primitives and its proved links to endpoints, curvature flux, observer cuts, and
complex-time phase.

## 41. Exactness topology and the immortality law

`[PAPER-PROVED] [TOPOLOGY GENERATED BY SOLVABILITY]`

The tower in `(I.206)` becomes a topology only after its observer dependence is made structural.
Let `O` be a poset and assume that observer strengthening enlarges the allowed stable primitives:

\[
 o\le o'\quad\Longrightarrow\quad
 S_o^k\subseteq S_{o'}^k
 \qquad(k\ge0).
\tag{I.207}
\]

For an exact `n`-cochain `c`, define its **stable-solvability region**

\[
 D_n(c)
 =\{o\in\mathcal O:[c]_o=0\text{ in }\mathbb H^n_{\infty,o}\}.
\tag{I.208}
\]

Let `tau_ex^n` be the topology on `O` generated by all sets `D_n(c)` with `c in dC^(n-1)`, and
let `tau_ex` be the topology generated jointly over all degrees.  Its basic finite intersections
are regions where a finite family of source equations is simultaneously stably solvable.  They do
not assert one common source synchronization; that strictly stronger incidence is what the
Gram-labelled nerve records.

### Theorem XXVI (terminal persistence and immortality)

Under `(I.207)`:

1. for every `o<=o'` there is a canonical surjection

   \[
   q_{oo'}^n:\mathbb H^n_{\infty,o}\longrightarrow
   \mathbb H^n_{\infty,o'},
   \qquad
   0\longrightarrow {dS_{o'}^{n-1}\over dS_o^{n-1}}
   \longrightarrow\mathbb H^n_{\infty,o}
   \xrightarrow{q_{oo'}^n}\mathbb H^n_{\infty,o'}
   \longrightarrow0;
   \tag{I.209}
   \]

2. the quotient maps to ordinary cohomology commute with every `q_(oo')^n`.  Consequently a class
   with nonzero image in `H^n(C)` is **immortal**: no observer strengthening can kill it.  Every
   class killed by `q_(oo')^n` lies in the exact, primitive-instability sector;
3. if `c=da`, then

   \[
   D_n(c)=\{o:a\in S_o^{n-1}+Z^{n-1}\};
   \tag{I.210}
   \]

   this formula is independent of the primitive `a`, and `D_n(c)` is an upper set;
4. `tau_ex^n` and `tau_ex` are contained in the Alexandrov upper topology of `O`.  A filtered
   cochain isomorphism carrying `S_o^k` onto `S'_(theta(o))^k` for an order isomorphism `theta`
   carries every `D_n(c)` onto `D'_n(Uc)` and therefore induces a homeomorphism of exactness
   topologies.

Thus ordinary cohomology and terminal geometry occupy provably different persistence sectors:
ordinary classes cannot die, while an ordinary-exact class dies precisely when its affine space of
primitives first meets the observer's stable subspace.

### Proof

Inclusion `(I.207)` gives `dS_o^(n-1) subset dS_(o')^(n-1)`, so quotienting `Z^n` first by the
smaller and then by the larger subspace gives `q_(oo')^n`.  Its kernel is exactly the displayed
quotient in `(I.209)`, and it is surjective.  The map to `H^n=Z^n/dC^(n-1)` forgets which
primitives were allowed, so it is unchanged by this further quotient.  A class which dies is
therefore represented by an ordinary coboundary.  This proves items 1 and 2.

For `c=da`, its class vanishes at `o` exactly when `da=ds` for some `s in S_o^(n-1)`, equivalently
`a-s in Z^(n-1)`.  This is `(I.210)`.  Replacing `a` by another primitive changes it by an element
of `Z^(n-1)`, and inclusion `(I.207)` makes the displayed set upward closed.  A topology generated
by upper sets is contained in the upper Alexandrov topology.  Finally a filtered cochain
isomorphism preserves `d`, cocycles, and stable subspaces, so it preserves `(I.210)` exactly.  This
proves items 3 and 4. `QED`

### What is genuinely added

Persistent cohomology, filtered homotopy, reduced cohomology, bounded primitives, and regularity
thresholds for cohomological equations are established theories.  Theorem XXVI does not rename
their invariants.  It proves a different division forced by the endpoint problem: ordinary
cohomology is the observer-immortal quotient, whereas observer topology is generated solely by
where ordinary-exact equations acquire *forward-stable* primitives.  The terminal nerve then
detects failure of joint synchronization inside finite intersections of those solvability opens.
This is the first point in the construction where topology, cohomology, and higher incidence have
nonredundant exact roles.

## 42. Arithmetic realization: one class, three noncoherent charts

`[PAPER-PROVED] [SOURCE-PURE ARITHMETIC INSTANTIATION] [NOT RH]`

The abstract geometry now has a noncoherent HGT realization.  Fix the base prime `p_0=2`.  For a
real function `f` on `P x N_0`, define its based mixed rectangle and, when the limit exists, its
mixed area rate by

\[
 \begin{aligned}
 B_{P,M}f
 &=f(P,M)-f(P,0)-f(2,M)+f(2,0),\\
 q(f)
 &=\lim_{\substack{P\to\infty\\M\to\infty}}
   {B_{P,M}f\over(\log P-\log2)M}.
 \end{aligned}
\tag{I.211}
\]

Let `R` be the vector space of functions for which this finite limit exists and which satisfy the
source-regularity condition `B_(p,M)f=O_p(M)` for every fixed prime `p`.  This condition is
invariant under separated gauges and is obeyed by the source logarithmic intensities below.
Predeclare the critical mixed bornology

\[
 \mathcal S=\ker q
 =\{f\in\mathcal R:B_{P,M}f=o((\log P-\log2)M)\}.
\tag{I.212}
\]

This definition is source-only: it uses prime and depth clocks, not a zero, divisor, or desired
vanishing.  Define the full rectangular difference

\[
 (Df)(p,q;m,n)
 =f(p,m)-f(p,n)-f(q,m)+f(q,n),
\tag{I.213}
\]

and the two-term radial mixed complex

\[
 C^1_{\rm rad}=\mathcal R,
 \qquad C^2_{\rm rad}=D\mathcal R,
 \qquad d=D,
 \qquad C^3_{\rm rad}=0.
\tag{I.214}
\]

Thus every radial mixed two-cochain is ordinarily exact by construction; the question is whether
it has a primitive in the critical bornology `(I.212)`.

### Theorem XXVII (three-chart stable-boundary identification)

1. Mixed area rate is unchanged if the base prime `2` in `(I.211)` is replaced by any fixed prime.
   It induces a canonical isomorphism

   \[
   \bar q:
   \mathbb H^2_{\infty}(C_{\rm rad})
   ={D\mathcal R\over D\mathcal S}
   \xrightarrow{\ \cong\ }\mathbb R,
   \qquad [Df]\longmapsto q(f),
   \tag{I.215}
   \]

   while ordinary `H^2(C_rad)=0`.
2. For every `s` in the domain of the source charts, the gauge-reduced prime--depth logarithmic
   intensity from the source localization law,

   \[
   \ell_s(p,m)=(1-2\operatorname {Re}s)m\log p,
   \tag{I.216}
   \]

   defines a class whose coordinate is

   \[
   \bar q([D\ell_s])=1-2\operatorname {Re}s.
   \tag{I.217}
   \]

3. The same coordinate is recovered exactly from two other independently constructed HGT charts.
   Let the Sonin relative determinant torsion be
   `tau_r(s)=r^(2 Re(s)-1)`.  Let `Hol_R(s)` be the positive Route-R BV--Wold transport holonomy on
   the ordered cells `(2,0),(2,1),(2,2)`, using its uniform centered parameter
   `a_s^R=2 Re(s)-1`; explicitly, with `i_e=(2,e)`,

   \[
   \operatorname {Hol}_R(s)
   ={U_{a_s^R}(i_0,i_1)U_{a_s^R}(i_1,i_2)
     \over U_{a_s^R}(i_0,i_2)}.
   \]

   Then, for every `r>1`,

   \[
   \boxed{
   \bar q([D\ell_s])
   =-{\log\tau_r(s)\over\log r}
   ={8\over\log2}\log\operatorname {Hol}_{R}(s).
   }
   \tag{I.218}
   \]

4. Reflection `s -> 1-conj(s)` negates this class.  The class vanishes exactly on
   `Re(s)=1/2`.

### Proof

Let `q_b` denote `(I.211)` with fixed base prime `b`.  Direct subtraction gives

\[
 B^{b}_{P,M}f=B^{2}_{P,M}f-B^{2}_{b,M}f.
\]

The second term is `O_b(M)`, while either denominator is asymptotic to `M log P`; the ratio of the
two denominators tends to one.  Hence `q_b(f)=q_2(f)`.  This proves base-prime independence.

If `Dh=0`, apply `(I.213)` with `q=2` and `n=0` to get

\[
 h(p,m)=h(p,0)+h(2,m)-h(2,0).
\tag{I.219}
\]

Hence `B_(P,M)h=0` and `q(h)=0`.  Therefore `(I.215)` is well-defined.  It is surjective because
`f_a(p,m)=a m log p` has `q(f_a)=a`.  If `[Df]` is in its kernel, then `q(f)=0`, so `f in S` and
`[Df]=0`.  Conversely every `D S` maps to zero.  Thus `(I.215)` is an isomorphism.  Since
`C_rad^2=D R` and `C_rad^3=0`, ordinary `H^2` is zero.  This proves item 1.

Substitution of `(I.216)` into `(I.211)` gives `(I.217)` exactly.  The Sonin identity follows from

\[
 \log\tau_r(s)=(2\operatorname {Re}s-1)\log r.
\tag{I.220}
\]

For the Route-R cells, the proved oriented triangle sum is

\[
 \theta(2,0;2,1)+\theta(2,1;2,2)-\theta(2,0;2,2)
 =-{log2\over8}.
\tag{I.221}
\]

Since Route-R transport is `U=exp(a_s^R theta)` and
`a_s^R=-(1-2 Re(s))`, its triangle holonomy satisfies

\[
 \log\operatorname {Hol}_{R}(s)
 ={\log2\over8}(1-2\operatorname {Re}s).
\tag{I.222}
\]

Equations `(I.217)`, `(I.220)`, and `(I.222)` prove `(I.218)`.  Finally
`1-2 Re(1-conj(s))=-(1-2 Re(s))`, and this real number is zero exactly on the critical line.
`QED`

### What this closes—and what it cannot close

This is not the still-missing full source module provisionally called `H^2_mod(zeta)` in the
localization program.  It is its dependency-closed one-dimensional radial mixed sector.  It
constructs the controlled quotient instead of naming it, proves that its nonzero class is an
ordinary-exact primitive escaping a predeclared source bornology, and identifies three corpus
realizations without choosing a zero.  At an actual Xi conormal, the class detects horizontal
displacement.  Nothing here forces it to vanish; such a theorem would contain the RH-bearing
source-dagger/Stokes assertion and remains open.

The gain is nevertheless structural.  Prime--depth boundary escape, flat Sonin relative torsion,
and nonflat BV--Wold triangle transport looked like incompatible obstruction types.  They factor
through one stable-primitive class, while their different local geometries become three readers of
that class.  This is the first proved noncoherent arithmetic source functor into `(I.134)`.

## 43. Scott realization: observers are subspaces of solvable equations

`[PAPER-PROVED] [POINT-FREE TOPOLOGICAL REPRESENTATION]`

The exactness topology of Section 41 has a canonical ambient space.  Put

\[
 B^n=dC^{n-1},
 \qquad
 K_o^n=dS_o^{n-1}\subseteq B^n,
 \qquad
 \kappa_n(o)=K_o^n.
\tag{I.223}
\]

Thus `K_o^n` is not a set of points visible to observer `o`; it is the linear space of source
equations which that observer can solve with a stable primitive.  Order `Sub(B^n)` by inclusion and
give it the Scott topology.

### Theorem XXVIII (Sierpinski--Scott representation)

For every degree `n`:

1. The sets

   \[
   U_c=\{K\in\operatorname {Sub}(B^n):c\in K\},
   \qquad c\in B^n,
   \tag{I.224}
   \]

   are Scott-open.  Their finite intersections, equivalently the sets
   `U_F={K:F subset K}` for finite-dimensional `F subset B^n`, form a basis of the Scott topology.
2. The stable-exactness topology is exactly the pullback topology

   \[
   \tau_{\rm ex}^n=\kappa_n^{-1}\tau_{\rm Scott},
   \qquad
   D_n(c)=\kappa_n^{-1}(U_c).
   \tag{I.225}
   \]

3. Equivalently, let `S={0,1}` be Sierpinski space with `{1}` open and define the solvability
   profile

   \[
   e_n:\mathcal O\longrightarrow\mathbb S^{B^n},
   \qquad
   e_n(o)(c)=1\Longleftrightarrow c\in K_o^n.
   \tag{I.226}
   \]

   Then `tau_ex^n` is the initial topology of `e_n`.  Jointly over all degrees, `tau_ex` is the
   initial topology of `prod_n e_n`.
4. The `T_0` reflection of the all-degree observer space identifies exactly those observers with

   \[
   K_o^n=K_{o'}^n\qquad\text{for every }n.
   \tag{I.227}
   \]

   Its observable specialization preorder is

   \[
   o\preceq_{\rm ex}o'
   \Longleftrightarrow
   K_o^n\subseteq K_{o'}^n\quad\text{for every }n.
   \tag{I.228}
   \]

Hence the actual points of interfinity topology are solvability profiles, and observer
strengthening is inclusion of stable-coboundary subspaces.

### Proof

The set `U_c` is upward closed.  If a directed family of subspaces has union containing `c`, then
`c` lies in one member of the family; directed unions are their suprema in `Sub(B^n)`.  Therefore
`U_c` is Scott-open.  A finite intersection of membership opens says that a finite list of vectors,
hence its finite-dimensional span `F`, is contained in `K`.

Conversely, the lattice of subspaces is algebraic.  Every subspace is the directed union of its
finite-dimensional subspaces, and a finite-dimensional subspace is compact: if it is contained in
a directed union, a finite basis is contained in finitely many members and directedness puts the
whole basis in one member.  The upper sets generated by compact elements are therefore a Scott
basis.  This proves item 1.

By definition, an exact cochain `c` dies at `o` exactly when `c in dS_o^(n-1)=K_o^n`.  Thus
`D_n(c)=kappa_n^(-1)(U_c)`.  Since the membership opens generate the Scott topology, their
pullbacks generate exactly `tau_ex^n`, proving item 2.

Coordinate projection to `c` in the Sierpinski product has `{1}` as its basic open preimage.
Equation `(I.226)` pulls that set back to `D_n(c)`, proving the initial-topology statement.  Two
observers are topologically indistinguishable precisely when every such membership predicate has
the same truth value, which is `(I.227)`.  Finally, every solvability open containing `o` also
contains `o'` exactly when every vector in every `K_o^n` lies in `K_(o')^n`.  This is `(I.228)`.
`QED`

### Consequence for the geometry

This theorem removes the last dependence on a pre-existing point set.  The geometry can be
constructed in the order

\[
 \text{source equations}
 \longrightarrow
 \text{stable-coboundary subspaces}
 \longrightarrow
 \text{Scott solvability space}
 \longrightarrow
 \text{Gram-labelled higher incidence}.
\tag{I.229}
\]

The Scott space records every finite family which is individually solvable at one observer.  It
still cannot decide whether their endpoints admit one common source synchronization; Theorem XIV's
nonfillable horn proves that the terminal nerve is strictly additional structure.

Scott topology, algebraic lattices, Sierpinski classifiers, and initial topologies are established
parents.  Candidate-new knowledge is the representation theorem `(I.225)--(I.229)` for
forward-stable source equations and its exact separation from the synchronized terminal nerve.

## 44. Higher incidence is not reconstructible from topology and edges

`[PAPER-PROVED] [STRICT TWO-LAYER GEOMETRY]`

The parity horn proves one missing filler, but a stronger hostile question remains: perhaps the
Scott exactness space together with the *entire Gram-labelled one-skeleton* determines every higher
simplex.  It does not.

### Theorem XXIX (same solvability space and one-skeleton, different two-geometry)

There exist two interfinity systems with:

1. the same singleton observer space and the same stable-coboundary subspaces in every degree;
2. the same three terminal vertices `A,B,C`;
3. exactly the same Gram-labelled edges between every pair of those vertices;
4. different Gram-labelled two-simplices.

Consequently neither exactness topology nor its enrichment by all pairwise transition data
determines the terminal nerve.

### Proof

Give every label the zero cocycle, so every vertex is terminal and both systems have identical
Scott solvability data.  Let `H=C^3`, let `A_n=e_1`, and put

\[
 h={1\over2}e_1+{\sqrt3\over2}e_2.
\tag{I.230}
\]

In system `X`, use the two periodic states

\[
 (B_n,C_n)=
 \begin{cases}
 (h,e_3),&n\text{ even},\\
 (e_3,h),&n\text{ odd}.
 \end{cases}
\tag{I.231}
\]

Its limiting edge labels are exactly

\[
 g_{AB}\in\{0,1/2\},
 \qquad g_{AC}\in\{0,1/2\},
 \qquad g_{BC}=0.
\tag{I.232}
\]

A convergent synchronization must eventually select one value of each discrete overlap.  Hence
the only triangle Gram matrices in `X` are the even and odd ones; the matrix

\[
 G=\begin{pmatrix}
 1&1/2&1/2\\
 1/2&1&0\\
 1/2&0&1
 \end{pmatrix}
\tag{I.233}
\]

is not realized.

In system `Y`, retain the even state of `(I.231)` on `n=1 mod 3`, retain the odd state on
`n=2 mod 3`, and on `n=0 mod 3` put

\[
 B_n=h,
 \qquad
 C_n={1\over2}e_1-{1\over2\sqrt3}e_2+\sqrt{2\over3}e_3.
\tag{I.234}
\]

The last vector has norm one, inner product `1/2` with `A_n`, and inner product zero with `B_n`.
Thus the `0 mod 3` synchronization realizes `(I.233)`.  Across all three residue classes, the
possible `AB`, `AC`, and `BC` edge limits are still exactly `(I.232)`.  Therefore `X` and `Y` have
identical Gram-labelled one-skeleta, but `Y` contains the `G`-labelled two-simplex and `X` does
not. `QED`

### Consequence

Interfinity geometry has two irreducible layers:

\[
 \boxed{\text{Scott space of individually solvable equations}}
 \quad+\quad
 \boxed{\text{source-synchronous higher nerve}}.
\tag{I.235}
\]

No topology on vertices, no pairwise positive kernel, and no complete labelled graph recovers the
second box.  The missing datum is genuinely joint source time.

## 45. Hostile truth, novelty, and significance verdict

`[INTERNAL REVIEW COMPLETE 2026-08-08] [EXTERNAL PRIORITY UNVERIFIED]`

### Claims killed or demoted

The conjecture--proof--failure loop materially changed the object.  The following statements are
not part of the surviving claim:

1. **Phase/Fock geometry is the new ontology — killed by corpus and literature collision.**
   Coherent states, inequivalent representations, projective metrics, and Bargmann phases are
   parents.
2. **Filtered endpoint topology alone is new — killed.**  Pro-objects, persistence, filtered
   topology, regularity cuts, and observer-dependent completions are parents.
3. **Ordinary distributional cohomology locates the horizon — false.**  Finite-part primitives
   trivialize the model earlier; forward stability is the missing condition.
4. **Existence of all faces defines an abstract simplicial complex — false.**  A Gram label and its
   actual common synchronization must be retained, giving a simplicial set.
5. **Terminal residues or phases are automatically predictive — false.**  The free-source theorem
   realizes arbitrary finite configurations before source relations are imposed.
6. **Local mixed Hessian is an ordinary `H^2` curvature — false for the arithmetic Stokes model.**
   Its bilinear bulk potential exists; the nonzero record is failure of that primitive to lie in
   the critical cofinal bornology.
7. **Bargmann phase is an independent component of `(I.134)` — false after the Gram correction.**
   Full Hermitian triangle labels determine it; it survives only as a derived face observable.
8. **Numerical death cuts make sense on every observer poset — false.**  Upper death regions are
   intrinsic; infima and widths require a calibrated numerical observer line.

### Truth verdict

The dependency-closed core now consists of six Step-2 cards:

1. all-degree stable-primitive exact sequence, persistence, immortality, and Scott realization;
2. one-dimensional finite-part horizon, fixed-ray residue, and phase--cut law;
3. multi-time polyhedral death region, Boolean fixed faces, and phase conormal;
4. coherent source functor, Gram-labelled nerve laws, and two strict nonreconstructibility models;
5. flat and curved terminal transgression with cofinal-normalizer rigidity;
6. source-pure arithmetic degree-two quotient with the exact three-chart identity `(I.218)`.

Their proofs use only declared hypotheses.  Equation tags and internal references are sequential
and closed.  The multi-time primitive-independence argument was repaired locally away from the
other coordinate faces; the nerve death invariant was repaired from a numerical infimum to an
upper region; the final object was repaired so phase is derived.  No Lean code was written or
built.

### Priority verdict

Nearly every ambient ingredient is occupied:

| Ingredient | Parent territory | Novelty credit here |
|---|---|---|
| exact cochains nontrivial under restricted primitives | bounded/controlled cohomology | none for slogan |
| filtered deaths and multi-time regions | persistence modules and filtered topology | none by itself |
| regularity-dependent solvability | cohomological equations and Sobolev obstruction theory | none by itself |
| Scott lattice and Sierpinski classifier | domain theory | none for Theorem XXVIII's ambient proof |
| coherent boundary vectors | Fock/white-noise/rigged-Hilbert theory | none for exponential formula |
| simplicial incidence and Bargmann phase | simplicial and quantum-geometric parent theory | none individually |
| cocycle curvature and Bianchi identity | ordinary cohomology and discrete connection theory | none individually |

No exact collision was found for the conjunction:

> observer points are stable-coboundary profiles; exactness topology is their Scott pullback;
> endpoint comparisons form a source-synchronous Gram-labelled nerve not determined by its entire
> one-skeleton; non-dying classes land on fixed residue faces; and a concrete arithmetic mixed
> class is read identically by Stokes density, Sonin torsion, and BV--Wold holonomy.

This is a **candidate novel synthesis**, not a proved priority claim.  Database search cannot show
that nobody has formulated an equivalent decorated controlled-cohomology object.  A specialist in
controlled cohomology, domain theory, or higher persistence could still find a categorical
equivalence.

### Significance verdict

The construction clears a real internal bar:

1. It replaces “find one missing Hilbert space/topology” by a representation object whose points
   are solvability profiles.
2. It proves ordinary cohomology, terminal primitive failure, and joint synchronization are
   different gates.
3. It proves pairwise data are insufficient even after retaining the complete labelled graph.
4. It gives both coherent and noncoherent source functors.
5. It compresses three exact arithmetic obstruction formulas into one source-defined class without
   selecting a zero.

It does **not** clear the RH-bearing bar.  The radial arithmetic quotient is one-dimensional by
construction and detects `1-2 Re(s)`; it supplies no source theorem forcing that coordinate to
vanish on Xi conormals.  The missing source-normal dagger/Stokes landing remains exactly where the
corpus placed it.  The free-source no-go proves geometry cannot manufacture this relation.

Verdict: **significant as a new internal geometry and research language; external mathematical
significance and priority remain unverified; not an RH advance.**

### Stop rule

Further unconstrained examples, metaphors, or categorical renamings would not move the load-bearing
frontier.  Non-theatrical next steps are now disjoint from this discovery turn:

1. formalize the six extracted Step-2 cards in their stated order;
2. obtain specialist collision review;
3. independently construct the source-normal arithmetic relation required to annihilate or bound
   the class—without defining it from Xi zeros.

Within the authorized paper-proof scope and available source data, hostile review exposes no
additional theorem that changes the representation object or closes its arithmetic open core.
