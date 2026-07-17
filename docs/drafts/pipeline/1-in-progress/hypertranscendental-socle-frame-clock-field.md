# The socle-frame clock field of a constrained hypertranscendental source

- **ID:** `hypertranscendental-socle-frame-clock-field`
- **Stage:** 1-in-progress
- **Type:** FOUNDATIONAL STRUCTURE THEOREM / UNIFIED-FIELD CONJECTURE
- **Scientific status:** `[THEOREMS A AND C ARE PARENT THEORY]`
  `[THEOREM D PAPER-PROVED PARENT DUALITY / NEW EXACT TRANSITION RECEIVER]`
  `[THEOREM B PAPER-PROVED VIA TAIL-FULL DIRICHLET CRITERION]`
  `[ALGEBRAIC CONSERVATIVITY AND EXACT DUAL-TRANSITION CORE LEAN-FORMALIZED]`
  `[ANALYTIC CONJUNCTION NOVELTY PROVISIONAL] [NAIVE SOCLE PRO-TOWER REFUTED]`
  `[DUALIZING-EXTENSION FIELD SUCCESSOR OPEN]`
  `[NOT AN RH RESULT]`
- **Parents:**
  - `hypertranscendental-affine-torus-constraint-spectrum-universality.md`
  - `hypertranscendental-polarized-strict-descent-field.md`
  - `source-framed-galois-colligation.md`
  - `hypertranscendental-constraint-sheaf-reconstruction-duality.md`

## 1. The displacement

The complete affine constraint scheme does not select a hypertranscendental realization.  The
finite-dual universality theorem proves more: even nilpotent thickness and embedded components can
be prescribed independently of scalar hypertranscendence.  The missing datum is therefore not a
finer spectrum of the same algebra.  It is a **choice of how the algebra is read**.

For a finite local constraint algebra that choice has a sharp minimal carrier.  It is not the full
dual space and not an arbitrary reporter.  It is a frame of the dual socle, lifted to primitive
cogenerators and repeated through an infinite rationally independent clock.

This produces two independent capacities:

```text
boundary width = Cohen--Macaulay type = number of primitive amplitude generators;
clock depth     = infinite rational frequency rank = scalar HT amplification.       (1)
```

The first is finite and source-transverse.  The second is infinite and observable-vertical.  Their
coupling, not either invariant alone, is the proposed local atom of the unified field.

## 2. Primitive amplitudes

Let `A` be a finite-dimensional commutative local complex algebra, with maximal ideal `m`, and put

```text
Soc(A)=Ann_A(m),                 r=dim_C Soc(A).
```

Give `A*=Hom_C(A,C)` its regular left `A`-module structure

```text
(a . ell)(b)=ell(ab).                                                    (2)
```

A width-`c` primitive amplitude system is a tuple

```text
ell=(ell_1,...,ell_c) in (A*)^c,
M_ell=A ell_1+...+A ell_c subset A*.                                    (3)
```

It is **conservative** when `M_ell=A*`.  This means that structural translates of the primitive
readouts generate every finite-dual amplitude; it does not mean that the `ell_j` themselves span
`A*` as a complex vector space.

## 3. The finite socle-frame theorem

> **THEOREM A -- MINIMAL CONSERVATIVE SOCLE FRAME.** For every `A` above:
>
> 1. restriction to the socle induces a canonical isomorphism
>
>    ```text
>    A*/mA*  ~=  Soc(A)*;                                                (4)
>    ```
>
> 2. `ell_1,...,ell_c` generate `A*` as an `A`-module exactly when their socle restrictions span
>    `Soc(A)*`;
> 3. the minimum conservative width is `r`;
> 4. at width `r`, the reductions of the primitive amplitudes form an ordered frame of
>    `Soc(A)*`;
> 5. quotienting conservative minimal tuples by the subleading gauge `(mA*)^r` gives exactly the
>    frame torsor
>
>    ```text
>    Gen_r(A*)/(mA*)^r  ~=  Fr(Soc(A)*).                                (5)
>    ```

### Proof

The annihilator in `A` of `mA*` under the perfect vector-space pairing `A x A* -> C` is

```text
{a in A : ell(xa)=0 for every x in m and ell in A*}=Ann_A(m)=Soc(A).
```

Dualizing the quotient therefore gives `(A*/mA*)* ~= Soc(A)`.  Equivalently, the restriction map
`A* -> Soc(A)*` is surjective with kernel `mA*`, proving `(4)`.  Nakayama's lemma now says that a
tuple generates `A*` exactly when its reductions span the quotient.  Its minimal cardinality is
therefore `dim Soc(A)=r`; at minimal cardinality spanning is the frame condition.  Two lifts have
the same frame exactly when their componentwise difference lies in `mA*`, which proves `(5)`.

This theorem is Macaulay--Matlis/Nakayama parent algebra.  It is recorded because it determines the
only possible minimal boundary width; it is not claimed as new by itself.

## 4. Clocked analytic amplification

Suppose now that

```text
A=C[t_1^(+-1),...,t_n^(+-1)]/I
```

is finite-dimensional and local.  A primitive frame `ell_1,...,ell_r` generates `A*`.  Hence a
finite set of structural orbit amplitudes

```text
lambda_k=a_k . ell_(j(k))                                                   (6)
```

is a complex basis of `A*`.  Repeat this finite orbit basis infinitely often, attach a positive
frequency set which is linearly independent over `Q`, realize the commuting units `t_i` by matrix
exponentials, and damp diagonally.  This gives one scalar entire function

```text
F_(I,ell)(z,y)=sum_k c_k phi_(lambda_k)(z) exp(-mu_k y).                   (7)
```

> **THEOREM B -- SOCLE-FRAME CLOCKED UNIVERSALITY.** The function `(7)` has
>
> ```text
> P(delta,T)F_(I,ell) DA over C(z,y)
>   iff P belongs to C[delta]I;                                            (8)
> ```
>
> and for every finite family `P_1,...,P_s`, its structural observables are jointly
> differentially algebraically independent exactly when their residue classes are
> `C(delta)`-linearly independent in `C(delta) tensor A`.
>
> Conversely, any orbit-generated amplitude construction with exact structural separation has
> at least `r` primitive generators.  Thus `type(A)` is the exact primitive boundary width of a
> scalar clocked HT realization retaining the full nonreduced differential matroid.

### Proof

The orbit basis `(6)` separates every finite-dimensional subspace of `A`, and its infinite
repetition remains separating in every tail.  It therefore satisfies the amplitude hypothesis in
the proof of clocked finite-dual universality.  Matrix logarithms give actual unit translations;
normal damping gives an entire scalar; Ostrowski excludes an algebraic differential equation for
every surviving operator; and rational independence plus generalized-Dirichlet uniqueness and
polarization gives the full finite-family rank law.

For minimality, let `M` be the `A`-submodule generated by `c` primitive amplitudes.  Every amplitude
obtainable from them by structural translation lies in `M`.  If `M != A*`, finite-dimensional
duality gives `0 != a in A` annihilated by all of `M`.  Every structural translate of every
available amplitude then annihilates `a`, so no orbit-generated construction from those primitives
can have exact structural separation.  Hence `M=A*`, and Theorem A forces `c>=r`.

The analytic proof uses the same generalized-Dirichlet and matrix-logarithm inputs as its parent
universality theorem.  The system-level step is closed by the following criterion.

### Tail-full Dirichlet differential-independence theorem

> **THEOREM B1 -- TAIL-FULL CRITERION.** Let `lambda_k>0` tend to infinity and let the complete
> family `(lambda_k)` be linearly independent over `Q`.  Let
>
> ```text
> f_j(y)=sum_k a_(j,k) exp(-lambda_k y),       1<=j<=s,                    (8a)
> ```
>
> converge normally, together with all termwise derivatives, on every compact subset of `C`.
> For `R>=0`, put
>
> ```text
> v_k^R=((-lambda_k)^r a_(j,k))_(1<=j<=s,0<=r<=R).                       (8b)
> ```
>
> If every tail `{v_k^R:k>=N}` spans `C^(s(R+1))` for every `R,N`, then
> `f_1,...,f_s` are differentially algebraically independent over `C(y)` for the derivation
> `d/dy`.

### Proof of Theorem B1

Assume a nonzero differential-polynomial relation.  Clear denominators and write it as a finite
sum

```text
sum_(d,h) y^h H_(d,h)(X_(j,r)),                                             (8c)
```

with every `H_(d,h)` homogeneous of total degree `d`.  Normal convergence permits expansion and
regrouping by finite multisets of frequency indices.  Full `Q`-linear independence makes the sum
of frequencies attached to a multiset unique, even across different total degrees.

The resulting generalized Dirichlet expansion has distinct exponents and polynomial coefficients
in `y`.  Such an expansion is unique.  Indeed, its exponent set is locally finite because
`lambda_k -> infinity` and the polynomial has bounded total degree.  Isolate the least exponent,
multiply by its exponential, and let `y -> +infinity`; the remaining normally convergent tail is
exponentially small, so the leading polynomial tends to zero and is therefore the zero polynomial.
Induction through the locally finite ordered exponent set kills every coefficient.

Fix `d,h` and choose a multiset of `d` distinct indices.  Its coefficient is the symmetric
polarization of `H_(d,h)` evaluated on the corresponding `v_k^R`, so that polarization vanishes on
every tuple of distinct tail vectors.  To evaluate it on arbitrary vectors, express the first
vector in one tail span, then the second in a tail beginning after all indices used for the first,
and continue.  Multilinearity makes the polarization vanish everywhere.  Characteristic zero
then gives `H_(d,h)=0`.  Repeating for every `d,h` makes `(8c)` the zero polynomial, a
contradiction.

For Theorem B, after an integer specialization in the translation variables, failure of tail-full
span would give polynomials `A_j(X)` satisfying

```text
ell_k(t^q sum_j A_j(-lambda_k)P_j(-lambda_k))=0                            (8d)
```

on a tail.  Each orbit-basis functional occurs infinitely often.  Polynomial uniqueness in
`lambda_k`, followed by separation by the orbit basis, gives a nonzero relation
`sum_j A_j(X)[P_j(X)]=0` in `A[X]`, contradicting `C(delta)`-linear independence.  Thus Theorem B1
applies.  Rational coefficients in the translation variables cause no gap: after clearing them,
`Z^n`-density supplies an integer specialization at which the differential polynomial remains
nonzero.

This also clarifies the derivation convention in `(8)`: differential algebraicity is with respect
to the transverse derivation `delta=partial_y`; the translation variables lie in the coefficient
field.  No independence under additional `z_i`-derivations is claimed.

## 5. Canonical scalar selection is impossible

The minimal data are canonical as a torsor, not as a point.

> **THEOREM C -- NO SOURCE-FREE NATURAL FRAME.** There is no isomorphism-natural rule assigning a
> minimal conservative primitive-amplitude class to every finite local complex constraint algebra.

### Proof

Apply such a rule to the dual-number algebra

```text
A=C[epsilon]/(epsilon^2).
```

Its socle is `C epsilon`, so a minimal class is a nonzero frame of `Soc(A)*`.  Every `u in C*`
defines an automorphism `epsilon |-> u epsilon`.  The induced action on `Soc(A)*` has weight
`u^(-1)`, and therefore fixes no nonzero frame.  Naturality would require the selected frame to be
fixed by every automorphism, a contradiction.

> **POSITIVE SUCCESSOR.** For the dual numbers, the normalized minimal classes form a genuine
> `C*`-torsor, and the automorphism group acts simply transitively.  In general, the canonical
> source-free object is the frame groupoid `Fr(Soc(A)*) // Aut(A)`.  A source normalization is a
> reduction or section of this groupoid, not more topology extracted from `Spec(A)`.

This is the exact local reason a bare constraint, even with its complete nonreduced or derived
scheme, cannot canonically select a primitive scalar frame.  It does **not** by itself exclude a
natural scalar HT carrier which encodes an entire frame orbit without selecting one point; that
stronger no-go would require a theorem extracting a frame functorially from every exact carrier.

## 6. What orientation blindness means

The derived constraint algebra determines the socle and therefore the frame bundle, but it does not
choose a frame.  The determinant of that missing frame is only its first rank-one shadow:

```text
determinant shadow = det(Soc(A)*).                                      (9)
```

For `r>1`, `(9)` forgets the entire `SL_r` part of a frame; over `C` it does not supply a sign or a
positive real chamber.  The full amplitude frame is therefore the local orientation datum, while
the determinant is only a necessary quotient.  A genuine Krein or positivity orientation requires
additional real structure and a reduction of the complex frame group.

Thus “the full derived topology is blind to orientation surgery” does not mean that the scheme has
no duality module.  It means that unframed derived data cannot distinguish different framed or
real-polarized lifts of the same algebra.  The socle frame explains one finite local part of that
blindness; it is not the complete analytic orientation field.

For any potential RH proof this is a typing obstruction: a chain factoring only through an
unframed scheme, derived category, determinant support, or self-dual spectrum has discarded the
sign/phase trivialization before positivity is asked.  No later construction functorial in that
forgotten object can recover it.

## 7. The naive pro-frame conjecture fails

Bare socles do not form the required clock tower.  The canonical test is

```text
A_N=C[epsilon]/(epsilon^(N+1)),
q_N:A_(N+1) -> A_N.                                                        (10)
```

Every chart is Gorenstein of type one and

```text
Soc(A_N)=C epsilon^N.
```

But the quotient transition sends the next socle generator to zero:

```text
q_N(epsilon^(N+1))=0.                                                       (11)
```

Therefore the expression `holim_N Fr(Soc(A_N)*)` is not merely unproved; with ordinary truncation
maps it is not a nonzero compatible frame tower even in the simplest type-one example.

> **NO-GO -- BARE SOCLE FRAMES ARE NOT THE UNIFIED FIELD.** Finite local conservativity frames do
> not carry their own source-clock transition law.  A tower of unshifted socles loses the boundary
> generator at every truncation.

> **POSITIVE -- THE TRANSITION IS A DUALIZING EXTENSION, NOT A SOCLE MAP.** Put
> `omega_R=Hom_C(R,C)`.  Precomposition along any finite quotient `q:B -> A` is a canonical
> injection
>
> ```text
> q^vee:omega_A -> omega_B,
> im(q^vee)=Ann_(omega_B)(ker q)=Hom_B(A,omega_B),                           (12)
> ```
>
> and finite-dimensional duality gives the canonical exact sequence
>
> ```text
> 0 -> omega_A -> omega_B -> (ker q)* -> 0.                                (12a)
> ```
>
> If `i:Spec(A) -> Spec(B)`, this is the inclusion
> `i_* i^! omega_B -> omega_B`, with `i^! omega_B ~= omega_A`.  The earlier candidate arrow
> `q^! omega_A -> omega_B` was ill-typed and is discarded.  In the monogenic tower, after the
> standard Frobenius identifications `omega_(A_N) ~= A_N`, the canonical injection `(12)` becomes
> multiplication by `epsilon`, carrying `epsilon^N` to `epsilon^(N+1)`.  The multiplication formula
> depends on those trivializations; the dual injection does not.

The ordinary transition defect has a general exact form.

> **THEOREM D -- RELATIVE SOCLE-TRANSITION LAW.** Let `q:B -> A` be a surjective local morphism of
> finite-dimensional local complex algebras.  Precomposition gives `q*:A* -> B*` and descends to
>
> ```text
> q_bar*:A*/m_A A* -> B*/m_B B*.                                         (12b)
> ```
>
> Under the canonical restriction identifications with `Soc(A)*` and `Soc(B)*`, `(12b)` is exactly
> the dual of
>
> ```text
> q_Soc:Soc(B) -> Soc(A).                                                  (12c)
> ```
>
> Hence a minimal frame transports conservatively exactly to the rank carried by `q_Soc`; at equal
> type it transports as a frame exactly when `q_Soc` is an isomorphism.  The pair
>
> ```text
> D_Soc(q)=(ker q_Soc, coker q_Soc)                                       (12d)
> ```
>
> is the complete ordinary primitive-frame transition defect.

Indeed, locality makes `q` carry `Soc(B)` into `Soc(A)` and makes `q*` preserve the maximal-ideal
dual gauges.  For `lambda in A*` and `s in Soc(B)`, both routes around the restriction square equal
`lambda(q(s))`; this proves that the induced quotient map is `(q_Soc)*`.  The rank and equal-type
claims follow from finite-dimensional duality.  This is parent linear/Matlis duality, but `(12d)` is
the exact positive receiver forced by the failed pro-frame conjecture.

The full dualizing transition has a stronger exact conservativity law.

> **THEOREM E -- EXACT TRANSITION-KERNEL LAW.** Let `ell` be any primitive family on `A` whose
> joint structural readout is injective.  Transport it to `B` by `q^vee`.  Then
>
> ```text
> ker Obs_(q^vee ell) = ker q.                                             (12e)
> ```
>
> Consequently the transported family is conservative on `B` exactly when `q` is injective.  For
> a proper quotient it is lossless on the embedded exceptional-dual interval and blind to exactly
> the new finer-source layer--never to an accidental larger subspace.

For `(10)`, `q_Soc=0` while `q^vee` is injective.  Thus the primitive socle orientation can die
under ordinary truncation even though the full dualizing carrier is conserved exactly.  This is
the **conservation--orientation separation**: associated socle frames record endpoint orientation,
whereas the exact sequence `(12a)` records how that endpoint is attached.  Passing to the socle or
associated graded destroys the extension arrow that transports it.

The corpus independently forces the same correction: a nonprimitive source charge is carried by
an indecomposable oriented interval with charge-raising arrows, while its split character sectors
and endpoint line forget the ordered extension.  The local frame is a stalk of that interval, not
the interval itself.

> **[CONJECTURE -- DUALIZING-EXTENSION FIELD PRINCIPLE.]** For every regular finite-source minimal
> constrained HT system, its intrinsic finite source-clock filtration carries the exact-couple
> pro-object
>
> ```text
> E_N: 0 -> q_N^vee omega_N -> omega_(N+1) -> Delta_N -> 0,
> Delta_N=(ker q_N)*.                                                       (13)
> ```
>
> After differential-algebraic localization, every intrinsic reconstruction, continuation,
> spectral, positivity, or monodromy obstruction factors through a polarized analytic realization
> of this extension field.  Two obstruction chains represent the same obstruction only if their
> reporters are jointly conservative on the extension classes in `(13)`, not merely if they have
> the same support, spectrum, socle, determinant, or associated graded.  Hypertranscendental
> nontermination means that no finite DA-relative quotient is conservative on the realized
> extension field; it does not mean that the raw socle rank grows.

This conjecture is bolder but better typed than the discarded pro-frame tower.  It predicts that
the recurring obstructions live in different features of the same **transition-bearing** object:

```text
spectral incompleteness = nonclosed or rank-defective completed transition reporter;
continuation failure    = failure to glue the exceptional-dual intervals analytically;
positivity failure      = no positive real reduction of the polarized full-frame field;
monodromy               = holonomy of its interval/frame transport;
boundary noncanonicity  = absence of a source-natural compatible splitting of E_N;
orientation blindness   = forgetting the extension arrows or the full real reduction.    (14)
```

Equation `(14)` remains a representation conjecture.  It clears the anti-theatre gate only after
two independently constructed natural HT obstruction functors preserve the same intervals and
connecting arrows.

> **[CONJECTURE -- ZETA PRESSURE TEST, NOT AN RH RESULT.]** If the zeta obstruction chains really
> are representations of one object, their common critical-line zeros are the self-dual points at
> which two independently constructed polarized reporters lose conservativity on the same
> extension class of `(13)`.  Equality of degeneracy sets alone is insufficient: the reporters
> must identify the same kernel object and its dual cokernel.

## 8. Strong falsifiers and positive residues

1. If a natural constrained HT family has finite truncations whose minimal conservative readouts
   are not controlled by the relative dual/socle module, then `(13)` is false.  The positive result
   is the new minimal module detected by that family.
2. If the transition-bearing dualizing interval stabilizes finitely while the selected germ
   remains HT, interval nontermination is not the HT criterion.  The positive result is an exact
   separation between transition stabilization and differential-algebraic stabilization.
3. If two natural obstruction functors have the same degeneracy set but do not preserve the same
   extension class, kernel object, and dual cokernel, they are not representations of one object.
   The positive result is an exact nonconservativity witness.
4. If source presentation changes the dualizing-extension field, replace ordinary isomorphism by the minimal
   Morita/dualizing invariant that restores it; do not add a chosen frame by hand.
5. If the analytic construction requires more primitive amplitude generators than `type(A)`, the
   orbit-generation claim in Theorem B is false.  The positive survivor is the exact excess width
   between algebraic cogeneration and analytic effectivity.
6. If two source presentations have equivalent DA-relative dualizing-extension pro-objects but
   different intrinsic obstruction states, the principle `(13)` is false.  The positive successor
   is the minimal extra structure distinguishing those states.

## 9. Novelty gate

Established parents, excluded from novelty:

- Matlis duality, Macaulay inverse systems, level type, and Nakayama's lemma;
- local Frobenius/Gorenstein criteria via a functional nonzero on the socle;
- frame bundles, quotient stacks, determinant lines, and orientation local systems;
- exact dual sequences, exceptional inverse image for finite morphisms, and Matlis-dual transport;
- finite duals and spectral synthesis;
- Ostrowski hypertranscendence of infinite-rank general Dirichlet series;
- parameterized difference Galois torsors and generic observability theory.

The candidate-new theorem is the exact conjunction in Theorem B: `type(A)` primitive amplitudes,
their constraint-algebra orbits generating the complete finite-dual amplitude system, one entire
scalar clock realization with actual commuting translations, the exact arbitrary nonreduced ideal,
and the complete nonlinear differential-matroid rank law.  This is a finite-local sharpening of
the parent clocked finite-dual universality theorem, not a separate foundational paper.  Exact-form
searches found the parent columns but not the complete analytic conjunction.  Priority is
provisional.

Two closer analytic parents materially narrow the claim.  Oberst--Pauer's module--behaviour duality
already uses injective-cogenerator signal spaces, including analytic signal spaces, and
Bourlès--Oberst treat analytic operator rings containing both derivatives and translations.
Ostrowski already excludes algebraic difference--differential equations for sufficiently
infinite-rank convergent Dirichlet series.  The remaining possible novelty is therefore the cyclic
**one-scalar** entire realization of an arbitrary nonreduced Laurent ideal together with the exact
DA annihilator and full `C(delta)` matroid law, not the general idea that analytic signals read
operator modules.

The Fields-scale claim is not Theorem A or the generic frame stack.  It is `(10)` plus a
source-natural essential-image and conservativity theorem across genuinely different analytic HT
families.  Without that cross-family theorem, the extension field is a bold research hypothesis, not new
science.

Theorems D and E are exact and useful but their algebraic content is parent duality.  Their new
role is diagnostic: together they prove that endpoint orientation loss and full-carrier
conservation are different phenomena.  The candidate-new science begins only with the analytic
factorization and joint-conservativity assertion `(13)` across independent HT families.

Primary comparison points:

- Stacks Project, *Duality over Artinian local rings*, Tags `08YW`, `08YY`, `08YZ`;
- J. Elias and M. E. Rossi, *The structure of the inverse system of Gorenstein k-algebras*,
  `https://arxiv.org/abs/1705.05686`;
- A. Iarrobino, P. Macias Marques, and C. McDaniel, inverse systems and orientations of level
  algebras, `https://par.nsf.gov/servlets/purl/10231187`;
- G. M. Bergman, *Minimal faithful modules over Artinian rings*,
  `https://arxiv.org/abs/1310.5365`;
- M. L. Reyes, *The finite dual coalgebra as a quantization of the maximal spectrum*,
  `https://arxiv.org/abs/2111.07081`;
- A. Ostrowski, *On Dirichlet Series and Algebraic Differential Equations*,
  `https://arxiv.org/abs/2211.02088`;
- T. Dreyfus, *Hypertranscendence and linear difference equations, the exponential case*,
  `https://arxiv.org/abs/2212.00388`.
- W. Y. Pong, *Applications of differential algebra to algebraic independence of arithmetic
  functions*, `https://arxiv.org/abs/1504.03263`;
- U. Oberst and F. Pauer, module--behaviour duality for analytic signal spaces,
  `https://www.uibk.ac.at/mathematik/personal/oberst/oberstpauer2000.pdf`;
- H. Bourlès and U. Oberst, analytic operator rings with derivatives and translations,
  `https://doi.org/10.1007/s00498-012-0089-8`.

## 10. Lean target

The exact unconditional algebraic core is formalized in

```text
formal/GaloisForLFunctions/HTGeometry/SocleFrameClockField.lean.
```

It proves:

1. the regular action of a commutative algebra on its linear dual;
2. equivalence between joint structural observability and generation of the dual amplitude module;
3. existence of a nonzero jointly invisible law whenever the primitive orbit span is proper;
4. the stronger positive survivor: such an invisible law can have an algebraically independent
   complete transverse clock jet;
5. detection of every surviving quotient law by a conservative primitive family;
6. the exact transported-readout identity `ker Obs_(q^vee ell)=ker q` for every surjective algebra
   transition and conservative quotient readout;
7. transported conservativity if and only if the source transition is injective;
8. the dual-number scaling no-natural-frame theorem.

The local type/frame quotient and the analytic Dirichlet realization remain paper mathematics.
The Lean file does not claim them.  The dual-transition theorem is proved at the structural
readout level rather than repackaging mathlib's existing dual-map lemmas.  The next exact formal
target is the separation square comparing the full transition kernel with the socle transition
defect, but only if it contains content beyond existing dual and oriented-interval APIs.

## Gates

- [x] live source/colligation/strict-descent corpus audited
- [x] Macaulay--Matlis/Frobenius parent collision identified
- [x] minimal primitive width isolated as `type(A)`
- [x] structural-orbit amplification mechanism stated
- [x] dual-number canonicality falsifier found
- [x] nontrivial positive frame-torsor replacement found
- [x] naive compatible socle-frame tower falsified by the monogenic truncation tower
- [x] ill-typed exceptional transition rejected and corrected to the canonical dual injection
- [x] conservation--orientation separation isolated as the positive successor
- [x] determinant-only orientation claim rejected
- [x] exact orbit-conservativity and invisible-HT-survivor core formalized in Lean
- [x] exact transported-readout kernel law formalized in Lean
- [x] polynomial-coefficient generalized-Dirichlet uniqueness proved
- [x] distinct-index polarization and tail-span argument proved
- [x] Theorem B closed on paper from Theorem B1
- [ ] independent specialist paper audit of Theorems B and B1
- [x] ordinary-versus-exceptional transition law proved without duplicating the interval API
- [ ] one natural HT family identified with its dualizing-extension field
- [ ] two analytic obstruction functors proved conservative on one tower
- [ ] specialist novelty audit completed
