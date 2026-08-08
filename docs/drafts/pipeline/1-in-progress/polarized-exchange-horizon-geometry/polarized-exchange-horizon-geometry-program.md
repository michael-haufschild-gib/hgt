# Polarized exchange-horizon geometry

- **ID:** `polarized-exchange-horizon-geometry-program`
- **Stage:** 1-in-progress
- **Type:** FOUNDATIONAL CONJECTURE / META-THEORY / RH PRODUCER
- **Scientific status:** `[FROZEN CONJECTURE] [RANK-ONE OBSTRUCTION PAPER-PROVED]`
  `[BIORIENTED AMBIENT PARENT IDENTIFIED] [ACTUAL SOURCE REALIZATION OPEN] [NOT RH]`
- **Source:** ordinary-prime first-trace, ramified top-conormal, Gamma/co-Poisson/Sonin,
  source-normal Stokes--Bockstein, and source/reporter ambidexterity corpus
- **Statement:** Arithmetic correspondences, Fourier adjunction, and geometric duality are three
  restrictions of one partial-\(K\)-labelled exchange formalism.  Its polarized realization has a
  canonical coherence defect;
  the critical line is the rank-one locus where the arithmetic inverse and analytic adjoint can
  belong to one coherent exchange geometry.

## Goal

Replace the static picture

```text
arithmetic object  <->  Fourier spectrum  <->  geometric space
```

by one object whose morphisms already contain all three operations.  The proposed geometry is not
a manifold with primes, zeros, or phases added as coordinates.  Its primitive is a source
correspondence together with its tangent label and its two exchange realizations.

The RH-facing goal is exact: construct the ordinary-integer source-normal realization before
divisor specialization and prove that the already-computed first-trace essential edge and the
Gamma/co-Poisson/Sonin source-error syzygy are images of the same exchange morphism.  The theory
must then carry the full reduced Xi principal conormal conservatively and identify source inverse
duality with Hilbert adjunction.  No zero-indexed metric, Hilbert space, or exchange map is allowed
as input.

## 1. Why the three sides have resisted unification

The corpus already closes many pairwise comparisons:

```text
arithmetic -> geometry:
  power correspondences, different/top-conormal shift, Cartier and Rost--Schmid boundaries;

arithmetic -> spectral:
  Euler/Mellin scalarization, prime dilation characters, first-trace essential normal edge;

geometry -> spectral:
  Grothendieck residue adjunction, Gamma orientation, co-Poisson/Sonin quotient and Hilbert dagger.
```

Pairwise closure is insufficient.  Off the critical line all three objects still exist, and the
finite Gamma/co-Poisson connection is even operator-flat.  What fails is functorial composition
after the analytic dagger gain acts on only one conormal coefficient.  Thus the missing invariant
is not a point, spectrum, curvature of the flat connection, or extra reporter.  It is the failure
of the three operations to be restrictions of one polarized exchange functor.

## 2. Parent universal category

Let \((\mathcal C_{\rm ar},\mathcal E,\mathcal S)\) be a source category with pullbacks and nested
classes of arithmetic correspondences.  Fisher's universal exchange theorem associates a
partial-\(K\)-labelled category and, with compatible base change, a labelled span category

\[
 \operatorname{Span}^{K}(\mathcal C_{\rm ar},\mathcal E).
\tag{1}
\]

A morphism is not merely a map.  It is a correspondence labelled by a partial-\(K\) tangent
class.  Partial \(K\)-theory is load-bearing: it imposes additivity of tangent labels without
freely adjoining inverses, so a Thom twist need not be invertible before the geometry proves the
required smoothness or orientation.

Strict exchange is not the whole ambient theory.  Gepner--Heine's oriented category theory treats
lax and oplax compositions as geometric orientation data and combines them in bioriented
categories.  The proposed source-normal enhancement uses:

```text
source transfer / arithmetic time       = orientation;
analytic adjoint / dagger reversal      = antiorientation;
their coherent lax--oplax comparison    = bioriented exchange cell;
strict interchange on a Cartier packet = polarized exchange horizon.
```

Thus the curved polarization below is required to be a coherent oriented/antioriented structure,
not an arbitrary family of nonfunctorial matrices.

The proposed arithmetic source category is generated before Xi specialization by:

1. ordinary power/prime correspondences and their pullback squares;
2. the ramified top-conormal correction selected by Grothendieck residue;
3. Gamma and co-Poisson interval correspondences;
4. the all-prime first-trace preclosure and its essential normal edge; and
5. reflection, source inversion, and strict principal-Cartier base change.

This list does not yet prove that the pullbacks, admissible classes, or coherences required by
`(1)` exist in the source-normal category.  Their construction is the open mathematics.

## 3. The new object

A **polarized exchange-horizon geometry** is a tuple

\[
 \mathfrak X_{\mathrm{PEH}}
 =(
   \mathcal C_{\rm ar},\mathcal E,\mathcal S,
   K_{\partial},
   \mathcal R_{\rm sn},
   \mathcal R_{\rm an},
   \eta_{\rm ex},
   \mathcal P_{+},
   \Omega_{\rm int},
   \mathfrak C_{\rm ex},
   \tau_{\rm PE},
   \operatorname{Sp}_{\rm Car}
 ).
\tag{2}
\]

Its terms have the following noninterchangeable roles.

- \(K_{\partial}\) is the partial-\(K\) tangent labelling of source correspondences.  This is the
  geometric side: it records normal, different, and Thom data before an inverse is granted.
- \(\mathcal R_{\rm sn}\) is the arithmetic source-normal realization.  It retains the prime
  action, integral incidence, essential first-trace edge, and nondivisive Stokes/Bockstein data.
- \(\mathcal R_{\rm an}\) is the unpolarized analytic Fourier/Gamma/co-Poisson realization.  It is
  functorial and carries the flat finite source connection.
- \(\eta_{\rm ex}\) is the canonical twisted exchange norm comparing the two realization
  variances.  It is constructed from `(1)`, not chosen on a zero fibre.
- \(\mathcal P_+\) is a bioriented curved positive polarization of \(\mathcal R_{\rm an}\).  It
  installs the Hilbert dagger on the rigid coefficient through coherent lax/oplax comparison
  cells but is not assumed to satisfy strict interchange.
- \(\Omega_{\rm int}(f,g)\) is the oriented interchange cell for each composable pair: its source
  is “compose arithmetically, then polarize,” and its target is “polarize each edge, then compose
  analytically with reversed dagger variance.”  Triple compositions must satisfy oriented
  interchange coherence, not merely pairwise equality.
- \(\mathfrak C_{\rm ex}\) is its composition curvature.  Its vanishing is a theorem to be proved
  on a source-selected subcategory, not a global axiom.
- \(\tau_{\rm PE}\) is the initial provenance-exactness topology of source-boundary/cycle flags.
- \(\operatorname{Sp}_{\rm Car}\) is conservative principal-Cartier specialization.  Its support
  is where exchange defects become finite spectral packets with multiplicity jets.

In an additive target, the strict shadow of \(\Omega_{\rm int}(f,g)\) is the polarized exchange
curvature

\[
 \mathfrak C(f,g)
 =
 \mathcal P_+(g)\mathcal P_+(f)-\mathcal P_+(gf).
\tag{3}
\]

In a stable nonadditive model, `(3)` is replaced by the cofiber of \(\Omega_{\rm int}(f,g)\).  The
**exchange horizon** is the derived strict-interchange locus: the full
source-Cartier subcategory on which `(3)` has a source-natural compatible null-homotopy and
\(\mathcal P_+\) therefore descends to a genuine polarized exchange functor.  Defining that
null-homotopy from a desired zero fibre would be circular.

The higher coherence requirement is not optional.  The oriented interchange cells must obey their
Gray-tensor coherence; at the matrix shadow this includes the already-proved nonabelian Bianchi
identity for \(\mathfrak C\).  A scalar family with formula `(5)` but no coherent interchange data
does not define the geometry.

This curved correction is forced.  A globally functorial polarized realization with matrices
`(4)` would make `(5)` vanish for every spectral parameter, which is false.  Only the
unpolarized exchange formalism is global; arithmetic must prove that its Xi Cartier packets land
in the derived zero locus of the curved polarization.

This use of “horizon” is mathematical, not a black-hole claim.  It is the boundary between
partial tangent data and an oriented coherent realization.  A physical holographic realization,
if one exists, is a later model and not evidence for `(2)`.  The earned analogy appears only in
`(6f)`: off horizon, transverse data determine boundary-error data isomorphically and no independent
edge homology remains; on horizon, that contraction dies and edge modes survive.  This is a precise
bulk-to-boundary degeneration a wormhole or black-hole model would have to realize, not a premise.

## 4. How arithmetic, Fourier, and geometry become one theory

```text
arithmetic side:
  correspondence f, transfer, incidence, prime composition
                    |
                    | relative tangent T_f in partial K
                    v
geometric side:
  K-labelled span; diagonal, normal/different, Cartier base change
                    |
                    | universal twisted exchange norm
                    v
spectral/Fourier side:
  pull/push adjoints and Mellin characters
                    |
                    | curved positive polarization
                    v
exchange horizon:
  source-selected zero locus where inverse and Hilbert adjoint compose coherently
```

The three sides are therefore not three charts on a hidden set of points.  Arithmetic supplies
composition, geometry supplies the tangent price of changing variance, and Fourier analysis
evaluates the same correspondence on characters.  A divisor point is a finite Cartier module on
which the exchange curvature can be tested.  Its horizontal coordinate is the regulator of the
polarized tangent twist.

This explains five corpus phenomena at once.

1. Finite source connection flatness is expected: unpolarized source correspondences compose.
2. Half-density is forced by the categorical degree needed to compare the two variances.
3. Off-line torsion survives flatness because polarization, not connection curvature, fails.
4. Ordinary Hilbert closure loses the obstruction because it is formed before the essential
   source-normal exchange edge has landed.
5. Integral or group-completed \(K\)-theory cannot quantize the horizontal regulator: it has
   forgotten the noninvertible, oriented passage represented by `(3)`.

## 5. Closed rank-one shadow

For \(n\ge1\), put

\[
 A_n=\begin{pmatrix}n&n-1\\0&1\end{pmatrix},
 \qquad
 \chi_s(n)=n^{2\operatorname{Re}s-1},
 \qquad
 T_s(n)=\operatorname{diag}(\chi_s(n),1)A_n.
\tag{4}
\]

The dedicated Stage-2 card proves

\[
 T_s(m)T_s(n)-T_s(mn)
 =
 \begin{pmatrix}
 0&\chi_s(m)(m-1)(1-\chi_s(n))\\
 0&0
 \end{pmatrix}.
\tag{5}
\]

Consequently the framed family can be the restriction of a functorial exchange realization only
if

\[
 \operatorname{Re}s=\frac12.
\tag{6}
\]

Conversely `(6)` removes this rank-one composition obstruction.  It does not construct the full
exchange formalism or prove Xi conormal admission.

Equation `(5)` is the exact meeting point of the three sides:

```text
n and n-1       = arithmetic degree and ramified different;
matrix product  = geometric composition of correspondences;
chi_s           = Fourier/Hilbert modular character;
curvature       = failure to be one polarized exchange functor.
```

The Stage-2 theorem also constructs a paracyclic rotation \(J_s(n)\) with

\[
 J_s(n)^2=\chi_s(n)I,
 \qquad
 \mathfrak C_s(m,n)
 =-\chi_s(m)(m-1)E_{12}\bigl(J_s(n)^2-I\bigr).
\tag{6a}
\]

Thus source--dagger cyclic monodromy, one-sided framed curvature, and exchange incoherence are
exactly calibrated shadows of one defect.  The cyclic rigidity and nonzero-quotient principle were
already present in the corpus; `(6a)` supplies the universal-exchange placement, not a competing
producer.

The matrices depend on \(s\) only through \(2\operatorname{Re}s-1\).  Exchange geometry can
therefore select a purity weight but cannot locate an imaginary spectral height.  Arithmetic
Cartier support must supply the spectrum; Fourier realization reads its characters; polarized
exchange geometry constrains their real weights.

The closed theorem is more general than this power law.  For every characteristic-zero field and
every multiplicative modular character \(\chi:\mathbb N_{>0}\to k^\times\), the maximal coherent
subspace is \(k^2\) exactly when \(\chi\) is trivial and is the permanent line \(ke_1\) otherwise.
Thus the meta-theory's universal selector is **modular-anomaly trivialization**.  A functional
equation turns that selector into a purity line; arithmetic Cartier support supplies the remaining
spectral location.

### Exchange-curvature homology

The first nontrivial curvature \(D_s=\mathfrak C_s(2,2)\) is square-zero.  The Stage-2 theorem
proves

\[
 \ker D_s/\operatorname{im}D_s
 \cong
 \begin{cases}
 \mathbb R^2,&\operatorname{Re}s=1/2,\\
 0,&\operatorname{Re}s\ne1/2,
 \end{cases}
\tag{6e}
\]

and, off the critical line,

\[
 \mathbb R^2/\mathbb Re_1
 \xrightarrow{\ \overline D_s\ }\mathbb Re_1
\quad\text{is an isomorphism.}
\tag{6f}
\]

This gives the exchange shadow a typed shape.  It does **not** identify the first-trace edge or the
Gamma/co-Poisson/Sonin syzygy with \(D_s\).  The corpus proves that the latter controls flat
connection error and explicitly does not equal mate curvature.  A new dagger-sensitive
transgression is required between that flat exact-couple target and the exchange complex.

It also explains why prior nonvanishing arguments stall.  Off horizon every nonzero vector in the
conormal error line is a boundary, uniquely lifted from the transverse quotient by `(6f)`.  A
nonzero error vector therefore proves no exchange homology at all.  Source arithmetic must prove
that the Cartier error class is not such a boundary—equivalently, that the composite source lift
survives in homology.  This is the homological content of the corpus warning “nonzero vector is not
nonzero quotient class.”

The proposed producer is therefore the two-stage composite, constructed before Xi specialization,

\[
 \operatorname{gr}{\mathfrak B}_{\rm first\ trace}
 \xrightarrow{\operatorname{gr}\Phi_{\rm src}}
 \operatorname{gr}{\mathfrak B}_{\Gamma/{\rm coP}/{\rm Sonin}}
 \xrightarrow{\Psi_{\rm PE}}
 \mathcal E_s
 :=\left[\mathbb R^2/\mathbb Re_1
   \xrightarrow{\overline D_s}\mathbb Re_1\right].
\tag{6g}
\]

Here \(\Phi_{\rm src}\) is the already-open source-normal exact-couple morphism, while
\(\Psi_{\rm PE}\) is a new bioriented realization that must retain the one-sided dagger defect
before the flat syzygy cancels it.  The Stage-2 landing criterion proves that if reduced Xi Cartier
base change carries a nonzero source homology class through the composite `(6g)` to nonzero
exchange homology, then \(\operatorname{Re}s=1/2\).  Thus the open statement is exact but strictly
stronger than merely constructing \(\Phi_{\rm src}\): the composite must be homology-conservative.

The corpus already determines the scalar shadow required of \(\Psi_{\rm PE}\).  If reciprocal
source transport has
character \(\lambda\), set \(\tau=|\lambda|^2\) and \(a=1-\tau\).  The Stage-2 theorem proves

\[
 a(mn)=a(m)+\tau(m)a(n),
 \qquad
 \Psi_{\rm PE}^{(1)}(\lambda)(m,n)
 =\tau(m)(m-1)a(n)E_{12}.
\tag{6h}
\]

Moreover \(a(n)=0\) exactly when source inverse \(\lambda(n)^{-1}\) equals Hilbert adjoint
\(\overline{\lambda(n)}\).  Thus `(6h)` canonically converts flat reciprocal transport into its
Hermitian exchange defect once the ramified affine different \(m-1\) is supplied.  Open work is
lifting this forced scalar transgression to \(\Psi_{\rm PE}\) on the actual exact couple, not
guessing its value.

### Kernel-only coherence topology (preliminary shadow)

For a family of curved polarized realizations on a finite framed carrier \(V\), let
\(\Delta_{x,D}:V\to V_D\) be the additive shadow of the failure of strict interchange for an
oriented pasting diagram \(D\).  For \(q\ge2\), define the cumulative coherent subspace

\[
 H_x^{(q)}
 =\bigcap_{2\le \dim D\le q}\ker\Delta_{x,D}
 \subseteq V.
\tag{6b}
\]

These form a descending **coherence spectrum**

\[
 H_x^{(2)}\supseteq H_x^{(3)}\supseteq\cdots,
 \qquad
 H_x^{(\infty)}=\bigcap_{q\ge2}H_x^{(q)}.
\tag{6c}
\]

Give each \(\operatorname{Sub}(V)\) its Scott topology, restrict the product topology to descending
chains, and give the parameter/Cartier space the initial topology of

\[
 \kappa_{\rm PE}:x\longmapsto (H_x^{(2)},H_x^{(3)},\ldots).
\tag{6d}
\]

This is the **cycle-shadow topology**. A basic open says that specified finite framed classes
are coherently transportable through specified finite pasting dimensions.  It separates three
questions that ordinary topology merges: pairwise composition, higher interchange, and stable
all-arity strictification.  Scott and initial topologies are standard; the new datum is the
bioriented coherence spectrum indexed by source pasting diagrams.

For `(4)`, the Stage-2 theorem computes only the pairwise layer

\[
 H_s^{(2)}=
 \begin{cases}
 \mathbb R^2,&\operatorname{Re}s=1/2,\\
 \mathbb Re_1,&\operatorname{Re}s\ne1/2,
 \end{cases}
\]

and the weight-line topology is exactly

\[
 \{\varnothing,\{0\},\mathbb R\}
\]

under \(\theta=2\operatorname{Re}s-1\).  This is the \(q=2\) Sierpinski capability topology, not
the usual topology of the complex plane.  It distinguishes full framed pairwise coherence from
the permanent conormal line, while deliberately leaving all off-weight parameters and all
imaginary heights unresolved.  The Stage-2 theorem further proves that every ordinary higher-word
matrix defect has the same kernel \(H_s^{(2)}\).  What remains unproved is equality with the full
bioriented \(H_s^{(\infty)}\): strict matrix reassociation stabilizes at arity two, but oriented
interchange cells and their higher homotopies still require the source realization.

### Provenance-exactness topology (hostile correction)

The preceding Scott profile is not the final geometry. The proved secondary Poisson theorem gives
a literal source range \(\mathcal B_{\rm P}\) strictly smaller than its reflected radical
\(\Gamma_{\rm sec}\). A common kernel records cycles but forgets which cycles are arithmetic
boundaries. Consequently it cannot even state the live range-incidence obstruction.

For each pasting depth, retain geometric cycle space \(Z_x^{(q)}:=H_x^{(q)}\), but require source
arithmetic to construct a boundary map

\[
 d_{x,{\rm src}}^{(q)}:S_x^{(q)}\longrightarrow V,
 \qquad
 B_x^{(q)}=\operatorname{im}d_{x,{\rm src}}^{(q)}
 \subseteq Z_x^{(q)}.
\tag{6i}
\]

The inclusion in (6i) is precisely the source Stokes chain condition. It is not supplied by
Fourier reflection. The new representation object is the provenance-exactness flag and its
spectral quotient

\[
 \mathfrak F_x^{(q)}=(B_x^{(q)}\subseteq Z_x^{(q)}),
 \qquad
 \mathsf H_x^{(q)}=Z_x^{(q)}/B_x^{(q)}.
\tag{6j}
\]

Give boundary coordinate lower topology and cycle coordinate Scott topology, restrict their
product to flags, and use initial topology of

\[
 \kappa_{\rm PE}^{\rm prov}:x\longmapsto
 (\mathfrak F_x^{(2)},\mathfrak F_x^{(3)},\ldots).
\tag{6k}
\]

The dedicated Stage-2 paper theorem proves this is \(T_0\), with specialization order

\[
 (B,Z)\preceq(B',Z')
 \quad\Longleftrightarrow\quad
 B'\subseteq B\subseteq Z\subseteq Z'.
\tag{6l}
\]

Thus horizon formation has a precise direction: boundary range contracts while cycle space
expands. A framed survival locus

\[
 \{x:v\in Z_x^{(q)},\ v\notin B_x^{(q)}\}
\tag{6m}
\]

is open and means exactly that \(v\) represents a nonzero class. The theorem also proves
inverse-image transport continuous while general quotient/direct-image range formation is not.
This explains the live asymmetry: Fourier constraints pull back cleanly, whereas arithmetic
source range is singular extra data.

For rank-one exchange, full flag is

\[
 (B_s^{(2)},Z_s^{(2)})=
 \begin{cases}
 (0,\mathbb R^2),&\operatorname{Re}s=1/2,\\
 (\mathbb Re_1,\mathbb Re_1),&\operatorname{Re}s\ne1/2.
 \end{cases}
\tag{6n}
\]

Initial parameter topology remains Sierpinski, but now its semantics is exact: permanent
off-horizon line is simultaneously cycle and boundary, so it carries no surviving class. In the
Poisson model, the open survival tests separate
\((\mathcal B_{\rm P},\Gamma_{\rm sec})\) from falsely exact
\((\Gamma_{\rm sec},\Gamma_{\rm sec})\). Hence arithmetic, geometry, and Fourier spectrum have
noninterchangeable coordinates

\[
 \boxed{\text{arithmetic}=B,\qquad\text{geometry}=Z,\qquad\text{spectrum}=Z/B.}
\tag{6o}
\]

Analytic dagger reverses this flag:

\[
 (B\subseteq Z)^\dagger=(Z^\circ\subseteq B^\circ),
 \qquad
 (Z/B)^\vee\cong B^\circ/Z^\circ.
\tag{6p}
\]

A second dedicated Stage-2 theorem proves dagger is not continuous in one-sided provenance
topology. Minimal bioriented refinement is join of source topology with its dagger pullback. It
also proves positivity-placement no-go: if a nondegenerate Green form makes
\(Z=B^\perp\), then positive-definiteness forces \(B=0\). Therefore nontrivial arithmetic
boundaries cannot live in a positive self-dual cochain geometry. Source Green--Stokes form must be
indefinite, alternating, or relational before exact reduction; positive Hilbert dagger belongs on
\(Z/B\) afterward.

The earlier Scott profile is exactly the cycle projection \((B,Z)\mapsto Z\) of this geometry.

## 6. Frozen source conjecture

`[BOLD CONJECTURE] [XI_POLARIZED_EXCHANGE_HORIZON_LANDING]`

The ordinary-integer Euler--Gamma--co-Poisson source admits a global unpolarized source-normal
partial-\(K\)-labelled exchange realization and a curved positive polarization `(2)` such that:

1. finite power correspondences realize as the actual ramified top-conormal pair;
2. the first-trace essential normal edge \(e_1\mapsto Se_1\) is a tangent-labelled exchange edge;
3. the nondivisive Gamma/co-Poisson/Sonin source-error syzygy admits the dagger-sensitive
   transgression \(\Psi_{\rm PE}\), whose additive shadow is the curved composition comparison;
4. action condensation gives the complete reciprocal-Xi Bockstein before any zero is selected;
5. reduced principal-Cartier base change is strict, conservative, and coefficient-faithful;
6. the framed Cartier image has nonzero projection to the quotient by the always-coherent
   conormal line \(\mathbb Re_1\); survival inside that line alone is excluded;
7. a source-derived coherent system of Stokes null-homotopies places every reduced Xi conormal jet
   in \(H^{(\infty)}\), hence in the pairwise zero locus of \(\mathfrak C_{\rm ex}\);
8. on that zero locus, the descended polarized exchange norm identifies Riemann source inverse
   with Hilbert adjunction; and
9. all constructions and null-homotopies are natural under source aperture and prime-set
   enlargement.

Clauses 2--8 are not consequences of Fisher's universal theorem.  They assert that the actual
arithmetic data instantiate its unpolarized hypotheses, that the curved polarization has the
computed source target, and that its source-natural null-homotopy survives cofinal completion.

## 7. Exact RH consumer

Let \(K_\rho\) be a nonzero reduced Xi principal conormal admitted by Clause 5, transverse by
Clause 6, and landed by Clause 7.  Normalized prime transfer has character

\[
 \lambda_{r,\rho}=r^{\rho-1/2}.
\tag{7}
\]

Its framed modular weight is

\[
 \theta_\rho=2\operatorname{Re}\rho-1.
\]

Clause 7 makes the polarized exchange curvature vanish on the Cartier image, while Clause 6 gives
a class with nonzero projection to \(\mathbb R^2/\mathbb Re_1\).  The maximal-coherent-subspace
classification in the Stage-2 theorem then excludes \(\theta_\rho\ne0\).  Hence

\[
 \theta_\rho=0,
 \qquad
 \operatorname{Re}\rho=\frac12.
\]

Source inversion acts by \(\lambda_{r,\rho}^{-1}\), while Hilbert adjunction acts by
\(\overline{\lambda_{r,\rho}}\).  Clause 8 gives the equivalent same-fibre identity

\[
 \lambda_{r,\rho}^{-1}=\overline{\lambda_{r,\rho}},
 \qquad
 |\lambda_{r,\rho}|=1,
 \qquad
 \operatorname{Re}\rho=\frac12.
\tag{8}
\]

Thus the conjecture implies RH without simplicity by two shadows of the same landing: framed
coherence-rank jump and inverse--adjoint equality.  This is a consumer, not a proof.

## 8. Conjecture--attack ledger

### Loop 1: generic ambidexterity

- **Conjecture:** geometry, spectrum, and arithmetic are the dualizing twist, adjunction, and
  categorical degree of one ambidextrous reporter.
- **Failure:** corpus collision.  This is already the frozen source/reporter ambidexterity law,
  with ramified top-conormal finite blocks formalized.
- **Survivor:** use the 2026 universal exchange theorem to ask which source realization could
  carry that ambidexterity, rather than assuming an invertible dualizing object.

### Loop 2: static three-face object

- **Conjecture:** the missing class is an irreducible triple interaction among arithmetic,
  spectral, and geometric faces.
- **Failure:** corpus collision and no-go.  Source-fracture hypercubes, three-face defects, and
  triadic comparison have already been developed; higher interactions need not be generated by
  arity three.
- **Survivor:** comparison itself must be a morphism in the primitive category, not a higher
  decoration of three completed realizations.

### Loop 3: partial-\(K\) invertibility horizon

- **Conjecture:** RH is the locus where the source tangent twist becomes invertible.
- **Failure:** false rank-one test.  The scalar \(r^{\rho-1/2}\) is invertible at every zero,
  including off-line zeros.  The proved Sonin connection is already flat and invertible.
- **Survivor:** the defect is polarized functoriality—equality of inverse and adjoint—not bare
  invertibility.

### Loop 4: polarized exchange geometry

- **Conjecture:** off-line conormals are exactly those on which the framed arithmetic/Fourier
  polarization fails to descend through the universal exchange category.
- **Proof at rank one:** equation `(5)` and the Stage-2 theorem.
- **Open global attack:** construct the global unpolarized source-normal functor, its curved
  polarization, and conservative Xi base change.  Without that construction, `(5)` is only a
  selector on an already-admitted fibre.

### Loop 5: could this be only RH in categorical notation?

- **Attack:** declare every Xi conormal exchange-admissible.
- **Failure:** circular; by `(5)` this declaration already forces RH.
- **Positive correction:** the horizon landing must be proved before Xi specialization by sending
  the computed first-trace edge to the already-computed source-error syzygy and constructing its
  source Stokes null-homotopy.  This is a concrete morphism construction with independent finite
  restrictions and falsifiers.

### Loop 6: globally functorial polarized exchange

- **Conjecture:** the polarized realization itself is one global exchange functor over the full
  spectral base.
- **Failure:** inconsistent with `(5)`, which is nonzero for every off-critical parameter.  A
  global functor would make the defect vanish identically, not merely on Xi packets.
- **Survivor:** the global object is an unpolarized exchange functor with a curved polarization.
  Arithmetic content is precisely the theorem that reduced Xi Cartier packets land in its derived
  zero locus through a source-natural Stokes null-homotopy.

### Loop 7: any nonzero Cartier landing is enough

- **Conjecture:** a nonzero Xi conormal together with vanishing curved exchange action forces the
  purity line.
- **Failure:** false.  The Stage-2 theorem computes a permanent coherent kernel
  \(\mathbb Re_1\) for every off-critical weight.  A nonzero packet can hide there.
- **Survivor:** criticality is the jump of maximal coherent framed dimension from one to two.
  Source landing must retain a nonzero class in the transverse quotient
  \(\mathbb R^2/\mathbb Re_1\).  This is the precise coefficient-faithfulness condition previously
  hidden inside “nonannihilating landing.”

### Loop 8: any curved nonfunctor is a geometry

- **Conjecture:** a parameterized family of composition defects already defines the missing
  geometry, with its vanishing locus as the horizon.
- **Failure:** underconstrained.  Any desired closed set can be encoded as the zero locus of an
  arbitrary defect, so this would be theatre rather than structure.
- **Survivor:** the global parent must be bioriented: source transfer supplies an oriented/lax
  direction, analytic dagger supplies an antioriented/oplax direction, and their comparison cells
  obey oriented interchange coherence.  The horizon is then the strict-interchange locus of a
  pre-existing coherent structure.  Equation `(5)` is only its rank-one additive shadow.

### Loop 9: the power character is essential

- **Conjecture:** the horizon works only because the Riemann modular gain is the real power
  \(n^{2\operatorname{Re}s-1}\).
- **Failure:** false.  The Stage-2 proof uses only multiplicativity and unit-valuedness.
- **Survivor:** for every characteristic-zero coefficient field, the horizon separates the trivial
  modular character from all nontrivial modular characters and has the same one-versus-two
  coherence-rank jump.  The power law is analytic input converting anomaly triviality into the
  line \(\operatorname{Re}s=w/2\).

### Loop 10: pairwise curvature vanishing is full coherence

- **Conjecture:** once every binary matrix curvature vanishes and the Bianchi identity holds, the
  polarized exchange geometry is strict on that packet.
- **Failure:** unsupported.  Bianchi is a necessary threefold shadow and is automatic for any
  matrix transport; it does not construct oriented interchange cells or their higher homotopies.
- **Survivor:** the exchange horizon carries the descending coherence spectrum `(6b)`--`(6d)`.
  The Stage-2 theorem proves all ordinary higher-word defects stabilize at \(H^{(2)}\); therefore
  any later drop must be genuinely oriented-categorical.  Source mathematics must prove stable
  membership in \(H^{(\infty)}\), so every hidden higher-coherence obstruction becomes a typed,
  falsifiable layer rather than being silently discarded.

### Loop 11: common kernel is the sharpest binary invariant

- **Conjecture:** the permanent line/common-kernel computation exhausts the binary information.
- **Failure:** false.  Every nonzero defect is square-zero with image equal to that same kernel.
- **Survivor:** off horizon, curvature induces an isomorphism from transverse quotient to conormal
  error line and makes the framed block acyclic; at the horizon the differential dies and exchange
  homology jumps to the full plane.  This identifies the target types that a dagger-sensitive
  transgression of the first-trace/source-error exact-couple morphism must realize.

### Loop 12: the source comparison is an untyped null-homotopy

- **Conjecture:** it is enough to ask for a source Stokes null-homotopy of curvature on Xi packets.
- **Failure:** still hides domain, codomain, and conservativity; such a null-homotopy could be
  chosen after seeing the zero set.
- **Survivor:** construct the two-stage pre-divisor composite `(6g)`: the source-normal exact-couple
  morphism followed by a dagger-sensitive exchange transgression.  Cartier base change must induce
  a nonzero map on homology.  The target is proved acyclic off horizon, so this exact source
  theorem—not a metaphor—would force purity.

### Loop 13: source-error syzygy is the exchange differential

- **Conjecture:** the already-computed Gamma/co-Poisson/Sonin source-error syzygy can be placed
  directly as \(\overline D_s\) in `(6g)`.
- **Failure:** contradicted by the corpus's hostile audit.  That syzygy controls connection-error
  curvature; Hermitian mate nonmetricity survives it.
- **Survivor:** retain the flat syzygy as the middle exact-couple object and construct the separate
  transgression \(\Psi_{\rm PE}\) which remembers dagger before cancellation.  Failure of such a
  transgression is a clean falsifier of polarized exchange-horizon geometry.

### Loop 14: the exchange transgression has no computable shadow

- **Conjecture:** after separating the flat syzygy from mate curvature, \(\Psi_{\rm PE}\) is wholly
  unknown.
- **Failure:** corpus collision.  Reciprocal character, relative Hermitian torsion, reduced defect
  \(1-\chi\), mate polarization, and finite Gamma calibration are already computed.  Together with
  the affine different they force `(6h)`; the crossed-cocycle identity is elementary.
- **Survivor:** \(\Psi_{\rm PE}\) has a fixed scalar boundary condition on every prime generator.
  Remaining freedom is only the source-normal exact-couple lift and its higher coherence.  Any
  candidate lift with a different scalar shadow is falsified immediately.

### Loop 15: common-kernel topology is enough

- **Conjecture:** all source-relevant information is contained in descending common kernels
  \(H_x^{(q)}\), so their Scott topology is missing exchange-horizon topology.
- **Failure:** false against a proved corpus model. Secondary Poisson energy has radical
  \(\Gamma_{\rm sec}\), while literal Poisson boundaries form strict subspace
  \(\mathcal B_{\rm P}\subsetneq\Gamma_{\rm sec}\). Kernel topology assigns actual flag and
  falsely exact flag same point.
- **Survivor proved on paper:** replace kernel by provenance flag \(B\subseteq Z\), with lower
  topology on arithmetic boundaries and Scott topology on geometric cycles. Framed survival
  \(v\in Z\setminus B\) is open; inverse image is continuous; general range pushforward is not.
  This isolates source incidence as a singular coordinate rather than another spectral kernel.
- **RH consequence:** source-normal Stokes/Bockstein work must construct \(B\) and a conservative
  map on \(Z/B\). Landing only in \(Z\), even nontrivially, cannot overcome known obstruction.

### Loop 16: impose Hilbert positivity before source reduction

- **Conjecture:** make provenance flag dagger-invariant using one positive-definite Hermitian form
  on cochains, then read spectrum directly.
- **Failure proved on paper:** a Green self-dual flag satisfies \(Z=B^\perp\). Since
  \(B\subseteq Z\), boundary space is isotropic. Positive-definiteness therefore forces \(B=0\)
  and \(Z=V\). Every nontrivial arithmetic boundary is deleted.
- **Topological failure:** annihilator dagger is also discontinuous in one-sided lower--Scott
  topology. Source and analytic variances cannot be identified before comparison.
- **Survivor:** use source-provenance topology first, its minimal bipolar dagger refinement for
  comparison, an indefinite/alternating Green--Stokes relation before quotient, and positive
  Hilbert polarization only on \(Z/B\). Hahn--Banach proves continuous phase separators exist for
  closed \(B\), so open debt is canonical Euler/Gamma-covariant joint reporter, not existence of
  arbitrary separators.

## 9. Falsifiers

1. The ordinary-prime source data do not form the required pullback/exchange diagrams before
   analytic continuation.
2. The relative tangent label of the actual ramified correspondence is not the top-conormal
   different used in `(4)`.
3. The first-trace essential edge and Gamma/co-Poisson syzygy are images of different source
   morphisms or require incompatible topologies.
4. Source-normal completion destroys the exchange comparison or makes it non-strict.
5. Reduced Xi Cartier base change annihilates the exchange edge or creates a new attainment
   class.
6. The Cartier image survives but is contained in the always-coherent line \(\mathbb Re_1\), so
   its transverse framed quotient is zero.
7. No source-natural Stokes null-homotopy of the curved polarization survives reduced Xi Cartier
   base change, or source inverse and analytic dagger differ by a residual Nakayama/modular
   automorphism after Gamma orientation.
8. An off-line generalized-prime system satisfies the same literal ordinary-integer incidence,
   partial-\(K\) tangent, curved polarization, source Stokes null-homotopy, and conservative
   Cartier clauses.
9. The proposed polarization admits no bioriented lax/oplax enhancement satisfying interchange
   coherence, even though its rank-one matrix shadow satisfies the known Bianchi identity.
10. Some reduced Xi packet lies in \(H^{(2)}\) but leaves \(H^{(q)}\) at a finite higher pasting
    dimension, or the coherence spectrum fails to stabilize under aperture enlargement.
11. The flat source-error syzygy admits no dagger-sensitive transgression \(\Psi_{\rm PE}\), or
    every such transgression annihilates the essential transverse quotient after Cartier base
    change.
12. Any construction defines its functor, polarization, or tangent label from Xi zeros or from
   the desired vanishing of `(5)`.

13. The proposed source incidence does not produce a boundary coordinate
    \(B_x^{(q)}\subseteq Z_x^{(q)}\), or its induced map on \(Z/B\) vanishes after Cartier base
    change.

Falsifiers 1--7 kill the RH producer while leaving the rank-one exchange obstruction theorem.
Falsifier 8 kills the proposed arithmetic purity law.  Falsifiers 9--10 kill the claimed geometry;
Falsifier 11 kills its bridge to live source exact couple. Falsifier 12 is circularity.
Falsifier 13 kills provenance-exactness rather than merely its cycle shadow.

## 10. Literature and novelty boundary

Parent mathematics includes six-functor formalisms, correspondence categories, exchange and base
change, Poincare--Verdier duality, Thom twists, partial \(K\)-theory, Grothendieck residue, and
ramified duality.  In particular:

- William Fisher, *Exchange theorems and coherent duality in six functors*,
  <https://arxiv.org/abs/2607.12123>;
- Peter Scholze, *Six-Functor Formalisms*, <https://arxiv.org/abs/2510.26269>;
- Markus Land and Marco Volpe, *Homology manifolds via six functor formalisms*,
  <https://arxiv.org/abs/2607.00236>;
- David Gepner and Hadrian Heine, *Oriented Category Theory*,
  <https://arxiv.org/abs/2510.10504>.

Broad exactness-topology audit also found known parents rather than a pre-existing RH object:

- Chen--Kou--Lyu, *Two topologies on the lattice of Scott closed subsets*,
  <https://arxiv.org/abs/2103.15139>;
- Cerulli Irelli--Feigin--Reineke, *Quiver Grassmannians and degenerate flag varieties*,
  <https://arxiv.org/abs/1106.2399>;
- Bauer--Schmahl, *Efficient Computation of Image Persistence*,
  <https://arxiv.org/abs/2201.04170>;
- Slaftsos--Vitória, *Relative Q-shaped homological algebra*,
  <https://arxiv.org/abs/2602.22986>.

The universal exchange category is Fisher's, not new here.  The generic multiplicative-character
framed-curvature identity is already formalized in the HGT corpus.  The centered-flow capacity card
already isolates triviality of the actual Xi modular cocycle as an RH-equivalent open theorem.
Source--dagger cyclic monodromy already contains the nonzero-quotient warning.  Candidate-new
knowledge is restricted to their conjunction:

\[
 \text{actual top-conormal arithmetic source}
 +\text{partial-}K\text{ exchange tangent}
 +\text{one-sided Hilbert polarization}
 \Longrightarrow
 \text{exact obstruction to exchange-geometrizability}.
\tag{9}
\]

No external priority claim is made. Modular-character triviality, exactness flags, Scott topology,
and lower topology are not
claimed new.  Significance is internal and conditional: `(9)` turns the
source-normal dagger landing from an unstructured request for a miraculous map into the problem of
constructing one unpolarized exchange realization, one computed curved polarization, and one
source Stokes null-homotopy on the Cartier horizon.  It does not prove those objects exist.

Candidate-new structure is mixed-variance assembly forced by strict Poisson graph/range gap:

\[
 \text{source range }B
 \subseteq
 \text{exchange cycles }Z,
 \qquad
 \text{spectral survivor }Z/B.
\tag{9a}
\]

For a self-dual completed Euler source of functional-equation weight \(w\), the same rank-one
calculation replaces \(\chi_s(n)\) by \(n^{2\operatorname{Re}s-w}\) and selects
\(\operatorname{Re}s=w/2\).  This is a general purity template, not a theorem that arbitrary
\(L\)-functions possess the required source exchange realization.

## 11. Next theorem, not next metaphor

`[OPEN CORE] [FINITE_SOURCE_NORMAL_CURVED_K_EXCHANGE_SQUARE]`

At finite prime set, first-trace depth, and Gamma aperture:

1. define the literal source correspondence category and its admissible pullbacks;
2. compute its partial-\(K\) tangent label on the ramified top-conormal generator;
3. construct the unpolarized source-normal and Gamma/co-Poisson exchange functors;
4. construct the positive dagger as a bioriented curved polarization, construct
   \(\Omega_{\rm int}\), prove its lax/oplax triple-interchange coherence, and recover `(5)` as
   its finite framed additive shadow;
5. construct \(\Phi_{\rm src}\) and the distinct dagger-sensitive transgression \(\Psi_{\rm PE}\)
   in `(6g)`, prove that its scalar shadow is forced formula `(6h)`, and recover the
   quotient-to-line contraction `(6f)` only after their composition;
6. construct source boundary coordinate \(B_{\rm src}\subseteq Z_{\rm src}\), map it into target
   flag \(B_s\subseteq Z_s\), and prove or refute that reduced Cartier base change induces a
   nonzero map on quotient homology, including nonzero transverse framed class;
7. construct or refute the source-natural Stokes homotopies making `(6g)` a chain map, compatibly
   with aperture enlargement;
   and
8. compute provenance flags \(B^{(q)}\subseteq Z^{(q)}\) for first nontrivial higher pasting
   dimensions and identify any obstruction to cofinal all-arity exactness as a typed quotient
   class, not a scalar zero condition.

A negative result must classify the missing tangent, exchange, or attainment class and becomes the
positive survivor.

## Gates

- [x] 0 -> 1: proof-independent meta-theory, exact parent category, RH consumer, and falsifiers
- [x] rank-one polarized exchange obstruction paper-proved in dedicated Stage-2 card
- [x] generic ambidexterity, static three-face, and bare partial-\(K\) routes killed
- [x] globally functorial polarized realization falsified; curved polarization correction frozen
- [x] permanent off-critical coherent line classified; bare nonzero landing rejected
- [x] arbitrary curved nonfunctor rejected; bioriented lax/oplax coherence required
- [x] arbitrary unit-valued multiplicative modular character classified
- [x] pairwise-flatness shortcut rejected; descending all-arity coherence spectrum defined
- [x] strict matrix higher-word spectrum proved to stabilize at binary layer
- [x] curvature homology and exact transverse-to-error contraction paper-proved
- [x] abstract homology-conservative source landing criterion paper-proved
- [x] direct syzygy-equals-mate-curvature identification falsified; two-stage bridge required
- [x] scalar Hermitian torsion-to-exchange transgression dependency-closed and identified as prior
  corpus boundary data
- [x] kernel-only Scott geometry falsified by strict Poisson graph/range gap
- [x] provenance-exactness flag topology and specialization law paper-proved in dedicated Stage-2
  card
- [x] inverse-image continuity and general source-range pushforward discontinuity paper-proved
- [x] exactness-flag dagger duality and minimal bipolar topology paper-proved
- [x] positive-definite chain-level self-duality no-go paper-proved
- [x] continuous phase-separator existence isolated from source-canonical reporter construction
- [ ] construct actual source boundary coordinate rather than only geometric cycle kernel
- [ ] construct finite source-normal curved partial-\(K\)-labelled exchange square
- [ ] prove cofinal source-normal strictness
- [ ] prove conservative reduced Xi Cartier horizon landing
- [ ] prove transverse framed quotient survives Cartier landing
- [ ] construct source Stokes null-homotopy on every reduced Xi conormal
- [ ] identify source inverse with Hilbert adjunction on same landed class
- [ ] derive RH
- [ ] external specialist collision audit
- [ ] formalization deferred; no Lean written or built in this research pass

## Log

- 2026-08-08 — Created after hostile corpus audit killed generic ambidexterity and three-face
  formulations.  Fisher's July 2026 universal exchange theorem supplied the parent category.
  Bare partial-\(K\) invertibility failed the off-line scalar test; one-sided polarized exchange
  functoriality survived and was isolated as the exact rank-one obstruction.
- 2026-08-08 — Hostile review killed a global polarized exchange functor: its functoriality would
  contradict the nonzero off-critical curvature.  Replaced it by a global unpolarized exchange
  functor, a curved polarization, and a source-selected derived zero locus with Stokes
  null-homotopy as the exact RH-bearing landing.
- 2026-08-08 — Computed the maximal coherent subspace: it is \(\mathbb Re_1\) off the purity
  line and the full framed plane on it.  Strengthened source admission to transverse framed
  quotient survival; mere nonzero conormal landing is now an explicit falsifier.
- 2026-08-08 — Broad current arXiv audit identified oriented category theory as the correct parent
  for the non-strict polarization.  Rejected an arbitrary curvature zero locus as underconstrained;
  froze source orientation, dagger antiorientation, coherent lax/oplax interchange, and strict
  Cartier horizon as required structure.  The matrix theorem remains only a strict shadow.
- 2026-08-08 — Removed Riemann-specific power-law dependence from the closed shadow.  Proved that
  every nontrivial unit-valued modular character has exactly the permanent coherent line, while
  the trivial character has the full framed plane.  Functional-equation weight now appears as one
  realization of a universal modular-anomaly horizon.
- 2026-08-08 — Rejected binary curvature plus automatic Bianchi as evidence of full geometry.
  Defined the descending all-arity coherence spectrum and exchange-horizon topology.  Pairwise
  rank jump is closed; stable higher-interchange membership is now an explicit source debt.
- 2026-08-08 — Proved that the invariant binary coherent kernel annihilates every ordinary
  higher-word matrix defect.  Any further coherence loss is therefore forced to be genuinely
  oriented/Gray-categorical rather than hidden strict reassociation.
- 2026-08-08 — Upgraded common-kernel warning to an exact homological law: off horizon the
  square-zero curvature has equal kernel and image and contracts transverse quotient isomorphically
  onto the conormal error line; at horizon exchange homology jumps from zero to the full frame.
- 2026-08-08 — Replaced untyped “Stokes annihilates curvature” by the exact pre-divisor chain map
  `(6g)`.  Proved abstractly that any homology-conservative landing in its exchange target forces
  the horizon; construction and Cartier conservativity of the source map remain open.
- 2026-08-08 — Corpus audit rejected direct identification of the flat source-error syzygy with
  mate curvature.  Corrected `(6g)` to a two-stage composite: the existing open exact-couple
  morphism followed by a new dagger-sensitive exchange transgression \(\Psi_{\rm PE}\).
- 2026-08-08 — Recognized the corpus's Hermitian torsion, reduced defect, mate polarization, and
  Gamma calibration as the forced scalar shadow of \(\Psi_{\rm PE}\).  Added the crossed-cocycle
  packaging and exchange factorization; no scalar priority claimed.  Only source-normal lift
  remains.
- 2026-08-08 — Hostile comparison with secondary Poisson graph/range theorem falsified the
  kernel-only Scott geometry. Replaced primitive with provenance flag \(B\subseteq Z\), assigning
  arithmetic to boundary range, exchange geometry to cycles, and Fourier spectrum to \(Z/B\).
  Dedicated Stage-2 theorem proves lower--Scott topology, specialization, homology-survival opens,
  and source-range pushforward discontinuity. Open core is now construction of actual \(B\), not
  another kernel.
- 2026-08-08 — Dagger audit proved one-sided provenance topology is not duality-continuous and
  produced minimal bipolar refinement. Positivity audit proved any positive-definite Green
  self-dual cochain flag has zero boundaries. This forces two-stage order already demanded by live
  corpus: unsquared non-diagonal Green--Stokes provenance first, quotient second, positive Hilbert
  dagger last.
