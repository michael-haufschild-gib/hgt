# Adjoint--duality coincidence on the arithmetic Cauchy nerve

- **ID:** `adjoint-duality-cauchy-nerve-purity-law`
- **Stage:** 1-in-progress
- **Type:** UNIVERSAL PURITY LAW / SOURCE-SPECIFIC RH CONJECTURE
- **Scientific status:** `[ABSTRACT SELECTOR: PARENT MATHEMATICS]`
  `[INTERVAL-CHARACTER TRIPLE REALIZATION: LEAN FORMALIZED]`
  `[FINITE CUBICAL COHERENCE: LEAN FORMALIZED]`
  `[GLOBAL SOURCE CONSTRUCTION: CONJECTURAL]` `[NOT RH]`
- **Parents:**
  - `source-record-relative-hyperrigidity-purity-law.md`;
  - `deninger-bilateral-prime-angle-moderation-selector.md`;
  - `deninger-global-green-energy-radical.md`;
  - `deninger-arithmetic-calderon-green-intermediate-extension.md`;
  - `deninger-unit-amalgamation-derived-lagrangian-enhancement.md`;
  - `deninger-derived-stratum-kummer-arithmetic-coefficient.md`;
  - `hypertranscendental-source-fracture-hypercube.md`;
  - `hypertranscendental-source-face-vanishing-cycle-conservation.md`;
  - `../2-fully-proven/not_new_scientific_knowledge/source-face-observation-cohomology-transmutation.md`.
- **Statement:** positivity and functional-equation reflection impose two
  different laws on the negative prime-angle half of one character.  Positivity
  makes it the adjoint/conjugate of the positive half; reflection makes it the
  multiplicative inverse.  If the two halves are restrictions of one nonzero
  positive source class, their coincidence forces unit modulus and hence the
  critical line.  The missing arithmetic theorem is a polarized
  completion--specialization interchange law.  Every finite prime
  specialization must be retained before the cofinal arithmetic completion;
  the resulting source comparison must then descend strictly, without radial
  leakage, to the already constructed coefficient
  \(H^1_{\rm arith}\simeq M_\zeta\).  The stack of source-selected local
  positive completions is one realization of this interchange record, not the
  law itself.  Zeros are source-effective completion--specialization
  anomalies, not point eigenvectors of an ambient Hilbert operator.

## 1. What the obstruction corpus means

The repeated failures have one common form:

```text
one positive/source chart:
  retains one chiral half but permits interior nonunitary characters;

reflected chart:
  retains the inverse character but may live in a different completion;

scalar or local quotient:
  declares both charts present but forgets whether they are one class;

ambient Hilbert completion:
  makes adjoints honest but dissolves point conormals into continuous spectrum.
```

The missing datum is therefore not another scalar sign or another norm.  It is
the equality, on one source-produced cohomology class, of:

1. the categorical duality induced by Riemann reflection; and
2. the Hilbert adjoint induced by a positive Hodge/Green polarization.

This is the arithmetic analogue of the usual mechanism behind purity:
Poincaré duality supplies an inverse eigenvalue, while polarization identifies
duality with adjunction and therefore supplies its complex conjugate.

## 2. Exact one-character selector

Let \(u\) be the unitary generator of
\(\mathbb C[\mathbb Z]=\mathbb C[u,u^{-1}]\), with \(u^*=u^{-1}\).
Let \(\omega\) be a nonzero positive functional.  Positivity implies
\[
  \omega(a^*)=\overline{\omega(a)}.                         \tag{1}
\]
Suppose one source character \(\lambda\ne0\) supplies both chiral moments:
\[
 \omega(u^n)=\lambda^n,\qquad
 \omega(u^{-n})=\lambda^{-n}\qquad(n\ge1).                 \tag{2}
\]
Applying `(1)` to \(a=u^n\) and comparing with `(2)` gives
\[
 \lambda^{-n}=\overline{\lambda}^{\,n}.                    \tag{3}
\]
Already \(n=1\) yields
\[
 |\lambda|=1.                                              \tag{4}
\]

Equivalently, the \(2\times2\) moment section cannot be a positive
Hermitian section unless inverse reflection and adjoint reflection agree.
No infinite estimate is needed after the common positive source class exists.

For the centered prime character
\[
 \lambda_p(\rho)=p^{1/2-\rho},
\]
equation `(4)` is
\[
 p^{1/2-\operatorname{Re}\rho}=1,
\qquad
\operatorname{Re}\rho=\frac12.                             \tag{5}
\]

This selector is parent reflection-positivity/Hodge theory.  It is not an RH
proof and carries no novelty claim.

## 3. Equivalence of the existing infinity selectors

The corpus's three strongest target selectors are shadows of `(3)`:

1. **bilateral moderation:** the formal coefficients
   \(\lambda^e\), \(e\in\mathbb Z\), have polynomial two-sided growth only
   when \(|\lambda|=1\);
2. **Kakutani/Wold normality:** the coherent radial twist remains in the
   critical product-measure sector only when \(|\lambda|=1\);
3. **Wold--Higgs/Kummer energy:** the coherent logarithmic displacement
   \((\log|\lambda_p|)_p\) has finite all-prime energy only when
   \(|\lambda_p|=1\).

These do not give three independent reasons for RH.  Each tests whether the
reflected half is the adjoint half in a different completion category.  Their
shared missing premise is that the actual Xi conormal, produced before divisor
specialization, enters one common positive reflected object.

The explicit off-line generalized-prime systems explain the boundary:
positive Euler data and a functional equation can construct the two halves,
but not their identification as the adjoint restrictions of one positive
source class.

## 4. Why the present global Green radical is incomplete

Let \(x\) be a global middle cocycle.  Suppose every local Cauchy restriction
is a local boundary:
\[
 r_i x=d a_i.                                               \tag{6}
\]
This does not imply that \(x\) is a global boundary.  On overlaps,
\[
 a_j-a_i
\]
is closed and defines the first descent obstruction.  Choices of primitives
for that obstruction have their own triple-overlap defect, and so on.
Thus the implication
\[
 \text{all local quotient energies vanish}
 \Longrightarrow
 \text{global class is a boundary}                         \tag{7}
\]
requires exactly the conservative boundary law left conjectural in
`deninger-global-green-energy-radical.md`.

The omitted object is not another local chart.  It is the full homotopy
coherence record of the local primitives.  In this project that record is
already algebraically named by:

- the relative Sullivan generators for Steinberg products and higher
  syzygies;
- Rost--Schmid residue/corestriction arrows;
- real-orientation descent;
- the product-formula endpoint;
- Poisson/Fourier correction cells.

A valid energy must be defined on the total Cauchy nerve of these data.  Local
Dirichlet energies occupy simplicial degree zero.  Primitive differences,
higher coherence defects, and endpoint mismatch occupy positive degrees.
Information invisible at one degree is transferred to the next rather than
deleted.

This is the exact Hodge form of the corpus's complementary-record law:

\[
\boxed{
\text{local loss}
\;=\;
\text{higher descent curvature}.
}                                                           \tag{8}
\]

Čech totalization, sheaf Laplacians, and Hodge theory of total complexes are
parent mathematics.  Candidate-new content begins only with the strict
ordinary-prime Euler--Gamma/Tate--Milnor/Calderón realization below.

## 5. Hostile correction: purity is completion descent, not one completion

The corpus now proves two exact no-go theorems which change the target.

First, every finite positive Calderón--Milnor graph/conormal packet is
contractible.  An ordinary derived limit of already-specialized acyclic
packets is again zero.  Hence global \(H^1\) is not a class manufactured by
\(R^1\!\varprojlim\) from those finite fibres.

Second, two unitary completions of the same visible event on one fixed
carrier differ by a unitary supported on the complementary defect sector,
and their relative memories are the strict coboundary
\[
 \mu(U,V)=U^\dagger V,\qquad
 \mu(U,V)\mu(V,W)=\mu(U,W).                                 \tag{9}
\]
All triangular holonomies are therefore trivial.  A globally labelled
family of completions is flat and cannot carry the arithmetic class.

The positive survivor is a local-to-global object with no chosen common
carrier:

```text
local positive Calderón--Milnor completions
  + unitary equivalences of their lost/created defect sectors
  + failure to descend to one global completion
  = arithmetic completion-descent class.
```

The Hilbert metric may vary with the source scale.  A transition is required
to be an isometry between the two source-selected metrics, not a bounded
operator on one fixed Hilbert space.  This is exactly the categorical room
needed for factorial Gamma transport, nonclosed cofinal range, and retained
point conormals to coexist.

Local wild or irregular-Hodge polarization does not prove the claim:
rank-one exponential objects with arbitrary nonzero real slopes can be
polarized.  The new premise is the source-specific descent comparison with
\(\mathscr E_{\rm arith}\), not the existence of polarized nearby cycles.

The already-proved Frobenius homotopy defect
\[
 c_{m,n}=h_{mn}-F_mh_n-a_nh_m                              \tag{10}
\]
is a diagnostic coordinate on this curvature: it is closed and satisfies
the multiplicative two-cocycle identity.  It is not the definition of
arithmetic \(H^1\), and no claim is made that it is nonzero or generates
\(M_\zeta\).

This gives the proposed universal interpretation:

\[
\boxed{
\text{purity}
=
\text{unitary descent of source-selected local completions};
\qquad
\text{off-critical modulus}
=
\text{failure of that descent to preserve polarization}.
}                                                           \tag{11}
\]

Finite leakage is the local defect sector.  Infinite nonattainment is
failure of one common carrier.  Hypertranscendence prevents finite closure of
the descent record.  Functional equation is categorical duality.  Positivity
turns its transition maps into adjoints.  The critical line is the unitary
holonomy locus where duality and adjunction coincide.

General unitary local systems, Hilbert bundles, descent of polarizations, and
Hodge theory with unitary coefficients are parent mathematics.  The
source-specific claim is that the ordinary-prime Euler--Gamma/Tate--Milnor
coefficient constructs this unitary descent object and that its
hypercohomology is the already-proved \(M_\zeta\).

## 5a. Sharper law: polarized completion--specialization interchange

The completion-stack formulation has a tautology risk.  If its local objects
are defined only over the unitary boundary, then conormal faithfulness merely
deletes every nonunitary fibre by definition.  The corpus rules out that move.
For every finite prime packet, an arbitrary coherent radial exponent has a
bounded positive Kummer regulator.  Criticality appears only when the packet
is enlarged through all primes in the strict source topology.

Let
\[
 B_0=\mathbb C[\mathbb Q_{>0}^{\times}]
\]
and let \(C_{\rm src}\) be the independently constructed
Euler--Gamma/Tate--Milnor/co-Poisson source complex.  For an algebraic
quasi-character \(\chi\), write
\[
 \operatorname{Sp}_{\chi}(C)
 =
 C\mathop{\otimes}^{\mathbb L}_{B_0}\mathbb C_\chi
                                                               \tag{12a}
\]
for derived spectral specialization.  Write
\(\operatorname{Comp}_{\rm ar}\) for the source-relative completion which
retains the Wold--Toeplitz ideal, its Gamma/BV transgression, the mixed
\(L^1/L^2\) product-formula boundary, and every Rees rate grade.

There is no general interchange theorem
\[
 \operatorname{Comp}_{\rm ar}\operatorname{Sp}_{\chi}(C_{\rm src})
 \;\simeq\;
 \operatorname{Sp}_{\chi}\operatorname{Comp}_{\rm ar}(C_{\rm src}).
                                                               \tag{12b}
\]
Here \(\operatorname{Comp}_{\rm ar}\) includes strict topological
cohomology, closure of ranges, polarization, and the source-normal Rees
grade.  It is not merely a formal derived functor.

This distinction is forced by the HT source-face corpus.  Derived tensor is
exact and preserves homotopy fibres, so a commutator between derived
rigidification and derived specialization is canonically zero.  The actual
born class is the edge term measuring failure of ordinary/strict cohomology
to commute with derived specialization.  For a one-face parameter \(x\), its
model is
\[
0\longrightarrow H^{-1}(C)/x
\longrightarrow H^{-1}(C\mathop{\otimes}^{\mathbb L}A/(x))
\longrightarrow
\operatorname{Tor}_1^A(H^0(C),A/(x))
\longrightarrow0.                                      \tag{12b+}
\]
Thus `(12b)` must be implemented by a filtered observation complex and its
Tor/Bockstein edge map, not by postulating a nonzero commutator of exact
derived functors.

Its failure is exactly what the completion no-go corpus has been measuring:

```text
specialize first, then complete:
  finite conormal fibre survives, but cofinal prime covariance leaks;

complete first, then specialize in scalar L2:
  covariance survives, but every point fibre disappears;

retain the relative/Rees comparison between both orders:
  ideal transgression, vanishing order, point fibre, and polarization
  can coexist.
```

The correct source theorem must construct `(12b)` first on every finite prime
packet for all quasi-characters, then prove compatibility through the
cofinal prime tower.  It may factor through the unitary boundary only as a
theorem about that strict limit.  It may not be defined only on the unitary
locus.

This yields the sharper universal hunch:
\[
\boxed{
\begin{aligned}
\text{source-effective spectral support}
&=
\text{support where arithmetic completion and spectral specialization}\\
&\quad\text{interchange conservatively and preserve polarization}.
\end{aligned}}                                               \tag{12c}
\]

For a centered coherent character
\[
 \chi_\rho(p)=p^{1/2-\rho},
\]
finite specialization is possible for every \(\rho\).  The proved Kummer
leakage classification shows that the radial part of `(12b)` can descend
strictly through all primes only when
\[
 \operatorname{Re}\rho=\frac12.                              \tag{12d}
\]
Equivalently, in the reflected Hodge reading, functional-equation duality
sends \(\chi\) to \(\chi^{-1}\), while positive adjunction sends it to
\(\overline\chi\).  A nonzero conservative polarized interchange identifies
the two and gives \(\chi^{-1}=\overline\chi\).

Derived completion, base-change comparison maps, Beck--Chevalley defects,
relative cyclic excision, Toeplitz boundary extensions, and Rees modules are
parent mathematics.  Candidate-new content is the arithmetic theorem that
the already fixed \(\Xi\) principal conormal is the conservative spectral
specialization of this one source-relative interchange record.

This formulation also gives an exact role to hypertranscendence.  It does not
imply positivity or criticality.  It rules out replacing the cofinal
interchange record by a finite differential-algebraic closure.  The
all-orders compatibility tower is load-bearing because every finite packet
admits the off-critical radial exponent.

## 5b. Exact transgression law: cohomology is the Bockstein of a missing primitive

The unit-exponential Wold--Calderón theorem gives more than an analogy.  Put
\[
 \rho(q)=q^{-1}T_{\log q},\qquad
 R=\int_0^\infty e^{-c}T_c\,dc .
\]
Its first cell is
\[
 B_q=(I-\rho(q))R                                      \tag{12e}
\]
and satisfies
\[
 B_{qr}=B_q+\rho(q)B_r.                                \tag{12f}
\]
Thus all finite Wold/Euler boundary cells are coboundaries of one common unit
resolvent.  Any construction which supplies \(R\) globally on one source
carrier makes the class flat.  This is the analytic counterpart of the
fixed-carrier unitary-completion flatness theorem.

There is a standard exact mechanism by which `(12e)` can nevertheless create
cohomology after completion.  Let
\[
 0\longrightarrow M_{\rm src}
 \longrightarrow M_{\rm amb}
 \longrightarrow M_{\rm cor}
 \longrightarrow0                                      \tag{12g}
\]
be an invariant strict exact sequence.  Suppose
\(R\in M_{\rm amb}\) but \(R\notin M_{\rm src}\), while
\[
 B_q=R-\rho(q)R\in M_{\rm src}
\]
for every \(q\).  Then \([R]\in M_{\rm cor}\) is invariant, and the connecting
map sends it to the cocycle
\[
 \partial_{\rm Bock}[R]
 =
 [q\longmapsto \rho(q)R-R]
 =
 -[B_q]\in H^1(G,M_{\rm src}).                          \tag{12h}
\]
This is an immediate cochain proof of the long-exact-sequence boundary map.
The class vanishes exactly when a source-continuous primitive can be supplied,
up to an invariant correction.

Equation `(12h)` is the exact common skeleton behind the corpus:

```text
finite packet exactness:
  the primitive exists locally;

ordinary inverse limit of finite cohomologies:
  remains zero because it forgets the primitive's escape;

Rees/corona completion:
  retains the class of the escaping primitive;

Gamma determinant and BV first trace:
  regular and singular readings of its boundary cocycle;

fixed-carrier completion memory:
  a coboundary because one global primitive was supplied;

nontrivial arithmetic H1:
  possible only as the Bockstein of source nonattainment.
```

This gives a more precise universal law than “descent obstruction”:
\[
\boxed{
\text{source cohomology at infinity}
=
\text{polarized Bockstein of a primitive lost under strict completion}.
}                                                         \tag{12i}
\]

Group cohomology connecting maps and completion coronas are parent
mathematics.  The source-specific conjecture is now sharply typed:

1. construct `(12g)` from the actual mixed Kummer/Rees completion and the
   relative Wold--Toeplitz extension;
2. take \(R\) to be the source-selected unit Calderón primitive, not a
   zero-dependent resolvent;
3. identify `(12h)`, including Gamma/BV and all higher cells, with the
   arithmetic residue fibre
   \(\mathscr E_{\rm arith}=\operatorname{Fib}(\partial_{\rm ar}^S)\);
4. prove its middle class is the distinguished principal conormal in
   \(M_\zeta\), with every multiplicity jet nonzero;
5. prove the connecting construction is compatible with the positive
   polarization and functional-equation duality.

This is the Riemann specialization of the corpus conjecture
`HT BOCKSTEIN CONSERVATIVITY`: the arithmetic presentation/observation
complex is one receiver, the Wold--Calderón/Gamma/BV boundary is an
independently typed analytic receiver, and a natural map of complexes must
carry the same characteristic Tor class to the analytic principal-conormal
charge.  Equality of scalar coefficients such as \(1-q^{-1}\) is evidence
for the map but is not the map.

If these hold, the nonzero Bockstein class carries inverse character by
duality and conjugate character by adjunction.  Their equality forces the
unitary locus.  No nonunitary fibre is removed by definition: it is excluded
because its finite specializations fail to arise from one strict polarized
Bockstein class.

## 6. Frozen source theorem

`[CONJECTURE] [XI_POLARIZED_COMPLETION_SPECIALIZATION_INTERCHANGE]`

The completed ordinary-prime Euler--Gamma/co-Poisson source constructs,
before divisor specialization, a stack
\(\mathfrak U_{\rm arith}\) of local polarized
Tate--Milnor/Calderón completions on the arithmetic Cauchy nerve with:

1. **local conservative completion:** every pro-Stein generic, prime packet,
   and real endpoint chart has the source-selected positive completion of its
   actual local coefficient, after augmentation removal;
2. **unitary defect transport:** every overlap map transports the lost source
   defect isometrically to the created target defect.  These maps are between
   scale-dependent fibres and form a homotopy-coherent unitary groupoid; no
   global common carrier is assumed;
3. **complete record:** its descent nerve contains all primitive differences,
   Milnor/Steinberg cells, residues, real orientation, Poisson/Fourier
   corrections, Gamma transgression, and higher compatibility data;
4. **strict source comparison:** the nuclear descent totalization is
   cup- and flow-equivariantly quasi-isomorphic to the proved derived-stratum
   coefficient \(\mathscr E_{\rm arith}\).  Consequently its reduced middle
   cohomology is the Hausdorff group
   \(H^1_{\rm arith}\cong M_\zeta\), with no completion kernel;
5. **adjoint--duality coincidence:** on that descent object, unitary overlap
   adjunction agrees with functional-equation duality, including on each
   principal conormal and its full multiplicity filtration;
6. **conormal conservativity:** every nonzero principal Xi conormal and every
   top multiplicity jet survives as a nonzero descent-holonomy fibre;
7. **source construction:** all local completions, transition maps, and
   comparisons use the integral multiplication source, ordinary primes,
   Gamma transgression, Poisson summation, mixed \(L^1/L^2\) residue topology,
   and real orientation, never a zero list.
8. **finite-first spectral interchange:** before restricting to a unitary
   boundary, every finite prime packet carries a source-defined comparison
   `(12b)` for the full quasi-character family; these comparisons form a
   singular Rees/relative system under prime enlargement.
9. **cofinal no-leakage:** the comparison for the distinguished principal
   conormal descends through every cofinal prime exhaustion in the strict
   arithmetic topology.  Unitary support is concluded from this descent and
   is not imposed on the target category.
10. **Bockstein identification:** the descent class is the connecting image
    `(12h)` of the common unit Calderón primitive in the actual
    source/ambient/corona exact sequence, and this connecting image agrees
    strictly with the principal-conormal class under the comparison with
    \(\mathscr E_{\rm arith}\).

Clause 4 prevents the stack from becoming a decorative unitary object
unrelated to zeta.  Clause 5 is the purity mechanism.  Unlike a postulated
global Green metric, clauses 1--3 specify where positivity lives and why its
nontrivial global information is a descent obstruction rather than a chosen
global completion.

## 7. RH consequence

Meyer/Burnol prime-dilation covariance gives, on the conormal fibre at every
nontrivial zero \(\rho\),
\[
 \lambda_p(\rho)=p^{1/2-\rho}.                              \tag{12}
\]
Clause 6 makes the fibre nonzero.  Clause 5 identifies its reflected negative
character simultaneously with the inverse in `(2)` and the adjoint in `(1)`.
The selector gives \(|\lambda_p(\rho)|=1\), hence `(5)`.  This applies to every
multiplicity jet and proves RH.

## 8. First non-parent theorem

Do not prove another abstract holonomy or local positivity lemma.  Both are
parent mathematics.  The corpus already proves the local unitary-face
Calderón domain, prime extended domain, real orientation domain, and
generic/prime conformal overlap.  Reconstructing those objects would be
rediscovery.

The first source-specific theorem not already present is the
**finite-prime spectral interchange comparison**.  For a finite prime packet
\(P\), let
\[
 C_{{\rm ar},P}
 =
 [\,\mathscr G_\eta\longrightarrow\mathscr D_{{\rm ar},P}[-1]\,]
\]
be the actual restricted arithmetic observation complex.  Let
\(C_{{\rm WC},P}\) be the independently defined reporter complex whose common
primitive is the unit Calderón resolvent \(R\), whose face cells are
\(B_p=(I-\rho(p))R\), and whose relative ideal carries the nested
Gamma/BV character.  The theorem must construct a natural map of filtered
complexes
\[
 \Theta_P:C_{{\rm ar},P}\longrightarrow C_{{\rm WC},P}          \tag{13}
\]
with the following properties:

1. construct both sides of `(12b)` from the restriction of
   \(\mathscr E_{\rm arith}\) and the smooth relative Wold--Toeplitz/Rees
   extension, without choosing a zero;
2. construct their natural comparison on the full finite
   quasi-character torus, including radial characters;
3. identify its ideal boundary with the proved Gamma determinant and BV
   principal-conormal transgression, not merely with their scalar values;
4. realize that boundary as the finite restriction of the Bockstein
   `(12h)` for one source/ambient/corona exact sequence;
5. identify its underlying two-chart complex with the corresponding
   restriction of \(\operatorname{Fib}(\partial_{\rm ar}^S)\);
6. prove compatibility under \(P\subset P\cup\{q\}\), preserving cup,
   centered power action, the full multiplicity filtration, and the mixed
   \(L^1/L^2\) strict/Rees topology.

By unit-amalgamation universal descent, construction of `(13)` should reduce
to one sheafwise Kummer-generator square plus its topology.  The scalar
unit-exponential identity proves the value of that square after Laplace
evaluation; it does not yet prove the sheafwise map.  This is the smallest
honest obstacle.

### Signed finite generator double `[PROVED VALUE-LEVEL BRIDGE]`

The required value-level map is forced.  For a prime \(p\) and
\(m\in\mathbb Z\), put
\[
\begin{aligned}
 \sigma_m(t)&=p^{-m}t,\\
 b_m&=1-p^{-m},\\
 D_m(t)&=\frac{\Phi(t)}{\Phi(p^{-m}t)}.
\end{aligned}                                             \tag{13a}
\]
The determinant formula is read on the common disk where all displayed
arguments of \(\Phi\) lie in its regular domain.
Then
\[
\begin{aligned}
 \sigma_{m+n}&=\sigma_m\sigma_n,\\
 b_{m+n}&=b_m+p^{-m}b_n,\\
 D_{m+n}(t)&=D_m(t)D_n(p^{-m}t).                         \tag{13b}
\end{aligned}
\]
The proof is direct cancellation.  For \(m\geq0\), these are respectively
the Wold scale action, the full \(p^m\)-cell mass, and the nested Gamma
determinant cocycle.  The BV principal-conormal reading is
\[
 J(E_{p^m}a)=b_mJ(a).                                    \tag{13c}
\]
For \(m<0\), `(13a)`--`(13b)` give the unique crossed-cocycle continuation
to the reflected chart:
\[
 b_{-m}=-p^m b_m,\qquad
 D_{-m}(t)=D_m(p^mt)^{-1}.                               \tag{13d}
\]

Thus a signed Kummer residue \(m=\operatorname{ord}_p(a)\) already has one
faithful modular reporter double.  Positive and negative valuations cannot
both be realized by one unilateral Wold carrier; they require the two
reflected charts whose common polarized descent is the conjecture.  This
bridge closes formula and rational-power compatibility at the generator
level.  It does not construct the sheafwise map `(13)`, its strict topology,
or conormal faithfulness.

### Common oriented interval character `[PAPER PROVED]`

The apparent mismatch between the integral Kummer residue \(m\) and the
modular value \(1-p^{-m}\) comes from applying two different characters to
one equivariant interval, not from a failure of the interval boundary.  In
the Laurent group ring define
\[
 \chi_m(u)=
 \begin{cases}
  \displaystyle\sum_{k=0}^{m-1}u^k,&m>0,\\[4pt]
  0,&m=0,\\[4pt]
  \displaystyle-\sum_{k=m}^{-1}u^k,&m<0.
 \end{cases}                                               \tag{13e}
\]
Direct splitting of the oriented interval gives, for all
\(m,n\in\mathbb Z\),
\[
\begin{aligned}
 (1-u)\chi_m(u)&=1-u^m,\\
 \chi_{m+n}(u)&=\chi_m(u)+u^m\chi_n(u),\\
 \chi_{-m}(u)&=-u^{-m}\chi_m(u).                           \tag{13f}
\end{aligned}
\]
This is the virtual associated-graded character of the positive boundary
interval \(B(m)\), or of its oppositely oriented reflected interval when
\(m<0\).  It has three exact realizations:
\[
\begin{array}{rcll}
 \epsilon_1(\chi_m)&=&m,
   &\text{Kummer/localization rank},\\[2pt]
 (1-p^{-1})\chi_m(p^{-1})&=&1-p^{-m},
   &\text{Wold/BV modular mass},\\[2pt]
 \det_\Phi(\chi_m)(t)&=&
   \Phi(t)/\Phi(p^{-m}t),
   &\text{nested Gamma determinant}.
\end{array}                                                \tag{13g}
\]
Here the determinant character is defined layerwise by
\[
 \det_\Phi(\chi_m)(t)=
 \begin{cases}
  \displaystyle\prod_{k=0}^{m-1}D_1(p^{-k}t),&m>0,\\[5pt]
  1,&m=0,\\[3pt]
  \displaystyle\prod_{k=m}^{-1}D_1(p^{-k}t)^{-1},&m<0,
 \end{cases}
 \qquad
 D_1(t)={\Phi(t)\over\Phi(p^{-1}t)}.                       \tag{13h}
\]
Both `(13g)` identities telescope.  Thus arithmetic localization, the
unilateral clock interval, Wold/BV weighting, and the Gamma determinant do
not require a fitted scalar map: they are decategorifications of one
filtered equivariant interval class.  What remains open at one prime is the
source-natural comparison identifying the actual Tate-theta/Kummer
localization morphism with this interval object in the declared strict
Barnes-face topology.

The dependency-closed positive-charge theorem package is formalized in
`GaloisForLFunctions.RHTower.TateKummerWoldGammaIntervalCharacter`:
`tateClockPairing_unitInterval_one_eq_natCast` is the Kummer augmentation,
`unitExponentialWoldCells_eq_intervalBoundary` is the Wold/BV realization,
and `tateIntervalDeterminant_eq_boundary_ratio` is the multiplicative
endpoint telescope.

The interval is not only an associated-graded character.  Let
\[
 V=K^{(\mathbb N)},\qquad
 T_m=\{a:a_0=\cdots=a_{m-1}=0\}=\operatorname{range}S^m .
\]
Restriction to the first \(m\) coordinates is surjective with kernel
\(T_m\), hence gives the canonical linear equivalence
\[
 V/T_m\;\simeq\;K^{\operatorname{Fin}m}.                   \tag{13h+}
\]
Under `(13h+)`, the unilateral forward shift sends the \(k\)-th basis
vector to the \((k+1)\)-st and sends the top vector into the discarded
tail.  Thus it is exactly the nilpotent interval arrow, the typed linear
model of multiplication by \(x\) on \(K[x]/(x^m)\).  This upgrades equality
of \(K\)-classes to equality of the filtered representation with all
successor arrows retained.  It is Lean-formalized by
`tateClockIndBoundaryCoordinateMap_ker`,
`tateClockIndTailQuotientEquiv`,
`tateClockIndBoundaryCoordinateMap_forward_single`, and
`tateClockIndBoundaryCoordinateMap_forward_last`.

The unresolved one-prime statement is now narrower: prove that the actual
analytic nodal class \(x\mapsto\ell_1\) carries its localization module
\(K[x]/(x^m)\) to `(13h+)` naturally over the Barnes face, rather than only
after choosing a local coordinate and a positive chamber.

### Prime commutativity forces higher cells `[PAPER PROVED]`

The one-prime interval is still insufficient to construct \(\Theta_P\).
Let \([g]\) denote the oriented interval edge of a commuting dilation \(g\),
with boundary
\[
 \partial[g]=1-g.
\]
For two dilations \(g,h\), multiplication has two ordered interval paths,
\[
 P(g,h)=[g]+g[h],\qquad P(h,g)=[h]+h[g].                  \tag{13i}
\]
Their scalar boundaries agree because \(gh=hg\), but the oriented paths do
not agree.  With the Koszul orientation
\[
 \partial([g]\wedge[h])
   =(1-g)[h]-(1-h)[g],
\]
one has the exact chain identity
\[
 P(g,h)-P(h,g)=-\partial([g]\wedge[h]).                   \tag{13j}
\]
This is the missing commuting square.  For three primes, the different
square homotopies are themselves related by the boundary of the canonical
three-cube; inductively, a finite prime packet requires the entire cubical
bar/Koszul object, not only its vertices and face edges.

The already proved operator and scalar formulas
\[
\begin{aligned}
 E_{gh}&=E_g+S_gE_hS_g^*
        =E_h+S_hE_gS_h^*,\\
 1-(gh)^{-1}
   &=(1-g^{-1})+g^{-1}(1-h^{-1})
    =(1-h^{-1})+h^{-1}(1-g^{-1})
\end{aligned}                                             \tag{13k}
\]
are decategorified shadows of `(13j)`: they identify the two path images
after the square cell has been forgotten.  Consequently the earlier claim
that unit-amalgamation reduces `(13)` to one generator square is corrected:
one generator square determines the local edge, but naturality under
adjoining and reordering primes requires all cubical coherences.

The square identities are Lean-formalized in the same module as
`primeIntervalEdgeBoundary_pathGH`,
`primeIntervalEdgeBoundary_pathHG`,
`primeIntervalEdgeBoundary_squareBoundary`, and
`primeIntervalPaths_sub_eq_squareBoundary`.

This gives a finite model for the sought comparison.  Its arithmetic side is
the finite Koszul/Čech nerve of the Kummer generators; its analytic side is
the cubical interval object whose one-faces have Wold/BV and Gamma
realizations `(13g)`.  The new finite theorem still required for `(13)` is
that the actual source filtrations realize this abstract cubical model,
including extension arrows, and that the resulting comparison is strict in
the mixed \(L^1/L^2\) Rees topology.

### Decategorified Toeplitz index is too coarse `[CORRECTED PROVED NO-GO]`

A tempting construction sends a Kummer uniformizer to the Toeplitz symbol
unitary, forgets the equivariant interval filtration, and then uses only the
ordinary \(K\)-theory boundary rank.  This decategorified construction loses
the arithmetic power law.  For \(m\geq1\),
\[
 E_{p^m}
 =
 \sum_{k=0}^{m-1}S_p^kE_pS_p^{*k},                       \tag{14}
\]
so an ordinary additive index sees \(m\) defect copies.  The actual
Gamma/BV reporter includes the reciprocal occupation operator and gives
\[
\begin{aligned}
 \operatorname{ResTr}(E_{p^m}Q)
 &=
 (1-p^{-1})\sum_{k=0}^{m-1}p^{-k}\\
 &=1-p^{-m}.                                             \tag{15}
\end{aligned}
\]
For \(m>1\), this is not \(m(1-p^{-1})\).  Therefore `(13)` cannot be an
ordinary nonequivariant boundary rank followed by an untwisted trace or
Chern character.  This does not rule out the filtered equivariant interval
class `(13e)`: that class retains every layer and gives `(15)` under its
modular character.

The positive replacement is already visible in `(12e)`--`(12f)`.  It is a
modular/twisted relative regulator retaining simultaneously:

1. the integral Kummer exponent \(m\);
2. the layer action \(p^{-k}\);
3. the crossed cocycle \(1-p^{-m}\);
4. the regular determinant cocycle
   \(\Phi(t)/\Phi(t/p^m)\); and
5. the BV principal-conormal boundary.

The identity
\[
 1-p^{-(m+n)}
 =
 (1-p^{-m})+p^{-m}(1-p^{-n})                            \tag{16}
\]
is precisely the cocycle law, while ordinary additivity would erase its
modular action.  Twisted cyclic theory and modular index pairings are parent
containers.  The new arithmetic task is the source map `(13)` carrying the
Kummer/Tor Bockstein class to the full cubical interval cocycle, before
applying any one of its scalar characters.

The first RH-bearing step is the subsequent all-prime theorem that the
distinguished principal-conormal comparisons totalize strictly and
conservatively.  The existing leakage theorem then forces `(12d)`.  Failure
must identify a precise comparison radical, nonclosable Rees transition,
lost multiplicity jet, or unrecorded prime-infinity boundary charge.

## 9. Hostile falsifiers

1. The construction chooses one global family of completion operators; `(9)`
   then makes its holonomy flat.
2. The local transition is called unitary only after transporting the metric
   from one chart, rather than deriving both metrics from the source.
3. The descent totalization is not compared to
   \(\operatorname{Fib}(\partial_{\rm ar}^S)\) and therefore defines an
   unrelated unitary local system.
4. Positivity is obtained only after choosing upper/lower zero sectors.
5. Functional-equation reflection and overlap adjunction agree only on scalar
   traces, not on principal conormal cohomology.
6. A multiplicity jet vanishes under descent or completion.
7. An off-line generalized-prime system carries the same ordinary-prime
   integral incidence, source-derived unitary completion stack,
   adjoint--duality comparison, and conormal-faithful strict totalization.
8. The unitary stack is obtained by deleting non-moderate or nonunitary
   fibres.
9. Hypertranscendence is used to infer positivity directly.  Its legitimate
   role is only to rule out a finite coherence truncation of the complete
   source record.
10. The Frobenius homotopy defect is declared to generate arithmetic \(H^1\)
    without a source comparison.
11. The spectral comparison is defined only after restricting to unitary
    characters.  This makes criticality tautological and does not instantiate
    `(12b)`.
12. Finite-packet boundedness is promoted to strict all-prime descent.  The
    explicit Kummer leakage family proves that implication false.
13. The Bockstein primitive or the exact sequence `(12g)` is chosen after
    reading the Xi divisor.  The common unit Calderón primitive and both
    completion functors must be fixed on the source first.
14. The comparison factors through an ordinary additive Toeplitz index or
    untwisted cyclic trace.  Equations `(14)`--`(16)` show that this loses the
    required rational-power covariance.

## 10. Literature boundary

Parent components include reflection positivity for
\((\mathbb Z,\mathbb N,n\mapsto-n)\), positive Hankel operators, Hodge theory
of Hilbert/total complexes, Čech and hypercover descent, cellular sheaf
Laplacians, unitary local systems and harmonic bundles, PTVV Lagrangian
intersections, Calderón projectors, determinant lines, and moderate/rapid
nearby cycles.

Relevant primary parents:

- K.-H. Neeb and G. Ólafsson, *Reflection positivity for the circle group*,
  arXiv:1411.2439;
- M. S. Adamo, K.-H. Neeb, and J. Schober,
  *Reflection positivity and Hankel operators*, arXiv:2105.08522;
- J. Hansen and R. Ghrist, *Toward a spectral theory of cellular sheaves*,
  arXiv:1808.01513;
- T. Pantev, B. Toën, M. Vaquié, and G. Vezzosi,
  *Shifted symplectic structures*, arXiv:1111.3209;
- J. Kaad, *On modular semifinite index theory*, arXiv:1111.6546;
- J. Cuntz, C. Deninger, and M. Laca,
  *C*-algebras of Toeplitz type associated with algebraic number fields*,
  arXiv:1105.5352;
- Cuntz--Quillen excision and the boundary map in periodic cyclic
  cohomology;
- standard Tor edge sequences for ordinary cohomology after derived base
  change.

No novelty is claimed for the selector, unitary completion groupoids, or
polarized descent, Bockstein edge maps, or modular index theory.  Targeted
search found arithmetic Toeplitz/KMS systems and modular twisted index
pairings, but no construction carrying Deninger's Tate--Milnor residue
Bockstein to the Wold--Gamma/BV principal-conormal cocycle and then strictly
to \(M_\zeta\).  Candidate-new content is that source-first arithmetic
comparison, not the parent containers.

## Gates

- [x] identify adjoint--duality coincidence as common purity selector
- [x] prove the one-character selector on paper
- [x] show Kakutani, bilateral moderation, and Higgs energy share that locus
- [x] isolate local-boundary/global-boundary gap as omitted descent record
- [x] rule out ordinary derived limits of specialized acyclic packets
- [x] use fixed-carrier unitary-completion flatness to rule out one global
      completion family
- [x] reject local wild polarization as sufficient for slope-zero purity
- [x] identify Frobenius homotopy defects as diagnostics, not source \(H^1\)
- [x] audit parent reflection-positivity and sheaf-Laplacian literature
- [x] verify local Calderón domains and generic/prime overlap already exist
- [x] reject a unitary-boundary-only formulation as tautological
- [x] identify completion--specialization interchange as the common fracture
- [x] identify Wold--Calderón cocycle as a completion Bockstein
- [ ] construct finite-prime source spectral-interchange comparison
- [ ] construct the strict source/ambient/corona exact sequence
- [ ] identify its relative Wold--Gamma/BV boundary with arithmetic residue fibre
- [ ] iterate through full Sullivan/Milnor and prime-enlargement coherence tower
- [ ] prove strict all-place completion descent with no prime-infinity leakage
- [ ] identify overlap adjunction with functional-equation duality
- [ ] prove conormal and multiplicity-jet descent faithfulness
- [ ] dependency-close and formalize unconditional theorems in Lean
- [ ] prove RH

## 11. Local interval transgression and cofinal Bockstein

The previously untyped one-face comparison is now closed at the exact local divisor-jet level.
For every field \(K\) and \(m\geq 0\), Lean constructs canonical linear equivalences
\[
 K[X]/(X^m)
 \;\simeq\;
 K^{\{0,\ldots,m-1\}}
 \;\simeq\;
 K^{(\mathbb N)}/K^{(\{m,m+1,\ldots\})}.                 \tag{17}
\]
Under `(17)`, the class of \(X^k\) is the \(k\)-th Tate-clock point mass and multiplication by
\(X\) is the common nilpotent forward arrow.  Over \(\mathbb C\), for every nonzero Barnes period
\(\omega\), the same interval injects into the analytic nodal receiver by
\[
 X^k\longmapsto
 \ell_k(z)=
 \exp\!\left({2\pi i k z\over\omega}\right),
 \qquad 0\leq k<m.                                      \tag{18}
\]
Every image in `(18)` is killed by the selected face operator \(T_\omega-1\), and finite packets
remain linearly independent.  Thus the local Kummer jet, Tate tail quotient, and Barnes nodal
charge packet are not merely equinumerous: they are one typed interval representation.

The crucial new finite-to-infinite law is the failure of the truncated forward arrows to be a
morphism of the cofinal interval system.  If
\[
 I_m:K^{m+1}\longrightarrow K^{m+2}
\]
appends a zero top coordinate, \(S_m\) is the truncated forward arrow, and
\(\beta_m\) sends the old top coefficient to the new top vertex, then
\[
 S_{m+1}I_m-I_mS_m=\beta_m.                              \tag{19}
\]
The map \(\beta_m\) has rank one and is nonzero at every stage.  Its analytic realization is
exactly the first excluded charge:
\[
 \ell_1(z)\sum_{k=0}^{m}a_k\ell_k(z)
 =
 \sum_{k=0}^{m}(S_ma)_k\ell_k(z)
 +a_m\ell_{m+1}(z).                                     \tag{20}
\]
Equivalently, for a polynomial \(P\),
\[
 \ell_1\cdot{\cal R}_{m+1}([P])
 =
 {\cal R}_{m+1}([XP])
 +[X^m]P\,\ell_{m+1}.                                   \tag{21}
\]

Equations `(19)`--`(21)` identify the one-prime completion Bockstein without an abstract
surrogate.  Finite nilpotence is produced by deleting \(\beta_m\); the algebraic Ind clock keeps
it as the next charge; scalar Hilbert completion can make its cofinal orbit escape; a correct
enhanced completion must retain its class at infinity.  This is the precise local meaning of
“nonuniform finite exactness creates a boundary class.”

This advance does **not** control the semisimple radial character
\(p^{\rho-1/2}\).  The jet charge \(k\) in `(18)` records nilpotent multiplicity, while zero
location is the independent radial/Rees grading.  Conflating them would turn `(17)` into a false
RH argument.  The remaining global theorem must therefore preserve both gradings:

> **[CONJECTURE — POLARIZED ASYMPTOTIC EXACTNESS.]**  The pre-divisor ordinary-prime
> Tate--Milnor/Poisson source has a strict enhanced totalization in which the cofinal classes
> \(\beta_m\), their full prime cubical coherences, and the semisimple Wold--Gamma radial record
> form one source-generated derived boundary.  Analytic positive graph and arithmetic conormal
> jointly generate its Hodge comparison.  Source reflection is an order-zero equivalence of this
> same boundary object, rather than an equivalence between two separately completed scalar
> shadows.

If constructed source-first, the nilpotent part of this conjecture is now supplied by
`(17)`--`(21)`.  Its semisimple part would feed either dense-resolvent purity or exact reflected
Rees-depth equality and force \(\Re\rho=1/2\).  The first unresolved theorem is not the elementary
bilateral-moderateness selector, which the corpus already proves.  It is the strict all-prime map
from Meyer's pre-divisor conormal quotient into this polarized asymptotic boundary, with no
temperedness, normality, or divisor-selected topology assumed.

Lean file
`formal/GaloisForLFunctions/RHTower/TateKummerWoldGammaIntervalCharacter.lean` now proves:

- `localDivisorJetEquivFiniteInterval`;
- `localDivisorJetEquivTateClockTailQuotient`;
- `localDivisorJetEquivFiniteInterval_X_mul_intertwines`;
- `nodalIntervalSynthesis_injective`;
- `localDivisorJetNodalIntervalRealization_injective`;
- `localDivisorJetNodalIntervalRealization_X_pow`;
- `tateClockFinIntervalForward_inclusion_defect`;
- `tateClockFinIntervalTopBoundary_basis_last_ne_zero`;
- `nodalIntervalSynthesis_topBoundary_basis_last`;
- `nodalIntervalSynthesis_forward_leakage`;
- `localDivisorJetNodalIntervalRealization_X_mul_leakage`.

Direct `lake env lean` verification passes.  Final module build, axiom audit, and lint remain
reserved until the dependency-closed local theorem set stops changing.

## 12. Fourier-fixed Möbius inverse and the massive prime-circle Laplacian

The prime-square comparison has a stronger source lift than equality of principal angles.  For a
prime \(p\), define the valuation-radial function on
\(\mathbb Z/p^2\mathbb Z\)
\[
 g_p(x)=
 \begin{cases}
  1,&p\nmid x,\\
  -p,&p\parallel x,\\
  0,&p^2\mid x.
 \end{cases}                                               \tag{22}
\]
For the unitary additive Fourier transform
\[
 ({\cal F}_pf)(a)
 ={1\over p}\sum_{x\bmod p^2}f(x)e^{-2\pi iax/p^2},
\]
one has the exact fixed-point identity
\[
 \boxed{{\cal F}_pg_p=g_p.}                                \tag{23}
\]
Indeed the unit-residue character sum is \(p(p-1),-p,0\) according as
\(a=0\), \(p\parallel a\), or \(p\nmid a\), while the sum on the nonzero
multiples of \(p\) is \(p-1,p-1,-1\) in the same three cases.  Subtracting
\(p\) times the second sum and dividing by \(p\) gives \(0,-p,1\), exactly
`(22)`.

This fixed vector is not unrelated to the earlier continuation line.  In the notation of the
prime-square Fourier polarization,
\[
 {g_p\over\sqrt{p(p^2-1)}}
 =
 {u_p-\sqrt p\,v_p\over\sqrt{p+1}}
 =c_p.                                                     \tag{24}
\]
Thus the Fourier-fixed continuation vector is the normalized local inverse-Möbius current.
The cyclic three-dimensional additive space with orthonormal basis
\((c_p,t_p,w_p)\) has Fourier matrix
\[
 1\oplus
 \begin{pmatrix}
  -p^{-1}&\sqrt{1-p^{-2}}\\
  \sqrt{1-p^{-2}}&p^{-1}
 \end{pmatrix}.                                          \tag{25}
\]
The projective cyclic space generated by the common line \(u_p^0\), the producer transverse line
\(v_{\infty,p}\), and its normalized leakage has the identical Weyl matrix.  Therefore the unique
marked isometry
\[
 u_p^0\longmapsto c_p,\qquad
 v_{\infty,p}\longmapsto t_p,\qquad
 \text{projective leakage}\longmapsto w_p               \tag{26}
\]
intertwines projective Weyl inversion with the literal prime-square additive Fourier transform.
This upgrades “minimal principal-angle model” to a source-marked unitary equivalence on the full
cyclic continuation--record dilation.

Let \(P\) be a nonempty finite prime set,
\[
 M_P=\prod_{p\in P}p^2,\qquad
 g_P(n)=\prod_{p\in P}g_p(n\bmod p^2).                   \tag{27}
\]
Good--Thomas/CRT factorization and invariance of `(22)` under multiplication by local units give
\[
 {\cal F}_{M_P}g_P=g_P.                                  \tag{28}
\]
For every fixed positive integer \(n\), the net is eventually constant and
\[
 \boxed{\lim_{P\uparrow\mathbb P}g_P(n)=\mu(n)n.}         \tag{29}
\]
If \(n\) is squarefree, each prime divisor contributes \(-p\); if \(p^2\mid n\), the corresponding
factor is zero.  Equation `(29)` identifies the cofinal Fourier-fixed record with the closed
inverse projective cross-Gram symbol
\[
 ({\cal A}^{\circ})^{-1}e_n=\mu(n)n\,e_n.
\]
The inverse graph is therefore not an auxiliary weighted space chosen after seeing the Möbius
diagonal.  It is the pointwise boundary of exact finite additive Fourier fixed points.

The archimedean ordering is also present before a limit is taken.  The crystalline distribution
\[
 {\cal T}_P=\sum_{n\in\mathbb Z}g_P(n)\,
 \delta_{\,n/\sqrt{M_P}}                                  \tag{30}
\]
is exactly Fourier self-dual.  This follows by applying Poisson summation to a periodic coefficient
vector: Fourier transformation changes its weights by the unitary finite transform and changes the
lattice spacing by \(M_P\); the self-dual spatial scale is precisely \(\sqrt{M_P}\).  Equivalently,
\[
 \Theta_P(t)
 :=
 \sum_{n\in\mathbb Z}g_P(n)e^{-\pi n^2t/M_P}
 =
 t^{-1/2}\Theta_P(t^{-1}).                               \tag{31}
\]
Both the zero coefficient and the mean of \(g_P\) vanish, so `(31)` has exponential decay at both
ends.

For \(\Re s>1\), the positive Mellin coefficient is
\[
 G_P(s)
 :=
 \sum_{n\geq1}{g_P(n)\over n^s}
 =
 \zeta(s)\prod_{p\in P}(1-p^{-s})(1-p^{1-s}).            \tag{32}
\]
Consequently
\[
 \Xi_P(s)
 :=
 \pi^{-s/2}\Gamma(s/2)M_P^{s/2}G_P(s)                   \tag{33}
\]
extends to an entire function satisfying
\[
 \Xi_P(s)=\Xi_P(1-s).                                   \tag{34}
\]
For every nontrivial zeta zero, every local factor in `(32)` is nonzero.  Hence every
\(\Xi_P\) retains the complete nontrivial zeta divisor with multiplicity, before a zero is
selected.

The prime-enlargement transition in `(33)` is the exact bilateral operator missing from the
earlier finite clocks.  Put
\[
 \lambda_p(s)=p^{s-1/2}.
\]
Then
\[
\begin{aligned}
 p^s(1-p^{-s})(1-p^{1-s})
 &=\sqrt p\bigl(\lambda_p(s)+\lambda_p(s)^{-1}\bigr)-(p+1)\\
 &=-Q_p(\lambda_p(s)),                                  \tag{35}\\
 Q_p(z)&=p+1-\sqrt p(z+z^{-1}).
\end{aligned}
\]
Thus
\[
 \Xi_{P\cup\{p\}}=-Q_p(\lambda_p)\Xi_P.                 \tag{36}
\]
On the fixed prime circle, with \(S\) the bilateral shift,
\[
 Q_p(S)
 =
 (\sqrt p-S)(\sqrt p-S^*)>0,                            \tag{37}
\]
and
\[
 Q_p(e^{i\theta})=|\sqrt p-e^{i\theta}|^2
 \geq(\sqrt p-1)^2.
\]
Its Green kernel is the exact absolutely convergent Fourier series
\[
 Q_p(S)^{-1}
 =
 {1\over p-1}\sum_{e\in\mathbb Z}p^{-|e|/2}S^e.         \tag{38}
\]
Equations `(35)`--`(38)` identify five previously separate objects:

```text
projective Weyl leakage;
prime-square additive Fourier continuation/record;
closed inverse Möbius cross-Gram;
critical bilateral Tate half-density;
positive massive Green operator on the prime circle.
```

They are one source transition.  Finite truncation deletes its leakage coordinate; projective
compression records its cross-Gram; cofinal pointwise passage produces the unbounded inverse
current; Mellin completion turns it into the Laurent Laplacian `(35)`; the circle Green kernel
retains the missing bilateral half-density record.

### Hostile boundary of the advance

This theorem closes the finite additive--multiplicative comparison but does not yet prove the
moderate Xi landing.

1. The Green series `(38)` is analytic on the whole annulus
   \(p^{-1/2}<|z|<p^{1/2}\).  Every nontrivial-strip character
   \(z=p^{\rho-1/2}\), including an off-line one, lies in this annulus.  A single transition
   therefore selects the strip, not the critical line.
2. Algebraically, every map `(36)` is invertible on every nontrivial zero fibre.  An ordinary
   pro- or Ind-limit of the one-dimensional conormal fibres remains nonzero for all strip zeros.
   Criticality can enter only through the source topology of the all-prime continuation--record
   correspondence.
3. Self-duality of `(30)`--`(34)` is not a positivity theorem.  Functional-equation/crystalline
   counterexamples remain valid falsifiers of any argument using only this symmetry.
4. Pointwise convergence `(29)` does not give convergence of `(30)` or of the normalized finite
   vectors in a scalar Hilbert sector.  The previous orthogonality catastrophe remains and is now
   identified with escape of the inverse comparison current.

The RH-bearing theorem is consequently sharper:

> **[CONJECTURE — SOURCE-STRICT FOURIER--EULER INVERSE LIMIT.]**  The source map from Meyer's
> Poisson quotient to the cofinal system `(33)`--`(38)` extends to a Hausdorff
> continuation--record correspondence whose prime-angle boundary is distributional grade by
> grade, whose Euler-time face is enhanced, and whose transition maps are the literal positive
> operators \(Q_p(S)\).  Every Xi top conormal jet lands nontrivially in this strict inverse limit.

If this holds, the conormal character on every bilateral prime clock is
\(p^{\rho-1/2}\).  Distributional moderation forces its modulus to be one, hence
\(\Re\rho=1/2\).  The new work reduces the conjecture from “find a third completion” to construction
of one named inverse system with explicit finite source objects, exact transition operators,
source-fixed Green kernels, and a pre-divisor Mellin map.  What remains load-bearing is strict
all-prime source landing, not another local matrix identity.

## 13. Radial Green blow-up and the two-ended prime-circle record

The transition in `(35)` is already an operator on the pre-divisor Poisson source.  This removes
one more arbitrary step from the proposed third completion.

Let
\[
 (D_pf)(x)=f(px),\qquad (U_pf)(x)=\sqrt p\,f(px)
                                                                  \tag{39}
\]
on \(L^2(\mathbb R_{>0},dx)\).  Then \(U_p\) is unitary and
\[
 U_p^*=U_p^{-1}.
\]
Define
\[
\begin{aligned}
 A_p
  &:=D_p^{-1}(1-D_p)(1-pD_p)\\
  &=D_p^{-1}-(p+1)+pD_p\\
  &=-Q_p(U_p),                                               \tag{40}\\
 Q_p(U_p)
  &:=(\sqrt p-U_p)(\sqrt p-U_p^*)\\
  &=p+1-\sqrt p(U_p+U_p^*).
\end{aligned}
\]
Thus the reflected Euler deletion is literally the negative massive Hodge Laplacian of normalized
prime dilation.  In particular,
\[
 Q_p(U_p)\geq(\sqrt p-1)^2I
                                                                  \tag{41}
\]
on radial \(L^2\), and
\[
 C_p:=Q_p(U_p)^{-1}
 ={1\over p-1}\sum_{e\in\mathbb Z}p^{-|e|/2}U_p^e             \tag{42}
\]
in operator norm.

### Exact pre-Mellin source factorization

For an even Schwartz source \(f\) with \(f(0)=\widehat f(0)=0\), write
\[
 Zf(x)=\sum_{n\geq1}f(nx).
\]
The normalized dilation commutes with the Poisson operator:
\[
 ZU_pf=U_pZf.                                               \tag{43}
\]
For the prime-square Fourier-fixed coefficient `(22)`, put
\[
 Z_{g_p}f(x)=\sum_{n\geq1}g_p(n)f(nx).
\]
Since
\[
 g_p(n)=1-(p+1)\mathbf1_{p\mid n}+p\mathbf1_{p^2\mid n},
\]
one has
\[
\begin{aligned}
 Z_{g_p}f
  &=(1-(p+1)D_p+pD_p^2)Zf,\\
 D_p^{-1}Z_{g_p}f
  &=A_pZf=-Q_p(U_p)Zf.                                    \tag{44}
\end{aligned}
\]
For a finite prime set \(P\), the operators commute and therefore
\[
 \left(\prod_{p\in P}D_p^{-1}\right)Z_{g_P}f
 =
 (-1)^{|P|}
 \left(\prod_{p\in P}Q_p(U_p)\right)Zf.                  \tag{45}
\]
Under the Mellin convention
\[
 {\cal M}h(s)=\int_0^\infty h(x)x^{s-1}\,dx,
\]
equation `(40)` gives
\[
\begin{aligned}
 {\cal M}(A_ph)(s)
  &=
 \bigl(p^s-(p+1)+p^{1-s}\bigr){\cal M}h(s)\\
  &=
 p^s(1-p^{-s})(1-p^{1-s}){\cal M}h(s)\\
  &=-Q_p(p^{s-1/2}){\cal M}h(s).                         \tag{46}
\end{aligned}
\]
Hence `(44)`--`(46)` are the operator-level source antecedent of `(32)`--`(38)`.  The
prime-square additive Fourier fixed point, reflected Euler deletion, completed Mellin multiplier,
and massive prime-circle Laplacian are not merely spectrally analogous: they are four
realizations of one source endomorphism before a zero is chosen.

### The Hilbert inverse exits the nuclear source through two canonical records

Let \({\cal H}_-\) be Meyer's faster-than-every-power radial source.  Equivalently, after the
half-density logarithmic change
\[
 ({\cal L}f)(t)=e^{t/2}f(e^t),
\]
its elements and all derivatives decay faster than every exponential as
\(t\to\pm\infty\).  Formula `(42)` is bounded on \(L^2\), but it does not preserve
\({\cal H}_-\).

Indeed, for \(f\in{\cal H}_-\), `(42)` is the pointwise absolutely convergent formula
\[
 (C_pf)(x)
 =
 {1\over p-1}
 \left(
  \sum_{e\geq0}f(p^ex)
  +
  \sum_{e\geq1}p^{-e}f(p^{-e}x)
 \right).                                                \tag{47}
\]
For \(1\leq y<p\), define the two multiplicative periodizations
\[
\begin{aligned}
 B_{p,0}f(y)
  &:={1\over p-1}\sum_{j\in\mathbb Z}f(p^jy),\\
 B_{p,\infty}f(y)
  &:={y\over p-1}\sum_{j\in\mathbb Z}p^jf(p^jy).
                                                               \tag{48}
\end{aligned}
\]
Both series converge with all logarithmic derivatives and extend to smooth functions on the
prime circle
\[
 \mathbb R_{>0}/p^{\mathbb Z}.
\]

`[PAPER-PROVED — RADIAL GREEN BOUNDARY LAW]` Uniformly with all logarithmic derivatives on
\(1\leq y<p\),
\[
\begin{aligned}
 (C_pf)(p^{-N}y)&\longrightarrow B_{p,0}f(y),\\
 p^Ny\,(C_pf)(p^Ny)&\longrightarrow B_{p,\infty}f(y).
                                                               \tag{49}
\end{aligned}
\]
Moreover,
\[
 C_pf\in{\cal H}_-
 \quad\Longleftrightarrow\quad
 B_{p,0}f=B_{p,\infty}f=0.                              \tag{50}
\]
Consequently
\[
 Q_p(U_p){\cal H}_-
 =
 \ker(B_{p,0},B_{p,\infty}).                            \tag{51}
\]

To prove `(49)`, substitute \(x=p^{-N}y\) and \(x=p^Ny\) into `(47)` and reindex.  Faster-than-
every-power decay gives dominated convergence, including after every logarithmic derivative.
If both limits vanish, subtract the complete bilateral sums in `(48)` from the two one-sided
sums in `(47)`.  What remains is a tail of a faster-than-every-exponential sequence at each end,
so \(C_pf\in{\cal H}_-\).  The converse follows directly from `(49)`.  Since \(C_p\) is the
two-sided \(L^2\) inverse of \(Q_p(U_p)\), `(51)` follows.

The maps in `(48)` are continuous.  Therefore the local Green blow-up
\[
 {\cal E}_p:=C_p({\cal H}_-)\subset L^2(\mathbb R_{>0},dx)
                                                                  \tag{52}
\]
has a canonical Hausdorff boundary quotient
\[
 {\cal E}_p/{\cal H}_-
 \cong
 {\cal H}_-/Q_p(U_p){\cal H}_-
 \hookrightarrow
 C^\infty(\mathbb R_{>0}/p^{\mathbb Z})^{\oplus2}.       \tag{53}
\]
The two components are the \(s=0\) and \(s=1\) indicial records of the reflected Euler operator.
Normalized additive Fourier transform conjugates \(U_p\) to \(U_p^{-1}\), hence commutes with
\(Q_p(U_p)\) and induces the functional-equation involution on `(53)`.  Determining its explicit
matrix on the two boundary profiles is a local Tate-scattering calculation; no formula for that
matrix is used here.

### What this means

The missing record is not created by an abstract \(\lim^1\).  It is already the concrete failure
of a bounded Hilbert Green inverse to preserve the source's nuclear decay:
\[
\begin{array}{c}
 Q_p(U_p)^{-1}\text{ bounded on radial }L^2\\
 \text{but}\\
 Q_p(U_p)^{-1}{\cal H}_-\not\subset{\cal H}_-,
\end{array}
\qquad
\text{lost part}=
\text{two smooth prime-circle boundary records}.        \tag{54}
\]
This is the local form of the proposed universal law:

> **Completion--record conservation.**  When a source operator becomes invertible after Hilbert
> completion, the quotient between its Hilbert Green domain and its nuclear source domain is the
> complementary boundary record erased by scalar completion.  Reflection acts on the complete
> Green graph, not on either scalar shadow separately.

For a finite prime packet \(P\), the commuting operators \(Q_p(U_p)\) give a canonical iterated
Green blow-up and a cubical normal-crossing boundary assembled from the pairs `(48)`.  This is the
semisimple radial counterpart of the nilpotent interval/Bockstein cube in §11.  The two axes now
belong to one finite source construction:

```text
local divisor multiplicity jets
  -> nilpotent interval transgression / Bockstein faces;

reflected Euler dilation
  -> massive Green inverse / prime-circle faces.
```

### Hostile boundary and sharpened open core

The local theorem does not yet land a Xi conormal.

1. The two boundary profiles in `(48)` are endpoint records of one source function.  They do not
   by themselves identify the complete nontrivial divisor quotient.
2. Although \(Z\) commutes with every \(Q_p(U_p)\) on the nuclear source, extending the Poisson
   embedding to the iterated Green blow-ups requires summing functions with the endpoint tails
   `(49)`.  Ordinary Poisson summation does not justify that extension.
3. Quotienting the numerator and denominator Green blow-ups before proving this extension may
   manufacture or erase boundary classes.  This is exactly the base-change defect excluded by the
   acyclic-finite-fibre no-go.
4. A finite packet has a finite cubical boundary.  The all-prime object still needs an
   exhaustion-independent strict topology and an enhanced Euler-time face.
5. Distributional moderation of a nonzero divisor character on any prime circle would force the
   critical line, but proving that such a character is the boundary of the actual Meyer class is
   still the RH-bearing source theorem.

The open core is now a specific extension problem:

> **[CONJECTURE — GREEN--POISSON BOUNDARY SEWING.]**  The strict Poisson embedding extends
> functorially from the nuclear source pair to the cofinal cubical Green blow-ups generated by
> `(52)`, including the Fourier-exchanged endpoint records `(48)`.  Its quotient map is
> conservative on every top Xi conormal jet and takes each finite multiplicity grade to a
> finite-order distribution on every prime-circle face.

If this theorem holds, the boundary character at a zero \(\rho\) is
\(p^{\rho-1/2}\).  A finite-order distribution on the bilateral prime circle has polynomial
Fourier growth, so \(|p^{\rho-1/2}|=1\) and \(\Re\rho=1/2\).

### Collision audit

The parent ingredients are standard: translation Green kernels, smooth periodization of rapidly
decreasing functions, Mellin diagonalization of dilation, and Poisson/Tate functional equations.
Targeted searches found work on Mellin--Schwartz algebras, zeta-integral Schwartz spaces, and
periodic Gelfand--Shilov operator complexes, but no source identifying `(22)`, `(40)`, `(44)`,
and the two-ended quotient `(53)` as one prime-square Fourier--Euler boundary law.  No external
priority claim is made.  The RH-bearing Green--Poisson sewing conjecture remains unaudited
mathematics, not a theorem.

## 14. Common-indicial resonance and the arithmetic middle-extension law

The finite-prime boundary is not a transverse product of unrelated circles.  All normalized prime
Laplacians act on the same archimedean logarithmic coordinate and have the same two indicial
walls.  This produces a resonance that was invisible in the scalar one-prime analysis.

For a finite nonempty prime set \(P\), put
\[
 d=|P|,\qquad
 C_P=\prod_{p\in P}Q_p(U_p)^{-1},
                                                                  \tag{55}
\]
and define the Mellin denominator
\[
\begin{aligned}
 R_P(s)
  &:=\prod_{p\in P}\bigl(p+1-p^s-p^{1-s}\bigr)\\
  &=(-1)^d
    \prod_{p\in P}p^s(1-p^{-s})(1-p^{1-s}).              \tag{56}
\end{aligned}
\]
On the critical Mellin line,
\[
 {\cal M}(C_Pf)(s)=\frac{{\cal M}f(s)}{R_P(s)}.           \tag{57}
\]

### Finite-prime common-indicial resonance theorem

`[PAPER-PROVED]` The zero divisor of \(R_P\) on the two boundary lines is:

1. an order-\(d\) zero at \(s=0\);
2. an order-\(d\) zero at \(s=1\);
3. for each \(p\in P\), simple zeros
   \[
    {2\pi ik\over\log p},\qquad
    1+{2\pi ik\over\log p},
    \qquad k\in\mathbb Z\setminus\{0\}.                  \tag{58}
   \]

There are no other coincidences among the nonzero points in `(58)`.  Indeed, a coincidence for
distinct primes would give
\[
 k\log q=\ell\log p
\]
with nonzero integers \(k,\ell\), hence \(q^k=p^\ell\), impossible by unique factorization.

At the two common roots,
\[
\begin{aligned}
 p+1-p^s-p^{1-s}
   &=(p-1)\log(p)\,s+O(s^2),\\
 p+1-p^s-p^{1-s}
   &=-(p-1)\log(p)\,(s-1)+O((s-1)^2).                   \tag{59}
\end{aligned}
\]
Therefore, unless cancelled by the corresponding source Mellin jet,
\[
\begin{aligned}
 {{\cal M}f(s)\over R_P(s)}
  &=
  {{\cal M}f(0)\over
    s^d\prod_{p\in P}(p-1)\log p}
  +O(s^{1-d}),                                         \tag{60}\\
 {{\cal M}f(s)\over R_P(s)}
  &=
  {(-1)^d{\cal M}f(1)\over
    (s-1)^d\prod_{p\in P}(p-1)\log p}
  +O((s-1)^{1-d}).                                     \tag{61}
\end{aligned}
\]
Mellin inversion turns `(60)`--`(61)` into logarithmic endpoint jets through degree \(d-1\):
\[
\begin{aligned}
 C_Pf(x)
  &=
  \sum_{j=0}^{d-1}a_{0,j}(f)(\log x)^j
  +\text{prime-periodic sidebands}
  +o(1)
       &&(x\downarrow0),\\
 C_Pf(x)
  &=
  x^{-1}\left[
   \sum_{j=0}^{d-1}a_{\infty,j}(f)(\log x)^j
   +\text{prime-periodic sidebands}
  \right]
  +o(x^{-1})
       &&(x\uparrow\infty).                              \tag{62}
\end{aligned}
\]
Here the sidebands have frequencies \(2\pi k/\log p\) from `(58)`.  For a fixed finite \(P\),
the source Mellin transform decays faster than every power on vertical lines.  Lower bounds for
nonzero linear forms \(k\log q-\ell\log p\) prevent the other factors in `(56)` from becoming
superpolynomially small at a sideband pole.  Hence the residue coefficients decay rapidly and
the sideband profiles are smooth.

The exact leading coefficient at the zero wall is
\[
 a_{0,d-1}(f)
 =
 {(-1)^{d-1}{\cal M}f(0)\over
  (d-1)!\prod_{p\in P}(p-1)\log p},                    \tag{63}
\]
with the analogous reflected formula at \(s=1\).  The sign convention in `(63)` follows from
\(x^{-s}=\exp(-s\log x)\).

### Semisimple and nilpotent records are one object

Equation `(58)` is the semisimple record: each prime contributes its own circle-frequency family,
and rational independence of the prime logarithms keeps the finite-prime phase corank equal to
\(d\).

Equations `(60)`--`(63)` are the nilpotent record: every prime factor meets at the same two
half-density walls, so prime enlargement raises the length of one common logarithmic Jordan jet.
Thus the earlier two-axis picture has a single source:

```text
independent nonzero indicial frequencies
  = semisimple prime-angle / Kronecker record;

common roots at 0 and 1
  = nilpotent logarithmic jet / interval-Bockstein record.
```

This does not collapse infinite prime corank to one archimedean generator.  The corpus
archimedean-corank no-go remains decisive.  One radial flow carries an unbounded common jet order,
while the sideband families retain the independent prime-log directions.  Flow dimension one and
prime corank infinity coexist in `(56)`.

As \(P\) grows, the common indicial order \(d\) is unbounded.  Any cofinal object retaining all
finite source records must therefore be:

1. infinite-order or enhanced in the common Euler/Poisson boundary variable;
2. distributional and finite-order grade by grade in each compact prime-angle variable;
3. non-scalar, because the independent prime sidebands cannot be compressed into the one radial
   flow without losing the corank proved by the HT corpus.

These are exactly the three regularity requirements reached independently by the Mertens
adiabatic-corner, prime-Schwartz moderation, source-rigged-clock, and HT minimality cards.

### Universal interpretation

The common source law now has a concise form.

> **[CONJECTURE — POLARIZED COMMON-INDICIAL MIDDLE-EXTENSION LAW.]**
> For every source-minimal completed Euler--Poisson object, form the cofinal Green graph of its
> reflected local Euler operators before Mellin scalarization.  Suppose:
>
> 1. all finite-place Green factors share the two source-dual half-density indicial walls;
> 2. the independent local sidebands retain the integral place lattice;
> 3. source Fourier duality exchanges the two walls and preserves the complete Green graph;
> 4. the common-root Rees filtration and the sideband distribution filtration are retained before
>    taking the quotient by the source constraint.
>
> Then the source quotient is the unique polarized intermediate extension between the two
> boundary Green objects.  Its principal conormal representation is moderate in the compact
> sideband variables and enhanced only in the common indicial variable.

For the completed ordinary-prime source, the concrete finite Green graphs are `(44)`--`(57)`,
the source constraint is Meyer's strict Poisson embedding, and the proposed intermediate
extension is denoted
\[
 {\rm IC}_{\rm arith}(\partial{\cal G}_{\rm Euler}).
                                                                  \tag{64}
\]
The zeta-specific assertion is
\[
 M_\zeta
 \cong
 {\rm IC}_{\rm arith}(\partial{\cal G}_{\rm Euler})               \tag{65}
\]
as a strict, source-effective, Fourier-polarized conormal representation, with no loss of any
top multiplicity jet.  Equation `(65)` is a truth-hunch; no proof method is included in the
conjecture.

If `(65)` holds, a zero \(\rho\) supplies on the \(p\)-sideband circle the centered character
\[
 e\longmapsto p^{e(\rho-1/2)}
\]
times a polynomial in \(e\) of degree below its multiplicity.  Intermediate-extension
moderation makes this a finite-order circle distribution.  Its Fourier coefficients must have
polynomial two-sided growth, so
\[
 |p^{\rho-1/2}|=1,\qquad \Re\rho={1\over2}.              \tag{66}
\]
Thus RH is the purity statement for `(65)`.

### Why the preceding failures are shadows of this law

The law simultaneously reinterprets the corpus:

1. **Finite clocks leak.**  They retain a finite piece of `(62)` but truncate the Green graph
   before its complementary boundary record is attached.
2. **Scalar adelic \(L^2\) loses zeros.**  Every \(Q_p(U_p)\) is boundedly invertible there, so
   scalar completion identifies source with Green domain and discards quotient `(53)`.
3. **Ordinary pro-limits are zero or RH-blind.**  They specialize before taking the
   source/Green base-change defect and therefore see only invertible finite fibres.
4. **Functional equation alone is insufficient.**  It exchanges the two walls but does not impose
   the intermediate-extension or moderation condition.
5. **Positivity alone is insufficient.**  \(Q_p(U_p)>0\) throughout the Hilbert middle, including
   for source systems whose singular boundary quotient carries off-line zeros.
6. **Hypertranscendence alone is insufficient.**  It detects unbounded source complexity but not
   whether the conormal occupies the moderate middle extension or an enhanced off-wall sector.
7. **Kakutani and projective leakage detect the wall but do not land the source.**  They are norm
   and finite-clock shadows of the same sideband moderation in `(64)`.
8. **Nilpotent interval/Bockstein and semisimple prime angle were repeatedly separated.**
   Equations `(58)`--`(63)` show that both are indicial parts of the same reflected Euler Green
   operator.
9. **Generalized-prime countermodels survive the old axioms.**  They need not carry the integral
   independent sideband lattice together with the source-effective middle-extension comparison
   `(65)`.

The missing theorem is no longer an unexplained sign or a hand-chosen topology.  It is the
source-derived identification `(65)`.  Proving only that a middle extension can be defined is
theatre; the work must construct its comparison with Meyer's quotient from `(44)`, prove
strictness under cofinal prime enlargement, and prove noncensorship of every Xi conormal jet.

### Literature boundary

Parent theories include Mellin methods for \(q\)-difference equations, indicial/Fuchsian
asymptotics, smooth periodization, Gelfand--Shilov solvability, Tate zeta integrals, perverse
intermediate extensions, and the Connes--Consani scaling Hamiltonian.  Targeted searches found no
statement identifying the finite Fourier-fixed source `(22)`, the reflected dilation Laplacians
`(40)`, the order-\(|P|\) common indicial resonance `(60)`--`(63)`, and Meyer's complete zeta
quotient as the single arithmetic middle-extension problem `(65)`.  No priority claim is made.

## 15. Finite Green--Poisson sewing is canonical; the raw Ind-limit is not pure

The extension part of the Green--Poisson conjecture can be constructed at every finite prime
stage without summing the endpoint tails directly.

Write
\[
 Q_P=\prod_{p\in P}Q_p(U_p),\qquad C_P=Q_P^{-1}
                                                                  \tag{67}
\]
on radial \(L^2\).  For either member \({\cal H}_\bullet\) of Meyer's strict Poisson pair, define
the Green-blown source space
\[
 {\cal E}_{\bullet,P}:=C_P({\cal H}_\bullet)              \tag{68}
\]
with the transported nuclear topology for which
\[
 Q_P:{\cal E}_{\bullet,P}\xrightarrow{\sim}{\cal H}_\bullet
                                                                  \tag{69}
\]
is a topological isomorphism.  Since \(Q_P{\cal H}_\bullet\subset{\cal H}_\bullet\),
\[
 {\cal H}_\bullet\subset{\cal E}_{\bullet,P}\subset L^2.  \tag{70}
\]

Let
\[
 Z:{\cal H}_\cap\longrightarrow{\cal H}_-
\]
be Meyer's strict Poisson embedding.  Every normalized dilation commutes with \(Z\), hence so do
\(Q_P\) and \(Z\).  Define
\[
 Z_P^{\rm G}
 :=
 C_PZQ_P:
 {\cal E}_{\cap,P}\longrightarrow{\cal E}_{-,P}.         \tag{71}
\]

`[PAPER-PROVED — FINITE GREEN--POISSON SEWING]`

1. \(Z_P^{\rm G}\) is a strict closed embedding.
2. It extends the actual Poisson map:
   \[
    Z_P^{\rm G}f=Zf\qquad(f\in{\cal H}_\cap).             \tag{72}
   \]
3. The diagram
   \[
   \begin{CD}
    {\cal E}_{\cap,P} @>{Z_P^{\rm G}}>> {\cal E}_{-,P}\\
    @V{Q_P}V{\sim}V @V{Q_P}V{\sim}V\\
    {\cal H}_\cap @>{Z}>> {\cal H}_-
   \end{CD}                                               \tag{73}
   \]
   commutes.
4. Therefore
   \[
   0\to{\cal E}_{\cap,P}
     \xrightarrow{Z_P^{\rm G}}
     {\cal E}_{-,P}
     \to M_{\zeta,P}^{\rm G}
     \to0                                                 \tag{74}
   \]
   is strict exact and
   \[
    M_{\zeta,P}^{\rm G}\cong M_\zeta                     \tag{75}
   \]
   as a nuclear source quotient.

The proof is conjugation of Meyer's strict sequence by the topological isomorphisms `(69)`.
For `(72)`,
\[
 C_PZQ_Pf=C_PQ_PZf=Zf.
\]
Thus the extension is not an arbitrary continuation of a divergent Poisson sum; it is the unique
extension making `(73)` commute.

### Prime-enlargement compatibility

If \(q\notin P\), then
\[
 {\cal E}_{\bullet,P}\subset{\cal E}_{\bullet,P\cup\{q\}},
                                                                  \tag{76}
\]
because \({\cal H}_\bullet\subset C_q{\cal H}_\bullet\).  On the smaller space,
\[
 Z_{P\cup\{q\}}^{\rm G}=Z_P^{\rm G}.                     \tag{77}
\]
Indeed, for \(f=C_Ph\),
\[
\begin{aligned}
 C_PC_qZQ_qQ_Pf
  &=C_PC_qZQ_qh\\
  &=C_PZh.
\end{aligned}
\]
Hence the finite Green source maps form a literal cofinal system, not merely isomorphic
stagewise copies.

Under the coordinates `(69)`, the inclusion `(76)` is the closed source operator
\[
 Q_q:{\cal H}_\bullet\longrightarrow{\cal H}_\bullet.    \tag{78}
\]
The one-prime boundary law `(51)` identifies its range as the kernel of two continuous boundary
maps, so the inclusion is strict.  Consequently the strict final union
\[
 {\cal E}_{\bullet,\mathrm{fin}}
 =
 \underset{P\Subset\mathbb P}{\operatorname{colim}^{\rm str}}
 {\cal E}_{\bullet,P}                                    \tag{79}
\]
is a canonical Hausdorff source-rigged carrier with compatible Poisson map
\[
 Z_{\mathrm{fin}}^{\rm G}:
 {\cal E}_{\cap,\mathrm{fin}}
 \longrightarrow
 {\cal E}_{-,\mathrm{fin}}.                              \tag{80}
\]

This closes three formerly conjectural interfaces:

```text
finite source Green domain:       constructed;
finite Poisson boundary sewing:   constructed;
prime-order/exhaustion coherence: constructed algebraically and strictly.
```

### Hostile theorem: final topology retains every strip fibre

The construction is not yet the arithmetic middle extension.  Identify each quotient in `(74)`
with \(M_\zeta\) using \(Q_P\).  Under prime enlargement, the induced transition is
\[
 [h]\longmapsto[Q_qh].                                   \tag{81}
\]
At a zero \(\rho\), its top conormal jet transforms by the nonzero scalar
\[
 Q_q(q^{\rho-1/2})
 =
 q+1-q^\rho-q^{1-\rho}.                                 \tag{82}
\]
For \(0<\Re\rho<1\), `(82)` cannot vanish: its two factored zeros lie on the boundary lines
\(\Re s=0,1\).  Therefore every nontrivial strip zero survives every finite transition and the
algebraic system `(81)`.

More strongly, the final locally convex topology in `(79)` imposes continuity stage by stage but
no uniform moderation across growing \(P\).  A compatible family of continuous conormal
functionals is therefore admitted for every strip zero.  Thus:
\[
\boxed{
\text{strict finite Green--Poisson Ind-limit is Hausdorff and source-faithful,
but RH-blind.}}
                                                                  \tag{83}
\]

The positive survivor is exact.  The missing third completion is a completion of `(79)`, not a
replacement for it.  It must impose one cofinal bornology coupling:

1. the growing common-root jet order in `(60)`--`(63)`;
2. the independent prime-sideband directions in `(58)`;
3. the source-normal boundary scale from the Wold/BV cylinder law;
4. Fourier exchange of the two indicial walls.

Imposing arbitrary uniform boundedness would merely restate prime-Schwartz temperedness and hence
RH.  The next theorem must derive the middle bornology from these four already-source-defined
structures.

## 16. The Green middle is exactly the critical Wold--Szegő--Poisson sector

The one-prime Green inverse in Section 13 is not a new third completion.  It is an operator
presentation of a critical sector already constructed elsewhere in the corpus.  The exact
identification is nevertheless useful because it joins the radial Green graph to the literal
valuation source rather than only to a scalar Poisson kernel.

Put
\[
 r_p=p^{-1/2},\qquad
 v_p(k)=\sqrt{1-r_p^2}\,r_p^k\quad(k\geq0),              \tag{84}
\]
and let \(S\) be the unilateral shift on \(\ell^2(\mathbb N_0)\).  Then
\[
 \|v_p\|=1,\qquad
 \langle v_p,S^e v_p\rangle=r_p^e\quad(e\geq0).          \tag{85}
\]
Equivalently, the Hardy outer function
\[
 h_p(z)=\frac{\sqrt{1-r_p^2}}{1-r_pz}                   \tag{86}
\]
has coefficient vector \(v_p\) and boundary density
\[
 |h_p(e^{i\theta})|^2
 =
 P_{r_p}(\theta)
 :=
 \frac{1-r_p^2}{|1-r_pe^{i\theta}|^2}.                  \tag{87}
\]
The Fourier coefficients of `(87)` are \(r_p^{|e|}\).  Comparing with `(45)` gives the exact
functional-calculus identity
\[
 \boxed{\quad
 (p-1)C_p=P_{p^{-1/2}}(U_p).
 \quad}                                                  \tag{88}
\]
Indeed
\[
 Q_p(U_p)
 =p\bigl(1-r_pU_p\bigr)\bigl(1-r_pU_p^\ast\bigr),
\]
and the reciprocal of its symbol is \((p-1)^{-1}P_{r_p}\).

`[PAPER-PROVED — GREEN/WOLD/SZEGŐ IDENTIFICATION]`

Equations `(84)`--`(88)` say that the following are one local object in three polarizations:

```text
coefficient polarization:
  the Wold valuation half-density
  sqrt(1-p^(-1)) p^(-k/2);

Hardy boundary polarization:
  the outer vector sqrt(1-p^(-1))/(1-p^(-1/2)z);

radial Green polarization:
  the normalized inverse (p-1)Q_p(U_p)^(-1).
```

For a finite prime set \(P\), tensoring gives
\[
 \nu_P=\bigotimes_{p\in P}P_{p^{-1/2}}(\theta_p)
                  \frac{d\theta_p}{2\pi},               \tag{89}
\]
whose Fourier coefficient at \(e=(e_p)_{p\in P}\in\mathbb Z^P\) is
\[
 \widehat\nu_P(e)=\prod_{p\in P}p^{-|e_p|/2}.           \tag{90}
\]
Unique factorization makes
\[
 e\longmapsto\sum_{p\in P}e_p\log p
\]
injective.  Thus the radial product Green multiplier retains every mixed prime mode in `(90)`.
Only Mellin determinant scalarization replaces this full Fourier cube by the union of the
one-factor zero sets of \(R_P(s)\).

Each density in `(89)` is continuous and strictly positive.  Hence its state is faithful on
\(C(\mathbb T^P)\): for \(a\geq0\),
\[
 \int_{\mathbb T^P}a\,d\nu_P=0\Longrightarrow a=0.      \tag{91}
\]
The infinite product
\[
 \nu_{\rm crit}
 =
 \bigotimes_p\nu_p                                      \tag{92}
\]
exists, has full support on \(\mathbb T^{\mathcal P}\), and its state is faithful on
\(C(\mathbb T^{\mathcal P})\).  Thus every nonzero positive cylinder innovation is detected.
This closes the finite/cylinder innovation-separation part of the relative-hyperrigidity
programme without an abstract Gram factorization.

### Exact corpus collision

The measure `(92)` is precisely the \(s=1/2\), height-zero member of the already proved
prime-Poisson superselection family.  Phase rotation gives the height-\(t\) member.  Its
coefficient probabilities
\[
 |v_p(k)|^2=(1-p^{-1})p^{-k}                            \tag{93}
\]
are precisely the critical Wold/Kakutani valuation laws.  Therefore:

```text
Green middle completion       = critical product-Poisson GNS sector;
Green coefficient vector      = critical valuation half-density;
Green radial twists           = prior Kakutani/Rees radial sectors;
Green phase rotations         = prior height superselection sectors.
```

This identification is a new cross-card weld, not new parent mathematics and not an RH advance.
The corpus already proves that reflected Poisson sectors are equivalent exactly on the critical
line and also proves that zero-to-sector descent is the missing RH-equivalent assertion.

The corrected conclusion is important:

\[
\boxed{
\text{the kinematic third completion is already constructed;
the unsolved problem is conservative source landing into it.}}
                                                               \tag{94}
\]

No further choice of scalar topology, Green norm, product state, Hardy rigging, or projective
tensor carrier can close `(94)`.  Such choices either reproduce `(92)`, admit every radial sector,
or discard hypothetical off-line conormals.

## 17. Universal-law candidate: source-effective harmonic boundary conservativity

All live routes now point to one statement which is stronger than their individual selector
criteria and weaker than inserting RH as a norm hypothesis.

Let \({\cal C}_{\rm src}(F)\) denote the source-effective object of a constrained HT section
\(F\), retaining:

1. its integral labelled source semigroup;
2. its distinguished effective section;
3. its full derived face/Koszul object rather than a determinant scalarization;
4. its Wold range defects and boundary self-symbols;
5. its regular Gamma determinant and singular first-trace/BV transgression;
6. its Fourier/reflection polarization and critical product bornology.

Let
\[
 H_{\rm con}(F)
 \]
be its principal-conormal cohomology before divisor specialization.  The Wold--Toeplitz extension
and `(84)`--`(92)` provide a source-defined relative boundary realization
\[
 {\mathfrak B}_F:
 H_{\rm con}(F)
 \longrightarrow
 H_{\rm rel}\!\left(
 J_\Gamma\longrightarrow T_\Gamma
       \longrightarrow C(\mathbb T^{\mathcal P});
 \nu_{\rm crit}\right).                                  \tag{95}
\]
The notation in `(95)` is a theorem target, not a completed construction: the ideal
transgression and boundary GNS state must remain in one relative object.

> **[CONJECTURE — SOURCE-EFFECTIVE HARMONIC BOUNDARY CONSERVATIVITY.]**
> For every integral, Fourier-self-dual, source-minimal HT effective lift, the map `(95)` is
> conservative on principal conormal cohomology and its nonzero semisimple boundary support lies
> in the unitary character spectrum:
> \[
> \ker({\mathfrak B}_F|_{H_{\rm con}(F)})=0,\qquad
> \operatorname{Supp}_{\rm ss}{\mathfrak B}_F(H_{\rm con}(F))
> \subseteq\operatorname{Hom}(G,\mathbb T).              \tag{96}
> \]
> Higher conormal jets map to finite-order distributions at the same unitary character.

The first clause in `(96)` is effectivity; the second is harmonic purity.  Neither may be
replaced by the other.  A plain \(C^\ast\)-boundary gives the second clause but can kill the
conormal.  A raw analytic or Ind completion retains the conormal but also retains every
nonunitary strip character.

For \(F=\Xi\), the established principal-conormal covariance is
\[
 \chi_\rho(p)=p^{\rho-1/2}.                              \tag{97}
\]
Fibre faithfulness in `(96)` makes this character nonzero after boundary realization.  Unitary
support then gives
\[
 |p^{\rho-1/2}|=1
 \quad\Longrightarrow\quad
 \Re\rho=\frac12.                                       \tag{98}
\]
Thus `(96)` implies RH with multiplicity.

### What all the obstructions mean under `(96)`

They are failures of conservativity of different forgetful functors:

1. finite clocks retain the section but forget cofinal boundary records;
2. scalar \(L^2\) retains the unitary action but forgets point conormals;
3. raw Ind-limits retain conormals but forget uniform harmonic moderation;
4. determinant and sign criteria forget the full derived face cube;
5. HT alone retains unbounded differential capacity but forgets positive \(\ast\)-descent;
6. positivity alone retains a cone but forgets the distinguished source section;
7. reflection pairs two nonpure fibres but does not identify either with harmonic support;
8. generalized-prime countermodels reproduce scalar shadows but need not carry the integral
   ordinary-prime extension, source-effective section, and conservative comparison `(95)`;
9. the normal-crossing excess theorem says why a scalar totalization cannot be conservative:
   compatibility capacity grows exteriorly even while classical support stays thin;
10. projective leakage, Hellinger singularity, Rees order, Wold first trace, and Green blow-up are
    different norms or boundary charts of the failure of `(95)` to be a strict conservative
    comparison.

This is the proposed universal reinterpretation:

\[
\boxed{
\text{purity is faithful source base change from complex HT conormal support
to its harmonic unitary boundary.}}
                                                               \tag{99}
\]

Equation `(99)` is the jump; it is not yet the theorem.  It subsumes the earlier
source-determinant-purity, relative-hyperrigidity, prime-Schwartz-temperedness, and polarized
middle-extension conjectures by identifying their common missing morphism.

### First proof-bearing obstacle

Do not prove another selector.  Construct `(95)` on the finite bivariate prime/face diagram and
calculate its radical before any zero is selected:

\[
 {\cal R}_{P,N}
 =
 \ker\!\left(
 H_{\rm con}({\cal C}_{P,N})
 \longrightarrow
 H_{\rm rel}({\cal C}_{P,N}^{\rm Green/Wold})
 \right).                                                \tag{100}
\]

The Green state faithfulness `(91)` removes positive cylinder innovations, while the HT
face/Koszul reporters must remove nilpotent, mixed-face, and exponentially flat innovations.
The first substantive theorem must show that the cofinal source transition maps carry
\({\cal R}_{P,N}\) injectively into the next new face and that the intersection of all transported
radicals is zero.  A merely algebraic zero common kernel is insufficient; the source-gauge
observability trichotomy requires a noncompact transverse channel or a uniform lower bound on
the normalized radical.

If the intersection is nonzero, that class is the exact missing seventh channel and must be
classified.  If it is zero with a source-derived strictness estimate, `(96)` becomes a theorem
rather than a restatement of prime-Schwartz temperedness.

## 18. Finite Green faithfulness becomes infinitely ill-conditioned

The faithfulness in `(91)` has an exact stability constant, and that constant collapses at a
source-forced rate.

For \(P\Subset\mathcal P\), write
\[
 w_P(\theta)=\prod_{p\in P}P_{p^{-1/2}}(\theta_p).
\]
The one-prime Poisson kernel has
\[
 \min_\theta P_{p^{-1/2}}(\theta)
 =\frac{1-p^{-1/2}}{1+p^{-1/2}},\qquad
 \max_\theta P_{p^{-1/2}}(\theta)
 =\frac{1+p^{-1/2}}{1-p^{-1/2}}.                        \tag{101}
\]
Consequently the sharp comparison with Haar \(L^2\) is
\[
 m_P\|f\|_{L^2(m_P^{\rm Haar})}^2
 \leq
 \|f\|_{L^2(\nu_P)}^2
 \leq
 m_P^{-1}\|f\|_{L^2(m_P^{\rm Haar})}^2,                 \tag{102}
\]
where
\[
 m_P=\prod_{p\in P}
       \frac{1-p^{-1/2}}{1+p^{-1/2}}.                   \tag{103}
\]
The constants are sharp by concentrating continuous functions near the maximum or minimum point
of \(w_P\).

Let \(P(x)=\{p:p\leq x\}\).  The prime number theorem and partial summation give
\[
 \sum_{p\leq x}p^{-1/2}
 =
 \frac{2\sqrt x}{\log x}(1+o(1)).                       \tag{104}
\]
Since
\[
 \log\frac{1-r}{1+r}
 =
 -2\left(r+\frac{r^3}{3}+\frac{r^5}{5}+\cdots\right)
\]
and \(\sum_pp^{-3/2}<\infty\), `(103)`--`(104)` give
\[
 \boxed{\quad
 \log m_{P(x)}
 =
 -\frac{4\sqrt x}{\log x}(1+o(1)).
 \quad}                                                  \tag{105}
\]

`[PAPER-PROVED — GREEN OBSERVABILITY-COLLAPSE LAW]`

Thus every finite Green reporter is faithful, but no uniform anti-Lipschitz estimate survives
prime enlargement.  There are Haar-unit vectors in growing cylinder algebras whose Green
observation norm tends to zero at the stretched-exponential rate `(105)`.

The failure is stronger than the Wold normal scale.  Mertens' theorem gives
\[
 a_x=\prod_{p\leq x}(1-p^{-1})
 =
 \frac{e^{-\gamma}}{\log x}(1+o(1)).
 \]
Therefore, for every fixed \(N>0\),
\[
 \frac{m_{P(x)}}{a_x^N}\longrightarrow0.                \tag{106}
\]
Finite Green faithfulness becomes flat beyond every finite Rees order of the source-normal
boundary.

This proves a concrete part of the radical problem `(100)`:

```text
finite algebraic/cylinder radical:  zero;
cofinal normalized approximate radical: nonzero;
collapse rate: exp(-4 sqrt(x)/log(x));
ordinary Wold Rees jets: insufficient at every fixed order.
```

The result prevents a false inference from `(91)` to `(96)`.  Adding every finite face reporter
can preserve algebraic injectivity while the completed comparison remains approximately blind.
Any conservative boundary theorem must retain either an infinite-order/noncompact transverse
channel or the full module-valued boundary before scalarization.

### Height averaging explains why a module, not one sector, is forced

For a finite \(P\), rotate the Green state by the arithmetic height flow
\[
 R_t(\theta)_p=\theta_p-t\log p.
\]
For a nonzero Fourier index \(e\in\mathbb Z^P\), unique factorization gives
\[
 \sum_{p\in P}e_p\log p\neq0.
\]
Hence
\[
 \frac1{2T}\int_{-T}^T(R_t)_\ast\nu_P\,dt
 \xrightarrow[T\to\infty]{w^\ast}
 m_P^{\rm Haar}.                                       \tag{107}
\]
The same cylinder argument gives the infinite-prime version already present in the
prime-Poisson screen theorem.

Equations `(105)` and `(107)` expose a duality:

```text
one height sector:
  retains its singular phase fibre, but has collapsing cofinal observability;

all heights before scalarization:
  restore Haar-uniform observability, but scalar Haar L2 loses every point fibre;

required relative module:
  retains the entire torus of point fibres and the Wold/Gamma/BV ideal transgression.
```

This is why the universal object in `(95)` must be module-valued and relative.  A chosen GNS
sector is too ill-conditioned; averaging sectors is too destructive; the relative
Toeplitz-boundary object is the smallest category capable of carrying both.

## 19. Conservation is not purity: the missing law is source recurrence

The continuation--record interpretation still overclaims if ``conservative'' is read as the
purity mechanism.  A lossless completion can retain every deleted record and nevertheless carry
an arbitrary off-boundary zero as internal storage.

For \(a\in\mathbb D\), put \(d_a=(1-|a|^2)^{1/2}\) and
\[
 {\cal U}_a=
 \begin{pmatrix}
  a&d_a\\
  d_a&-\overline a
 \end{pmatrix}.                                           \tag{108}
\]
Direct multiplication gives
\[
 {\cal U}_a^\ast{\cal U}_a
 =
 {\cal U}_a{\cal U}_a^\ast
 =I.
\]
Its scalar transfer function is
\[
 \Theta_a(z)
 =
 a+z\,d_a(1+z\overline a)^{-1}d_a
 =
 {a+z\over1+\overline a z}.                              \tag{109}
\]
Thus the realization is two-sided unitary, minimal when \(|a|<1\), and reciprocal:
\[
 \Theta_a(1/\overline z)
 =
 {1\over\overline{\Theta_a(z)}}.
                                                               \tag{110}
\]
Nevertheless \(\Theta_a\) has the freely prescribed zero \(-a\) in the open disk.  The missing
amplitude has not been destroyed; it is stored in the one-dimensional state coordinate coupled
with strength \(d_a\).

`[PAPER-PROVED — PARENT SYSTEM THEORY / ROUTE CORRECTION]`

Equations `(108)`--`(110)` are the elementary Julia colligation of one Blaschke factor, not new
mathematics.  Their consequence here is load-bearing:

```text
unitary completion
  + faithful complementary record
  + reciprocal reflection
  + minimality
does not force transfer zeros to the reflection boundary.
```

This also explains why an off-line Euler quartet can coexist with positive source data,
reflection, entire completion, Hypertranscendence, and a fully conservative dilation.  A
conservative system does not delete the offending mode; it realizes it as Blaschke storage.
The source-effective conservation conjecture in Section 17 can imply purity only through its
additional ``unitary support'' clause.  That clause is not a consequence of conservation and must
be proved independently.

### Exact Wold storage identity

Let \(V\) be an isometry on a Hilbert space and
\[
 E=I-VV^\ast
\]
its Wold range-defect projection.  If \(0\ne k\) satisfies
\[
 V^\ast k=\lambda k,
\]
then
\[
 \boxed{\quad
 \|Ek\|^2
 =
 (1-|\lambda|^2)\|k\|^2.
 \quad}                                                   \tag{111}
\]
Indeed,
\[
 \|Ek\|^2
 =\langle k,Ek\rangle
 =\|k\|^2-\|V^\ast k\|^2.
\]
Consequently:

1. if \(|\lambda|<1\), the eigencharacter has a nonzero unilateral-storage component;
2. if \(|\lambda|=1\), then \(Ek=0\), \(k\) lies in every range \(V^nH\), and its character is
   carried by the unitary Wold summand;
3. a reciprocal reflected pair can be realized conservatively for every
   \(\lambda\ne0\), with the member of modulus below one stored on the corresponding shift side.

For the centered Riemann character
\[
 \lambda_q(\rho)=q^{\rho-1/2},
 \]
unitary Wold support is exactly
\[
 |\lambda_q(\rho)|=1
 \quad\Longleftrightarrow\quad
 \operatorname{Re}\rho=\frac12.                         \tag{112}
\]
The prior Wold--Higgs, Kakutani, Hellinger--Rees, projective leakage, and prime-Schwartz
selectors are different completions of the storage term in `(111)`.  They all locate the same
wall because they all measure whether a coherent prime character has a unilateral component.

### The universal law after the correction

The corpus is not saying only that information is conserved.  It is saying:

> **[CONJECTURE — SOURCE-RECURRENT HARMONIC CONORMAL LAW.]**  In the source-effective
> continuation--record completion of a source-minimal self-dual constrained HT object, every
> principal conormal class is recurrent under the complete source automorphism.  Equivalently,
> after all complementary records have been restored, principal conormal cohomology has no
> unilateral Wold/storage summand.

Here recurrence is literal, not projective.  For a nonzero class \(x\), there must be
\(n_j\to\infty\) such that
\[
 U^{n_j}x\longrightarrow x                                \tag{113}
\]
in the Hausdorff source-effective topology.  If \(Ux=\lambda x\), `(113)` forces
\(\lambda^{n_j}\to1\), hence \(|\lambda|=1\).  Applied to any one prime dilation and the
Meyer/BV character law, this proves `(112)` and therefore RH.

This formulation explains all three completion failures without conflating them:

```text
finite prime truncation:
  keeps the conormal and has projective recurrence, but amplitude leaks and return constants
  have no cofinal lower bound;

bare infinite adelic L2:
  has unitary recurrent dynamics, but every divisor point fibre disappears into continuous
  spectrum;

conservative record completion:
  keeps both the fibre and all leaked information, but may retain an off-line fibre as
  unilateral Blaschke storage;

required third completion:
  keeps the fibre and the record, and proves that the source conormal itself belongs to the
  recurrent/unitary Wold summand.
```

This is stronger and more precise than ``source normality'', ``sector equivalence'', or
``conservation''.  It says why those conditions were close: each tries to rule out the shift
summand, but none constructs source recurrence.

### Hostile boundary and first proof-bearing obstacle

The conjecture is not counted as an RH advance merely because `(113)` implies `(112)`.
In Meyer's natural nuclear quotient, an off-line eigenfunctional has an exponentially growing
discrete dilation orbit, so recurrence of every Xi conormal there is exactly RH.  Likewise, a
global unitary dilation does not help: `(108)` stores the nonrecurrent compressed state in its
record channel.

The first noncircular theorem must therefore be source-local and pre-divisor:

> construct return morphisms on the finite prime/face Wold--Gamma--BV relative complex, prove
> that their complementary-record components are generated by the literal source differential,
> and obtain a cofinal return estimate in the strict relative topology whose constants do not
> collapse like `(105)`.

A weak, projective, scalar-state, or zero-indexed return is insufficient.  If every such
source-local return estimate still degenerates, the positive survivor is the exact classification
of the nonrecurrent storage object and its growth filtration.  That object, rather than a seventh
scalar invariant, is then the missing channel.

### Novelty boundary

Julia colligations, Blaschke transfer functions, Wold decomposition, and the fact that recurrent
eigenvalues have unit modulus are parent operator theory.  The candidate-new claim is only the
source-specific conjunction: the complete ordinary-prime Euler--Gamma/co-Poisson conormal
comparison is recurrent after its Wold/BV complementary record is restored.  No literature or
corpus theorem currently proves that conjunction.  Existing corpus results prove its finite
shadows, its exact selector, and the failure of all scalar or ordinary-Hilbert limits.

## 20. All-depth recurrence fracture and the global completion-phase law

The proposed first obstacle at the end of Section 19 is still too local.  The new
global-recurrence theorem in
`../../4-publication-ready/multiple-elliptic-gamma-rational-rank-dichotomy/main.tex`
(current title: *Whether quantum history repeats is not locally determined*) proves the following.
An indeterminate positive moment class can contain two probability measures with

\[
 G_{\mu_{\rm r}}=G_{\mu_{\rm e}},
 \qquad
 J_{\mu_{\rm r}}=J_{\mu_{\rm e}}                         \tag{114}
\]

on every polynomial pair, hence the same connected Jacobi rule at every depth, while
\(\mu_{\rm r}\) is pure point with positive mean recurrence and \(\mu_{\rm e}\) is atomless with
zero mean recurrence.  This is not a finite-truncation counterexample.  The complete polynomial
Hilbert geometry and the full local multiplication law agree.

Therefore a compatible tower of finite return morphisms, finite innovation separation at every
depth, or even an all-depth local Wold--Gamma--BV Jacobi rule cannot by itself prove `(113)`.
Boundary data at infinity are an independent mathematical datum in the limit-circle case.  The
earlier proof programme is corrected:

```text
not enough:
  every finite source face returns and every finite innovation is detected;

required:
  the literal arithmetic source selects the recurrent global completion phase.
```

This correction agrees exactly with the high-shell corpus.  The positive exponent-shell frame
has canonical weights
\[
 w_m=H_m(1)>0,
 \qquad
 H_m(s)=\zeta((m+1)s)^{-1}-\zeta(ms)^{-1},               \tag{115}
\]
and every zeta zero of order \(d\) gives the actual top shell conormal
\[
 (\zeta H_m)^{(d)}(\rho)=\zeta^{(d)}(\rho)H_m(\rho).      \tag{116}
\]
Nevertheless the adelic Fourier cross-Gram is rank one on this shell frame and annihilates every
transverse shell-label direction.  The all-depth positive frame constructs the local Jacobi data;
it does not select its global recurrence phase.

### Exact global invariant

For a probability spectral measure \(\mu\), let
\[
 \Delta\mu=(E-E')_\#(\mu\otimes\mu),
 \qquad
 \kappa_n(\mu)=((\Delta\mu)^{*n})(\{0\}).                 \tag{117}
\]
The same recurrence theorem proves
\[
 \lim_{T\to\infty}\frac1{2T}
 \int_{-T}^{T}\left|\int e^{itE}\,d\mu(E)\right|^{2n}dt
 =\kappa_n(\mu),                                        \tag{118}
\]
and the complete sequence \((\kappa_n)_{n\geq0}\) determines the long-time mean of every
continuous fidelity statistic.  In particular,
\[
 \kappa_1(\mu)=\sum_{\lambda\in\mathbb R}\mu(\{\lambda\})^2, \tag{119}
\]
so \(\kappa_1>0\) detects a genuine atomic completion phase, while every atomless Poisson storage
completion has \(\kappa_1=0\).

This identifies the datum omitted by every finite/local route.  It is not another moment, jet,
Gram matrix, or defect norm.  It is the **collision hierarchy of the completed boundary
measure**.

### One-character completion-phase selector

Let \(|z|\leq1\), and let \(\mu_z\) be a probability measure on the unit circle satisfying
\[
 \int_{\mathbb T}\xi^n\,d\mu_z(\xi)=z^n
 \qquad(n\geq0).                                        \tag{120}
\]
Positivity determines the negative Fourier coefficients by conjugation, so Fourier uniqueness
determines \(\mu_z\) completely.  If \(|z|<1\), it is the atomless Poisson measure of \(z\); if
\(|z|=1\), equality in the triangle inequality forces
\[
 \mu_z=\delta_z.                                        \tag{121}
\]
Consequently
\[
 \boxed{\quad
 \kappa_1(\mu_z)>0
 \quad\Longleftrightarrow\quad
 |z|=1.
 \quad}                                                  \tag{122}
\]

Equation `(122)` is the global-completion version of the Wold identity `(111)` and the scalar
maximality theorem.  It adds the missing distinction:

```text
interior character:
  all semigroup moments exist
  + conservative minimal dilation
  + atomless Poisson storage
  + zero collision plateau;

boundary character:
  all semigroup moments exist
  + no storage dilation
  + one atomic phase
  + positive collision plateau.
```

Thus conservation, moment completeness, and a faithful record still permit the first case.
Atomic completion phase is the extra global condition.

### Sharpened universal hunch

> **[CONJECTURE — SOURCE-EFFECTIVE GLOBAL COMPLETION-PHASE CONSERVATION.]**
> A source-minimal self-dual constrained hypertranscendental object does not consist only of its
> finite differential/Krylov data.  Its source-effective continuation includes a distinguished
> global boundary completion and the full collision hierarchy of that completion.  For an
> integral principal conormal, the source collision class is nonzero and atomic, and source
> duality preserves that atomic class rather than replacing it by an atomless Poisson storage
> state.

The word `integral` is load-bearing.  Generic analytic characters, generic HT functions,
generalized-prime Euler systems, and disk-algebra evaluations can have atomless Poisson
completions.  The proposed arithmetic source of the atomic class is the literal ordinary-integer
package already present in the corpus:

1. prime-square CRT additive Fourier clocks;
2. the integral multiplication lattice and Möbius phase;
3. the full prime-power Wold--Gamma/BV record;
4. the archimedean Poisson ordering;
5. the strict Meyer principal-conormal quotient; and
6. every multiplicative collision tensor, not only its moments or determinant.

For a nontrivial zeta zero \(\rho\), the centered \(p\)-character is
\[
 z_p(\rho)=p^{1/2-\rho}.                                 \tag{123}
\]
The complete semigroup moment tower in `(120)` is already its prime-dilation covariance.  If the
conormal comparison carries the nonzero source collision class required by the conjecture, then
`(122)` gives
\[
 |z_p(\rho)|=1
 \quad\Longrightarrow\quad
 \operatorname{Re}\rho=\frac12.                         \tag{124}
\]
This proves RH for every conormal and every multiplicity jet.

### Exact construction target

The next theorem must not try to derive recurrence from the finite nerve.  It must construct a
global source map
\[
 {\cal C}_{\rm CRT/Wold/Gamma/Poisson}
 \longrightarrow
 {\cal M}_{\rm coll}(\mathbb T^{\mathcal P})             \tag{125}
\]
before selecting a zero, where the target retains measure-valued multiplicative moments and their
collision products.  It must then prove:

1. the moment coordinate of a principal conormal is `(123)` at every prime;
2. its collision class is nonzero in the strict source quotient;
3. the class is atomic rather than the Poisson state with the same analytic moments;
4. Poisson/Fourier reflection preserves the class and all multiplicity jets; and
5. no scalar \(L^2\), determinant, finite-Jacobi, or zero-indexed quotient is used.

The high-shell Hardy corona gives an explicit one-prime chart for `(125)`: right-half conormals
are interior Hardy evaluations, critical conormals are nonzero boundary-corona characters, and
reflected left-half conormals leave the bounded chart.  The projective and prime-square clocks
supply the finite collision tensors.  What remains is their source-global, archimedean-compatible
totalization.

### Immediate corpus collision: the positive source bulk is atomless

The first literal source test rejects the naive reading of the conjecture.
`formal/GaloisForLFunctions/RHTower/HighExponentShellClockMeasure.lean` proves that, for every
fixed high shell, the positive Gibbs clock
\[
 (\sigma-1)\log n,
 \qquad
 \mathbb P_{m,\sigma}(n)
 =
 \frac{a_m(n)n^{-\sigma}}{S_m(\sigma)}
 \]
converges as \(\sigma\downarrow1\) to the unit-rate exponential law.  The oriented difference of
two independent shell clocks converges to the Laplace law.  Both limits are atomless, so their
positive-order collision masses at zero vanish.

Thus

```text
literal integral positive source
  does not by itself select an atomic recurrence phase;

principal conormal
  cannot be treated as an atom already present in the positive bulk measure.
```

The same conclusion is visible in ambient adelic \(L^2\): the source dynamics is unitary but its
point conormals lie outside the continuous spectral representation.  Therefore the atomic clause
in the global-completion-phase conjecture is false if it refers to the bulk Gibbs/Poisson measure.
It can survive only as a **relative atom-birth statement**:

> the principal conormal is a new singular collision class created by the Bockstein of the missing
> Calderón primitive, and not an atom of the underlying positive source clock.

This returns the global-completion law to the exact transgression `(12h)`.  The new information is
that the Bockstein target must retain a measure-valued collision class, not only an \(H^1\) vector,
first trace, determinant, or Rees order.  The RH-bearing claim becomes:

\[
\boxed{
\begin{gathered}
\text{atomless source bulk}
\xrightarrow{\ \text{relative completion Bockstein}\ }
\text{nonzero principal collision class},\\
\text{self-dual source birth}
\Longrightarrow
\text{the born class is boundary-atomic rather than Poisson-stored}.
\end{gathered}}                                             \tag{126}
\]

Rank-one perturbations of continuous spectrum can create ordinary off-spectrum bound states, so
`(126)` is not generic spectral theory.  Generalized-prime off-line systems are direct
falsifiers of any claim based only on positivity, self-duality, or rank one.  The load-bearing
arithmetic theorem must identify the relative atom-birth map with the literal
CRT/Wold/Gamma/co-Poisson Bockstein before divisor specialization.

### Hostile falsifiers and anti-theatre boundary

1. If the collision class is defined to be atomic after restricting to the unit circle, the
   argument is circular.
2. If only \(\kappa_1>0\) is postulated without preserving every moment in `(120)`, an interior
   point can be represented by an unrelated atomic measure; `(122)` no longer follows.
3. If the source map factors through finite moments, all-depth Jacobi data, or the scalar
   determinant, `(114)` falsifies it.
4. If a generalized-prime off-line system realizes the same literal ordinary-integer collision
   package and a nonzero atomic conormal class, the conjecture is false.
5. If the conormal is called an atom merely because it is one-dimensional algebraically, the disk
   algebra is a counterexample: an interior scalar character has an atomless Poisson dilation.
6. If the map `(125)` uses the Xi divisor to choose its measure, it is an RH restatement rather
   than a source theorem.
7. If the principal collision class is identified with the positive shell Gibbs collision law,
   the formalized exponential/Laplace limit makes it atomless and the construction fails.

Moment-indeterminate Jacobi extensions, Poisson representing measures, Wiener's atom formula,
maximal dilations, and collision moments are parent mathematics.  The new candidate is only the
source-specific claim that the ordinary-prime Euler--Gamma/co-Poisson Bockstein creates a nonzero
boundary-atomic principal collision class from the atomless literal integral bulk.  At present
that claim is RH-bearing and unproved.  The advance is the correction of the false finite-return
and inherited-atom programmes and the identification of the exact global datum that any valid
proof must construct.

## 21. What the corpus means: cofinal completion and balanced boundary do not commute

Sections 19--20 still describe the missing object from inside one operator realization.  The
larger synthesis is categorical.  Every finite Euler packet is an invertible gauge.  It has no
zeta divisor class, and every finite source complex contracts.  The nonzero class appears only
after all ordinary primes, the Gamma boundary, the Meyer/co-Poisson quotient, and the strict
source topology have been assembled.  Therefore the divisor cannot be an eigenvalue already
present in a finite approximation.  It is an anomaly measuring failure of two infinite
operations to commute.

Let \(({\cal E}_P)_{P\Subset{\cal P}}\) denote the finite-prime enhanced Euler--Gamma source
system, with all six independently forced channels retained: external source action, signed
reflection polarization, critical Gevrey product bornology, controlled transport germ,
distinguished source section, and integral/ramified comparison lattice.  Write
\[
 {\sf C}_{\rm src}({\cal E})
 =
 \mathop{\rm Ind\!-\!colim}^{\rm strict}_{P}
 {\cal E}_P                                                   \tag{127}
 \]
for source-effective strict completion before specialization.  Write
\({\sf J}_{\rm bal}\) for the reflected intermediate-boundary operation: the strict image
between the rapid/minimal and two-sided moderate/maximal extensions, with the Green pairing and
half-density normalization retained.

There is a comparison morphism
\[
 \eta_{\cal E}:
 {\sf C}_{\rm src}\bigl({\sf J}_{\rm bal}{\cal E}_P\bigr)
 \longrightarrow
 {\sf J}_{\rm bal}\bigl({\sf C}_{\rm src}{\cal E}\bigr).       \tag{128}
 \]
Define its cofinal-boundary commutator anomaly by
\[
 {\mathfrak A}_{\cal E}
 =
 {\rm cofib}(\eta_{\cal E}).                                  \tag{129}
 \]
At every finite stage the principal Euler gauge is exact, so its relevant balanced-boundary
class is zero.  Equation `(129)` permits a nonzero class only because strict all-source
completion was taken before the balanced boundary.

### Frozen conjecture: source-effective cofinal-intermediate purity

> **[CONJECTURE — SOURCE-EFFECTIVE COFINAL-INTERMEDIATE PURITY LAW.]**
> Let \({\cal E}\) be a regular source-minimal integral hypertranscendental constraint system
> with:
>
> 1. finite source gauges that are exact and compatible under genuine source enlargement;
> 2. an additive Poisson realization and a multiplicative Euler realization related by the
>    literal integral source lattice;
> 3. a reflected duality exchanging the two adiabatic ends;
> 4. principal finite-plus-archimedean Kummer slope cancellation;
> 5. the six-channel source-effective strict completion in `(127)`; and
> 6. a nonzero cofinal first-trace/Maurer--Cartan gauge defect.
>
> Then the commutator anomaly \({\mathfrak A}_{\cal E}\):
>
> ```text
> is presentation-independent and conservative on the complete principal-conormal jet;
> lies in the reflected intermediate extension, not merely either one-sided extension;
> has pure real Stokes slope zero after the source half-density centering.
> ```

This is a conjecture in the strict sense: it is the statement suggested by the whole corpus, not
a statement selected because a proof is visible.  No proof of the general law is known.  Its
premises are source-side and can be checked before a divisor is chosen.  Neither conormal
temperedness, unitary divisor characters, zero location, Weil positivity, nor an RH-equivalent
norm occurs among them.

The law says that hypertranscendence and arithmetic integrality have opposite roles.
Hypertranscendence prevents the cofinal defect from being represented or killed at any finite
differential order.  The conjugate integral Poisson/Euler polarizations prevent the surviving
defect from choosing an arbitrary one-sided completion phase.  Their conjunction converts
infinite irregular capacity into a balanced slope-zero boundary charge.

### Zeta specialization and the RH consumer

For the completed ordinary-prime source, the all-prime Maurer--Cartan connection is
\[
 -Z_h^{-1}\partial_hZ_h
 =
 \sum_p\sum_{k\geq1}(\log p)p^{-kh}U_{p^k}.                    \tag{130}
 \]
Every finite \(Z_{P,h}\) is an invertible gauge.  After Gamma completion, the meromorphic
boundary of `(130)` is the independently constructed completed logarithmic Green current.  The
zeta instance of the conjecture predicts
\[
 {\rm CharSupp}({\mathfrak A}_{\zeta})
 =
 {\rm Div}(\Xi)
 \quad\text{with every multiplicity jet retained}.            \tag{131}
 \]
Equation `(131)` is not to be imposed by defining \({\mathfrak A}_{\zeta}\) from \(\Xi\).  It is
the source-to-divisor comparison theorem that must be derived from `(130)`, Gamma
transgression, co-Poisson continuation, and strictness of `(127)`.

At a nontrivial zero \(\rho\), the centered rational-dilation character on the principal
conormal is
\[
 \chi_\rho(g)=g^{\rho-1/2}.                                   \tag{132}
 \]
Its real adiabatic/Stokes slope is \(\operatorname{Re}\rho-\tfrac12\).  Conservativity in
`(131)` keeps its top nonzero jet; slope-zero purity in the conjecture gives
\[
 \operatorname{Re}\rho-\frac12=0.                             \tag{133}
 \]
Thus the zeta instance implies RH, including all multiplicities.

### What this reinterprets

The previous obstructions become shadows of `(128)`--`(129)`:

```text
finite truncation leakage
  = balanced boundary taken before strict cofinal source completion;

adelic L2 loss of point fibres
  = completion retained but the intermediate conormal boundary forgotten;

moment-indeterminate recurrence phases
  = nonuniqueness of one-sided closed extension before reflected intermediate image;

Wold storage / Clark parameters / Suzuki residual escape
  = one-sided boundary pieces removed only after the balanced source comparison;

Gamma determinant and BV first trace
  = regular and singular readings of the same cofinal gauge anomaly;

high-shell positive atomless bulk
  = ambient source measure before the relative commutator anomaly is formed;

prime-Schwartz temperedness
  = the slope-zero distributional shadow after `(129)` has been proved conservative;

hypertranscendental infinite horizon
  = impossibility of representing the anomaly in any finite jet, rate, or obstruction layer.
```

The “third completion” is therefore not primarily a third normed space.  It is the relative
object \({\mathfrak A}_{\cal E}\) produced by the noncommutation of source completion and balanced
boundary, together with its strict image and pairing.  A Hilbert or rigged-Hilbert carrier is a
realization of this relative object, not its definition.

### Hostile collision audit

1. Standard irregular Riemann--Hilbert theory supplies enhanced exponential objects and
   moderate/rapid boundary functors, but permits arbitrary nonzero irregular slopes.  Reflected
   pairs \((a,-\overline a)\) show that self-duality alone does not imply purity.
2. Stone--von Neumann uniqueness fixes a regular additive Weyl representation but does not prove
   that the multiplicative Xi conormal lands in the valuation-Schwartz dual.  Bare representation
   uniqueness is therefore insufficient.
3. Prime-Schwartz conormal temperedness is exactly RH in the natural Xi quotient.  It can be a
   consequence of `(129)` but not a premise or proof of the conjecture.
4. The positive high-shell clock has an atomless exponential/Laplace limit.  The anomaly in
   `(129)` is a relative boundary birth, not an inherited atom of that bulk.
5. General self-dual hypertranscendental or generalized-prime Euler systems can have off-line
   zeros.  The literal ordinary-integer additive Poisson lattice, principal product formula, and
   strict comparison in clauses 2--6 are load-bearing.
6. An ordinary derived colimit of finite acyclic packets may remain zero.  The conjecture uses a
   strict nuclear/source-effective completion whose failure of exactness is measured before
   specialization.  If no such nonzero strict defect exists, the conjecture is false.

### First proof problem after conjecture generation

The first new theorem is not `(133)`.  It is the construction of `(128)` on the actual
all-prime Euler-gauge family and a source-side identification of its cofiber.  A successful first
step must prove, without choosing a zero:

1. the finite comparison morphisms form a strict, presentation-independent six-channel system;
2. completion of the Maurer--Cartan connections has a nonzero cofinal class although every finite
   gauge class is exact;
3. its Gamma-completed boundary equals the independently constructed Green/co-Poisson current;
4. the class belongs to both reflected moderate extensions and its nonzero-real-slope pieces map
   to the rapid acyclic sector; and
5. the comparison is conservative on principal conormal jets.

Clauses 4--5 together are RH-bearing in the zeta quotient.  The point of `(127)`--`(129)` is to
give a pre-divisor object from which they might follow, rather than to disguise them as
continuity.  Failure at any clause must identify the precise surviving noncommutation defect,
cofinal-order dependence, or one-sided Stokes component.

The external parent boundary is clear.  Enhanced irregular Riemann--Hilbert, moderate/rapid
nearby cycles, strict Ind-categories, intermediate extensions, Poisson summation, Euler products,
and Maurer--Cartan connections are established mathematics.  The conjectural new law is their
source-specific conjunction: a strict integral HT gauge anomaly is conservative and pure because
it is born only in the commutator of cofinal completion with reflected intermediate extension.

## 22. Exact coefficient model: reflected Mertens slope purity

The slope-zero part of Section 21 is not merely an analogy.  It is already an unconditional
theorem on the actual-prime Mertens boundary, before any Xi divisor or zero is introduced.
The positive- and zero-slope cases below, including the complete boundary-jet law, were already
proved in `deninger-poisson-mertens-boundary-jet-fracture.md`.  The additional content here is the
negative-slope exclusion, complex-phase formulation, and reflected three-way synthesis.  This is
an internal-corpus consolidation, not a fresh external novelty claim.

For \(k\geq0\), let \(M_k\) be the weighted prime Marcinkiewicz space with
\[
 \|b\|_{M_k}
 =
 \sup_{X\geq2}
 {1\over(\log X)^{k+1}}
 \sum_{p\leq X}{\log p\over p}|b_p|,                      \tag{134}
\]
and let \(M_{k,0}\) be its closed finite-support subspace.  For
\(\alpha\in\mathbb C\), define the logarithmic-grade exponential source
\[
 c_{\alpha,k}(p)=(\log p)^k p^{-\alpha}.                  \tag{135}
\]

### Theorem: Mertens exponential-slope trichotomy

For every \(k\geq0\) and \(\alpha\in\mathbb C\):

\[
\begin{array}{c|c}
\operatorname{Re}\alpha>0
&
c_{\alpha,k}\in M_{k,0},
\\[2mm]
\operatorname{Re}\alpha=0
&
c_{\alpha,k}\in M_k\setminus M_{k,0},
\quad
\|[c_{\alpha,k}]\|_{M_k/M_{k,0}}={1\over k+1},
\\[2mm]
\operatorname{Re}\alpha<0
&
c_{\alpha,k}\notin M_k.
\end{array}                                               \tag{136}
\]

Consequently the reflected pair
\[
 c_{\alpha,k},\qquad c_{-\overline\alpha,k}               \tag{137}
\]
is simultaneously admissible and nonzero in the two Mertens corona quotients if and only if
\[
 \operatorname{Re}\alpha=0.                              \tag{138}
\]

#### Proof

If \(a=\operatorname{Re}\alpha>0\), then
\[
 |c_{\alpha,k}(p)|=(\log p)^k p^{-a}.
\]
The already-proved positive Euler-translation estimate
\[
 S_a:M_k\longrightarrow M_{k,0},
\qquad
 (S_ab)_p=p^{-a}b_p,                                     \tag{139}
\]
applied to \(u_k(p)=(\log p)^k\), gives the first line of `(136)`.

Suppose \(a=0\).  Absolute values in `(134)` erase the unit phase \(p^{-\alpha}\), so
\[
 \|c_{\alpha,k}\|_{M_k}
 =
 \|u_k\|_{M_k}.
\]
Multiplication by the phase is an isometric automorphism of \(M_k\), preserves finite support,
and therefore preserves \(M_{k,0}\).  The proved Mertens asymptotic
\[
 \sum_{p\leq X}{(\log p)^{k+1}\over p}
 =
 {(\log X)^{k+1}\over k+1}+C_k+o(1)                     \tag{140}
\]
gives
\[
 u_k\in M_k\setminus M_{k,0},
\qquad
 \|[u_k]\|={1\over k+1}.
\]
The phase automorphism transfers both conclusions to \(c_{\alpha,k}\).

Finally suppose \(a<0\), and put \(b=-a>0\).  Restrict the sum in `(134)` to
\(\sqrt X<p\leq X\).  On this interval \(p^b\geq X^{b/2}\), so
\[
\begin{aligned}
 {1\over(\log X)^{k+1}}
 \sum_{p\leq X}{\log p\over p}|c_{\alpha,k}(p)|
 &\geq
 {X^{b/2}\over(\log X)^{k+1}}
 \sum_{\sqrt X<p\leq X}{(\log p)^{k+1}\over p}.
\end{aligned}                                             \tag{141}
\]
By `(140)`, the last normalized interval sum tends to
\[
 {1-2^{-(k+1)}\over k+1}>0.                              \tag{142}
\]
The right side of `(141)` therefore diverges, proving
\(c_{\alpha,k}\notin M_k\).  Reflection changes \(a\) to \(-a\); the three cases now give
`(138)`.  `QED`

### Full logarithmic-jet compatibility

Differentiation in the slope parameter gives
\[
 \partial_\alpha^r c_{\alpha,k}
 =
 (-1)^r c_{\alpha,k+r}.                                  \tag{143}
\]
Thus `(136)` holds compatibly at every logarithmic grade:

```text
positive slope:
  every finite boundary jet lies in the rapid/tail-null layer;

zero slope:
  every jet grade survives with exact corona norm 1/(k+r+1);

negative slope:
  no jet grade enters the moderate Marcinkiewicz carrier.
```

For every \(a>0\), the source jump is already exact in the quotient:
\[
 [c_{0,k}-c_{a,k}]=[c_{0,k}],
\qquad
 \|[c_{0,k}-c_{a,k}]\|={1\over k+1}.                    \tag{144}
\]
Hence \(a\downarrow0\) is not a small perturbation in the corona.  Every positive-slope gauge is
zero there, while the slope-zero boundary has a fixed nonzero charge at every differential
grade.  Equation `(144)` is a literal finite-gauge/boundary noncommutation law.

### Meaning and limitation

Set
\[
 \alpha={1\over2}-\rho.
\]
Then `(135)` is the modulus-bearing part of the centered prime character
\[
 p^{\rho-1/2}=p^{-\alpha}.                               \tag{145}
\]
The theorem proves the desired critical selector entirely on the independently defined
actual-prime coefficient boundary:

```text
nonzero reflected Mertens intermediate class
  implies
Re(alpha)=0
  implies
Re(rho)=1/2.
```

This is not RH progress by itself.  It neither constructs the Xi conormal in the Mertens
intermediate class nor proves that the cofinal Euler--Gamma anomaly is conservative on every
divisor jet.  It proves the coefficient-side purity mechanism that such a comparison would
consume.

The first-trace exponential-flat theorem locates why the ordinary corona is insufficient for the
construction step.  Its actual-prime error has size \(p^{-1}\), hence positive exponential slope
one, and `(136)` sends it to the rapid-null layer.  Nevertheless its dimensionless exponential
rate grade is nonzero.  Therefore the all-prime source object must retain an exponential
associated graded before applying the reflected Mertens intermediate quotient.  This matches the
order required in `(127)`--`(129)`:

```text
first retain all exponential/Stokes rates in the strict source completion;
then form the reflected intermediate image;
only its surviving nonzero principal class is forced to slope zero.
```

The remaining frontier is now one sharply typed arrow:
\[
 {\mathfrak A}_{\zeta}
 \longrightarrow
 \bigoplus_{k\geq0}
 \left(M_k/M_{k,0}\right)
 \quad\text{conservative on every Xi principal jet}.     \tag{146}
\]
Constructing `(146)` before zero specialization would combine the exact cofinal anomaly with the
proved slope-purity selector.  Assuming `(146)` only on the Xi quotient is again equivalent to
RH and is forbidden.

## 23. Universal interpretation: the arithmetic Stokes--Gauss law

The new synthesis does not require inventing another completion after `(146)`.  It changes what
**source effectivity** should mean.

The source already carries an intrinsic real exponential-slope filtration.  At prime scale
\[
 \varepsilon_p={1\over\log p},
\]
the elementary exponential grade is
\[
 p^{-\alpha}
 =
 \exp(-\alpha/\varepsilon_p),                            \tag{147}
\]
and its real slope is \(\operatorname{Re}\alpha\).  The Mertens class \(c_{0,k}\) is pure slope
zero.  The first-trace error \(p^{-1}\) is slope one.  Critical Fisher damping \(p^{-1/2}\) is
slope one-half before the source half-density twist.  A centred Xi conormal has slope
\[
 \operatorname{Re}\left({1\over2}-\rho\right)
 =
 {1\over2}-\operatorname{Re}\rho.                       \tag{148}
\]
Thus all asymptotic faces already use one valuation; previous cards had treated its regular,
formal, WKB, and conormal readings separately.

Let
\[
 0\longrightarrow M_{\rm src}
 \longrightarrow M_{\rm amb}
 \longrightarrow M_{\rm cor}
 \longrightarrow0                                      \tag{149}
\]
be the conjectural source/ambient/corona sequence from `(12g)`, now formed in a category carrying
the complete exponential-slope filtration \(F^{\rm St}\).  Its connecting morphism is
\[
 \partial_{\rm src}:
 H^0(M_{\rm cor})
 \longrightarrow
 H^1(M_{\rm src}).                                      \tag{150}
\]

### Frozen conjecture: filtered-Bockstein source effectivity

> **[CONJECTURE — ARITHMETIC STOKES--GAUSS LAW.]**
> For every regular integral self-dual source-minimal HT constraint, its source-effective
> completion constructs `(149)` before exceptional-divisor specialization such that:
>
> 1. \(F^{\rm St}\) is intrinsic to the arithmetic source and presentation-independent;
> 2. `(149)` is strict for \(F^{\rm St}\), and \(\partial_{\rm src}\) is a strict morphism of
>    Stokes degree zero;
> 3. the escaping unit Calderón primitive defines a nonzero pure slope-zero class
>    \([R]\in H^0(M_{\rm cor})\);
> 4. \(\partial_{\rm src}[R]\) is the complete source principal-conormal charge, not merely its
>    scalar trace, determinant, or finite jet;
> 5. its realization in the holomorphic constraint quotient is conservative on every
>    exceptional-divisor point and every multiplicity jet; and
> 6. source reflection reverses Stokes slope and agrees with duality on the same strict sequence.

This conjecture is not constrained by whether a proof is presently visible.  It is the strongest
law suggested by the corpus.  It is also falsifiable: a source-equivalent presentation changing
the slope filtration, a non-strict completion, a Bockstein with nonzero degree, a lost divisor
jet, or an explicit off-line system satisfying all six clauses refutes it.

### Why “Gauss law”

Equation `(150)` is a boundary-charge map.  The missing primitive is bulk data; its Bockstein is
the boundary charge.  Strictness says exponential slope is conserved across that transgression:
\[
 \operatorname{slope}\bigl(\partial_{\rm src}[R]\bigr)
 =
 \operatorname{slope}([R])
 =
 0.                                                     \tag{151}
\]
This is the exact analogue of a Gauss law needed here: a global source charge cannot acquire an
arbitrary radial/Stokes grade when it becomes divisor flux.

The word `strict` is load-bearing.  An ordinary filtered morphism can send a pure class into a
larger filtration and hide nonzero associated-graded components.  A scalar trace can cancel
opposite slopes.  A non-Hausdorff quotient can kill the grade-zero class.  Strictness plus
fibrewise conservativity excludes all three.

### Formal RH deduction

Assume the zeta instance.  Clause 4 identifies
\(\partial_{\rm src}[R]\) with the complete Xi principal conormal, and clause 5 gives a nonzero
component at every zero \(\rho\).  On a prime axis that component has character
\[
 p^{\rho-1/2}
 =
 \exp\!\left(-{(1/2-\rho)\over\varepsilon_p}\right).     \tag{152}
\]
By `(151)`, its real slope `(148)` is zero.  Hence
\[
 \operatorname{Re}\rho={1\over2}.                       \tag{153}
\]
Every nontrivial zero is covered, so RH follows.

No positivity inequality is needed after the Stokes--Gauss law.  Positivity and reflection are
structural inputs ensuring the source sequence and its two ends are the correct self-dual ones;
the location theorem itself is conservation of filtered degree.

### What all previous results become

```text
Mertens unit corona:
  the pure slope-zero source charge;

positive Euler translation vanishing:
  positive slopes pass into the rapid/null subobject;

negative-slope Marcinkiewicz divergence:
  negative slopes fail the moderate source lattice;

first-trace exponential flatness:
  nonzero higher Stokes grades erased by every finite-order completion;

Gamma determinant / BV first trace:
  two readings of the Bockstein boundary;

finite Wold exactness:
  local Gauss law with a primitive and therefore no charge;

cofinal Bockstein:
  charge born only when the common primitive escapes strict completion;

functional equation:
  reflection of slope a to -a, not a proof that a vanishes;

Meyer all-zero quotient:
  holomorphic decomposition of the boundary charge into divisor fibres;

prime-Schwartz moderation:
  distributional realization of the slope-zero associated graded;

generalized-prime and rational-quartet countermodels:
  systems where the source Bockstein, its framing, its slope strictness, or its integral
  realization is not the ordinary-integer one.
```

This also explains why every scalar sign route failed.  A scalar pairs or sums reflected slopes
and can erase their grade.  The full associated-graded Bockstein retains the slope of each
conormal component before any trace.

### Parent theorem versus frontier theorem

In a strict filtered exact category, a degree-zero strict connecting morphism preserves the
associated grade.  That abstract statement is parent homological algebra and proving it again
would be theatre.  Frontier content is entirely arithmetic:

1. construct the exponential filtration from actual prime scales and Gamma/Poisson
   normalization;
2. build `(149)` on the strict all-prime source before specialization;
3. prove the Wold--Gamma/BV connecting map has Stokes degree zero;
4. identify its nonzero slope-zero source class with the co-Poisson/Xi principal conormal; and
5. prove strict fibrewise conservativity, including multiplicity.

The first serious obstruction is clause 3 above.  The local interval Bockstein records nilpotent
multiplicity grade but is independent of semisimple radial slope.  The next theorem must show that
the actual Gamma/BV transgression is homogeneous of Stokes degree zero after the forced
half-density normalization.  Only then can the nilpotent interval tower and semisimple radial
filtration live in one strict source sequence.

## 24. Correction at infinity: arithmetic divisor charge must not diffuse

The preceding order of attack is too local.  The corpus already proves that local Gamma Stokes
data are Tate-local and projectively scalar, while the Wold/BV scalar coefficient has leading
Stokes degree zero independently of a divisor parameter.  Homogeneity of that scalar coefficient
cannot attach a Xi conormal to the unitary boundary.  It is therefore not the first serious
obstruction and is retired as a standalone frontier target.

The all-prime operator-algebra audit exposes a sharper issue.  The conjectural implication

\[
 \text{complete complementary record}
 +\text{zero common reporter kernel}
 \Longrightarrow
 \text{maximal representation}                           \tag{154}
\]

is false without an additional terminality condition.

### Exact Poisson-dilation countermodel to record maximality

Let \(A(\mathbb D)\) be the disk algebra and let
\(\chi_z(f)=f(z)\), where \(|z|<1\).  Let \(\mu_z\) be harmonic measure at \(z\),
\[
 d\mu_z(e^{i\theta})
 =
 {1-|z|^2\over |e^{i\theta}-z|^2}\,{d\theta\over2\pi},
                                                               \tag{155}
\]
let \(U\) be multiplication by \(e^{i\theta}\) on \(L^2(\mu_z)\), and let
\(\xi=1\).  The Poisson formula gives
\[
 \langle f(U)\xi,\xi\rangle=f(z)
 \qquad(f\in A(\mathbb D)).                               \tag{156}
\]
Thus \((U,\xi)\) is a boundary dilation of \(\chi_z\).  It records every analytic moment of the
interior character.  It also records the exact one-step Schwarz defect
\[
 1-|z|^2>0.                                               \tag{157}
\]
No information-theoretic incompleteness is present: the complete moment sequence and the
complementary defect recover \(z\), yet the original character is nonmaximal.

For \(|z|<1\), the measure `(155)` is non-atomic with strictly positive density, so the cyclic
boundary sector generated by \(\xi\) is infinite-dimensional.  For \(|z|=1\), harmonic measure
degenerates to the atom \(\delta_z\), the cyclic sector is one-dimensional, and the scalar
character is already a boundary representation.  In the prime polydisk, one strict coordinate
\(|z_p|<1\) already produces the same infinite-dimensional dilation along that coordinate.

This is parent Sz.-Nagy--Foiaş/Poisson dilation mathematics.  Its role here is a killing theorem:
reporter completeness detects a proper dilation; it does not prohibit one.

### Finite-fibre/no-diffusion trilemma `[PROVED ABSTRACTLY]`

Let \(\chi_z\) be a finite-dimensional scalar prime-semigroup character and attempt to pass it to
a maximal unitary boundary realization.  If some \(|z_p|\ne1\), then at least one of the following
must happen:

1. **boundary-fibre annihilation:** extension of scalars to
   \(C^*(\mathbb Q_{>0}^{\times})\) kills the nonunitary character fibre, because
   \(u_p-z_p\) is invertible on the unitary character torus;
2. **Poisson diffusion:** retaining \(\chi_z\) as a compression replaces its finite point fibre by
   an infinite-dimensional cyclic boundary sector;
3. **nonmaximality:** the realization keeps the finite character fibre but has a nontrivial
   boundary dilation.

Consequently a finite, nonzero, maximal, point-character fibre exists only when
\[
 |z_p|=1\quad\text{for every }p.                          \tag{158}
\]
This is not another norm criterion.  It classifies the three possible failures of commuting
finite divisor specialization with maximal completion.

For the centered Xi conormal,
\[
 z_p(\rho)=p^{1/2-\rho}.                                  \tag{159}
\]
Equation `(158)` is therefore equivalent to
\(\operatorname{Re}\rho=1/2\).

### Frozen conjecture: source-terminal nearby-cycle strictness

`[CONJECTURE] [XI_SOURCE_TERMINAL_NEARBY_CYCLE_STRICTNESS]`

The literal integral Euler--Gamma/co-Poisson relative complex admits a source-generated terminal
envelope \(\operatorname{Env}_{\rm src}\) for the Wold--Toeplitz extension such that:

1. \(\operatorname{Env}_{\rm src}\) is constructed before divisor specialization and is maximal
   only among morphisms preserving the integral source, Gamma/BV transgression, reflection, and
   complete algebraic and exponential rate records;
2. principal Xi nearby cycles commute strictly with this terminalization;
3. a zero of multiplicity \(d\) has a nonzero finite-length completed principal-conormal fibre of
   the same length \(d\);
4. no finite fibre is replaced by a diffuse cyclic boundary state; and
5. the comparison is compatible with prime enlargement and independent of source presentation.

The conjecture asserts an arithmetic properness/non-diffusion law.  It does not infer maximality
from complete records.  Maximality is part of the independently defined terminal envelope;
the new arithmetic statement is that finite Xi nearby cycles survive terminalization without
annihilation or diffusion.

By the trilemma, clauses 2--4 force every character `(159)` to be unitary.  Hence the conjecture
implies RH, including multiplicity.

### What the corpus means under this law

```text
finite truncation:
  finite point fibre survives, but representation is nonmaximal and leaks;

ambient adelic L2:
  unitary completion exists, but point fibre diffuses into continuous spectrum;

plain C*-boundary:
  unitary point fibres survive, but nonunitary fibres are annihilated and the anomaly ideal is lost;

relative Wold--Gamma/BV extension:
  retains the obstruction record needed to define source-compatible terminalization;

high-shell Hardy interior:
  a strict-right conormal is a bounded interior state, hence a nonmaximal Poisson compression;

high-shell Calkin boundary and prime-Schwartz boundary:
  exactly the atomic/non-diffusive grade;

first-trace and Mertens fractures:
  witnesses that completion and specialization need not commute;

hypertranscendence:
  forces the complete record tower, but does not prohibit Poisson diffusion;

functional equation:
  pairs reciprocal diffusive sectors, but does not atomize either one;

generalized-prime off-line systems:
  valid sources whose divisor charge is allowed to diffuse or whose terminal nearby-cycle
  comparison is not the literal ordinary-prime one.
```

The new universal interpretation is:

> **A zero is a finite arithmetic boundary charge.  Off the critical line, maximal completion can
> retain that charge only by dissolving the point into a Poisson boundary cloud.  RH says the
> ordinary-prime source is non-diffusive: every integral divisor charge remains a finite atom
> under terminal completion.**

This is the finite-fibre form of the arithmetic Stokes--Gauss law.  “Slope is conserved” now has
an exact categorical meaning: the specialization remains atomic through completion, rather than
being annihilated or spread across a boundary measure.

### Hostile boundary and actual next theorem

1. Integrality of total charge alone is insufficient; a probability measure can be diffuse and
   still have integral total mass one.
2. Complete reporter data alone are insufficient by `(155)`--`(157)`.
3. Generic C*-envelopes and boundary representations are parent theory; they erase the relative
   Gamma/BV ideal.
4. Projective strictness in irregular Hodge theory is a finite-stage parent theorem.  It does not
   prove strictness for the countable ordinary-prime Ind-limit or identify its nearby cycles with
   the Xi conormal.
5. Declaring terminalization to commute with Xi specialization is RH-bearing and may not be used
   as a definition.

The first serious construction problem is therefore:

> build the source-relative terminal envelope before specialization and prove one finite-length
> base-change theorem for its principal conormal nearby cycles.

The proof must expose the exact boundary term that would cause Poisson diffusion and show, using
the literal Euler--Gamma/co-Poisson transgression rather than abstract positivity, that this term
vanishes or is returned to the finite conormal fibre.  If the term does not vanish, classify its
boundary measure; that measure is the strongest positive survivor and the conjecture must be
revised.

External parent boundary: Dritschel--McCullough construct maximal boundary dilations and the
\(C^*\)-envelope for general operator algebras; Sabbah--Yu prove strict projective pushforward for
finite exponentially twisted mixed Hodge modules.  Neither parent supplies the source-relative
ordinary-prime terminal envelope or the claimed finite Xi nearby-cycle base change.

## 25. The jump: dualizable arithmetic charge cannot diffuse

Section 24 still makes maximal terminalization carry more weight than is necessary.  A finite
divisor fibre does not need to be a maximal boundary representation.  It only needs to survive as
an invariant finite object inside a positive prime representation.  The obstruction is therefore
not maximality itself but failure of completion to preserve **dualizable defect objects**.

### Parent categorical lemma

Let \(\mathcal C^\otimes\) be a symmetric monoidal source category and let
\[
 {\cal R}:\mathcal C^\otimes\longrightarrow {\rm Hilb}
                                                               \tag{160}
\]
be a dagger Frobenius monoidal functor.  Strong monoidality is sufficient, but not necessary.
Then:

1. \({\cal R}\) preserves dualizable objects;
2. a dualizable object of \({\rm Hilb}\) is finite-dimensional;
3. if a unitary \(U\) preserves a finite-dimensional subspace \(E\), then
   \(U|_E\) is unitary and \(E\) is reducing.

The third statement uses only finite dimension: \(U|_E\) is an isometry and hence surjective.
Consequently every eigenvalue of \(U|_E\) has modulus one.

These are parent results.  Strong monoidal functors preserve duals; Day--Pastro prove that the
weaker Frobenius monoidal condition still suffices.  The noncompact category of all Hilbert spaces
is not compact closed; its dualizable sector is the finite-dimensional one.  No novelty is
claimed for `(160)`.

### The Cartier-orbit package

Let \(\rho\) be a nontrivial Xi zero and let
\[
 {\cal O}_\rho
 =
 \{\rho,\overline\rho,1-\rho,1-\overline\rho\}
                                                               \tag{161}
\]
with repetitions removed.  The local principal-conormal object of the Xi Cartier divisor,
together with its multiplicity jets, has a finite perfect Koszul model at every member of
`(161)`.  Write
\[
 K_\rho
 =
 \bigoplus_{\sigma\in{\cal O}_\rho}
 K_{\Xi,\sigma}.                                             \tag{162}
\]
The full orbit package, rather than one fibre, is the correct dagger object: reflection and
complex conjugation need not fix an off-line fibre separately.

Prime half-density dilation preserves `(162)`.  On its semisimple conormal line at \(\sigma\), it
has character
\[
 \lambda_p(\sigma)=p^{\sigma-1/2}.                          \tag{163}
\]
This is the already-proved Tate/Meyer/BV covariance.  Nilpotent multiplicity jets only add a
finite upper-triangular part with the same diagonal character.

Suppose a source realization, constructed before choosing \(\rho\), has the following properties
on `(162)`:

1. strict Cartier base change identifies the realized point package with
   \({\cal R}(K_\rho)\);
2. \({\cal R}\) is dagger Frobenius monoidal on the rigid defect subcategory containing
   \(K_\rho\);
3. \({\cal R}\) is conservative on every nonzero Xi point package; and
4. prime half-density dilation is carried to a unitary operator and `(163)` is preserved.

Then \({\cal R}(K_\rho)\) is nonzero and finite-dimensional.  It is invariant under the realized
prime unitary.  Hence `(163)` is an eigenvalue of a finite-dimensional unitary, so
\[
 |p^{\rho-1/2}|=1,
 \qquad
 \operatorname{Re}\rho=\frac12.                           \tag{164}
\]
This proves RH.  Exact base change also retains the finite nilpotent package and therefore does
not discard multiplicity.

`[PAPER-PROVED — DUALIZABLE-CHARGE PURITY CONSUMER]`

The proof of `(164)` is complete under the four displayed realization properties.  It is not new
mathematics and should not be formalized as an RH advance.  Its value is that it removes two
unnecessary hypotheses from Section 24:

```text
maximal boundary representation: not needed;
explicit no-diffusion axiom:      not needed;

Frobenius-monoidal preservation of the rigid defect:
  automatically forbids diffusion;

conservativity:
  forbids annihilation;

dagger prime-equivariance:
  supplies unitary dynamics.
```

### Frozen conjecture: source Frobenius realization of the Xi defect

`[CONJECTURE] [XI_SOURCE_FROBENIUS_CARTIER_REALIZATION]`

The completed ordinary-prime Euler--Gamma/co-Poisson source has a positive realization functor
\[
 {\cal R}_{\rm src}:
 {\rm Perf}_{\rm def}({\cal C}_{\rm Euler/Gamma/PZ})
 \longrightarrow {\rm Hilb}                               \tag{165}
\]
defined before divisor specialization, with these properties:

1. it is dagger Frobenius monoidal on the rigid subcategory generated by the cofinal
   Euler-gauge defect, its Cartier conormal, reflection, and multiplicity Koszul objects;
2. its dagger is induced by the source Fourier/real-orientation involution and sends normalized
   prime dilation to a unitary;
3. derived Cartier base change to every Xi point commutes strictly with `(165)`;
4. it is conservative on every nonzero finite-length Xi conormal package; and
5. it is compatible with prime enlargement, Gamma/BV transgression, and the literal integral
   Rost--Schmid source lattice.

This is a truth-hunch in the user's strict sense.  No proof method is included in the conjecture.
Its attraction is explanatory: it asks for one universal preservation law rather than an
independent sign, norm bound, recurrence estimate, or anti-diffusion clause at every zero.

The completion need not be strongly monoidal on the infinite bulk.  Hypertranscendence and the
all-prime gauge defect force that bulk to be noncompact and infinite-order.  The claim is
selective rigidity:

> completion may enlarge the nondualizable bulk, but it preserves the dualizable arithmetic
> defect sector and its dagger.

This is the precise sense in which infinity and finite divisor charge coexist.

### What the prior obstructions mean

```text
finite prime truncations:
  retain dualizable defect packets, but not the complete unitary prime action;

ambient adelic L2:
  has the dagger-unitary prime action, but Cartier base change is nonconservative and all point
  packages vanish into continuous spectrum;

Meyer/co-Poisson quotient:
  retains finite Xi packages, but has no proved positive dagger Frobenius realization;

Poisson/GNS dilation of an interior character:
  is only a compression/lax realization on the point object and sends one dualizable line to an
  infinite nondualizable cyclic cloud;

plain C*-boundary:
  preserves unitary points but annihilates nonunitary point packages and the Gamma/BV ideal;

functional equation:
  supplies the dagger orbit `(161)`, but not a positive realization of that orbit;

hypertranscendence:
  forces the full rigid source record and prevents finite-order scalarization, but does not by
  itself make its realization Frobenius or conservative;

generalized-prime off-line systems:
  must fail strict dagger Frobenius base change, conservativity on the point package, or the
  literal ordinary-prime source comparison.  Positive density and reflection do not supply
  those properties.
```

The universal law is therefore:

> **Arithmetic compact charge is conserved as dualizability.**  A positive source realization
> may move or enlarge bulk information, but a Cartier divisor charge that is dualizable before
> completion cannot become a diffuse boundary state after a conservative Frobenius-monoidal
> realization.

For Xi, prime half-density covariance turns that conservation law into `(164)`.

### Corpus weld and first construction theorem

Two existing programmes supply different halves of `(165)`:

1. `DAC_FINITE_CORRESPONDENCE_ANALYTIC_REALIZATION` asks for a symmetric monoidal Deninger
   realization of the rational-Witt/Milnor source;
2. `DAC_ARITHMETIC_CALDERON_GREEN_INTERMEDIATE_EXTENSION` asks for a positive dagger Hodge
   realization faithful on Meyer's quotient.

They have previously been treated as parallel bridges.  The new construction target is their
agreement on the rigid cofinal-defect subcategory.  It is unnecessary to build a universal
terminal envelope first.

The first non-parent theorem must construct one explicit Frobenius comparison square for the
all-prime Euler-gauge commutator anomaly and prove strict Cartier base change for its principal
conormal:
\[
\begin{CD}
 K_{\Xi}^{\rm src}\otimes (K_{\Xi}^{\rm src})^\vee
     @>>> \mathbbm 1_{\rm src}\\
 @V{{\cal R}_{\rm src}\otimes{\cal R}_{\rm src}}VV
     @VV{{\cal R}_{\rm src}}V\\
 {\cal R}_{\rm src}(K_{\Xi}^{\rm src})
   \widehat\otimes
 {\cal R}_{\rm src}((K_{\Xi}^{\rm src})^\vee)
     @>>> \mathbb C .
\end{CD}                                                     \tag{166}
\]
The square must be formed before zero expansion and then commute with the finite-orbit base
change `(161)`.  The evaluation and coevaluation composites must be identities in the completed
defect sector, not merely nonzero scalar pairings.

Failure of `(166)` has a sharp positive survivor: its cofiber is the **duality leakage object**.
Under point base change, that object classifies exactly how much of a finite Xi charge is
annihilated or converted into Poisson storage.  Constructing and identifying this cofiber is
therefore useful even if the conjecture is false.

### Hostile boundary

1. A lax monoidal or state-valued GNS construction does not preserve duals and is defeated by
   the disk Poisson model.
2. Duality of \(K_{\Xi,\rho}\) with \(K_{\Xi,1-\overline\rho}\) is not positivity.  Dagger
   compatibility must be proved on the full orbit `(161)`.
3. Conservativity cannot be inferred from monoidality.  A point-supported perfect object may be
   sent to zero.
4. Strict Cartier base change is RH-bearing.  It must be derived from the literal source
   comparison, not declared as the definition of the target fibre.
5. A symmetric monoidal realization into completed locally convex spaces is insufficient until
   its rigid defect sector lands in Hilbert dualizable objects with the source dagger.
6. The conormal being a line before completion does not prevent diffusion under a non-Frobenius
   functor.
7. Proving `(160)` or the finite-isometry lemma again in Lean would be theatre; the only
   formalization-worthy theorem is a source-specific instance of `(166)` or a nonzero computed
   duality-leakage cofiber.

Primary parent boundaries:

- Brian Day and Craig Pastro, *Note on Frobenius monoidal functors*,
  https://arxiv.org/abs/0801.4107;
- Peter Selinger, *Finite dimensional Hilbert spaces are complete for dagger compact closed
  categories*, https://arxiv.org/abs/1207.6972.

Targeted corpus and literature searches found the parent dualizability statements and the two
separate Deninger realization conjectures, but no source-relative theorem joining the
ordinary-prime Euler--Gamma/co-Poisson Cartier defect to a conservative dagger Frobenius Hilbert
realization.  This is preliminary noncollision, not a priority claim.

## 26. The universal defect is multiplicative-domain curvature

Section 25 identifies the categorical preservation law but leaves its analytic shadows separate.
They are in fact exact transforms of one real curvature.

For a complex divisor point \(\rho\) and a rational prime \(p\), put
\[
 \delta(\rho)=1-\rho-\overline\rho\in\mathbb R,\qquad
 z_p(\rho)=p^{1/2-\rho}.                                  \tag{167}
\]
Here \(z_p\) is the centered prime character used by the Wold, Koszul, Kakutani, and
Cartier-orbit realizations.  Let
\[
 C_p(\rho)
 =(\log p)\left(p^{-\overline\rho}-p^{-(1-\rho)}\right)   \tag{168}
\]
be the already formalized FE--Schwarz prime seam.

### Purity exponential-transgression theorem `[PAPER-PROVED]`

The following identities hold:
\[
 |z_p(\rho)|^2=p^{\delta(\rho)},                          \tag{169}
\]
\[
 C_p(\rho)
 =(\log p)\,p^{-(1-\rho)}
   \left(p^{\delta(\rho)}-1\right)
 =-(\log p)\,p^{-(1-\rho)}
   \left(1-|z_p(\rho)|^2\right).                          \tag{170}
\]
If \(\lambda_\rho=\rho\) denotes the uncentered Deninger Frobenius eigenvalue, the local Hodge
calculation is
\[
 \Theta_c\star_\rho-\star_\rho\Theta
 =\delta(\rho)\star_\rho.                                 \tag{171}
\]
The local form \(\star_\rho\) is nonzero unconditionally.  Therefore, for every \(p\),
\[
\begin{aligned}
 \operatorname{Re}\rho=\tfrac12
 &\Longleftrightarrow \delta(\rho)=0\\
 &\Longleftrightarrow |z_p(\rho)|=1\\
 &\Longleftrightarrow C_p(\rho)=0\\
 &\Longleftrightarrow
   \Theta_c\star_\rho=\star_\rho\Theta.                   \tag{172}
\end{aligned}
\]

**Proof.**  Since the base \(p\) is positive real,
\[
 |p^{1/2-\rho}|^2
 =p^{1/2-\rho}p^{1/2-\overline\rho}
 =p^{1-\rho-\overline\rho},
\]
which proves `(169)`.  Factoring \(p^{-(1-\rho)}\) from `(168)` gives
\[
 p^{-\overline\rho}
 =p^{-(1-\rho)}p^{1-\rho-\overline\rho},
\]
hence `(170)`.  Equation `(171)` is the proved Deninger local-Hodge obstruction.  Since
\(\log p\ne0\), \(p^{-(1-\rho)}\ne0\), the real exponential is injective, and
\(\star_\rho\ne0\), all equivalences in `(172)` follow. `QED`

There is also a canonical divided-difference form:
\[
 {C_p(\rho)\over
   \delta(\rho)(\log p)^2p^{-(1-\rho)}}
 =
 {e^{\delta(\rho)\log p}-1\over\delta(\rho)\log p},       \tag{173}
\]
with continuous value \(1\) at \(\delta=0\).  For real \(\delta\), the right side is strictly
positive.  Thus the seam is not merely another reader with the same zero locus.  It is the finite
prime holonomy of the infinitesimal Hodge curvature, with no extra zero and no sign cancellation.

### Poisson diffusion is the same curvature

Let \(\Phi_z:C(\mathbb T)\to\mathbb C\) be the Poisson state at \(|z|<1\), and let \(u(\zeta)=\zeta\)
be the boundary unitary.  Then
\[
 \Phi_z(u)=z,\qquad
 \Phi_z(u^*u)-\Phi_z(u)^*\Phi_z(u)=1-|z|^2.               \tag{174}
\]
In the Poisson GNS representation this is exactly
\[
 \|(1-P_{\mathbb C\xi})\,U\xi\|^2=1-|z|^2,               \tag{175}
\]
the squared component by which the point character spreads into the orthogonal boundary cloud.
For \(\delta(\rho)<0\), substitute \(z=z_p(\rho)\) into `(174)`:
\[
 D_p(\rho)=1-p^{\delta(\rho)}
 =-{C_p(\rho)\over(\log p)p^{-(1-\rho)}}.                \tag{176}
\]
For \(\delta(\rho)>0\), the reflected orbit point
\(1-\overline\rho\) has curvature \(-\delta(\rho)\), lies in the disk chart, and has defect
\(1-p^{-\delta(\rho)}\).  Hence every off-line quartet has a strictly positive Poisson-diffusion
defect on one of its two oriented disk faces.

Equations `(171)`, `(170)`, and `(176)` give the promised reinterpretation:

```text
delta(rho)                    = infinitesimal Hodge curvature;
p^delta                       = prime holonomy;
p^delta-1                     = finite transgression;
C_p(rho)                      = phase-weighted Euler seam;
1-|z_p(rho)|^2                = Kadison--Schwarz / Stinespring leakage;
off-line Kakutani separation  = all-prime accumulation of that leakage;
Poisson boundary cloud        = dilation realizing the leakage;
duality-leakage cofiber       = categorical receiver before scalarization.
```

These are not analogies and not independent RH criteria.  They are realizations of one curvature.
The exact seam/norm-growth theorem is the quadratic all-divisor accumulation of `(170)`;
the finite-fibre trilemma classifies what completion can do when `(174)` is nonzero.

### Multiplicative-domain meaning

For a unital completely positive map \(\Phi:A\to B\) and a unitary \(u\in A\), the
Kadison--Schwarz defect
\[
 D_\Phi(u)=1-\Phi(u)^*\Phi(u)\ge0                         \tag{177}
\]
vanishes, together with the identical defect for \(u^*\), exactly when \(u\) belongs to the
multiplicative domain of \(\Phi\).  If \(\Phi(u)=z\,1\) on a nonzero point fibre, `(177)` becomes
\((1-|z|^2)1\).  Thus:

> **A positive realization retains a prime character as a finite multiplicative point exactly
> when the normalized prime unitary lies in the point realization's multiplicative domain.**

Off the unitary axis, a positive realization has only the three outcomes already found in
Section 24: annihilate the point, diffuse it through a nonmultiplicative Stinespring dilation, or
retain it in a nonmaximal/non-dagger chart.  The multiplicative-domain defect is the scalar shadow
of the duality-leakage object from `(166)`.

This also explains why the proposed Frobenius condition is natural rather than decorative.  The
reduced support of a finite Cartier point carries copying and deletion maps from its diagonal and
structure correspondences.  A dagger strong-monoidal realization preserves this special dagger
Frobenius structure.  Its image remains a copyable classical charge, so the normalized prime
unitary acts multiplicatively on the semisimple point character; no Poisson randomization is
possible.

The reduced qualifier is essential.  A multiplicity-\(d\) Cartier thickening has a finite perfect
Koszul/Frobenius package but need not be a special dagger classical object; requiring special
dagger copyability of the whole thickening could silently force semisimplicity and hence simple
zeros.  The nilpotent multiplicity package is retained separately as a dualizable module over the
copyable reduced support.  The weaker Frobenius-monoidal condition of Section 25 preserves that
dualizable package even when strong monoidality is unavailable.

### Refined frozen conjecture: Cartier classicality survives completion

`[CONJECTURE] [XI_SOURCE_CARTIER_CLASSICALITY_BASE_CHANGE]`

The source-first co-Poisson/Xi Cartier package admits a model as a derived zero locus in the
ordinary-prime finite-correspondence category, constructed before selecting a zero.  Its reduced
support has diagonal, counit, and transpose correspondences; its full thickening has the
reflection orbit and multiplicity Koszul structure.  The finite-correspondence analytic
realization satisfies, on the rigid subcategory generated by this package:

1. after strict Cartier base change, the reduced-support diagonal and counit survive the all-prime
   completion as a special dagger Frobenius object, while the full multiplicity package survives
   as a dualizable module of the same finite length;
2. transpose correspondence realizes as the positive analytic dagger;
3. derived Cartier base change is strict and conservative on every finite Xi orbit package;
4. normalized prime dilation realizes as the source unitary and preserves the source action on
   the semisimple conormal line; and
5. the construction commutes with prime enlargement, Gamma/BV transgression, and the integral
   Rost--Schmid boundary.

This is a construction form of `XI_SOURCE_FROBENIUS_CARTIER_REALIZATION`, not an additional
purity axiom.  If true, the reduced image of every nonzero Xi Cartier package is copyable and lies
in the multiplicative domain of every normalized prime unitary, while its nilpotent jets retain
their length through dualizability.  Equations `(167)` and `(177)` force
\(|z_p(\rho)|=1\), and `(172)` gives RH without asserting simplicity.

The first source-specific theorem is correspondingly sharper than `(166)`: construct the
completed image of the actual reduced-support Cartier diagonal and prove
\[
 {\cal R}_{\rm src}(\Delta_{K_{\rm red}})
 =
 \Delta_{{\cal R}_{\rm src}(K_{\rm red})},\qquad
 {\cal R}_{\rm src}(\Delta_{K_{\rm red}}^\top)
 =
 {\cal R}_{\rm src}(\Delta_{K_{\rm red}})^\dagger,       \tag{178}
\]
then prove `(178)` commutes with principal-conormal base change.  Dualizability follows from the
Frobenius identities; multiplicative-domain vanishing follows from dagger copyability.  If
`(178)` fails, its mapping cofiber is the duality leakage object, whose \(p\)-local scalar shadow
must recover `(176)`.  This gives a computable falsifier rather than an unspecified failure of
positivity.

### Hostile audit

1. Choi's multiplicative-domain theorem, Stinespring dilation, special dagger Frobenius
   structures, and preservation of duals by Frobenius monoidal functors are parent mathematics.
2. The exact algebra in `(169)`--`(173)` is elementary.  Candidate-new content is the
   cross-realization identification with the independently constructed Deninger Hodge form,
   FE--Schwarz seam, Poisson diffusion, and source Cartier duality leakage.
3. Local positive Deninger forms do not prove `(178)`: they exist at hypothetical off-line zeros
   and fail Frobenius commutation by exactly `(171)`.
4. A positive generalized-prime density does not prove multiplicative-domain membership of its
   divisor character.  The explicit off-line Euler systems realize nonzero `(174)`.
5. Functional-equation reflection exchanges \(\delta\) and \(-\delta\); it pairs the two leakage
   faces but does not make either vanish.
6. Hypertranscendence supplies a large source record but does not preserve a Cartier diagonal
   through completion.  The positive HT divisor frame remains a counterexample to any such
   inference.
7. Merely formalizing `(169)`--`(173)` would be theatre.  Formalization becomes significant only
   when the theorem connects the existing Lean Deninger obstruction and prime-seam definitions,
   or when a source-specific instance of `(178)` is constructed.

Primary literature boundaries are Choi's multiplicative-domain theorem, Day--Pastro's preservation
of duals by Frobenius monoidal functors, and the purity theorem for isometric comonoids in
`CPM(fHilb)`.  Targeted corpus and literature searches found these parents separately but no
identification of Deninger Hodge curvature, the Xi FE--Schwarz prime seam, Poisson
Kadison--Schwarz leakage, and Cartier Frobenius failure as the infinitesimal, holonomy,
Stinespring, and categorical images of `(167)`.  This is a preliminary noncollision finding, not
a priority claim.

## 27. The missing universal law: an adelic Hodge index for completion curvature

The preceding interpretation is still incomplete.  It identifies one curvature and says what
would make it vanish, but it does not explain why the source should make it vanish.  Two tempting
answers are already present in the corpus and therefore cannot be promoted as new progress:

1. require the Xi conormal to be normal in the critical prime-valuation sector;
2. require its polar regulator to land in the mixed \(L^1/L^2\) Kummer space.

Both are exact RH consumers, but fibrewise they are RH-equivalent landing assumptions.  Likewise,
finite-stage dagger monoidality is insufficient: every finite packet can be perfect while
normalization amplifies the source transition from the summable \(a_P/p\) scale to the
nonsummable \(1/p\) scale.  The missing theorem must operate before this normalization and explain
the landing as a consequence.

### The proposed change of interpretation

The source-producing and divisor-reporting completions have the Beck--Chevalley comparison
\({\rm BC}_X\) and completion-curvature object
\[
 \Omega_X=\operatorname{Cone}({\rm BC}_X)
\]
from `source-effective-boundary-complexity-conservation-law.md`.  Section 26 computes the scalar
curvature of its reduced Xi fibre:
\[
 \delta(\rho)=1-\rho-\overline\rho.                       \tag{179}
\]
The prime seam, Poisson leakage, Hellinger separation, projective Weyl leakage, and Deninger
Hodge commutator are positive or oriented analytic realizations of \(\Omega_\rho\).

What was missing is a second, source-side realization of the same object.  The ordinary-prime
finite-correspondence source, its integral Rost--Schmid boundary, and its principal Cartier
conormal should make \(\Omega_\rho\) a **primitive arithmetic intersection class**.  A Hodge index
law identifies its negative square with the analytic defect energy:
\[
 \underbrace{q_{\rm src}(\Omega_\rho,\Omega_\rho)}_{\text{primitive source intersection}}
 \leq0,
 \qquad
 \underbrace{q_{\rm an}(\Omega_\rho,\Omega_\rho)}_{\text{completion-defect energy}}
 \geq0.                                                     \tag{180}
\]
The sign alone does not force purity: it is exactly compatible with an off-line defect.  The
decisive source statement is that, after every first-trace and prime-infinity boundary term has
been restored, \(\Omega_X\) is the boundary of the **same principal enhanced arithmetic
conormal**.  Hence its arithmetic intersection class vanishes.  The comparison is
\[
 [\Omega_X]_{\widehat{\rm CH}}=0,
 \qquad
 q_{\rm an}(\Omega_\rho,\Omega_\rho)
 =
 -q_{\rm src}(\Omega_\rho,\Omega_\rho).                    \tag{181}
\]
The first equality makes the source square zero; the second and faithfulness of the analytic
realization make the defect energy zero.

This is the analogue, for a principal divisor of a hypertranscendental Euler object, of the role
played by the Hodge index theorem in the function-field proof.  It is not an ordinary Arakelov
application: a Xi zero is not an algebraic closed point, and its prime holonomies are generally
transcendental.  The required new object is an arithmetic intersection theory for
source-effectively normalized **hypertranscendental Cartier conormals**, retaining the integral
prime correspondence, the analytic divisor, the source-normal Rees boundary, and the
Gamma/archimedean face simultaneously.

### Frozen universal conjecture

`[CONJECTURE] [HT_ADELIC_PRINCIPAL_COMPLETION_CURVATURE_HODGE_INDEX]`

Let \(X\) be a source-effectively normalized, integral, self-dual hypertranscendental Euler object
with:

1. an ordinary-prime finite-correspondence presentation;
2. a principal derived Cartier divisor \(K_X\), constructed before selecting a divisor point;
3. the six-channel effective lift and its higher comparison coherence;
4. a source reflection package, including its Gamma/archimedean boundary; and
5. a distinguished source-effective principal conormal.

On the rigid derived subcategory generated by \(K_X\), there is a presentation-independent
intersection realization
\[
 {\cal I}_{\rm HT}:
 \langle\Omega_X\rangle_{\rm rig}
 \longrightarrow
 {\cal H}_{\rm prim}^{\rm ar},
                                                               \tag{182}
\]
and a positive analytic realization
\[
 {\cal A}_{\rm HT}:
 \langle\Omega_X\rangle_{\rm rig}
 \longrightarrow
 {\cal H}_{\rm def}^{\rm an},                                  \tag{183}
\]
such that:

1. **Enhanced arithmetic principality.**  The completion curvature of the distinguished
   principal conormal is zero in the enhanced arithmetic Chow/cofiber group after adjoining its
   Rost--Schmid, first-trace, source-normal, and Gamma boundary terms.  In particular it has
   primitive degree zero and zero source self-intersection.
2. **Hypertranscendental Hodge index.**  The source intersection form is negative semidefinite on
   this primitive subspace.
3. **Defect-energy positivity.**  The analytic form is positive semidefinite and faithful on the
   reduced completion-curvature support.
4. **Index--energy comparison.**  Equations `(182)` and `(183)` identify analytic energy with the
   negative source square as in `(181)`, including the source-normal/Rees boundary term; no
   first-trace or prime-infinity residue is dropped.
5. **Strict Cartier base change.**  The comparison commutes with reduced divisor base change and
   retains the full multiplicity package as a same-length dualizable module.
6. **Dagger and product formula.**  Transpose, reflection, Frobenius/Verschiebung degree, and the
   Gamma/real boundary are compatible with the comparison.  No divisor-selected metric or
   RH-equivalent sign is inserted.

The conjecture is a truth-hunch.  No proof is presently known.  Provability is not part of its
statement.

### Exact zeta consumer

For the completed zeta source, the independently proved curvature dictionary gives, at each
nontrivial zero \(\rho\),
\[
 q_{\rm an}(\Omega_\rho,\Omega_\rho)
 =
 W(\rho)\,\delta(\rho)^2,                                  \tag{184}
\]
where \(W(\rho)>0\) is the faithful reduced-fibre weight.  The weight can be read in equivalent
charts:

- as the positive divided-exponential factor in `(173)`;
- as the Hellinger/Fisher coefficient of the prime-valuation sector;
- as projective Weyl leakage in the ordinary-prime source clock;
- as the squared norm of the duality-leakage cofiber; or
- as the positive local Hodge norm of the Deninger commutator.

Only positivity and faithfulness of \(W(\rho)\), not a preferred formula for it, enter the
argument.  Enhanced arithmetic principality and equations `(180)`--`(184)` give
\[
 0\leq W(\rho)\delta(\rho)^2
 =q_{\rm an}(\Omega_\rho,\Omega_\rho)
 =-q_{\rm src}(\Omega_\rho,\Omega_\rho)
 =0.
                                                               \tag{185}
\]
Hence \(\delta(\rho)=0\), so
\[
 \operatorname{Re}\rho=\frac12.                              \tag{186}
\]
Strict base change applies this to every reduced support point, while dualizability retains
multiplicity without asserting simplicity.  Thus the zeta instance of the conjecture proves RH.

### Why this subsumes the previous shadows

The universal law changes the status of the earlier completion criteria:

```text
Deninger Hodge defect        = infinitesimal curvature in (184);
prime FE--Schwarz seam       = finite holonomy of the same class;
Poisson/Stinespring leakage  = positive analytic energy;
Kakutani sector separation   = all-prime energy accumulation;
Wold/BV first-trace anomaly  = boundary term needed in (181);
Cartier dagger failure       = categorical support of the curvature;
polar Kummer nonlanding      = failure to have a finite-energy harmonic representative;
Meyer point-fibre escape     = loss of the class before intersection realization.
```

Vanishing of \(\Omega_X\) then implies all the desired consequences at once:

1. the normalized prime unitary lies in the multiplicative domain;
2. reduced Cartier support remains copyable after completion;
3. the polar Kummer regulator has no radial charge at prime infinity;
4. the Xi conormal is normal in the critical product sector;
5. finite Frobenius/Verschiebung unitarity survives the infinite limit; and
6. source and reporter completions commute strictly on the divisor package.

These are corollaries of a source index theorem, not independent hypotheses.

### Why hypertranscendence matters

Hypertranscendence alone supplies none of `(180)`--`(181)`: the explicit positive HT off-line
divisor frames already disprove that.  Its role is structural.  It forces work outside the
finite-rank holonomic category and makes the completion-curvature object, complete transport
class, flat boundary face, and higher fracture coherence unavoidable.  The proposed Hodge index
is therefore not a theorem for bare HT functions.  It is a theorem only for the
source-effectively normalized integral Euler stratum.

Multiplication by an arbitrary self-dual off-line orbit polynomial fails this stratum: it changes
the analytic divisor without producing the corresponding ordinary-prime principal conormal and
intersection class.  The generalized-prime off-line systems likewise have positive scalar
shadows but do not carry the literal rational-Witt/ordinary-prime finite-correspondence source
and its comparison `(181)`.

### First theorem to construct

The first non-theatrical target is not the full conjecture and not another scalar equivalence.
For the monic finite-correspondence generators of the rational-Witt source:

1. construct the reduced Cartier completion-curvature class before analytic evaluation;
2. construct its codimension-one source intersection pairing, including transpose and the
   Rost--Schmid/Gamma boundary;
3. prove that the fully enhanced curvature is the boundary of the principal source conormal and
   therefore has zero class and zero source square;
4. prove primitive negativity and that analytic character evaluation sends the negative square
   to the already constructed projective-Weyl/Hellinger defect energy; and
5. prove strict compatibility with the co-Poisson principal-conormal base change.

The exact open square is therefore
\[
\begin{CD}
 \Omega_{K_X}^{\otimes2} @>{q_{\rm src}}>> {\bf1}_{\rm ar}\\
 @V{{\cal R}_{\rm src}^{\otimes2}}VV       @VV{\operatorname{place}}V\\
 {\cal R}_{\rm src}(\Omega_{K_X})^{\otimes2}
       @>{-q_{\rm an}}>> {\bf1}_{L^1/L^2}.
\end{CD}                                                     \tag{187}
\]
Equation `(178)` is the dagger/diagonal edge of `(187)`.  The polar-regulator landing is its
harmonic consequence.  This identifies one construction target rather than three unrelated open
cores.

### Hostile audit

1. Ordinary arithmetic Hodge index theorems apply to adelic line bundles on algebraic varieties;
   they do not construct `(182)` for a hypertranscendental divisor.
2. Weil's function-field argument is a parent interpretation, not the missing zeta theorem.
3. Calling completion leakage an “intersection class” does not prove enhanced arithmetic
   principality, primitive negativity, or the comparison in `(181)`.
4. Defining \(q_{\rm src}\) by the right side of `(184)` would be circular.  It must be built from
   finite correspondences and the integral boundary before character evaluation.
5. Local Deninger positivity exists at hypothetical off-line zeros and supplies only the
   nonnegative analytic energy.  Hodge-index negativity by itself is compatible with that energy
   through the minus sign in `(181)` and does not prove purity.
6. A regularized scalar degree can hide prime-infinity leakage.  The full source-normal boundary
   term in Clause 4 is load-bearing.
7. If an explicit off-line generalized-prime system admits the same source-effective integral
   finite-correspondence lift and satisfies `(187)`, the conjecture is false.

### Literature boundary

Parent theories include Weil's intersection-theoretic proof over finite fields; arithmetic Hodge
index theorems of Faltings--Hriljac--Moriwaki and Yuan--Zhang; \(l^1\)-adelic Cartier divisors;
intersection theory over adelic curves; enhanced irregular Riemann--Hilbert theory; and
arithmetic differential geometry.  Targeted searches found these ingredients separately but no
intersection theory for source-effectively normalized hypertranscendental Euler conormals, and no
index--energy comparison whose analytic fibre is the Deninger/seam/Hellinger/Weyl completion
curvature `(184)`.  This is a preliminary noncollision result, not a priority claim.
