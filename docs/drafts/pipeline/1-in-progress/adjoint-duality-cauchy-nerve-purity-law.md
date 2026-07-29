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
