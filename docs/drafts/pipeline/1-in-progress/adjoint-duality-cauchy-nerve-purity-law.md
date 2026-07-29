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
