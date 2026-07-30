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

`[WITHDRAWN HUNCH] [HT_ADELIC_PRINCIPAL_COMPLETION_CURVATURE_HODGE_INDEX]`

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

### Topological refinement: off-line curvature consumes Euler boundary index

The metric square in `(184)` measures the size of transverse displacement, but it misses a second
piece of information: whether a transverse orbit exists at all.  The publication-ready
Julia--Euler--Weil packet theorem computes that topological charge exactly.  For every finite
inserted off-line quartet packet \(J\),
\[
 \frac{Q_{\rm Julia}(J)}{4\pi}
 =
 \Delta\operatorname{ord}_{s=1}(F_J)
 =
 \operatorname{ind}_{-}({\cal W}_J)
 =
 2|J|.                                                       \tag{188}
\]
This identity is stronger than a sign.  It says that a transverse divisor orbit, Euler boundary
normalization, and negative Weil block are three realizations of one integer index.

The theorem currently applies to inserted packets.  It explicitly warns that retaining the
simple pole only forbids insertions inside that deformation class; it says nothing about a
hypothetical **native** off-line zero of zeta.  The missing jump is an excision theorem saying that
the index in `(188)` belongs to the source-native completion-curvature object, not to the chosen
rational surgery presentation.

`[WITHDRAWN HUNCH] [HT_SOURCE_NATIVE_EULER_BOUNDARY_INDEX_CONSERVATION]`

For every source-effectively normalized integral self-dual HT Euler object in the class of the
preceding conjecture, the enhanced completion-curvature object carries a locally finite
nonnegative transverse index measure
\[
 \operatorname{Ind}_{\perp}(\Omega_X)
 \in {\cal M}_{\rm lf}^{+}(|K_X|/\langle{\rm FE,Schwarz}\rangle;\mathbb Z),
                                                               \tag{189}
\]
constructed before divisor specialization, such that:

1. every genuine off-fixed reflection quartet of reduced support has mass \(2\), independent of
   height and horizontal displacement;
2. critical-line support has transverse mass \(0\), while multiplicity jets remain in a separate
   length filtration;
3. restriction to a finite divisor window is excisive and agrees with Julia--Ward charge and the
   localized Weil negative index;
4. its pushforward to the Euler boundary equals the **excess source boundary index** above the
   source-minimal pole/endpoint normalization;
5. this equality is invariant under source presentation and includes first-trace, Gamma, and
   prime-infinity boundary terms; and
6. analytic multiplication by an external self-dual orbit polynomial changes both sides by the
   packet index `(188)`, rather than being silently treated as a source equivalence.

For the Riemann source the minimal boundary normalization is its one simple pole at \(s=1\), so
the excess boundary index is zero.  Clause 4 would give
\[
 \operatorname{Ind}_{\perp}(\Omega_\xi)(|K_\xi|)=0.          \tag{190}
\]
Nonnegativity and Clause 1 then exclude every off-critical quartet.  Functional-equation and
Schwarz symmetry give RH.  No summation over the full zero divisor is needed: excision says that
any one hypothetical off-line orbit already contributes a positive compactly supported
submeasure, contradicting `(190)`.

The target and surgery ends are already formalized unconditionally:

- `finiteQuartet_eulerWardWeil_index_law` proves `(188)` for every finite generic packet;
- `xiEndpointWeightedWardIndex_eq_twoPi_offLineCharge` constructs a convergent positive
  source-weighted analytic index of the actual Xi divisor; and
- `xiEndpointWeightedWardIndex_eq_zero_iff_rh` proves that its vanishing is exactly RH.

These theorems do not construct Clause 4.  They make its required output exact: a pre-divisor
boundary-index pushforward must force the already constructed Xi Ward index to vanish from the
zero excess source budget.  No new divisor scalar needs to be invented.

Equations `(181)` and `(188)` are the metric and topological parts of one proposed enhanced index
theorem:

```text
K-theoretic/transverse index  -> whether completion curvature is present;
Hodge/energy realization     -> how far its fibre is from the critical locus;
Euler boundary pushforward   -> source budget that must carry the curvature;
principal enhanced class     -> conservation through every completion face.
```

If this law is correct, it explains why all target-only criteria fail.  They measure the analytic
charge after it has appeared but never compare it with the fixed source budget.  It also explains
why the simple pole is relevant only when coupled to the literal discrete-prime source and strict
presentation-independent excision: pole order by itself has no control over native zeros.

#### Hostile audit of the index refinement

1. Equation `(188)` is proved only for finite rational quartet surgery.  Native excision is the
   entire new claim.
2. A simple pole, Euler product, functional equation, or hypertranscendence alone does not imply
   `(190)`.
3. Defining the source boundary index by counting off-line zeros would be circular.  It must be
   constructed from finite correspondences, endpoint normalization, and the enhanced boundary
   complex before analytic divisor evaluation.
4. The packet Weil form supplies a negative-index count, not an unconditional global
   index-additivity theorem.  Clause 3 must prove the missing localization.
5. Infinite off-line divisors cannot be assigned a regularized signed total that cancels.  The
   conjecture requires a nonnegative locally finite measure and compact-window excision.
6. Positive generalized-prime systems and external HT orbit insertions are falsifiers of any
   version omitting integral ordinary-prime source minimality.
7. Helson zeta functions use the literal rational primes with completely multiplicative
   unimodular coefficients and admit highly flexible prescribed zero/pole sets after meromorphic
   continuation.  Thus ordinary-prime discreteness and an Euler product are still insufficient.
   The conjecture must use the positive/integral finite-correspondence lift, transpose, source
   reflection, and enhanced principal-conormal excision; it cannot be a theorem about bare
   ordinary-prime Euler products.

The first source theorem is now even narrower than `(187)`: construct one
presentation-independent boundary-index map on the reduced monic rational-Witt Cartier
generator, prove its excision square, and show that external quartet multiplication changes its
value by two.  Only after that finite source theorem exists is passage to the native Xi divisor a
meaningful construction problem.

Primary hostile comparisons are Bochkov--Romanov, *On zeroes and poles of Helson zeta functions*
(`arXiv:2106.15949`), and Andersson, *Mittag-Leffler type theorems for Helson zeta-functions*
(`arXiv:2408.15713`).  They show why actual-prime Euler support cannot replace the enhanced
integral/source-effective hypotheses.

## 28. Reflected forward contractivity is the missing completion law

### Hostile correction to Section 27

Both speculative refinements in Section 27 are withdrawn.

- Enhanced arithmetic principality does not make a nonzero curvature class have square zero.
  Hodge index supplies a polarization and an adjoint, not that vanishing.
- A native numerator zero does not consume denominator pole order.  Function-field cohomology
  already shows that middle Frobenius spectrum can vary while the endpoint factors remain fixed.
  The packet index law is a surgery law, not a native Euler-budget conservation theorem.

The surviving Hodge insight must also respect the exact source asymmetry
\[
 F_pV_p=p\,\mathrm{id}.                                      \tag{191}
\]
The reverse scalar relation \(V_pF_p=p\,\mathrm{id}\) is generally false.  Requiring a bilateral
unitary on the original source therefore asks for more than finite-correspondence geometry gives.
The functional equation supplies the missing reverse inequality without supplying an inverse
operator.

### Reflected power-equicontinuous purity theorem

Let \(\Phi\) be a Hausdorff locally convex complex vector space and let
\(U:\Phi\to\Phi\) be continuous.  Say that \(U\) is **forward power-equicontinuous** if, for every
continuous seminorm \(q\), there are a continuous seminorm \(r\) and \(C>0\) such that
\[
 q(U^n x)\le C r(x)\qquad(x\in\Phi,\ n\ge0).                \tag{192}
\]

`[PAPER-PROVED] [REFLECTED_POWER_EQUICONTINUOUS_TRANSPOSE_PURITY]`

Suppose \(0\ne\ell\in\Phi'\) and
\[
 U'\ell=\lambda\ell.                                      \tag{193}
\]
Then \(|\lambda|\le1\).  If there is also \(0\ne\ell^\#\in\Phi'\) with
\[
 U'\ell^\#={1\over\overline\lambda}\ell^\#,               \tag{194}
\]
then \(|\lambda|=1\).

Indeed, choose \(x\) with \(\ell(x)\ne0\).  Continuity of \(\ell\) and `(192)` give a constant
bound, independent of \(n\), for
\[
 |\lambda|^n|\ell(x)|
 =|\ell(U^n x)|.
\]
Thus \(|\lambda|\le1\).  Applying the same argument to `(194)` gives
\(|\lambda|^{-1}\le1\).  This proves the theorem.

The same conclusion holds for finite generalized transpose eigenjets.  On the top nonzero
associated-graded coordinate, \(U'\) acts by \(\lambda\); equivalently, iterates of a Jordan jet
are \(\lambda^n\) times a polynomial in \(n\).  Polynomial factors cannot compensate exponential
growth in one reflected direction.

This is parent locally convex operator theory, not a novelty claim.  Its arithmetic use is new
relative to the corpus: it replaces all of the following by one forward semigroup estimate:

```text
bilateral unitary dilation;
the generally false relation V_p F_p = p;
continuous real-time extension;
off-axis resolvent preservation;
Hilbert-bounded point evaluation;
finite-dimensional realization of every Cartier fibre.
```

### The modular curvature character

At a nontrivial Xi zero \(\rho\), centered prime pullback has transpose character
\[
 \lambda_{p,\rho}=p^{\rho-1/2}.                            \tag{195}
\]
Functional-equation/Schwarz reflection sends
\[
 \rho\longmapsto\rho^\#=1-\overline\rho
\]
and hence
\[
 \lambda_{p,\rho^\#}
 =p^{1/2-\overline\rho}
 ={1\over\overline{\lambda_{p,\rho}}}.                    \tag{196}
\]
The real logarithm
\[
 \kappa_\rho(p)
 :=\log|\lambda_{p,\rho}|
 =(\operatorname{Re}\rho-\tfrac12)\log p
 =-\tfrac12\delta(\rho)\log p                             \tag{197}
\]
is the modular curvature character of the conormal orbit.  It is additive under rational
dilation, changes sign under reflection, and vanishes exactly on the critical line.

This gives the sought universal interpretation.  The scalar defects already proved in the
corpus are functorial readings of `(197)`:

```text
Deninger Hodge commutator        = infinitesimal modular curvature;
prime FE--Schwarz seam           = exponential transgression of curvature;
Poisson/Kadison defect           = one-sided norm loss;
Wold boundary leakage            = failure of uniform forward power control;
Kakutani singularity             = infinite-product amplification of nonzero curvature;
projective cosh coefficient      = reflection-even spherical moment;
bilateral temperedness failure   = exponential growth in one valuation direction;
Cartier dagger failure           = absence of a common reflected contractive realization.
```

An off-line zero is therefore not merely a badly placed scalar.  It is a nontrivial positive
modular character.  The critical line is the unimodular locus.

### Frozen source conjecture

`[CONJECTURE] [HT_SOURCE_EFFECTIVE_REFLECTED_CONTRACTIVE_COMPLETION]`

The ordinary-prime rational-Witt/Milnor--Rost--Schmid, Gamma, Poisson/co-Poisson, reflection, and
enhanced-HT source package for completed zeta admits a source-defined complete Hausdorff nuclear
graph space \(\Phi_{\rm src}\) and a continuous dense comparison
\[
 j:\Phi_{\rm src}\longrightarrow M_\zeta                 \tag{198}
\]
to Meyer's nuclear middle quotient with these properties:

1. **Pre-divisor construction.**  \(\Phi_{\rm src}\), its topology, and \(j\) are constructed
   from the integral finite-correspondence source before a zero or divisor fibre is selected.
2. **One-prime centered transfer.**  For at least one rational prime \(p\), normalized pullback
   \(U_p=p^{-1/2}V_p\) acts continuously on \(\Phi_{\rm src}\), and \(j\) intertwines it with
   Meyer's centered \(p\)-dilation.
3. **Forward Hodge power control.**  The family
   \(\{U_p^n:n\ge0\}\) is equicontinuous on \(\Phi_{\rm src}\).  More specifically, the topology
   is generated by source Green/Hodge graph seminorms on which \(U_p\) is contractive.  This is
   to be derived from projection-formula adjunction, `(191)`, moving-Hodge naturality, the
   chain-map law, and strict cofinal passage.
4. **Reflection-saturated conservativity.**  Density in `(198)` is in Meyer's nuclear quotient
   topology.  Consequently every nonzero Meyer conormal functional, including both members of
   every functional-equation/Schwarz pair, restricts nontrivially to the same
   \(\Phi_{\rm src}\).
5. **Cartier and jet strictness.**  The comparison commutes with reduced Cartier base change and
   retains every top nonzero multiplicity jet.  Nilpotent length is not replaced by reduced
   support.
6. **Source presentation independence.**  Prime enlargement, Gamma/BV transgression,
   Poisson reflection, and the literal integral source lattice induce the same graph topology
   and comparison.

This is a truth-hunch in the strict sense: current evidence makes the statement plausible, but no
proof of `(198)` or Clause 4 is known.  A construction recipe is not being smuggled into the
conjecture.

### Exact RH deduction

Let \(\rho\) be a nontrivial Xi zero.  Meyer supplies a nonzero continuous transpose
eigenfunctional \(\ell_\rho\in M_\zeta'\).  Dense range in `(198)` makes
\(\ell_\rho\circ j\) nonzero.  Clauses 2--3 and `(195)` give
\[
 |p^{\rho-1/2}|\le1.                                      \tag{199}
\]
Apply the same argument to the nonzero reflected zero
\(\rho^\#=1-\overline\rho\).  Equations `(196)` and `(199)` give
\[
 |p^{1/2-\overline\rho}|\le1.
\]
Thus \(|p^{\rho-1/2}|=1\), so
\[
 \operatorname{Re}\rho=\frac12.                           \tag{200}
\]
Every nontrivial zero is critical; hence the conjecture implies RH.  Associated-graded top jets
give the same conclusion without asserting simplicity.

Only one prime action is required after the global source comparison exists.  All-prime
Kakutani divergence, a real-time flow, and a bilateral inverse are diagnostic shadows, not
logical necessities for the final purity step.

### Why this is the third completion

The earlier completion trilemma now has an exact solution specification:

```text
finite clocks:
  both reflected fibres survive,
  but power bounds deteriorate with aperture;

ambient adelic L2:
  prime action is isometric,
  but both point fibres disappear;

enhanced exponential completion:
  both fibres survive,
  but an off-line reflected pair occupies opposite moving-annulus/Stokes sectors;

required source graph completion:
  one forward prime action is power-equicontinuous,
  and both reflected conormals remain nonzero in one Hausdorff strong dual.
```

The law is therefore **reflection-saturated one-sided effectivity**.  A one-sided Hardy
completion can retain a character strictly inside the disk.  Its reflected reciprocal lies
outside.  Arithmetic completion must retain both in one source topology; only the common boundary
survives.

Hypertranscendence explains why the Euler-time direction must remain enhanced and infinite-order.
It does not force `(200)`.  The new category is anisotropic:

```text
Euler/Gamma continuation direction: enhanced exponential/HT;
prime correspondence direction:     Hodge-graph power-equicontinuous;
Cartier divisor direction:           conservative strong dual.
```

Off-line positive Euler and Helson systems can inhabit the first direction while splitting the
two reflected conormals between inequivalent chiral topologies.  They therefore do not falsify
the law unless they also admit the literal integral source comparison `(198)` and all six
clauses.

### Exact reduction of existing open cores

This conjecture is weaker than the previous source targets:

1. `DAC_ARITHMETIC_HODGE_SCHWARTZ_RESOLVENT_CORE` asks for a closed real-time generator and every
   off-axis resolvent on a dense core.  Clauses 2--4 use one discrete prime transfer and no
   resolvent.
2. `PRIME-SCHWARTZ XI CONORMAL TEMPEREDNESS` asks directly for bilateral Schwartz continuity and
   is exactly RH in the natural Xi quotient.  Here forward equicontinuity is produced by source
   Hodge graph norms; reflection supplies the second radial inequality.
3. `XI_SOURCE_FROBENIUS_CARTIER_REALIZATION` asks that each finite Cartier package remain
   dualizable and land in finite-dimensional Hilbert space.  Here point conormals may remain
   genuine distributions in a strong dual.
4. `XI CONORMAL CRITICAL-SECTOR NORMALITY` asks for an all-prime GNS normality theorem.  Here one
   prime and nuclear-density conservativity suffice.
5. The topological Euler-index conjecture and zero-square Hodge conjecture from Section 27 are
   not used.

### First source theorem to attack

The first non-theatrical construction target is

`[OPEN CORE] [ONE_PRIME_SOURCE_HODGE_GRAPH_POWER_EQUICONTINUITY]`.

For one fixed prime \(p\), construct the strict cofinal source graph core before Xi comparison
and prove, uniformly in every finite-correspondence aperture,
\[
 q_{\alpha,m,r}(U_p^n x)
 \le q_{\alpha,m,r}(x)
 \qquad(n\ge0),                                           \tag{201}
\]
where \(q_{\alpha,m,r}\) are the actual Tate--Poisson/Green, incidence, real-boundary, and
Hodge-Laplacian graph seminorms.  Finite source ingredients already prove:

- \(F_pV_p=p\,\mathrm{id}\);
- projection-formula adjunction;
- moving-Hodge half-density isometry;
- a unitary chain map commutes with \(Q^\dagger\) and the BRST--Hodge Laplacian.

What remains in `(201)` is strict passage through the global incidence relation, unbounded
regularity operators, and cofinal source topology.  After `(201)`, the sole RH-bearing theorem is
the dense conservative comparison `(198)`.  This cleanly separates source metric construction
from divisor survival.

### Hostile audit

1. Pointwise continuity of each \(U_p^n\) is insufficient.  Uniform equicontinuity in \(n\) is
   load-bearing.
2. A forward contraction may carry any eigencharacter in the closed disk.  Reflection-saturated
   nonzero conservativity, not contractivity alone, forces the boundary.
3. Functional equation alone places the reciprocal point in the divisor.  It does not put both
   conormals in the same continuous dual.
4. Defining \(\Phi_{\rm src}\) by deleting growing Xi eigencharacters is circular.  Its seminorms
   must be built from source Green/Hodge and correspondence data.
5. Finite-stage isometries do not imply `(201)` if graph constants grow with aperture or
   prime-infinity leakage survives.
6. If \(U_p\) changes a scale index, the source orbit object and its transition topology must be
   constructed explicitly.  One may not silently identify distinct Hodge fibres.
7. Hilbert unitarity after scalar completion is insufficient because it can erase every Meyer
   conormal.
8. Density in a Hilbert norm is insufficient.  It must hold in the nuclear topology on which
   Meyer zero functionals are continuous.
9. Real-coefficient Weil cohomology cannot be assumed; Deninger's no-go forces the odd/complex
   polarized and enhanced source used here.
10. An explicit off-line Euler system satisfying all six source clauses would refute the
    conjecture.

### Literature boundary

Power-equicontinuous representations, smooth-vector/graph cores, Schwartz strong duals,
enhanced ind-sheaves, and finite-correspondence push--pull are parent mathematics.  Relevant
parents include Kashiwara--Schapira on ind-sheaves and tempered growth
(`arXiv:math/9906200`), Hepler--Hohl on moderate/rapid enhanced nearby cycles
(`arXiv:2206.06095`), Deninger's real-coefficient Weil-cohomology obstruction
(`arXiv:2204.02714`), and Deninger's rational-Witt finite-correspondence realization
(`arXiv:2508.05329`).

Targeted corpus and arXiv searches found the continuous-resolvent, bilateral-tempered,
finite-dualizable, and all-prime-normality routes separately.  They did not locate the precise
one-prime theorem `(192)`--`(200)` sourced from the asymmetric relation \(F_pV_p=p\) and
reflection-saturated nuclear conservativity.  Novelty is provisionally restricted to this
arithmetic reduction and universal interpretation, not to the elementary operator lemma.

## 29. Source-effective bidual scale descent is the universal purity law

### Correction: the third completion need not be one carrier

Section 28 still imposed too much global geometry.  The HT positive-realization theorem proves
that a faithful infinite jet grading with nonunit dilation cannot be boundedly flattened onto one
fixed carrier.  The finite Deninger source theorem likewise gives an isometric chain map, not in
general a unitary endomorphism of one fixed Hodge space.  The correct recipient is therefore a
directed contractive scale together with its source-normal Rees/local-cohomology boundary and a
jointly sewn dual.

This is not a cosmetic weakening.  It removes the conflict between:

```text
HT vertical faithfulness:
  the noncompact jet grading must remain scale-valued;

arithmetic horizontal purity:
  one prime correspondence must be contractive along the scale;

divisor conservativity:
  the two reflected Xi conormals must be boundary sections of one sewn dual system.
```

The vertical and horizontal directions are different.  Hypertranscendental scale-rigidity is
allowed in the first; purity is forced by bidual effectivity in the second.

The boundary qualification is load-bearing.  The proved Poisson--Mertens fracture says that every
positive Euler-time representative can vanish in a Hausdorff quotient while the complete
time-zero logarithmic jet is nonzero.  An ordinary projective limit of positive-time Hilbert
spaces therefore still loses the arithmetic conormal.  It must be retained as a Rees normal,
Bockstein, local-cohomology, hyperfunction, or equivalent derived boundary section.

### Directed conormal descent theorem

Let \(H_n\) be complex Hilbert spaces, let
\[
 T_n:H_n\longrightarrow H_{n+1}
\]
be contractions, and put \(T_{0,n}=T_{n-1}\cdots T_0\).  A **uniformly normal covariant
conormal section** of multiplier \(\lambda\) is a family
\(\ell_n\in H_n^\ast\) such that
\[
 \sup_n\|\ell_n\|<\infty,\qquad
 \ell_{n+1}T_n=\lambda\ell_n,\qquad
 \ell_0\ne0.                                               \tag{202}
\]

`[PAPER-PROVED] [DIRECTED_CONORMAL_DESCENT_CONTRACTIVITY]`

Every section `(202)` satisfies
\[
 |\lambda|\le1.                                            \tag{203}
\]
If a second uniformly normal section has multiplier
\[
 \lambda^\#={1\over\overline\lambda},
\]
then
\[
 |\lambda|=1.                                              \tag{204}
\]

Choose \(x\in H_0\) with \(\ell_0(x)\ne0\).  Iteration gives
\[
 |\lambda|^n|\ell_0(x)|
 =|\ell_n(T_{0,n}x)|
 \le \|\ell_n\|\,\|T_{0,n}x\|
 \le \Bigl(\sup_m\|\ell_m\|\Bigr)\|x\|.
\]
Taking \(n\)-th roots proves `(203)`.  Apply the same argument to the reflected section to obtain
\(|\lambda|^{-1}\le1\), proving `(204)`.

Uniform boundedness may be weakened to zero exponential type:
\[
 \limsup_n\|\ell_n\|^{1/n}\le1,\qquad
 \limsup_n\|T_{0,n}\|^{1/n}\le1.
\]
The same proof still gives `(203)`.  This version retains finite conormal jets, because their
nilpotent factors grow only polynomially.

The theorem is elementary directed functional analysis.  Bellomonte--Trapani's contractive
Hilbert systems and their joint projective/inductive limits are parent theory
(`arXiv:1312.1371`).  No novelty is claimed for `(202)`--`(204)`.

### Isometric chain maps already give the horizontal contraction

The finite source ingredients in Section 28 were misstated.  Under the already isolated
Gamma-polarized projection-formula, Hodge-naturality, and degree hypotheses, normalized pullback
is an isometric chain map between moving source complexes.  It need not be onto, so the unitary
\(Q^\dagger\)-commutation theorem cannot be applied to it.  Constructing the arithmetic
Gamma-polarized realization satisfying those hypotheses remains a separate specialization gate.

There is a weaker theorem which is both sufficient and automatic.  Let
\[
 U:(C^\bullet,d)\longrightarrow(D^\bullet,d)
\]
be an isometric chain map of Hilbert complexes.  On reduced cohomology
\[
 \overline H^k(C)
 =
 \ker d_k/\overline{\operatorname{im}d_{k-1}},
\]
the induced map is contractive:
\[
 \|\overline U[x]\|_{\overline H^k(D)}
 \le
 \|[x]\|_{\overline H^k(C)}.                              \tag{205}
\]
Indeed, \(U\) maps boundaries to boundaries, and
\[
\begin{aligned}
 \|\overline U[x]\|
 &=\inf_{b\in\overline{\operatorname{im}d_D}}\|Ux+b\|\\
 &\le
   \inf_{a\in\overline{\operatorname{im}d_C}}\|U(x+a)\|\\
 &=\inf_{a\in\overline{\operatorname{im}d_C}}\|x+a\|.
\end{aligned}
\]
Surjectivity is not needed.  If the actual source regularity operators strictly intertwine the
chain maps, the same proof applies to every graph-norm complex and gives the corresponding family
of quotient-seminorm contractions.

Thus the abstract finite metric producer is already present in the correct category.  After its
arithmetic specialization, the remaining issue is not a missing reverse adjoint formula.  It is
strict assembly of the reduced quotient maps and uniform normality of the source-produced Xi
conormal section.

### Universal ordered-cone form

Let \(\Gamma\) be an additive scale-character group and let \(C_{\rm eff}\subset\Gamma\) be the
closed cone of forward-effective growth characters.  Assume it is pointed:
\[
 C_{\rm eff}\cap(-C_{\rm eff})=\{0\}.                    \tag{206}
\]
Reflection duality acts on modular curvature by
\[
 \kappa\longmapsto-\kappa.                               \tag{207}
\]
If one source-effective sewn class realizes both a conormal and its reflected dual, forward
descent puts both
\[
 \kappa\in C_{\rm eff},\qquad-\kappa\in C_{\rm eff}.
\]
Pointedness `(206)` forces
\[
 \boxed{\kappa=0.}                                      \tag{208}
\]

Equation `(208)` is the universal law:

```text
source effectivity
  + reflected source effectivity
  + pointed horizontal scale descent
  = modular flatness.
```

The critical locus is not selected by a target-side sign.  It is the lineality locus of the
source-effective cone.  A one-sided analytic completion sees the whole interior of one cone.
Reflection sees the opposite cone.  Only a source object in which the two are genuinely sewn,
rather than merely paired after specialization, restricts them to the common boundary.

### What the obstruction corpus was saying

The repeated failures are now exact failures of one clause of `(208)`:

```text
finite clocks:
  conormals survive, but transition contractions are not uniform;

ambient adelic L2:
  transition is isometric, but every point conormal is non-effective;

high-shell Hardy completion:
  the right conormal is effective and the reflected conormal lies in the opposite Hardy scale;

enhanced/Stokes completion:
  both conormals survive, but in different chiral fibres with no strict common descent;

HT capacity universality:
  arbitrary kinematic scale cocycles exist before source selection;

HT scale rigidity:
  a faithful vertical grading cannot be flattened to manufacture horizontal purity;

Wold/Gamma and BV anomalies:
  record the transition defect erased by coarse completion;

Kummer prime-infinity leakage:
  finite effective sections fail strict cofinal descent;

fixed-carrier completion flatness:
  a globally chosen bounded trivialization is only a coboundary, so genuine content lives in
  descent and sewing;

off-line Euler and Helson systems:
  realize the two chiral cones without the ordinary-prime integral source-effective sewing.
```

This also explains why the positive shell frame matters but does not prove RH.  Its canonical
residue Hilbert scale constructs the two opposite effective cones and measures their displacement
exactly.  It does not prove that the two normal jets are realizations of one source-effective
section.

### The algebraic Rees boundary section is already constructed

The prime-sieve Wold--Gamma/BV theorem supplies more than a hint.  For a finite prime set \(P\),
put
\[
 a_P=\prod_{p\in P}(1-p^{-1}),\qquad
 E_P=\prod_{p\in P}(I-S_pD_p).
\]
Its source identity is
\[
 J(E_Pp_a)=a_PJ(p_a).                                  \tag{209}
\]
Define the source-normal Rees section
\[
 \eta_P:=a_P^{-1}J(E_Pp_a).                             \tag{210}
\]

`[PAPER-PROVED FROM THE EXISTING SOURCE IDENTITIES]`
`[PRIME_SIEVE_REES_CONORMAL_DESCENT]`

For every finite \(P\),
\[
 \eta_P=J(p_a).                                        \tag{211}
\]
Consequently \((\eta_P)_P\) is a presentation-independent compatible section over the complete
finite-prime poset.  It does not need to converge as a net of normalized states.  The coarse
section \(J(E_Pp_a)\) vanishes with \(a_P\), while `(210)`--`(211)` retain its nonzero normal
direction.

The centered dilation
\[
 \widetilde D_q=q^{1/2}D_q
\]
has exact conormal character
\[
 J(\widetilde D_qp_a)(s)=q^{s-1/2}J(p_a)(s).            \tag{212}
\]
At an uncensored Xi zero \(\rho\), the top associated-graded normal therefore has multiplier
\(q^{\rho-1/2}\); higher multiplicity only adds polynomial Jordan factors.  A jointly
noncensoring BV family gives at least one nonzero coordinate at every nontrivial zero.

Thus three pieces of strict scale descent are no longer conjectural:

```text
source-first normal boundary carrier;
prime-exhaustion compatibility without strong convergence;
exact centered prime character on every uncensored top conormal jet.
```

What `(209)`--`(212)` do not provide is a positive quotient norm on the Rees normal line or a
strict comparison with the Hodge/Green boundary scale.  Assigning
\(\|\eta_P\|=1\) by hand would make `(212)` pure by definition and is rejected by the
projective-conormal calibration no-go.  The missing theorem is precisely an independently
source-generated Hermitian landing.

### Refined frozen conjecture

`[CONJECTURE] [XI_SOURCE_EFFECTIVE_BIDUAL_SCALE_DESCENT]`

The completed ordinary-prime Euler--Gamma/co-Poisson source has a presentation-independent
derived directed system of reduced Hodge/Green graph cohomologies and source-normal boundary
cohomologies
\[
 \bigl(H_\alpha,T_{\beta\alpha}\bigr)
\]
and a source-produced comparison from the principal Xi conormal module
\((\Xi)/(\Xi)^2\) into its joint dual with the following properties:

1. **Source-first derived scale.**  The system, graph norms, transition maps, integral lattice,
   Rees/local-cohomology boundary, and comparison are constructed before divisor specialization.
2. **Horizontal contractivity.**  For one rational prime \(p\), the centered finite-correspondence
   maps induce a cofinal directed subsystem of contractions by `(205)`.
3. **Uniform boundary-conormal descent.**  Every nonzero top Xi multiplicity jet gives a nonzero
   covariant boundary-conormal section of zero exponential type whose multiplier is
   \[
   \lambda_{p,\rho}=p^{\rho-1/2}.
   \]
4. **Order-zero reflected sewing.**  Functional-equation/Schwarz reflection is a strict
   source comparison on the same derived joint dual system and sends that section to a nonzero
   section with multiplier \(1/\overline{\lambda_{p,\rho}}\), without changing its exponential
   order or local-cohomology degree.
5. **Source effectivity.**  Nonvanishing and uniform normality follow from the distinguished
   integral source section and its typed comparison maps, not from a zero-selected quotient or
   metric.
6. **Presentation independence.**  Prime enlargement, Hodge-scale refinement, Gamma/BV
   transgression, Poisson presentation, and shell resolution induce the same joint conormal
   section.

This replaces the fixed-carrier conjecture of Section 28.  It is compatible with
hypertranscendental scale-valued positive geometry and with the asymmetric relation
\(F_pV_p=p\,\mathrm{id}\).

### RH deduction

For a nontrivial zero \(\rho\), Clauses 2--3 and `(203)` give
\[
 |p^{\rho-1/2}|\le1.
\]
Clause 4 and the reflected application give
\[
 |p^{1/2-\overline\rho}|\le1.
\]
Hence equality holds and
\[
 \operatorname{Re}\rho=\frac12.
\]
Top associated-graded jets handle multiplicity.  Thus the refined conjecture implies RH.

In cone language,
\[
 \kappa_\rho(p)
 =(\operatorname{Re}\rho-\tfrac12)\log p
\]
and its negative are both forward-effective; `(208)` forces
\(\kappa_\rho(p)=0\).

### Exact remaining open core

The first non-immediate theorem is now narrower than
`ONE_PRIME_SOURCE_HODGE_GRAPH_POWER_EQUICONTINUITY`:

`[OPEN CORE] [XI_REES_CONORMAL_HODGE_LANDING]`

Let \(\mathcal N_{\Xi,\mathrm{BV}}^{\rm Rees}\) be the Rees-normal conormal module generated by a
fixed jointly noncensoring BV source family through `(209)`--`(212)`.  Construct, before divisor
specialization, one natural transformation
\[
 \mathcal N_{\Xi,\mathrm{BV}}^{\rm Rees}
 \longrightarrow
 \mathbb H_{\partial,\mathrm{src}}^\ast
\]
where \(\mathbb H_{\partial,\mathrm{src}}^\ast\) is the source-normal
Rees/local-cohomology boundary of the joint projective/inductive Hodge scale, and prove:

1. every top divisor jet is nonzero in the joint Hausdorff dual;
2. its norm growth along one prime correspondence is of zero exponential type;
3. reflection is an order-zero sewing of the same section, not a map to an inequivalent Stokes
   object; and
4. the construction is induced by the distinguished ordinary-prime integral source lift.

Finite Hodge isometry supplies the contraction side by `(205)`.  Equations `(209)`--`(212)`,
Meyer, and the high-shell entire graph supply the algebraic boundary section, noncensorship, and
exact characters.  None supplies the strict source-effective Hermitian landing.

Stating only fibrewise existence of such a section is RH-equivalent and therefore theatre.  The
candidate-new theorem is a source-defined natural transformation on the whole principal conormal
module, together with strict descent and presentation independence.

This target also supersedes the earlier mixed-Cauchy regulator proposal.  The normalized
prime-sieve states move by exactly \(1/p\) and are not strongly Cauchy, while the
Poisson--Mertens class is zero at every positive time.  A valid source section is therefore a
compatible boundary section, not a strong limit of normalized representatives.  The directed
purity theorem needs zero exponential type along the horizontal correspondence; it does not need
total-variation or \(L^1+L^2\) convergence across prime exhaustions.

### Hostile falsifiers

1. The moving source complexes fail to form a contractive directed system after reduced
   incidence/Hodge quotient.
2. Their joint topological limit is non-Hausdorff or has no dual containing the source conormal.
3. The conormal exists algebraically but has positive exponential norm growth at a hypothetical
   off-line fibre.
4. Reflection necessarily changes the source scale order, reproducing the high-shell
   chiral fracture instead of an order-zero sewing.
5. The integral source section does not determine a Hermitian/exponential calibration, in accord
   with the projective-conormal scale no-go.
6. A source-equivalent prime exhaustion changes the joint section or its exponential order.
7. An explicit off-line ordinary-prime Euler system carries the same distinguished integral
   source lift and all six clauses.

If any falsifier occurs, the positive survivor must identify the exact descent obstruction or
additional source comparison channel.  Reverting to a fixed carrier, an abstract antiunitary,
or a divisor-selected norm is not a repair.

### Literature and novelty boundary

Directed contractive Hilbert systems, projective/inductive joint limits, rigged Hilbert spaces,
reduced Hilbert cohomology, and the cone identity `(206)`--`(208)` are parent mathematics.
Bellomonte--Trapani explicitly construct joint dual limits from contractive Hilbert families and
allow an order-reversing dual index.  Enhanced nearby cycles and moderate/rapid duality provide
the parent language for the chiral boundary fracture.

Targeted primary-source searches found these parents, Meyer's all-zero nuclear realization,
Connes--Consani's unitary scaling realization, and Deninger's finite-correspondence programme.
They did not locate the arithmetic conjunction in the refined conjecture: a source-first
ordinary-prime integral conormal natural transformation into a contractive Hodge scale whose
functional-equation reflection is order-zero and jointly effective.  Novelty is provisional and
begins only with that arithmetic source-descent theorem, not with `(202)`--`(208)`.

### Anti-theatre verdict

The cone law `(208)` is not an RH proof and is not new by itself.  The Rees identity
`(209)`--`(212)` is an unconditional source construction, but it is projective and has no
source-forced Hermitian norm.  Therefore it also does not exclude an off-line zero.

The genuine frontier movement is the exact reduction:

```text
retired requirements:
  one fixed carrier;
  bilateral inverse;
  real-time flow and resolvents;
  strong convergence of normalized prime-sieve states;
  ordinary positive-time projective limit;
  all-prime normality;

already constructed:
  source-normal Rees conormal carrier;
  presentation-compatible boundary section;
  one-prime centered character;
  abstract reduced-Hodge contraction;

single remaining theorem:
  source-induced Hermitian landing of that existing Rees section,
  with reflection order zero in the same derived boundary scale.
```

This last theorem is still RH-bearing.  Calling the Rees generator unit length, defining its norm
from the Xi divisor, or asserting that source duality preserves its order would restate the
conclusion.  Progress after this section must construct the landing map or prove a new
source identity that forces it.

## 30. Positive shell conormals expose spectral location as a source-boundary order

The publication-ready positive hypertranscendental divisor frame supplies a second, more concrete
model of the source-normal boundary.  It does not require an arbitrary prime aperture.  For
\(m\geq1\), let
\[
 a_m=\mathbf 1_{\{n:M(n)=m\}},\qquad
 S_m(s)=\sum_{n\geq1}a_m(n)n^{-s},
\]
where \(M(n)\) is the largest prime exponent in \(n\).  The frame theorem gives
\[
 S_m^\#(s)=\zeta(s)H_m(s),\qquad
 H_m(s)={1\over\zeta((m+1)s)}-{1\over\zeta(ms)}.          \tag{213}
\]
For \(m\geq12\), \(H_m\) is holomorphic and zero-free on
\(\Re s>1/2\).  The coefficient supports of the \(S_m\) are positive and pairwise disjoint, and
the smallest integer in the \(m\)-th shell is canonically
\[
 \min\{n:a_m(n)=1\}=2^m.                                  \tag{214}
\]
Thus \(2^{m/2}\), the critical half-density dual scale of the least source atom, is not a
zero-selected normalization.

### Least-atom asymptotic theorem

`[PAPER-PROVED FROM THE POSITIVE SHELL FRAME]`
`[POSITIVE_SHELL_CONORMAL_BOUNDARY_ORDER]`

For every fixed \(s\) with \(\sigma=\Re s>0\),
\[
 \boxed{\quad
  2^{ms}H_m(s)\longrightarrow 1-2^{-s}.
 \quad}                                                     \tag{215}
\]

Indeed, once \(m\sigma>1\), the absolutely convergent Möbius series gives
\[
\begin{aligned}
 H_m(s)
 &=\sum_{n\geq1}\mu(n)n^{-ms}(n^{-s}-1)\\
 &=(1-2^{-s})2^{-ms}+R_m(s),                               \tag{216}
\end{aligned}
\]
where
\[
 |2^{ms}R_m(s)|
 \leq
 2\sum_{n\geq3}(2/n)^{m\sigma}.
\]
For \(a=m\sigma>1\),
\[
 \sum_{n\geq3}(2/n)^a
 \leq
 (2/3)^a\left(1+{3\over a-1}\right)\longrightarrow0,
\]
which proves `(215)`.

Put
\[
 v_m(s):=2^{m/2}H_m(s),\qquad A(s):=1-2^{-s}.             \tag{217}
\]
Then
\[
 v_m(s)
 =
 A(s)\,2^{-m(s-1/2)}+o\!\left(2^{-m(\sigma-1/2)}\right), \tag{218}
\]
and hence the source-boundary order is
\[
 \boxed{\quad
 \kappa_{\rm sh}(s)
 :=
 \lim_{m\to\infty}
 {1\over m\log2}\log|v_m(s)|
 =
 {1\over2}-\Re s.
 \quad}                                                     \tag{219}
\]
The factor \(A(s)\) is nonzero in the open critical strip.

At a zero \(\rho\) of multiplicity \(d\), multiplication by \(H_m(\rho)\) is exactly the map on
the top local conormal grade of
\[
 S_m^\#=\zeta H_m.
\]
Thus `(219)` is not merely a value asymptotic: it is the exponential escape rate of one
source-constructed coordinate of the actual Xi/zeta top conormal.  Multiplicity changes the
polynomial jet block but not this exponential grade.

### The all-grade shell corona

For \(\delta\in\mathbb R\), define
\[
\begin{aligned}
 B_\delta
 &=
 \left\{x=(x_m):
   \sup_m 2^{-m\delta}|x_m|<\infty\right\},\\
 B_{\delta,0}
 &=
 \left\{x\in B_\delta:
   2^{-m\delta}|x_m|\longrightarrow0\right\},\\
 \mathcal C_\delta&=B_\delta/B_{\delta,0}.                \tag{220}
\end{aligned}
\]
These are weighted versions of the canonical sequence corona
\(\ell^\infty/c_0\).  Equation `(218)` gives a nonzero class
\[
 [v(s)]_{\kappa_{\rm sh}(s)}
 \in\mathcal C_{\kappa_{\rm sh}(s)}                       \tag{221}
\]
for every \(0<\Re s<1\).  Therefore the graded family
\[
 \mathcal C_{\rm sh}:=\{\mathcal C_\delta\}_{\delta\in\mathbb R} \tag{222}
\]
is a literal third completion of this conormal frame:

```text
every divisor conormal survives:
  in exactly one exponential grade delta=1/2-Re(s);

critical divisor conormals:
  are precisely the nonzero classes in the unweighted corona C_0;

strict-right divisor conormals:
  decay to zero in C_0 but survive in a negative grade;

strict-left divisor conormals:
  are unbounded in C_0 but survive in the reflected positive grade.
```

The unweighted trichotomy is exact:
\[
\begin{array}{c|c}
\Re s>1/2 & v(s)\in c_0,\\
\Re s=1/2 & v(s)\in\ell^\infty\setminus c_0,\\
\Re s<1/2 & v(s)\notin\ell^\infty.
\end{array}                                                \tag{223}
\]
This is the first source-first completion in this route which both retains every conormal and
records, rather than erases, why an off-line conormal fails to live in the critical carrier.

Let \(R(x)_m=x_{m+1}\).  On \(\mathcal C_\delta\), the grade-normalized shift
\[
 T_\delta=2^{-\delta}R                                  \tag{224}
\]
is contractive.  Equation `(218)` makes `[v(s)]` an eigenclass with eigenvalue
\[
 2^{-\delta}2^{-(s-1/2)}
\]
of modulus one when \(\delta=\kappa_{\rm sh}(s)\).  This is also a warning: every spectral point
can be made unitary inside its own fitted grade.  Purity is the source theorem selecting grade
zero, not gradewise unitarizability.

### Reflection retains duality but negates boundary order

For \(0<\Re s<1\), `(218)` also gives
\[
 v_m(s)\,
 \overline{v_m(1-\overline s)}
 \longrightarrow
 A(s)A(1-s)\ne0.                                         \tag{225}
\]
Consequently the functional equation supplies a nondegenerate pairing between the grades
\[
 \mathcal C_{\kappa_{\rm sh}(s)}
 \quad\text{and}\quad
 \mathcal C_{-\kappa_{\rm sh}(s)}.                        \tag{226}
\]
It does not force either grade to be zero.  This one formula explains the recurring fracture:
reflection-perfect indefinite duality survives every hypothetical off-line quartet, while a
positive Hermitian realization on one source-normal grade exists only at the balance wall.

### Universal interpretation

The new invariant is not a zero value, sign, or finite jet.  It is the **source-normal conormal
boundary order**.  In a positive disjoint HT frame whose \(m\)-th channel has least atom \(N_m\)
and transverse multiplier
\[
 H_m(s)\sim A(s)N_m^{-s},
\]
half-density normalization gives
\[
 N_m^{1/2}H_m(s)
\sim A(s)N_m^{-(s-1/2)}.                                 \tag{227}
\]
The real part of a divisor point is therefore the Lyapunov/Stokes escape rate of its conormal
through the infinite positive frame.  Reflection reverses that rate.  Criticality means zero
escape, not vanishing curvature or positive orientation.

This interpretation subsumes the corpus observations more sharply:

```text
finite clocks and compact-open jets:
  cannot see an asymptotic boundary order;

ambient L2:
  forgets all nonzero corona classes;

high-shell Hardy inside/outside:
  is the analytic realization of the signs of kappa_sh;

HT order escape:
  says no bounded differential order can capture kappa_sh;

prime-aperture Stokes action:
  is a continuous-aperture version of the discrete shell grade;

Wold/BV/Rees normalization:
  constructs the same conormal before shell specialization;

functional equation:
  pairs opposite grades but does not collapse them;

positive generalized-prime surgery:
  preserves divisor orientation while lacking this exact
  least-integer-shell source filtration.
```

### Sharper conjecture and open core

`[BOLD CONJECTURE] [XI_SOURCE_BALANCED_SHELL_CONTINUATION]`

The completed ordinary-prime Euler--Gamma source continuation is strict of degree zero on the
principal conormal for the least-atom half-density filtration `(214)`--`(220)`.  Equivalently,
the source-defined continuation from the positive shell fusion to the Gamma/reflection boundary
lands every nonzero Xi top conormal in \(\mathcal C_0\), and this landing is faithful and
reflection-positive before divisor specialization.

Combined with `(219)`, this statement forces
\[
 \kappa_{\rm sh}(\rho)=0
 \quad\Longrightarrow\quad
 \Re\rho=\frac12,
\]
so it implies RH.

The corresponding non-immediate theorem is now concrete:

`[OPEN CORE] [XI_POSITIVE_SHELL_CORONA_DEGREE_ZERO_LANDING]`

Construct one source-global continuation morphism from the coefficient-positive, pairwise
disjoint shell fusion into the shell-corona boundary such that:

1. its critical scale is forced by the least source atoms \(2^m\);
2. it agrees on the top principal conormal with the already constructed coordinates \(H_m\);
3. it is strict of degree zero under Gamma completion and reflection;
4. it is faithful on every top Xi jet; and
5. degree-zero strictness follows from an independently positive source pairing or complete
   Pick/Hodge transport, not from boundedness of \(v(\rho)\).

This is a discrete source-normal model of
`XI_REES_CONORMAL_HODGE_LANDING`.  It removes the arbitrary aperture coordinate and exhibits the
exact filtration on which the landing must be proved.

### Anti-theatre verdict

Equations `(215)`--`(226)` are unconditional and materially new to this route: they construct the
all-grade carrier and compute the grade of every divisor conormal from a positive HT source
frame.  They do not prove that the actual Xi conormal has grade zero.

Asking for `[v(\rho)]\ne0` in \(\mathcal C_0\) fibrewise is exactly RH by `(223)` and is forbidden
as a proof.  Positivity of the coefficients \(a_m\) does not survive analytic continuation as a
positive value statement, and the nonzero reflected product `(225)` proves that duality alone
still permits off-line grades.  The next progress must be a source-global degree-zero strictness
theorem.  If that theorem fails, the positive survivor is the canonical defect
\[
 \kappa_{\rm sh}(\rho)=\frac12-\Re\rho,
\]
now realized as an actual HT conormal boundary order rather than inserted from the zero coordinate.

## 31. The shell conormal is a uniformly invertible gauge of the pure exponential model

The asymptotic theorem can be made uniform on the full strict right half-plane.  Define
\[
 G_m(s)
 =
 {2^{ms}H_m(s)\over1-2^{-s}},
 \qquad \Re s>\frac12.                                    \tag{228}
\]

`[PAPER-PROVED] [POSITIVE_SHELL_UNIFORM_EXPONENTIAL_GAUGE]`

There are a source-only integer \(m_0\) and a constant \(0<q<1\) such that
\[
 \sup_{\substack{m\geq m_0\\ \Re s>1/2}}
 |G_m(s)-1|
 \leq q.                                                   \tag{229}
\]
Consequently
\[
 1-q\leq |G_m(s)|\leq1+q                                \tag{230}
\]
uniformly in \(m\geq m_0\) and \(\Re s>1/2\).

To prove this, use `(216)` and write \(\sigma=\Re s\), \(a=m\sigma\).  Since
\[
 |1-2^{-s}|\geq1-2^{-1/2},
\]
the same integral estimate gives
\[
 |G_m(s)-1|
 \leq
 {2\over1-2^{-1/2}}
 \left({2\over3}\right)^a
 \left(1+{3\over a-1}\right).                            \tag{231}
\]
For \(m\geq m_0\), one has \(a>m_0/2\), and the right side is bounded by a number
\(q<1\) after choosing \(m_0\) once.  This proves `(229)`--`(230)` without any zero
specialization.

For fixed \(s\), the diagonal map
\[
 (x_m)_m\longmapsto(G_m(s)x_m)_m                         \tag{232}
\]
therefore induces a bounded invertible automorphism of every weighted corona
\(\mathcal C_\delta\).  It carries the pure source character
\[
 \bigl((1-2^{-s})2^{-m(s-1/2)}\bigr)_m
\]
to the actual shell conormal \(v(s)\).

This removes a possible hidden obstruction.  The transverse zero-free multipliers \(H_m\) do not
create the off-line grade, change its sign, or distort the relevant corona topology.  Up to one
uniformly invertible source gauge, the actual conormal is the pure exponential character with
modular curvature
\[
 \kappa_{\rm sh}(s)=\frac12-\Re s.
\]
Thus the remaining degree-zero landing theorem cannot be repaired by better estimates on
\(H_m\), prime-two domination, or a different finite shell threshold.  It must prove that
ordinary-prime Euler--Gamma continuation makes the **common divisor conormal itself** tempered
at the source half-density scale.

This also sharpens the universal law:

> A source-minimal positive HT divisor frame separates its finite transverse geometry from its
> infinite spectral displacement.  Uniformly invertible transverse gauges carry no purity
> information; the real part of a divisor is the exponential boundary order of the common
> conormal, and purity is strict preservation of the source half-density order under
> continuation.

The theorem is unconditional.  The final strict-preservation clause remains the RH-bearing
conjecture.

## 32. The critical shell metric is the maximum-valuation law of the Wold source

The half-density normalization in Section 30 has an exact positive source interpretation.  For
each prime \(p\), let \(K_p\) be independent with the critical Wold valuation law
\[
 \mathbb P(K_p=k)=(1-p^{-1})p^{-k},
 \qquad k\in\mathbb N_0.                                  \tag{233}
\]
This is the product law already forced independently by the multiplication Wold tower, the
first-trace density, and the BV principal conormal.

Put
\[
 M=\sup_pK_p.
\]

`[PAPER-PROVED] [WOLD_MAXIMUM_VALUATION_SHELL_LAW]`

The random variable \(M\) is finite almost surely and
\[
 \boxed{\quad
 \mathbb P(M=m)
 =
 h_m
 :=
 {1\over\zeta(m+1)}-{1\over\zeta(m)}
 =
 H_m(1),
 \qquad m\geq1,
 \quad}                                                     \tag{234}
\]
where \(1/\zeta(1)\) is interpreted as zero.

Indeed, for \(m\geq1\),
\[
 \mathbb P(K_p<m)=1-p^{-m},
\]
so independence gives
\[
 \mathbb P(M<m)=\prod_p(1-p^{-m})={1\over\zeta(m)}.       \tag{235}
\]
For \(m=1\), Euler's divergence makes the product zero.  Since
\[
 {1\over\zeta(m)}\longrightarrow1,
\]
equation `(235)` also proves \(\mathbb P(M<\infty)=1\).  Taking consecutive differences gives
`(234)`.

Thus \((h_m)_{m\geq1}\) is a source-constructed probability distribution, not a divisor-fitted
metric.  Equation `(215)` at \(s=1\) gives
\[
 2^mh_m\longrightarrow\frac12.                           \tag{236}
\]
The critical least-atom half-density \(2^{-m/2}\) is therefore, up to its forced constant, exactly
the square-root density \(\sqrt{h_m}\) of the Wold maximum statistic.

### Conormal likelihood-rate theorem

For \(\Re s>0\), define the source-normal conormal amplitude
\[
 w_m(s):={H_m(s)\over\sqrt{h_m}}.                         \tag{237}
\]
Equations `(215)` and `(236)` imply
\[
 w_m(s)
 =
 \sqrt2(1-2^{-s})\,2^{-m(s-1/2)}(1+o(1)),                \tag{238}
\]
and hence
\[
 \boxed{\quad
 \lim_{m\to\infty}
 {1\over m\log2}
 \log {\,|H_m(s)|^2\over h_m}
 =
 1-2\Re s.
 \quad}                                                     \tag{239}
\]

For a nontrivial zero \(\rho\), the numerator in `(239)` is the squared intensity of the actual
top shell-conormal coordinate, while the denominator is the probability of the same shell under
the distinguished ordinary-prime source.  Therefore
\[
 2\kappa_{\rm sh}(\rho)
 =
 1-2\Re\rho
\]
is, up to the sign convention of Section 29, the exact asymptotic log-likelihood slope between
divisor-conormal intensity and source maximum-valuation mass.

The three cases are:

```text
Re(s)>1/2:
  conormal intensity is exponentially thinner than source shell mass;

Re(s)=1/2:
  conormal intensity and source shell mass are exponentially contiguous;

Re(s)<1/2:
  conormal intensity is exponentially thicker than source shell mass.
```

Reflection sends the likelihood slope to its negative.  The indefinite reflected product remains
nonzero by `(225)`, while zero likelihood slope is exactly the source/reflection balance wall.

This is the sought joint interpretation of several previously separate laws:

```text
Wold/BV renewal:
  produces the independent critical valuation source;

positive HT exponent shells:
  are the pushforward of that source by the maximum statistic;

Fisher/half-density normalization:
  is square root of the maximum-valuation probability;

Kakutani radial separation:
  is the full product-sector version of nonzero likelihood slope;

Stokes boundary order:
  is the shell-tail version of the same slope;

modular curvature:
  is one half of that source/conormal likelihood rate;

critical line:
  is exponential contiguity of source mass and divisor-conormal intensity.
```

The probability theorem and rate identity are unconditional.  They provide an independently
positive **reference** calibration on the shell coordinate: the candidate shell metric is
\(h_m=H_m(1)\), derived before analytic continuation and before reading a zero.  They do not yet
identify the projective Rees section with an amplitude in that metric.

They do not yet prove that a continued Xi conormal must be exponentially contiguous with this
source law.  That is now the exact strictness statement:

`[BOLD CONJECTURE] [XI_WOLD_SHELL_BORN_RATE_CONSERVATION]`

The principal Xi conormal is the boundary amplitude of the distinguished Wold/BV source state, and
the source-to-Gamma/reflection continuation preserves zero asymptotic likelihood rate under the
maximum-valuation pushforward.

By `(239)`, this conjecture implies RH.  Unlike a fitted norm, every term in the source reference
law \(h_m\) is already fixed by `(233)`--`(235)`.  The remaining theorem must construct the
amplitude comparison and prove rate conservation; merely imposing
\[
 \log(|H_m(\rho)|^2/h_m)=o(m)
\]
at each zero would be an RH-equivalent restatement.

### New corollaries independent of RH

1. The positive shell frame is not an unrelated decomposition of the integer coefficients: its
   transverse multipliers are the analytic continuation of one concrete maximum statistic of the
   Wold valuation source.
2. The least-integer normalization, Wold product law, and Fisher half-density select the same
   exponential scale independently.
3. Every hypothetical off-line zero has a canonical, source-measurable information defect
   \(1-2\Re\rho\); no finite differential jet or uniformly invertible transverse gauge can erase
   it.
4. Functional equation symmetry conserves the reflected likelihood product but reverses the
   defect.  This explains, in one formula, why reflection and positive orientation permit
   off-line quartets while a positive source-Born realization would not.

## 33. Scale--phase complementarity of the source conormal

The likelihood slope has a stronger projective meaning.  Fix \(M\geq12\), put
\[
 r_m(s):={|H_m(s)|^2\over h_m},
 \qquad
 Z_N(s):=\sum_{m=M}^{N}r_m(s),
 \qquad
 \nu_{N,s}(m):={r_m(s)\over Z_N(s)},                     \tag{240}
\]
and regard \(\nu_{N,s}\) as the Born distribution of the conormal over the first \(N\)
source shells.  This normalization is projective: rescaling the conormal line changes neither
\(\nu_{N,s}\) nor any conclusion below.

Let
\[
 q(s):=2^{1-2\Re s},
 \qquad
 C(s):=2|1-2^{-s}|^2.
\]
Sections 31--32 give the exact tail form
\[
 r_m(s)=C(s)q(s)^m(1+o(1)).                              \tag{241}
\]

`[PAPER-PROVED] [SOURCE_CONORMAL_PROJECTIVE_DEPTH_TRICHOTOMY]`

For every fixed \(s\) with \(0<\Re s<1\), the projective shell law has exactly one of the
following three completion phases.

1. If \(\Re s>1/2\), then \(q(s)<1\), \(Z_N(s)\) converges, and \(\nu_{N,s}\) converges in total
   variation to the probability
   \[
   \nu_{\infty,s}(m)
   ={r_m(s)\over\sum_{j=M}^{\infty}r_j(s)}.              \tag{242}
   \]
   Conormal information remains localized at the finite entrance of the shell tower.
2. If \(\Re s=1/2\), then \(q(s)=1\), and the pushforward of \(\nu_{N,s}\) by \(m\mapsto m/N\)
   converges weakly to Lebesgue probability on \([0,1]\):
   \[
   (m/N)_*\nu_{N,s}\Longrightarrow{\rm Unif}[0,1].       \tag{243}
   \]
   No fixed entrance packet and no fixed terminal packet retains positive mass.
3. If \(\Re s<1/2\), then \(q(s)>1\).  In the terminal coordinate \(k=N-m\),
   \(\nu_{N,s}\) converges in total variation to the geometric law
   \[
   \nu_{N,s}(N-k)
   \longrightarrow
   (1-q(s)^{-1})q(s)^{-k},
   \qquad k\geq0.                                        \tag{244}
   \]
   Conormal information is localized at the moving cutoff rather than at any intrinsic finite
   shell.

To prove the theorem, use `(241)`.  For \(q<1\), its geometric tail is summable and truncation
gives `(242)`.  For \(q=1\), \(r_m(s)\to C(s)>0\), so
\[
 Z_N(s)\sim C(s)N
\]
and weighted Riemann sums give `(243)`.  For \(q>1\), divide numerator and denominator by
\(r_N(s)\).  For each fixed \(k\),
\[
 {r_{N-k}(s)\over r_N(s)}\longrightarrow q(s)^{-k},
\]
while eventual two-sided geometric bounds dominate the reversed tail.  Normalizing its sum
\(\sum_{k\geq0}q^{-k}=(1-q^{-1})^{-1}\) proves `(244)` and total-variation convergence.

This trichotomy has two intrinsic information formulations.  Define projective participation
and Shannon information by
\[
 D_N(s):={1\over\sum_m\nu_{N,s}(m)^2}
 ={Z_N(s)^2\over\sum_{m=M}^{N}r_m(s)^2},
 \qquad
 {\cal H}_N(s):=-\sum_m\nu_{N,s}(m)\log\nu_{N,s}(m).     \tag{245}
\]
Then
\[
 \boxed{\quad
 \Re s=\frac12
 \quad\Longleftrightarrow\quad
 {D_N(s)\over N}\longrightarrow1
 \quad\Longleftrightarrow\quad
 {{\cal H}_N(s)\over\log N}\longrightarrow1
 \quad\Longleftrightarrow\quad
 \max_m\nu_{N,s}(m)\longrightarrow0.
 \quad}                                                   \tag{246}
\]
Off the line, \(D_N\) and \({\cal H}_N\) remain bounded.  On the left, `(244)` gives the explicit
participation limit
\[
 D_N(s)\longrightarrow{q(s)+1\over q(s)-1}.             \tag{247}
\]
On the right the finite limit depends on the complete entrance profile `(242)`, not merely its
tail ratio.

### The dual phase completion

The same theorem has a complementary Hardy/Wold face.  Put
\[
 z(s):=2^{1/2-s};
 \qquad |z(s)|^2=q(s).                                   \tag{248}
\]
For \(|z|\leq1\), let \(\mu_z\) be the unique probability measure on \(\mathbb T\) with
\[
 \int_{\mathbb T}\xi^n\,d\mu_z(\xi)=z^n,
 \qquad n\geq0.                                          \tag{249}
\]
If \(|z|<1\), \(\mu_z\) is the atomless Poisson measure of \(z\).  If \(|z|=1\), equality in
the triangle inequality gives \(\mu_z=\delta_z\).  Its first collision mass
\[
 \kappa_1(\mu_z)
 :=\sum_{\xi\in\mathbb T}\mu_z(\{\xi\})^2
 \]
therefore satisfies
\[
 \kappa_1(\mu_z)>0
 \quad\Longleftrightarrow\quad
 |z|=1.                                                  \tag{250}
\]

For \(\Re s\geq1/2\), use \(z(s)\).  For \(\Re s\leq1/2\), use the reflected interior
character
\[
 z(1-\overline s)={1\over\overline{z(s)}}.
\]
Both have phase \(e^{-i(\Im s)\log2}\).  Combining `(243)` and `(250)` gives the exact
scale--phase complementarity:

```text
critical conormal:
  diffuse through the entire exhaustive shell depth
  + atomic in the completed unitary phase
  + positive long-time collision plateau;

off-line conormal:
  localized at one shell endpoint
  + atomless Poisson phase storage
  + zero long-time collision plateau;

reflection:
  swaps entrance and terminal localization
  + preserves the atomless nature of off-line phase storage.
```

The uniformly invertible gauge of Section 31 does not alter this classification.  It tends to
one, so it preserves the projective limits `(242)`--`(247)` and the asymptotic character `(248)`.
The actual positive-shell conormal is therefore in the same scale--phase completion class as the
pure Szegő character \(z(s)^m\).

### Universal law suggested by the conjunction

The parent mathematics is classical separately: geometric endpoint limits, Szegő kernels,
Poisson representing measures, Wiener collision mass, and projective participation.  The
source-specific conjunction is new to this corpus:

> one and the same Wold-calibrated Xi conormal has a depth law and a phase law which exchange
> localization under passage from the Hardy interior to its recurrent boundary.

This changes the interpretation of the desired third completion.  It must not merely keep a
graded vector or a reflected pairing.  It must retain, for the same principal conormal class,
both:

1. its projective distribution over every exhaustive positive source frame; and
2. the collision hierarchy of its minimal unitary phase completion.

`[BOLD CONJECTURE] [SOURCE_EFFECTIVE_SCALE_PHASE_PURITY]`

For every source-minimal integral self-dual constrained HT object with an exact positive fusion,
the relative completion Bockstein of its principal divisor is **scale--phase pure**: it is
projectively non-atomic on every bornologically cofinal source-depth exhaustion and
collision-atomic in the corresponding unitary phase completion.  Both properties are transported
by one source morphism constructed before divisor specialization.

For the ordinary-prime source, either conclusion in this conjecture forces `(246)` or `(250)`,
hence
\[
 \Re\rho=\frac12
\]
for every nontrivial zero.  Stating either property only after choosing \(\rho\) is therefore
RH-equivalent and forbidden.  The content to prove is the joint source morphism: the positive
exponent shells already provide the depth distribution, while the CRT/Wold/Gamma/co-Poisson
Bockstein must prove that its completion is the same recurrent phase object.

### What this explains, and what it does not

This law joins results that previously appeared contradictory.

- The positive shell Gibbs bulk is atomless in clock time, yet a critical principal conormal may
  be phase-atomic: the atom is born in the relative completion, not inherited from the bulk.
- Ambient adelic \(L^2\) loses divisor points because it retains phase continuum without the
  nonzero shell-corona class.
- A Julia/Blaschke colligation retains an off-line zero because it converts endpoint-localized
  depth into atomless Poisson storage.
- Finite truncations always recur because they cannot distinguish bulk delocalization from
  endpoint localization before \(N\to\infty\).
- Hypertranscendence supplies unbounded transverse depth, but does not by itself force the
  projective distribution to use that depth.  The missing source theorem is precisely
  nonlocalization of the relative conormal, not another finite-rank or finite-jet estimate.

Equations `(240)`--`(250)` are unconditional.  They are more informative than the scalar slope
`(239)`, but they still classify rather than exclude a hypothetical off-line zero.  External
search found the classical Hardy/Poisson and product-measure parents, but no literature theorem
combining the largest-prime-exponent Wold law, positive HT common-divisor frame, projective depth
limit, and collision phase of the same Xi conormal.  This is a provisional noncollision statement,
not a priority claim.

## 34. Divisor--clock tame transgression: the missing interaction is secondary

The preceding mechanisms all attach the same centered prime character to a divisor conormal, but
none explained why an analytic divisor and an arithmetic clock should meet in one source
operation.  The interaction is not a primary tensor term in the relevant complex.  It is a
Milnor-\(K_2\) boundary.

### Universal divisor--clock theorem

Let \(X\) be a connected Riemann surface, \(M(X)\) its meromorphic function field, \(A\) an
abelian group, and
\[
 g:A\longrightarrow {\cal O}(X)^\times
 \qquad (a\longmapsto g_a)
\]
a group homomorphism into the nowhere-vanishing holomorphic functions.  For
\(f\in M(X)^\times\), define
\[
 \kappa_f(a):=\{f,g_a\}\in K_2^M(M(X)).                    \tag{251}
\]

`[PAPER-PROVED] [DIVISOR_CLOCK_TAME_TRANSGRESSION]`

For every \(x\in X\), with \(m_x=\operatorname{ord}_x(f)\), the tame boundary of `(251)` is
\[
 \boxed{\qquad
  \partial_x\kappa_f(a)=g_a(x)^{-m_x}.
 \qquad}                                                   \tag{252}
\]
Consequently \(a\mapsto\partial_x\kappa_f(a)\) is a character
\[
 A\longrightarrow\mathbb C^\times.                         \tag{253}
\]
If \(u\) is a meromorphic unit at \(x\), replacing \(f\) by \(uf\) does not change `(252)`.
Thus the boundary depends on the local divisor conormal and clock, not on a local equation chosen
for the divisor.

Indeed, the tame-symbol formula is
\[
 \partial_x\{f,g\}
 =
 (-1)^{v_x(f)v_x(g)}
 \left.
 {f^{v_x(g)}\over g^{v_x(f)}}
 \right|_x .
\]
Here \(v_x(g_a)=0\), giving `(252)`.  Multiplicativity of the Milnor symbol in its second
argument and \(g_{a+b}=g_ag_b\) give `(253)`.  If \(v_x(u)=0\), then
\(\partial_x\{u,g_a\}=1\), proving equation-independence.

The theorem is standard local \(K\)-theory.  Its source specialization below, and especially its
completed all-prime landing, are the new content of this route.

### The Riemann source specialization

Use the completed Riemann function in the uncentered variable, so
\[
 \Xi(s)=\Xi(1-s),
\]
and take the rational clock group
\[
 A=\mathbb Q_{>0}^{\times}
 \cong\bigoplus_p\mathbb Z[p].
\]
Its centered source clock is the nowhere-vanishing entire character
\[
 g_n(s):=n^{s-1/2}
 =\exp((s-\tfrac12)\log n).                                \tag{254}
\]
Define before choosing a zero
\[
 \boxed{\qquad
 \kappa_\Xi(n):=\{\Xi(s),n^{s-1/2}\}.
 \qquad}                                                   \tag{255}
\]
This is one multiplicative natural transformation in \(n\), not a list of zero-indexed
constructions.

If \(\rho\) is a zero of multiplicity \(m_\rho\), `(252)` gives
\[
 \boxed{\qquad
 \partial_\rho\kappa_\Xi(n)
 =
 n^{-m_\rho(\rho-1/2)}.
 \qquad}                                                   \tag{256}
\]
In particular, at a prime,
\[
 \partial_\rho\kappa_\Xi(p)
 =
 p^{m_\rho(1/2-\rho)},\qquad
 \log\left|\partial_\rho\kappa_\Xi(p)\right|
 =
 -m_\rho(\operatorname{Re}\rho-\tfrac12)\log p.            \tag{257}
\]

Equation `(257)` closes the **local analytic divisor--clock comparison**:
the centered prime holonomy is the actual tame boundary of one globally written analytic
divisor--clock symbol.  It also retains multiplicity and is independent of a local divisor
equation.  It does not yet identify this analytic \(K_2\) class with Deninger's arithmetic
Tate--Milnor coefficient; that source comparison remains open.  Taking an \(m_\rho\)-th root is
unnecessary: every completion selector below vanishes at slope
\(m_\rho(\operatorname{Re}\rho-\tfrac12)\) exactly when it vanishes at
\(\operatorname{Re}\rho-\tfrac12\).

This does not by itself prove RH.  Formula `(257)` exists for every entire function and every
zero.  Its value is the local datum which the missing source completion must conserve.

### Reflection is boundary inversion

The holomorphic reflection \(j(s)=1-s\) satisfies
\[
 g_n\circ j=g_n^{-1}.
\]
Therefore the symbols and their divisor boundaries obey
\[
 j^*\kappa_\Xi(n)=\kappa_\Xi(n)^{-1},\qquad
 \partial_{1-\rho}\kappa_\Xi(n)
 =
 \partial_\rho\kappa_\Xi(n)^{-1}.                         \tag{258}
\]
Including conjugation gives
\[
 \partial_{1-\overline\rho}\kappa_\Xi(n)
 =
 \overline{\partial_\rho\kappa_\Xi(n)}^{-1}.               \tag{259}
\]
Thus a reflected divisor point is fixed exactly when its tame clock character is unitary:
\[
 \rho=1-\overline\rho
 \quad\Longleftrightarrow\quad
 \left|\partial_\rho\kappa_\Xi(p)\right|=1
 \quad\Longleftrightarrow\quad
 \operatorname{Re}\rho=\frac12.                            \tag{260}
\]
Again `(260)` is a classification, not the source theorem forcing fixedness.

### The missing harmonic \(H^1\) channel is the real regulator of `(255)`

On Deninger's transverse orbit
\[
 S_p=\mathbb R/(\log p)\mathbb Z,
\]
the character `(257)` is the holonomy of a rank-one flat system.  Its real harmonic period is
\[
 b_{\rho,p}
 :=
 \log\left|\partial_\rho\kappa_\Xi(p)\right|
 =
 -m_\rho(\operatorname{Re}\rho-\tfrac12)\log p.             \tag{261}
\]
The exact local Dirichlet theorem of
`infinite-prime-wold-higgs-energy-purity` shows that the Tate-normalized minimum harmonic energy
of this period is \(b_{\rho,p}^2\); the Wold refinement multiplies it by
\(\delta_p=1-p^{-1}\).  Hence `(255)` gives, without adding a new primary cohomology summand,
\[
 {\cal E}_{P}^{W}(\partial_\rho\kappa_\Xi)
 =
 m_\rho^2(\operatorname{Re}\rho-\tfrac12)^2
 \sum_{p\in P}(1-p^{-1})(\log p)^2.                       \tag{262}
\]

`[PAPER-PROVED] [TAME_TRANSGRESSION_WOLD_ENERGY_PURITY]`

For cofinal finite prime sets \(P\),
\[
 \sup_P{\cal E}_{P}^{W}(\partial_\rho\kappa_\Xi)<\infty
 \quad\Longleftrightarrow\quad
 \operatorname{Re}\rho=\frac12.                            \tag{263}
\]
No prime number theorem is needed: every summand in `(262)` is at least
\(\tfrac12(\log2)^2\) times the fixed squared slope.

Equivalently, the tame boundary character belongs to the already-constructed third character
completion
\[
 \operatorname{Char}_W
 =
 \left\{
  \chi:
  \sum_p(\log|\chi(p)|)^2<\infty
 \right\}
 \quad\Longleftrightarrow\quad
 \operatorname{Re}\rho=\frac12.                            \tag{264}
\]
The finite mixed-Kummer Riesz regulator of `(257)` is exactly the coherent regulator of
`source-effective-polar-kummer-conormal-purity` with
\[
 c=-m_\rho(\operatorname{Re}\rho-\tfrac12).
\]
Its finite representatives have bounded bare Hilbert behavior but form a strict mixed-Cauchy
net only for \(c=0\).  Thus Wold energy divergence and prime-infinity Kummer leakage are two
different completion tests applied to the same tame boundary.  They have the same coherent-power
purity locus; their ambient completed spaces are not identified.

### Why the square-zero amalgamation was right

The Poisson radial ideal and the Tate--Milnor ideal cannot be joined by a raw tensor product:
that creates the forbidden primary term
\[
 P_{\mathbb Q}\widehat\otimes M_\zeta.
\]
Equation `(255)` does not revive that term.  A Milnor symbol is a secondary product, and `(256)`
is its localization boundary.  Any comparison with the arithmetic relevant complex can only
land at the cup/\(k\)-invariant level
\[
 H^1_{\rm radial}\times H^1_{\rm clock}
 \longrightarrow H^2_{\rm boundary},                      \tag{265}
\]
after the two primary ideals have been amalgamated over their common unit.  This is exactly where
the square-zero construction already said the missing interaction must live.  Constructing that
comparison is Clause 5 of `(266)`, not a consequence of the local tame formula.

The same observation identifies the harmonic-\(H^1\) issue correctly.  One must not append an
independent copy of \(H^1(S_p)\) to the three-term complex.  The constant harmonic form is the
real regulator of the secondary boundary `(256)`.  Its existence should follow from the global
cup/Green enhancement, while its energy is `(262)`.

### What the corpus is saying

The preceding dead ends become shadows of one law.

```text
finite jets and finite prime packets are freely controllable
  -> every finite restriction of the tame boundary is admissible;

ambient adelic L2 erases point fibres
  -> it completes primary functions rather than relative K2 boundaries;

positive Euler, Julia orientation, and hypertranscendence allow off-line systems
  -> they do not force continuity of the divisor--clock regulator;

Wold/Higgs energy rejects coherent off-line rays
  -> it is the harmonic norm of the tame boundary;

mixed Kummer completion detects mass at prime infinity
  -> it is the strong regulator topology of the same boundary;

functional equation reverses the radial defect
  -> it inverts the second entry of the Milnor symbol;

Meyer Toeplitz--Green cross-ray terms
  -> they are the analytic transgression needed to realize the secondary product;

Gamma and local Stokes data alone do not close the source
  -> the clock is essential at infinity and needs the global Ext/regulator seam.
```

The candidate universal interpretation is therefore:

> **Divisors do not acquire purity from a sign.  A constrained HT divisor is pure when its
> source clock symbol has a continuous global secondary regulator in the source-forced
> all-boundary topology.**

Critical-line purity is the unitary boundary of that conservation law.

### Exact new open core

`[BOLD CONJECTURE] [XI_SOURCE_DIFFERENTIAL_K2_TAME_LANDING]`

Let \(U_\Xi=\mathbb C\setminus\operatorname{div}(\Xi)\).  The completed
Euler--Gamma/co-Poisson source has a presentation-independent relative analytic/differential
\(K_2\) class
\[
 \mathfrak K_\Xi:
 \mathbb Q_{>0}^{\times}
 \longrightarrow
 \widehat K_{2,\mathrm{rel}}^{\rm src}
 \bigl(U_\Xi,\partial_{\rm ar}\cup\partial_\infty\bigr)      \tag{266}
\]
with the following properties.

1. **Finite-clock restriction.**  On every finite rational clock packet, `(266)` is the
   Beilinson/Deligne regulator class of \(\{\Xi(s),n^{s-1/2}\}\).
2. **Localization.**  Its finite divisor boundary is exactly `(256)`, including multiplicity.
3. **Source completion.**  The boundary map lands continuously in the Wold finite-energy
   harmonic character completion before any zero is selected.  A stronger alternative is a
   compatible landing in the strict polar Kummer--Arakelov completion.  These receivers have the
   same coherent-power purity locus but are not asserted to be equivalent spaces.
4. **Archimedean seam.**  The essential singularity of \(n^{s-1/2}\) at the compactified spectral
   infinity is repaired by the global Gamma/real \(\operatorname{Ext}^1\) regulator.  Local
   Stokes multipliers alone are insufficient and are not substituted for this clause.
5. **Derived typing.**  The class realizes the cup/\(k\)-invariant `(265)` in the shifted
   analytic-graph/Milnor-conormal intersection, not a forbidden primary tensor cross term.
6. **Conormal conservativity.**  Every nonzero top principal divisor jet has nonzero boundary;
   changing the source determinant by a nowhere-vanishing factor changes `(266)` by a
   boundary-trivial symbol.
7. **Presentation independence.**  Euler windows, Gamma gauges, co-Poisson models, and
   source-equivalent prime exhaustions give the same completed class.

The analytic local models required by Clauses 1--2, including equation-independence, have now been
proved by `(251)`--`(257)`.  Their lift to the completed arithmetic source in `(266)` has not.
Clause 3 is the RH-bearing theorem.  Stating it separately at a chosen \(\rho\) is equivalent to
RH by `(263)` and is forbidden.  Candidate-new mathematics begins with construction of the one
global source class `(266)`, comparison of its analytic and arithmetic \(K\)-theory readings, and
proof that its localization is continuous in the independently constructed source topology.

If `(266)` exists, every nontrivial zero has a tame boundary in \(\operatorname{Char}_W\).
Equation `(264)` then gives
\[
 \operatorname{Re}\rho=\frac12
\]
for every nontrivial zero, hence RH.

### First construction target

For a finite prime packet \(P\), construct the relative Deligne regulator currents
\[
 {\cal R}_{P}
 =
 \left(
  r_D\{\Xi,p^{s-1/2}\}
 \right)_{p\in P},                                         \tag{267}
\]
where \(r_D\) is the standard regulator of a Milnor symbol.  Prove simultaneously:

1. its divisor current is `(257)`;
2. its real period on \(S_p\) is `(261)`;
3. its Green boundary pairing is Meyer's cutoff-independent Toeplitz transgression;
4. its Kummer boundary is the finite strict pro-log residue;
5. finite-set enlargement is the restriction of one nested Wold-sieve/Rees cocycle, with the
   global Gamma \(\operatorname{Ext}^1\) seam supplying the infinity correction.

Items 1--2 are closed above.  Existing corpus theorems separately supply the target in items 3--4.
The first non-immediate obstacle is item 5: construct one chain-level regulator whose Green and
Kummer readings are those already-proved maps.  This is narrower than constructing an arbitrary
Hodge star or postulating source-effectivity of every conormal.

### Hostile audit

1. The local tame formula is standard and is not an RH advance by itself.
2. Any entire function admits `(251)`; arithmetic content begins only with the completed
   ordinary-prime source landing.
3. Assuming Clause 3 at each zero is RH in different notation.
4. \(\Xi\) is an analytic determinant, not an algebraic unit of the original arithmetic field.
   A comparison to Deninger's Tate--Milnor coefficient must be constructed, not inferred.
5. The exponential clock has an essential singularity at compactified infinity.  Ordinary Weil
   reciprocity on a compact algebraic curve does not apply.
6. The corpus proves that local archimedean Stokes multipliers are Tate-local; the missing seam is
   a global regulator.  A local wild-monodromy argument cannot prove Clause 4.
7. The tame symbol records multiplicity but not the entire nilpotent jet tower.  RH needs only
   nonzero support; any stronger simplicity claim requires additional faithfulness.
8. An off-line generalized-prime Euler system automatically has local symbols like `(255)`.
   It falsifies the universal law only if it also carries the same literal ordinary-prime source
   completion, global Gamma regulator, strict Kummer boundary, and continuous secondary landing.
9. A raw all-prime product of symbols diverges.  The source object must use the nested
   Wold-sieve/Rees completion already forced by the corpus.
10. No positivity, self-adjointness, or reflected norm equality may be inserted to prove
    continuity; those would import the conclusion.

### Literature boundary and anti-theatre verdict

Milnor \(K_2\), tame symbols, localization sequences, Deligne/Beilinson regulators, and regulator
currents of pairs of meromorphic functions are parent mathematics.  Targeted corpus and primary
literature searches found no use of the specific source family
\[
 \{\Xi(s),n^{s-1/2}\}
\]
to realize the centered prime conormal character, and no completed ordinary-prime
differential-\(K\) landing whose continuity gives Riemann purity.  Search noncollision is not a
priority proof.

The non-theatrical advance is exact:

```text
previously conjectural:
  why the Xi divisor conormal has the ordinary-prime centered character;
  where the missing harmonic-H1 mode belongs;
  what operation can couple square-zero radial and Kummer sectors;

now paper-proved:
  all three are the tame boundary / real regulator of one secondary K2 symbol;

remaining:
  construct its one global completed source regulator and prove continuous localization.
```

No Lean formalization is started here.  The local theorem is standard and the global
source-landing theorem is still open; formalizing the former alone would not move the RH frontier.

### Determinant central extension: one object behind four reporters

There is a canonical determinant central extension of the local Tate loop group
\[
 1\longrightarrow\mathbb C^\times
 \longrightarrow\widehat{\mathbb C((z))^\times}
 \longrightarrow\mathbb C((z))^\times
 \longrightarrow1.                                          \tag{268}
\]
A classical theorem identifies the commutator of lifts in `(268)` with the
Contou--Carrère symbol; over the field \(\mathbb C\), this is the ordinary tame symbol, up to the
fixed convention for inversion.

At a zero \(\rho\), choose \(z=s-\rho\) and write
\[
 \Xi(s)=z^{m_\rho}u_\rho(z),\qquad u_\rho(0)\ne0,
\]
while
\[
 p^{s-1/2}
 =
 p^{\rho-1/2}\exp(z\log p).                                  \tag{269}
\]
The determinant commutator of these two local loop multipliers is therefore
\[
 [\widehat\Xi,\widehat g_p]_{\det}
 =
 p^{-m_\rho(\rho-1/2)},                                     \tag{270}
\]
which is `(256)`.

The real regulator form of the same symbol is
\[
 \eta(f,g)
 =
 \log|f|\,d\arg g-\log|g|\,d\arg f.                          \tag{271}
\]
For the Riemann clock,
\[
 \boxed{\quad
 \eta(\Xi,p^{s-1/2})
 =
 \log p\left(
  \log|\Xi|\,d\,\operatorname{Im}s
  -(\operatorname{Re}s-\tfrac12)d\arg\Xi
 \right).
 \quad}                                                      \tag{272}
\]
Hence every prime regulator is one scalar evaluation of the universal rank-one field
\[
 \eta_\Xi
 :=
 \log|\Xi|\,d\,\operatorname{Im}s
 -(\operatorname{Re}s-\tfrac12)d\arg\Xi.                    \tag{273}
\]
For a sufficiently small positive loop \(\gamma_\rho\),
\[
 {1\over2\pi}\int_{\gamma_\rho}\eta(\Xi,p^{s-1/2})
 =
 -m_\rho(\operatorname{Re}\rho-\tfrac12)\log p
 =
 \log\left|\partial_\rho\kappa_\Xi(p)\right|.                \tag{274}
\]
The first term in `(272)` has vanishing limiting loop integral; the second uses
\(\int_{\gamma_\rho}d\arg\Xi=2\pi m_\rho\).

Thus the corpus's proposed one-field phenomenon is literal here:

```text
group-level commutator:
  Contou--Carrère / tame character (270);

real differential regulator:
  harmonic-H1 period (274);

infinitesimal central-extension cocycle:
  residue / first-trace boundary;

operator realization:
  determinant and Toeplitz--Green transgression.
```

Only the first two identifications are closed for the Riemann symbol.  The last two are a sharply
typed comparison target, not yet a theorem: one must show that the already-constructed nested
Wold determinant extension and Meyer's Toeplitz extension pull back to the same determinant
central-extension class as `(268)`, with the BV term supplying the singular first-trace
correction.

This replaces the vague instruction “integrate the Wold determinant and BV trace into one
differential character” by the following cocycle comparison.

`[OPEN CORE] [XI_WOLD_CONTOU_CARRERE_EXTENSION_COMPARISON]`

Construct a morphism of source-defined central extensions
\[
 \widehat{\mathcal G}_{\rm Wold/Gamma/BV}^{\rm src}
 \longrightarrow
 \widehat{\mathcal G}_{\rm CC}^{\rm rel}                       \tag{275}
\]
such that:

1. the prime-dilation generator maps to \(p^{s-1/2}\);
2. the distinguished determinant section maps to the local multiplier \(\Xi(s)\);
3. the group commutator maps to `(270)`;
4. differentiation of `(275)` maps the BV/renormalized first trace to the residue cocycle of
   `(268)`;
5. the Green realization maps Meyer's cutoff-independent Toeplitz cocycle to the real regulator
   `(271)`;
6. the nested prime-sieve/Rees filtration makes `(275)` a morphism of restricted, not direct
   product, extensions.

Parent theory proves that determinant extensions, Contou--Carrère symbols, Deligne pairings, and
their local reciprocity laws fit this architecture.  It does not construct `(275)` for the
Euler--Gamma/co-Poisson HT source.  If `(275)` is built, Clauses 1--2 of `(266)` and the
chain-level typing in Clause 5 become consequences of one extension comparison.  The remaining
RH-bearing step is still restricted implementability/continuity of its principal conormal
commutator in the all-prime completion.

This also locates the third completion more precisely.  It is not merely a Hilbert space or a
measure sector.  It should be the restricted determinant/Heisenberg extension in which:

```text
unitary prime phase remains an actual central character;
localized square-summable radial displacement remains implementable;
coherent off-line radial displacement is non-implementable;
the source principal conormal nevertheless has a canonical lift.
```

The last line is the new source theorem.  Declaring that lift implementable after choosing a zero
would again restate RH.

### Local Wold-defect determinant retains every multiplicity jet

The determinant interpretation can be proved without invoking an abstract central extension.
Let \({\cal O}_\rho\) be the local analytic ring at a zero \(\rho\), and put
\[
 A_\rho:={\cal O}_\rho/(\Xi).
                                                               \tag{276}
\]
If \(m=m_\rho\), choose \(z=s-\rho\).  Since
\(\Xi=z^m u\) with \(u\) a local unit,
\[
 A_\rho\cong\mathbb C[z]/(z^m).                                \tag{277}
\]
Let \(N_\rho\) be multiplication by \(z\) on \(A_\rho\), so
\[
 N_\rho^m=0.
\]

`[PAPER-PROVED] [LOCAL_XI_CLOCK_WOLD_DEFECT_DETERMINANT]`

The prime clock acts on the complete local divisor jet by
\[
 \boxed{\qquad
 G_{p,\rho}
 :=
 M_{p^{s-1/2}}\big|_{A_\rho}
 =
 p^{\rho-1/2}\exp((\log p)N_\rho).
 \qquad}                                                       \tag{278}
\]
Consequently
\[
 \det G_{p,\rho}
 =
 p^{m_\rho(\rho-1/2)},\qquad
 \partial_\rho\kappa_\Xi(p)
 =
 (\det G_{p,\rho})^{-1}.                                      \tag{279}
\]

To prove `(278)`, reduce the identity
\[
 p^{s-1/2}
 =
 p^{\rho-1/2}\exp((s-\rho)\log p)
\]
modulo \(z^m\).  The exponential becomes the finite polynomial
\[
 \exp((\log p)N_\rho)
 =
 \sum_{j=0}^{m-1}{(\log p)^j\over j!}N_\rho^j.
\]
It is unipotent upper triangular in the basis
\((1,z,\ldots,z^{m-1})\), so its determinant is one.  This proves the first equation in `(279)`;
the second is `(257)`.

There is also a literal Wold-defect model.  On a local Hardy germ, multiplication by \(z^m\) has
range \(z^mH^2\) and defect quotient
\[
 H^2/z^mH^2
 \cong
 \operatorname{span}\{1,z,\ldots,z^{m-1}\}
 \cong A_\rho.                                                \tag{280}
\]
Multiplication by the analytic unit \(p^{s-1/2}\) preserves the range and induces `(278)` on the
defect.  Its determinant-line action is `(279)`.  Thus the local tame symbol, the prime-dilation
jet, and determinant holonomy on a Wold defect are one exact object.

This corrects the earlier concern that the tame boundary sees multiplicity but not the nilpotent
jet.  The scalar boundary `(279)` sees only the determinant, but its canonical lift `(278)` retains
the complete length-\(m_\rho\) local algebra and its nilpotent clock action.  Any global restricted
extension comparison should transport `(278)`, not only `(279)`.

The remaining infinity problem is now exact:

```text
finite divisor point:
  canonical Wold defect A_rho and full prime-clock jet G_(p,rho);

all divisor points and all primes:
  construct one source-restricted determinant/Fock module containing these defects;

purity:
  prove every source-produced defect is implementable in that fixed module.
```

Every finite family of operators `(278)` is implementable for every \(\rho\).  Only the
all-prime restricted determinant extension can force the radial semisimple part to be unitary.

### Global analytic localization produces every divisor jet at once

The local algebras `(276)` are the stalks of one source-defined coherent torsion sheaf.  Let
\[
 D_\Xi:=V(\Xi)\subset\mathbb C,\qquad
 U_\Xi:=\mathbb C\setminus D_\Xi,\qquad
 {\cal O}_{D_\Xi}:={\cal O}_{\mathbb C}/\Xi{\cal O}_{\mathbb C}.  \tag{281}
\]
Multiplication by \(\Xi\) is a global analytic Cartier equation, so
\({\cal O}_{D_\Xi}\) is defined without enumerating its support.

Use the localization boundary from analytic \(K\)-theory of the complement to coherent
\(K\)-theory with support,
\[
 \partial_{D_\Xi}:
 K_2(U_\Xi)\longrightarrow K_1^{D_\Xi}(\mathbb C).             \tag{282}
\]

`[PUBLISHED LOCALIZATION THEOREM, SPECIALIZED HERE]`
`[GLOBAL_XI_CLOCK_SUPPORTED_K1_CLASS]`

With the tame-symbol convention of `(252)`,
\[
 \boxed{\qquad
 \partial_{D_\Xi}
 \{\Xi(s),n^{s-1/2}\}
 =
 \left[
  M_{n^{1/2-s}}:
  {\cal O}_{D_\Xi}\xrightarrow{\sim}{\cal O}_{D_\Xi}
 \right].
 \qquad}                                                       \tag{283}
\]
The right side is one global supported \(K_1\)-class.  Its stalk at a zero \(\rho\) is
\[
 G_{n,\rho}^{-1}
 =
 n^{1/2-\rho}\exp(-(\log n)N_\rho)                              \tag{284}
\]
on the complete local divisor algebra \(A_\rho\).  Its local determinant is
\[
 \det(G_{n,\rho}^{-1})
 =
 n^{-m_\rho(\rho-1/2)},                                        \tag{285}
\]
the tame boundary `(256)`.

Equation `(283)` is the \(K\)-theoretic localization description of the tame symbol.  It can also
be checked from the two-term perfect complex
\[
 [{\cal O}_{\mathbb C}\xrightarrow{\Xi}{\cal O}_{\mathbb C}]
\]
supported on \(D_\Xi\): the global unit \(n^{1/2-s}\) acts on its support cohomology
\({\cal O}_{D_\Xi}\), and devissage gives `(283)`.  Localizing and taking determinants gives
`(285)`.

Several formerly separate source requirements now close at the analytic \(K\)-theory level.

1. **Source-first production.**  The class `(283)` is written on the whole divisor sheaf before
   a zero is selected.
2. **Multiplicity-jet conservativity.**  Every stalk contains its full nilpotent operator
   `(284)`, not only its determinant.
3. **Clock coherence.**  The assignment
   \[
    n\longmapsto
    [M_{n^{1/2-s}}|_{{\cal O}_{D_\Xi}}]
   \]
   is a group homomorphism from \(\mathbb Q_{>0}^{\times}\) to supported \(K_1\).
4. **Equation independence.**  Replacing \(\Xi\) by a nowhere-vanishing multiple gives the same
   divisor sheaf and the same supported boundary.
5. **Reflection.**  Pullback by \(s\mapsto1-s\) inverts the supported clock automorphism.

This does not yet prove the arithmetic source landing.  The coherent analytic divisor sheaf and
Deninger's Tate--Milnor/Wold coefficient live in different realizations.  The exact remaining
comparison is now a realization functor, not construction of a zero-indexed character:
\[
 \boxed{\qquad
 {\cal R}_{\rm ar/Wold}:
 \operatorname{Hom}\!\left(
  \mathbb Q_{>0}^{\times},K_1^{D_\Xi}(\mathbb C)
 \right)_{\rm src}
 \longrightarrow
 \Gamma\!\left(
  D_\Xi,\mathscr{Char}_{W}^{\,\rm rel}
 \right).
 \qquad}                                                       \tag{286}
\]
Here \(\mathscr{Char}_{W}^{\,\rm rel}\) denotes the sheaf of restricted determinant/Wold
characters along the divisor, not a Hilbert completion of the exponent lattice
\(\mathbb Q_{>0}^{\times}\).  The latter completion would be wrongly typed: the logarithm map on
clock exponents need not be continuous for an unweighted \(\ell^2\) norm.

The functor `(286)` must be induced by the Euler--Gamma/co-Poisson source, preserve the local
operators `(284)`, and be continuous for the independently constructed topology on the **target
character field**.  Membership of every stalk of its output is `(263)` and therefore
RH-equivalent.  Frontier content is a single global functor on the supported clock homomorphism
`(283)`, together with its source construction and strict target landing before support
decomposition.

This also eliminates the divergent-symbol-product mistake.  One never multiplies
\(\{\Xi,p^{s-1/2}\}\) over all primes.  The algebraic source is the homomorphism in item 3 on the
finite-support clock group.  Infinity enters only when asking whether its polar boundary defines a
section of the restricted Wold or Kummer **character** completion.

### Meyer's Green cocycle is the infinitesimal determinant cocycle

The operator/Green realization in `(275)` can be identified on Meyer's proved source test algebra.
Use the Mellin convention
\[
 \widehat F(s)
 =
 \int_0^\infty F(x)x^s\,d^\times x.                           \tag{287}
\]
Then multiplicative convolution becomes multiplication and
\[
 \widehat{\partial G}(s)
 =
 {d\over ds}\widehat G(s),
 \qquad
 \partial G(x)=G(x)\log x.                                    \tag{288}
\]
Mellin inversion at \(x=1\) gives, on any vertical line in the common holomorphy strip,
\[
 \boxed{\qquad
 \omega_{\rm mult}(F,G)
 =
 \tau(F*\partial G)
 =
 {1\over2\pi i}
 \int_{\sigma-i\infty}^{\sigma+i\infty}
 \widehat F(s)\,d\widehat G(s).
 \qquad}                                                       \tag{289}
\]
With the opposite Mellin convention, both derivative and orientation introduce the corresponding
fixed sign.  Schwartz decay makes the endpoint term vanish, so integration by parts gives the
antisymmetry already proved by Meyer.

`[PAPER-PROVED FROM MELLIN INVERSION]`
`[MEYER_GREEN_IS_INFINITESIMAL_DETERMINANT_COCYCLE]`

Equation `(289)` is the standard Heisenberg/determinant Lie-algebra cocycle
\[
 (a,b)\longmapsto {1\over2\pi i}\int a\,db,                  \tag{290}
\]
the infinitesimal form of the Contou--Carrère commutator.  Thus Meyer's source Green form and the
local determinant extension `(268)` are already the same parent cocycle on their common smooth
domain.

The Riemann specialization makes the group-level boundary visible.  Put
\[
 \ell_p(s):=\log g_p(s)=(s-\tfrac12)\log p.
\]
On a small positive loop around a multiplicity-\(m_\rho\) zero,
\[
 \boxed{\qquad
 {1\over2\pi i}
 \int_{\gamma_\rho}
 \ell_p(s)\,d\log\Xi(s)
 =
 m_\rho(\rho-\tfrac12)\log p.
 \qquad}                                                       \tag{291}
\]
Indeed \(d\log\Xi=m_\rho\,ds/(s-\rho)+d\log u_\rho\), and the unit term has zero residue.
Exponentiating the negative of `(291)` gives
\[
 \exp\!\left(
  -{1\over2\pi i}\int_{\gamma_\rho}\ell_p\,d\log\Xi
 \right)
 =
 p^{-m_\rho(\rho-1/2)},
 \]
which is simultaneously `(256)`, `(270)`, and `(285)`.

This closes the comparison on finite contours:

```text
Meyer Green cocycle on Mellin test packets
  = infinitesimal determinant cocycle;

Xi log connection paired with prime log clock
  = logarithm of the tame/determinant commutator;

local residue
  = full prime-clock determinant on the Xi Wold defect.
```

It does not yet justify inserting \(\ell_p\) and \(\log\Xi\) directly into Meyer's nuclear
Schwartz algebra.  They are logarithmic relative currents, not compactly supported test packets.
The next analytic theorem is therefore exact:

`[OPEN CORE] [MEYER_GREEN_LOGARITHMIC_RELATIVE_EXTENSION]`

Extend `(289)` from the nuclear Mellin test algebra to the relative pair
\[
 (\ell_p,d\log\Xi)
\]
so that:

1. excision around \(D_\Xi\) has local boundary `(291)`;
2. Meyer's \(Z\)-conjugation supplies the finite Euler logarithmic connection;
3. Fourier reflection and the Gamma factor supply the global real/\(\operatorname{Ext}^1\)
   boundary at spectral infinity;
4. the extension is cutoff-independent and agrees with the supported class `(283)`;
5. nested prime-sieve enlargement is continuous in the restricted determinant topology, uniformly
   on the source principal-conormal sheaf.

Items 1 and the test-domain identity are closed by `(289)`--`(291)`.  Meyer's published trace
theorem supplies source nuclearity after convolution by admissible packets, but it does not state
the logarithmic relative extension above.  Item 5 remains the all-prime RH-bearing landing.

## 35. Polarized tame base change: localize first, then complete

The previous section still leaves one dangerous ambiguity.  A single global determinant central
extension is not enough.  Reflection can pair two nonunitary local determinant characters whose
product is unitary.  Thus a global \(U(1)\)-valued determinant can coexist with an off-line zero.
The missing structure must retain the centre **over divisor support**, before taking a determinant
product or trace.

### The factorized radial obstruction

Let \(D_f\) be the divisor of a meromorphic function \(f\) on a Riemann surface, and let
\[
 {\cal A}_x={\cal O}_x/(f),\qquad
 \lambda_x:=\det_{\mathbb C}{\cal A}_x
 \]
at a zero \(x\) of multiplicity \(m_x\).  The supported boundary of the divisor--clock symbol
\(\{f,g_a\}\) acts on \(\lambda_x\) by the scalar
\[
 c_{x,a}:=g_a(x)^{-m_x}.                                    \tag{292}
\]
Do not multiply these scalars over \(x\).  Retain them as a section of the factorized centre
\[
 c_{f,g}(a)\in
 \Gamma\!\left(D_f,\underline{\mathbb C^\times}_{D_f}\right). \tag{293}
\]
Quotienting each local centre by its maximal compact subgroup gives the radial-obstruction sheaf
\[
 \underline{\mathbb C^\times/U(1)}_{D_f}
 \cong\underline{\mathbb R}_{D_f},
 \qquad
 [z]\longmapsto\log|z|.
\]
The factorized radial obstruction is therefore
\[
 {\mathfrak a}_{f,g}(a)_x
 :=
 \log|c_{x,a}|
 =
 -m_x\log|g_a(x)|.                                         \tag{294}
\]

`[PAPER-PROVED] [FACTORIZED_TAME_RADIAL_OBSTRUCTION]`

Equations `(292)`--`(294)` are natural under restriction to an open subset, independent of the
local equation of the divisor, additive in the clock variable, and preserved by analytic
localization.  The obstruction vanishes at \(x\) exactly when the tame boundary acts isometrically
on the one-dimensional determinant line \(\lambda_x\), for one—and hence every—positive
Hermitian norm on that line.

For the Riemann clock,
\[
 {\mathfrak a}_{\Xi}(p)_\rho
 =
 -m_\rho(\operatorname{Re}\rho-\tfrac12)\log p.             \tag{295}
\]
This is simultaneously the real regulator period `(274)`, the logarithm of the local determinant
commutator `(270)`, and the real Higgs displacement `(261)`.

The determinant line is essential here.  Requiring the complete jet operator `(278)` to be unitary
would also kill its nontrivial unipotent part and would force simplicity of every zero.  That is
stronger than RH and is neither needed nor justified.  The proposed polarization acts on the
factorized determinant/associated-graded line while the nilpotent multiplicity filtration remains
present as filtered data.

### Global pushforward blindness

`[PAPER-PROVED] [REFLECTED_GLOBAL_DETERMINANT_RADIAL_BLINDNESS]`

On one reflected-conjugate pair \(\{\rho,1-\overline\rho\}\), functional-equation symmetry gives
\[
 {\mathfrak a}_{\Xi}(p)_{1-\overline\rho}
 =
 -{\mathfrak a}_{\Xi}(p)_\rho.                              \tag{296}
\]
Consequently
\[
 \left|
 \partial_\rho\kappa_\Xi(p)\,
 \partial_{1-\overline\rho}\kappa_\Xi(p)
 \right|=1                                                  \tag{297}
\]
even when \(\operatorname{Re}\rho\ne1/2\).

Thus every reporter which first pushes the local centres to one scalar by the reflection-invariant
product, determinant, or additive trace annihilates the radial obstruction on each off-line
pair.  This is an exact no-go, not merely an insufficiency observed so far:

```text
factorized local centre:
  remembers a_rho and -a_rho separately;

global determinant / trace:
  sees only a_rho + (-a_rho) = 0;

functional equation:
  guarantees the cancellation but not either local vanishing.
```

This explains why global self-duality, a Krein-unitary pairing, determinant modulus one, and
reflection-positive quartet data can all hold off the critical line.  A global projective-unitary
commutator is still too coarse if its centre has already been pushed forward from divisor support.

### Universal polarized-localization theorem

Let a source object produce:

1. a divisor \(D_f\) and the divisor--clock \(K_2\) class before support decomposition;
2. its supported localization `(293)`;
3. a factorized Hermitian determinant line
   \[
   (\lambda_{D_f}^{\rm fac},h_{D_f})
   =
   \{(\lambda_x,h_x)\}_{x\in D_f};
   \]
4. a source clock action on these lines agreeing with `(292)`.

`[PAPER-PROVED ABSTRACT IMPLICATION] [POLARIZED_TAME_BASE_CHANGE_PURITY]`

If the clock action is supportwise isometric,
\[
 h_x(c_{x,a}v,c_{x,a}v)=h_x(v,v)
 \qquad
 (x\in D_f,\;v\in\lambda_x),                               \tag{298}
\]
then
\[
 {\mathfrak a}_{f,g}(a)_x=0
 \qquad (x\in D_f).                                        \tag{299}
\]

Indeed, choose \(v\ne0\).  Since \(\lambda_x\) is one-dimensional, `(298)` gives
\[
 |c_{x,a}|^2h_x(v,v)=h_x(v,v).
\]
Positivity permits cancellation, so \(|c_{x,a}|=1\), which is `(299)`.

For `(255)`, one prime clock already gives
\[
 1
 =
 \left|p^{-m_\rho(\rho-1/2)}\right|
 =
 p^{-m_\rho(\operatorname{Re}\rho-1/2)}.
\]
Since \(p>1\) and \(m_\rho>0\),
\[
 \operatorname{Re}\rho=\frac12.                            \tag{300}
\]
Therefore supportwise polarized tame base change for the source-produced Riemann class proves RH.

The theorem is elementary after its hypotheses are typed.  The research content is the
source-natural base-change law producing `(298)` before any zero is selected:
\[
\boxed{\qquad
 {\rm Pol}_{D_\Xi}^{\rm fac}\circ\partial_{D_\Xi}
 \;\simeq\;
 \partial_{D_\Xi}^{\,U(1),{\rm fac}}\circ{\rm Pol}_{\rm src}.
\qquad}                                                     \tag{301}
\]
Here \({\rm Pol}_{\rm src}\) is the completed Euler--Gamma/co-Poisson polarization, while the
right boundary is a factorized \(U(1)\)-central determinant boundary.  Equation `(301)` says:

> **positive completion commutes with secondary divisor localization before global
> pushforward.**

This is the sharper universal law.  Purity is not positivity of a global scalar.  It is exactness
of polarization under localization, with the factorized centre retained.

### The reporters are shadows of one obstruction

For the coherent Riemann power character, the corpus now gives the following implications from one
local section `(295)`:
\[
\begin{array}{c}
 {\mathfrak a}_{\Xi}(p)_\rho=0\ \text{for one prime}\\
 \Updownarrow\\
 \text{factorized tame commutator lies in }U(1)\\
 \Updownarrow\\
 \text{real divisor--clock regulator period vanishes}\\
 \Updownarrow\\
 \text{cofinal Wold--Higgs energy is finite}\\
 \Updownarrow\\
 \text{strict mixed-Kummer mass does not leak to prime infinity}\\
 \Updownarrow\\
 \text{Kakutani radial sector equals the critical sector}\\
 \Updownarrow\\
 \operatorname{Re}\rho=\tfrac12 .
\end{array}                                                  \tag{302}
\]
The equivalences in `(302)` concern this coherent one-parameter character.  They do not identify
the ambient Wold, Kummer, and Kakutani completions.  Those are distinct realizations of the same
factorized radial obstruction.

Equation `(302)` changes the role of the earlier selectors.  None is the cause of purity.  Each is
a norm, boundary, or measure-class reporter of failure of `(301)`.  The cause would be
source-effective polarized localization.

### What all the no-go results mean

```text
finite truncations:
  localize divisor jets, but do not retain a source-cofinal polarization;

ambient adelic L2:
  retains unitary source covariance, but localization is nonconservative;

global determinant and functional equation:
  push factorized centres together and cancel opposite radial defects;

positive Euler / Julia / hypertranscendental off-line models:
  possess analytic divisor localization but not the literal source-polarized base change (301);

Wold energy, Kummer leakage, and Kakutani singularity:
  retain the local radial obstruction after different infinite completions;

Meyer nuclear trace:
  gives global traceability modulo nuclear defects, but not a supportwise positive projector;

square-zero radial--Kummer amalgamation:
  correctly forbids a fake primary tensor; tame localization supplies the secondary interaction;

the missing harmonic H1 channel:
  is the real part of the factorized determinant commutator, not a free cohomology summand.
```

The “third completion” is therefore not one more ambient Hilbert space.  It is a factorization
determinant/Heisenberg boundary with:

1. analytic \(K_2\) localization retaining every support and multiplicity filtration;
2. a source-produced positive metric on every local determinant line;
3. a restricted all-prime topology on the radial obstruction sheaf;
4. a global Gamma/real seam;
5. pushforward only after local \(U(1)\)-reduction.

This order of operations is load-bearing:
\[
 \text{localize}\longrightarrow\text{polarize}\longrightarrow\text{push forward},
\]
not
\[
 \text{polarize globally}\longrightarrow\text{push forward}\longrightarrow\text{infer locality}.
\]

### Exact RH-bearing open core

`[BOLD CONJECTURE] [XI_SOURCE_POLARIZED_TAME_BASE_CHANGE]`

The Euler--Gamma/co-Poisson source admits a factorization-natural refinement of `(275)` and `(286)`
for which:

1. the analytic symbol `(255)` maps to the source residue-corrected Wold--Gamma/BV determinant
   character;
2. localization is the supported \(K_1\)-class `(283)` before any support pushforward;
3. the factorized determinant line of every local multiplicity filtration receives a positive
   source metric, without requiring the full nilpotent jet operator to be unitary;
4. the clock action on that determinant line is isometric and agrees with `(284)` on its
   determinant;
5. Meyer Green, BV first trace, strict Kummer boundary, and Gamma reflection are comparison
   realizations of the same factorized class;
6. the construction is strict under nested ordinary-prime and source-jet enlargement;
7. no divisor stalk is killed, paired with its reflection before polarization, or renormed using
   its zero coordinate.

Clauses 1--2 are proved at the analytic/localization level in Section 34.  The finite-contour
infinitesimal comparison is `(289)`--`(291)`.  The corpus separately supplies the Wold/BV source
character, Meyer nuclear relation, and the target radial reporters.  Clauses 3--7—the
factorized positive base-change morphism—are the remaining theorem.

If this conjecture is proved, `(298)`--`(300)` give RH without a separate finite-energy assumption.
Wold energy finiteness then becomes a corollary of local unitarity, not the load-bearing premise.

### Hostile audit

1. A single determinant line, global \(U(1)\) extension, or global Krein pairing does not imply
   `(298)`; `(296)`--`(297)` give an explicit off-line cancellation.
2. A Hermitian metric selected after choosing \(\rho\) is circular.  The metric and localization
   comparison must be natural on the entire source divisor object.
3. Positivity before localization does not automatically descend through a quotient.  Exactness
   of `(301)` is the theorem, not category notation for a presumed fact.
4. Meyer's almost-projector is idempotent only modulo nuclear defects.  Nuclear traceability does
   not supply the supportwise positive determinant lines in Clause 3.
5. Requiring the full jet clock `(278)` to be unitary would silently assert zero simplicity.
   Only its determinant/associated-graded line is polarized here.
6. A factorization determinant gerbe exists in parent mathematics, but its \(U(1)\) reduction for
   this Euler--Gamma/co-Poisson source is not automatic.
7. Clause 7 is indispensable.  Pairing \(\rho\) with \(1-\overline\rho\) first collapses exactly
   the obstruction that must be shown to vanish.
8. Rephrasing \(\operatorname{Char}_W\)-membership as “polarized localization” without constructing
   `(301)` is still RH-equivalent theatre.

### Literature boundary

Localization in algebraic/analytic \(K\)-theory, determinant lines and gerbes, factorization
extensions, Contou--Carrère symbols, Deligne pairings, and unitary reductions of Hermitian lines
are parent mathematics.  The generalized Contou--Carrère symbol as a \(K\)-theory boundary and
higher commutator is treated by Braunling--Groechenig--Wolfson
(<https://arxiv.org/abs/1410.3451>); determinant bundles and Deligne pairings are compared by
Biswas--Schumacher--Weng (<https://arxiv.org/abs/1106.0255>).

The candidate-new content is not those constructions.  It is the source-specific law `(301)`:
factorized positive completion of the ordinary-prime Euler--Gamma/co-Poisson determinant character
commutes with its Xi tame localization, and therefore reduces every local divisor-clock
commutator to \(U(1)\).  No located source proves this.  Search noncollision is not a priority
certificate.

## 36. The universal primitive-torsor law

The factorized base-change law has an equivalent global form which exposes the missing
hypertranscendental object: one real primitive.

### Centered divisor regulator exactness

Let \(f\) be a nonzero entire function, let \(D_f\) be its zero divisor, put
\[
 U_f=\mathbb C\setminus D_f,
\]
and fix \(c\in\mathbb R\).  Write \(s=x+iy\).  On \(U_f\), the one-form
\[
 d\arg f:=\operatorname{Im}(d\log f)
\]
is globally defined even though \(\arg f\) need not be.  Define the centered divisor regulator
\[
 \boxed{\qquad
 \eta_{f,c}
 :=
 \log|f(s)|\,dy-(x-c)\,d\arg f(s).
 \qquad}                                                     \tag{303}
\]

`[PAPER-PROVED] [CENTERED_DIVISOR_REGULATOR_EXACTNESS]`

The form `(303)` is closed.  If \(\rho\) is a zero of multiplicity \(m_\rho\), then for a
sufficiently small positive loop \(\gamma_\rho\),
\[
 {1\over2\pi}\int_{\gamma_\rho}\eta_{f,c}
 =
 -m_\rho(\operatorname{Re}\rho-c).                         \tag{304}
\]
Consequently the following are equivalent:
\[
\boxed{\quad
 D_f\subset\{s:\operatorname{Re}s=c\}
 \quad\Longleftrightarrow\quad
 [\eta_{f,c}]=0\text{ in }H^1_{\rm dR}(U_f;\mathbb R)
 \quad\Longleftrightarrow\quad
 \exists\Phi_{f,c}:U_f\to\mathbb R,\ d\Phi_{f,c}=\eta_{f,c}.
\quad}                                                       \tag{305}
\]

To prove closedness, choose a local holomorphic logarithm
\[
 \log f=u+i\theta.
\]
The Cauchy--Riemann equations give
\[
 du\wedge dy=dx\wedge d\theta,
\]
hence \(d\eta_{f,c}=0\).  Near \(\rho\),
\[
 \log|f|=m_\rho\log|s-\rho|+O(1),\qquad
 \int_{\gamma_\rho}d\arg f=2\pi m_\rho.
\]
The first term of `(303)` has loop integral
\(O(r|\log r|)\to0\), while the second tends to the right side of `(304)`.

Every singular one-cycle in the complement of a locally finite divisor is compact and homologous
to a finite sum of small divisor loops.  Thus `(304)` proves `(305)` by the real de Rham theorem.
No growth condition at spectral infinity is needed for this ordinary exactness statement; such a
condition becomes essential only for source-effective continuation in the completed arithmetic
category.

This theorem is universal: any vertical-line zero problem is a primitive-effectivity problem for
one centered real regulator.

### Explicit local primitives and their monodromy

On a simply connected \(V\subset U_f\), choose
\[
 L=\log f=u+i\theta
\]
and a holomorphic antiderivative \(F\) with \(F'=L\).  Then
\[
 \boxed{\qquad
 \Phi_V
 =
 \operatorname{Im}F-(x-c)\theta
 \qquad}                                                     \tag{306}
\]
satisfies
\[
 d\Phi_V=\eta_{f,c}.                                        \tag{307}
\]
Indeed
\[
 d\,\operatorname{Im}F=\theta\,dx+u\,dy,
\]
and subtracting \(d((x-c)\theta)\) gives `(303)`.

Changing \(L\) by \(2\pi i k\) changes `(306)` only by a real constant.  Therefore the local
primitives form a canonical affine real local system
\[
 \mathscr{Prim}_{f,c}
 :=
 \{\Phi:d\Phi=\eta_{f,c}\}.                                 \tag{308}
\]
Its monodromy is
\[
 \operatorname{mon}_{\mathscr{Prim}_{f,c}}(\gamma_\rho)
 =
 -2\pi m_\rho(\operatorname{Re}\rho-c).                    \tag{309}
\]
Thus `(305)` says that the divisor is boundary-pure exactly when the centered regulator primitive
torsor has a global section.

This is the precise source-effectivity object which the general HT architecture had left
unnamed.  It is not the entire function, its divisor, a zero-indexed character, or a postulated
Hilbert norm.  It is the torsor of compatible local real primitives of the Hermitian/analytic
tame-symbol mismatch.

### Hermitian--holomorphic parent and the exact correction

Aldrovandi's Hermitian-holomorphic tame-symbol theorem supplies a canonical Hermitian metric on
the Deligne/Heisenberg line of two holomorphic units.  It also separates:

1. the analytic Deligne connection; and
2. the Chern connection of the Hermitian metric.

Their difference is represented, up to the fixed convention for imaginary forms, by Goncharov's
regulator
\[
 r_2(f,g)
 =
 \operatorname{Im}(d\log f)\log|g|
 -
 \log|f|\operatorname{Im}(d\log g).                       \tag{310}
\]
For \(g(s)=e^{s-c}\), `(310)` is \(-\eta_{f,c}\).  Thus the existence of a Hermitian tame-symbol
line is parent mathematics and does **not** imply `(305)`.  The obstruction is the connection
mismatch itself.

Requiring `(310)` to vanish pointwise on \(U_f\) would be much stronger than vertical-line purity
and is generally false.  The correct requirement is only that its real local system have trivial
monodromy, equivalently that `(303)` be exact.  A global primitive changes the Hermitian gauge so
that the flat clock holonomy is unitary supportwise; it need not annihilate the full regulator
field.

This corrects Clause 3 of the preceding conjecture: the frontier is not construction of some
positive metric.  A canonical Hermitian parent exists.  The frontier is source-effective
trivialization of the factorized **analytic--Hermitian connection-difference torsor**.

### Riemann specialization

For the completed Riemann function, set
\[
 \eta_\Xi:=\eta_{\Xi,1/2}
 =
 \log|\Xi|\,d\,\operatorname{Im}s
 -
 (\operatorname{Re}s-\tfrac12)d\arg\Xi.                   \tag{311}
\]
This is exactly the universal field `(273)`.  Equations `(304)` and `(305)` give:
\[
\boxed{\qquad
 \mathrm{RH}
 \quad\Longleftrightarrow\quad
 [\eta_\Xi]=0
 \quad\Longleftrightarrow\quad
 \mathscr{Prim}_{\Xi,1/2}(U_\Xi)\ne\varnothing.
\qquad}                                                     \tag{312}
\]
Moreover
\[
 \eta(\Xi,p^{s-1/2})=(\log p)\eta_\Xi,
\]
so all prime clocks are scalar readings of this one torsor.  No all-prime product is required to
define the obstruction.  The all-prime Wold/Kummer/Kakutani completions test whether the same
monodromy can survive their independently forced source topologies.

Equation `(312)` is an exact RH criterion, not yet a proof.  Its advance is to identify one global
geometric object whose effectivity simultaneously implies every local unitarity condition and to
show that this object is the standard Hermitian tame-symbol connection mismatch.

### Safe-half-plane source section

The primitive torsor is already source-effectively pointed where the Euler product converges.
Write
\[
 A(s)
 =
 \frac12s(s-1)\pi^{-s/2}\Gamma(s/2),
 \qquad
 \Xi(s)=A(s)\zeta(s).
\]
Fix a real \(s_0>1\) and the real-positive logarithmic branches there.  On
\(\operatorname{Re}s>1\), define
\[
\begin{aligned}
 F_\Xi^{>}(s)
 &:=
 \int_{s_0}^{s}\log A(w)\,dw\\
 &\quad
 -
 \sum_{n\ge2}
 {\Lambda(n)\over(\log n)^2}
 \bigl(n^{-s}-n^{-s_0}\bigr).                              \tag{313}
\end{aligned}
\]
The series converges normally on every closed sub-half-plane
\(\operatorname{Re}s\ge1+\varepsilon\), and
\[
 {d\over ds}F_\Xi^{>}(s)
 =
 \log A(s)
 +
 \sum_{n\ge2}{\Lambda(n)\over\log n}n^{-s}
 =
 \log\Xi(s).                                               \tag{314}
\]
The Gamma integral in `(313)` is a Barnes-type primitive; the Euler term is the prime-power
dilogarithmic primitive
\[
 -\sum_{p}\sum_{k\ge1}{p^{-ks}\over k^2\log p}
\text{ calibration}.
\]

Hence
\[
 \Phi_\Xi^{>}(s)
 :=
 \operatorname{Im}F_\Xi^{>}(s)
 -
 (\operatorname{Re}s-\tfrac12)\arg\Xi(s)                  \tag{315}
\]
is a canonical source-pointed section of \(\mathscr{Prim}_{\Xi,1/2}\) on the safe Euler
half-plane, with
\[
 d\Phi_\Xi^{>}=\eta_\Xi.                                   \tag{316}
\]
This section is built from prime powers, Gamma completion, and one real calibration before any
zero is selected.

The RH problem is now a continuation problem of a named object:

> continue `(315)` through the completed co-Poisson/Meyer source as one single-valued real
> primitive on \(U_\Xi\), without choosing paths from the zero divisor.

Ordinary analytic continuation only produces the local system `(308)` and permits nonzero
translation constants `(309)`.  The new theorem must show that the source continuation kills
those constants.

### Positive HT shells carry one common regulator class

The publication-ready positive divisor-frame theorem supplies, for every \(m\ge12\),
\[
 S_m^\#(s)=\zeta(s)H_m(s)
\]
on \(\operatorname{Re}s>1/2\), where \(H_m\) is holomorphic and zero-free.  Restrict to the strict
right strip
\[
 \mathcal S^+=\{s:\tfrac12<\operatorname{Re}s<1\}.
\]
The completion factor \(A(s)\) is also holomorphic and zero-free there.  Regulator additivity
gives
\[
 \eta_{S_m^\#,1/2}
 =
 \eta_{\zeta,1/2}+\eta_{H_m,1/2}.                          \tag{317}
\]
Because \(\mathcal S^+\) is simply connected and \(H_m\) is zero-free, \(H_m\) has a global
holomorphic logarithm there.  Formula `(306)` supplies a global primitive for
\(\eta_{H_m,1/2}\).  Likewise the completion factor changes the regulator only by an exact form.
Therefore
\[
\boxed{\qquad
 [\eta_{S_m^\#,1/2}]
 =
 [\eta_{\zeta,1/2}]
 =
 [\eta_{\Xi,1/2}]
 \quad\text{on }\mathcal S^+\setminus D_\Xi
 \qquad(m\ge12).
\qquad}                                                     \tag{318}
\]

`[PAPER-PROVED] [POSITIVE_HT_SHELL_REGULATOR_CLASS_REPLICATION]`

This is what the positive HT divisor frame means at the secondary level:

```text
disjoint positive coefficient sources
  + maximally differentially independent zero-free multipliers
  + one common divisor
  =
infinitely many exact regulator gauges around one identical primitive-torsor obstruction.
```

The transverse \(H_m\) directions are not candidate causes of the zero location: they change the
regulator only by exact potentials.  The nontrivial information is the shared class `(318)`.
Positive fusion and hypertranscendence can coexist with an off-line zero because neither forces
that common class to vanish.  This explains the explicit generalized-prime counterexamples and the
shell theorem in one statement.

It also identifies how the HT theory can matter.  A valid proof must construct a **source-selected
common primitive** compatible with the countably free exact gauges, not derive a finite
differential identity among the shells.  The latter is impossible by their proved maximal
relative differential rank.

### Exact new open core

`[BOLD CONJECTURE] [XI_SOURCE_REGULATOR_PRIMITIVE_DESCENT]`

The safe source section `(315)` extends through the completed ordinary-prime
Euler--Gamma/co-Poisson object to a section
\[
 \Phi_\Xi^{\rm src}\in
 \mathscr{Prim}_{\Xi,1/2}(U_\Xi)                            \tag{319}
\]
such that:

1. it is constructed from the Euler prime-power primitive, Barnes/Gamma primitive, Meyer
   Poisson relation, BV first-trace correction, and source calibration before divisor
   specialization;
2. its local analytic differential is `(311)`;
3. its continuation constants are the factorized tame boundaries `(309)`, and source descent
   proves every such constant zero rather than cancelling reflected pairs;
4. on the right strip it is compatible with all shell gauges in `(317)`--`(318)`;
5. the resulting section is strict under both ordinary-prime enlargement and positive-shell/source
   depth;
6. its Gamma reflection is the same pointed primitive, not an independently renormalized
   reflected copy.

If `(319)` is constructed, `(312)` proves RH immediately.  Conversely, RH makes the ordinary real
primitive torsor trivial, but it does not automatically provide the source formula or strict
comparison required in Clauses 1 and 4--6.  Thus the conjecture contains an RH-equivalent
existence conclusion plus additional source-effectivity content.

The first non-immediate obstacle is now narrower than “construct a Hodge theory”:

\[
\boxed{\quad
\text{prove source path-independence of the explicitly pointed safe-half-plane potential `(315)`.}
\quad}                                                       \tag{320}
\]

Equivalently, extend Meyer's logarithmic Green cocycle to the relative pair and prove that its
real connection-difference class has zero factorized boundary before global trace.  This is the
same open theorem as `(301)`, expressed as primitive descent.

### Hostile audit

1. Every entire function has local primitives `(306)`.  Only source-selected global gluing is
   RH-bearing.
2. Integrating \(\log\Xi\) along a path and declaring that path canonical is circular unless
   source continuation proves path independence.
3. The canonical Hermitian tame-symbol metric does not prove exactness; its analytic/Chern
   mismatch is precisely `(310)`.
4. Pointwise vanishing of `(310)` is unnecessary and generally too strong.  Only monodromy
   vanishing is claimed.
5. The shell equality `(318)` does not force its common class to be zero.  It proves why infinitely
   many positive HT channels can all fail together.
6. Reflection sends the period at \(\rho\) to its negative.  Summing or multiplying before
   factorized localization again produces a false zero.
7. A source potential fitted by dividing by \(\Xi\), enumerating zeros, or selecting branch cuts
   from their locations is rejected.
8. No Lean formalization should begin with `(312)` alone.  The universal theorem `(303)`--`(305)`
   is elementary; the source descent `(319)` is the mathematical frontier.

### Literature boundary

The real regulator form, Deligne tame-symbol torsor, Heisenberg line, Hermitian-holomorphic metric,
and analytic/Chern compatibility obstruction are parent mathematics; see Aldrovandi,
*Hermitian-holomorphic (2)-Gerbes and tame symbols*
(<https://arxiv.org/abs/math/0310027>).  Barnes-type primitives and the absolutely convergent
Euler logarithm are also standard.

The candidate-new exact consequences are the centered divisor-regulator theorem `(303)`--`(305)`
as a universal vertical-line criterion, its source-pointed Riemann potential `(313)`--`(316)`, and
the positive-HT shell regulator-class replication `(318)`.  Their ingredients are elementary or
published parent mathematics; priority is claimed only provisionally for the conjunction and
interpretation.  The proof-producing theorem `(319)` is open.

## 37. The factorized conormal-anomaly index

Sections 35--36 and the earlier prime-Schwartz moderation theorem have one common numerical
invariant.  Making it explicit separates the universal theorem from the source theorem still
needed for RH.

### One local index, five exact realizations

Let \(f\) be a nonzero entire function, let \(\rho\) be a zero of multiplicity \(m_\rho\), fix a
real centre \(c\), and put
\[
 {\cal I}_{f,c}(\rho)
 :=
 m_\rho(\operatorname{Re}\rho-c).                       \tag{321}
\]
This is the **factorized conormal-anomaly index**.  It is retained at \(\rho\), before summing
over the divisor or pairing \(\rho\) with a reflected point.

Fix a clock base \(b>1\).  The determinant tame boundary of
\(\{f,b^{s-c}\}\) is
\[
 \partial_\rho\{f,b^{s-c}\}
 =
 b^{-m_\rho(\rho-c)}.                                   \tag{322}
\]
Its bilateral powers form the explicit record
\[
 R_{\rho,b}(k)
 :=
 b^{-k m_\rho(\rho-c)},
 \qquad k\in\mathbb Z.                                  \tag{323}
\]

`[PAPER-PROVED] [FACTORIZED_CONORMAL_ANOMALY_INDEX_LAW]`

The following quantities are equal readings of `(321)`:
\[
\begin{aligned}
 {1\over2\pi}\int_{\gamma_\rho}\eta_{f,c}
   &=-{\cal I}_{f,c}(\rho),                              \tag{324}\\
 {1\over\log b}\log\left|
   \partial_\rho\{f,b^{s-c}\}\right|
   &=-{\cal I}_{f,c}(\rho),                              \tag{325}\\
 \lim_{k\to+\infty}{1\over k\log b}\log|R_{\rho,b}(k)|
   &=-{\cal I}_{f,c}(\rho),                              \tag{326}\\
 \operatorname{mon}_{\mathscr{Prim}_{f,c}}(\gamma_\rho)
   &=-2\pi{\cal I}_{f,c}(\rho).                          \tag{327}
\end{aligned}
\]
Equations `(324)`, `(325)`, and `(327)` are respectively `(304)`, `(294)`, and `(309)`;
`(326)` is immediate from `(323)`.  Thus de Rham period, Hermitian--analytic connection
mismatch, tame-symbol radial modulus, and bilateral exponential slope are not analogous
obstructions.  They are one indexed local class.

There is a fifth exact realization.  A distribution on the circle has polynomially growing
Fourier coefficients, and every polynomially growing bilateral sequence defines a distribution.
Therefore
\[
\boxed{\quad
 R_{\rho,b}\text{ is the Fourier-coefficient record of a circle distribution}
 \quad\Longleftrightarrow\quad
 {\cal I}_{f,c}(\rho)=0.
\quad}                                                   \tag{328}
\]
Indeed, if \(\operatorname{Re}\rho\ne c\), one of the two directions in `(323)` grows
exponentially.  If \(\operatorname{Re}\rho=c\), the coefficients are bounded.  Multiplicity jets
only multiply `(323)` by polynomials in \(k\), so `(328)` retains every finite multiplicity
grade and does not imply simplicity.

To avoid a category overclaim, `(323)` is called an exponential record here.  Off the line it is
not an ordinary periodic hyperfunction on the fixed real circle: the multiplier
\(z-b^{-m_\rho(\rho-c)}\) is invertible near that circle.  Retaining it requires a moving-annulus
or enhanced exponential/Stokes category.  On the line it descends to an ordinary finite-order
distribution.

### The HT shell rate is the same index

For the Riemann divisor put \(c=1/2\).  The entire high-shell completion graph already constructs
\[
 A_m(s)
 =
 (ms-1)((m+1)s-1)
 \bigl(\zeta(ms)-\zeta((m+1)s)\bigr)
\]
and its functional-equation-odd quotient
\[
 U_m(s)={A_m(s)\over A_m(1-s)}.
\]
Prime-two domination gives
\[
 {U_{m+1}(s)\over U_m(s)}
 \longrightarrow
 2^{1-2s}.                                               \tag{329}
\]
At a zero \(\rho\) of multiplicity \(m_\rho\),
\[
 \boxed{\quad
 \log\left|
 \lim_{m\to\infty}{U_{m+1}(\rho)\over U_m(\rho)}
 \right|
 =
 -{2\log2\over m_\rho}\,
 {\cal I}_{\Xi,1/2}(\rho).
 \quad}                                                  \tag{330}
\]
Thus the cofinal projective boundary of the countably maximal positive HT shell frame is the
multiplicity-normalized version of the same tame-regulator index.  Infinite relative
differential rank lives in the transverse bulk; the entire RH-bearing horizontal information
survives in one rank-one projective boundary slope.

Equation `(330)` explains why more finite differential algebra cannot prove purity.  The
decisive invariant appears only after an infinite shell-depth limit, and every uniformly
invertible zero-free shell gauge leaves it unchanged.

### Ward charge supplies multiplicity, not displacement

The Julia--Euler--Weil index law assigns an off-line quartet of multiplicity \(m_\rho\) the
nonnegative charge
\[
 Q_{\rm Ward}(\rho)=8\pi m_\rho.                         \tag{331}
\]
It is independent of horizontal displacement.  Combining `(324)` and `(331)` recovers that
missing coordinate:
\[
 \operatorname{Re}\rho-c
 =
 -4\,{\displaystyle\int_{\gamma_\rho}\eta_{f,c}
       \over\displaystyle Q_{\rm Ward}(\rho)}.           \tag{332}
\]
Here the Ward charge uses the corresponding reflected quartet, while the regulator loop retains
one oriented local factor.  Formula `(332)` is the exact reason Ward positivity can be fully
realized off line: it records \(m_\rho\), whereas the regulator records
\(m_\rho(\operatorname{Re}\rho-c)\).  Taking charge without the oriented regulator forgets the
coordinate that RH must kill.

### The third completion is now forced

The five representations of `(321)` classify the earlier completion failures:

```text
finite truncation:
  every finite record has finite support and cannot see exponential type;

one-sided Hardy completion:
  retains one off-line half because exponential decay in one direction is allowed;

ambient bilateral L2:
  restores unitary covariance but loses even unit-circle point fibres to continuous spectrum;

circle-distribution rigging:
  retains every unitary point fibre as a generalized eigenvector
  and excludes every nonzero exponential slope;

moving-annulus / enhanced completion:
  retains off-line exponential records but therefore cannot prove purity;

global determinant or reflection pushforward:
  adds opposite local indices and returns zero before either index vanishes.
```

This identifies the “third completion” at the prime-clock boundary:
\[
 {\cal S}(\mathbb Z)
 \subset
 \ell^2(\mathbb Z)
 \subset
 {\cal S}'(\mathbb Z),                                  \tag{333}
\]
factorized over divisor support and tensored with an enhanced Euler/Gamma-time direction.
The anisotropy is essential.  The all-order Mertens/Gamma direction may require an enhanced
object, while each fixed compact prime-angle grade must land in the distributional dual in
`(333)`.

The ambient distribution space in `(333)` is parent mathematics and `(328)` is the already-known
moderation selector.  The new synthesis is the exact index identification
`(324)`--`(330)` with the tame-regulator primitive torsor and the positive HT shell completion
graph.

### Universal law and Riemann source specialization

The corpus now suggests a law broader than a positivity or boundedness assertion.

`[BOLD CONJECTURE] [SOURCE_FACTORIZED_MODERATE_LOCALIZATION_LAW]`

> For a source-minimal self-dual constrained hypertranscendental analytic object, perform
> secondary divisor localization before scalar completion or reflection pushforward.  The
> resulting factorized conormal, with its analytic--Hermitian tame connection, has a
> source-effective continuation--record realization.  In every compact source-clock direction
> that realization lands conservatively and grade by grade in the distributional boundary
> module; enhanced exponential growth is permitted only in the common irregular source-time
> direction.  Source duality acts on this one factorized record rather than on two independently
> renormalized chiral records.

For Xi this asks for one pre-divisor morphism
\[
 {\cal N}^{\rm src}_\Xi
 \longrightarrow
 \prod_{\rho\in D_\Xi}^{\rm fac}
 {\cal S}'(\mathbb Z)_{\rho}                             \tag{334}
\]
with all of the following properties:

1. it is constructed from the ordinary-prime Euler object, Gamma/Barnes completion, Meyer
   co-Poisson quotient, BV first trace, and the distinguished safe-half-plane primitive `(315)`;
2. it is nonzero on every top principal-conormal jet of \(I_\Xi/I_\Xi^2\);
3. prime dilation acts by the bilateral shift and its local determinant boundary is `(322)`;
4. the induced connection-difference torsor is \(\mathscr{Prim}_{\Xi,1/2}\);
5. it is strict under finite-prime and positive-HT-shell enlargement;
6. reflection exchanges the two orientations inside the same distributional record and never
   pushes opposite support factors together first.

If `(334)` exists, `(328)` gives
\[
 {\cal I}_{\Xi,1/2}(\rho)=0
\]
for every nontrivial zero, and RH follows.  Equivalently, `(334)` supplies the source
path-independence required in `(319)` and the factorized polarized base change required in
`(301)`.

This conjecture is not claimed as proved or as weaker than RH in the natural analytic quotient.
Without the source-effective construction, its nonzero specialized distributional landing is
RH-equivalent.  Its value is that it states one pre-specialization universal law whose shadows
are exactly the regulator, shell, Wold, Kummer, Kakutani, and Hausdorff-collapse obstructions.

### Superseding correction to Section 35

Clause 3 of `XI_SOURCE_POLARIZED_TAME_BASE_CHANGE` should not be read as asking for an arbitrary
new positive metric.  Aldrovandi's Hermitian tame-symbol line already supplies the canonical
metric.  The corrected Clauses 3--4 are:

3. identify that canonical factorized Hermitian metric with the literal source polarization,
   without requiring the full nilpotent jet operator to be unitary;
4. prove that the analytic Deligne connection and its Chern connection differ by the
   source-exact primitive `(319)`, equivalently that their determinant holonomy is unitary
   supportwise.

The frontier is the source-effective connection comparison, not metric existence.

### Hostile audit

1. `(321)`--`(330)` identify one obstruction but do not make it vanish.
2. Distributional landing read directly at a chosen zero is exactly the old temperedness
   criterion.  Only a construction of `(334)` before divisor specialization can count as a
   creator theorem.
3. A hyperfunction or enhanced exponential target in every variable is too large: it retains
   `(323)` off the line and has no purity consequence.
4. Plain bilateral \(\ell^2\) is too small: it loses bounded unitary characters and therefore all
   critical-line point fibres.
5. One-sided Hardy continuity is oriented the wrong way; it makes every strict-right shell
   conormal bounded.
6. A global determinant, trace, or reflected product annihilates
   \({\cal I}(\rho)+{\cal I}(1-\overline\rho)\) identically.
7. The canonical Hermitian metric alone does not imply unitary analytic holonomy.  Its
   connection mismatch is exactly `(324)`.
8. Positive HT shell replication does not force distributional descent.  It supplies the actual
   source cofinal record `(329)` whose landing must be proved.
9. Generalized-prime off-line Euler systems falsify every version omitting literal
   ordinary-integer source incidence: their nonzero indices simply remain enhanced exponential
   records.

### Literature and priority boundary

Fourier characterization of circle distributions, moderate/enhanced boundary categories,
Hermitian tame-symbol lines, regulator forms, and conormal determinant characters are parent
mathematics.  The corpus already contained the prime-Schwartz moderation criterion and the
high-shell bipolar rate separately.  Targeted corpus and arXiv searches found no statement
identifying those quantities with the centered tame-regulator primitive-torsor period and the
factorized determinant modulus as one local index.  This is negative collision evidence, not a
priority certificate.  The RH-producing source law `(334)` remains open.

## 38. Cofinal Euler--Gamma boundary dipole and conormal proper base change

The target-side third completion is no longer missing.  The mixed Kummer space, the
prime-valuation Kakutani sector, the source-normal Wold blow-up, and the factorized clock
distribution all exist.  What is missing is a theorem that an operation commutes with that
completion.  The operation is principal-conormal localization.

This changes the interpretation:

```text
the third completion is not one more ambient function space;
it is a completion together with a proper-base-change law for factorized conormals.
```

The failure of that base-change law has a concrete boundary measure.

### Exact two-infinity limit of the finite Kummer regulators

Let \(\mathcal P\) be the rational primes and let
\(\mathcal P^\ast=\mathcal P\sqcup\{\omega_{\rm pr}\}\) be their one-point compactification.
Keep the Arakelov place \(\infty_{\rm ar}\) distinct from the cofinal prime end
\(\omega_{\rm pr}\), and put
\[
 B_{\rm EP}
 =
 \{\infty_{\rm ar}\}\sqcup\mathcal P^\ast .
                                                               \tag{335}
\]
For a finite prime packet \(P\), \(n=|P|\), and a coherent real radial exponent \(c\), the
component-constant Kummer Riesz regulator of Section 3 of
`source-effective-polar-kummer-conormal-purity` is the signed measure
\[
 \nu_{P,c}
 =
 {nc\over n+1}\delta_{\infty_{\rm ar}}
 -
 {c\over n+1}\sum_{p\in P}\delta_p .
                                                               \tag{336}
\]
It has total mass zero and is the measure reading of
\[
 h_{P,c}={c\over n+1}\sum_{p\in P}
 \bigl(1_{Y(\mathbb Q,\infty)}-1_{Y(\mathbb Q,p)}\bigr).
\]

`[PAPER-PROVED] [COFINAL_EULER_GAMMA_BOUNDARY_DIPOLE_LAW]`

As \(P\) runs through the directed set of finite prime packets,
\[
 \boxed{\quad
 \nu_{P,c}
 \stackrel{w^\ast}{\longrightarrow}
 c\bigl(\delta_{\infty_{\rm ar}}-\delta_{\omega_{\rm pr}}\bigr).
 \quad}                                                        \tag{337}
\]
Moreover,
\[
 \|\nu_{P,c}\|_{\rm TV}
 =
 {2n\over n+1}|c|
 \longrightarrow2|c|.                                        \tag{338}
\]

To prove `(337)`, let \(\varphi\in C(B_{\rm EP})\).  Continuity at
\(\omega_{\rm pr}\) says that for every \(\epsilon>0\), all but finitely many primes satisfy
\[
 |\varphi(p)-\varphi(\omega_{\rm pr})|<\epsilon.
\]
The exceptional finite set contributes \(o(1)\) to the packet average, uniformly over the
directed cofinal net.  Hence
\[
 {1\over |P|}\sum_{p\in P}\varphi(p)
 \longrightarrow\varphi(\omega_{\rm pr}),
\]
and substitution in `(336)` proves `(337)`.  Formula `(338)` is immediate because the two
supports in `(336)` are disjoint.

Thus the \(L^2\) limit
\[
 h_{P,c}\longrightarrow c\,1_{Y(\mathbb Q,\infty)}
\]
does not destroy the missing finite-place mass.  It sends it outside the uncompactified
Hilbert receiver.  The compactified weak limit retains the exact oriented dipole between two
different infinities.  The strict mixed \(L^1/L^2\) topology refuses this escape because its
total variation stays \(2|c|\).

### The dipole coefficient is the factorized conormal-anomaly index

For a zero \(\rho\) of \(f\) with multiplicity \(m_\rho\), use the full tame-clock radial
exponent
\[
 c_\rho
 =
 -{\cal I}_{f,c_0}(\rho)
 =
 -m_\rho(\operatorname{Re}\rho-c_0).                         \tag{339}
\]
Then `(337)` becomes
\[
 \Delta_{f,c_0}(\rho)
 :=
 -{\cal I}_{f,c_0}(\rho)
 \bigl(\delta_{\infty_{\rm ar}}-\delta_{\omega_{\rm pr}}\bigr).
                                                               \tag{340}
\]
The boundary dipole vanishes exactly when the regulator period, tame-symbol modulus,
bilateral exponential slope, primitive-torsor monodromy, and HT shell reflection rate in
Section 37 vanish:
\[
 \boxed{\quad
 \Delta_{f,c_0}(\rho)=0
 \quad\Longleftrightarrow\quad
 {\cal I}_{f,c_0}(\rho)=0.
 \quad}                                                        \tag{341}
\]

The Wold--Gamma irregular coordinate is another exact scalar reading.  Put
\(\epsilon_P=\prod_{p\in P}(1-p^{-1})\).  The two reflected Gamma branches with the
multiplicity-weighted parameter \(t_\rho=m_\rho(\rho-c_0)\) obey
\[
 \lim_P{\epsilon_P\over2}
 \log\left|\exp\left(\pm{2t_\rho\over\epsilon_P}\right)\right|
 =
 \pm{\cal I}_{f,c_0}(\rho).                                  \tag{342}
\]
Equation `(342)` does not identify the scalar Gamma parameter with the \(\Xi\) conormal; that
identification remains source-bearing.  It proves that once the source transgression is made,
its Gamma Stokes slope and its Kummer boundary dipole carry the same coefficient.

### The completion--localization fracture square

There are two orders of operation:

```text
finite Euler--Gamma source --principal-conormal localization--> finite Kummer regulators
          |                                                        |
   source-normal cofinal completion                         strict mixed completion
          |                                                        |
completed source section  --principal-conormal localization--> completed conormal
```

On the coherent rank-one radial sector, `(337)`--`(341)` calculate the entire
Beck--Chevalley obstruction of this square:
\[
 \operatorname{BCDef}_\rho
 =
 \Delta_{f,c_0}(\rho).                                      \tag{343}
\]
More explicitly, localization followed by weak cofinal completion produces `(340)`.
Localization followed by strict mixed completion exists exactly when this boundary class is
zero.  Therefore
\[
 \boxed{\quad
 \text{strict factorized conormal base change exists at }\rho
 \quad\Longleftrightarrow\quad
 {\cal I}_{f,c_0}(\rho)=0.
 \quad}                                                        \tag{344}
\]
This is a target theorem, not yet a source theorem.  It neither asserts that the lower
horizontal arrow exists for \(\Xi\) nor obtains it from entire continuation.

### Universal source law suggested by all obstructions

`[BOLD CONJECTURE] [SOURCE_EFFECTIVE_CONORMAL_PROPER_BASE_CHANGE]`

> Let a source-minimal constrained HT analytic object be given with:
>
> 1. a distinguished source-effective section;
> 2. an ordinary-integral prime action and its finite valuation residues;
> 3. a self-dual Gamma/real boundary;
> 4. a source-normal relative character whose regular and singular cofinal increments have
>    finite total variation;
> 5. a factorized analytic/differential \(K_2\) principal conormal, retained before reflection
>    pushforward.
>
> Then source-normal cofinal completion commutes with calibrated principal-conormal
> localization in the strict Deligne--Kummer boundary category.  Equivalently, the
> Beck--Chevalley morphism in `(343)` exists before divisor specialization and is conservative
> on every top conormal jet.

For the Riemann source, Items 1--4 are supplied separately by the pointed
Euler--Gamma/co-Poisson section, the ordinary-prime Wold/BV valuation law, the real Kummer
boundary, and the nested sieve relative character.  Section 36 constructs the local
differential \(K_2\) symbol required in Item 5.  What is not proved is their assembly into the
one proper-base-change morphism.

If the conjecture holds for that assembled source, `(344)` gives
\[
 {\cal I}_{\Xi,1/2}(\rho)=0
 \qquad\text{for every nontrivial zero }\rho,
\]
and therefore RH.

The conjecture says what the corpus was missing at a higher level:

```text
finite arguments see no obstruction because the dipole is supported at the cofinal prime end;

bare Hilbert completion loses one pole of the dipole;

global reflection or determinant pushforward adds the opposite dipole and reports zero;

one-sided Hardy theory admits one orientation of the dipole;

enhanced/Stokes theory retains both nonzero orientations but does not demand descent;

mixed Kummer and Kakutani sectors detect the dipole but do not create the source comparison;

positive HT shells carry the same dipole coefficient to infinite differential depth;

the missing mathematics is proper base change for a source-effective HT conormal across an
infinite arithmetic completion.
```

This is the proposed universal law: purity is not primarily positivity, self-adjointness,
temperedness, or a favorable topology.  Purity is **properness of factorized conormal
localization at source infinity**.  The critical line is the zero-dipole locus of that
properness law.

### New consequences and research reduction

1. **Two infinities are load-bearing.**  Identifying
   \(\infty_{\rm ar}\) and \(\omega_{\rm pr}\) before taking the factorized boundary kills
   `(340)` for every \(c\) and is nonconservative.  A valid completion must retain both faces and
   prove descent between them.
2. **The next theorem is functorial, not spectral.**  It is enough to construct a continuous
   regulator functor from the source-normal relative determinant/\(K_2\) category to the strict
   mixed Kummer category and prove that summable Wold--BV source increments remain summable after
   principal-conormal localization.  This implies the contractive transgression estimate of
   `prime-sieve-wold-gamma-bv-relative-character`.
3. **The law extends beyond \(\Xi\).**  Any self-dual completed Euler object with the same proper
   source comparison has every divisor conormal on its symmetry line.  The conclusion is a
   generalized RH for that object; the difficult hypothesis is the source proper-base-change
   theorem, not the target selector.
4. **Finite HT data cannot decide purity.**  The dipole is zero on every finite-prime
   compactification boundary because \(\omega_{\rm pr}\) is absent.  Maximal finite differential
   rank, all finite jets, and every finite occupation determinant can therefore agree while
   `(340)` differs.
5. **A proof can now fail at one typed place.**  Either the Riemann principal conormal is not the
   differential \(K_2\) localization of the nested source character, or the regulator fails to
   preserve its summable cofinal variation.  Every other target-side purity test is redundant.

### Hostile audit

1. `(337)`--`(344)` are an exact reinterpretation and reduction, not an RH proof.
2. Declaring the lower horizontal arrow in `(343)` continuous is exactly the missing theorem.
3. Calling an object “proper” because its divisor dipoles vanish is circular.  Properness must be
   proved from the five pre-divisor source clauses in the conjecture.
4. Ordinary proper-base-change theorems do not automatically apply: the source is infinite,
   bornological, singularly normalized by \(\epsilon_P^{-1}\), and carries a first-trace residue.
5. Differential cohomology or a determinant line without the distinguished section and BV
   residue remains divisor-blind.
6. A generalized-prime Euler system may have an analogous target dipole.  It is a falsifier only
   if it also satisfies the literal ordinary-integer source incidence and the same
   source-normal proper-base-change hypotheses.
7. The weak compactification `(337)` retains off-line dipoles; it does not exclude them.  The
   purity conclusion comes only from source-effective strict descent.
8. No Lean formalization of the elementary compactification theorem should be prioritized until
   the source proper-base-change morphism is constructed.  Formalizing another selector would be
   theatre.

### Literature boundary

One-point compactification and weak convergence of escaping empirical measures, Kakutani product
sector theory, proper base change, determinant-line gluing, differential characters, and tame
regulators are parent mathematics.  Dai--Freed's determinant-line gluing and variation theorem
and Aldrovandi's Hermitian tame-symbol construction are relevant parent structures, but neither
supplies the infinite ordinary-prime source-normal comparison in `(343)`.  Targeted corpus and
arXiv searches found no theorem identifying the two-infinity dipole `(340)` simultaneously with
the Riemann tame-regulator index, Wold--Gamma Stokes slope, HT shell reflection rate, and failure
of strict principal-conormal base change.  This is provisional noncollision evidence only.  The
source law remains conjectural.

## 39. Normalization-amplification no-go and the nearby-cycle correction

Section 38 still permits a dangerous weakening.  Ordinary continuity of a regulator on the
coarse source completion cannot prove purity, even if the unnormalized source increments have
finite total variation.  The conormal lives in the normal cone of a class which vanishes at the
coarse endpoint.  The regulator must commute with that normal-cone specialization.

### Coarse continuity erases every radial exponent

Let
\[
 a_P=\prod_{p\in P}(1-p^{-1}),
 \qquad
 \xi_P=J(E_Pp_a)=a_PJ(p_a),                              \tag{345}
\]
and let
\[
 \eta_P=a_P^{-1}\xi_P=J(p_a)                             \tag{346}
\]
be the paper-proved source-normal Rees section.  At a coherent radial exponent \(c\), the finite
mixed-Kummer representative is \(h_{P,c}\) from `(336)`.  An additive regulator compatible with
the scalar source coefficient in `(345)` necessarily has the coarse radial shadow
\[
 \operatorname{Reg}^{\rm coarse}_P(\xi_P)
 =
 a_Ph_{P,c}.                                             \tag{347}
\]
The exact finite norms give
\[
 \|a_Ph_{P,c}\|_1
 =
 {2|P|\over |P|+1}|c|a_P
 \longrightarrow0,
\qquad
 \|a_Ph_{P,c}\|_2
 \le |c|a_P
 \longrightarrow0.                                      \tag{348}
\]
Thus the unnormalized regulator is strongly continuous at the coarse endpoint for every
\(c\), including every off-critical \(c\ne0\).  Ordinary completion sees only zero.

After source-normal blow-up,
\[
 a_P^{-1}\operatorname{Reg}^{\rm coarse}_P(\xi_P)
 =
 h_{P,c}.                                                \tag{349}
\]
For nested packets \(P_n\subset P_m\), \(|P_j|=j\), the exact transition law is
\[
 \|h_{P_m,c}-h_{P_n,c}\|_1
 =
 2|c|{m-n\over m+1}.                                     \tag{350}
\]
Hence the normalized target family is strict mixed-Cauchy exactly when \(c=0\).

`[PAPER-PROVED] [COARSE_CONTINUITY_NORMAL_CONE_FRACTURE]`

\[
\boxed{
\begin{aligned}
 a_Ph_{P,c}&\longrightarrow0
 &&\text{strictly for every }c,\\
 (h_{P,c})_P&\text{ is strict mixed-Cauchy}
 &&\Longleftrightarrow c=0.
\end{aligned}}
                                                               \tag{351}
\]

This is the exact normalization amplification which defeated earlier Hilbert, determinant, and
bounded-regulator arguments.  A map may be perfectly continuous before blow-up and completely
non-strict on the retained conormal direction.

### The correct universal law is a nearby-cycle theorem

The degeneration \(a_P\to0\), together with `(345)`--`(346)`, is a cofinal Rees deformation:
the coarse endpoint kills \(\xi_P\), while its source-normal associated-graded class is the
nonzero principal conormal \(\eta\).  In geometric language, \(\eta\) is a nearby/vanishing-cycle
direction of the nested arithmetic sieve.

Therefore `SOURCE_EFFECTIVE_CONORMAL_PROPER_BASE_CHANGE` from Section 38 must be read in the
following stronger form.

`[BOLD CONJECTURE] [SOURCE_EFFECTIVE_REES_CONORMAL_NEARBY_CYCLE_BASE_CHANGE]`

> The completed ordinary-prime Euler--Gamma/co-Poisson source carries a pointed,
> residue-corrected differential determinant/\(K_2\) character over the cofinal Rees parameter
> \(a_P\).  Its strict Deligne--Kummer regulator:
>
> 1. is constructed on the unnormalized source character before divisor specialization;
> 2. extends to the source-normal deformation to the cone at \(a_P=0\);
> 3. commutes with principal-conormal localization and source reflection on the associated
>    graded/nearby-cycle object;
> 4. is strict, presentation-independent, and conservative on every top principal-conormal jet.

The order of operations is load-bearing:

```text
source character
  -> regulator on the Rees deformation
  -> source-normal nearby cycle
  -> factorized divisor localization
  -> strict mixed boundary
```

Taking the coarse endpoint before the nearby cycle gives `(348)` and loses all horizontal
information.  Normalizing an already scalarized determinant gives `(349)` without strictness.
Only a regulator constructed on the Rees deformation can compare the retained source conormal
with the two-infinity dipole.

For a Riemann zero, use
\[
 c=-{\cal I}_{\Xi,1/2}(\rho)
\]
in the multiplicity-retaining tame normalization.  Clauses 2--4 make the normalized family in
`(349)` a strict mixed nearby cycle.  Equation `(351)` then forces
\[
 {\cal I}_{\Xi,1/2}(\rho)=0.
\]
Thus the conjecture proves RH.

### What this corrects

1. Finite total variation of the Wold--BV source character does not by itself control the
   normalized conormal.  Division by \(a_P\) is singular.
2. A continuous regulator on the coarse determinant line is insufficient.  It maps every
   coherent radial class to zero at the endpoint.
3. A regulator defined only after blow-up can be target-fed.  The Rees extension before
   specialization is the non-circular content.
4. The third completion is therefore a **deformation-to-the-normal-cone package with strict
   nearby-cycle base change**, not a bare test-function space.
5. The first genuinely new construction target is now exact: build the finite-packet
   residue-corrected regulator on \((a_P,\xi_P)\), prove its prime-enlargement cocycle is a
   morphism of Rees objects, and show the induced associated-graded map lands in the mixed
   Kummer boundary without losing the BV principal conormal.

### Universal meaning

The corpus obstructions are shadows of failure to commute three nonexact operations:

```text
infinite source completion;
normal-cone/nearby-cycle specialization;
factorized divisor localization.
```

Reflection adds a fourth operation which reverses the resulting dipole.  Performing reflection
or scalar completion first makes the anomaly disappear.  Performing localization first retains
an off-line exponential record but does not prove it descends.  The sought law says that a
source-effective HT object admits one joint order-independent realization of all four
operations.  In its coherent radial rank-one sector, the obstruction to that order independence
is exactly \({\cal I}_{f,c_0}(\rho)\).

This is sharper than “zeros should be spectral” or “the completion should be unitary.”  It says:

> **critical-line purity is strict nearby-cycle properness of the factorized source conormal.**

### Hostile audit

1. The nearby-cycle conjecture is unproved and remains RH-strength for the Riemann source.
2. The word “Rees” does not solve the problem: `(345)`--`(346)` construct the algebraic normal
   direction, while strictness of its Hermitian regulator is the open analytic theorem.
3. Standard algebraic nearby-cycle proper base change cannot be cited directly.  The parameter
   is a cofinal arithmetic net, the normalization is singular, and the target is bornological.
4. If the differential determinant character is constructed only from \(\det_2\), it omits the
   degree-one first trace which defines \(a_P\) and cannot recover `(346)`.
5. If the associated-graded regulator is defined by prescribing \(h_{P,c}\) at a chosen zero,
   the construction is circular.
6. The conjecture must be tested first on a non-RH HT model with a genuine source-normal
   degeneration.  Failure there would kill universality before any Riemann claim.

## 40. Corpus collision correction

The normalization-amplification mechanism in Section 39 is not new to the corpus.
`prime-valuation-conditioning-normalization-amplification-no-go` already proves the stronger
exact total-variation identities
\[
 d_{\rm TV}(\nu_P,\nu_{P\cup\{p\}})=p^{-1},
 \qquad
 d_{\rm TV}(\nu_P,\delta_{\mathbf0})=1,
\]
and already concludes that a Rees/mapping-cone/local-cohomology boundary is required.
`polarized-critical-rees-corona-transgression-rh` constructs the same general Rees-corona
architecture, while `source-effective-boundary-complexity-conservation-law` already formulates
the producer--reporter Beck--Chevalley cone and identifies completion curvature as the missing
comparison object.

Accordingly:

1. `(345)`--`(351)` are a Kummer-regulator restatement of an existing corpus no-go, not a novelty
   claim.
2. `SOURCE_EFFECTIVE_REES_CONORMAL_NEARBY_CYCLE_BASE_CHANGE` is a sharpening of the existing
   Rees-corona/completion-curvature program to the factorized tame-regulator target, not an
   independent route.
3. The exact positive survivor new to this card is `(337)`--`(342)`: the compactified
   two-infinity dipole and its coefficientwise identification with the factorized
   conormal-anomaly index and the candidate Gamma Stokes slope.
4. The live frontier remains the one already isolated by the recent corpus: identify the
   projective producer--reporter Weyl comparison with the additive Poisson/Tate intertwiner, then
   land the pre-divisor \(\Xi\) conormal conservatively in the resulting strict graph.

This collision strengthens rather than weakens the interpretation.  Independent regulator,
Rees-corona, Hellinger, projective-Weyl, and HT-boundary analyses have converged to the same typed
missing morphism.

## 41. Local Tate--Julia seam factorization

The first part of the remaining projective-Weyl/Poisson comparison is local and exact.  It is
classical after the correct half-density coordinate is exposed.

For a rational prime \(p\), put
\[
 q=p^{-1/2},
 \qquad
 z=p^{\,s-1/2}.                                         \tag{352}
\]
The normalized finite-place Fourier/Tate multiplier is
\[
 U_p(s)
 =
 {1-p^{-(1-s)}\over1-p^{-s}}
 =
 {1-qz\over1-qz^{-1}}.                                  \tag{353}
\]
Connes--Consani recall that the additive Fourier transform, after passage to the multiplicative
spectral coordinate, is inversion followed by multiplication by this ratio of local
\(L\)-factors.

Now form the scalar half-density Julia colligation
\[
 {\mathcal J}_q
 =
 \begin{pmatrix}
 q&\sqrt{1-q^2}\\
 \sqrt{1-q^2}&-q
 \end{pmatrix}.                                         \tag{354}
\]
It is a real orthogonal involution.  With the first coordinate as state and the second as
input/output, its transfer function is
\[
\begin{aligned}
 \Theta_q(z)
 &=
 -q+
 z(1-q^2)(1-qz)^{-1}\\
 &=
 {z-q\over1-qz}.                                       \tag{355}
\end{aligned}
\]
This is the scalar Blaschke factor of the source half-density contraction \(q=p^{-1/2}\).

`[PAPER-PROVED] [LOCAL_TATE_JULIA_CLOCK_SEAM]`

Equations `(353)`--`(355)` give the exact factorization
\[
 \boxed{\quad
 U_p(s)\,\Theta_{p^{-1/2}}\!\left(p^{s-1/2}\right)
 =
 p^{s-1/2}.
 \quad}                                                  \tag{356}
\]

The proof is one cancellation:
\[
 {1-qz\over1-qz^{-1}}\,
 {z-q\over1-qz}
 =
 z.
\]
Reflection is equally exact:
\[
 U_p(1-s)=U_p(s)^{-1},
 \qquad
 \Theta_q(z^{-1})=\Theta_q(z)^{-1}.                     \tag{357}
\]

### Meaning

The local additive and multiplicative polarizations are not supposed to agree.  Their
source-normalized comparison leaves precisely the centered prime clock:

```text
additive Fourier/Tate Weyl multiplier
  x half-density Julia scattering factor
  = centered multiplicative clock.
```

This is the local seam/Bianchi identity which the broader completion-curvature language had not
written explicitly.  On the critical line, \(|z|=1\), and all three factors in `(356)` are
unitary.  Off the line, the residual clock has radial modulus
\[
 \log|z|
 =
 (\operatorname{Re}s-\tfrac12)\log p.                   \tag{358}
\]
For a divisor point of multiplicity \(m_\rho\), the top conormal clock is \(z^{m_\rho}\), so
\[
 {1\over\log p}\log|z^{m_\rho}|
 =
 {\cal I}_{\Xi,1/2}(\rho).                              \tag{359}
\]
Thus the factorized conormal-anomaly index is exactly the radial part of the local
Poisson-versus-Euler seam, not an external critical-line coordinate.

The parameter \(q=p^{-1/2}\) is source-forced in three already-proved ways:

1. it is the square root of the critical squarefree odds \(p^{-1}\);
2. it is the half-density of one Bruhat--Tits radial edge;
3. its square is the magnitude of the transverse projective producer--reporter overlap
   \(-p^{-1}\).

The colligation `(354)` is the minimal conservative dilation of that scalar half-density
contraction.  What is not yet proved is that the full projective boundary Weyl correspondence,
including its complementary record and Möbius phase, reduces to this minimal colligation in a
way compatible with all prime-power cylinders and the additive Schwartz--Bruhat carrier.

### Consequences for the next construction

Equation `(356)` narrows the adelic comparison problem.

1. The local comparison map must not annihilate its defect.  It must output the clock
   \(z=p^{s-1/2}\).
2. The ordinary-prime restricted product must retain the collection of these local clock defects
   as one factorized conormal record.  Taking their scalar product is undefined or cancels after
   reflection.
3. The compact prime-angle direction may retain the record only distributionally.  Polynomial
   bilateral growth of \(z^{m_\rho k}\) forces `(359)` to vanish.
4. Gamma supplies the archimedean factor of the Fourier/Tate multiplier; the two-infinity dipole
   `(340)` is the real boundary of the same clock seam after cofinal completion.
5. The remaining source theorem is no longer an unspecified equality between projective Weyl and
   Poisson Fourier.  It is a strict global lift of the local factorization `(356)`, conservative
   on the Meyer/BV principal conormal and its multiplicity jets.

### Hostile audit

1. The local \(L\)-factor ratio, Julia colligation, Blaschke transfer function, and algebraic
   identity `(356)` are parent mathematics.  Novelty can lie only in their source-geometric
   conjunction with the projective-prime comparison and conormal index.
2. `(356)` is not RH.  It calculates the residual clock but does not prove that a \(\Xi\)
   conormal is a finite-order record of the strict global comparison.
3. A scalar colligation is not the full \(\mathbb P^1(\mathbb Q_p)\) boundary representation.
   The prime-power cylinder filtration, complementary record, Möbius determinant torsor, and
   regular dyadic tower remain to be attached.
4. Infinite tensoring of the scalar transfer functions is not licensed.  The restricted adelic
   object must be constructed at correspondence level before applying any state or determinant.
5. On an enhanced/Stokes target, off-unit \(z\) remains admissible.  The source theorem must land
   compact prime-clock directions in a finite-order distributional boundary.

### Literature boundary

Connes--Consani, *The Scaling Hamiltonian* (arXiv:1910.14368), Lemma 2.3 and Section 4, give the
additive-Fourier decomposition into multiplicative inversion and the product of local
\(L\)-factor ratios.  Conservative Julia colligations and scalar Blaschke transfer functions are
classical operator-model theory.  Targeted corpus and arXiv searches found no statement of
`(356)` as the local seam between the projective-prime half-density comparison and the
factorized Riemann conormal anomaly.  This is negative collision evidence only.

## 42. Transverse metaplectic square root and the all-prime phase obstruction

There is a nontrivial projective--Julia bridge, but it is not the unitary equivalence of two
rank-one reflections.  That equivalence exists for every reflection and would insert
\(p^{-1/2}\) only through an arbitrary basis choice.  The source-marked bridge instead starts
from the negative transverse Gram coefficient.

Put \(q=p^{-1/2}\).  The projective producer and reporter transverse unit vectors satisfy
\[
 \langle v_{\infty,p},v_{0,p}\rangle=-q^2,
 \qquad
 w_pv_{\infty,p}=v_{0,p},
 \qquad
 w_pv_{0,p}=v_{\infty,p}.                               \tag{360}
\]
Let \({\cal S}_p\) be the two-dimensional Hermitian space generated by unit vectors \(a_p,b_p\)
with
\[
 \langle a_p,b_p\rangle=q.                              \tag{361}
\]
Since \(0<q<1\), this Gram matrix is positive definite.  Define
\[
 M_pa_p=i\,b_p,\qquad M_pb_p=i\,a_p.                    \tag{362}
\]
The equality of the Gram matrices before and after `(362)` proves that \(M_p\) is unitary, and
\[
 M_p^2=-1.                                              \tag{363}
\]
In the symmetric square put
\[
 A_p=a_p^{\odot2},\qquad B_p=-b_p^{\odot2}.             \tag{364}
\]
Then
\[
 \langle A_p,B_p\rangle=-q^2,
 \qquad
 \operatorname{Sym}^2(M_p)A_p=B_p,
 \qquad
 \operatorname{Sym}^2(M_p)B_p=A_p.                     \tag{365}
\]
Consequently the marked isometry
\[
 A_p\longmapsto v_{\infty,p},\qquad
 B_p\longmapsto v_{0,p}                                \tag{366}
\]
intertwines the symmetric-square spin lift with projective Weyl on the two transverse source
lines.

`[PAPER-PROVED] [TRANSVERSE_PROJECTIVE_WEYL_METAPLECTIC_LIFT]`

Equations `(360)`--`(366)` prove:

> The negative projective overlap \(-p^{-1}\) is the signed symmetric square of the positive
> source half-density overlap \(p^{-1/2}\).  Its source-faithful square root is an order-four
> unitary, not an involution.

The phase in `(362)` is forced up to sign.  Indeed, without an \(i\)-phase, a pure square cannot
map to the negative pure square in `(364)`.  This gives an exact local meeting of four corpus
features:

```text
projective transverse overlap  -p^(-1);
Tate--Julia source coordinate   p^(-1/2);
metaplectic/quaternionic lift   M_p^2=-1;
projective Weyl shadow          Sym^2(M_p)^2=1.
```

The lift exposes a new obstruction at infinity.  Its normalized symmetric spin vacuum is
\[
 r_p^+={a_p+b_p\over\sqrt{2(1+q)}},
 \qquad
 M_pr_p^+=i\,r_p^+.                                     \tag{367}
\]
For a finite prime packet \(P\),
\[
 M_P:=\bigotimes_{p\in P}M_p,\qquad
 r_P^+:=\bigotimes_{p\in P}r_p^+,
 \qquad
 M_Pr_P^+=i^{|P|}r_P^+.                                 \tag{368}
\]
The phase net \(i^{|P|}\) has no limit over the directed set of finite prime packets: adjoining
one new prime changes it by the fixed factor \(i\).  Replacing \(M_p\) by a phase
\(\lambda_pM_p\) still covers the marked projective Weyl swap in `(365)` only if
\(\lambda_p^2=1\).  Its vacuum coefficient is then still \(\pm i\), so it cannot approach one.
Rephasing by \(-i\) fixes the vacuum, but
\[
 \operatorname{Sym}^2((-i)M_p)
 =
 -\operatorname{Sym}^2(M_p),                            \tag{369}
\]
and therefore changes the marked projective Weyl lift by its central sign.

`[PAPER-PROVED] [ALL_PRIME_METAPLECTIC_VACUUM_PHASE_OBSTRUCTION]`

Thus the honest all-prime projective Weyl unitary can exist while no source-faithful choice of
its marked half-density lifts has an ordinary incomplete tensor product on the spin vacuum.
The missing all-prime lift is necessarily central-extension-valued: a phase torsor,
metaplectic line, or equivalent \(2\)-descent object must be retained before scalarization.

### Hostile audit

1. The Gram-plane construction is elementary spin/symmetric-square linear algebra.  Candidate
   new content is only its exact source conjunction with the projective-prime overlap,
   Tate--Julia coordinate, and all-prime vacuum obstruction.
2. `(366)` covers the producer/reporter transverse pair, not the full three-dimensional
   continuation--record cyclic space.  The complementary symmetric-square line has different
   eigenvalue bookkeeping and must not be silently identified with the projective common line.
3. A central phase torsor does not force its radial character to be unitary.  The theorem
   identifies the correct category of the missing lift; it does not prove critical-line purity.
4. The earlier metaplectic/Steinberg corpus conjectures anticipated a square-root coefficient
   extension.  Equations `(360)`--`(369)` add a source-marked local realization and a precise
   all-prime tensor obstruction; they do not construct the global Steinberg descent.

## 43. The polarization \(2\)-curvature law

The strongest HTGeometry input changes the type of the sought completion.  Multiple-elliptic-
Gamma mixed-constraint classes are:

1. detected on rank-two faces;
2. glued by rank-three compatibility;
3. noncompressible to any proper collection of pair faces.

HT status itself is not completion-stable, so it cannot be the line selector.  The structural
survivor is instead the complete pair-face nerve.  Tame symbols, Steinberg \(K_2\), determinant
torsors, the metaplectic phase obstruction `(368)`, and producer--reporter comparison all live
naturally one categorical level above a scalar Hilbert completion.

This suggests that the three source polarizations should be organized as
\[
 {\sf E}=\text{multiplicative Euler},\qquad
 {\sf P}=\text{additive Poisson},\qquad
 {\sf G}=\text{archimedean Gamma}.                       \tag{370}
\]
The three pair faces carry conservative continuation--record correspondences
\[
 {\cal C}_{{\sf E}{\sf P}},\qquad
 {\cal C}_{{\sf P}{\sf G}},\qquad
 {\cal C}_{{\sf G}{\sf E}},                             \tag{371}
\]
and their triple compatibility is the chain-level Poisson/Tate/product-formula
\(2\)-isomorphism.  For a divisor conormal at \(\rho\), the local seam `(356)` leaves the
factorized clock holonomy
\[
 h_{p,\rho}
 =
 p^{\,m_\rho(\rho-1/2)}.                                \tag{372}
\]
Its normalized real \(2\)-curvature is
\[
 \kappa_{p,\rho}
 :=
 {1\over\log p}\log|h_{p,\rho}|
 =
 m_\rho(\operatorname{Re}\rho-\tfrac12)
 =
 {\cal I}_{\Xi,1/2}(\rho).                              \tag{373}
\]
The right side is independent of \(p\).  The Kummer two-infinity dipole, tame-regulator period,
Wold--Gamma Stokes slope, bilateral clock growth, projective leakage, and Julia residual are
therefore scalar shadows of one candidate real \(2\)-curvature.

`[BOLD CONJECTURE] [SOURCE_PRINCIPAL_POLARIZATION_2_CURVATURE_UNITARY_REDUCTION]`

> The completed Riemann source admits a source-fixed Hermitian continuation--record
> \(2\)-descent field on the complete pair-face nerve `(370)`--`(371)`, constructed before
> divisor localization from the additive Schwartz--Bruhat Poisson carrier, the multiplicative
> Euler/projective carrier, and the Gamma/metaplectic carrier.  Strict source-normal
> factorized-conormal localization preserves its triple \(2\)-isomorphism and multiplicity
> filtration.  Every principal \(\Xi\)-conormal then has a unitary reduction in this fixed
> Hermitian \(2\)-descent field.  Equivalently, its real \(2\)-curvature `(373)` vanishes
> supportwise.

This is a conjecture in the strong sense: current evidence gives a hunch that it is true, while
no proof of the unitary-reduction clause is known.  The clause must be derived from the
source-first triple comparison; it may not be imposed as a topology selected after the zero is
known.

### Conditional purity theorem

If the conjecture holds, RH follows immediately.  Unitary reduction gives
\[
 |h_{p,\rho}|=1.
\]
Using `(372)`, any single prime gives
\[
 0=\log|h_{p,\rho}|
  =m_\rho(\operatorname{Re}\rho-\tfrac12)\log p.
\]
Since \(m_\rho>0\) and \(\log p>0\),
\[
 \operatorname{Re}\rho=\frac12.                         \tag{374}
\]
This deduction is elementary; all RH-strength lies in constructing the source-fixed
\(2\)-descent field and proving unitary reduction after strict factorized localization.

### Why this subsumes the obstruction corpus

```text
finite Hilbert truncation
  = one face retained, complementary record deleted;

projective all-prime Weyl
  = projective shadow exists, metaplectic 2-phase omitted;

Kummer mixed completion
  = real regulator face retained, triple descent not constructed;

Rees / Beck--Chevalley fracture
  = conormal localization fails to commute with 2-descent;

HT pair noncompression
  = no proper face subcollection can carry the complete source;

off-line generalized Euler systems
  = Euler/Gamma target data exist, but no source-chain additive Poisson triple lift is supplied;

critical-line purity
  = principal conormal 2-holonomy admits source-fixed unitary reduction.
```

The proposed “third completion” is therefore not primarily a third normed space.  It is a
Hausdorff Hermitian \(2\)-descent completion whose objects are source polarizations, whose
pairwise \(1\)-morphisms retain continuation plus record, and whose \(2\)-morphisms retain the
Steinberg/metaplectic phase and factorized conormal curvature.

### Exact proof obligations

1. Construct `(371)` on one common source Schwartz--Bruhat/prime-power cylinder category, with
   the already-proved prime-square Fourier/projective Weyl equivalence as its finite shadow.
2. Lift `(360)`--`(369)` to the universal Steinberg extension; derive the global central-phase
   cancellation from Poisson summation and the archimedean Weil/Gamma factor.
3. Prove the resulting triple comparison is Hermitian and source-fixed, rather than unitarized
   separately for each spectral parameter.
4. Construct strict Rees/nearby-cycle localization of this \(2\)-descent field and prove that the
   full \(\Xi\) principal conormal and all multiplicity jets land conservatively.
5. Derive unitary reduction of a principal conormal from those chain-level source properties.
   This is the first genuinely RH-strength theorem and must survive the explicit off-line
   generalized-Euler countermodels.
6. Only after Items 1--5 are dependency-closed should `(373)`--`(374)` be formalized as the final
   Lean selector.

### Two false shortcuts ruled out

1. **Ordinary adelic restrictedness.**  The quasicharacter
   \(|\cdot|^{c+it}\) is unramified and defines a restricted idele-class character for every
   real \(c\).  Restricted tensor products do not force unitary Satake parameters.  Replacing
   the coefficient group by a restricted product relative to \(U(1)\) would assume the desired
   temperedness.
2. **Abstract gerbe language.**  A flat complex gerbe may have nonunitary holonomy.  Merely
   renaming the completion a \(2\)-descent field proves nothing.  Frontier content is the
   source-derived Hermitian unitary-reduction theorem in Item 5.

### Literature and corpus boundary

Metaplectic covers, Weil representations, Steinberg symbols, \(K_2\)-central extensions,
Hermitian tame-symbol lines, gerbes, and adelic Poisson splitting are parent mathematics.  The
corpus already conjectured metaplectic--Steinberg coefficient descent and independently proved
HT pair localization/triple gluing/noncompression.  Targeted corpus and arXiv searches found no
source asserting the conjunction `(370)`--`(373)` or its principal-conormal unitary-reduction
law.  This is negative collision evidence, not a priority claim.

The supplied arXiv identifier `1707.06610` is *Quark matter may not be strange* and contains no
Riemann, hypertranscendence, Poisson, or tame-regulator input for this route.

## 44. Correction: curvature is a reporter, not the producer

The hostile audit of Section 43 changes the logical order.  A Hermitian \(2\)-descent field can
have nonunitary radial holonomy, and requiring its principal conormals to have unitary reduction
is exactly the desired conclusion.  Thus the curvature formula
\[
 \kappa_{p,\rho}=m_\rho(\operatorname {Re}\rho-\tfrac12)                 \tag{375}
\]
is an exact reporter, but the unitary-reduction clause of the conjecture in Section 43 is not yet
a source theorem.

The corpus gives a more precise diagnosis.  It repeatedly constructs unconditional positivity on
one fibre:

```text
absolute-Euler Carathéodory kernels;
moving theta hyperbolic carriers;
all-prime Sonin positive master effects;
finite von Mangoldt--Gamma joint Grams;
positive projective Julia defect channels.
```

None supplies the cross-fibre identification required when aperture, Gamma depth, prime cutoff, or
polarization changes.  The failures are all losses of cross terms:

```text
finite truncation                 loses prime-dilation covariance;
ambient infinite L2              loses divisor evaluation fibres;
freezing the theta carrier       deletes the replicator covariance;
factorial trace normalization    replaces a Gram by an unoriented Beta cross-pairing;
scalarizing metaplectic lifts    loses the all-prime phase record;
positive Sonin replica moments   leave their Bernstein mismatch with the Xi source uncontrolled.
```

This suggests a sharper universal principle:

> Fibrewise positivity is not the missing law.  The missing law is complete positivity of the
> source comparison *between every pair of fibres*, coherent under triple composition.

The complete pair-face nerve from HTGeometry is then not decorative categorical language.  It is
the natural domain of a two-parameter positive kernel.  Rank-three compatibility is the
composition law for the pairwise transports.  The scalar curvature `(375)` is what remains after
that coherent comparison is localized at a divisor and scalarized.

`[CORRECTION]` The source-first order must therefore be

```text
pairwise source Gram + triple coherence
  -> one positive resolvent cocycle
  -> fixed Markov/Thorin carrier
  -> unitary principal-conormal holonomy
  -> curvature (375) vanishes
  -> RH.
```

It may not begin by postulating the fourth line.

## 45. Exact covariant calculus of the moving theta carrier

The theta boundary source makes the missing coherence explicit.  Put \(q=t^2\), let
\[
 p_q(x)\,dx={2\cosh(\sqrt q\,x)\Phi(x)\over Z(\sqrt q)}\,dx,\qquad
 K_q(x)={x\tanh(\sqrt q\,x)\over\sqrt q},\qquad
 F(q)=\mathbb E_qK_q.                                    \tag{376}
\]
Here \(\Phi\) is the positive theta-cusp source on the positive half-line.  The formalized
hyperbolic source law identifies \(F(q)\) with the genuine inward Cassini response.

Direct differentiation gives
\[
 \partial_q\log p_q(x)={K_q(x)-F(q)\over2}.               \tag{377}
\]
For every differentiable observable \(f_q\) for which differentiation under the integral is
valid,
\[
 {d\over dq}\mathbb E_qf_q
 =
 \mathbb E_q(\partial_qf_q)
 +{1\over2}\operatorname {Cov}_q(f_q,K_q).                \tag{378}
\]
This is the exact replicator connection already visible at first order.

There is also a canonical spatial transport form.  Define the theta Stein kernel
\[
 \tau_q(x)
 =
 {1\over p_q(x)}
 \int_x^\infty\bigl(K_q(y)-F(q)\bigr)p_q(y)\,dy.           \tag{379}
\]
Since \(K_q\) is increasing in \(x\), the centered tail integral in `(379)` is nonnegative.
Moreover,
\[
 \partial_x(\tau_qp_q)=-(K_q-F(q))p_q,\qquad
 \partial_qp_q=-{1\over2}\partial_x(\tau_qp_q).            \tag{380}
\]
Thus \(v_q=\tau_q/2\) is a positive velocity for the continuity equation.  Integration by parts
in `(378)` gives the covariant expectation law
\[
 {d\over dq}\mathbb E_qf_q
 =
 \mathbb E_q\!\left[(\partial_q+v_q\partial_x)f_q\right]. \tag{381}
\]
Writing \(\nabla_q=\partial_q+v_q\partial_x\), one obtains recursively
\[
 F^{(n)}(q)=\mathbb E_q\!\left[\nabla_q^{\,n}K_q\right].   \tag{382}
\]

`[PAPER-PROVED] [EXACT_THETA_COVARIANT_TRANSPORT_BRIDGE]`

Equations `(377)`--`(382)` follow from the positive source law, monotonicity of \(K_q\), and the
theta decay already established in the corpus.  The generic continuity-equation/Stein-transport
mechanism is parent mathematics and is not claimed as new.  Its exact role here is diagnostic:
ordinary derivatives inspect a moving fibre, whereas the RH-bearing signs are covariant
derivatives of the transported observable.

The fixed-carrier target has an equally exact local dictionary.  If
\[
 F(q)=\int_{[0,B]}{d\nu(y)\over1+qy},                     \tag{383}
\]
then at any \(q_0\ge0\)
\[
 {(-1)^n\over n!}F^{(n)}(q_0)
 =
 \int_{[0,B]}
 \left({y\over1+q_0y}\right)^n{d\nu(y)\over1+q_0y}.       \tag{384}
\]
Consequently the full covariant jet in `(382)`, after alternating factorial normalization, must
be one Hausdorff moment sequence on
\[
 \left[0,{B\over1+q_0B}\right].                          \tag{385}
\]
Conversely, compact Hausdorff determinacy and analyticity recover the local germ `(383)` from
`(384)`.  The remaining source theorem is therefore not an unspecified inequality: it is the
simultaneous Hausdorff hierarchy for the covariant theta observables
\(\nabla_q^{\,n}K_q\), with one compatible measure.

There is a cross-aperture form that exposes the pair-face geometry.  A representation `(383)`
gives two positive kernels
\[
 {\mathsf A}_F(q,r)
 =
 {F(q)-F(r)\over r-q}
 =
 \int {y\,d\nu(y)\over(1+qy)(1+ry)},                     \tag{386}
\]
\[
 {\mathsf B}_F(q,r)
 =
 {qF(q)-rF(r)\over q-r}
 =
 \int {d\nu(y)\over(1+qy)(1+ry)},                        \tag{387}
\]
with the diagonal values supplied by derivatives.  These are Gram kernels of the two resolvent
features
\[
 {y^{1/2}\over1+qy},\qquad {1\over1+qy}.                 \tag{388}
\]
Thus the all-order one-fibre hierarchy `(384)` and the complete pair-fibre positivity
`(386)`--`(387)` are two shadows of one resolvent object.

### What the recent Sonin Hausdorff theorem does and does not supply

`SoninCoupledQuantumHausdorff.lean` unconditionally proves a complete Hausdorff hierarchy for the
density-replica moments of the actual all-prime Sonin master effect.  This is important evidence
that the corpus already possesses positive compact spectral fibres.  It does **not** identify
their moments with `(384)`.  The formalized Bernstein comparison isolates the exact remaining
quantity as the source/target mismatch.  Hence the theorem says:

```text
positive compact generator exists on the Sonin face;
Xi Cassini response exists on the theta face;
the missing mathematics is the coherent source intertwiner between those faces.
```

Calling the Sonin moment measure the desired \(\nu\) without proving this intertwiner would merely
rename the open core.

## 46. The Euler--Poisson--Gamma covariant resolvent law

The preceding analysis suggests the following stronger replacement for Section 43.

`[BOLD CONJECTURE] [EULER_POISSON_GAMMA_COVARIANT_RESOLVENT_COMPLETION]`

> There is a source-defined pointed rigged Hilbert module
> \(({\cal H}_{\mathrm{EPG}},\Omega)\) and a positive self-adjoint generator \(Y\), constructed
> as the closable cofinal integration of the finite theta-shell, von Mangoldt prime-power,
> Gamma/polar, and complementary-record blocks, such that:
>
> 1. the moving theta fibres \(L^2(P_q)\) have source-defined isometric transports into
>    \({\cal H}_{\mathrm{EPG}}\) whose infinitesimal compression is the exact connection
>    `(380)`--`(381)`;
> 2. the transported completed response vectors are
>    \(u_q=(1+qY)^{-1}\Omega\);
> 3. their scalar response is the genuine Cassini source,
>    \[
>      F(q)=\langle\Omega,(1+qY)^{-1}\Omega\rangle;        \tag{389}
>    \]
> 4. the finite source transports retain the Euler--Gamma and Poisson--Gamma cross terms, obey
>    the resolvent cocycle before scalarization, and converge in a Hausdorff rigged topology
>    retaining every principal \(\Xi\)-conormal evaluation.

The operative identity is
\[
 (1+qY)^{-1}-(1+rY)^{-1}
 =
 (r-q)(1+qY)^{-1}Y(1+rY)^{-1}.                           \tag{390}
\]
Its two compressions are exactly the Gram kernels `(386)`--`(387)`.  This makes “triple
coherence” testable: the transport from \(q\) to \(r\) and then \(r\) to \(s\) must agree with
the direct transport and preserve `(390)`.  It also makes “third completion” precise.  The
completion is the reproducing/rigged module generated by the whole resolvent history
\(\{u_q\}\), not a finite truncation and not ambient adelic \(L^2\).

### Why this would force the critical line

The compact version of `(389)`, with the corpus support aperture, is exactly the local
theta-boundary Markov premise already transported in Lean to the centered completed-seam germ.
The existing unconditional consumer then yields RH.  Equivalently, the squared centered divisor
is the singular support of a positive self-adjoint resolvent, hence lies on the real
nonpositive spectral ray.  Therefore every centered divisor coordinate is purely imaginary,
and localization of `(390)` gives
\[
 |p^{m_\rho(\rho-1/2)}|=1,\qquad
 \kappa_{p,\rho}=0.                                      \tag{391}
\]
Thus principal-conormal unitarity and Section 43's curvature law are consequences of the
resolvent completion, not hypotheses inserted into it.

### New universal interpretation

The conjecture asserts a general mechanism beyond this one function:

> Temperedness is source resolvent coherence.  A completed Euler--Poisson--Gamma object is
> tempered when its positive local polarizations integrate to one self-adjoint resolvent
> history; nontempered divisor curvature is the obstruction to that integration.

This interpretation simultaneously explains:

```text
Euler positivity               = positivity of one convergence-side fibre;
theta positivity               = positivity of a moving additive fibre;
Gamma/polar completion         = cross-term orienting the fibre comparison;
Sonin master effects           = finite positive spectral models;
HT rank-two detection          = pairwise resolvent Gram detection;
HT rank-three gluing           = resolvent-cocycle composition;
metaplectic phase obstruction  = failure of scalar rather than module-valued coherence;
projective leakage             = norm lost after deleting the complementary record;
off-line generalized systems   = local positive fibres without the EPG coherent intertwiner;
critical-line purity           = self-adjoint spectral support after coherent integration.
```

### Finite-stage construction obligations

For a prime packet \(P\) and Gamma depth \(N\), the conjecture demands explicit objects, not
abstract dilation language:

1. construct a joint completed source block \(Y_{P,N}\) from theta integer shells, von Mangoldt
   prime powers, incomplete-Gamma packets, polar cancellation, and the complementary record;
2. prove \(Y_{P,N}\ge0\) only after the polar--zeta cancellation and Beta-reflection orientation
   have been included;
3. construct the finite resolvent vectors \(u^{P,N}_q\) and prove the exact analogue of `(390)`
   for all pairs \(q,r\) in one source interval;
4. prove compatibility under \(P\subset P'\) and \(N\le N'\), including the mixed cross terms,
   rather than only convergence of diagonal moments;
5. prove closability, tight spectral support, and convergence of the two Gram kernels
   `(386)`--`(387)` to the genuine theta response;
6. identify the limit on an open source domain without using Xi zeros, target Hankel
   determinants, target Jacobi parameters, or a post-selected unitarization.

The existing finite von Mangoldt--Gamma joint Grams address pieces of Items 1--2.  The exact theta
transport `(380)` addresses the infinitesimal form of Item 3.  The Sonin master effect supplies a
candidate positive generator for Item 1.  No corpus theorem currently proves their common
intertwiner or the cofinal resolvent identity.

### Falsifiers

The route fails if any one of the following occurs:

1. some completed finite pair kernel corresponding to `(386)` or `(387)` has a negative Gram
   matrix after all forced source cross terms are included;
2. the finite transports are positive but violate the three-aperture cocycle;
3. the cofinal operator is nonclosable or loses the pointed vector;
4. spectral tightness requires a measure read from the Xi divisor;
5. the limit matches only finitely many derivatives rather than an analytic source germ;
6. the proposed generator is merely the positive Sonin master effect with the unresolved
   Bernstein mismatch renamed.

### Novelty calibration

Stein transport for changing probability laws, Hausdorff moment theory, positive self-adjoint
resolvents, Loewner kernels, GGC/Thorin representations, Stinespring dilation, and Hilbert-module
completion are parent mathematics.  Targeted corpus and arXiv searches found these ingredients
separately, including Stein transport along tempered probability curves and the known
Thorin/RH equivalence.  No located source supplies the exact EPG conjunction `(376)`--`(390)` or
constructs its generator from divisor-free Riemann source data.  This is negative collision
evidence, not a priority claim.

Most importantly, `(389)` remains an RH-strength conjecture.  The advance here is not a proof of
its positivity.  It replaces a circular unitary-reduction hunch by one exact cross-aperture source
law, exposes its finite falsifiers, and shows which existing positive corpus objects must be
intertwined rather than accumulated independently.

## 47. Reversibility is insufficient; the equilibrium sector must be source-pinned

A natural attempted interpretation of Section 46 is that Euler prime powers are forward jumps,
Poisson reflection supplies reversed jumps, and Gamma/polar completion enforces detailed balance.
This is too weak.

For a centered radial exponent \(c<1/2\), the proved prime-valuation law is
\[
 \mu_{p,c}(k)=(1-b_{p,c})b_{p,c}^{\,k},\qquad
 b_{p,c}=p^{-(1-2c)}.                                    \tag{392}
\]
On \(\mathbb N_0\), consider the birth--death rates
\[
 k\longrightarrow k+1\quad\hbox{at rate }b_{p,c},\qquad
 k+1\longrightarrow k\quad\hbox{at rate }1.              \tag{393}
\]
Then
\[
 \mu_{p,c}(k)b_{p,c}=\mu_{p,c}(k+1),                      \tag{394}
\]
so `(392)` is reversible for `(393)` for **every** \(c<1/2\).  Taking products gives a reversible
prime-valuation process in every radial sector.  Abstract detailed balance therefore does not
select the critical line; it allows the equilibrium state to move with the conormal.

`[PAPER-PROVED] [RADIAL_DETAILED_BALANCE_NONSELECTIVITY]`

This is the stochastic version of two existing corpus countermodels:

```text
diag(exp(delta t),exp(-delta t)) with reflected time reversal
  is reversible for every delta;

the Kakutani product sector mu_c
  is internally well-defined for every c<1/2,
  but is normal to the critical sector mu_0 only for c=0.
```

Thus neither reflection, reversibility, a self-adjoint realization in a conormal-dependent
metric, nor zero cycle affinity proves RH.

The adjective **source-defined** in `(389)` is consequently load-bearing.  The conjecture must
produce one pointed state \(\Omega\), one generator \(Y\), and one spectral measure before divisor
localization.  It must then prove strict source-normal base change:
\[
 \operatorname{Loc}_{\rho}
   \bigl(\operatorname{Completion}_{\rm EPG}(\text{source})\bigr)
 \;\cong\;
 \operatorname{Completion}_{\rm EPG}
   \bigl(\operatorname{Loc}_{\rho}(\text{source conormal})\bigr),       \tag{395}
\]
with the right side normal in the same pointed sector for every \(\rho\).  A metric, invariant
measure, or self-adjoint extension allowed to depend on \(\rho\) makes `(395)` vacuous.

Equation `(395)` is exactly where the infinity problem lives:

```text
finite level:
  localization exists, but completion covariance leaks;

ambient infinite L2:
  completion exists, but localization fibre vanishes;

prime-valuation sector field:
  both objects exist, but source-normal base change is unproved;

covariant EPG resolvent completion:
  conjecturally makes completion and principal-conormal localization commute.
```

The Kakutani theorem then becomes the radial selector rather than the producer.  If `(395)` puts
the fibre at \(\rho\) normally in the source-pinned critical sector, its exponent
\(c=1/2-\operatorname{Re}\rho\) must be zero.  But source-normality in `(395)` remains RH-strength;
it cannot be inferred from internal reversibility of the fibre.

### Revised universal-law statement

The strongest surviving interpretation is therefore:

> **Temperedness is source-pinned resolvent base change.**  A completed arithmetic object is
> tempered when its divisor localization commutes with one divisor-independent, record-complete
> positive resolvent completion.  Off-line curvature is the Radon--Nikodym/Kakutani obstruction
> to that base change.

This law is sharper than “zeros are eigenvalues of a self-adjoint operator.”  It says why the
inner product and operator cannot be selected after seeing the zeros, why finite truncations and
ambient \(L^2\) fail in opposite ways, and why a generalized off-line Euler system is not a
counterexample unless its conormals also satisfy the same literal ordinary-prime EPG base-change
theorem.

It also identifies the first genuinely proof-bearing lemma more precisely than Section 46:

`[OPEN CORE] [SOURCE_PINNED_EPG_RESOLVENT_BASE_CHANGE]`

Construct the finite completed EPG resolvent comparison on the source-normal blow-up and prove
that its pointed spectral state is independent of prime cutoff, Gamma depth, theta aperture, and
eventual conormal specialization.  The cofinal limit must carry the BV/Mertens principal normal
class normally in that one state.  Once this is proved, the existing Kakutani, compact-Markov,
and principal-curvature consumers give three independent routes to `(391)`.

## 48. The quasianalytic jump is false: flatness is a retained face, not a vanishing criterion

One tempting attempt to strengthen `(395)` is:

```text
finite divisor multiplicity + membership in every powered prime range
  ==> zero.
```

The internal HT corpus rules this out.  The multiple-elliptic-Gamma flat-phase-reversal theorem
constructs a nonzero hypertranscendental source section whose difference from the
differential-algebraic boundary is flat to every order.  More decisively, the unconditional Lean
theorems

```text
periodIncidenceFlatTarget_mem_all_poweredRanges
periodIncidenceFlatTarget_ne_zero_of_not_discrete
```

in `HTGeometry/PeriodIncidenceFlatIntersection.lean` exhibit a nonzero target in every powered
range; the same formal development separates exact ranges while their norm closures collapse.

`[CORPUS-PROVED] [ALL_ORDERS_FLAT_NONVANISHING]`

Therefore neither Krull-intersection rhetoric, norm-closure separation, finite spectral
multiplicity, nor hypertranscendence alone can delete an off-line conormal.  A source topology
fine enough to remember the HT flat face is necessary.  What must vanish is not the flat vector
but a **resolvent defect carried by it**.

This also sharpens the role of the multiple-elliptic-Gamma rank dichotomy.  Rational-rank
arithmetic may determine which seminorms and incidence directions the source topology must see;
it does not by itself turn that topology quasianalytic.  Any proof using it as a bare
flat-implies-zero principle contradicts the formal corpus.

Thus `[SOURCE_PINNED_EPG_RESOLVENT_BASE_CHANGE]` in Section 47 is still too compressed.  It hides
three noncommuting operations:

```text
form source cohomology;
complete in a positive metric;
localize at a divisor conormal.
```

The corpus says that completing first loses the conormal, while localizing first permits a
conormal-dependent metric.  The missing construction must fix the order rather than identify a
single miraculous ambient Hilbert space.

## 49. The third completion is a rigged cohomology sequence

The proposed universal reinterpretation is:

> **Constraints before completion; purity by source-topology resolvent exactness.**
> Form the strict source cohomology before metric completion.  Use its positive Hodge completion
> only to produce unitary dynamics, while retaining the original nuclear topology as the test
> topology on which arithmetic conormals live in the continuous dual.

The required object is consequently a sequence, not one space:
\[
 C^\bullet_{\rm src}
 \ \longmapsto\
 E:=H^1_{\rm str}(C^\bullet_{\rm src})
 \ \supset\
 D_{\rm src}
 \ \hookrightarrow\
 H_{\rm Hdg}
 \ \hookrightarrow\
 D_{\rm src}',                                                   \tag{396}
\]
where:

1. \(C^\bullet_{\rm src}\) is built from Euler, Gamma, Poisson, and Cauchy data before zero
   localization;
2. \(E\) is Hausdorff strict nuclear cohomology;
3. \(D_{\rm src}\) is nuclear-dense in \(E\), invariant under the centered flow
   \(A=\Theta-\tfrac12\), and fine enough that every nonzero divisor conormal remains nonzero on
   \(D_{\rm src}\);
4. a source-defined positive Green form embeds \(D_{\rm src}\) densely into
   \(H_{\rm Hdg}\);
5. \(A\) extends to a skew-adjoint operator on \(H_{\rm Hdg}\).

The divisor points need not be vectors of \(H_{\rm Hdg}\).  They are allowed, and expected, to be
continuous transpose eigenfunctionals in \(D_{\rm src}'\).  This simultaneously avoids the two
known failures:

```text
finite truncation:
  conormals remain, covariance leaks;

ambient adelic L2:
  covariance and self-adjointness remain, conormals disappear;

rigged source cohomology:
  conormals remain in D_src', while H_Hdg supplies the unitary axis.
```

### Exact defect law

For \(z\in\mathbb C\), define the reduced source resolvent cohomology
\[
 {\mathfrak R}_z(D_{\rm src})
 :=
 D_{\rm src}/\overline{(A-z)D_{\rm src}}^{\,D_{\rm src}}.          \tag{397}
\]
Continuous linear duality gives the exact identity
\[
 {\mathfrak R}_z(D_{\rm src})'
 \cong
 \ker\!\left((A-z)' : D_{\rm src}'\longrightarrow D_{\rm src}'\right).
                                                                    \tag{398}
\]
Indeed, both sides are exactly the continuous functionals annihilating
\((A-z)D_{\rm src}\).  No positivity, compactness, or spectral theorem is used in `(398)`.

If the Riemann conormal \(\lambda_\rho\) satisfies
\[
 \Theta'\lambda_\rho=\rho\lambda_\rho ,
\]
then its nonzero restriction to \(D_{\rm src}\) gives
\[
 0\ne[\lambda_\rho]\in
 {\mathfrak R}_{\,\rho-1/2}(D_{\rm src})'.                         \tag{399}
\]
Thus a zero is not fundamentally a point eigenvector.  It is a nonzero topological obstruction
to solving the source-normal equation
\[
 (A-(\rho-\tfrac12))u=f.                                          \tag{400}
\]

This yields a strictly weaker proof obligation than source-core automorphy: dense range is enough.
If
\[
 \overline{(A-z)D_{\rm src}}^{\,D_{\rm src}}=D_{\rm src}
 \qquad(\operatorname{Re}z\ne0),                                  \tag{401}
\]
then `(398)` forbids every off-axis divisor conormal.  Consequently `(399)` and `(401)` give
\[
 \operatorname{Re}(\rho-\tfrac12)=0,
 \qquad\text{hence}\qquad
 \operatorname{Re}\rho=\tfrac12.                                  \tag{402}
\]

`[PAPER-PROVED] [REDUCED_RESOLVENT_COHOMOLOGY_DUALITY]`

`[CONDITIONAL] [SOURCE_DENSE_RANGE_PURITY]`

The algebraic implication is exact.  The arithmetic premise `(401)` is the RH-strength step.

### Bold source law

`[BOLD CONJECTURE] [SOURCE_COHOMOLOGY_FIRST_POLARIZED_RESOLVENT_EXACTNESS]`

The literal Riemann Euler--Gamma--Poisson source admits `(396)` such that
\[
 \operatorname{supp}_{\mathbb C}{\mathfrak R}_\bullet(D_{\rm src})
 \subset i\mathbb R.                                               \tag{403}
\]
Equivalently, every off-axis centered Hilbert resolvent has dense source-topology range, even
though its inverse need not preserve every source seminorm continuously.

This is a conjecture in the intended strong sense: the corpus gives reasons to expect it, but no
present proof of its arithmetic premise.  It is also falsifiable.  A single off-axis \(z\) and a
nonzero continuous source functional annihilating \((A-z)D_{\rm src}\) refutes `(403)`.

The conjecture is not asserted for arbitrary hypertranscendental functions or arbitrary
self-dual entire functions; the explicit generalized-prime off-line systems forbid that.  Its
domain is the source-minimal, self-dual, polarizable Euler--Gamma--Poisson complex with the
literal ordinary-prime source.

### What the earlier laws become

Under `(396)`--`(403)`, the major corpus phenomena are shadows of one order-of-operations law:

```text
Kakutani singularity:
  radial image of a nonzero source resolvent defect;

Ward/Cauchy orientation:
  scalar boundary report of the defect, not its sign-producing cause;

principal conormal curvature:
  local geometric image of failure of source exactness;

all-orders-flat HT sections:
  legitimate D_src directions invisible to coarser Hilbert closure;

finite propagation/leakage:
  failure of finite source stages to be resolvent invariant;

continuous-spectrum disappearance:
  result of completing before taking strict cohomology;

Meyer divisor module:
  strong-dual support of reduced source resolvent cohomology;

critical line:
  unitary boundary on which skew-adjoint dynamics may support that cohomology.
```

The scalar Stieltjes/Markov conjecture of Section 46 is therefore demoted: a scalar Cassini
response need not itself be a positive resolvent transform.  EPG data should construct the
chain-level Green operator and the topology of \(D_{\rm src}\); scalar transforms are
compressions that report whether `(401)` holds.

### Immediate new corollaries and audit gates

If `(403)` is proved, then:

1. every continuous generalized eigenfunctional of the source complex lies on the unitary axis,
   not only those already identified with zeta zeros;
2. no all-orders-flat HT direction can carry an off-axis continuous resolvent defect;
3. any off-axis resonance in an analytically continued Hilbert resolvent proves failure of the
   proposed source topology or polarization, rather than merely failure of self-adjointness;
4. RH reduces to topological dense range, not construction of zero-indexed Hilbert eigenvectors
   or a compact operator with prescribed spectrum.

The construction is circular unless all of the following are source-side:

```text
positive complex structure / second Riemann bilinear relation;
global all-place Green form and full Cauchy boundary classification;
strict nuclear Poisson comparison before divisor localization;
strong compatibility of centered resolvents with source regularity and boundary conditions;
proof that every Meyer divisor functional is continuous and nonzero on D_src.
```

Local Hodge stars, target-indexed polarizations, or metrics selected after observing
\(\rho\) do not satisfy these gates.  Skew-adjointness on \(H_{\rm Hdg}\) alone is also
insufficient: it gives off-axis inversion in the Hilbert topology, while `(401)` concerns the
strictly finer source topology.

`[OPEN CORE] [GLOBAL_SOURCE_POLARIZATION_AND_DENSE_RESOLVENT_RANGE]`

Construct the source-positive complex structure and prove `(401)` directly from its
Euler--Gamma--Poisson boundary calculus.  This is now the unique nonformal mathematical producer.
The divisor comparison, reduced-defect duality, and critical-line deduction are consumers.

## 50. Collision correction: dense range is a weakening, not the universal jump

Sections 28--29 and `deninger-tate-poisson-pro-hodge-rigging` already identified the essential
locally convex/directed-Hilbert alternatives to one ambient Hilbert space.  In particular, they
already proved the forward equicontinuous and directed-conormal purity consumers and proposed a
positive-collar pro-Hodge family retaining strong-dual conormals.

Therefore Section 49 contributes only the following genuine refinement:

```text
old source-resolvent consumer:
  every off-axis operator difference is surjective;

new source-resolvent consumer:
  every off-axis operator difference merely has dense range
  in the topology on which divisor conormals are continuous.
```

The Lean theorems

```text
deningerContinuousTransposeEigenfunctional_eq_zero_of_sub_denseRange
deningerSourceDenseRange_transposeEigenvalue_re_eq_zero
deningerSourceDenseRange_transposeEigenvalue_re_eq_half
riemannHypothesis_of_hodgeSchwartzDenseRangeXiSpectrum
```

now formalize that weakening unconditionally.  It is useful, but it does not construct the source
topology or its polarization.  Calling `(396)` itself the missing universal law would rediscover
the earlier pro-Hodge work.

The producer still has to explain why one source-positive structure controls all shell/prime/HT
directions simultaneously.  The next synthesis uses a different corpus ingredient: scalar
commutant rigidity of a complete labelled observation.

## 51. Complete-observation unitarization: fusion turns Hodge naturality into a two-generator law

The positive HT divisor frame gives more than many copies of the same zero.  It canonically gives
an irreducible **source observation pair**.

Fix \(M\ge12\) and put
\[
 h_m:=H_m(1)
 =
 {1\over\zeta(m+1)}-{1\over\zeta(m)}>0,
 \qquad m\ge M.                                           \tag{404}
\]
For a finite shell aperture \(I_N=\{M,\ldots,N\}\), let
\[
 \Omega_N=(\sqrt{h_m})_{m\in I_N},\qquad
 L_N=\operatorname{diag}(m)_{m\in I_N},\qquad
 P_N=\Omega_N\Omega_N^\ast.                              \tag{405}
\]
Here \(L_N\) remembers which positive source shell is being observed, while \(P_N\) remembers
that all shells fuse into one pointed source.  Neither uses a zero.

`[PAPER-PROVED] [FULL_SUPPORT_FUSION_COMMUTANT_RIGIDITY]`

If \(X\in\operatorname{End}(\mathbb C^{I_N})\) commutes with both \(L_N\) and \(P_N\), then
\[
 X=c\,1.                                                  \tag{406}
\]
Indeed, the simple spectrum of \(L_N\) makes \(X\) diagonal.  The
\((m,n)\)-entry of \([X,P_N]\) is
\[
 (X_{mm}-X_{nn})\sqrt{h_mh_n}.
\]
Every \(h_m\) is nonzero, so all diagonal entries agree.

`[LEAN-FORMALIZED]`

The theorem

```text
eq_scalar_of_commutes_labelledCoordinate_weightedCompleteCoupling
```

formalizes `(406)` over an arbitrary field and arbitrary nonzero full-support weights.

### Polar-defect commutant law

Let \(\mathcal A_N\) be the algebra generated by \(L_N\) and \(P_N\), and let \(C_N\) be
invertible.  Suppose spatial continuation
\[
 \alpha_N(A)=C_NAC_N^{-1}                                \tag{407}
\]
preserves adjoints on \(\mathcal A_N\):
\[
 \alpha_N(A^\ast)=\alpha_N(A)^\ast.
                                                                    \tag{408}
\]
Taking adjoints in `(407)` and comparing with `(408)` gives
\[
 A^\ast C_N^\ast C_N=C_N^\ast C_NA^\ast
 \qquad(A\in\mathcal A_N).                               \tag{409}
\]
Thus \(C_N^\ast C_N\) lies in the commutant of \(\mathcal A_N\), and `(406)` forces
\[
 C_N^\ast C_N=c_N1,\qquad c_N>0.                         \tag{410}
\]
So a spatial continuation that is natural for only the two source observables in `(405)` is
already conformal.  No zero-indexed inner product or full list of Hodge matrix coefficients is
needed.

This is parent Schur/multiplicative-domain mathematics.  The arithmetic content is the proposed
choice of the two generators from the positive shell source.

### Exact shell-purity consequence

For \(\Re s>1/2\), the positive divisor frame provides the nonzero diagonal continuation
coordinates
\[
 c_m(s):={H_m(s)\over\sqrt{h_m}},
 \qquad
 C_N(s)=\operatorname{diag}(c_m(s))_{m\in I_N}.           \tag{411}
\]
Its polar defect is
\[
 C_N(s)^\ast C_N(s)
 =
 \operatorname{diag}\left(
   {|H_m(s)|^2\over h_m}
 \right)_{m\in I_N}.                                     \tag{412}
\]
If the source continuation on the principal divisor conormal satisfies `(408)` compatibly for
all \(N\), then `(410)` makes the ratios in `(412)` independent of \(m\).  But the proved shell
likelihood-rate theorem gives
\[
 \lim_{m\to\infty}{1\over m\log2}
 \log {|H_m(s)|^2\over h_m}
 =
 1-2\Re s.                                                \tag{413}
\]
A constant positive sequence has rate zero.  Hence
\[
 (408)\quad\Longrightarrow\quad
 \Re s=\frac12.                                          \tag{414}
\]
If RH is false, the functional equation supplies a zero in
\(\Re s>1/2\), where `(411)` is available.  Therefore a source-global version of `(408)` on the
Riemann principal conormal proves RH.

This deduction is different from demanding a scalar sign.  Off-line displacement is the
non-scalar positive operator `(412)`.  The critical line is exactly the locus where the polar
defect can belong to the scalar commutant of the complete source observation.

### Universal interpretation

> **A complete source observation turns covariance into unitarity.**
> Analytic continuation may preserve an indefinite pairing while acquiring a non-scalar polar
> defect.  If it is adjoint-natural for a source-labelled observable and one full-support fusion
> coupling, that defect has nowhere to live: irreducibility makes it scalar.  Source asymptotics
> then force zero modular drift.

This reinterprets the obstruction corpus as follows:

```text
finite truncation leakage:
  adjoint-natural similarities exist separately, but their scalar rays
  need not be compatible under aperture enlargement;

ambient adelic L2:
  covariance exists after the fusion conormal has disappeared, so the
  full-support rank-one generator is absent;

off-line generalized-prime Euler systems:
  retain diagonal positivity and reflection, but their polar defect is
  non-scalar and therefore fails full-fusion adjoint naturality;

all-orders-flat HT directions:
  remain legitimate source directions; they are not killed, but a
  natural metric defect cannot assign them an independent positive weight;

positive shell frame:
  supplies the simple label and full-support coupling before localization;

Wold likelihood slope:
  is the asymptotic spectrum of the polar defect;

Hodge/Green positivity:
  is no longer an arbitrary global matrix construction; it is the
  assertion that continuation preserves the star on two source generators;

critical line:
  is scalarity of the continuation polar defect.
```

The HT role is therefore not “hypertranscendence implies a zero.”  The disjoint positive shell
channels and their transverse differential independence prevent the complete source observation
from collapsing to a finite redundant channel.  The Kähler--Tate clock supplies the Ind--Pro
boundary on which the infinite labelled observation should live.  The fusion projector supplies
the missing coupling that a diagonal or fibrewise metric never sees.

### Bold source conjecture

`[BOLD CONJECTURE] [XI_SHELL_FUSION_STAR_COVARIANT_CONTINUATION]`

The ordinary-prime Euler--Gamma/co-Poisson continuation of the principal Xi conormal admits a
source-defined compatible spatial lift on every finite positive-shell packet such that:

1. its shell-coordinate restriction is `(411)`;
2. it intertwines the labelled shell observable \(L_N\);
3. conjugation by the lift preserves the adjoint of the source fusion projector \(P_N\);
4. the lifts commute with aperture enlargement, Gamma transgression, the Rees boundary map, and
   functional-equation reflection; and
5. all structures are constructed on the principal conormal module before divisor
   specialization.

Clause 3 is the sole new metric equation.  Since the diagonal relation in Clause 2 is automatic,
it is enough to prove
\[
 \left(C_NP_NC_N^{-1}\right)^\ast
 =
 C_NP_NC_N^{-1}                                         \tag{415}
\]
as a source-cohomological identity.  Equivalently, in a unital completely positive realization,
\(P_N\) lies in the multiplicative domain of continuation.  Equations `(406)`--`(414)` then prove
RH.

This conjecture is a truth hunch, not a disguised claim of proof.  It is motivated by the exact
positive fusion, full-support Wold weights, finite Hodge chain maps, and scalar-commutant theorem.
Its provability is unknown.

### Hostile audit

1. Coefficientwise positive fusion does not itself construct the operator lift `(407)`.
2. Analytic continuation is not generally positive or completely positive.
3. Verifying `(415)` after choosing a zero and fitting a metric is exactly circular.
4. Multiplicativity on the diagonal shell algebra is useless; the rank-one fusion projector must
   lie in the same multiplicative domain.
5. A separate star on each aperture is insufficient.  Compatibility of the scalar rays in
   `(410)` is load-bearing.
6. Indefinite reflection pairing gives
   \(H_m(s)\overline{H_m(1-\overline s)}\), not the positive defect `(412)`, and permits every
   off-line quartet.
7. Tomita--Takesaki positivity or abstract unitarization does not prove `(415)`; the failed
   modular routes remain failed.
8. The full-support commutant theorem is classical.  Frontier movement occurs only if the
   Euler--Gamma/co-Poisson source proves the fusion star-covariance.

`[OPEN CORE] [XI_POSITIVE_SHELL_FUSION_MULTIPLICATIVE_DOMAIN]`

Construct the fusion projector as a class in the source Rees/Calderón boundary complex and prove
that its Kadison defect under Gamma--Poisson continuation vanishes compatibly with aperture:
\[
 \Phi_N(P_N^\ast P_N)-\Phi_N(P_N)^\ast\Phi_N(P_N)=0,
 \qquad
 \Phi_N(P_NP_N^\ast)-\Phi_N(P_N)\Phi_N(P_N)^\ast=0.       \tag{416}
\]
This is a sharper producer than scalar orientation or off-axis resolvent preservation.  It asks
one source-global operator equation whose failure is measured exactly by the already computed
shell likelihood drift.

## 52. Correction: raw fusion covariance is too rigid; the gauge-reduced shift is only a selector

### Withdrawal of the raw critical-locus interpretation

Section 51 overstates what the shell likelihood-rate theorem proves.  Equations `(410)`--`(413)`
do prove the one-way implication
\[
 \text{raw fusion star-covariance}\Longrightarrow\Re s=\frac12,
                                                               \tag{417}
\]
but they do **not** identify the critical line with raw scalarity of `(412)`.  Even when
\(\Re s=1/2\), the finite-shell ratios in `(412)` retain a generally nonconstant transverse
zero-free gauge.  Rate zero is necessary for a constant sequence, not sufficient.

The conjecture `XI_SHELL_FUSION_STAR_COVARIANT_CONTINUATION`, if read as an exact raw identity on
all critical divisor fibres, is therefore unsupported and probably false.  It is withdrawn in
that form.  The scalar-commutant theorem `(406)` remains valid, but it is a selector and not a
source producer.

### Exact source gauge

Recall the uniformly invertible shell gauge
\[
 G_m(s)=\frac{2^{ms}H_m(s)}{1-2^{-s}},
 \qquad \Re s>\frac12.
                                                               \tag{418}
\]
At \(s=1\),
\[
 h_m=H_m(1)=2^{-m-1}G_m(1).
                                                               \tag{419}
\]
Hence, with the positive square root of \(G_m(1)\),
\[
\begin{aligned}
 c_m(s)
 &=\frac{H_m(s)}{\sqrt{h_m}}\\
 &=\sqrt2(1-2^{-s})\,
   \frac{G_m(s)}{\sqrt{G_m(1)}}\,
   2^{-m(s-1/2)}.                                         \tag{420}
\end{aligned}
\]
Put
\[
 Q_m(s):=\frac{G_m(s)}{\sqrt{G_m(1)}},
 \qquad
 z(s):=2^{-(s-1/2)}.
                                                               \tag{421}
\]
The uniform gauge theorem gives \(Q_m(s)\to1\) for fixed \(s\), and \(Q_m(s)\) is uniformly
bounded and bounded away from zero on the source tail.  Removing \(Q_m(s)\) leaves the exact
pure character
\[
 \widetilde c_m(s)
 =\sqrt2(1-2^{-s})z(s)^m.                                \tag{422}
\]
Thus transverse shell variation is a zero-rate gauge.  The only gauge-invariant radial datum is
\[
 |z(s)|=2^{-(\Re s-1/2)}.                                \tag{423}
\]

### Weighted-shift and Toeplitz boundary law

Let \(S e_m=e_{m+1}\) be the unilateral shell shift.  On the eventual tail define
\[
 w_m(s):=\frac{c_{m+1}(s)}{c_m(s)}
 =z(s)\frac{Q_{m+1}(s)}{Q_m(s)},
 \qquad
 W_s e_m=w_m(s)e_{m+1}.                                  \tag{424}
\]
Then
\[
 w_m(s)\longrightarrow z(s).                            \tag{425}
\]
Consequently the diagonal defects of the weighted shift satisfy
\[
\begin{aligned}
 W_s^\ast W_s-I&=\operatorname{diag}(|w_m(s)|^2-1),\\
 W_sW_s^\ast-I&=
 \operatorname{diag}(-1,|w_0(s)|^2-1,|w_1(s)|^2-1,\ldots).
                                                               \tag{426}
\end{aligned}
\]
Both are compact exactly when \(|w_m(s)|\to1\).  Therefore:

`[PAPER-PROVED] [GAUGE_REDUCED_SHELL_SHIFT_ESSENTIAL_UNITARITY]`
\[
 \boxed{\quad
 W_s\text{ is essentially unitary}
 \quad\Longleftrightarrow\quad
 \Re s=\frac12.
 \quad}                                                     \tag{427}
\]

Equivalently, in the Toeplitz/Calkin boundary,
\[
 [W_s]=z(s)[S],
 \qquad
 [S]\text{ unitary},
                                                               \tag{428}
\]
so \([W_s]\) is unitary exactly when \(|z(s)|=1\).

The exact algebraic version needs only one adjoint identity.  If the gauge-reduced continuation
acts on the Toeplitz generator by
\[
 \alpha_s(S)=z(s)S,\qquad
 \alpha_s(S^\ast)=z(s)^{-1}S^\ast,
                                                               \tag{429}
\]
then star preservation gives
\[
 z(s)^{-1}S^\ast
 =\alpha_s(S^\ast)
 =\alpha_s(S)^\ast
 =\overline{z(s)}S^\ast.
                                                               \tag{430}
\]
Since \(S^\ast\ne0\), `(430)` is equivalent to \(|z(s)|=1\), hence to the critical line.

### Corpus collision and anti-theatre verdict

The elementary implication `(427)` is not frontier movement.  Sections 16--17 already identify
the Wold--Toeplitz carrier, Sections 28--29 already prove reflected power-equicontinuous purity,
Sections 30--33 already construct the shell corona, uniform gauge, likelihood rate, and
scale--phase completion, and the failed Calkin cards already prove that imposing a compactness or
essential-unitarity condition only after Xi-fibre specialization is an RH-equivalent endpoint.

The positive correction is therefore only a cleaner dictionary:

```text
finite truncation leakage:
  the terminal defect of the unilateral shift;

uniform transverse shell gauge:
  compact/zero-rate perturbation of the shift weights;

strict-right off-line fibre:
  a proper contraction character in the Toeplitz interior;

critical fibre:
  a unitary character in the Toeplitz boundary;

ambient Hilbert completion:
  restores the shift but loses divisor point fibres;

source-relative completion:
  must retain the conormal and prove that its character reaches the
  selfadjoint boundary before fibre specialization.
```

No new Toeplitz conjecture is opened here.  The live producer remains the corpus's existing
source-first additive--multiplicative comparison: identify the projective producer--reporter Weyl
relation with the Poisson/Tate intertwiner, construct the strict enhanced Fourier--Mellin graph,
and prove conservative principal-conormal base change.  In operator-algebra language this is the
already isolated relative-hyperrigidity/multiplicative-domain theorem; in nearby-cycle language it
is strict factorized Rees base change.  Naming either property on a chosen zero is theatre.
