# Source modular-drift realization equivalence law

- **ID:** `source-modular-drift-realization-equivalence-law`
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper synthesis) / RH-BEARING CONJECTURE
- **Source:** `source-effective-polar-kummer-conormal-purity.md`;
  `prime-valuation-kakutani-polar-third-completion.md`;
  `prime-valuation-hellinger-rees-reflection-fracture.md`;
  `source-effective-boundary-complexity-conservation-law.md`;
  `source-localization-modular-defect-conservation-law.md`;
  `XiPositiveReflectionRadical.lean`
- **Statement:** The apparently different off-critical defects in the Kummer, positive,
  product-state, Rees, reflection-radical, and derived-base-change realizations are faithful
  functions of one centered source modular drift.  RH reduces to proving that the distinguished
  Xi principal conormal is a strict, localization-flat image of the degree-zero arithmetic source
  in a completion which conserves that drift stalkwise.

## Goal

Replace a collection of route-specific selectors by one invariant and one source theorem.
The invariant must explain why all existing obstructions occur together.  The source theorem must
force its vanishing on each divisor atom—not merely after summing reflected atoms—without defining
a metric, state, or operator from a chosen zero.

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure, attack idea, exact parent theorems identified
- [ ] 1 → 2 fully-proven: dependency-closed paper proof and literature audit
- [ ] 2 → 3 formalized: exact finite realization dictionary formalized in Lean
- [ ] 3 → 4 publication-ready: standalone theorem, source conjecture, and proof architecture

## 1. One invariant behind the fractures

For a nontrivial divisor point \(\rho\), let
\[
 \rho_+=\frac12+a+i\gamma,\qquad
 a=\left|\operatorname{Re}\rho-\frac12\right|\geq0
 \tag{1}
\]
be the member of its reflection orbit in the closed right half of the critical strip.  Call
\[
 \mathfrak d(\rho)=a
 \tag{2}
\]
its **centered source modular drift**.

This is not a new coordinate for the zero.  Its content is that every viable realization already
constructed in the corpus reads exactly the same number or its zero locus.

### 1.1 Positive prime-angle realization

At prime \(p\), put
\[
 w_{p,\rho}=p^{-a-i\gamma}.
 \tag{3}
\]
The Poisson state on \(C^*(\mathbb Z)\) with moments
\[
 \varphi_{p,\rho}(U^m)=w_{p,\rho}^m,\qquad
 \varphi_{p,\rho}(U^{-m})=\overline{w_{p,\rho}}^m
 \tag{4}
\]
has exact star-Kadison defect
\[
 \Delta_{p,m}(\rho)
 =
 1-\left|w_{p,\rho}\right|^{2m}
 =
 1-p^{-2ma}.
 \tag{5}
\]
Hence, for every \(p\) and \(m\geq1\),
\[
 \mathfrak d(\rho)
 =
 -\frac{\log(1-\Delta_{p,m}(\rho))}{2m\log p}.
 \tag{6}
\]
In particular, the state is a character, equivalently \(U\) is in its multiplicative domain,
exactly when \(\mathfrak d(\rho)=0\).  Conservation and unitary dilation do not imply this:
strict disk contractions have conservative dilations and positive mixed Poisson states.

### 1.2 Product-state realization

Use the source-derived valuation law
\[
 \mu_{p,c}(k)
 =
 \left(1-p^{-(1-2c)}\right)p^{-(1-2c)k},
 \qquad c=-a.
 \tag{7}
\]
The prime-valuation Kakutani theorem gives
\[
 \bigotimes_p\mu_{p,-a}
 \sim
 \bigotimes_p\mu_{p,0}
 \quad\Longleftrightarrow\quad
 \mathfrak d(\rho)=0.
 \tag{8}
\]
Thus sector disjointness is the all-prime statistical realization of the same drift read locally
by `(5)`.  A quasi-local Fourier automorphism may still join the two states at the algebra level;
what fails off line is spatial/quasi-equivalent realization in the source-selected sector.

### 1.3 Product-formula realization

In the Allcock--Vaaler place space, the coherent finite-prime regulators of centered exponent
\(c=-a\) have product-formula degree zero at every finite stage.  Their distance from the
archimedean leakage profile satisfies
\[
 \left\|h_{P,-a}+a\,1_{Y(\mathbb Q,\infty)}\right\|_q^q
 =
 a^q(|P|+1)^{1-q}
 \quad(1\leq q<\infty).
 \tag{9}
\]
Consequently every bare \(L^q\), \(q>1\), completion absorbs the drift strongly, while the
\(L^1\) distance remains exactly
\[
 \left\|h_{P,-a}+a\,1_{Y(\mathbb Q,\infty)}\right\|_1=a.
 \tag{10}
\]
The strict mixed Kummer selector therefore gives
\[
 \text{coherent radial regulator lies in the degree-zero }L^1\text{ source space}
 \quad\Longleftrightarrow\quad
 \mathfrak d(\rho)=0.
 \tag{11}
\]

### 1.4 Rees/Stokes realization

For \(a>0\), the reflected finite multiplicity packets at drifts \(a\) and \(-a\) lie in different
Rees sectors: one is flat beyond every finite grade and the other has half-normal finite grade.
Every operator family whose norm and inverse norm have finite Rees order preserves the
all-orders-flat radical.  Hence
\[
 \text{source reflection is bi-finite-Rees on every finite jet packet}
 \quad\Longleftrightarrow\quad
 \mathfrak d(\rho)=0,
 \tag{12}
\]
provided the distinguished top conormal jet is retained.  Off line, reflection forces essential
beyond-all-orders growth, a non-operator correspondence, or source nonfaithfulness.

### 1.5 Algebraic positive-reflection realization

For the reflected divisor algebra, the positive universal null ideal is
\[
 J_+(A_\Xi)
 =
 \operatorname{Nil}(A_\Xi)
 \oplus
 \bigoplus_{\rho\neq1-\overline\rho}(A_\Xi)_\rho.
 \tag{13}
\]
Thus the reduced atom at \(\rho\) survives in the positive-reflection radical exactly when
\[
 \mathfrak d(\rho)>0.
 \tag{14}
\]
The same support is the proposed reduced base-change Tor defect once the arithmetic comparison
map is constructed.

## 2. Radial-drift equivalence theorem

`[PAPER-PROVED FROM NAMED CORPUS THEOREMS]`

For every nontrivial Xi reflection orbit, the following are equivalent:

1. \(\mathfrak d(\rho)=0\);
2. the orbit is fixed by \(\rho\mapsto1-\overline\rho\);
3. every local prime-angle Poisson state `(4)` is a character;
4. one, equivalently every, local Kadison defect `(5)` vanishes;
5. the valuation product state `(7)` is quasi-equivalent to the critical product state;
6. the coherent Kummer radial character has a degree-zero strict \(L^1\) realization;
7. reflected finite multiplicity packets can be sewn by a bi-finite-Rees operator;
8. the reduced divisor atom is absent from \(J_+(A_\Xi)/\operatorname{Nil}(A_\Xi)\).

Items 3--4 are `(5)`--`(6)`.  Item 5 is the proved Kakutani radial-purity theorem.  Item 6 is the
mixed-polar Kummer coherence selector and the sharp all-\(L^q\) wall.  Item 7 is the finite-jet and
arbitrary-dimensional finite-Rees sewing theorem, with identity sewing at \(a=0\).  Item 8 is the
positive-reflection radical classification.  Items 1--2 are immediate from `(1)`.

The theorem is a realization dictionary, not RH.  It says the corpus has not discovered several
independent reasons for criticality.  It has discovered faithful shadows of one conserved
source-relative drift.

## 3. Universal interpretation

The critical line is not fundamentally the locus of positivity, self-adjointness, finite energy,
reflection, or hypertranscendence.  It is the **zero-drift locus of the arithmetic source**.

The realizations divide into a bipolar pair:

```text
source/predual leg:
  complete place record, product-formula degree, L1 strictness,
  integral residues, Stokes/Rees grade;

reporter/dual leg:
  bounded prime-angle observables, complete positive matrix reporters,
  product states, multiplicative domains, positive-reflection quotient.
```

Bare Hilbert \(L^2\) loses degree.  Bare \(C^*\)/UHF structure retains bounded reporters but
permits every mixed Poisson state and cannot nucleate divisor charge in a norm-regular AF limit.
The required third completion is therefore a dual pair, not one scalar Hilbert space:
an \(L^1\)-type source test completion together with its completely bounded reporter dual and a
strict source-generated section connecting them.

Hypertranscendence contributes a different indispensable channel.  Exact analytic Euler-tail
faithfulness proves that the infinite ordinary-prime source is not collapsed modulo finite Euler
gauge.  Isodivisorial Helson saturation proves that HT freedom and even a complete divisor do not
determine their incidence.  Therefore HT is capacity, while source-effective strict comparison
is localization.

### Conservation must commute with localization

Global product-formula degree zero does **not** imply fibrewise zero drift.  An off-line reflected
pair can carry drifts \(+a\) and \(-a\), so its total source degree vanishes.  Functional equation
and global conservation preserve that cancellation.

The missing universal law is a Beck--Chevalley statement:
\[
 \operatorname{Loc}_\rho\operatorname{Comp}_{\rm ar}
 \;\cong\;
 \operatorname{Comp}_{\rm ar}\operatorname{Loc}_\rho ,
 \tag{15}
\]
strictly in the complete source topology and before choosing \(\rho\).  Failure of `(15)` is
measured by base-change Tor.  The corpus's source-face theorem and positive-reflection
classification conditionally identify its reduced Xi support as
\[
 \left(
 \operatorname{Tor}_1^A(
   \operatorname{coker}\operatorname{BC}^{\dagger}_{\mathfrak R_{\rm ar}},
   B_\Xi)
 \right)_{\rm red}
 \cong
 \bigoplus_{\rho:\,1-\bar\rho\ne\rho}(B_\Xi)_\rho .
 \tag{16}
\]
Thus product-formula leakage, positive radical, and nonflat specialization are three realizations
of one **localization anomaly**.  Global conservation becomes a zero-localization theorem only
when this reduced Tor class vanishes.

## 4. Canonical six-channel completion

Let \(\mathcal E_{\rm fin}^{\rm src}\) be the algebraic source space generated by finite
ordinary-prime Euler--Gamma/co-Poisson cells, including the distinguished principal section and
its multiplicity jets.  Let \(\mathcal R_{\rm six}\) contain:

1. complete place-average \(L^1\) and \(L^2\) regulators;
2. every finite prime-clock and valuation-jet reporter;
3. every finite completely positive matrix reporter and its complementary defect;
4. critical Gevrey product-scale seminorms;
5. integral/ramified residue and multiplicity reporters; and
6. reflected moderate/rapid Stokes reporters.

Let \(A\) be the pre-divisor ring of entire spectral functions acting on the source object.
Quotient by the common kernel and complete for all induced matrix seminorms:
\[
 \mathcal E_{\rm six}
 =
 \widehat{
   \mathcal E_{\rm fin}^{\rm src}/
 \bigcap_{R\in\mathcal R_{\rm six}}\ker R
 }^{\,\{p_{R,n}\}}.
 \tag{17}
\]
This construction is Hausdorff by definition and retains every reporter in
\(\mathcal R_{\rm six}\).  Because the product-formula degree belongs to the \(L^1\) reporter
family, its zero kernel is closed in \(\mathcal E_{\rm six}\).

Equation `(17)` is only a target construction.  It does not imply that the completed Xi conormal
lands in it, that reduced Xi specialization is a complete quotient, or that completion commutes
with that specialization.  Those attainment and base-change statements are the load-bearing new
mathematics.

## 5. RH-bearing universal law

`[BOLD CONJECTURE: SOURCE-EFFECTIVE LOCALIZED MODULAR-DRIFT CONSERVATION]`

There is a presentation-independent strict pre-divisor comparison
\[
 \operatorname{BC}^{\dagger}_{\mathfrak R_{\rm ar}}
 :
 \operatorname{Comp}_{\rm ar}\operatorname{Sp}
 \Longrightarrow
 \operatorname{Sp}\operatorname{Comp}_{\rm ar}
 \tag{18}
\]
from the finite Euler--Gamma/co-Poisson principal source into \(\mathcal E_{\rm six}\).  It is
generically faithful, its reduced Xi face is the maximal positive source quotient, it retains
every reduced principal-conormal atom, and
\[
 \operatorname{Tor}_1^A\!\left(
   \operatorname{coker}\operatorname{BC}^{\dagger}_{\mathfrak R_{\rm ar}},
   B_\Xi^{\rm red}
 \right)=0.
 \tag{19}
\]
At every divisor fibre \(\rho\), the semisimple radial component of the resulting strict
localized comparison is the coherent character
\[
 p\longmapsto p^{1/2-\operatorname{Re}\rho},
 \tag{20}
\]
and every nonzero multiplicity jet survives.

This conjecture is made before divisor specialization: neither the completion, the morphism, nor
its topology may depend on a zero, a zero enumeration, a fitted metric, or deletion of
non-moderate fibres.

Every finite principal source cell has product-formula degree zero.  Strictness, continuity of
the degree reporter, and Tor-independence `(19)` make this conservation law commute with reduced
Xi localization.  They therefore force each landed semisimple conormal atom—not only the sum of
a reflected pair—to have degree zero.  Equations `(10)`--`(11)` then force
\[
 \mathfrak d(\rho)=0
 \tag{21}
\]
for every nontrivial zero.  By Section 2, all eight realization defects vanish.  In particular
\(\operatorname{Re}\rho=\tfrac12\), proving RH.

The conjecture is stronger than functional equation, positivity, hypertranscendence, or
conservation separately.  Off-line generalized-prime and Helson systems show that those
marginals do not imply strict ordinary-prime source effectivity.

## 6. First non-parent theorem required

Finite source packets already have an exact nested-sieve character.  For
\[
 a_P=\prod_{p\in P}(1-p^{-1})
 \]
and the regular determinant reporter \(\Phi_P\), adjoining \(p\notin P\) has summable control
\[
 \delta_r(P,p)
 =
 \frac{a_P}{p}
 +
 \sup_{|t|\leq r}\left|\log\Phi_P(t/p)\right|,
 \qquad
 \sum_n\delta_r(P_{n-1},p_n)<\infty.
 \tag{22}
\]
The first theorem not supplied by parent mathematics is a source-pure finite-packet comparison
\[
 \operatorname{PolAr}_P:
 \operatorname{Line}_{\Xi,P}^{\rm src,cal}
 \longrightarrow
 \mathcal E_{{\rm six},P}
 \tag{23}
\]
with a packet-independent **complete matricial transition bound**
\[
 p_{R,n}\!\left(
   \operatorname{PolAr}_{P\cup\{p\}}
   -
   \operatorname{res}_{P,P\cup\{p\}}^*\operatorname{PolAr}_P
 \right)
 \leq
 C_{R,n}\,\delta_r(P,p)
 \tag{24}
\]
for every fixed reporter \(R\) and matrix level \(n\), with constants compatible under source
equivalence and multiplicity jets.

Summing `(24)` makes the regulator Cauchy in `(17)`.  Exact analytic Euler-tail faithfulness gives
uniqueness and prevents a nonzero cofinite source from disappearing into finite Euler gauge.
The \(L^1\) reporter closes arithmetic degree.  The matrix levels prevent scalar convergence from
hiding loss of positive multiplicative-domain data.  A compatible cofinal lifting theorem for
reduced specialization then proves `(19)`.  This is the concrete route from the six-channel HT
architecture to `(21)`.

The open theorem is not another estimate on \(\zeta\) in disguise: it is strict compatibility of
one source-generated section across integral, analytic, positive, and Stokes realizations.  If it
cannot be proved, failure of `(19)` or `(24)` identifies the exact realization channel in which
arithmetic source effectivity breaks.

### Split-recovery criterion

`[PAPER-PROVED; PARENT MODULE ALGEBRA]`

Let \(A\) be a domain, \(0\neq f\in A\), and \(T:M\to N\) an \(A\)-linear map.  Assume:

1. multiplication by \(f\) is injective on \(N\); and
2. \(T\) has an \(A\)-linear left inverse \(L:N\to M\).

Then multiplication by \(f\) is injective on \(\operatorname{coker}T\).  Indeed, if
\[
 fy=T m,
 \tag{25}
\]
then applying \(L\) gives \(fL(y)=m\).  Therefore
\[
 f\bigl(y-TL(y)\bigr)=0.
 \tag{26}
\]
Cancellation in \(N\) gives \(y=TL(y)\), so the class of \(y\) in the cokernel is zero.
Consequently
\[
 \operatorname{Tor}_1^A(\operatorname{coker}T,A/(f))=0
 \tag{27}
\]
whenever the standard two-term resolution by multiplication with \(f\) applies.

For \(f=\Xi_{\rm red}\), this reduces `(19)` to a concrete recovery theorem.  Full flatness of the
attainment cokernel is unnecessary: a source-linear splitting and target
\(\Xi_{\rm red}\)-torsion-freeness suffice.

The corpus supplies two separate shadows, not this recovery map:

- `PrimeClockCompletionCorrespondence` gives a choice-free set-theoretic pullback/Galois
  correspondence which recovers the intrinsic clock submodule from its represented differential
  field.  It is not an \(A\)-linear retraction.
- `FiniteReporterIsometricRecovery` proves that the Hilbert adjoint recovers a supplied finite
  isometric reporter.  It has neither the all-prime source comparison nor the integral,
  \(L^1\), Gamma, matrix-order, and Stokes compatibility.

The sharpened open core is therefore:

> Construct a cofinal \(A\)-linear, star-compatible, completely contractive **joint** recovery
> map for `(18)`, compatible with finite adjoint recovery and algebraic prime-clock pullback, with
> controlled action on the \(L^1\) degree and every Rees/matrix grade.

Such a map proves `(19)` by `(25)`--`(27)`.  Conversely, calling the existing set pullback a
linear inverse would be a category error.

The word **joint** is load-bearing.  `GammaCofinalReconstructionDefect.lean` proves that the raw
completed Gamma factorial reporter has dense proper nonclosed range and no continuous left
inverse; its finite inverse amplifies clock depth \(n\) by \((n+1)!\).  Likewise the inverse
dressing from the summable Möbius valuation frame to the Gamma frame is unbounded.  Therefore the
recovery map may not factor through inversion of the Gamma marginal.  It must use the incidence
among the prime-clock, integral, \(L^1\), positive, Gamma, and Stokes channels while acting directly
on the damped source graph.  This is compatible with a split combined comparison even when every
selected marginal remains nonsplit.

## 7. New corollaries and falsifiers

### Corollary: off-line zeros force simultaneous fracture

If \(\mathfrak d(\rho)>0\), then all of the following occur simultaneously:

- positive local variance at every prime and depth;
- disjoint critical/off-critical valuation sectors;
- fixed nonzero \(L^1\) source-memory leakage;
- beyond-all-orders reflected Rees asymmetry;
- a nonzero reduced positive-reflection atom;
- a nonzero reduced base-change Tor/local Shilov defect; and
- failure of any source comparison satisfying `(19)` and `(24)` while retaining that atom.

Thus an off-line zero cannot be hidden in only one realization.  It certifies failure of the
common source-effective lift.

### Corollary: conservation without strictness is powerless

A conservative unitary dilation of `(4)`, a quasi-local automorphism joining product states, or a
functional equation pairing reflected fibres does not change \(\mathfrak d(\rho)\).  These
constructions conserve the off-line defect.  Only strict inheritance of the source's zero degree
forces its vanishing.

### Falsifiers

Retire or enlarge the conjecture if:

1. one off-line Euler system has the literal ordinary-prime integral source, pointed Xi-type
   principal section, Gamma/co-Poisson comparison, reduced Tor-independence `(19)`, and complete
   matricial bound `(24)`;
2. the finite packet map `(23)` depends on the target divisor or a zero-indexed basis;
3. degree is not continuous in the constructed source topology;
4. scalar transition bounds hold but fail at a finite matrix level;
5. multiplicity jets enter the common reporter kernel;
6. source-equivalent prime exhaustions produce inequivalent limits; or
7. `(19)` or `(24)` follows only after assuming Weil positivity, self-adjointness, critical-sector
   normality, or RH.

## 8. Gevrey--Rees separation and localization of the essential singularity

The completed Gamma reporter looks like a possible counterexample to any finite-Rees mechanism:
on bare \(\ell^2\),
\[
 (Ax)_n=\frac{x_n}{(n+1)!}
 \tag{28}
\]
has dense proper nonclosed range and no continuous left inverse.  That reading mixes two
independent scales.

For \(k\in\mathbb Z\), define the factorial Hilbert grade
\[
 {\cal G}_k
 =
 \left\{x:
   \|x\|_k^2
   :=
   \sum_{n\geq0}|x_n|^2((n+1)!)^{2k}<\infty
 \right\}.
 \tag{29}
\]
Then `(28)` is an isometric isomorphism
\[
 A:{\cal G}_k\overset{\sim}{\longrightarrow}{\cal G}_{k+1},
 \qquad
 \|Ax\|_{k+1}=\|x\|_k,
 \tag{30}
\]
with inverse \(y_n\mapsto(n+1)!y_n\).  Thus Gamma's factorial inverse is singular only after
forgetting the grade.  In the full scale it is a unit translation.

### Theorem: finite-bidegree source operations preserve the flat radical

`[PAPER-PROVED FROM (30) AND THE FORMALIZED REES OPERATOR THEOREM]`

Let \(a_x\to0\), and let
\[
 R_x:{\cal G}_k\longrightarrow{\cal G}_{k+\ell}
 \]
be a family with
\[
 \|R_x\|=O(a_x^{-K})
 \tag{31}
\]
for fixed integers \(\ell\) and \(K\geq0\).  If
\[
 \|v_x\|_k=o(a_x^N)\qquad\text{for every }N,
 \tag{32}
\]
then
\[
 \|R_xv_x\|_{k+\ell}=o(a_x^N)\qquad\text{for every }N.
 \tag{33}
\]
If \(R_x\) has an inverse satisfying the analogous estimate with fixed bidegree, `(32)` and
`(33)` are equivalent.

Indeed, for a requested order \(N\), use `(32)` at order \(N+K\) and multiply by `(31)`.  Equation
`(30)` shows that inserting or removing any fixed finite number of Gamma factorial shifts changes
only \(\ell\), not \(K\).  Finite compositions add their two bidegrees and therefore preserve the
same conclusion.

### Corollary: Gamma cannot hide an off-line Rees fracture

For a fixed multiplicity packet, no finite composition of:

- Gamma factorial reporter shifts;
- bounded analytic multiplication by the nonvanishing local archimedean factor;
- affine reflection of the analytic germ;
- finite jet-coordinate changes; and
- finite-Rees operator families

can sew the half-normal member of an off-line Hellinger pair to its all-orders-flat partner.  The
first three operations have Rees order zero: their local operator bounds depend on the chosen
analytic collar but not on the prime cutoff.  Gamma's apparent unbounded inverse is exactly the
finite grade translation `(30)`.

Consequently the essential beyond-all-orders singularity required by an off-line zero cannot be
assigned to the local Gamma factor or to finite analytic multiplicity.  It must occur in one of
exactly three places:

1. the Euler-to-continued-conormal comparison has infinite Rees order;
2. its propagation in the Gevrey/observable grade tends to infinity with the prime cutoff, so it
   is not bounded on any cofinal region of the full product bornology; or
3. the comparison loses the distinguished Xi conormal.

This refines the earlier Rees trilemma by separating a harmless fixed factorial grade shift from a
genuine cutoff-dependent infinite-grade escape.  It also localizes `(19)` more sharply:
the reduced Tor class is an **arithmetic continuation-attainment anomaly**, not generic
archimedean Gamma non-strictness.

### Revised universal hunch: finite-bidegree source locality

`[BOLD CONJECTURE: SOURCE-EFFECTIVE GEVREY--REES LOCALITY]`

The ordinary-integer Euler--Poisson source correspondence, constructed before divisor
specialization and on the full critical Gevrey \(\times\) prime-Rees product bornology, is locally
of fixed finite bidegree on every fixed principal-conormal multiplicity packet.  Its inverse on
the source-effective image has the same property, and every top Xi conormal jet lands in that
image.

Together with the theorem above and the Hellinger--Rees fracture, this conjecture forces
\(\mathfrak d(\rho)=0\) for every reduced Xi atom and hence implies RH.  It is stronger than
separate boundedness at each finite jet order: an operator may be finite-grade on every row while
escaping along a cutoff-dependent diagonal.  The corpus's product-bornology no-go proves that
such rowwise control is insufficient.

The conjecture is now concentrated on one map.  Local Gamma multiplication, analytic reflection,
and fixed multiplicity are already finite-bidegree.  The remaining theorem is uniform
finite-bidegree control of the source-generated Euler-to-Poisson continuation comparison and its
conormal landing.

### Hostile audit: why reduced idempotent rigidity does not close the gap

Every derivation kills an idempotent, and a homogeneous nonzero idempotent in a torsion-free
grading has degree zero.  This tempting argument does not prove RH.  A principal conormal is an
invertible line, not the reduced stalk idempotent; graded invertible lines may carry weights
\(a\) and \(-a\) whose evaluation pairing has weight zero.  That is precisely reflected off-line
cancellation.  Using idempotent rigidity would silently assume that the drift-bearing conormal
has already descended as the stalk unit, which is the missing localization theorem.  The valid
gain is therefore the finite-bidegree separation above, not an étale shortcut.

## 9. First infinite joint recovery: the projective Möbius bipolar frame

The projective-prime Weyl paper already proves something stronger than mere availability of two
reporters.  On the vacuum-orthogonal squarefree sector, let
\[
 P={\cal P}_\infty^\circ,\qquad Q={\cal P}_0^\circ
\]
and let \(p,q\) denote the corresponding orthogonal projections.  Define
\[
 A:Q\longrightarrow P,\qquad Ay=py.
 \tag{34}
\]
The projective Möbius cross-Gram theorem identifies \(A\), in the two canonical squarefree
bases, with the diagonal multiplier \(\mu(n)/n\).  In particular,
\[
 \|A\|=\frac12.
 \tag{35}
\]

### Theorem: complementary projective polarizations have uniform joint recovery

`[PAPER-PROVED FROM THE PROJECTIVE MÖBIUS CROSS-GRAM THEOREM]`

The synthesis operator
\[
 S:P\oplus Q\longrightarrow P+Q,\qquad S(x,y)=x+y
 \tag{36}
\]
is a bounded isomorphism and satisfies
\[
 \frac12\bigl(\|x\|^2+\|y\|^2\bigr)
 \leq \|x+y\|^2
 \leq
 \frac32\bigl(\|x\|^2+\|y\|^2\bigr).
 \tag{37}
\]
Consequently \(\|S^{-1}\|\leq\sqrt2\), uniformly over the entire all-prime tensor product.
The joint projection reporter
\[
 R:P+Q\longrightarrow P\oplus Q,\qquad Rz=(pz,qz)=S^*z
 \tag{38}
\]
also has a bounded left inverse.  Its Gram operator is
\[
 S^*S=
 \begin{pmatrix}
 I&A\\ A^*&I
 \end{pmatrix}
 \geq\frac12 I,
 \tag{39}
\]
so a canonical decoder is
\[
 L=S(S^*S)^{-1},\qquad LR=I_{P+Q},
 \qquad \|L\|\leq\sqrt2.
 \tag{40}
\]

Indeed, the strict-angle estimate from the projective Weyl paper gives
\[
 2|\operatorname{Re}\langle x,y\rangle|
 \leq \|x\|\,\|y\|
 \leq \frac12(\|x\|^2+\|y\|^2),
\]
which is exactly `(37)`.  For an explicit component decoder, if
\[
 u=pz=x+Ay,\qquad v=qz=A^*x+y,
\]
then
\[
 \begin{aligned}
 x&=(I-AA^*)^{-1}(u-Av),\\
 y&=(I-A^*A)^{-1}(v-A^*u).
 \end{aligned}
 \tag{41}
\]
Both inverses in `(41)` have norm at most
\[
 \frac1{1-\|A\|^2}=\frac43.
 \tag{42}
\]

This changes the interpretation of the compact cross-Gram obstruction.  The marginal operator
\(A\) is injective with dense proper nonclosed range and has no bounded inverse, but joint
recovery never inverts \(A\).  It inverts the positive block Gram matrix `(39)`, whose gap is
uniform.  Thus the all-prime limit has already supplied one genuine infinite, cutoff-independent
decoder of the kind demanded by the word **joint** in Section 6.

### Corollary: the Möbius inverse is another forgotten-grade artefact

For \(k\in\mathbb Z\), put
\[
 {\cal D}_k
 =
 \left\{a:
   \sum_{\substack{n>1\\\mu^2(n)=1}}n^{2k}|a_n|^2<\infty
 \right\}.
 \tag{43}
\]
Then the transverse cross-Gram is an isometric isomorphism
\[
 A:{\cal D}_k\overset{\sim}{\longrightarrow}{\cal D}_{k+1},
 \qquad
 \|Aa\|_{k+1}=\|a\|_k.
 \tag{44}
\]
Therefore its unbounded inverse on bare \(\ell^2\), like the Gamma factorial inverse in `(30)`,
is a unit translation after restoring the missing scale coordinate.  Two superficially different
nonclosed-range obstructions have the same cause: completion forgot a source grade.

### New interpretation: loss is asymmetric compression

The corpus's Gamma no-go and the projective cross-Gram no-go do not say that the infinite source
cannot be recovered.  They say that one cannot recover it after simultaneously forgetting:

1. the complementary polarization; and
2. the Gevrey/Dirichlet scale coordinate on which smoothing is a translation.

The candidate third completion is therefore not a single Hilbert norm between finite truncation
and adelic \(L^2\).  It is a **bipolar graded graph completion**: retain the two complementary
source polarizations, retain the scale index, and complete the joint graph rather than either
marginal range.  In this category:

- Gamma factorial damping and Möbius \(1/n\) damping are invertible grade shifts;
- the projective all-prime double is a uniformly stable frame;
- finite-Rees operations preserve the flat radical; and
- an off-line atom can disappear only through infinite bidegree escape or failure of Xi-conormal
  landing, not through ordinary compact smoothing.

This is the first corpus-level mechanism that simultaneously explains the finite/infinite
completion dilemma and defeats a proved marginal no-left-inverse obstruction without denying it.
It does **not** yet prove RH.  Decoder `(40)` is complex-linear on the squarefree projective
sector.  The split-recovery criterion in Section 6 additionally requires the full decoder to be
source-\(A\)-linear, star-compatible, completely contractive across every matrix grade, compatible
with the \(L^1\) and Rees degrees, and defined on the image containing the top Xi conormal.

### Revised bold conjecture: source bipolar-frame localization

`[BOLD CONJECTURE: SOURCE BIPOLAR-FRAME LOCALIZATION]`

The ordinary-prime Euler--Poisson comparison extends to the bipolar graded graph completion so
that:

1. its two source polarizations have a cutoff-independent strict cross-angle;
2. the resulting joint decoder is \(A\)-linear, star-compatible, and completely contractive;
3. it has fixed finite Gevrey--Rees bidegree; and
4. every top Xi principal-conormal jet lands in its jointly recoverable image.

If true, `(40)` supplies analytic recovery, finite-bidegree locality prevents an off-line
Hellinger--Rees pair from being sewn, and the \(A\)-linear split-recovery lemma gives vanishing of
the reduced base-change Tor.  The positive-reflection radical theorem then forces every reduced
Xi atom onto the fixed locus \(\operatorname{Re}s=1/2\), proving RH.

Hostile boundary: the strict projective angle proves only item 1 in one squarefree Hilbert sector.
It gives no \(A\)-linearity, no matrix-order theorem, no \(L^1\) control, and no Xi-conormal
attainment.  Treating `(40)` alone as an RH argument would be theatre.  Its real value is that the
previously vague demand for “joint recovery” now has an explicit infinite model and a precise
block-Gram mechanism.

## 10. Faithful dagger-split law: the missing bridge from recovery to purity

Section 9 still does not explain why a recovered off-line record must vanish.  A unitary
colligation can retain an arbitrary disk character in a faithful complementary state coordinate.
Conservation and recovery are different notions.  The required strengthening is visible from one
elementary operator identity.

### Theorem: a UCP split sends every Kadison defect into the recovery kernel

`[PAPER-PROVED — PARENT KADISON--CHOI THEORY, NEW CORPUS APPLICATION]`

Let \(A,B\) be unital \(C^*\)-algebras and let
\[
 \Phi:A\longrightarrow B,\qquad
 \Psi:B\longrightarrow A
 \tag{45}
\]
be unital completely positive maps satisfying
\[
 \Psi\Phi=I_A.
 \tag{46}
\]
For \(a\in A\), define the two Kadison defects
\[
 \begin{aligned}
 \Delta_\Phi^R(a)&=\Phi(a^*a)-\Phi(a)^*\Phi(a),\\
 \Delta_\Phi^L(a)&=\Phi(aa^*)-\Phi(a)\Phi(a)^*.
 \end{aligned}
 \tag{47}
\]
Then
\[
 \Delta_\Phi^R(a),\Delta_\Phi^L(a)\geq0,
 \qquad
 \Psi(\Delta_\Phi^R(a))
 =
 \Psi(\Delta_\Phi^L(a))
 =0.
 \tag{48}
\]

Indeed, Kadison--Schwarz for \(\Phi\) gives positivity.  Positivity of \(\Psi\) and `(46)` give
\[
 0\leq\Psi(\Delta_\Phi^R(a))
 =
 a^*a-\Psi(\Phi(a)^*\Phi(a)).
 \]
Kadison--Schwarz for \(\Psi\) gives the reverse inequality
\[
 \Psi(\Phi(a)^*\Phi(a))
 \geq
 \Psi(\Phi(a))^*\Psi(\Phi(a))
 =a^*a.
 \]
Thus the middle expression is zero.  The left defect is identical after replacing \(a\) by
\(a^*\).

Let \(I_{\rm rec}\) be the closed operator-system record generated by the defects `(47)`.  If
\(\Psi\) is faithful on its positive cone,
\[
 b\in (I_{\rm rec})_+,\quad\Psi(b)=0
 \Longrightarrow b=0,
 \tag{49}
\]
then every defect `(47)` vanishes.  Hence every \(a\) under consideration belongs to the
multiplicative domain of \(\Phi\).  Full faithfulness of \(\Psi\) on \(B_+\) makes \(\Phi\) a
star-monomorphism; only the localized condition `(49)` is needed for selected source generators.

This is stronger than a faithful complementary record.  A Blaschke/Julia unitary colligation
stores the defect conservatively but does not give a positive retraction faithful on that defect.
It therefore does not contradict `(48)`--`(49)`.

### Corollary: one dagger split controls both purity and base-change Tor

Suppose additionally that `(45)` is the positive realization of an \(A_{\rm src}\)-linear source
comparison \(T:M\to N\), its recovery is \(A_{\rm src}\)-linear, and \(N\) is
\(\Xi_{\rm red}\)-torsion-free.  Then:

1. the algebraic left inverse makes \(\operatorname{coker}T\)
   \(\Xi_{\rm red}\)-torsion-free by `(25)`--`(27)`;
2. reduced Xi base-change Tor vanishes;
3. record-faithfulness `(49)` kills the local Shilov/Kadison defect; and
4. every landed prime-angle unitary belongs to the multiplicative domain.

If on a nonzero Xi point fibre the prime generator has scalar value
\[
 \Phi(U_p)=p^{1/2-\rho},
 \tag{50}
\]
item 4 makes this scalar unitary.  Therefore
\[
 |p^{1/2-\rho}|=1
 \quad\Longrightarrow\quad
 \operatorname{Re}\rho=\frac12.
 \tag{51}
\]
Equivalently, the reduced positive radical and the reduced Tor class vanish.  Thus one
source-linear faithful dagger split would discharge the order-theoretic and homological versions
of the RH obstruction simultaneously.

### What the universal obstruction means

The corpus losses now align under one law:

```text
nonclosed Gamma or Möbius marginal
  = recovery attempted after forgetting grade/complement;

Stinespring or Poisson complementary record
  = positive Kadison defect retained in a recovery kernel;

local Shilov defect
  = positive part of that kernel after specialization;

base-change Tor / positive radical
  = reduced Xi-supported part of the same failure of source-linear splitting;

Hellinger--Rees fracture
  = asymptotic grade in which faithful finite-bidegree splitting fails;

critical line
  = locus where the prime-angle source unit is recovered multiplicatively.
```

This suggests a more exact universal statement than conservation alone:

> **Faithful dagger-split saturation.**  A source-effective completion is saturated on a
> localized principal conormal when its joint comparison admits a source-linear UCP recovery
> which is faithful on the positive complementary-record cone and finite-bidegree on the full
> Gevrey--Rees scale.  Saturation is equivalent there to simultaneous Tor-independence,
> local-Shilov exactness, and multiplicative-domain purity.

The equivalence between the first three statements requires the source comparison and the
universal positive Xi-face identifications from Section 6; it is not a theorem of bare
operator-system theory.

### Revised RH-bearing conjecture: arithmetic faithful dagger-split saturation

`[BOLD CONJECTURE: ARITHMETIC FAITHFUL DAGGER-SPLIT SATURATION]`

The ordinary-integer Euler--Poisson comparison on the bipolar graded graph completion admits,
after reduced Xi base change but before decomposition into zero fibres, a recovery satisfying:

1. source-\(A_{\rm src}\)-linearity and star compatibility;
2. UCP at every matrix reporter level;
3. the left-inverse identity `(46)` on the landed principal-conormal module;
4. faithfulness `(49)` on the prime-angle complementary-record cone;
5. fixed finite Gevrey--Rees bidegree; and
6. conservative landing of every reduced Xi conormal and integral top multiplicity jet.

Then `(48)` kills every prime-angle Kadison defect, `(51)` proves RH, and the algebraic splitting
kills the reduced Tor/positive radical.  The conjecture is strictly stronger than the bipolar
Hilbert decoder `(40)`: that decoder is bounded and cutoff-independent, but no positivity,
source-linearity, record-faithfulness, or Xi-conormal landing has been proved for it.

This formulation also supplies a finite/cofinal falsifier.  Any proposed arithmetic comparison
must produce matrix-level recovery maps whose positive kernels on the record generators shrink to
zero while their source seminorm and Gevrey--Rees bidegree remain controlled.  A persistent
positive kernel realizes an off-line Poisson storage channel rather than a proof of purity.

## 11. Source-Gram adjoint anomaly and the first-trace law

Section 9 supplies a canonical positive metric on the bipolar producer/reporter coordinates,
not merely a bounded decoder.  Put
\[
 G=S^*S=
 \begin{pmatrix}I&A\\A^*&I\end{pmatrix},
 \qquad
 A e_n={\mu(n)\over n}e_n
 \quad(\mu^2(n)=1,\ n>1).
 \tag{52}
\]
For a bounded operator \(D\) on the coordinate double, the transported operator
\(T=SDS^{-1}\) on \(P+Q\) satisfies
\[
 S^{-1}T^*S=G^{-1}D^*G.
 \tag{53}
\]
Hence \(T\) is self-adjoint in the source Hilbert space exactly when
\[
 D^*G=GD.
 \tag{54}
\]
This is standard metric-adjoint algebra.  Its source specialization exposes a new exact
realization of modular drift.

For a reflected real drift \(a\), define
\[
 D_a=
 \begin{pmatrix}aI&0\\0&-aI\end{pmatrix}.
 \tag{55}
\]
It is self-adjoint in the orthogonal coordinate sum: each reflected leg separately looks
harmless.  Its source-Gram adjoint anomaly is
\[
 \boxed{
 \Omega_a:=D_aG-GD_a
 =
 2a
 \begin{pmatrix}0&A\\-A^*&0\end{pmatrix}.}
 \tag{56}
\]

### Theorem: projective source welding detects drift exactly

`[PAPER-PROVED FROM THE PROJECTIVE MÖBIUS CROSS-GRAM THEOREM]`

On the transverse projective double:

1. \(\Omega_a=0\) if and only if \(a=0\);
2. the singular values of \(\Omega_a\) are
   \[
   {2|a|\over n},{2|a|\over n}
   \qquad(\mu^2(n)=1,\ n>1);
   \tag{57}
   \]
3. for every \(q>1\),
   \[
   \|\Omega_a\|_{\mathcal S_q}^q
   =
   2^{q+1}|a|^q
   \left({\zeta(q)\over\zeta(2q)}-1\right);
   \tag{58}
   \]
4. if \(a\neq0\), then \(\Omega_a\) is compact and belongs to every
   \(\mathcal S_q,\ q>1\), but is not trace class; and
5. its first-trace spectral residue is
   \[
   \boxed{
   \lim_{q\downarrow1}
   (q-1)\operatorname{Tr}|\Omega_a|^q
   ={4|a|\over\zeta(2)}.}
   \tag{59}
   \]

Equation `(56)` is block multiplication.  Because \(A\) is injective, `(56)` vanishes exactly
when \(a=0\).  The absolute value of its off-diagonal skew block is the direct sum of two copies
of \(2|a||A|\), which gives `(57)` and `(58)` from
\[
 \operatorname{Tr}|A|^q
 =
 \sum_{\substack{n>1\\\mu^2(n)=1}}n^{-q}
 =
 {\zeta(q)\over\zeta(2q)}-1.
\]
The pole residue at \(q=1\) is \(1/\zeta(2)\), proving `(59)`.  Equivalently, under the standard
measurability theorem for weak trace-class operators, every normalized Dixmier trace of
\(|\Omega_a|\) is \(4|a|/\zeta(2)\).

At one projective prime the cross coefficient is \(-1/p\), so the two local singular values are
\(2|a|/p\) and the exact squared Hilbert--Schmidt energy is
\[
 {8a^2\over p^2}.
 \tag{60}
\]
The local matrix identity, its zero-drift equivalence, and `(60)` are formalized unconditionally
in `HTGeometry/BipolarGramDriftAnomaly.lean`.

### What this means

Off-criticality is not merely nonunitarity of one selected scalar.  It is failure of a
reflection-odd modular observable to descend as an adjointable observable after the two
ordinary-prime source polarizations are welded by their canonical nonorthogonal Gram.

This explains several otherwise separate walls.

- **Why the raw projective \(L^2\)/Calkin image fails.**  Every \(\Omega_a\) is compact and
  Hilbert--Schmidt, even when \(a\neq0\).  Passing this unrenormalized anomaly to a Calkin quotient
  erases it identically; Hilbert energy only makes it finite.  A Calkin route can remain live only
  if it performs a source-fixed first-trace renormalization before taking the quotient, as the
  corpus's noncompact Sonin seams attempt.
- **Why the first trace is exceptional.**  The anomaly fails exactly at trace exponent one.
  This is the operator-ideal counterpart of the Allcock--Vaaler law `(9)`--`(10)`, where every
  \(L^q,\ q>1\), completion regularizes radial leakage while \(L^1\) retains its source degree.
  The two laws have the same arithmetic endpoint, though their norms have different
  normalizations.
- **Why the unsquared seam mattered but its sign did not.**  Squaring gives the finite energy
  `(58)` at \(q=2\); the unsquared first-trace residue `(59)` is linear in \(|a|\) and cannot be
  canceled by the reflected sign.  It detects displacement without requiring a one-sided Julia
  orientation.
- **Why fitted metrics are powerless.**  A parameter-dependent complementary-series metric can
  re-unitarize an off-line character.  Here \(G\) is fixed before divisor specialization by the
  projective ordinary-prime source.  Changing it with \(a\) deletes the source theorem.
- **Why the third completion needs more than a Hilbert graph.**  The bipolar graded graph must
  retain its weak first-trace residue.  The resulting target is a
  **bipolar graded weak-trace completion**: Hilbert enough for joint recovery, scale-complete
  enough to invert Gamma/Möbius grade shifts, and singular-trace sensitive enough not to erase
  `(59)`.

Equation `(56)` is the infinitesimal Gram realization of the duality--adjunction fracture
`(163)`--`(169)` in `source-localization-modular-defect-conservation-law.md`.  Inverse transport
and positive adjunction can coincide on the welded graph only when this anomaly vanishes.

### New RH-bearing source theorem

`[BOLD CONJECTURE: SOURCE-GRAM ADJOINT LANDING]`

The Euler-decorated Calderón/Poisson comparison lands the reduced Xi principal conormal, before
zero-fibre decomposition, in the bipolar graded weak-trace graph so that:

1. the two functional-equation legs have the projective source Gram `(52)`;
2. the centered real modular clock restricts on every reflected conormal orbit to `(55)`;
3. that clock is symmetric on the strict arithmetic graph by the common finite-cell Green
   identity; and
4. completion and reduced Xi specialization preserve the weak first-trace residue and every
   multiplicity jet.

Clause 3 and `(53)` give \(\Omega_a=0\).  The theorem above then gives \(a=0\) on every landed
reduced Xi atom, hence RH.  Equivalently, clause 4 makes `(59)` a source-conserved nonnegative
localization anomaly, while the finite-cell dagger identity makes its source value zero.

This is not yet a proof.  Clauses 1--2 identify the exact nonorthogonal metric and observable
required; clause 3 is the arithmetic Green/adjoint theorem; clause 4 is the strict
completion--specialization theorem.  Existing high-shell work proves the conormal covariance but
not this landing, and the projective paper proves `(52)` but not its Poisson/Tate identification.
The gain is a scalar-free target: no inequality, chosen zero metric, or zero-space
self-adjoint operator is requested.  One must prove equality of one source-defined adjoint
structure across one source-defined strict graph.

### Hostile boundary

The abstract implication “self-adjoint reflected weights on nonorthogonal eigenspaces force equal
weights” is elementary and not new.  Metric operators, quasi-Hermitian similarity, weak
Schatten ideals, and Dixmier traces are parent mathematics.  The source-specific candidate-new
content is the exact conjunction:
\[
 \text{projective Möbius cross-Gram}
 \Longrightarrow
 \text{drift anomaly `(56)`}
 \Longrightarrow
 \text{squarefree first-trace residue `(59)`}.
\]
It materially advances the mechanism only if the Poisson/Tate comparison proves
SOURCE-GRAM ADJOINT LANDING.  Without that theorem, `(56)` is another faithful reporter of the
already-known drift and must not be advertised as an RH proof.

## 12. Literature boundary

Parent mathematics includes:

- Allcock--Vaaler place-space \(L^1\) geometry and the product-formula hyperplane;
- Kakutani equivalence and singularity of infinite product measures;
- Choi multiplicative domains and Stinespring dilation;
- Rees filtrations, moderate/rapid Stokes structures, and irregular Riemann--Hilbert theory;
- operator-system matrix order, \(C^*\)-envelopes, and local Shilov boundaries; and
- strict determinant/differential-character and arithmetic regulator theories.

Targeted searches found no theorem identifying one zeta-centered drift simultaneously through
`(5)`, `(8)`, `(10)`, `(12)`, and `(13)`, or deriving its vanishing from a strict
ordinary-prime Euler--Gamma principal-source realization.  This is a noncollision result, not a
priority certificate.  Each individual equivalence remains parent or already proved in the
corpus; candidate novelty is the faithful realization dictionary and the source-effectivity law.
The general strict-angle/closed-sum and block-Gram inversion used in `(37)`--`(42)` are classical
two-subspace Hilbert geometry.  Targeted searches found no prior occurrence of their
source-specific combination with the projective Möbius diagonal \(\mu(n)/n\), its Dirichlet-scale
translation `(44)`, and the Euler--Poisson/Xi recovery problem.
The Kadison--Schwarz inequalities and multiplicative-domain conclusion behind `(47)`--`(49)` are
classical.  Targeted searches found related UCP recovery/error-correction and faithful conditional
expectation theory, but no use of the faithful positive split to identify simultaneously the
ordinary-prime Xi multiplicative-domain defect, reduced base-change Tor, local Shilov defect, and
Hellinger--Rees grade.  Novelty is claimed, at most, for that source-specific conjunction and not
for the operator lemma.

Primary references:

- Daniel Allcock and Jeffrey D. Vaaler, *A Banach space determined by the Weil height*,
  <https://arxiv.org/abs/0808.1038>.
- Shizuo Kakutani, *On equivalence of infinite product measures*, Annals of Mathematics 49
  (1948), 214--224.
- M.-D. Choi, *A Schwarz inequality for positive linear maps on C-star algebras*,
  Illinois Journal of Mathematics 18 (1974), 565--574.
- Ali S. Kavruk, Vern I. Paulsen, Ivan G. Todorov, and Mark Tomforde,
  *Quotients, exactness, and nuclearity in the operator system category*,
  <https://arxiv.org/abs/1008.2811>.
- Ian Koot, *A note on the minimal tensor product and the C-star-envelope of operator systems*,
  <https://arxiv.org/abs/2202.12144>.
- Mark Greenfield, Matilde Marcolli, and Kevin Teh,
  *Type III sigma-spectral triples and quantum statistical mechanical systems*,
  <https://arxiv.org/abs/1305.5492>.
- Jean-Pierre Antoine and Camillo Trapani,
  *Metric operators, generalized hermiticity and lattices of Hilbert spaces*,
  <https://arxiv.org/abs/1409.3497>.
- Magnus Goffeng and Alexandr Usachev,
  *Dixmier traces and residues on weak operator ideals*,
  <https://arxiv.org/abs/1710.08260>.

## Log

- 2026-07-30 — Identified off-critical location, positive mixedness, product-state singularity,
  \(L^1\) source-memory leakage, Rees reflection fracture, and positive-reflection radical as
  faithful realizations of one centered source modular drift.  Replaced the search for an
  additional selector by source-effective conservation of the zero arithmetic degree.
- 2026-07-30 — Defined the six-channel Hausdorff source completion `(17)` and isolated complete
  matricial finite-packet transition bound `(24)` as the first non-parent theorem required for
  Xi conormal attainment and RH.
- 2026-07-30 — Corrected global-conservation overreach: reflected off-line drifts cancel in total.
  Isolated strict localization--completion interchange and reduced base-change Tor-independence
  as the exact law needed to make zero arithmetic degree hold on each Xi atom.
- 2026-07-30 — Separated Gamma factorial depth from prime-Rees depth.  The completed Gamma
  reporter is a unit shift on its factorial Hilbert scale, and every fixed finite-bidegree
  Gevrey--Rees operation preserves the all-orders-flat radical.  Therefore an off-line reflected
  conormal forces infinite Rees order, cutoff-dependent escape through unbounded Gevrey grade, or
  loss of conormal faithfulness specifically in the Euler-to-Poisson continuation comparison.
  Rejected the false shortcut from idempotent rigidity: a conormal is a graded line and may carry
  nonzero reflected weight until strict localization is proved.
- 2026-07-30 — Extracted a uniform all-prime joint decoder from the projective Möbius
  cross-polarization theorem.  Although the marginal diagonal \(\mu(n)/n\) has no bounded inverse,
  the bipolar block Gram matrix is bounded below by \(1/2\), so the two projections jointly recover
  their closed sum with decoder norm at most \(\sqrt2\).  Identified both Möbius and Gamma damping
  as invertible translations after restoring their forgotten scale coordinates.  Proposed the
  bipolar graded graph completion and isolated the exact remaining upgrades: source-linearity,
  complete matrix contractivity, finite Gevrey--Rees bidegree, and Xi-conormal landing.
- 2026-07-30 — Corrected joint-recovery overreach.  A conservative record or unitary dilation
  permits every off-line Poisson/Blaschke storage state.  Proved that a UCP left inverse sends both
  Kadison defects into its positive kernel; faithfulness on the record cone therefore forces
  multiplicative-domain purity.  Combined this with the source-linear split lemma: one faithful
  dagger split would kill both reduced Xi base-change Tor and the prime-angle Kadison defect.
  Isolated arithmetic faithful dagger-split saturation as the unified remaining theorem.
- 2026-07-30 — Derived the projective source-Gram adjoint anomaly
  \(\Omega_a=2a\left(\begin{smallmatrix}0&A\\-A^*&0\end{smallmatrix}\right)\).
  Its singular values are two copies of \(2|a|/n\) on squarefree \(n>1\), so it lies in every
  Schatten class above one, is not trace class off line, and has exact first-trace residue
  \(4|a|/\zeta(2)\).  This identifies compact/Hilbert blindness and \(L^1\)/first-trace memory as
  two endpoint shadows of one source welding law.  Proposed the bipolar graded weak-trace
  completion and isolated source-Gram adjoint landing as the remaining RH-bearing theorem.
