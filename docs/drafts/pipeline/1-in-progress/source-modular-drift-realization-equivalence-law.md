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

## 12. Half-density dagger and conditional first-trace transgression

The projective coefficient \(\mu(n)/n\) is not merely a fitted cross-Gram entry.  It is forced by
the adjoint of the actual arithmetic dilation representation at critical half-density.

For real \(\sigma\), put
\[
 {\cal H}_\sigma
 =
 L^2\!\left(\mathbb R_{>0},x^{2\sigma}{dx\over x}\right),
 \qquad
 (D_n f)(x)=f(nx).
 \tag{61}
\]
A change of variables gives
\[
 \|D_n f\|_{{\cal H}_\sigma}^2
 =n^{-2\sigma}\|f\|_{{\cal H}_\sigma}^2,
 \qquad
 \boxed{D_n^*=n^{-2\sigma}D_{1/n}.}
 \tag{62}
\]
Consequently, for every finite dilation polynomial,
\[
 \left(\sum_n c_nD_n\right)^*
 =
 \sum_n \overline{c_n}\,n^{-2\sigma}D_{1/n}.
 \tag{63}
\]
Under inverse-basis identification \(D_{1/n}\leftrightarrow e_n\), the linear coefficient part
of the dagger, after the canonical conjugation, is
\[
 B_\sigma e_n=n^{-2\sigma}e_n.
 \tag{64}
\]
If \(M_\mu e_n=\mu(n)e_n\), then the critical Möbius-dagger symbol is
\[
 \boxed{M_\mu B_{1/2}e_n={\mu(n)\over n}e_n=Ae_n.}
 \tag{65}
\]
Thus `(52)` is the coefficient symbol of the critical half-density adjoint applied to the
Möbius-twisted dilation packet.  This is an exact coefficient-level Poisson/Wold identification,
not yet an equality of the projective synthesis map with the full adelic Poisson transform.

Reflection sends \(\sigma\) to \(1-\sigma\).  On any coefficient \(n>1\),
\[
 B_\sigma=B_{1-\sigma}
 \quad\Longleftrightarrow\quad
 \sigma={1\over2},
 \qquad
 B_{1-\sigma}B_\sigma^{-1}e_n=n^{4\sigma-2}e_n.
 \tag{66}
\]
For \(\sigma=\tfrac12+a\), the relative coefficient modular operator is \(n^{4a}\), or \(n^{-4a}\)
in the opposite comparison direction.  This gives a direct source meaning to the drift in
`(55)`: it is the logarithmic failure of the two reflected coefficient daggers to agree.

There is a second, nonlinear realization which joins the Wold first trace to the
Kadison--Schwarz defect.  On \(\ell^2(\mathbb N_{\geq1})\), let
\[
 S_qe_n=e_{qn},\qquad
 E_q=I-S_qS_q^*,\qquad
 Qe_n={1\over n}e_n.
 \tag{67}
\]
Suppose \(0\ne\xi\in\ell^2(\mathbb N_{\geq1})\) and
\[
 S_q^*\xi=z\xi,\qquad |z|<1,
 \tag{68}
\]
and write \(\omega_\xi(T)=\langle T\xi,\xi\rangle\).  Decompose every integer uniquely as
\(q^km\) with \(q\nmid m\).  Equation `(68)` makes the squared coefficients on each \(q\)-adic
ray a geometric progression of ratio \(|z|^2\).  Summing first along each ray gives
\[
 \boxed{
 {\omega_\xi(E_qQ)\over\omega_\xi(Q)}
 =
 1-{|z|^2\over q}.}
 \tag{69}
\]
The quotient is independent of the distribution of \(\xi\) among the \(q\)-free wandering
vectors.

On the other hand, the literal arithmetic first-trace exhaustion satisfies
\[
 {\operatorname{Tr}_{n\leq N}(E_qQ)
  \over
  \operatorname{Tr}_{n\leq N}(Q)}
 \longrightarrow
 1-{1\over q}.
 \tag{70}
\]
Combining `(69)` and `(70)` gives the **conditional first-trace--Kadison transgression law**
\[
 \boxed{
 {\omega_\xi(E_qQ)\over\omega_\xi(Q)}
 -
 \left(1-{1\over q}\right)
 =
 {1-|z|^2\over q}.}
 \tag{71}
\]
The right side is \(q^{-1}\) times the right Kadison defect of the scalar compression
\(S_q\mapsto\overline z\).  Equivalently, for the balanced density operator
\[
 {\cal B}_q=E_qQ-\left(1-{1\over q}\right)Q,
 \tag{72}
\]
the Wold covariance in `(67)` gives the exact commutator identity
\[
 \boxed{
 {\cal B}_q
 =
 S_q^*QS_q-QS_qS_q^*
 =
 [S_q^*,QS_q].}
 \tag{72a}
\]
Indeed, \(S_q^*QS_q=q^{-1}Q\) and \(QS_qS_q^*=Q(I-E_q)\).  Therefore every cyclic singular trace
on the weak first-trace ideal annihilates \({\cal B}_q\).  Its vanishing source symbol is not an
asymptotic coincidence: it is the trace of a literal arithmetic commutator.

By contrast, every interior Wold eigenstate is noncyclic on this commutator:
\[
 {\omega_\xi({\cal B}_q)\over\omega_\xi(Q)}
 ={1-|z|^2\over q}>0.
 \tag{73}
\]
Hence completion and principal first-trace specialization fail to commute by exactly the
multiplicative-domain curvature.  Equivalently, the missing source theorem is preservation of
the cyclic residue class under principal-conormal localization.

For the right-half centered Riemann character
\[
 z_q(\rho)=q^{1/2-\rho},
 \tag{74}
\]
equation `(71)` becomes
\[
 {\omega_\rho(E_qQ)\over\omega_\rho(Q)}
 -
 \left(1-{1\over q}\right)
 =
 {1-q^{1-2\operatorname{Re}\rho}\over q}.
 \tag{75}
\]
For \(q=p\) prime, conditioning the Wold eigenstate by \(Q\) gives the full valuation law
\[
 \mathbb P_{\rho,Q}(v_p=k)
 =
 (1-p^{-2\sigma})p^{-2\sigma k},
 \qquad \sigma=\operatorname{Re}\rho.
 \tag{75a}
\]
Indeed, the unconditioned squared eigenvector amplitudes have ratio
\(|z_p(\rho)|^2=p^{1-2\sigma}\), and \(Q\) contributes one further factor \(p^{-1}\).
With \(c=\tfrac12-\sigma\), `(75a)` is exactly the already-proved Kakutani-sector law
\(\mu_{p,c}\) in `prime-valuation-kakutani-polar-third-completion.md`.  Thus Poisson diffusion,
prime-valuation sector change, and Wold conditional density are literally the same localized
state.  The geometric measure and its Kakutani wall are corpus-known; the new bridge here is the
typed \(Q\)-conditioned eigenstate realization and the exact excess identity `(71)`.

For \(\operatorname{Re}\rho>\tfrac12\), the right side is positive.  Summed over ordinary primes,
it diverges:
\[
 \sum_p{1-p^{1-2\operatorname{Re}\rho}\over p}=+\infty,
 \tag{76}
\]
because \(\sum_pp^{-1}\) diverges while
\(\sum_pp^{-2\operatorname{Re}\rho}\) converges.  At the critical line every local excess
vanishes.

The infinitesimal form also recovers the projective source Gram.  With
\(\operatorname{Re}\rho=\tfrac12+a\),
\[
 {d\over da}\bigg|_{a=0}
 {1-p^{-2a}\over p}
 ={2\log p\over p}.
 \tag{77}
\]
At a prime, \(Ae_p=-p^{-1}e_p\); after applying the logarithmic prime clock, the magnitude of the
linearized off-diagonal anomaly `(56)` is the same \(2\log(p)/p\).  Thus the projective
source-Gram anomaly is the oriented linearization of the nonlinear first-trace--Kadison
transgression.

### Narrower RH-bearing source theorem

`[BOLD CONJECTURE: XI WOLD CONDITIONAL-DENSITY BASE CHANGE]`

The Euler--Gamma/BV/co-Poisson comparison carries the principal Xi conormal, before zero-fibre
decomposition, to the relative Wold extension so that:

1. the reciprocal occupation clock and Wold boundary are the literal \(Q\) and \(E_q\) in
   `(67)`;
2. the BV off-multiple principal-normal ratio \(1-q^{-1}\) is the localized conditional density
   in `(69)`, not merely an equal scalar in a separate model;
3. reduced Xi specialization preserves the cyclic logarithmic residue class, so the commutator
   `(72a)` remains zero in the localized principal symbol; and
4. every nonzero right-half Xi conormal gives the centered Wold character `(74)` without losing
   its top multiplicity jet.

Then `(71)` forces \(1-|z_q(\rho)|^2=0\), and `(74)` gives
\(\operatorname{Re}\rho=\tfrac12\).  Functional-equation reflection excludes the left half, so
the conjecture implies RH.

This is strictly narrower than demanding a faithful UCP split on the whole source operator
system.  It asks only that one source-fixed conditional first-trace density commute with
principal-conormal localization.  It is also load-bearing: equality of the standalone Wold and
BV coefficients \(1-q^{-1}\) does not prove clause 2.  One must construct the typed relative
state or conormal functional on the common span of \(Q\) and \(E_qQ\).  A plain Hilbert
completion, a boundary quotient killing \(Q\), or a zero-fitted state invalidates the argument.

The critical fibre is necessarily singular: a nonzero \(\ell^2\) eigenvector in `(68)` has
\(|z|<1\), so `(73)` is strictly positive.  Source-density preservation can occur only in the
boundary limit \(|z|\to1\), exactly where the scalar Hilbert eigenvector disappears and a
module/conormal boundary fibre is required.  This is the explicit one-prime form of the third
completion problem.

## 13. Universal law: source-effective base change conserves modular dimension

The preceding identities admit a stronger interpretation than either a Toeplitz boundary
selector or a comparison of two KMS sectors.

On one \(q\)-adic ray, let \(V e_k=e_{k+1}\).  The reciprocal occupation density restricts,
up to a constant on the \(q\)-free base point, to
\[
 Q_qe_k=q^{-k}e_k.
 \tag{78}
\]
Thus the source weak first-trace functional has the fixed twisted-cyclic ratio
\[
 {\rm src}(VV^*)=q^{-1}{\rm src}(V^*V).
 \tag{79}
\]
Equivalently, for the dynamics
\[
 \alpha_t(V)=q^{it}V,
 \tag{80}
\]
the source functional has modular parameter \(\beta_{\rm src}=1\).  Equation `(79)` is the
one-generator KMS relation on the analytic Toeplitz core.  This statement concerns the fixed
source weight; it is not the false claim that every coherent Wold vector state is a KMS state.

For a Wold eigenvector with character \(z\), condition by \(Q\) and then restrict to the
valuation diagonal.  The resulting geometric law has ratio
\[
 r={|z|^2\over q}.
 \tag{81}
\]
Gauge-averaging its phase gives the canonical diagonal Gibbs/KMS marginal with
\[
 q^{-\beta_{\rm con}}=r.
 \tag{82}
\]
For the centered Riemann character `(74)`,
\[
 r=q^{-2\operatorname{Re}\rho},
 \qquad
 \boxed{\ \beta_{\rm con}=2\operatorname{Re}\rho.\ }
 \tag{83}
\]
The distinction between the coherent state and its gauge-invariant KMS marginal is
load-bearing.  Only the radial marginal is used below.

`[PAPER-PROVED] [TOEPLITZ_KMS_VALUATION_LAW]`

More generally, let \(\varphi_\beta\) be a normalized KMS functional on the analytic
one-isometry Toeplitz core for `(80)`.  Then
\[
 \varphi_\beta(V^kV^{*k})=q^{-\beta k},
 \qquad
 \varphi_\beta\!\left(
   V^kV^{*k}-V^{k+1}V^{*(k+1)}
 \right)
 =(1-q^{-\beta})q^{-\beta k}.
 \tag{83a}
\]
Indeed, the KMS relation moves \(V^k\) past \(V^{*k}\), while
\(\alpha_{i\beta}(V^k)=q^{-\beta k}V^k\) and \(V^{*k}V^k=1\).  Subtracting
successive range projections gives the second identity.  Thus the entire valuation law, not
only its first cylinder, is the modular twist.

For commuting multiplicative isometries \(S_n\) with
\(\alpha_t(S_n)=n^{it}S_n\), the same proof gives
\[
 \varphi_\beta(S_nS_n^*)=n^{-\beta}.
 \tag{83b}
\]
In the multiplication Nica/Wold representation, coprime range projections intersect as the
range projection of the product.  Hence the differences
\(S_p^kS_p^{*k}-S_p^{k+1}S_p^{*(k+1)}\) are the valuation-shell projections and
`(83a)`--`(83b)` recover the product Gibbs laws.  This standard Toeplitz--KMS calculation
explains why one preserved twist controls every prime and every valuation layer.

### Additive Haar and multiplicative Gibbs are the same modular exponent

Let \(p\) be prime.  Additive Haar probability on \(\mathbb Z_p\) has valuation law
\[
 \nu_{p,1}(v_p=k)=(1-p^{-1})p^{-k}.
 \tag{84}
\]
For \(\beta>0\), define its radial Gibbs tilt by
\[
 \nu_{p,\beta}(v_p=k)=(1-p^{-\beta})p^{-\beta k},
 \tag{85}
\]
with Haar-uniform conditional distribution on each unit shell.

`[PAPER-PROVED] [ADDITIVE_HAAR_MULTIPLICATIVE_GIBBS_RIGIDITY]`

The following are equivalent:

1. \(\nu_{p,\beta}\) is invariant under additive translations of \(\mathbb Z_p\);
2. \(\nu_{p,\beta}\) is additive Haar probability;
3. \(\nu_{p,\beta}(p\mathbb Z_p)=p^{-1}\);
4. \(\beta=1\).

Indeed, translation invariance makes a probability on the compact additive group
\(\mathbb Z_p\) its unique Haar probability.  Haar gives mass \(p^{-1}\) to the index-\(p\)
subgroup \(p\mathbb Z_p\), whereas `(85)` gives \(p^{-\beta}\).  Since \(p>1\), equality is
equivalent to \(\beta=1\).  The converse is `(84)`.

For the product law on \(\widehat{\mathbb Z}=\prod_p\mathbb Z_p\), invariance even only under
the dense translation subgroup \(\mathbb Z\) implies invariance under
\(\widehat{\mathbb Z}\), hence Haar probability and \(\beta=1\).  Off the critical parameter,
the product Gibbs law is the already-proved Kakutani-singular sector.

Combining `(83)` with this rigidity gives the exact local selector
\[
 \boxed{
 \text{Riemann conormal Born marginal retains the source modular class}
 \quad\Longrightarrow\quad
 2\operatorname{Re}\rho=1.}
 \tag{86}
\]
One prime is enough once the comparison is typed.  The all-prime tower is not needed for the
last algebraic implication; it is needed to construct the source comparison without fitting it
to a divisor point.

Equation `(71)` is precisely the cylinder-level failure of `(86)`:
\[
 \frac{\omega_\rho({\cal B}_p)}{\omega_\rho(Q)}
 =
 p^{-1}-p^{-2\operatorname{Re}\rho}.
 \tag{87}
\]
Thus the cyclic commutator, the additive Haar index, the Wold conditional density, and the
KMS temperature are not analogous reporters.  They are four evaluations of one modular
exponent.

### Modular-dimension conservation

The common law suggested by the corpus is:
\[
 \boxed{
 \begin{gathered}
 \textbf{source-effective base change conserves modular dimension;}\\
 \text{a spectral specialization may change phase and representation,}\\
 \text{but it cannot retune the twist of the source cyclic class.}
 \end{gathered}}
 \tag{88}
\]

For an equivariant algebraic base change, preservation of a fixed twisted-cyclic relation is
formal: if
\[
 \tau(ab)=\tau(b\,\vartheta(a))
 \tag{89}
\]
and the base-change map intertwines \(\vartheta\), then the specialized nonzero functional
satisfies the same relation.  The Riemann difficulty is not `(89)`.  It is constructing the
strict meromorphic/BV conormal as that base change after cofinal completion, while retaining
its positive \(Q\)-Born marginal and every multiplicity jet.

This interpretation explains why the earlier mechanisms repeatedly selected the same locus:

```text
half-density dagger:
  the source modular exponent is one;

Wold interior/boundary:
  beta != 1 is a contraction state; beta = 1 reaches the source boundary;

Kakutani:
  retuning beta changes the all-prime measure sector;

first-trace commutator:
  p^(-1)-p^(-beta) is the local modular-class defect;

projective source Gram:
  2 log(p)/p is the oriented tangent of that defect at beta=1;

positive maximum-valuation shells:
  their reference law is the pushforward of the beta=1 Haar valuations;

finite truncation:
  sees the index p only up to terminal leakage;

ambient adelic L2:
  retains Haar modularity but loses the divisor conormal;

generalized-prime off-line systems:
  may reproduce scalar Euler, reflection, orientation, and HT data, but their
  off-line Born functional cannot be the specialization of this fixed ordinary-integer
  modular class.
```

Hypertranscendence has a precise supporting role.  The inverse-limit law of
`analytic-grassmann-lattice-dirichlet-fields` proves that a genuinely HT prime-profile carrier
cannot be controlled through a uniformly bounded family of finite clock annihilators.  Hence
the comparison in `(88)` cannot be certified by any fixed finite jet, finite prime packet, or
finite cyclic reporter.  It must be a class in the complete twisted-cyclic/Rees source object.
Hypertranscendence does not itself make that class positive or conservative.

### The reduced BV relation is already a Hochschild boundary

The first finite source-to-cyclic square does not need to be conjectured.  In the notation of the
typed renewal `(4j1)`--`(4j6)` in
`source-curved-prime-torus-conormal-temperedness`, put
\[
 r_{q,j}:=c_j-(1-q^{-1})p_j.
 \tag{90}
\]
The proved BV principal-conormal relation gives
\[
 J(r_{q,j})=0.
 \tag{91}
\]
On the two-dimensional reporter span define
\[
 {\cal W}_{q,j}(p_j)=Q,
 \qquad
 {\cal W}_{q,j}(c_j)=E_qQ.
 \tag{92}
\]
Then `(72)`--`(72a)` give the exact identity
\[
 \boxed{
 {\cal W}_{q,j}(r_{q,j})
 =
 E_qQ-(1-q^{-1})Q
 =
 [S_q^*,QS_q]
 =
 b(S_q^*\otimes QS_q),}
 \tag{93}
\]
where \(b(a_0\otimes a_1)=a_0a_1-a_1a_0\) is the degree-one Hochschild
boundary.

`[PAPER-PROVED] [BV_REDUCED_RELATION_TO_HOCHSCHILD_BOUNDARY]`

Thus the scalar BV coefficient, the balanced density operator, and cyclicity are already one
finite commuting square:
\[
 \begin{array}{ccc}
 r_{q,j} & \xmapsto{\ {\cal W}_{q,j}\ } & b(S_q^*\otimes QS_q)\\
 \big\downarrow J && \big\downarrow HH_0\\
 0 & \longmapsto & 0.
 \end{array}
 \tag{94}
\]
This is a value-level reporter square, not yet a chain map on the full Euler--Gamma/co-Poisson
source complex.  Its significance is that it fixes the required extension uniquely on the first
nontrivial relation.  An off-line conormal Born functional evaluates the upper-right term as
`(87)`, so its failure to descend through `(94)` is exactly its modular-dimension defect.

The first producer is therefore no longer “find some cyclic cocycle.”  It is:

> extend the concrete maps `(92)` compatibly to the finite Kummer/BV source complex and the
> relative Hochschild complex, then prove that their cofinal strict base change carries the
> positive conormal marginal through \(HH_0\).

If no such extension exists, the obstruction must already appear as failure of a specific
higher-face relation, positivity of the induced diagonal functional, or prime-enlargement
compatibility.  Those are falsifiable finite-stage failures, not an RH-equivalent norm condition.

### Sharpened RH-bearing source theorem

`[BOLD CONJECTURE: XI TWISTED-CYCLIC MODULAR-DIMENSION CONSERVATION]`

Before divisor specialization, the ordinary-prime Euler--Gamma/Tate--co-Poisson source
constructs a strict relative twisted-cyclic class on the Wold--Toeplitz/Rees extension with:

1. modular twist fixed by \(Q\), so its \(p\)-ray ratio is \(p^{-1}\);
2. BV principal-normal restriction equal to the already-proved off-multiple renewal;
3. strict equivariant base change to every nonzero Xi principal conormal and every
   multiplicity jet;
4. positive gauge-averaged \(Q\)-Born restriction equal to the valuation marginal of the
   centered conormal character \(p^{1/2-\rho}\).

Then `(83)`, twist preservation, `(93)`, and `(86)` prove RH.

This is narrower than a faithful UCP recovery on the whole source operator system and more
structured than imposing essential unitarity on a chosen fibre.  The producer is one global
twisted-cyclic class and one source-first base-change theorem.  Clause 4 is indispensable:
the complex BV residue is a linear conormal reporter, not automatically the square of a
Hilbert amplitude.  Calling it a Born state without constructing the positive restriction
would repeat the projective-source-square error.

### New consequences and hostile audit

1. **One-prime deduction, all-prime construction.**  Any one typed prime comparison forces
   criticality, but choosing that comparison after reading \(\rho\) is circular.  The cofinal
   ordinary-prime class is what makes the construction source-defined.
2. **Multiplicity is radial-neutral.**  Analytic order multiplies the residue amplitude but
   does not change `(81)`--`(83)`.  Every retained top jet has the same modular dimension.
3. **Critical fibres must be singular.**  At \(\beta=1\), \(|z|=1\); the coherent Wold vector
   leaves \(\ell^2\).  Any successful completion must therefore keep the conormal as a boundary
   functional/module fibre, not as an ordinary eigenvector.
4. **Functional equation is a reflection, not a producer.**  It sends
   \(\beta\mapsto2-\beta\).  Conservation of the source modular exponent, not reflection alone,
   fixes \(\beta=1\).
5. **The all-prime defect is macroscopic.**  For \(\beta>1\),
   \(\sum_p(p^{-1}-p^{-\beta})=+\infty\); for \(0<\beta<1\) it diverges with the opposite sign.
   No trace-density limit may average away one off-line conormal.
6. **No full-KMS overclaim.**  The unaveraged coherent conormal state has phase coherences and
   need not be KMS.  Only its gauge-invariant valuation marginal has parameter `(83)`.
7. **No automatic cyclic-residue shortcut.**  Laurent residues of a meromorphic family of
   twisted traces inherit twisted cyclicity, but the present BV scalar residue has not yet been
   constructed as such a trace-valued family.  That construction is the first proof-bearing
   obstacle.
8. **No additive-Haar overclaim.**  The proved BV ratios recover Haar valuation cylinders.
   Full translation invariance on every residue class is stronger and is not asserted for the
   Xi conormal before the twisted-cyclic comparison is built.

`[OPEN CORE: XI_BV_TWISTED_CYCLIC_BASE_CHANGE]`

Extend `(92)` from the reduced one-relation reporter square `(94)` to a morphism from the finite
Kummer/BV source complex into the relative Hochschild complex.  Its meromorphic trace boundary
must have the literal occupation twist, its Laurent boundary must be the existing BV principal
conormal, and its positive gauge-diagonal restriction must be the \(Q\)-conditioned Wold law.
Then prove compatibility under prime enlargement and strict Rees completion.  A failure must
exhibit one of five exact obstructions: failure of a higher source relation, loss of the twist, a
nonpositive diagonal restriction, a killed multiplicity jet, or nonclosable cofinal base change.

## 14. Correction: finite algebraic flatness, controlled curvature at infinity

The finite source-to-Hochschild problem is less obstructed than the open core above suggests.
The one-prime transgression has a canonical two-prime extension.

Let \(S_ne_k=e_{nk}\), \(P_n=S_nS_n^*\), and \(Qe_k=k^{-1}e_k\).  For coprime \(m,n\), put
\[
 {\cal B}_n=(n^{-1}1-P_n)Q,
 \qquad
 h_n=S_n^*\otimes QS_n,
 \qquad
 h_{n\mid m}=S_n^*\otimes P_mQS_n .
 \tag{95}
\]
The degree-one Hochschild boundary satisfies
\[
 b(h_n)={\cal B}_n,
 \qquad
 b(h_{n\mid m})=n^{-1}P_mQ-P_{mn}Q.
 \tag{96}
\]
Indeed, \(S_n^*QS_n=n^{-1}Q\), while coprimality gives the required double commutation
and \(P_mP_n=P_{mn}\).

Define the two ordered transgressions
\[
 H_{m\to n}:=n^{-1}h_m+h_{n\mid m},
 \qquad
 H_{n\to m}:=m^{-1}h_n+h_{m\mid n}.
 \tag{97}
\]
Then
\[
 \boxed{\quad
 b(H_{m\to n})=b(H_{n\to m})
 =(mn)^{-1}Q-P_{mn}Q={\cal B}_{mn}.
 \quad}
 \tag{98}
\]
Thus their difference is a Hochschild one-cycle.  It is in fact a boundary.

`[PAPER-PROVED] [TWO_PRIME_BV_HOCHSCHILD_FACE_FLATNESS]`

Write \(U=S_m\), \(V=S_n\), \(e=P_m\), \(f=P_n\), and \(x=Q\).  A direct application of
\[
 b(a_0\otimes a_1\otimes a_2)
 =
 a_0a_1\otimes a_2-a_0\otimes a_1a_2+a_2a_0\otimes a_1
 \tag{99}
\]
gives, modulo degree-two Hochschild boundaries,
\[
 H_{m\to n}
 \sim
 h_{mn}+f\otimes ex,
 \qquad
 H_{n\to m}
 \sim
 h_{mn}+e\otimes fx.
 \tag{100}
\]
For completeness, witnesses for the first congruence are
\[
 U^*V^*\otimes V\otimes QU,
 \qquad
 V^*\otimes P_UQ\otimes V,
 \tag{100a}
\]
with coefficient \(n^{-1}\) on the first boundary; the second congruence is obtained by
interchanging \(U,m,e\) with \(V,n,f\).  Expanding `(99)`, using
\[
 U^*QU=m^{-1}Q,\qquad V^*QV=n^{-1}Q,
 \tag{100b}
\]
and the double-commutation relations gives `(100)` term by term.
The residual cycle is therefore
\[
 C_{e,f,x}=f\otimes ex-e\otimes fx.
 \tag{101}
\]
For commuting \(a,e\) with \(e^2=e\), define
\[
 R(a,e)
 :=
 2ae\otimes e\otimes e-a\otimes e\otimes e .
 \tag{102}
\]
Then \(bR(a,e)=a\otimes e\).  Since \(e,f,x\) commute, `(99)` also gives
\[
\begin{aligned}
 C_{e,f,x}
 &=
 xf\otimes e-xe\otimes f\\
 &\quad-b(f\otimes e\otimes x)+b(e\otimes f\otimes x),
\end{aligned}
\tag{103}
\]
and hence
\[
 C_{e,f,x}
 =
 b\!\left(
 R(xf,e)-R(xe,f)-f\otimes e\otimes x+e\otimes f\otimes x
 \right).
 \tag{104}
\]
Equations `(100)`--`(104)` prove
\[
 \boxed{\quad H_{m\to n}-H_{n\to m}\in bC_2. \quad}
 \tag{105}
\]
Adjacent transpositions consequently make the degree-one transgression of every finite
squarefree prime packet independent of prime order in Hochschild homology.

The finite-packet formula is explicit.  For an ordering
\(\pi=(p_1,\ldots,p_r)\), put
\[
 M_j=\prod_{i\leq j}p_i,\qquad M_0=1,
 \tag{105a}
\]
and
\[
 H_\pi
 :=
 \sum_{j=1}^r
 \left(\prod_{k=j+1}^rp_k^{-1}\right)
 h_{p_j\mid M_{j-1}} .
 \tag{105b}
\]
Repeated use of `(96)` telescopes to
\[
 b(H_\pi)=M_r^{-1}Q-P_{M_r}Q={\cal B}_{M_r}.
 \tag{105c}
\]
Swapping two adjacent primes replaces \(Q\) in `(95)`--`(105)` by the commuting prefix
weight \(P_{M_{j-1}}Q\) and multiplies the result by the reciprocal scalar of the suffix.
The same primitive `(102)`--`(104)` therefore fills the swapped face.  Since adjacent
transpositions generate every permutation:
\[
 \boxed{\quad
 H_\pi-H_{\pi'}\in bC_2
 \quad\text{for all orderings of one finite squarefree packet.}
 \quad}
 \tag{105d}
\]

`[PAPER-PROVED] [FINITE_PACKET_BV_HOCHSCHILD_PATH_FLATNESS]`

This does **not** yet construct a coherently filled cubical chain map in every degree: braid and
higher-face compatibility require explicit higher homotopies.  It does close the first possible
rank-two obstruction.  In particular, the finite Boolean cylinder directions are algebraically
flat after their complementary record is retained.

The noncommutative algebraic core `(99)` and `(102)`--`(104)` is formalized unconditionally in
`formal/GaloisForLFunctions/HTGeometry/LowDegreeHochschildFaceFlatness.lean`.  The Lean module
defines the genuine degree-one boundary on \(A\otimes A\), proves \(b_1b_2=0\) on pure degree-two
chains, proves the idempotent primitive, and proves the commuting-idempotent face-difference
formula over every algebra over a commutative ring.  Its focused build and axiom audit pass; it
uses only Lean's standard `propext`, `Quot.sound`, and, for the generic \(b_1b_2\) lemma,
`Classical.choice`.  The operator specialization `(95)`--`(100)` and arbitrary-packet coherence
remain paper-level.

### What this means

The corpus's infinity fractures now have a common sharper form:

```text
finite Euler gauges:
  invertible;

finite Kummer/BV cubes:
  algebraically exact;

finite prime-order transgressions:
  Hochschild-homotopic;

finite HT jets:
  universally indistinguishable;

all-prime completion:
  the chosen inverses and homotopies need not remain controlled, strict, or nonzero.
```

The missing invariant is therefore not an ordinary finite cohomology class and not an algebraic
\(\lim^1\) of finite-dimensional packets.  It is the **source-controlled growth class of the
null-homotopies themselves**.  Kakutani singularity, Hellinger--Rees order, nonclosable inverse
graphs, prime-infinity flux, orthogonality catastrophe, and exponentially escaping HT annihilator
order are different scalar shadows of failure of a family of finite exact comparisons to define
one morphism in the source bornological/filtered totalization.

This suggests a general law about constrained hypertranscendental sources.

`[BOLD CONJECTURE: HT CONTROLLED NULL-HOMOTOPY CONSERVATION]`

> A source-minimal constrained HT object is not classified by its finite algebraic obstruction
> classes, which may all vanish.  Its conservative analytic invariant is the controlled homotopy
> type of the complete source comparison.  Source-effective localization preserves a principal
> conormal precisely when the canonical finite algebraic null-homotopies survive as strict
> morphisms in the source-selected critical bornology, with their pointing, dagger, and
> complementary records intact.

For the Riemann source, the conjectural specialization says that the finite homotopies
`(95)`--`(105)`, their higher cubical extensions, the Gamma determinant transgression, and the
additive Poisson/Tate comparison form one controlled all-prime null-homotopy before divisor
specialization.  Conservative base change carries that same controlled class, not merely its
zero in ordinary homology, to every Xi principal conormal and multiplicity jet.  The source class
has modular exponent one; a conormal radial marginal has exponent
\(2\operatorname{Re}\rho\).  Equality of the controlled classes then gives
\(\operatorname{Re}\rho=1/2\).

This is still a conjecture.  Its advantage over bare modular-dimension conservation is that it
identifies an explicit family of finite primitives whose survival can be constructed or
falsified.  It also explains the HT role without claiming that hypertranscendence implies
positivity: HT forces the decisive datum out of every fixed finite algebraic quotient and into
the control of the complete homotopy.

### Superseding hostile correction

The earlier open core `XI_BV_TWISTED_CYCLIC_BASE_CHANGE` is too broad at finite level and too weak
at the positive boundary.

1. The two-prime algebraic face is already filled by `(95)`--`(105)`.
2. Finite semisimple/cubical exactness cannot force an RH conclusion.
3. A twisted-cyclic class can coexist with an off-line smooth Poisson state unless the BV class
   and the positive conormal state are proved to be restrictions of the **same** controlled
   source morphism.
4. Preserving the scalar twist after choosing the conormal is the already-known
   multiplicative-domain/purity criterion in different language.

The revised exact open core is:

`[OPEN CORE: XI_CONTROLLED_CUBICAL_HOMOTOPY_BASE_CHANGE]`

Use the canonical separability diagonal of every finite Boolean prime algebra to extend `(105)`
in all Hochschild degrees; attach its literal Gamma, first-trace, Möbius-phase, and Poisson/Tate
records; and form a strict all-prime totalization despite the exact cofinal diagonal fracture
below.  Then prove that Xi Cartier base change is conservative on this controlled homotopy and
that its gauge-diagonal functional is the same specialization, not an independently fitted
Poisson state.  Failure must produce a nonstrict cofinal boundary, lost essential record, lost
multiplicity jet, or mismatch between cyclic and boundary restrictions.

This is where genuinely new mathematics is required.  Algebraic bar/Koszul comparison maps are
parent theory; the candidate-new theorem is their source-canonical controlled all-prime
Euler--Gamma/Poisson totalization and conservative Xi conormal base change.

### All-degree finite closure and exact cofinal fracture

The later theorem
`../2-fully-proven/not_new_scientific_knowledge/05-algebraic-geometry-cohomology/finite-boolean-hochschild-diagonal-cofinal-fracture.md`
removes the unspecified finite higher-homotopy clause.  For
\(A_P=C(\{\pm1\}^P)\), the separability diagonal
\[
 D_P=\sum_\omega\delta_\omega\otimes\delta_\omega
 =2^{-|P|}\sum_{\chi}\chi\otimes\bar\chi
\]
has projective norm one and supplies an all-degree Hochschild contraction of norm at most one,
independent of \(|P|\).  Hence finite braid and higher-cube fillers carry no hidden growth.

Infinity nevertheless fails strictly.  Under unit-extension from \(P\) to
\(P\cup\{q\}\),
\[
 \|D_{P\cup\{q\}}-\widetilde D_P\|_\pi=1.
\]
Thus the canonical finite contractions are bounded but never Cauchy.  A virtual diagonal in a
bidual is still finite-Rees and, by the arbitrary-dimensional flat-radical theorem, cannot sew
the actual Wold irregular/half-normal fracture.

The later theorem
`../2-fully-proven/not_new_scientific_knowledge/07-functional-analysis-operator-theory/wold-boolean-diagonal-renormalization-mismatch.md`
also kills scalar essential renormalization.  In the infinite Boolean prime cube, \(D_P\) is the
indicator that the two coordinates agree on \(P\).  Its unique nonzero finite-measure
normalization is \(2^{|P|}\), of saturated accelerated type.  Every scalar family with
\(\log^+c_x=O(a_x^{-K})\) for fixed \(K\), including the Gamma gauge \(\exp(C/a_x)\), gives the
zero measure.  The open core is therefore narrower:

1. construct a non-scalar coupled Boolean--Wold totalization whose distributional/Iwahori channel
   retains the equality diagonal while its Wold marginal retains the ordinary-prime modular class;
2. retain that coupling in a strict all-prime Tate/irregular totalization; and
3. prove the explicit Gamma/co-Poisson/Sonin Xi boundary section is the specialization of the
   same coupled class, not a scalar renormalization or an independently fitted Weyl record.

The same mismatch card constructs the first non-scalar carrier: the Wold-weighted thermofield
vectors factor exactly under prime enlargement and define a strict incomplete all-prime tensor
product.  Their overlap is the Hellinger/Kakutani product, so off-line reflection is precisely a
sector change in this carrier.  This is a standard-form vector for the diagonal multiplication
correspondence, not a Hochschild separability diagonal or contracting homotopy.  What remains in
item 1 is not existence of a product Hilbert vector; it is coupling that standard-form carrier
to the complete Boolean Hochschild/Tate/Gamma source complex without losing its fixed Wold
marginal.

Essential singularity is therefore necessary, but external essential intertwiners remain
nonselective.  The RH-bearing datum is source identity of the coupled Boolean--Wold class before
and after Xi boundary specialization.

### Exact essential action of exponent-depth reporting

The later theorem
`../2-fully-proven/not_new_scientific_knowledge/07-functional-analysis-operator-theory/wold-depth-xi-essential-amplification-law.md`
removes the phrase “essential singularity” as an unspecified escape.  The step
\(M\mapsto M+1\) adds the Wold maximum shell
\[
 \delta_{M+1},
 \qquad
 \|\delta_{M+1}\|
 \sim2^{-(M+2)/2},
\]
while the completed bounded-exponent reporter changes by
\[
 {1\over M+1}
 \left(-u{\Xi'(u)\over\Xi(u)}+o(1)\right).
\]
Consequently any bounded linear realization of that literal source-depth successor has
\[
 \|T_M\|
 \gtrsim {2^{(M+2)/2}\over M+1},
 \qquad
 \liminf_{M\to\infty}{\log\|T_M\|\over M+1}
 \geq{\log2\over2}.
\]
The action \((\log2)/2\) is source-fixed by the least integer \(2^{M+1}\), and is the same
half-density action appearing in the positive shell conormal and the \(r=2\) Sonin character.

The companion theorem
`../2-fully-proven/not_new_scientific_knowledge/prime-log-action-condensation-normal-cone-law.md`
shows that this leading action is only the first face of a complete system.  At fixed spectral
coordinate,
\[
 {1\over\zeta((m+1)s)}-{1\over\zeta(ms)}
 =
 \sum_{n\geq2}\mu(n)(n^{-s}-1)e^{-ms\log n},
\]
and successive asymptotic deflation recovers every squarefree action \(\log n\).  Under the
diagonal normal blow-up \(s=u/(m+1)\), all these exponentially separated sectors condense into
the reciprocal-zeta germ, while the normalized shell difference tends to
\(-u\zeta'(u)/\zeta(u)\); Gamma completion gives \(-u\Xi'(u)/\Xi(u)\).  The required essential
connection must therefore retain the full prime-log action system, not merely amplify its leading
dyadic sector.

The algebraic carrier for these actions is not missing:
`HTGeometry.DirFormal = ArithmeticFunction (ℂ[X])` already gives the complete formal Dirichlet
ring, its least-action valuation, and its spectral-shift automorphism in Lean.  What remains is
the analytic graph completing that carrier simultaneously toward reciprocal Xi, Gamma/co-Poisson,
and the reflected Laurent half.  This prevents the new conjecture from degenerating into “name a
Hahn field”: coefficient completion is available; the source-continuation dagger is not.

This sharpens the open core but does not solve it.  A fitted rank-one map attains the lower bound
for any reporter, so essential growth alone is completely nonselective.  The missing comparison
must be one source-global irregular connection, compatible across every depth and prime cutoff,
whose associated boundary section is the literal Gamma/co-Poisson/Sonin section and whose
independent quadrant growth is subexponential after the source-fixed Stokes action is retained.
Equivalently: construct the operation, do not fit its norm.  The all-orders-flat theorem excludes
finite-Rees realizations; the disjoint-sector theorem excludes closed source-linear off-line
realizations after ordinary boundary descent; the only live site is the source-normal relative
class before closure.

## 15. New infinite invariant: positive-shell conormal activation rate

`[REDISCOVERED FROM LOCAL-RESEARCH; NOT A NOVELTY CLAIM]` The activation-rate calculation below
is subsumed by the stronger all-grade shell-corona law already developed in
`adjoint-duality-cauchy-nerve-purity-law.md` and
`high-shell-critical-hardy-conormal-uniformization.md`. It is retained here only as the
realization of modular drift used by this card. In particular, high-shell Hardy continuity
favours the strict-right half-plane and does not itself select the critical line.

The controlled-homotopy conjecture still lacked an intrinsic observable of “control.”  The
positive hypertranscendental Riemann-divisor frame supplies one.

For \(m\geq12\), recall its disjoint positive shell and zero-free multiplier
\[
 S_m^\#(s)=\zeta(s)H_m(s),
 \qquad
 H_m(s)=\frac1{\zeta((m+1)s)}-\frac1{\zeta(ms)} .
 \tag{106}
\]
Let \(\rho\) be any nontrivial zeta zero of order \(d\).  For every sufficiently large \(m\),
\(\operatorname{Re}(m\rho)>1\), so \(H_m\) is holomorphic and nonzero near \(\rho\).  Define the
normalized shell-conormal **tail germ**, modulo alteration of finitely many coordinates, by
\[
 \nu_\rho(m)
 :=
 \frac{(S_m^\#)^{(d)}(\rho)}{\zeta^{(d)}(\rho)}
 =H_m(\rho).
 \tag{107}
\]
The equality follows directly from Leibniz: every derivative of \(\zeta\) below order \(d\)
vanishes at \(\rho\).  If \(\operatorname{Re}\rho>1/2\), the paper's uniform \(m\geq12\)
zero-free theorem supplies the whole displayed tail without exceptions.  On the reflected
left-half point, finitely many meromorphic coordinates may be exceptional; quotienting finite
coordinates is necessary and does not change any activation rate below.  Thus `(107)` retains
multiplicity but removes its irrelevant common scalar.  It is source-canonical at infinity:
shell coefficients are nonnegative and pairwise disjoint, while the normalized transverse family
is jointly differentially algebraically independent over the full zeta differential field.  No
fixed finite jet packet can replace this infinite frame.

### Exact activation-rate theorem

`[PAPER-PROVED] [POSITIVE_SHELL_CONORMAL_ACTIVATION_RATE]`

For fixed \(s\) with \(\sigma=\operatorname{Re}s>0\), absolute convergence far to the right gives
\[
 \zeta(ms)=1+2^{-ms}+O(3^{-m\sigma})
 \tag{108}
\]
and hence
\[
 \frac1{\zeta(ms)}
 =1-2^{-ms}+O(3^{-m\sigma}).
 \tag{109}
\]
Subtracting consecutive terms yields
\[
 \boxed{\quad
 H_m(s)
 =(1-2^{-s})\,2^{-ms}+O(3^{-m\sigma}).
 \quad}
 \tag{110}
\]
Since \(1-2^{-s}\neq0\) for \(\sigma>0\),
\[
 \lim_{m\to\infty}\frac{H_{m+1}(s)}{H_m(s)}=2^{-s},
 \qquad
 \lim_{m\to\infty}-\frac1m\log|H_m(s)|=\sigma\log2.
 \tag{111}
\]

Equivalently, on the exponential Rees tail scale, where sequences differing in finitely many
coordinates represent the same germ,
\[
 {\cal E}_r
 :=
 \left\{[a]_{\rm tail}:
 \|a\|_{r,M}:=\sup_{m\geq M}e^{rm}|a_m|<\infty
 \text{ for some }M\right\},
 \tag{112}
\]
define
\[
 \kappa(a):=\sup\{r:a\in{\cal E}_r\}.
 \tag{113}
\]
Then every nontrivial zero satisfies the exact source-depth law
\[
 \boxed{\quad
 \kappa(\nu_\rho)=\operatorname{Re}\rho\,\log2.
 \quad}
 \tag{114}
\]
For the Riemann reflection \(\tau\rho=1-\overline\rho\),
\[
 \kappa(\nu_{\tau\rho})=(1-\operatorname{Re}\rho)\log2,
 \tag{115}
\]
so
\[
 \kappa(\nu_\rho)=\kappa(\nu_{\tau\rho})
 \quad\Longleftrightarrow\quad
 \operatorname{Re}\rho=\frac12.
 \tag{116}
\]

This is more than another coordinate for drift.  It identifies an infinite, positive,
coefficient-disjoint, multiplicity-aware conormal frame whose **asymptotic source activation
rate** is the horizontal coordinate.  Hypertranscendence makes the whole frame irreducible to
finite differential data; `(110)` makes its missing infinite datum exact.

There is also an exact reflection rate-distortion cocycle.

`[PAPER-PROVED] [POSITIVE_SHELL_REFLECTION_RATE_DISTORTION]`

On every tail where both sides are defined, put
\[
 u_m(\rho):=\frac{H_m(\tau\rho)}{H_m(\rho)}.
 \tag{117}
\]
Equations `(110)`--`(111)` give
\[
 \boxed{\quad
 \lim_{m\to\infty}\frac1m\log|u_m(\rho)|
 =(2\operatorname{Re}\rho-1)\log2.
 \quad}
 \tag{118}
\]
Moreover \(u_m(\tau\rho)=u_m(\rho)^{-1}\), so the rate is an antisymmetric reflection cocycle.
This is the positive-shell realization of the same centered modular drift read by the
Kakutani, Hellinger--Rees, first-trace, source-Gram, and Wold defects.  It is not merely a
membership wall: it is the exact exponential condition-number growth of the literal comparison
between two complete, disjoint positive conormal frames.

The obvious normalization also exposes a new no-go.  Define
\[
 \widetilde\nu_\rho(m)
 :=
 2^{m(\rho-1/2)}\nu_\rho(m).
 \tag{119}
\]
Then `(110)` gives
\[
 \widetilde\nu_\rho(m)
 =(1-2^{-\rho})2^{-m/2}+o(2^{-m/2})
 \tag{120}
\]
for **every** \(\rho\) in the open strip.  Thus a parameter-dependent half-density gauge makes
the shell activation rate reflection-invariant everywhere, including off line.  Existence of
some balanced or scale-exact chart is therefore as powerless as a fitted Hilbert metric.
The unrenormalized positive/integral shell pointing is load-bearing.

### Universal law suggested by the corpus

Finite clock-alias rank conservation says a complete observation cannot create or destroy
projective rank; it only transfers rank between hidden relations and visible phase directions.
The infinite analogue suggested here is:

`[BOLD CONJECTURE: SOURCE ASYMPTOTIC-DIMENSION CONSERVATION]`

> A source-minimal constrained HT object has an asymptotic source dimension given by the critical
> abscissa of its complete conormal/homotopy frame.  Every source-internal symmetry acts
> bicontinuously on each step of the source Rees scale and therefore preserves this abscissa.
> Finite obstruction classes, finite differential jets, scalar Hilbert shadows, and individual
> positive states are quotient observations of this invariant and need not preserve it.

For Xi, this becomes the concrete open theorem:

`[OPEN CORE: XI_POSITIVE_SHELL_SCALE_EXACT_REFLECTION]`

Construct, before selecting a zero, the reflection comparison on the positive-shell principal
conormal module and the finite Kummer/BV homotopies of Section 14.  Prove that it and its inverse
preserve every \({\cal E}_r\) in `(112)`, preserve multiplicity jets, and identify the shell
conormal with the gauge-diagonal restriction of the same controlled Euler--Gamma/Poisson
homotopy.  Then the comparison carries \(\nu_\rho\) to a nonzero scalar multiple of
\(\nu_{\tau\rho}\); bicontinuity gives equality of `(114)` and `(115)`, and `(116)` proves RH.

This gives the proposed universal interpretation:

```text
finite rank conservation
  -> finite observers preserve resolved projective dimension;

finite Hochschild flatness
  -> every finite source path has a null-homotopy;

HT finite-jet blindness
  -> no finite differential observer sees the source dimension;

Kakutani / Hellinger--Rees / weak-first-trace fractures
  -> scalar shadows of an abscissa changing under uncontrolled completion;

positive disjoint divisor shells
  -> a canonical infinite conormal frame measuring that abscissa;

critical line
  -> fixed locus where Riemann reflection preserves asymptotic source dimension.
```

### Hostile audit

1. `(114)`--`(116)` are a new exact selector, not an RH proof.
2. Merely defining a fibrewise map
   \(\nu_\rho\mapsto\nu_{\tau\rho}\) is circular.  The map must descend from the source comparison
   before the divisor is decomposed.
3. A bounded map on one \(\ell^p\) space is insufficient: permutations or exponentially weighted
   diagonal maps can change \(\kappa\).  Preservation of every named Rees step by both map and
   inverse is load-bearing.
4. The naive diagonal ratio
   \(H_m(\tau\rho)/H_m(\rho)\) has exponential rate
   `(118)`.  Off line it is exactly **not** scale-exact.  The functional equation alone therefore
   does not prove the open core; it displays its anomaly.
5. Smooth positive off-line Poisson states remain valid countermodels to positivity,
   bilateral regularity, and finite-order orientation.  They do not refute the conjecture unless
   they also realize the literal disjoint positive zeta shell frame and a source-first
   scale-exact reflection comparison.
6. The static requirement that both reflected sequences lie in one chosen tail space is an
   already-known RH-equivalent membership test.  Candidate-new content is the construction of
   one source-internal comparison whose scale-exactness would force equality, not imposing that
   equality as a fibre condition.
7. The balanced frame `(119)`--`(120)` is an explicit off-line falsifier for any unpointed version
   of the conjecture.  Allowed comparison maps must preserve the raw positive coefficient
   partition, its integral shell depth, and its distinguished unit—not merely some isomorphic
   exponential scale.

The gain over the preceding open core is a falsifiable quantitative target.  “Controlled at
infinity” now means preservation of the explicit family of norms `(112)`, and its failure has the
measurable exponent in item 4.  The positive-shell frame supplies the left-invertible infinite
clock compass that finite HT data was missing.

## 16. Hermitian finite escape and the exact infinity boundary

The physical local-extension corpus now proves two unconditional finite theorems:

1. under maximal projectivity, injective layered spectrum, Hermitian transition, and connected
   interaction lift, every fixed nonzero balanced integer spectral relation has a real
   tensor-local extension with simple real spectrum and nonzero permutation-invariant coefficient
   obstruction;
2. one such extension can be chosen to erase **all** nonzero balanced integer relations
   simultaneously.

The exact Lean endpoints are
`exists_hermitianLocalExtension_simpleRealRootPacket_coefficientObstruction_ne_zero` and
`exists_hermitianLocalExtension_maximallyProjectiveRealRootPacket` in
`HTGeometry/HermitianLocalExtensionRelationEscape.lean`.

This supports the RH program, but only on the falsifier side. It proves that Hermiticity,
tensor-locality, simple real spectrum, connected finite interaction, and unordered spectral
detection do not preserve any nontrivial balanced relation. Hence a finite Hermitian
spectral-relation mechanism cannot select the critical line.

There is also an exact infinity consequence. Every absolutely summable integer-valued character
has finite support. Therefore, in any cofinal source system in which every finite support lies in
an admissible Hermitian local-extension chart, no nonzero balanced
\(\ell^1(\mathbb Z)\)-character can be stable under all finite local extensions. A surviving Xi
class must instead be a genuinely all-prime source class defined before specialization. It
cannot be manufactured as ordinary \(R^1\!\varprojlim\) cohomology of acyclic finite
specializations; that shortcut is already ruled out by the corpus.

The physics theorem and source saturation have different quantifiers:
\[
 \text{finite escape:}\qquad
 \forall n\ \exists p_n\ \forall k\in K_n,\quad
 {\cal O}_{n,k}(p_n)\ne0,
 \tag{121}
\]
whereas the RH-bearing complete-quotient statement requires, for every fixed source seminorm
\(\nu\),
\[
 \exists C_\nu<\infty\ \forall n\ \forall y\
 \exists x,\qquad q_nx=y,\qquad
 \nu(x)\le C_\nu\,\nu_{\rm quot}(y).
 \tag{122}
\]
Nonvanishing in `(121)` supplies no lower bound and no compatibility between \(p_n\) and
\(p_{n+1}\). Analytic escape is compatible with cofinal obstruction values approaching zero
arbitrarily fast. Thus it does not imply `(122)`, Xi-conormal faithfulness, or reduced Tor
vanishing.

`[POSITIVE SURVIVOR] [HERMITIAN_FINITE_SEPARATION_BOUNDARY]`

> The physical theorem supplies a complete family of finite symmetric spectral falsifiers.
> Consequently any valid third completion must distinguish qualitative finite separation from
> quantitatively controlled cofinal survival. Its Xi point fibres must be present in an
> all-prime object before specialization, and their normalized reporter obstruction must remain
> separated in every fixed source seminorm.

`[OPEN BRIDGE] [HERMITIAN_CLOCK_COFINAL_PERSISTENCE]`

Construct source maps from the literal ordinary-prime Euler--Gamma--Poisson reporter system to a
compatible exhaustion of the Hermitian tensor-local charts, then prove a source-derived
normalization for which:

1. the unordered coefficient obstruction represents the same reduced Xi conormal atom at every
   aperture;
2. restriction and local extension commute with the source maps;
3. the normalized obstruction has a positive lower bound in every fixed source seminorm; and
4. the induced matrix quotient constants satisfy `(122)`.

Clauses 1--2 would turn the physical result into a source connector; clauses 3--4 are precisely
the missing saturation theorem. The existing one-step theorem proves none of them. The
dimension-free linear locality cost
\[
 |T|\Lambda_R>\frac{2R+3}{2e^2}
\]
is a useful hostile constraint on any proposed normalization, but not a contradiction with
off-line modular drift: a linear action budget can support an exponential response after taking
logarithms. An arithmetic upper budget or a sharper source comparison is still required.

## 17. Literature boundary

Parent mathematics includes:

- Allcock--Vaaler place-space \(L^1\) geometry and the product-formula hyperplane;
- Kakutani equivalence and singularity of infinite product measures;
- Choi multiplicative domains and Stinespring dilation;
- Rees filtrations, moderate/rapid Stokes structures, and irregular Riemann--Hilbert theory;
- operator-system matrix order, \(C^*\)-envelopes, and local Shilov boundaries; and
- strict determinant/differential-character and arithmetic regulator theories;
- Cuntz--Quillen bar/X-complex excision; and
- entire, analytic, local, and equivariant cyclic homology for complete bornological algebras.

Targeted searches found no theorem identifying one zeta-centered drift simultaneously through
`(5)`, `(8)`, `(10)`, `(12)`, and `(13)`, or deriving its vanishing from a strict
ordinary-prime Euler--Gamma principal-source realization.  This is a noncollision result, not a
priority certificate.  Each individual equivalence remains parent or already proved in the
corpus; candidate novelty is the faithful realization dictionary and the source-effectivity law.
Further targeted searches found the standard KMS classification of Toeplitz/product-system
algebras, modular spectral triples with twisted weights, additive Haar measure on profinite
completions, and the adelic half-density scaling module.  No located source constructs an Xi
BV principal conormal as equivariant base change of a fixed occupation-twisted cyclic class, or
identifies its gauge-averaged conormal marginal with that class.  The local Haar/Gibbs rigidity
itself is elementary parent mathematics; candidate-new content is precisely this
ordinary-prime source comparison.
Bornological analytic/local cyclic theories already make controlled completion, excision, and
homotopy invariance into parent mathematics.  Therefore no novelty is claimed for the phrase
“controlled null-homotopy” or for the bar primitives `(99)`--`(104)`.  No located source constructs
the specific all-prime Euler--Gamma/Poisson family `(105b)`, proves its source-critical control,
or identifies its strict Xi Cartier specialization with the same positive conormal functional.
That source-specific construction is the only candidate-new content of Section 14.
Section 15's maximum-prime-exponent activation rate collides with stronger all-grade shell-corona
results already in the local corpus. No novelty is claimed for it here. The source-first,
scale-exact reflection comparison remains an open connector, not a proved theorem.
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
- Jeong Hee Hong, Nadia S. Larsen, and Wojciech Szymański,
  *KMS states on Nica--Toeplitz algebras of product systems*,
  <https://arxiv.org/abs/1202.4594>.
- Marco Matassa, *A modular spectral triple for kappa-Minkowski space*,
  <https://arxiv.org/abs/1212.3462>.
- Alain Connes and Caterina Consani, *The scaling Hamiltonian*,
  <https://arxiv.org/abs/1910.14368>.
- Ralf Meyer, *Analytic cyclic cohomology*,
  <https://arxiv.org/abs/math/9906205>.
- Ralf Meyer, *Bornological versus topological analysis in metrizable spaces*,
  <https://arxiv.org/abs/math/0310225>.
- Christian Voigt, *Equivariant local cyclic homology and the equivariant Chern--Connes
  character*, <https://arxiv.org/abs/math/0608609>.
- Luca Demangos and Ignazio Longhi,
  *Densities on Dedekind domains, completions and Haar measure*,
  <https://arxiv.org/abs/2009.04229>.
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
- 2026-07-30 — Identified \(A=\operatorname{diag}(\mu(n)/n)\) as the coefficient symbol of the
  critical half-density adjoint of a Möbius-twisted dilation packet.  Proved the exact Wold
  eigenstate law `(71)`: conditional occupation-defect density minus the ordinary-prime
  first-trace density is \(q^{-1}\) times the Kadison defect.  Its logarithmic linearization is
  the projective source-Gram anomaly, and its all-prime sum diverges off line.  Reduced the
  source comparison to the typed conditional-density base-change theorem in clauses 1--4 above.
- 2026-07-30 — Reinterpreted the conditional-density law as conservation of one modular
  exponent.  The fixed occupation weight is the \(\beta=1\) twisted-cyclic/Haar class, while the
  gauge-averaged \(Q\)-conditioned conormal has \(\beta=2\operatorname{Re}\rho\).  Proved local
  additive-Haar/multiplicative-Gibbs rigidity and identified the exact cylinder defect with
  \(\omega_\rho({\cal B}_p)/\omega_\rho(Q)=p^{-1}-p^{-2\operatorname{Re}\rho}\).  Isolated one
  trace-valued BV cocycle plus strict equivariant conormal base change as the source-first
  producer; explicitly retained the positive Born-identification gap.
- 2026-07-30 — Closed the first higher source face: for coprime \(m,n\), the two ordered
  BV--Hochschild transgressions have boundary \({\cal B}_{mn}\), and their difference is an
  explicit degree-two Hochschild boundary.  Therefore finite two-prime curvature vanishes after
  retaining the complementary record.  Corrected the proposed producer: the RH-bearing datum is
  controlled survival of the canonical finite null-homotopies through the strict all-prime
  Euler--Gamma/Poisson totalization and Xi Cartier base change, not finite cyclic exactness or a
  separately imposed twist.
- 2026-07-30 — Formalized the low-degree noncommutative Hochschild core axiom-clean in
  `HTGeometry/LowDegreeHochschildFaceFlatness.lean`.  Extracted a new infinite observable from the
  positive hypertranscendental divisor frame: the normalized shell conormal has exact activation
  abscissa \(\operatorname{Re}\rho\log2\), while its Riemann reflection has abscissa
  \((1-\operatorname{Re}\rho)\log2\).  Proposed source asymptotic-dimension conservation and
  isolated scale-exact, source-first reflection on the full positive-shell Rees frame as the
  quantitative RH-bearing open core.  Explicitly retained the hostile boundary: the abscissa
  equality is only a selector until that comparison is constructed.
- 2026-07-30 — Corrected the shell-activation novelty claim after collision with stronger local
  all-grade corona results. Audited the new Hermitian tensor-local relation-escape theorems and
  extracted their exact RH role: they close finite balanced spectral relations as selectors and
  provide finite symmetric falsifiers, but do not provide compatible or uniformly separated
  cofinal lifts. Isolated `HERMITIAN_CLOCK_COFINAL_PERSISTENCE` as the only bridge by which the
  physics theorem could support Xi source saturation.
- 2026-07-30 — Removed finite Gevrey--Rees bidegree as the decisive sewing requirement.
  Reflected ordinary-prime product-Poisson representations are disjoint off line, so every
  nonzero closed densely defined map linear over the same source cylinder algebra is impossible,
  even with arbitrary essential norm growth.  Polar decomposition reduces any such map to a
  forbidden bounded partial-isometry intertwiner.  The narrowed target is a nonzero closed
  source-linear producer--reporter round-trip graph carrying each Xi conormal; external Weyl
  joining evades it only by modular retuning, and a singular relation only by nonclosability.
- 2026-07-30 — Closed the multivalued loophole: every closed subspace relation invariant under
  two disjoint \(C^*\)-representations is reducing, and its projection has block-diagonal
  commutant form; hence the relation splits into pure input and pure output parts.  Arbitrary
  essential growth and closed multivaluedness therefore do not sew off-line prime-Poisson
  sectors.  Hostile type audit also retired the closed \(C(\mathbb T^{\mathbb P})\)-module graph
  as a direct Meyer target: \(M_\zeta\) carries only a locally convex dilation action, and
  upgrading its generalized zero characters to a unitary/tempered prime boundary is already the
  RH-bearing Hodge theorem.  The surviving object must be a relative class for the
  Wold--Toeplitz extension before boundary descent; essentiality is non-descent of the anomaly
  ideal, not merely operator blow-up.
- 2026-07-30 — Tested the correction on the literal first-trace source graph.  Lean already
  proves that its ordinary closure is the full source space times the zero-vacuum response
  hyperplane, hence exactly the maximally split relation predicted above.  The coupled algebraic
  graph survives only through its exponential normal data
  \(a_p(-\log b_p)\to1\), invisible at every finite Rees order.  This forces the construction
  order: take the source-normal/exponential associated graded before strict completion.
  Completing first irreversibly erases the coupling.  The remaining Xi theorem is a strict
  graded-relative boundary descent/Bockstein theorem, not a closed-graph theorem on the ordinary
  Hilbert completion.

## 18. Source-exceptional carrier and conservative-consumer closure

The updated ramified-character manuscript and the source-exceptional principal-parts theorem
close two previously conflated ends of the source-effective base-change problem.

First, the bounded-exponent source produces \(1/(2\Xi)\) before any zero is selected.  For a
commutative domain \(R\) and nonzero \(x\), the map
\[
 R\longrightarrow R[x^{-1}]/R,\qquad r\longmapsto[r/x]
 \tag{123}
\]
has kernel \(xR\).  Its image is therefore canonically \(R/(x)\).  With \(x=\Xi\), the source
itself generates the Cartier principal-parts object; at a zero \(\rho\) of order \(m_\rho\), its
stalk is
\[
 {\cal O}_\rho/(\Xi)\cong{\cal O}_\rho/(t^{m_\rho}).
 \tag{124}
\]
This theorem is formalized, without new axioms, in
`HTGeometry/SourceExceptionalPrincipalPart.lean`.  It solves algebraic carrier generation only.
It does not provide a topology, norm, adjoint, or conservative action.

Second, the updated manuscript identifies the complete regular divisor output as the ramified
character
\[
 (m_\rho,\chi_\rho),\qquad
 \chi_\rho(z)=e^{z(\rho-1/2)},
 \tag{125}
\]
and proves the abstract conservative consumer
\[
 TU=VT,\quad Ux=e^\nu x,\quad Tx\ne0,\quad
 \|Vy\|=\|y\|
 \quad\Longrightarrow\quad \nu=0.
 \tag{126}
\]
The Lean theorem is
`normConservative_equivariantDescent_forces_zero` in
`RHTower/XiSourceModularTypeSuperselectionLaw.lean`.

Third, the latest manuscript revision identifies an actual source-side odd generator.  If
\(C_x(p)\) is the Gamma-sewn scalar contraction and
\[
 \ell_x(p)=\frac{2}{\sqrt3}\frac{\sqrt{1-C_x(p)^2}}x,
\]
then
\[
 \ell_x(p)\longrightarrow\log p.                           \tag{127}
\]
On finite prime packets this is the literal logarithmic clock.  Its graph is dense in the full
product Hardy space, so every bounded global recovery has diverging norm.  This supplies the
previously missing odd source coordinate but simultaneously proves that it cannot descend
through the ordinary scalar Hilbert completion.  The relevant Lean endpoints are
`primeFiniteTraceClock_graphClosure_eq_top` and
`tendsto_norm_of_extends_gammaSewnMobiusJuliaFiniteTraceClock`.

Squaring after divisor formation instead gives the finite positive character energy
\[
 {\cal E}_\chi
 =\sum_{\xi(\rho)=0}
   \frac{m_\rho}{|\rho-\tfrac12|^2}\sin^2(2\pi\Re\rho).
 \tag{128}
\]
It vanishes exactly under RH and is reflection-even.  Thus `(128)` is a complete detector, not a
source theorem forcing neutrality; it cannot replace the odd clock or the conservative descent.

Equations `(123)`--`(128)` compress the frontier but do not bridge it.  Centered prime transfer
acts on `(124)` by multiplication with \(q^{1/2-s}\).  Its reduced eigenvalue at \(\rho\) has
modulus \(q^{1/2-\Re\rho}\), while the thickened fibre retains the multiplicity jets.  Thus a
source-defined equivariant map on the reduced character line which lands in a
norm-conservative action and does not kill that line would force
\(\Re\rho=1/2\).  The manuscript proves no strict base change coupling the odd source clock
`(127)` to this reduced character rate.  No such map or norm is constructed.

One must not demand that the same conservative action faithfully carry the thickened Cartier
module.  When \(m_\rho>1\), multiplication by \(q^{1/2-s}\) on
\({\cal O}_\rho/(t^{m_\rho})\) has a nontrivial unipotent Jordan part even on the critical line.
A norm-conservative finite-dimensional action has semisimple peripheral spectrum, so such a
landing would force simplicity in addition to RH.  This obstruction is already formalized in
the corpus by `xiLocalJordanNormal_iff_multiplicity_one` and
`exists_conservative_xiThetaMetric_iff_rh_and_simple`.  Continuous displacement and ramification
must therefore descend through separate but compatible channels, exactly as the pair
\((m_\rho,\chi_\rho)\) suggests.

`[OPEN CORE: XI_SOURCE_EXCEPTIONAL_SPLIT_RAMIFIED_CONSERVATIVE_BASE_CHANGE]`

> Starting from the literal Euler--Gamma/co-Poisson source and before zero specialization,
> construct a Hausdorff singular completion of its source-generated principal-parts object and
> compatible descents \((T_{\rm cont},T_{\rm ram})\) such that:
>
> 1. \(T_{\rm cont}\) is the strict Cartier base change of the explicit singular Julia/log-clock
>    graph `(127)`, not an arbitrary zero-indexed map;
> 2. it intertwines that odd source generator with the reduced centered-character action in a
>    norm-conservative target;
> 3. \(T_{\rm cont}\) is nonzero on the reduced transfer eigenline of every nonzero Xi Cartier
>    stalk;
> 4. the pair is strict and faithful on the valuation-depth/prime-breadth bifiltration;
> 5. \(T_{\rm ram}\), without an incompatible full-jet conservativity demand, retains every
>    multiplicity jet or equivalently the complete dyadic deck-character tower;
> 6. both maps arise from one source comparison, preserve raw alternating-tail/Rees grade, and
>    are fixed before divisor
>    evaluation.
>
> Then `(126)` applied at any prime forces every nontrivial Xi zero onto the critical line.

This is a typed refinement of `XI_CONTROLLED_CUBICAL_HOMOTOPY_BASE_CHANGE` and
`XI_BV_TWISTED_CYCLIC_BASE_CHANGE`, not a new universal-law claim.  The generalized-prime
off-line constructions remain the decisive falsifier: they satisfy source positivity,
reflection, entire completion, hypertranscendence, and principal-parts localization.  Hence
those inputs alone cannot imply clauses 1--5.  Any proof must use zeta-specific
Gamma/co-Poisson source structure to build the conservative descent rather than impose it.

- 2026-07-31 — Integrated the ramified-character update.  Algebraic exceptional-carrier
  generation and the abstract conservative consumer are now closed and Lean-checked.  The exact
  unsolved producer is source-native split base change: conservative and nonannihilating on every
  reduced exceptional eigenline, but separately faithful to bifiltration and ramification.  A
  single conservative full-jet landing would overprove simplicity and collides with the corpus
  Jordan obstruction.
- 2026-07-31 — Integrated odd Julia/Fisher revision.  The source logarithmic orientation
  generator is now explicit, while its dense graph rules out bounded recovery after ordinary
  scalar completion.  The Xi--Hurwitz energy is only a reflection-even RH detector.  Missing
  theorem is strict singular Cartier descent coupling the odd clock to the reduced character
  rate before conservative realization.
