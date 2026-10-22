# Source-effective polar Kummer conormal purity

- **ID:** `source-effective-polar-kummer-conormal-purity`
- **Stage:** 1-in-progress
- **Type:** MIXED-POLAR THIRD-COMPLETION THEOREM / SOURCE-LANDING CONJECTURE
- **Scientific status:** `[PAPER-PROVED CHARACTER SELECTOR]`
  `[FINITE PRIME-INFINITY LEAKAGE CLASSIFIED]`
  `[ALL-LQ SOURCE-MEMORY WALL PAPER-PROVED]`
  `[PRIME-VALUATION SCREEN RETIRED AFTER CORPUS COLLISION]`
  `[EXISTING HT SHELL BIPOLAR GRAPH ADOPTED]`
  `[SCALAR HELLINGER GAP LEAN-FORMALIZED]`
  `[SOURCE LANDING OPEN] [NOVELTY PROVISIONAL] [NOT RH]`
- **Parents:**
  - `../2-fully-proven/deninger-adelic-kummer-gelfand-triple.md`
  - `../2-fully-proven/deninger-adelic-place-average-residue.md`
  - `../2-fully-proven/deninger-real-kummer-arakelov-boundary.md`
  - `../../../3-formalized/source-conormal-projective-topology-calibration.md`
  - `../../../3-formalized/source-producer-integral-realization-minimality.md`
  - `../2-fully-proven/new_scientific_knowledge/irrational-triptic-source-effectivity-character.md`
  - `source-curved-prime-torus-conormal-temperedness.md`
  - `infinite-prime-wold-higgs-energy-purity.md`
  - `../2-fully-proven/prime-sieve-wold-gamma-bv-relative-character.md`
  - `../2-fully-proven/prime-valuation-kakutani-polar-third-completion.md`
  - `xi-entire-high-shell-bipolar-completion-graph.md`
- **Statement:** replacing the bare Hilbert--Kummer modulus by the strict mixed
  \(L^1/L^2\) Kummer test space gives a Hausdorff polar receiver which retains unitary phase
  point fibres and field-norm covariance but admits a coherent rational power modulus
  \(p^c\) only for \(c=0\).  The open RH-bearing theorem is a source-first polar regulator
  landing of the distinguished principal \(\Xi\)-conormal in this receiver.

## Goal and non-circular boundary

The target is not another critical-line criterion.  It is a source comparison:

```text
distinguished Euler--Gamma/co-Poisson principal conormal
  -> one joint integral--Hermitian pointed realization
  -> strict mixed Kummer--Arakelov radial anomaly
     + distributional unitary prime-angle phase
  -> no radial leakage at prime infinity
  -> Re(rho)=1/2 for every conormal fibre
  -> RH.
```

The analytic divisor and its zero set may not define the target topology, delete fibres, or
choose a metric.  The polar regulator must be constructed on the completed source object before
specialization at a divisor point.

## 1. Concrete mixed-polar receiver

Let \(Y\) be the Allcock--Vaaler place space and let

\[
 E_{\rm Kum}
 =
 \overline{\mathcal F}^{\,\|f\|_1+\|f\|_2}
 \hookrightarrow
 H_{\rm Kum}=L^2(Y,\lambda)
 \hookrightarrow
 E_{\rm Kum}'                                                  \tag{1}
\]

be the proved Kummer rigging.  Every element of \(E_{\rm Kum}\) is in \(L^1\cap L^2\) and has
product-formula integral zero.  Normalized field norms act contractively on both the \(L^1\)
and \(L^2\) channels.

For a rational prime \(p\), put

\[
 f_p=\log p\,
 \bigl(1_{Y(\mathbb Q,\infty)}-1_{Y(\mathbb Q,p)}\bigr).          \tag{2}
\]

The strict polar character receiver is

\[
 \check X_{\rm pol,mix}
 =
 \check X_{\rm unit}\times E_{\rm Kum}.                          \tag{3}
\]

For \((\eta,h)\) in `(3)`, its rational-prime character is defined on generators by

\[
 \chi_{\eta,h}(p)
 =
 \eta(p)\exp\langle h,f_p\rangle_{L^2},
 \qquad |\eta(p)|=1,                                             \tag{4}
\]

and extended multiplicatively to
\(\mathbb Q_{>0}^{\times}=\bigoplus_p\mathbb Z\).
The unitary factor is retained as an actual generic-character point and, after conormal
specialization, as a Dirac character and its finite distribution jets.  The radial factor is
required to come from the strong product-formula test space, not from bare \(L^2\).

This differs from the proved Hilbert--Kummer polar locus
\(\check X_{\rm unit}\times H_{\rm Kum}\) in exactly one place: `(3)` retains the \(L^1\)
boundary which bare \(L^2\) erases.

## 2. Infinite place-average coherence selector

`[PROVED HERE] [MIXED_POLAR_KUMMER_COHERENT_POWER_PURITY]`

Let \(h\in L^1(Y,\lambda)\cap L^2(Y,\lambda)\) be real with

\[
 \int_Yh\,d\lambda=0.                                           \tag{5}
\]

If there is \(c\in\mathbb R\) such that

\[
 \langle h,f_p\rangle_{L^2}=c\log p
 \qquad\text{for every rational prime }p,                        \tag{6}
\]

then \(c=0\).

### Proof

Write

\[
 a_v=\int_{Y(\mathbb Q,v)}h\,d\lambda .
\]

The rational-place components partition \(Y\), and

\[
 \sum_v|a_v|
 \leq\int_Y|h|\,d\lambda<\infty,\qquad
 \sum_va_v=0.                                                    \tag{7}
\]

Equations `(2)` and `(6)` give

\[
 a_\infty-a_p=c
 \qquad\text{for every }p.                                      \tag{8}
\]

The prime coordinates in `(7)` are summable, so the constant sequence
\(a_p=a_\infty-c\) must vanish.  Hence \(a_p=0\) for every prime and
\(a_\infty=c\).  The second identity in `(7)` now gives \(a_\infty=0\), hence \(c=0\).

The \(L^2\) hypothesis is not used by the selector.  It belongs to the positive-energy
realization.  The critical rigidity is supplied by the \(L^1\) product-formula channel.

### Character corollary

If a coherent centered power character

\[
 \chi_\rho(p)=p^{1/2-\rho}                                      \tag{9}
\]

has its radial logarithm represented by one \(h\in E_{\rm Kum}\), then

\[
 \log|\chi_\rho(p)|
 =
 \left(\frac12-\operatorname{Re}\rho\right)\log p
 =
 \langle h,f_p\rangle
\]

for every prime, and the theorem forces
\(\operatorname{Re}\rho=\tfrac12\).

No zeta zero, functional equation, positivity assertion, or numerical computation enters this
selector.

## 3. Exact radial-sequence classification and prime-infinity leakage law

Let \(\mathcal P\) be the rational primes and put

\[
 u_p=\frac{f_p}{\log p}
 =1_{Y(\mathbb Q,\infty)}-1_{Y(\mathbb Q,p)}.
\]

Let \(H_{\mathbb Q}\) be the \(L^2\)-space of functions constant on every rational-place
component, and let

\[
 E_{\mathbb Q}
 =
 \overline{\operatorname{span}_{\mathbb R}\{u_p:p\in\mathcal P\}}
 ^{\ \|\cdot\|_1+\|\cdot\|_2}.
\]

For \(h\) in either space define its normalized radial sequence

\[
 \mathcal R(h)_p=\langle h,u_p\rangle=a_\infty(h)-a_p(h).         \tag{10a}
\]

`[PROVED HERE] [POLAR_KUMMER_RADIAL_SEQUENCE_CLASSIFICATION]`

\[
\begin{aligned}
 \mathcal R(H_{\mathbb Q})
 &=
 \mathbb R\mathbf1\mathbin{\dotplus}\ell^2(\mathcal P),\\
 \mathcal R(E_{\mathbb Q})
 &=
 \left\{
   c\mathbf1+d:
   d\in\ell^1(\mathcal P),\
   c=\sum_pd_p
 \right\}.                                                       \tag{10b}
\end{aligned}
\]

Both decompositions in `(10b)` are unique.  If \(b=c\mathbf1+d\), its Hilbert
representer is

\[
 h=c1_{Y(\mathbb Q,\infty)}
   -\sum_pd_p1_{Y(\mathbb Q,p)}.                                 \tag{10c}
\]

Indeed, `(10c)` lies in \(H_{\mathbb Q}\) exactly when \(d\in\ell^2\), and then
\(\mathcal R(h)_p=c+d_p\).  Conversely every \(h\in H_{\mathbb Q}\) has this form.
The constant sequence is not in \(\ell^2(\mathcal P)\), so the decomposition is unique.

For the mixed statement, `(10c)` is in \(L^1\) exactly when \(d\in\ell^1\), and its
product-formula integral is

\[
 \int_Yh\,d\lambda=c-\sum_pd_p.                                  \tag{10d}
\]

Thus every mixed Kummer limit has the stated graph relation.  Conversely, when
\(d\in\ell^1\) and \(c=\sum_pd_p\),

\[
 h=\sum_pd_pu_p
\]

converges in both \(L^1\) and \(L^2\), so it belongs to \(E_{\mathbb Q}\).  This proves
`(10b)`.

Therefore bare Hilbert completion adds a one-dimensional coherent leakage direction
\(\mathbb R\mathbf1\).  The strict mixed completion replaces that affine freedom by the
global graph equation \(c=\sum_pd_p\).  Localized radial nonunitarity is allowed; a coherent
arithmetic power ray \(b_p\equiv c\) has \(d=0\) and is admitted only when \(c=0\).

### General finite Riesz regulator

For a finite prime packet \(P\) of cardinality \(n\), every real radial vector
\(b=(b_p)_{p\in P}\) has a unique Riesz representer in
\(\operatorname{span}_{\mathbb R}\{u_p:p\in P\}\):

\[
\begin{aligned}
 B_P&=\sum_{p\in P}b_p,\\
 h_{P,b}
 &=
 \sum_{p\in P}
 \left(b_p-\frac{B_P}{n+1}\right)u_p,\\
 \langle h_{P,b},u_p\rangle&=b_p,\\
 \|h_{P,b}\|_2^2
 &=\sum_{p\in P}b_p^2-\frac{B_P^2}{n+1}.                         \tag{10e}
\end{aligned}
\]

The proof is the exact Gram inversion
\(\langle u_p,u_q\rangle=1+\delta_{pq}\).
If \(P'=P\sqcup\{q\}\) and

\[
 D_{P,q}=(n+1)b_q-B_P,
\]

then the transition defect is

\[
\begin{aligned}
 h_{P',b}-h_{P,b}
 &=
 \frac{D_{P,q}}{n+2}
 \left(u_q-\frac1{n+1}\sum_{p\in P}u_p\right),\\
 \|h_{P',b}-h_{P,b}\|_1
 &=\frac{2|D_{P,q}|}{n+2},\\
 \|h_{P',b}-h_{P,b}\|_2^2
 &=\frac{D_{P,q}^2}{(n+1)(n+2)}.                                 \tag{10f}
\end{aligned}
\]

The finite regulators are compatible under \(L^2\)-orthogonal projection: the projection of
\(h_{P',b}\) onto the old span is \(h_{P,b}\).  Thus bounded Hilbert energy produces an
\(L^2\) limit, but `(10b)` shows that strict mixed landing is an additional arithmetic theorem.

### Coherent finite packet

The infinite theorem cannot be replaced by finite-packet estimates or uniform mixed-norm
boundedness.  Let \(P\) be a finite prime set of cardinality \(n\geq1\), and define

\[
 h_{P,c}
 =
 \frac{c}{n+1}
 \sum_{p\in P}\frac{f_p}{\log p}.                                \tag{10}
\]

Then \(h_{P,c}\) is in the finite real logarithmic Kummer span and

\[
\begin{aligned}
 a_\infty(h_{P,c})&=\frac{nc}{n+1},\\
 a_p(h_{P,c})&=-\frac{c}{n+1}\quad(p\in P),\\
 \int_Yh_{P,c}\,d\lambda&=0,\\
 \langle h_{P,c},f_p\rangle&=c\log p\quad(p\in P).                \tag{11}
\end{aligned}
\]

It is the unique rational-place-component-constant realization in
\(\operatorname{span}_{\mathbb R}\{f_p:p\in P\}\) satisfying the finite coherent contrast and
degree-zero equations.  Arbitrary zero-average fluctuations inside a place component are
invisible to these equations and are not claimed unique.  Its exact norms are

\[
 \|h_{P,c}\|_1=\frac{2n}{n+1}|c|,
 \qquad
 \|h_{P,c}\|_2^2=\frac{n}{n+1}c^2.                               \tag{12}
\]

Thus finite realizations of an off-critical radial exponent remain uniformly bounded in both
norms.

For nested packets \(P_n\subset P_m\) with \(|P_j|=j\),

\[
 \|h_{P_m,c}-h_{P_n,c}\|_1
 =
 2|c|\frac{m-n}{m+1}.                                           \tag{13}
\]

In particular, if \(m\geq2n+1\), the distance is at least \(|c|\), so the net is not
\(L^1\)-Cauchy when \(c\neq0\).  In bare \(L^2\), however,

\[
 h_{P,c}\longrightarrow
 c\,1_{Y(\mathbb Q,\infty)},\qquad
 \left\|h_{P,c}-c1_{Y(\mathbb Q,\infty)}\right\|_2^2
 =\frac{c^2}{n+1}.                                             \tag{14}
\]

The \(L^2\) limit has integral \(c\), whereas every finite stage has integral zero.  The
compensating finite-place mass has escaped through the cofinal end of the prime set.
Moreover,

\[
 \left\|h_{P,c}-c1_{Y(\mathbb Q,\infty)}\right\|_1=|c|,          \tag{15}
\]

so the mixed topology detects the escape exactly.

### Sharp all-\(L^q\) source-memory wall

`[PROVED HERE] [COFINAL_SOURCE_MEMORY_EXPONENT_WALL]`

The Hilbert failure in `(14)` is not specific to \(q=2\).  In the rational-place
component-constant chart, let \(1\leq q<\infty\).  Since the difference
\[
 h_{P,c}-c1_{Y(\mathbb Q,\infty)}
\]
has value \(-c/(n+1)\) on the archimedean component and on each of the \(n=|P|\)
finite-place components in \(P\), and vanishes on every other component,
\[
 \boxed{\quad
 \left\|h_{P,c}-c1_{Y(\mathbb Q,\infty)}\right\|_q^q
 =
 |c|^q(n+1)^{1-q}.
 \quad}                                                       \tag{15a}
\]
For the supremum norm,
\[
 \left\|h_{P,c}-c1_{Y(\mathbb Q,\infty)}\right\|_\infty
 =
 \frac{|c|}{n+1}.                                            \tag{15b}
\]
Consequently,
\[
 \begin{aligned}
 h_{P,c}&\longrightarrow c1_{Y(\mathbb Q,\infty)}
 &&\text{strongly in every }L^q,\quad 1<q\leq\infty,\\
 \left\|h_{P,c}-c1_{Y(\mathbb Q,\infty)}\right\|_1&=|c|
 &&\text{for every finite }P.
 \end{aligned}                                               \tag{15c}
\]
Every finite regulator has product-formula integral zero, whereas the strong
\(L^q\), \(q>1\), limit has integral \(c\).  Thus the product-formula degree is
not closed in any bare \(L^q\) source completion above exponent one.  Exponent
one is the sharp source-memory wall on the coherent radial sector.

This gives a route-wide no-go and a positive capability criterion:

```text
bare Lq energy or boundedness, q>1
  admits every coherent off-critical radial charge;

complete place-record control in l1
  keeps the product-formula conservation law closed.
```

The conclusion is not that every viable space must literally be \(L^1\).
It must dominate the complete place-average record on this sector, or retain an
equivalent invariant such as the prime-valuation measure class or the irregular
Rees/Stokes charge.  A Hilbert rigging may still provide energy in its middle
space, but its source test topology cannot be reconstructed from a bare
\(L^q\), \(q>1\), norm.

Equations `(10)`--`(15)` identify the missing infinite datum:

```text
finite prime packets + bounded energy
  do not force purity;

strong source convergence with no prime-infinity leakage
  forces purity.
```

This is the radial analogue of covariance leakage in finite clock truncations.  It also explains
why scalar adelic \(L^2\) restores covariance but admits the wrong coherent radial limit.

## 4. Algebraization firewall

The full complex conormal holonomy must not be forced into a finite algebraic or integral fibre.
By the Six Exponentials Theorem, if \(p_1,p_2,p_3\) are multiplicatively independent primes and
all three numbers \(p_j^\rho\) are algebraic, then \(1,\rho\) cannot be
\(\mathbb Q\)-linearly independent.  The same statement applies to
\(p_j^{\rho-1/2}\).  A nontrivial zeta zero is nonreal, so at least one of these three centered
holonomies is transcendental.

Consequently:

- the integral/Kummer realization may control the real logarithmic metric anomaly;
- the transcendental unitary phase must remain in the distributional character realization;
- algebraizing full holonomy would exclude known critical-line zeros and is therefore false.

This is why `(3)` is polar and fractured rather than one integral spectral fibre.

## 5. Frozen source theorem

> **[CONJECTURE -- SOURCE-EFFECTIVE PRINCIPAL-CONORMAL POLAR REGULATOR LANDING.]**
> Let \(\operatorname{Line}_{\Xi}^{\rm src,cal}\) be the groupoid of source-calibrated rank-one
> factors of the distinguished principal \(\Xi\)-conormal with their rational-dilation transport.
> The completed Euler--Gamma/co-Poisson source object has a source-defined polar regulator
> \[
>   \operatorname{PolAr}^{\rm src}:
>   \operatorname{Line}_{\Xi}^{\rm src,cal}
>   \longrightarrow E_{\rm Kum},
> \]
> constructed before divisor specialization and additive under tensor product, with:
>
> 1. **Pointed production.**  The regulator is induced by the distinguished source-effective
>    section and its principal conormal, not by a zero-indexed eigenvector or a chosen divisor
>    expansion.
> 2. **Joint integral--Hermitian realization.**  Its real logarithmic metric anomaly and its
>    finite valuation residues are images of one pointed source cochain.  Their comparison is the
>    already-constructed strict Kummer--Arakelov principal boundary, so the radial output lies in
>    \(E_{\rm Kum}\), not merely \(L^2(Y)\).
> 3. **Exact prime character comparison.**  At every nontrivial divisor fibre \(\rho\), the radial
>    output \(h_\rho\) satisfies, for the prime transport \(T_p\) on the calibrated conormal line,
>    \[
>      \langle h_\rho,f_p\rangle
>      =
>      \log\frac{\|T_pv\|}{\|v\|}
>      =
>      \left(\frac12-\operatorname{Re}\rho\right)\log p
>    \]
>    for every nonzero \(v\) and every rational prime, while the unitary phase
>    \(p^{-i\operatorname{Im}\rho}\) remains in the prime-angle distributional factor.
> 4. **Jet conservativity.**  Every nonzero principal conormal multiplicity jet survives.  Its
>    nilpotent polynomial factors remain on the distributional side and do not alter the radial
>    semisimple character.
> 5. **Strict source covariance.**  Finite-packet regulators form a Cauchy net in the mixed
>    topology under every source-equivalent prime exhaustion.  Equivalently, the distinguished
>    source conormal has no radial charge at prime infinity.
> 6. **Presentation independence.**  Euler windows, Gamma transgression gauges, and co-Poisson
>    presentations related by the proved source equivalences induce the same polar regulator.

The conjecture plus the theorem of Section 2 proves RH.

If Clause 3 is stated only as fibrewise existence of some \(h_\rho\), it is RH-equivalent:
under RH one may choose \(h_\rho=0\).  The proposed frontier content is Clauses 1--2 and 5--6:
one global source comparison constructed independently of the divisor and proved strongly
convergent before specialization.

## 6. Why this theorem is plausible but not proved

The corpus supplies all target-side and model-side parts separately:

1. `DAC_ADELIC_KUMMER_GELFAND_TRIPLE` constructs the strict product-formula/energy rigging.
2. `DAC_REAL_KUMMER_ARAKELOV_BOUNDARY` constructs the continuous real principal boundary and
   strict completed endpoint.
3. `DAC_ADELIC_PLACE_AVERAGE_RESIDUE` identifies place averages with normalized valuation
   residues and proves field-norm contractions.
4. The source-conormal topology theorem proves that a nonzero HT conormal requires a strict
   refinement; the projective-calibration theorem proves that topology alone does not fix its
   Hermitian scale.
5. The irrational triptic source-effectivity theorem proves in an actual HT model that one
   pointed cochain can produce compatible analytic, Hermitian, spectral, and integral
   realizations without storing the observed germ.
6. The Euler--Gamma/co-Poisson construction already supplies a distinguished principal
   conormal before choosing a zero.

What is absent is the typed comparison in Clause 2 for the zeta source.  Analytic principality
does not imply arithmetic Kummer principality, and a globally trivial Hermitian line can have
arbitrary nonunitary flat holonomy.  The comparison must be proved from the source-effective
pointed cochain and its strict all-prime convergence.

## 7. Candidate producer: residue-corrected determinant differential character

The polar regulator should not be attached as an independent metric.  The strongest available
source candidate is a differential determinant character of the completed relative
Wold--Gamma/co-Poisson complex.

At each prime \(p\), the corpus already proves two readings of one multiplication-Wold defect:

\[
\begin{aligned}
\text{regular reading:}\quad&
 \frac{\det_2(I-tE_pQ)}{\det_2(I+tE_pQ)}
 =
 \frac{\Phi(t)}{\Phi(t/p)},\\
\text{singular reading:}\quad&
 \operatorname{Res}_{\rm BV}(E_p)
 =
 (1-p^{-1})\operatorname{Res}_{\rm BV}.                         \tag{16}
\end{aligned}
\]

The first line is the polarized Gamma determinant cocycle.  The second is both the renormalized
first-trace density and the actual BV principal-conormal coefficient.  General
Quillen--Bismut--Freed determinant theory packages index, connection, curvature, and holonomy in
one determinant line; for regularized infinite-dimensional bundles, the regularized first Chern
form differs from determinant curvature by a residue correction.  Equation `(16)` is the
source-specific arithmetic candidate for exactly such a correction.

> **[PROOF HYPOTHESIS -- ARITHMETIC RESIDUE-CORRECTED DETERMINANT CHARACTER.]**
> Construct before divisor specialization one source differential character
> \[
>   \widehat{\operatorname{Det}}_{\Xi}^{\rm src}
> \]
> whose:
>
> 1. integral characteristic class is the Tate--Kummer/Wold index class;
> 2. regular holonomy is the polarized Gamma cocycle in `(16)`;
> 3. singular curvature/transgression is the BV first-trace class in `(16)`;
> 4. Hermitian real regulator is valued in the strict mixed Kummer--Arakelov coefficient;
> 5. distinguished determinant section is the completed Euler--Gamma/co-Poisson source section;
> 6. conormal of that section is the source principal conormal, with no radical loss.

The real logarithmic norm component of this one character would be
\(\operatorname{PolAr}^{\rm src}\).  Its unitary holonomy would supply the phase factor, while its
integral characteristic class and residue correction would supply the finite-place and
archimedean boundary data.  This is the same architecture proved in the irrational triptic model:
one pointed source cochain produces compatible Hermitian, holonomy, spectral, and integral
realizations.

This hypothesis is not ordinary Quillen-metric positivity.  The corpus proves that the basic
Quillen Laurent weight cannot be the unweighted Hardy--Green Ward norm.  The present mechanism
uses neither that norm nor a Ward inequality.  It uses the logarithmic metric anomaly and must
retain the missing first-trace/BV residue rather than discard it through \(\det_2\).

The hypothesis fails if `(16)` remains only equality of scalar reporters, if no determinant
section is produced before its zeros, or if the residue-corrected real regulator does not land in
the strict \(L^1\) channel.

### Prime-sieve correction `[PROVED; LOAD-BEARING]`

The independent one-prime defects in `(16)` cannot be multiplied over all primes.  Their regular
parts tend to the same nonidentity Gamma phase and their singular coefficients tend to one.  Such
a product diverges and does not define \(\widehat{\operatorname{Det}}_{\Xi}^{\rm src}\).

The paper-proved replacement is the nested coprime sieve.  For a finite prime set \(P\), let
\[
 E_P=\prod_{p\in P}(I-S_pS_p^*),\qquad
 Q_P=E_PQ,
\]
and put
\[
 \Phi_P(t)
 =
 \frac{\det_2(I-tQ_P)}{\det_2(I+tQ_P)},\qquad
 a_P=\prod_{p\in P}(1-p^{-1}).
\]
If \(p\notin P\), then
\[
\begin{aligned}
 \Phi_{P\cup\{p\}}(t)&=\frac{\Phi_P(t)}{\Phi_P(t/p)},\\
 a_{P\cup\{p\}}&=a_P(1-p^{-1}),\\
 J(E_{P\cup\{p\}}p_a)&=a_{P\cup\{p\}}J(p_a).             \tag{16a}
\end{aligned}
\]
The regular increments in `(16a)` are \(O(p^{-3})\) locally uniformly on \(|t|<1\).  Along every
prime exhaustion, the singular increments telescope exactly:
\[
 \sum_n\frac{a_{P_{n-1}}}{p_n}=1.                        \tag{16b}
\]
Thus the nested regular/singular source character converges before divisor specialization.
Its coarse limit retains only the one-dimensional occupation vacuum and kills the conormal because
\(a_P\to0\), while its source-normal blow-up retains
\[
 a_P^{-1}J(E_Pp_a)=J(p_a).                               \tag{16c}
\]

The same Wold/BV renewal gives a canonical product probability on all prime valuations,
\[
 \mu_0=\bigotimes_p\mu_p,\qquad
 \mu_p(k)=(1-p^{-1})p^{-k}.                               \tag{16d}
\]
The event that every prime in \(P\) has valuation zero has mass \(a_P\); conditioning on these
events is exactly the normal blow-up `(16c)`.

For a centered coherent radial exponent \(c\), squared-amplitude twisting by \(p^{ck}\) changes
the local law to
\[
 \mu_{p,c}(k)
 =
 (1-p^{-(1-2c)})p^{-(1-2c)k}.
\]
The exact local Hellinger affinity is
\[
 H_p(c)
 =
 \frac{
 \sqrt{(1-p^{-1})(1-p^{-(1-2c)})}
 }{
 1-p^{-(1-c)}
 }.
\]
Kakutani's theorem and Euler's divergence of \(\sum_pp^{-1}\) prove
\[
 \bigotimes_p\mu_{p,c}\sim\mu_0
 \quad\Longleftrightarrow\quad c=0.                      \tag{16e}
\]
Arbitrary unitary phase is retained as a separate actual sector label and does not change the
radial measure law.

The hostile corpus audit identifies the scalar Hellinger numerator exactly with a pre-existing
formal reflection aperture:
\[
\left(p^{-1/2}-p^{-(1/2-c)}\right)^2
=
\operatorname{weightedPrimeClockReflectionLogMomentEnergy}
\left(0,-c,\frac{1+c}{2};p\right).                       \tag{16f}
\]
Therefore its prime sum is finite exactly for \(c=0\), by the already proved aperture law; this
identity and corollary are formalized in
`formal/GaloisForLFunctions/RHTower/PrimeValuationKakutaniRadialPurity.lean`.
The scalar selector is not candidate-new mathematics.  Candidate novelty begins only when the
Wold/BV source law, valuation product sector, singular boundary blow-up, and Xi conormal
source-normality are joined.

Equations `(16a)`--`(16e)` construct the previously missing third completion on the target and
finite-source sides: a field of prime-valuation product sectors with a singular normal blow-up.
It is Hausdorff, implements prime Wold shifts, retains the normalized principal conormal, and
separates every coherent off-critical radial ray.  What remains is not to invent a completion but
to prove that the completed Xi principal conormal is normal in its source-generated critical
product sector.

This also corrects the determinant-character hypothesis above.  Its all-prime object must be the
nested sieve character and its source-normal blow-up, not a direct product of the one-prime
reporters in `(16)`.

## 8. First proof obstacle

For each finite prime packet \(P\), construct a logarithmic norm-cocycle regulator

\[
 \operatorname{PolAr}_P:
 \operatorname{Line}_{\Xi,P}^{\rm src,cal}
 \longrightarrow
 E_{{\rm Kum},P}                                                \tag{17}
\]

from:

- the integral multiplicative source core;
- the Gamma/real Kummer transgression;
- finite Rost--Schmid residues;
- the distinguished co-Poisson principal conormal;
- the source-fixed Hermitian calibration.

The regulator is a morphism of calibrated line/Picard groupoids, additive under tensor product.
It is not a linear map from conormal cohomology into the scalar Kummer module.  Such a linear
equivariant map would collide with the proved identity action on the centered scalar Kummer
sector and would already encode purity.

Then prove that the transition defect

\[
 \operatorname{PolAr}_{P'}-
 \operatorname{res}_{P,P'}^\ast\operatorname{PolAr}_P            \tag{18}
\]

is exactly the already-identified Wold/Gamma/BV boundary cell, with no unrecorded radial mass.
The first genuinely new estimate is that the telescoped defects make
\((\operatorname{PolAr}_P)_P\) Cauchy in \(\|\cdot\|_1+\|\cdot\|_2\), not merely bounded there.
Equations `(10)`--`(15)` show why boundedness cannot suffice.

The new prime-sieve theorem makes this obstacle quantitative.  For \(0<r<1\), define
\[
 \delta_r(P,p)
 =
 \frac{a_P}{p}
 +
 \sup_{|t|\leq r}|\log\Phi_P(t/p)|.
\]
Then \(\sum_n\delta_r(P_{n-1},p_n)<\infty\) for every prime exhaustion.  It is enough to construct
the source-normal polar transgression with a packet-independent estimate
\[
 \|\operatorname{PolAr}_{P\cup\{p\}}-\operatorname{PolAr}_P\|_{L^1+L^2}
 \leq C\,\delta_r(P,p).                                    \tag{18a}
\]
This is the strict Kummer reading of critical-sector normality.  The product-sector reading is
that every normalized Xi conormal fibre is a normal functional in the sector `(16d)`.  Either
comparison, constructed source-first and proved multiplicity-faithful, invokes `(16e)` or the
mixed Kummer selector and proves RH.

## 9. Hostile falsifiers

Retire or revise the conjecture if any of the following occurs.

1. The source principal conormal has no integral--Hermitian comparison before choosing a zero.
2. The comparison lands only in \(L^2(Y)\), so the product-formula boundary is lost.
3. Finite regulators are uniformly bounded but reproduce the leakage sequence `(10)` rather than
   a mixed-Cauchy net.
4. Hermitian calibration is inferred from the projective conormal topology, contradicting the
   formalized scale-separation theorem.
5. The regulator depends on \(\rho\), \(\operatorname{Re}\rho\), a zero enumeration, or deletion
   of non-moderate fibres.
6. Full complex holonomy is forced into the integral realization, contradicting the
   Six-Exponentials firewall and known critical-line phases.
7. An explicit off-line generalized-prime Euler system carries the same literal rational
   integral source, strict Kummer--Arakelov comparison, pointed principal conormal, and
   presentation-independent mixed-Cauchy regulator.  Positive source density, functional
   equation, entire completion, hypertranscendence, and Julia orientation alone do not meet this
   falsifier.
8. The only proof of mixed convergence imports Weil positivity, self-adjointness, or RH under
   another name.
9. The residue-corrected determinant character is replaced by the ordinary Quillen metric whose
   wrong Laurent mode weight is already proved, or its first-trace/BV correction remains a scalar
   identity with no source comparison map.

## 10. Literature boundary

Closest primary parents are:

- Allcock--Vaaler for the place-space \(L^1/L^2\) geometry and product-formula hyperplane;
- Deninger for the generic character space, Tate regulator, and arithmetic dynamical program;
- Meyer for the nuclear spectral quotient carrying the zeta divisor;
- Paugam for the symplectic functional-equation pairing on the Connes--Meyer spectrum;
- Felder--Henriques--Rossi--Zhu for a source-produced joint Hermitian/integral differential
  character in the elliptic-gamma model;
- Freed for determinant-line curvature and holonomy, Paycha--Rosenberg for residue corrections
  between regularized first Chern forms and determinant curvature, and Scott for relative
  zeta-determinant/Quillen boundary formulas.

Targeted searches found no source-first construction sending the Riemann principal conormal to a
strict mixed Kummer--Arakelov radial regulator, and no prime-infinity leakage classification used
as an RH mechanism.  This is a provisional noncollision result, not a priority claim.

## Gates

- [x] 0 \(\to\) 1: source-pure target, exact receiver, selector, and falsifiers stated
- [x] infinite mixed place-average selector paper-proved
- [x] finite symmetric packet and exact prime-infinity leakage paper-proved
- [x] sharp all-\(L^q\), \(q>1\), source-memory failure paper-proved
- [x] full-holonomy algebraization firewall identified
- [ ] specialist audit of the strict polar receiver and leakage mechanism
- [ ] finite source polar regulator `(17)` constructed
- [ ] transition identity `(18)` proved from Gamma/Wold/BV source data
- [ ] mixed-Cauchy no-leakage theorem proved without divisor input
- [ ] fibre character and multiplicity-jet comparison proved
- [ ] dependency-closed paper proof
- [ ] unconditional Lean formalization
- [ ] RH

## References

- Daniel Allcock and Jeffrey D. Vaaler,
  *A Banach space determined by the Weil height*:
  https://arxiv.org/abs/0808.1038
- Paul Fili and Zachary Miner,
  *Orthogonal decomposition of the space of algebraic numbers and Lehmer's problem*:
  https://arxiv.org/abs/0911.1975
- Christopher Deninger, *Dynamical systems for arithmetic schemes*:
  https://arxiv.org/abs/1807.06400
- Ralf Meyer, *A spectral interpretation for the zeros of the Riemann zeta function*:
  https://arxiv.org/abs/math/0412277
- Frédéric Paugam, *Spectral symmetries of zeta functions*:
  https://arxiv.org/abs/0803.0199
- Giovanni Felder, André Henriques, Carlo A. Rossi, and Chenchang Zhu,
  *A gerbe for the elliptic gamma function*:
  https://arxiv.org/abs/math/0601337
- Daniel S. Freed, *Determinant Line Bundles Revisited*:
  https://arxiv.org/abs/dg-ga/9505002
- Sylvie Paycha and Steven Rosenberg,
  *Curvature on determinant bundles and first Chern forms*:
  https://arxiv.org/abs/math/0009172
- Simon Scott, *Relative Zeta Determinants and the Quillen Metric*:
  https://arxiv.org/abs/math/9910148

## Log

- 2026-07-29 — Replaced the full-holonomy p-local algebraization attempt by a polar receiver.
  Proved the infinite mixed-Kummer coherent-power selector and classified the exact finite
  prime-infinity leakage which bare \(L^2\) admits.  Froze the source-effective principal-conormal
  polar regulator landing conjecture; isolated strong mixed convergence, rather than bounded
  energy, as the first non-immediate source theorem.
- 2026-07-29 — Typed the polar regulator as a logarithmic norm cocycle on calibrated conormal
  lines rather than an impossible linear map to the scalar Kummer module.  Isolated a
  residue-corrected determinant differential character as the strongest source producer:
  Wold--Gamma \(\det_2\) is its regular holonomy and the matched BV/renormalized-first-trace class
  is its mandatory singular correction.
- 2026-07-29 — Identified the prime-valuation Hellinger numerator with the existing damped
  prime-clock reflection energy at \((0,-c,(1+c)/2)\) and formalized its exact radial-purity
  locus.  This removes the scalar divergence calculation from the novelty claim and sharpens the
  open core to Xi conormal source-normality in the source-derived valuation sector.
- 2026-07-29 — Normalization-amplification no-go corrected the proposed quantitative producer.
  The nested sieve controls the unnormalized decrement \(a_P/p\), while its normalized
  conditional boundary states move by exactly \(1/p\) and are not total-variation Cauchy.
  Therefore `(18a)` cannot be inferred from the finite-variation relative character.  The live
  target must be a singular relative/Rees or Bockstein transgression retaining the vanishing
  scale and its presentation maps, not ordinary mixed-Cauchy convergence of normalized states
  obtained from `(16b)`.
- 2026-07-30 — Strengthened the prime-infinity leakage theorem from the \(L^1/L^2\) comparison
  to the exact all-\(L^q\) wall `(15a)`--`(15c)`.  Every bare \(L^q\) completion with \(q>1\)
  strongly absorbs a nonzero coherent radial charge into the archimedean component, while
  \(L^1\) retains a fixed distance \(|c|\).  The third completion must therefore preserve the
  complete place record, not merely improve Hilbert integrability.
