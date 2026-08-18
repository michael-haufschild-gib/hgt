# Prime--Wold accelerated-type modular-drift law

- **ID:** `prime-wold-accelerated-type-modular-drift-law`
- **Stage:** 2-fully-proven
- **Type:** EXACT ASYMPTOTIC-TYPE THEOREM / SOURCE NO-SEWING CLASSIFICATION
- **Scientific status:** `[PAPER-PROVED] [NOVELTY PROVISIONAL] [NOT RH]`
  `[NO COMPUTATION] [ZERO-ACCELERATION RH ARCHITECTURE RETRACTED]`
- **Parents:**
  - `../../1-in-progress/prime-valuation-hellinger-rees-reflection-fracture.md`;
  - `../not_new_scientific_knowledge/prime-square-deformed-reflection-line-superessential-fracture.md`;
  - `../not_new_scientific_knowledge/prime-square-mobius-fourier-complementary-record-law.md`;
  - `../prime-sieve-wold-gamma-bv-relative-character.md`;
  - `../new_scientific_knowledge/prime-occupation-polarized-gamma-phase-survival.md`;
  - `../../1-in-progress/source-modular-drift-realization-equivalence-law.md`;
  - `../../4-publication-ready/riemann-divisor-prime-transfer-spectrum/main.tex`;
  - `../../4-publication-ready/riemann-orientation-boundary-fracture/main.tex`.

## 1. Why the all-orders-flat radical is still too coarse

Let
\[
 a_x=\prod_{p\leq x}(1-p^{-1})
\]
be the ordinary-prime Wold boundary volume and let
\[
 {\cal H}_x(c)
 =
 \prod_{p\leq x}
 \frac{\sqrt{(1-p^{-1})(1-p^{-(1-2c)})}}
      {1-p^{-(1-c)}},
 \qquad |c|<\frac12,
\]
be the Hellinger affinity between the critical prime-valuation sector and radial drift \(c\).
The existing Hellinger--Rees theorem proves
\[
 {\cal H}_x(-c)
 =
 C_-(c)a_x^{1/2}(1+o(1)),
 \qquad
 \log{\cal H}_x(c)
 =
 -\frac{x^{2c}}{4c\log x}(1+o(1))
 \tag{1}
\]
for \(0<c<1/2\), where \(C_-(c)>0\).

Both
\[
 \exp(-C/a_x)
 \quad\hbox{and}\quad
 {\cal H}_x(c)
\]
are flat beyond every finite Rees order. They are nevertheless separated by one full
acceleration level: no factor with logarithm polynomial in \(a_x^{-1}\) can turn the second into
the first or into \(a_x^{1/2}\).

This card resolves that lost level.

## 2. Accelerated Rees type

For \(y\geq0\), put
\[
 \ell_2(y)=\log\!\bigl(1+\log(1+y)\bigr).
 \tag{2}
\]
For a family of bounded operators \(R_x\), define its upper accelerated Wold type by
\[
 \operatorname{Acc}_a(R)
 :=
 \limsup_{x\to\infty}a_x\,\ell_2(\|R_x\|).
 \tag{3}
\]
Finite-Rees families have accelerated type zero. More generally,
\[
 \log^+\|R_x\|=O(a_x^{-K})
 \quad\hbox{for one fixed }K
 \tag{4}
\]
also implies \(\operatorname{Acc}_a(R)=0\). Thus `(3)` permits ordinary essential singularities
such as \(\exp(C/a_x)\); it excludes only the next, accelerated level.

For \(c\ne0\), define the oriented Hellinger reflection type
\[
 {\mathfrak a}_{\rm Hel}(c)
 :=
 \operatorname{sgn}(c)
 \lim_{x\to\infty}
 a_x\log\left|
 \log\frac{{\cal H}_x(-c)}{{\cal H}_x(c)}
 \right|,
 \tag{5}
\]
provided the limit exists, and put \({\mathfrak a}_{\rm Hel}(0)=0\).

## 3. Exact accelerated-type theorem

`[PROVED HERE]`

For every \(|c|<1/2\),
\[
 \boxed{
 {\mathfrak a}_{\rm Hel}(c)=2e^{-\gamma}c.
 }
 \tag{6}
\]

### Proof

It is enough to take \(0<c<1/2\). By `(1)`,
\[
 \log\frac{{\cal H}_x(-c)}{{\cal H}_x(c)}
 =
 \frac{x^{2c}}{4c\log x}(1+o(1)),
 \tag{7}
\]
because \(\log{\cal H}_x(-c)=\frac12\log a_x+O(1)=O(\log\log x)\), negligible beside
\(x^{2c}/\log x\). Hence
\[
 \log\log\frac{{\cal H}_x(-c)}{{\cal H}_x(c)}
 =
 2c\log x-\log\log x-\log(4c)+o(1).
 \tag{8}
\]
Mertens' product theorem gives
\[
 a_x\log x\longrightarrow e^{-\gamma},
 \qquad
 a_x\log\log x\longrightarrow0.
 \tag{9}
\]
Multiplying `(8)` by \(a_x\) proves `(6)` for \(c>0\). Replacing \(c\) by \(-c\) inverts the
ratio in `(5)` and supplies the orientation. `QED`

Equation `(6)` refines the value \(+\infty\) of ordinary Rees order into the exact continuum
\[
 0<2e^{-\gamma}c<e^{-\gamma}.
 \]
Horizontal displacement is therefore not merely membership in the flat radical. It is the
accelerated type inside that radical.

## 4. Universal zero-type no-sewing theorem

`[PROVED HERE]`

Let \(E_x,F_x\) be arbitrary normed spaces, with no dimension restriction. Suppose
\[
 R_x:E_x\longrightarrow F_x
\]
is bounded and
\[
 R_xv_x(c)=v_x(-c),
 \qquad
 \|v_x(\pm c)\|={\cal H}_x(\pm c)
 \tag{10}
\]
for one \(0<c<1/2\). Then
\[
 \boxed{
 \liminf_{x\to\infty}
 a_x\,\ell_2(\|R_x\|)
 \geq 2e^{-\gamma}c.
 }
 \tag{11}
\]
In particular, no operator family satisfying `(4)` can sew the two reflected Hellinger sectors.

Indeed, `(10)` gives
\[
 \|R_x\|
 \geq
 \frac{\|v_x(-c)\|}{\|v_x(c)\|}
 =
 \frac{{\cal H}_x(-c)}{{\cal H}_x(c)}.
 \tag{12}
\]
Monotonicity of \(\ell_2\), followed by `(7)`--`(9)`, proves `(11)`.

The theorem remains valid if the two norms in `(10)` differ from the Hellinger norms by
bi-zero-type source gauges. Consequently the load-bearing hypothesis in the RH application is
not a chosen equality of scalar norms. It is a pre-divisor source comparison whose operator,
inverse, and landing gauges all have accelerated type zero.

## 5. The three source scales

The existing corpus now has three exact scales.

### 5.1 Full Wold--Gamma first trace: type zero

The reflected Wold--Gamma gauge has
\[
 \|G_x(t)\|
 =
 \exp\!\left(\frac{2\operatorname{Re}t}{a_x}\right).
 \tag{13}
\]
For fixed \(t\),
\[
 a_x\ell_2(\|G_x(t)\|)\longrightarrow0.
 \tag{14}
\]
The same holds for its inverse. Thus the essential singularity already present in Gamma has
accelerated type zero.

This is consistent with the exact occupation determinant decomposition. The unique divergent
piece is the first trace \(Z_P(1)=a_P^{-1}\); every higher odd trace has a cofinal finite limit.
Therefore the complete Wold--Gamma determinant torsor is first-level essential, not accelerated.

There is a source-linked compact-uniform version. Let
\[
 {\cal F}_x=\bigotimes_{p\leq x}{\cal F}_p
\]
be the full prime-square Fourier tensor, retaining all three valuation channels, and let
\(\Phi_x^{\rm reg}(t)\) be the tangent-normalized occupation determinant after removal of its
first trace. On every fixed compact \(K\) avoiding the real occupation divisor,
normal convergence of the genus-one product gives
\[
 \sup_{t\in K}
 \max\left(
 |\Phi_x^{\rm reg}(t)|,\,
 |\Phi_x^{\rm reg}(t)|^{-1}
 \right)\leq C_K
 \tag{14a}
\]
cofinally. Since \({\cal F}_x\) is unitary, the full finite-aperture comparison
\[
 {\cal U}_x(t)
 :=
 {\cal F}_x\widehat\otimes
 \begin{pmatrix}
  \Phi_x^{\rm reg}(t)&0\\
  0&\exp(2t/a_x)
 \end{pmatrix}
 \tag{14b}
\]
satisfies
\[
 \sup_{t\in K}
 \log
 \max\left(
 \|{\cal U}_x(t)\|,\,
 \|{\cal U}_x(t)^{-1}\|
 \right)
 \leq
 \frac{2M_K}{a_x}+O_K(1),
 \qquad
 M_K=\sup_{t\in K}|\operatorname{Re}t|.
 \tag{14c}
\]
Hence the literal full-clock plus Wold--Gamma determinant comparison has compact-uniform
accelerated type zero. This proves the growth part of the candidate source operator before
restricted adelic, Sonin, Meyer, and Xi-conormal interfaces are attached.

### 5.2 Hellinger reflection: displacement-dependent positive type

Equation `(6)` gives
\[
 \operatorname{type}_{\rm required}(c)=2e^{-\gamma}|c|.
 \tag{15}
\]
Equivalently, a scalar sewing multiplier must satisfy
\[
 \log\|R_x\|
 \geq
 \frac{x^{2|c|}}{4|c|\log x}(1+o(1)).
 \tag{16}
\]
In the Wold coordinate this is
\[
 \log\|R_x\|
 \geq
 \left(\frac{e^\gamma}{4|c|}+o(1)\right)
 a_x
 \exp\!\left(
 \frac{2|c|e^{-\gamma}+o(1)}{a_x}
 \right).
 \tag{17}
\]
It is an exponential of an exponential relative to \(a_x^{-1}\), not a Gamma-type factor.

### 5.3 Scalar prime-square reflected-line compression: saturated type

Let
\[
 B_x(c)=\prod_{p\leq x}\beta_p(c)
\]
be the critical-normalized scalar reflected-line compression from the literal prime-square
Fourier clock. The proved law
\[
 \log B_x(c)=(|c|+o(1))\vartheta(x)
\]
and the prime number theorem imply
\[
 \boxed{
 \lim_{x\to\infty}a_x\ell_2(B_x(c))=e^{-\gamma}
 \qquad(c\ne0).
 }
 \tag{18}
\]
Scalarization therefore sends every nonzero drift to the maximal strip-boundary type
\(e^{-\gamma}\), erasing its magnitude. This is the precise mathematical damage caused by
discarding the complementary Fourier record.

By contrast, the full prime-square Fourier tensor is unitary between its complete
continuation--record sectors. Its operator norm has type zero. The record does not prove RH, but
it removes the artificial saturated type `(18)` before the Gamma first-trace torsor is attached.

### 5.4 Gamma--Sonin depth matching: type zero

The Sonin aperture cannot be compared with prime cutoff arbitrarily. The Wold first trace fixes
its logarithmic depth. Fix \(r>1\) and define
\[
 N_x=
 \left\lfloor\frac{2}{a_x\log r}\right\rfloor,
 \qquad
 b_x=a_0r^{-N_x}.
 \tag{18a}
\]
This schedule is source-defined and independent of a zero. It obeys
\[
 0\leq\frac2{a_x}-N_x\log r<\log r.
 \tag{18b}
\]

Burnol--Sonin aperture-type rigidity gives, for an off-axis annihilator character \(\rho\),
\[
 \|k_{\rho,b_x}\|
 \asymp_\rho
 r^{N_x|\operatorname{Re}\rho-1/2|}.
 \tag{18c}
\]
Put \(d_\rho=|\operatorname{Re}\rho-1/2|\). Equation `(18b)` yields the sharp comparison
\[
 r^{-d_\rho}\exp(2d_\rho/a_x)
 \leq
 r^{N_xd_\rho}
 \leq
 \exp(2d_\rho/a_x).
 \tag{18d}
\]
Consequently
\[
 \boxed{
 \|k_{\rho,b_x}\|
 \asymp_\rho
 \exp(2d_\rho/a_x).
 }
 \tag{18e}
\]

The right side is exactly the larger of the two reflected Wold--Gamma gauge norms. Thus Gamma
first trace, co-Poisson character, and Sonin aperture escape have the same height-one essential
type after source depth is matched. The orthogonal Meyer/co-Poisson projection is contractive and
equals the full evaluator on a zero fibre, so it introduces no additional accelerated type.

This closes another possible hiding place: under the source schedule `(18a)`, Sonin/Meyer cannot
supply the positive accelerated type `(15)` required to identify reflected Hellinger sectors.
Any such type must enter in the still-unconstructed restricted adelic Euler-to-Poisson landing.

### 5.5 Restricted adelic Weyl joining is already saturated

The preceding last sentence is not an invitation to conjecture that adelic joining has type
zero.  The standard unramified \(PGL_2\) intertwiner supplies a hostile exact test.

In the normalized induction
\[
 f\!\left(\begin{pmatrix}x&*\\0&1\end{pmatrix}g\right)
 =
 |x|^{1/2}z^{\operatorname{val}(x)}f(g),
\]
the unnormalized local intertwiner \(M_p(z):I(z)\to I(z^{-1})\) acts on the spherical vector by
\[
 m_p(z)=\frac{1-z^2/p}{1-z^2}.
 \tag{18f}
\]
After spherical normalization, \(m_p(z)^{-1}M_p(z)\) has an Iwahori block with eigenvalues
\[
 1,\qquad
 \lambda_p(z)=\frac{pz^2-1}{p-z^2}.
 \tag{18g}
\]
Put \(z_p=p^{c-i\tau}\), where \(0<c<1/2\).  Then
\[
 \log|\lambda_p(z_p)|
 =
 2c\log p+O\!\left(p^{-(1-2c)}+p^{-(1+2c)}\right).
 \tag{18h}
\]
Consequently
\[
 \log\prod_{p\leq x}|\lambda_p(z_p)|
 =
 (2c+o(1))\vartheta(x).
 \tag{18i}
\]

This conclusion is independent of scalar normalization.  The ratio of the two local
eigenvalues is unchanged by a scalar gauge.  For every scalar-normalized finite tensor
\(T_x\) containing the full Iwahori record,
\[
 \|T_x\|\,\|T_x^{-1}\|
 \geq
 \prod_{p\leq x}|\lambda_p(z_p)|.
 \tag{18j}
\]
Hence
\[
 \boxed{
 \liminf_{x\to\infty}
 a_x\ell_2\!\left(
 \max\{\|T_x\|,\|T_x^{-1}\|\}
 \right)
 \geq e^{-\gamma}.
 }
 \tag{18k}
\]
Indeed `(18j)` makes the maximum at least
\(\exp((c+o(1))\vartheta(x))\), and Mertens plus the prime number theorem turn every positive
multiple of \(\vartheta(x)\) into the saturated accelerated type \(e^{-\gamma}\).

The local equality locus is exact:
\[
 |\lambda_p(z_p)|=1
 \quad\Longleftrightarrow\quad
 |z_p|=1
 \quad\Longleftrightarrow\quad
 c=0,
 \tag{18l}
\]
because
\[
 |pz^2-1|^2-|p-z^2|^2
 =(p^2-1)(|z|^4-1).
\]

Thus the standard restricted adelic Weyl comparison has more than enough asymptotic height to
cross every off-line Hellinger fracture.  Spherical normalization merely transfers that height
to the complementary Iwahori record; it does not remove it.  The accelerated invariant is
therefore a faithful drift reporter and a no-sewing theorem for zero-type maps, but it is not a
critical-line selector for the literal adelic joining.

## 6. One modular charge in four charts

Let \(\rho\) be a nontrivial zero, put
\[
 c_\rho=\frac12-\operatorname{Re}\rho,
\]
and let \(m_\rho\) be its multiplicity.

The positive-shell theorem gives the reflection rate
\[
 {\mathfrak r}_{\rm shell}(\rho)
 =
 \lim_{m\to\infty}
 \frac1m\log
 \left|
 \frac{H_m(1-\bar\rho)}{H_m(\rho)}
 \right|
 =
 (2\operatorname{Re}\rho-1)\log2.
 \tag{19}
\]
The Xi Julia current gives
\[
 \operatorname{ReRes}_\rho J_\Xi=m_\rho c_\rho.
 \tag{20}
\]
Combining `(6)`, `(19)`, and `(20)` yields the exact dictionary
\[
 \boxed{
 {\mathfrak a}_{\rm Hel}(c_\rho)
 =
 -\frac{e^{-\gamma}}{\log2}\,
 {\mathfrak r}_{\rm shell}(\rho)
 =
 \frac{2e^{-\gamma}}{m_\rho}\,
 \operatorname{ReRes}_\rho J_\Xi.
 }
 \tag{21}
\]

The adelic Weyl block adds a fourth coordinate.  Define its oriented prime Lyapunov rate by
\[
 {\mathfrak r}_{\rm Weyl}(c)
 :=
 \lim_{x\to\infty}
 \frac1{\vartheta(x)}
 \log\prod_{p\leq x}|\lambda_p(p^{c-i\tau})|.
 \tag{21a}
\]
Equation `(18i)` gives
\[
 \boxed{
 {\mathfrak r}_{\rm Weyl}(c_\rho)
 =
 2c_\rho
 =
 -\frac{{\mathfrak r}_{\rm shell}(\rho)}{\log2}
 =
 \frac{2}{m_\rho}\operatorname{ReRes}_\rho J_\Xi
 =
 e^\gamma{\mathfrak a}_{\rm Hel}(c_\rho).
 }
 \tag{21b}
\]
If \(\beta_\rho=2\operatorname{Re}\rho=1-2c_\rho\) is the conormal modular exponent, then
\[
 {\mathfrak r}_{\rm Weyl}(c_\rho)=1-\beta_\rho.
 \tag{21c}
\]

Julia orientation, positive-shell transfer entropy, Hellinger acceleration, and adelic Weyl
condition-number drift are therefore the same modular charge in local, shell-cofinal,
accelerated-normal, and intertwiner coordinates.  The standard Weyl map does not annihilate the
charge; it pays exactly the modular retuning cost \(1-\beta_\rho\).  This is why an external
essential intertwiner can join off-line fibres while a source-internal twist-preserving base
change could not.

## 7. Finite divisor activation cannot create accelerated type

The preceding operator obstruction becomes relevant to zeros only if divisor specialization cannot
create positive accelerated type from a type-zero source family. That statement is a direct
Cauchy theorem.

`[PROVED HERE] [FINITE_DIVISOR_ACCELERATION_NONCREATION]`

Let \(K\) be a fixed closed disk of radius \(r>0\), let \(T_x(s)\) be a holomorphic
operator-valued family on a neighborhood of \(K\), and suppose
\[
 \limsup_{x\to\infty}
 a_x\,\ell_2\!\left(\sup_{s\in K}\|T_x(s)\|\right)=0.
 \tag{22}
\]
Then for every fixed \(j\geq0\),
\[
 \limsup_{x\to\infty}
 a_x\,\ell_2\!\left(\|T_x^{(j)}(\rho)\|\right)=0
 \tag{23}
\]
at the center \(\rho\). Every fixed finite linear combination of the jets has the same property.

Cauchy's estimate gives
\[
 \frac{\|T_x^{(j)}(\rho)\|}{j!}
 \leq
 r^{-j}\sup_{s\in K}\|T_x(s)\|.
 \tag{24}
\]
Multiplication by the fixed scalar \(j!r^{-j}\), finite sums, and fixed finite matrices do not
change zero accelerated type, proving `(23)`.

Now let
\[
 \Xi(s)=(s-\rho)^m g(s),\qquad g(\rho)\ne0,
 \tag{25}
\]
with finite analytic multiplicity \(m\). Laurent residue, Cartier base change, and top-conormal
extraction at \(\rho\) use only a fixed finite packet of derivatives of \(T_x\), \(\Xi\), and
\(g^{-1}\). Therefore a finite-order Xi divisor specialization of a compact-uniform type-zero
source family still has type zero.

This is the accelerated analogue of finite-jet stability of the all-orders-flat radical. It
rules out a tempting on-shell escape: a finite-order zero cannot cancel or generate the positive
accelerated type required by an off-line Hellinger reflection. The source family itself would
already have to carry that type before the zero was selected.

## 8. Retraction and corrected frontier

`[RETRACTED OPEN CORE: XI_ZERO_ACCELERATION_POISSON_WOLD_LANDING]`

The proposed zero-acceleration landing architecture is false for the standard restricted adelic
Weyl joining. Equation `(18k)` shows that its full continuation--Iwahori record has saturated
accelerated condition number at every \(c\ne0\). This is not a hidden error removable by spherical
normalization: normalization moves the growth between the spherical and transverse channels.
The literal adelic comparison can therefore supply the height required by `(11)`.

What survives is:

1. the exact Hellinger type `(6)`;
2. arbitrary-dimensional no-sewing for genuinely zero-type operator families;
3. the four-chart modular-drift dictionary `(21)`--`(21c)`;
4. finite-divisor noncreation `(23)`; and
5. the exact identification of the adelic Weyl channel as a saturated source of essential
   height.

None of these statements forces a zero to be critical. They classify where the modular drift is
stored.

The corpus already contains the stronger non-metric frontier in
`source-modular-drift-realization-equivalence-law.md`:

`[OPEN CORE: XI_CONTROLLED_CUBICAL_HOMOTOPY_BASE_CHANGE]`

Finite Kummer/BV packets are algebraically exact and their prime-order transgressions are
Hochschild-homotopic. The missing theorem is that their source-canonical higher homotopies,
Gamma first-trace record, Möbius phase, and Poisson/Tate record admit one strict all-prime
controlled totalization, and that Xi Cartier base change conserves this same pointed
twisted-cyclic object together with its gauge-diagonal conormal marginal.

This formulation survives `(18k)`. An essential intertwiner may change the Hilbert metric and
cross the Hellinger radical; it does not thereby become an endomorphism of the fixed
ordinary-prime modular class. The source class has twist \(p^{-1}\), whereas a centered conormal
Born marginal has twist \(p^{-2\operatorname{Re}\rho}\). A single source-internal conservative
base change would therefore give
\[
 p^{-1}=p^{-2\operatorname{Re}\rho},
 \]
and hence \(\operatorname{Re}\rho=1/2\). Constructing that base change, rather than bounding an
available external intertwiner, is the actual RH-bearing task.

## 9. Hostile audit

1. **Still not RH.** The controlled all-prime totalization and conservative Xi base change are
   unconstructed.
2. **Essentiality is not selectivity.** Standard adelic reflection is already essential enough
   to join off-line sectors.
3. **A fitted complementary-series metric is external transport.** It can unitarize an off-line
   fibre but retunes the source modular class.
4. **Full Fourier unitarity is insufficient.** It conserves the complete local record for every
   drift and does not identify a Xi conormal as an internal source base change.
5. **Gamma and Sonin remain type zero at the accelerated scale.** Their exact matching does not
   cancel the saturated Iwahori condition number.
6. **Scalarization and standard Weyl joining both saturate.** They erase the magnitude of
   nonzero displacement at accelerated scale, though the Hellinger and Julia reporters retain it.
7. **Finite Cauchy stability is only negative control.** It proves that finite divisor jets
   cannot manufacture height from a zero-type source; the actual adelic source is not zero-type.
8. **Generalized-prime countermodels remain admissible external dualities.** They are excluded
   only if the ordinary-integer pointed modular class is proved to survive the same Xi base
   change.
9. **No finite-dimensional assumption occurs.** Both no-sewing `(11)` and the Iwahori
   lower bound `(18j)` are full-norm statements.
10. **Hypertranscendence has a supporting, not selecting, role.** It forces the decisive datum
    into the controlled all-prime homotopy rather than a finite reporter; it does not by itself
    conserve the modular twist.

## 10. Literature boundary

Malgrange--Ramis multisummability and Écalle acceleration provide parent theory for filtrations by
different exponential flatness orders. Enhanced irregular Riemann--Hilbert theory retains
exponential factors and Stokes filtrations rather than quotienting them to zero. Orthogonality
catastrophe literature supplies parent language for vanishing infinite-product overlaps.

Targeted searches found no source connecting those general theories to the exact ordinary-prime
law `(6)`, the saturated prime-square type `(18)`, or the four-chart modular-charge identity
`(21)`--`(21c)`. The local formula `(18f)`--`(18g)` is standard \(PGL_2\) representation theory;
`(18h)`--`(18k)` are its direct prime-number-theorem consequence. Novelty is provisional and
belongs only to the arithmetic accelerated-type identifications, not to levelled exponential
flatness, the local intertwiner, or the retracted zero-acceleration architecture.

Primary parent:

- B. Malgrange and J.-P. Ramis, *Fonctions multisommables*, Ann. Inst. Fourier 42 (1992),
  353--368, <https://doi.org/10.5802/aif.1295>.
- F. Calegari and A. Venkatesh, *A torsion Jacquet--Langlands correspondence*, draft,
  Section 6.6.3, equation (6.64),
  <https://www.math.uchicago.edu/~fcale/papers/torsion.pdf>.

## Gates

- [x] exact Hellinger accelerated type
- [x] arbitrary-dimensional zero-type no-sewing theorem
- [x] Wold--Gamma type-zero classification
- [x] full prime-square plus Wold--Gamma compact-uniform type-zero bound
- [x] source-depth Gamma--Sonin exact type matching
- [x] scalar prime-square saturated-type classification
- [x] Julia/shell/Hellinger/Weyl modular-charge dictionary
- [x] finite-divisor accelerated-type noncreation theorem
- [x] standard adelic Iwahori condition-number saturation
- [x] hostile circularity audit
- [x] preliminary parent-literature collision audit
- [x] retract zero-acceleration adelic landing conjecture
- [ ] independent analytic-number-theory audit of `(6)`--`(9)`
- [ ] construct source-controlled higher Kummer/BV cubical homotopies
- [ ] form strict all-prime Euler--Gamma/Poisson totalization
- [ ] prove conservative multiplicity-faithful Xi Cartier base change
- [ ] dependency-closed RH proof
- [ ] unconditional Lean formalization

## Lean progress — §2, §3, §4 closed unconditionally

`GaloisForLFunctions.RHTower.AcceleratedWoldType` formalizes the accelerated scale, the exact
accelerated type of the reflected Hellinger sewing cost, and the universal no-sewing theorem.  All
statements are unconditional and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

```text
ell2 y = Real.log (1 + Real.log (1 + y))                                   -- (2)
ell2_mono, ell2_nonneg
tendsto_mul_ell2_zero_of_log_le                                            -- (4)
    a → 0⁺  and  log (1 + R_N) ≤ C · (a_N)⁻¹ ^ K   ⟹   a_N · ℓ₂ (R_N) → 0
mertensPrimeProductBelow_pos, tendsto_mertensPrimeProductBelow_zero
tendsto_logReflectedSewingBelow_atTop
tendsto_mertensProduct_mul_ell2_reflectedSewing                            -- (6)
    a_N · ℓ₂ (H_N(-c) / H_N(c))  →  2 e^(-γ) c        for every 0 < c < 1/2
le_opNorm_of_map_eq                                                        -- (12)
    R v = w,  v ≠ 0   ⟹   ‖w‖ / ‖v‖ ≤ ‖R‖
eventually_lt_mertensProduct_mul_ell2_of_ge                                -- (11), scalar form
le_of_tendsto_mul_ell2_of_ge                                               -- (11), limit form
eventually_lt_mertensProduct_mul_ell2_opNorm                               -- (10)–(11)
    R_N : E_N →L[ℝ] F_N,  R_N v_N = w_N,  ‖v_N‖ = H_N(c),  ‖w_N‖ = H_N(-c)
    ⟹  ∀ ε > 0, eventually  2 e^(-γ) c − ε  <  a_N · ℓ₂ ‖R_N‖
```

The spaces `E_N`, `F_N` are arbitrary normed spaces and may vary with the cutoff, which is the
"no dimension restriction" of §4.

The two analytic inputs were already owned by the tree: Mertens' third theorem
(`RHTower.MertensThirdTheorem.tendsto_mertensPrimeProduct_mul_log`) and the logarithmic growth rate
of the sewing cost (`RHTower.tendsto_log_logReflectedSewing_div_log`, giving
`tendsto_mertensProduct_mul_log_logReflectedSewing : a_N · log log (H_N(-c)/H_N(c)) → 2 e^(-γ) c`).
What was missing is the passage from `log ∘ log` to the scale `ℓ₂` that the card's definition `(3)`
uses — the two differ by a bounded amount once the cost exceeds `e`, and `a_N → 0` erases it — and
the two obstruction theorems built on it.

The corpus works with the squared Hellinger affinity throughout, which is the convention in which
the constant is exactly `2 e^(-γ) c`.

Remaining for stage 3: §5's three source scales, §6's four-chart modular charge dictionary, and
§7's finite-divisor noncreation theorem (its abstract half — invariance of accelerated type zero
under a fixed scalar multiple, finite sums and Cauchy majorants — is elementary; the operator-valued
Cauchy estimate is the analytic input).

### §7's abstract half

The stability statements the finite-divisor noncreation argument uses are also proved in the same
module:

```text
ell2_le_add                              ℓ₂ (x + y) ≤ ℓ₂ x + ℓ₂ y
tendsto_mul_ell2_zero_of_le_const_mul    R_N ≤ C · S_N and S has type zero ⟹ R has type zero
tendsto_mul_ell2_zero_of_le_add          R_N ≤ S_N + T_N, both type zero ⟹ R has type zero
```

`(24)` is exactly the first of these with `C = j! r^(-j)` and `S_N = sup_K ‖T_x‖`, and "fixed finite
linear combinations" is the second.

`(22)` ⇒ `(23)` is then closed outright:

```text
tendsto_mul_ell2_iteratedDeriv_zero
    T_N holomorphic on ball ρ r, continuous on its closure, ‖T_N z‖ ≤ M_N on the boundary circle,
    a_N · ℓ₂ (M_N) → 0    ⟹    a_N · ℓ₂ ‖iteratedDeriv j (T_N) ρ‖ → 0   for every fixed j
```

for operator families valued in an arbitrary complex Banach space — Cauchy's estimate
(`Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le`) followed by the fixed-multiple
stability.  Sections 2, 3, 4 and 7 of the card are therefore unconditional in Lean.

### §5's saturation law, in abstract form

```text
tendsto_mertensProduct_mul_ell2_of_tendsto
    log S_N → ∞  ⟹  ℓ₂ and log∘log have the same accelerated type
tendsto_mertensProduct_mul_ell2_of_log_linear
    log S_N / N → κ > 0   ⟹   a_N · ℓ₂ (S_N) → e^(-γ),  for every κ
```

The second is `(18)` and `(18k)` stripped to their mechanism: a family whose logarithm grows
linearly in the cutoff has the maximal boundary type `e^(-γ)` whatever the growth constant — which is
exactly the magnitude erasure the card attributes to scalarization.  Instantiating it needs only
`log B_x(c) = (|c| + o(1)) ϑ(x)` together with `ϑ(x) ∼ x`; the abstract law is unconditional.

Note the contrast with `tendsto_mul_ell2_zero_of_log_le`: logarithm growing like `a_N^(-K)` gives
type zero, logarithm growing like `N` gives type `e^(-γ)`.  Mertens' third theorem is what puts
these two on opposite sides — `a_N^(-1) ∼ e^(γ) log N` is exponentially smaller than `N`.

## Lean progress — §5.1 and §5.5 closed unconditionally

Both are axiom-clean (`[propext, Classical.choice, Quot.sound]`) and wired into
`GaloisForLFunctions.RHTower`.

### §5.1 — the reflected Wold–Gamma gauge has type zero

`RHTower/AcceleratedWoldType.lean`:

```text
one_add_exp_le                          1 + e^u ≤ 2 e^|u|
tendsto_mertensProduct_mul_ell2_expGauge
    a_N · ℓ₂ (exp (2t / a_N)) → 0        for every real t                       -- (13), (14)
```

The statement is symmetric in `t`, so the inverse gauge is the case `t ↦ −t`: the essential
singularity `exp(2 Re t / a_x)` already present in Gamma is an *ordinary* one relative to the Wold
boundary volume, and the accelerated scale does not see it.  This is exactly the shape
`tendsto_mul_ell2_zero_of_log_le` consumes, with `K = 1` and `C = log 2 + 2|t|`: the crude bound
`log(1 + e^u) ≤ log 2 + |u|` is all that the criterion needs.

### §5.5 — the restricted adelic Weyl joining is already saturated

Two new modules.  `RHTower/AdelicIntertwinerSaturation.lean` is the local algebra:

```text
intertwinerEigen p z = (p z² − 1) / (p − z²)                                    -- (18g)
normSq_intertwiner_num, normSq_intertwiner_den   the two squared norms in re/im coordinates
normSq_intertwiner_sub
    ‖p z² − 1‖² − ‖p − z²‖² = (p² − 1)(‖z‖⁴ − 1)
norm_intertwinerEigen_eq_one_iff
    ‖λ_p(z)‖ = 1  ⟺  ‖z‖ = 1                                                    -- (18l)
norm_intertwinerEigen_pos                         on the radial family the eigenvalue is nonzero
log_intertwiner_ratio_bound                       the plain-real comparison with the pure power ρ²
abs_log_norm_intertwinerEigen_sub_le
    ‖z‖² = p^(2c),  0 < c < 1/2,  p ≥ 2
      ⟹  |log ‖λ_p(z)‖ − 2c log p| ≤ 2 (1 − 2^(2c−1))^(−1) p^(2c−1)             -- (18h)
```

The equality locus is exact and needs no estimate: the identity
`|pz²−1|² − |p−z²|² = (p²−1)(|z|⁴−1)` decides it outright.  The estimate `(18h)` is *uniform in the
phase* `τ`: only `‖z‖² = p^{2c}` enters, never `Re z²`, because the four two-sided bounds
`(pρ ∓ 1)² ≤ A`, `(p ∓ ρ)² ≤ B` already absorb the phase, and `ρ = p^{2c} < p` is what keeps the
denominator away from zero.

`RHTower/AdelicIntertwinerType.lean` is the global half:

```text
finsum_prime_log_eq_sum_primesBelow      the PNT finsum in Finset form
tendsto_sum_primesBelow_log_div          (∑_{p < N} log p) / N → 1
tendsto_sum_log_norm_intertwinerEigen_div
    (∑_{p < N} log ‖λ_p(z_p)‖) / N → 2c                                         -- (18i)
tendsto_mertensProduct_mul_ell2_intertwinerProduct
    a_N · ℓ₂ (∏_{p < N} ‖λ_p(z_p)‖) → e^(−γ)
tendsto_mertensProduct_mul_ell2_sqrt_intertwinerProduct
    the same for the square root — the slope halves, the type does not
eventually_lt_mertensProduct_mul_ell2_intertwiner
    ∏_{p < N} ‖λ_p(z_p)‖ ≤ T_N²  ⟹  ∀ ε > 0 eventually  e^(−γ) − ε < a_N ℓ₂(T_N) -- (18j), (18k)
```

The defect sum is where `2c < 1` is used and where it is used only once: the local defects are
`O(p^{−(1−2c)})`, and `∑_{p<N} p^{2c−1} ≤ ∑_{r≤N} r^{−(1−2c)} ≤ 1 + N^{2c}/(2c)` is `o(N)` exactly
because the exponent is above `−1`.  The prime number theorem then converts the leading term
`2c ∑_{p<N} log p` into `2c N`, and `tendsto_mertensProduct_mul_ell2_of_log_linear` — which is
independent of the slope — returns the maximal type `e^(−γ)`.

`(18k)` is stated with the *square* on the right because `‖T‖‖T⁻¹‖ ≤ max(‖T‖,‖T⁻¹‖)²`; the square
root halves the slope and the saturation law does not notice, which is the card's "spherical
normalization merely transfers that height to the complementary Iwahori record".

**Remaining for stage 3:** §5.2's Wold-coordinate restatement `(16)`–`(17)` of the already-proved
`(6)`, §5.3's scalar prime-square compression `(18)` (which needs the corpus law
`log B_x(c) = (|c| + o(1)) ϑ(x)`), §5.4's Sonin depth matching `(18a)`–`(18e)`, and §6's four-chart
modular-charge dictionary.

## Lean progress — §5.2's Wold-coordinate form and §5.3 closed unconditionally

### §5.2 — `(17)` read backwards

`RHTower/AcceleratedWoldType.lean`:

```text
exp_exp_le_of_mul_ell2_ge
    κ ≤ a · ℓ₂ (R)   ⟹   exp (exp (κ / a) − 1) − 1 ≤ R
```

This is `(17)` stripped to its mechanism and in exact rather than asymptotic form: an accelerated
type at least `κ` forces the family to be an *exponential of an exponential* in `a_x^{-1}`.  Applied
to `κ = 2 e^(−γ)|c| − ε` and the sewing family of `(6)` it is the card's displayed lower bound; the
point the card makes — that this is not a Gamma-type factor, whose logarithm is only `O(1/a_x)` —
is exactly the contrast with `tendsto_mertensProduct_mul_ell2_expGauge` of §5.1.

### §5.3 — the scalar prime-square compression saturates

`RHTower/PrimeSquareScalarCompression.lean`, unconditional and axiom-clean:

```text
one_le_scalarCompressionRatio, scalarCompressionRatio_eq_one_iff
    the plain-real form of the local law, from  N² − D² = P(P−1)x(x−2)   with  x = r + r⁻¹
betaLocal p c = (p (p^c + p^(−c)) − (p − 1)) / √((p + p^(2c))(p + p^(−2c)))
one_le_betaLocal,  betaLocal_eq_one_iff
    β_p(c) ≥ 1, with equality exactly at c = 0                                       -- (8)
scalarCompA, scalarCompB, scalarComp_num_factor, scalarComp_den_factor
    N = p u (1 + A),  D² = p² (1 + B)   with  u = p^c
abs_log_scalarCompressionRatio_sub_log_le
    |log (N/D) − log u| ≤ 4 u⁻¹ + 3 u² / (2 p)
abs_log_betaLocal_sub_le
    |log β_p(c) − c log p| ≤ 4 p^(−c) + (3/2) p^(2c−1)                               -- (11)
tendsto_sum_log_betaLocal_div
    (∑_{p < N} log β_p(c)) / N → c                                                   -- (12), (13)
tendsto_mertensProduct_mul_ell2_betaProduct
    a_N · ℓ₂ (∏_{p < N} β_p(c)) → e^(−γ)                                             -- (18)
```

The identity `N² − D² = p(p−1)x(x−2)` does the whole of `(7)`–`(8)`: `x = r + r⁻¹ ≥ 2` with equality
only at `r = 1`, and `p^c = 1` only at `c = 0`.  For `(11)` the two relative defects have *different*
rates — `A = O(p^{−c})` from the numerator, `B = O(p^{2c−1})` from the denominator — and both are
summable against the primes below `N` to `o(N)`, the first because `c > 0` and the second because
`2c < 1`.  That is the only place the strip condition `0 < |c| < 1/2` is used.  The saturation law
then returns `e^(−γ)` for every drift, which is the card's "scalarization erases the magnitude".

**Remaining for stage 3:** §5.1's compact-uniform version `(14a)`–`(14c)` (needs normal convergence
of the genus-one occupation product), §5.4's Sonin depth matching `(18a)`–`(18e)`, and §6's
four-chart modular-charge dictionary.

## Lean progress — §5.4's depth matching and §6's dictionary

### §5.4 — the Sonin aperture depth is fixed by the Wold first trace

`RHTower/SoninDepthMatching.lean`, unconditional and axiom-clean:

```text
soninDepth a r = ⌊2 / (a log r)⌋                                                  -- (18a)
soninDepth_bounds        0 ≤ 2/a − N_x log r < log r                             -- (18b)
soninDepth_rpow_bounds
    r^(−d) exp(2d/a) ≤ r^(N_x d) ≤ exp(2d/a)                                     -- (18d)
norm_le_of_soninDepth_rigidity
    C₁ r^(N_x d) ≤ ‖k‖ ≤ C₂ r^(N_x d)
      ⟹ C₁ r^(−d) exp(2d/a) ≤ ‖k‖ ≤ C₂ exp(2d/a)                                -- (18e)
```

The whole of `(18d)` is the floor estimate `(18b)` exponentiated: because the residual is less than
one step, the geometric escape and the reflected Wold–Gamma gauge differ by the *fixed* factor
`r^(−d)`, uniformly in the cutoff.  `(18c)` — Burnol–Sonin aperture-type rigidity — enters only as
the two-sided hypothesis of `norm_le_of_soninDepth_rigidity`, which is where the card's own
citation sits.

### §6 — the four charts

`RHTower/AdelicIntertwinerType.lean`:

```text
tendsto_sum_log_norm_intertwinerEigen_div_theta
    (∑_{p < N} log ‖λ_p(z_p)‖) / ϑ(N) → 2c                                        -- (21a)
modularCharge_dictionary
    r_shell = (2 Re ρ − 1) log 2,   ReRes = m_ρ c_ρ,
    a_Hel = 2 e^(−γ) c_ρ,           r_Weyl = 2 c_ρ,     β_ρ = 2 Re ρ
      ⟹  a_Hel = −(e^(−γ)/log 2) r_shell = (2 e^(−γ)/m_ρ) ReRes,
          r_Weyl = −r_shell/log 2 = (2/m_ρ) ReRes = e^γ a_Hel = 1 − β_ρ           -- (21), (21b), (21c)
```

`(21a)` is `(18i)` renormalized by `ϑ` rather than by the cutoff, which is legitimate because
`ϑ(N)/N → 1` and the limit is nonzero.  The dictionary itself is exactly the statement that the four
coordinates determine one another; the two inputs it takes as given — the positive-shell rate `(19)`
and the Xi Julia residue `(20)` — are the parent cards' theorems, and the two it now proves outright
are `(6)` (`tendsto_mertensProduct_mul_ell2_reflectedSewing`) and `(18i)`.  The final line
`r_Weyl = 1 − β_ρ` is the card's "the Weyl map pays exactly the modular retuning cost".

**Remaining for stage 3:** §5.1's compact-uniform version `(14a)`–`(14c)`, which needs normal
convergence of the genus-one occupation product; and the two dictionary inputs `(19)`, `(20)` in
Lean, which belong to the positive-shell and Xi-Julia parents.

## Lean progress — §5.1's compact-uniform form

`RHTower/AcceleratedWoldType.lean`:

```text
log_max_gauge_le
    1 ≤ C,  C⁻¹ ≤ |φ| ≤ C,  |t| ≤ M
      ⟹ log (max (max |φ| e^(2t/a)) (max |φ|⁻¹ e^(−2t/a))) ≤ log C + 2M/a        -- (14c)
tendsto_mertensProduct_mul_ell2_zero_of_log_gauge_le
    log (1 + R_N) ≤ log C + 2M / a_N   ⟹   a_N · ℓ₂ (R_N) → 0                    -- (14)
```

`(14b)`'s unitary factor contributes nothing to either norm, so the comparison's two norms are the
two entrywise maxima above; `(14a)`'s two-sided bound on the regularized occupation determinant
enters exactly as the hypothesis `C⁻¹ ≤ |φ| ≤ C`, which is where the card's citation of normal
convergence of the genus-one product sits.  With those two, `(14c)` is the elementary bound
`max(C, e^{2M/a}) ≤ C e^{2M/a}`, and the second theorem turns it into accelerated type zero — the
same criterion `(14)` uses pointwise.

**Sections 2, 3, 4, 5.1, 5.2, 5.3, 5.4, 5.5, 6 and 7 of this card are now Lean-proved**, each
unconditional and axiom-clean.  What the card still takes from its parents, and does not claim
itself, is `(14a)` (normal convergence of the genus-one occupation product), `(18c)`
(Burnol–Sonin aperture rigidity), `(19)` (the positive-shell reflection rate) and `(20)` (the Xi
Julia current residue); each enters as an explicit hypothesis of the theorem that consumes it.

## Lean progress — `(19)` and `(20)` are the tree's own theorems, and §6 is now unconditional

The two inputs the dictionary was taking as hypotheses are already owned:

```text
HighExponentShellLeastAtomAsymptotic.log_norm_shellTransferCharacter
    log ‖2^(1/2 − s)‖ = (1/2 − Re s) log 2
XiHypertranscendentalModularResidueTransgression.re_centeredXiAffineResidue_eq_shellTransferEntropy
    Re (−(ρ − 1/2) n) = n · (1/2 − Re ρ)
```

so `RHTower/ModularChargeFourCharts.lean` closes both and the dictionary with them:

```text
shellReflectionRate_eq
    log ‖χ(1 − ρ̄)‖ − log ‖χ(ρ)‖ = (2 Re ρ − 1) log 2                              -- (19)
modularCharge_dictionary_xi
modularCharge_dictionary_xi_residue
    a_Hel = −(e^(−γ)/log 2) r_shell = (2 e^(−γ)/n) Re Res_ρ,
    r_Weyl = −r_shell/log 2 = (2/n) Re Res_ρ = e^γ a_Hel = 1 − β_ρ                -- (21), (21b), (21c)
```

`(19)` is the difference of the shell character's logarithmic moduli at `ρ` and at its
functional-equation reflection — the corpus's `log ‖χ(s)‖ = (1/2 − Re s) log 2` evaluated twice —
and `(20)` is the corpus's centered affine Xi residue at a divisor point of multiplicity `n`.  With
those, every chart of §6 is a theorem of this tree.

**Everything this card proves is now Lean-proved, unconditional and axiom-clean**, except the two
literature/parent analytic inputs that appear as explicit hypotheses where they are used:
`(14a)` (normal convergence of the genus-one occupation product, in `log_max_gauge_le`) and `(18c)`
(Burnol–Sonin aperture rigidity, in `norm_le_of_soninDepth_rigidity`).

## Lean progress — `(14b)`–`(14c)` for the tree's own occupation phase

`RHTower/WoldGaugeCompactUniform.lean`:

```text
norm_finitePrimeGenusOnePolarizedPhase
    ‖Φ^(1)_S(t)‖ = exp (2 Re t / ε_S) · ‖Φ^(0)_S(t)‖
norm_finitePrimeGenusOnePolarizedPhase_neg
    ‖Φ^(1)_S(−t)‖ = ‖Φ^(1)_S(t)‖⁻¹
log_max_blockComparison_le
    C⁻¹ ≤ ‖Φ^(1)_S(t)‖ ≤ C,  |Re t| ≤ M
      ⟹ log (max (max ‖Φ^(1)_S(t)‖ e^(2 Re t/ε_S)) (max ‖Φ^(1)_S(t)‖⁻¹ e^(−2 Re t/ε_S)))
            ≤ log C + 2M / ε_S                                                    -- (14b), (14c)
```

`(14b)` is a unitary factor tensored with the diagonal pair `(Φ^reg, exp(2t/a_x))`; the unitary
contributes nothing to either norm, so the comparison's two norms are the two entrywise maxima
above, and `(14c)` is the elementary bound `max(C, e^{2M/a}) ≤ C e^{2M/a}`.  The regularized entry
`Φ^reg` is the *tangent-normalized* phase `Φ^(1)` — the one whose product converges — and the first
identity records exactly how it differs from the raw genus-zero phase: by the irregular gauge
`exp(2 Re t/ε_S)`, whose exponent blows up as `ε_S → 0`.  The only remaining input is `(14a)`, the
two-sided compact bound on `Φ^(1)` itself, which is the parent's normal convergence of the
genus-one product and appears here as the hypothesis `C⁻¹ ≤ ‖Φ^(1)_S(t)‖ ≤ C`.
