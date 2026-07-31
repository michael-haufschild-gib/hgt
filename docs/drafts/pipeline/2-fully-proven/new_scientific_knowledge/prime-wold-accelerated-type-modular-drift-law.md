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
