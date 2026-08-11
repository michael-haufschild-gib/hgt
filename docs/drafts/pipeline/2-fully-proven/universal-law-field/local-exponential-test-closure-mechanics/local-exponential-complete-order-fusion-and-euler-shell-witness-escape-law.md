# Local-exponential complete-order fusion and Euler-shell witness-escape law

- **ID:** ULF-LETCM-2
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / SOURCE-GENERATED COFINAL FUSION
- **Statement:** A finite local exponential window makes polynomial/Hankel and rational-phase
  tests independently reconstruct every bounded Hermitian source density and its matrix order;
  on the Euler-shell log source every negative atom is detected at finite depth, but the required
  depth has no uniform bound and the complete positive chart stops at the normalization wall.
- **Status:** `[PROVED HERE] [DEPENDENCY-CLOSED] [UNCONDITIONAL] [MATRIX-VALUED]`
  `[THREE-ORGAN FUSION] [FOURTH-ORGAN WITNESS-ESCAPE] [LITERAL ARITHMETIC SOURCE]`
  `[CLASSICAL PARENTS] [NOVELTY UNVERIFIED] [LEAN PENDING] [NOT RH]`

## 1. The mechanism

This theorem is not another route receiver.  It proves that one source-generated clock calculus
can be simultaneously complete for values, matrix order, phase history, and moment/Hankel
response on an infinite arithmetic source.

The load-bearing condition is local rather than entire exponential execution:

\[
  \exists a>0:\qquad \int_{\mathbb R}e^{a|x|}\,d\mu(x)<\infty.
  \tag{LEF.1}
\]

For sources supported in a half-line `[b,infinity)`, it is enough to assume

\[
  \int e^{ax}\,d\mu(x)<\infty
  \tag{LEF.2}
\]

for one `a>0`.  The difference matters for the Euler-shell source, whose positive exponential
chart has finite width and can never have entire bilateral moments.

## 2. Local-Laplace polynomial closure

### Theorem 2.1 — scalar polynomial density

Let `mu` be a finite positive Borel measure on `R` satisfying `(LEF.1)`.  Then real polynomials are
dense in `L^2(mu;R)` and complex polynomials are dense in `L^2(mu;C)`.

The same conclusion holds under `(LEF.2)` when `supp(mu) subset [b,infinity)`.

### Proof

It is enough to prove that the orthogonal complement of the polynomials is zero.  Let
`f in L^2(mu;C)` be orthogonal to every monomial.  Under `(LEF.1)`, Cauchy--Schwarz gives

\[
 \int e^{a|x|/2}|f(x)|\,d\mu(x)
 \le \|f\|_2\left(\int e^{a|x|}\,d\mu(x)\right)^{1/2}<\infty.
 \tag{LEF.3}
\]

Hence

\[
 F(z)=\int e^{zx}f(x)\,d\mu(x)
 \tag{LEF.4}
\]

is holomorphic on the strip `|Re z|<a/2`.  Differentiation under the integral is legitimate on
every smaller closed strip, and

\[
 F^{(n)}(0)=\int x^nf(x)\,d\mu(x)=0
 \tag{LEF.5}
\]

for every `n`.  Thus the Taylor germ of `F` at zero vanishes.  The identity theorem makes `F`
zero on the connected strip.  In particular, the Fourier transform of the finite complex measure
`f mu` vanishes on the whole imaginary axis.  Fourier uniqueness gives `f mu=0`, hence `f=0`
almost everywhere.

If `mu` is supported in `[b,infinity)` and satisfies `(LEF.2)`, translate the support to
`[0,infinity)`.  The same estimate makes `(LEF.4)` holomorphic on the half-plane `Re z<a/2`, which
again contains zero and the whole imaginary axis.  The proof is unchanged.  Taking real and
imaginary parts gives the real statement.  QED.

### Hostile scope

Absolute continuity with respect to Lebesgue measure is not used.  The result applies to pure
point measures.  A local exponential moment is sufficient, not necessary; the theorem makes no
classification outside this chamber.

## 3. Matrix-valued complete order reflection

Fix `d>=1`.  Let

\[
 J:\mathbb R\longrightarrow\operatorname{Herm}_d(\mathbb C)
 \tag{LEF.6}
\]

be weakly measurable and essentially bounded in operator norm.  Define

\[
 M_n(J)=\int x^nJ(x)\,d\mu(x)
 \tag{LEF.7}
\]

and the order-`N` block Hankel section

\[
 \mathcal H_N(J)=[M_{i+j}(J)]_{0\le i,j<N}.
 \tag{LEF.8}
\]

For a vector polynomial `p(x)=sum_(j=0)^(N-1)x^jv_j`, direct expansion gives

\[
 v^*\mathcal H_N(J)v
 =\int p(x)^*J(x)p(x)\,d\mu(x).
 \tag{LEF.9}
\]

### Theorem 3.1 — complete block-Hankel sign cone

Under Theorem 2.1's hypotheses, the following are equivalent:

\[
 \boxed{
 J(x)\succeq0\quad\mu\text{-a.e.}
 \quad\Longleftrightarrow\quad
 \mathcal H_N(J)\succeq0\quad\text{for every }N.}
 \tag{LEF.10}
\]

### Proof

The forward implication follows from `(LEF.9)`.

Conversely, positivity of every block Hankel section makes the multiplier quadratic form

\[
 \mathfrak q_J(f)=\int f(x)^*J(x)f(x)\,d\mu(x)
 \tag{LEF.11}
\]

nonnegative on every vector polynomial.  Scalar polynomial density in each coordinate makes
vector polynomials dense in `L^2(mu;C^d)`.  Essential boundedness of `J` makes `(LEF.11)`
continuous, so it is nonnegative on all of `L^2(mu;C^d)`.

Let `D` be a countable dense subset of `C^d`.  For `u in D` and every measurable `E`, test
`f=1_Eu`.  Then

\[
 \int_Eu^*J(x)u\,d\mu(x)\ge0.
 \tag{LEF.12}
\]

The standard set-integral sign criterion gives `u^*J(x)u>=0` almost everywhere.  Intersect the
resulting full-measure sets over countable `D`.  At every point in the intersection, continuity
of the quadratic form in `u` extends the inequality from `D` to all `C^d`.  Therefore `J(x)` is
positive semidefinite almost everywhere.  QED.

### Corollary 3.2 — finite negative witness

If `J` fails to be positive semidefinite on a set of positive measure, then some finite block
Hankel section has a strict negative vector:

\[
 \boxed{
 J\not\succeq0\text{ a.e.}
 \Longrightarrow
 \exists N,v:\ v^*\mathcal H_N(J)v<0.}
 \tag{LEF.13}
\]

This is the contrapositive of `(LEF.10)`, with strict negativity because a Hermitian matrix is not
positive semidefinite exactly when one quadratic value is negative.

## 4. Rational-phase closure

Let `P_Q` be the vector space of finite vector-valued phase packets

\[
 p(x)=\sum_{k=1}^re^{-iq_kx}v_k,
 \qquad q_k\in\mathbb Q,
 \quad v_k\in\mathbb C^d.
 \tag{LEF.14}
\]

### Lemma 4.1 — rational phases are dense

For every finite positive Borel measure `mu`, `P_Q` is dense in `L^2(mu;C^d)`.

### Proof

If a scalar `f in L^2(mu)` is orthogonal to all rational phases, the Fourier transform of the
finite measure `f mu` vanishes on `Q`.  It is continuous, hence vanishes on `R`; Fourier uniqueness
gives `f=0`.  Apply this coordinatewise.  QED.

### Theorem 4.2 — phase/Hankel/source fusion

Under Theorem 2.1's hypotheses, the following are equivalent:

\[
 \boxed{
 \begin{aligned}
 &J(x)\succeq0\quad\mu\text{-a.e.};\\
 &\mathcal H_N(J)\succeq0\quad\text{for every }N;\\
 &\int p(x)^*J(x)p(x)\,d\mu(x)\ge0
   \quad\text{for every }p\in\mathcal P_{\mathbb Q}.
 \end{aligned}}
 \tag{LEF.15}
\]

The phase implication follows by the same bounded-multiplier extension used in Theorem 3.1 and
Lemma 4.1.  Thus polynomial/Hankel and phase/Fourier tests independently close to the same matrix
order.

## 5. Exact compensation-gauge conservation

Let `W,H` be essentially bounded Hermitian matrix fields, with `W(x)>=0` almost everywhere, and
put

\[
 J_c(x)=cW(x)-H(x).
 \tag{LEF.16}
\]

Define the source, Hankel, and phase feasible sets

\[
\begin{aligned}
 \mathcal C_{\rm src}&=\{c\ge0:J_c\succeq0\text{ a.e.}\},\\
 \mathcal C_{\rm H}&=\{c\ge0:\mathcal H_N(J_c)\succeq0\ \forall N\},\\
 \mathcal C_{\rm F}&=\{c\ge0:Q_{J_c}(p)\ge0\ \forall p\in\mathcal P_{\mathbb Q}\}.
\end{aligned}
 \tag{LEF.17}
\]

### Theorem 5.1 — conservation

\[
 \boxed{
 \mathcal C_{\rm src}=\mathcal C_{\rm H}=\mathcal C_{\rm F}.}
 \tag{LEF.18}
\]

Consequently their extended sharp gauges agree:

\[
 \boxed{
 \kappa_{\rm src}=\kappa_{\rm H}=\kappa_{\rm F}\in[0,\infty].}
 \tag{LEF.19}
\]

### Proof

Apply Theorem 4.2 separately to `J_c` for every `c>=0`.  The feasible sets themselves agree, so
their infima agree, including the empty-set value `+infinity`.  QED.

This is not a limiting equality inferred from approximate matrices.  It is exact conservation of
the whole compensation law under two source-generated cofinal test closures.

## 6. Literal Euler-shell arithmetic realization

Fix the marked high-exponent shell coefficient `a_m(n)` and `sigma>1`.  Let

\[
 \mu_{m,\sigma}
 =\frac1{S_m(\sigma)}\sum_{n\ge2}a_m(n)n^{-\sigma}\delta_{\log n}.
 \tag{LEF.20}
\]

The measure is finite and supported in `[log 2,infinity)`.  For every `0<a<sigma-1`,

\[
 \int e^{ax}\,d\mu_{m,\sigma}(x)
 =\frac{S_m(\sigma-a)}{S_m(\sigma)}<\infty.
 \tag{LEF.21}
\]

Theorem 4.2 therefore gives the following unconditional source theorem.

### Theorem 6.1 — Euler-shell complete test closure

For every bounded Hermitian packet `J_n` on the active shell,

\[
 \boxed{
 \begin{aligned}
 &J_n\succeq0\quad\text{for every }n\text{ with }a_m(n)=1;\\
 &\left[\sum_na_m(n)n^{-\sigma}(\log n)^{i+j}J_n\right]_{0\le i,j<N}
   \succeq0\quad\text{for every }N;\\
 &\sum_na_m(n)n^{-\sigma}p(\log n)^*J_np(\log n)\ge0
   \quad\text{for every finite rational phase packet }p
 \end{aligned}}
 \tag{LEF.22}
\]

are equivalent.  Normalization by the positive scalar `S_m(sigma)` does not affect positivity.

The clock powers `(log n)^k` are derivatives of the source Mellin flow; the phases `n^{-it}` are
its imaginary-time characters.  Thus both test calculi are generated by the same pre-zero source,
not imported from target routes.

## 7. Fourth-organ theorem: finite detection with escaping depth

The complete tower detects every negative active atom, but no test depth depending only on the
source can do so.

### Theorem 7.1 — no uniform finite depth

For every `N>=1`, there is a bounded scalar packet `J^(N)` on the Euler shell such that

1. `J^(N)` is negative at one active atom;
2. every block Hankel section of order at most `N` is positive definite.

### Proof

Let `H_N(1)` be the order-`N` scalar Hankel matrix of the positive source.  It is positive
definite because the active shell has at least `N` distinct clock values: a nonzero polynomial of
degree less than `N` cannot vanish on all of them.  Let `lambda_N>0` be its smallest eigenvalue.

Choose active atoms `x_r=log n_r -> infinity`.  Their masses satisfy

\[
 w_r\sum_{j=0}^{N-1}x_r^{2j}\longrightarrow0,
 \tag{LEF.23}
\]

because `w_r` is a constant multiple of `n_r^{-sigma}` and every power of `log n_r` is
`o(n_r^epsilon)`.  Fix `M>1` and choose `r` so large that

\[
 M w_r\sum_{j=0}^{N-1}x_r^{2j}<\lambda_N.
 \tag{LEF.24}
\]

Set `J^(N)=1-M` at `x_r` and `J^(N)=1` elsewhere.  It is negative at `x_r`.  Its order-`N`
Hankel matrix is

\[
 H_N(J^{(N)})=H_N(1)-Mw_rv_rv_r^*,
 \qquad v_r=(1,x_r,\ldots,x_r^{N-1})^T.
 \tag{LEF.25}
\]

The perturbation norm is `Mw_r||v_r||^2<lambda_N`, so `(LEF.25)` remains positive definite.  Every
smaller section is a principal submatrix and is positive definite.  QED.

### Consequence

The negative witness promised by `(LEF.13)` must appear later than `N`.  Therefore complete order
reflection is genuinely cofinal: the detecting degree may migrate to infinity even though every
negative atom is eventually detected.

This is a theorem in the cofinal spectral/admission organ derived from source, phase, and Hankel
fusion.  It was not assumed in the construction of those tests.

## 8. Normalization-wall law

The source has positive exponential execution only while `sigma+t>1`.  Its exact negative-time
lifetime is `sigma-1`.  The physical half-density matching condition in the high-exponent shell is
`sigma=1/m<=1`, outside the normalized positive chart.

Hence:

\[
 \boxed{
 \text{complete phase/Hankel order on every safe fibre}
 \not\Longrightarrow
 \text{positive continuation across the normalization wall}.}
 \tag{LEF.26}
\]

This is the sharp failure of the stronger conjecture.  Local test completeness is real arithmetic
leverage, but it does not manufacture a positive critical fibre.

## 9. RH selection consequence

Only after Theorems 4.2--7.1 is the next selection statement well typed:

> Construct a source-canonical continuation of the Euler-shell matrix intervention through the
> normalization wall which preserves the complete feasible set `(LEF.18)`, and prove that every
> strict-right divisor would create one negative active matrix atom.

If such a continuation exists, `(LEF.13)` forces a finite negative Hankel/phase witness, while
complete positivity of the continued source forbids it.  Reflection would then give RH.

The continuation theorem is not proved here.  Ordinary meromorphic continuation of `S_m` is not
enough: it must preserve the matrix order represented by the full test closure.  This separates a
genuine selector from analytic relabeling.

## 10. Hostile conjecture loops

### Loop A — entire moments are load-bearing

**Falsified.**  A single local exponential window proves density and complete order reflection.
The positive survivor is Theorems 2.1--5.1.

### Loop B — scalar tests imply matrix order without amplification

**Falsified in general.**  Positive maps on noncommutative sources need not be completely positive.
The theorem retains vector-polynomial and vector-phase packets at every fixed matrix channel.

### Loop C — finite test depth is enough on the Euler source

**Falsified by Theorem 7.1.**  Negative atoms can be placed far enough into the exponentially
small tail to evade any prescribed finite Hankel depth.  Eventual finite detection is the sharp
survivor.

### Loop D — complete order reflection implies straight admission

**Falsified.**  The centered Euler score is unbounded below, so its straight positive radius is
zero, while its nonlinear exponential flow exists throughout a nontrivial real interval.  Test
closure and execution domain are independent field coordinates.

### Loop E — safe-fibre completeness crosses the critical fibre

**Falsified by `(LEF.26)`.**  The normalization wall occurs before half-density.  The survivor is
the exact type of required continuation: it must preserve complete order, not only coefficients.

### Loop F — phase and Hankel closure are merely two formulas

**Falsified.**  They require different completeness mechanisms: Fourier uniqueness for rational
phases and local-Laplace quasi-analyticity for polynomials.  Their exact feasible-set equality is a
nontrivial fusion through the source matrix cone.

## 11. Literature and priority boundary

- Labouriau, *The Laplace transform and polynomial approximation in L2*,
  <https://arxiv.org/abs/1603.03473>, proves a scalar exponential-tail density theorem.
- Bolotnikov, *On degenerate Hamburger moment problem and extensions of positive semidefinite
  Hankel block matrices*, <https://arxiv.org/abs/0812.4567>, is a parent for block-Hankel moment
  geometry.
- Berg--Szwarc, *Self-adjoint operators associated with Hankel moment matrices*,
  <https://arxiv.org/abs/2105.07252>, and Yafaev,
  <https://arxiv.org/abs/1601.08042>, occupy Hankel-form closure theory.
- The corpus's `CompleteHankelSignCone.lean` proves the scalar entire-moment chamber;
  `FourierKernelAdmission.lean` supplies the phase-kernel parent.

Polynomial density, Fourier uniqueness, bounded multipliers, and matrix moment problems are
classical parents.  No priority claim is made for those pieces.  The exact local-exponential
matrix sign-cone + rational-phase + compensation-gauge + Euler-shell witness-escape synthesis was
not located in the internal corpus or broad arXiv search.  Mark it `[NOVELTY UNVERIFIED]`, not a
priority theorem.

## 12. Formalization boundary

No Lean was written or built during this paper research loop.  The dependency-closed future Lean
target belongs only in

`formal/GaloisForLFunctions/HTGeometry/LocalExponentialTestClosure.lean`

after the Stage-2 audit.  Required formal components are:

1. local-exponential polynomial density for arbitrary finite Borel measures;
2. bounded Hermitian multiplier sign-cone equivalence;
3. rational-phase density and fusion;
4. feasible-set conservation;
5. abstract finite-witness implication;
6. Euler-shell specialization only after the universal core is certified.

## 13. Promotion gate

- [x] local exponential density proof closed;
- [x] matrix-valued sign-cone proof closed;
- [x] rational-phase fusion and exact gauge conservation closed;
- [x] literal Euler-shell source specialization closed;
- [x] fourth-organ finite-witness/no-uniform-depth theorem closed;
- [x] normalization wall and RH boundary stated without circularity;
- [x] hostile internal collision audit completed;
- [x] broad arXiv parent search completed;
- [ ] independent hostile reread;
- [ ] Lean formalization and Stage-3 promotion.

## Log

- 2026-08-11 — conjecture frozen, scalar and matrix proofs closed, and literal Euler-shell
  specialization derived.
- 2026-08-11 — finite-depth completeness falsified by a far-tail rank-one perturbation; eventual
  finite detection retained as sharp positive survivor.

