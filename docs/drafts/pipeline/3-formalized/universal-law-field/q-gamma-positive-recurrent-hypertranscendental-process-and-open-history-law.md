# q-Gamma positive recurrent hypertranscendental process and open-history law

- **ID:** ULF-QGPRH-1
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / INFINITE CROSS-DOCTRINE PROCESS
- **Source:** infinite common-process gate for Constitutive Process Mathematics
- **Statement:** Jackson's \(q\)-Gamma function is one explicit process with positive atomic, GNS/operator, recurrent-history, entropy-tilt, and hypertranscendental differential realizations.
- **Status:** [PAPER-PROVED] [ONE SOURCE PROCESS] [POSITIVE] [PURE-POINT RECURRENT] [OPEN LIFT] [HYPERTRANSCENDENTAL] [WITHHELD TILT RESPONSE] [CLASSICAL INGREDIENTS] [NOT RH] [LEAN CERTIFIED]

## 1. q-Gamma probability law

Fix \(0<q<1\). Write

\[
(q;q)_0=1,
\qquad
(q;q)_n=\prod_{k=1}^n(1-q^k),
\qquad
(q;q)_\infty=\prod_{k=1}^\infty(1-q^k).
\tag{1}
\]

Define

\[
w_n=(q;q)_\infty\frac{q^n}{(q;q)_n},
\qquad
x_n=n\log q-\log(1-q)
\qquad(n\ge0).
\tag{2}
\]

### Theorem 1.1

The numbers \(w_n\) are strictly positive and sum to one. For \(\operatorname{Re}s>-1\),

\[
\boxed{
F_q(s):=\Gamma_q(1+s)=\sum_{n=0}^\infty w_ne^{s x_n}.}
\tag{3}
\]

Thus \(F_q\) is the moment-generating/Mellin response of the discrete probability law

\[
\mu_q=\sum_{n=0}^\infty w_n\delta_{x_n}.
\tag{4}
\]

### Proof

Jackson's \(q\)-Gamma function is

\[
\Gamma_q(z)
=(1-q)^{1-z}\frac{(q;q)_\infty}{(q^z;q)_\infty}.
\tag{5}
\]

The \(q\)-binomial theorem gives

\[
\frac1{(a;q)_\infty}
=\sum_{n=0}^\infty\frac{a^n}{(q;q)_n}
\qquad(|a|<1).
\tag{6}
\]

Put \(a=q^{1+s}\). Then

\[
\begin{aligned}
\Gamma_q(1+s)
&=(1-q)^{-s}(q;q)_\infty
  \sum_{n\ge0}\frac{q^{n(1+s)}}{(q;q)_n}\\
&=\sum_{n\ge0}
  \left((q;q)_\infty\frac{q^n}{(q;q)_n}\right)
  \exp\!\left(s[n\log q-\log(1-q)]\right).
\end{aligned}
\]

At \(s=0\), \(\Gamma_q(1)=1\), so the positive coefficients sum to one. QED.

Since \((q;q)_n\ge(q;q)_\infty\), one has \(0<w_n\le q^n\). Because \(x_n\) grows
linearly, every polynomial moment of \(\mu_q\) is finite.

## 2. Positive kernel and GNS realization

Put

\[
C_q(t)=F_q(it)=\Gamma_q(1+it).
\tag{7}
\]

### Theorem 2.1

The translation kernel

\[
K_q(s,t)=C_q(t-s)
\tag{8}
\]

is positive definite. More precisely, let

\[
\mathcal H_q=\ell^2(\mathbb N_0,w),
\qquad
\langle \xi,\eta\rangle
=\sum_{n\ge0}w_n\overline{\xi_n}\eta_n,
\qquad
\Omega=(1,1,\ldots).
\tag{9}
\]

Let \(X\) be multiplication by \(x_n\) on its maximal domain and put \(U_t=e^{itX}\). Then

\[
\boxed{
C_q(t)=\langle\Omega,U_t\Omega\rangle.}
\tag{10}
\]

The operator \(X\) is self-adjoint with compact resolvent, and
\(\Omega\in\operatorname{Dom}X^k\) for every \(k\ge0\).

### Proof

For finite \(c_j\in\mathbb C\) and \(t_j\in\mathbb R\),

\[
\sum_{i,j}\overline{c_i}c_jC_q(t_j-t_i)
=\sum_{n\ge0}w_n
  \left|\sum_jc_je^{it_jx_n}\right|^2
\ge0.
\tag{11}
\]

Equation (10) is (3) at \(s=it\). Under the unitary identification
\(\ell^2(w)\to\ell^2\), \(\xi_n\mapsto\sqrt{w_n}\xi_n\), \(X\) is the real diagonal
operator with distinct eigenvalues \(x_n\), and \(|x_n|\to\infty\). Hence its resolvent is compact.
The geometric bound \(w_n\le q^n\) gives
\(\sum_nw_n|x_n|^{2k}<\infty\), proving the domain assertion. QED.

Every finite moment matrix

\[
M_N=\bigl(F_q^{(i+j)}(0)\bigr)_{0\le i,j\le N}
=\left(\int x^{i+j}\,d\mu_q(x)\right)_{i,j}
\tag{12}
\]

is positive definite. Indeed,

\[
c^*M_Nc=\int\left|\sum_{j=0}^Nc_jx^j\right|^2d\mu_q(x)>0
\tag{13}
\]

for \(c\ne0\), because a nonzero polynomial cannot vanish on the infinite distinct support
\(\{x_n:n\ge0\}\).

## 3. Recurrent observation and open marked history

The phase coordinates factor as

\[
e^{itx_n}
=e^{-it\log(1-q)}\bigl(e^{it\log q}\bigr)^n.
\tag{14}
\]

### Theorem 3.1

The orbit \(\{U_t\Omega:t\in\mathbb R\}\) has compact norm closure. There are unbounded
\(t_j\to+\infty\) such that

\[
\boxed{\|U_{t_j}\Omega-\Omega\|_{\mathcal H_q}\longrightarrow0.}
\tag{15}
\]

Yet the marked logarithmic lift

\[
h(t)=tX\Omega=(t x_n)_{n\ge0}
\tag{16}
\]

satisfies

\[
\boxed{
\|h(t_j)\|
=t_j\left(\sum_{n\ge0}w_nx_n^2\right)^{1/2}
\longrightarrow\infty.}
\tag{17}
\]

### Proof

Define

\[
\Phi:\mathbb T^2\longrightarrow\mathcal H_q,
\qquad
\Phi(\alpha,\beta)_n=e^{i\alpha}e^{in\beta}.
\tag{18}
\]

Finite-coordinate continuity plus the uniform tail bound
\(\sum_{n>N}w_n\to0\) makes \(\Phi\) norm-continuous. Equation (14) places the orbit in the compact
set \(\Phi(\mathbb T^2)\). Compact-group recurrence, equivalently simultaneous Dirichlet
approximation of

\[
\frac{-\log(1-q)}{2\pi},
\qquad
\frac{\log q}{2\pi},
\]

gives unbounded return times satisfying (15). Equation (17) is immediate from (16). Its coefficient
is finite by the moment bound and nonzero because the support is not concentrated at \(0\). QED.

Thus one process has a closed recurrent observer shadow and an open lifted history. The latter is
not inferred from recurrence alone; it is retained by the marked logarithmic spectral
realization.

## 4. Hypertranscendental analytic memory

### Theorem 4.1

The response \(F_q(s)=\Gamma_q(1+s)\) is hypertranscendental over \(\mathbb C(s)\). Consequently,

\[
\boxed{
\operatorname{trdeg}_{\mathbb C(s)}
\mathbb C(s)\bigl(F_q,F_q',\ldots,F_q^{(N)}\bigr)=N+1
\quad(N\ge0).}
\tag{19}
\]

### Proof

P. I. Pastro's \(q\)-analogue of Hölder's theorem proves that \(\Gamma_q(z)\) satisfies no
algebraic differential equation even over the larger differential field
\(\mathbb C(z,q^z)\). In particular it is hypertranscendental over \(\mathbb C(z)\).
The affine substitution \(z=1+s\) preserves differential algebraicity and its negation, proving
the first assertion. Equation (19) is the finite-jet characterization of hypertranscendence. QED.

Combining (12), (13), and (19), the same response has both maximal positive Hankel rank and maximal
algebraic intervention rank. Positivity does not create the HT statement; Pastro's theorem does.
Their coexistence is nevertheless intrinsic to the same \(\mu_q\)-process.

## 5. Exact intervention tilt and entropy law

Jackson's functional equation is

\[
\Gamma_q(z+1)=\frac{1-q^z}{1-q}\Gamma_q(z).
\tag{20}
\]

Since \(F_q(1)=\Gamma_q(2)=1\), the exponentially tilted weights

\[
\widetilde w_n=e^{x_n}w_n
\tag{21}
\]

again form a probability law. Their characteristic response is

\[
\widetilde C_q(t)
=\sum_n\widetilde w_ne^{itx_n}
=F_q(1+it).
\tag{22}
\]

### Theorem 5.1

The response to this unmeasured tilt is forced by the original response:

\[
\boxed{
\widetilde C_q(t)
=\frac{1-q^{1+it}}{1-q}\,C_q(t).}
\tag{23}
\]

Moreover \(X\) is the log-likelihood ratio:

\[
\log\frac{\widetilde w_n}{w_n}=x_n,
\tag{24}
\]

and

\[
\boxed{
D(\widetilde w\|w)=F_q'(1),
\qquad
D(w\|\widetilde w)=-F_q'(0).}
\tag{25}
\]

### Proof

Equation (23) is (20) with \(z=1+it\). Equation (24) follows from (21). Both measures have full
support, so direct summation gives

\[
D(\widetilde w\|w)=\sum_n\widetilde w_nx_n=F_q'(1)
\]

and

\[
D(w\|\widetilde w)=-\sum_nw_nx_n=-F_q'(0).
\]

All sums converge by the exponential tail. QED.

This is a cross-doctrine withheld prediction: the analytic \(q\)-difference law predicts an
unmeasured probabilistic intervention, its characteristic response, and both directed information
costs.

## 6. One-process synthesis

The single constitutive response \(F_q\) has the exact chart:

\[
\boxed{
\begin{array}{c}
\text{positive discrete law }\mu_q\\
\Updownarrow\\
\text{positive kernel }K_q\\
\Updownarrow\\
\text{GNS pair }(\mathcal H_q,X,\Omega)\\
\Updownarrow\\
\text{recurrent observer }U_t\Omega
\text{ with open lift }tX\Omega\\
\Updownarrow\\
\text{hypertranscendental analytic process }\Gamma_q(1+s)\\
\Updownarrow\\
\text{exponential tilt and entropy response}
\end{array}}
\tag{26}
\]

The vertical arrows are explicit equations (3), (10), (14), (19), and (23), not analogies.

This passes the infinite common-process gate of Constitutive Process Mathematics:

- positivity, recurrence, open history, and HT occur in one source-normalized process;
- observed compactness and maximal differential intervention memory coexist without being
  identified;
- one functional equation predicts a response in another intervention doctrine.

## 7. Hostile boundaries

1. The ingredients are classical: \(q\)-binomial theorem, Jackson \(q\)-Gamma, GNS/Bochner,
   compact pure-point dynamics, relative entropy, and Pastro's \(q\)-Hölder theorem.
2. Atomicity is load-bearing for norm-precompact recurrence. A continuous spectral law can be
   positive and HT without recurrent vector orbit.
3. The marked lift (16) is extra information erased by the phase observer.
4. Hypertranscendence does not follow from positive Hankel rank; many DA measures have infinite
   support and full moment rank.
5. Recurrence does not imply HT; finite atomic laws are recurrent and exponential-polynomial.
6. The functional equation supplies the tilt but no physical clock, Hamiltonian cost, or
   Brown--Susskind complexity.
7. No Morita/presentation invariance theorem, higher-slot intervention process, RH statement, or
   arithmetic zero theorem follows.

## Primary parents

- P. I. Pastro, *The q-analogue of Hölder's theorem for the gamma function*, Rendiconti del
  Seminario Matematico della Università di Padova **70** (1983), 47--53,
  <https://www.numdam.org/item/RSMUP_1983__70__47_0/>.
- Jackson's \(q\)-Gamma definition and the \(q\)-binomial theorem, summarized in NIST DLMF,
  Chapter 17, <https://dlmf.nist.gov/17>.

## Log

- 2026-08-09 — positive atomic representation, GNS recurrence, open lift, Pastro
  hypertranscendence, and exact entropy tilt closed as one infinite CPM process.
- 2026-08-10 — §4 closed in Lean: `qᶻ` and the q-digamma jets are algebraically independent over
  `ℂ(z)`, and Pastro's q-analogue of Hölder's theorem is certified unconditionally.  Card promoted
  to stage 3.

## Lean certification status

**COMPLETE.**  Modules `GaloisForLFunctions/HTGeometry/QBinomialTheorem.lean` and
`GaloisForLFunctions/HTGeometry/ConstitutiveQGammaProcess.lean`, both wired into
`GaloisForLFunctions.HTGeometry.UniversalLawField` (11,512-job build green).  The corpus already
owned the q-Pochhammer/q-Gamma layer (`HTGeometry/QPochhammer.lean`): `qGamma`, Jackson's
translation law `qGamma_shift` (equation (20)), `qGamma_one`, `qGamma_two`, `qGammaWeight`
(equation (2)), `qGammaWeight_nonneg`, `qGammaWeight_hasSum_one`, and the integral q-binomial
transform.

Certified so far — everything except §4 and two clauses noted below:

- **The complex q-binomial theorem** `∑ aⁿ/(q;q)ₙ = 1/(a;q)_∞` for `‖a‖ < 1`
  (`qBinomial_hasSum`), the analytic input the corpus had deferred: Euler's functional equation
  `F(aq) = (1−a)F(a)` (`qBinomialTerm_hasSum_mul`), its iteration (`qBinomialSum_mul_prod`) and
  Tannery's theorem for the limit (`tendsto_qBinomialSum_mul_qpow`).
- **§1** — `qGammaAtom` (equation (2)), `qGammaResponse`, `qGammaWeight_pos`,
  `qGammaWeight_le_pow` (`0 < w_n ≤ qⁿ`), and **equation (3)** `qGammaResponse_hasSum`.
- **§2** — the GNS realization in `lp (fun _ : ℕ => ℂ) 2`: `qOmega` (`Ω = (√w_n)`), `qOrbit`
  (`U_tΩ`), `qChar` (equation (7)), `inner_qOrbit` and **equation (10)** `qChar_eq_inner`,
  **equation (11)** `qChar_kernel_eq_normSq` and `qChar_kernel_nonneg`; the moment layer
  `qMomentTerm_summable` (every polynomial moment converges, from `w_n ≤ qⁿ`), `qMoment`,
  **equation (12)** `qMomentMatrix`, `qMomentMatrix_hasSum`, `qMomentMatrix_quadratic`, and
  **equation (13)** `qMomentMatrix_posDef` (through `qGammaAtom_injective` and the fact that a
  nonzero polynomial cannot vanish on the infinite atomic support).
- **§3** — `norm_sq_lp`, `norm_qOrbit_sub_qOmega_sq`, **equation (15)**
  `exists_qOrbit_near_qOmega` (recurrence at arbitrarily late *integer* times, by the corpus's
  compact-group recurrence `exists_pow_mem_of_compactSpace` in the torus `Fin (N+1) → Circle`
  together with the tail bound `∑_{n>N} w_n → 0`), **equation (16)** `qLift`, `norm_qLift_sq`,
  `qMoment_two_pos`, and **equation (17)** `norm_qLift_tendsto_atTop`.
- **§5** — **equation (21)** `qTiltWeight`, `qTiltWeight_pos`, `qTiltWeight_hasSum_one` (the tilt
  is again a probability law, because `Γ_q(2) = 1`), **equation (24)** `log_qTiltWeight_div`,
  **equation (22)** `qTilt_hasSum`, and **equation (23)** `qTilt_response_eq` (Jackson's
  functional equation).

`#print axioms` on every one of these reports only `propext`, `Classical.choice`, `Quot.sound`.

Also certified since: **equation (25)** — `qWeightExp_summable` (all weighted exponential-tilt
moments converge), `qResponseFun` and `qResponseFun_eq`, `qStrip` with `isOpen_qStrip` and
`convex_qStrip`, `norm_qResponseTerm_deriv_le`, and `hasDerivAt_qResponseFun` (term-by-term
differentiation of the response series on the strip `−1/2 < Re s < 2`, through mathlib's
`hasDerivAt_tsum_of_isPreconnected`); then `qKLTiltBase`, `qKLBaseTilt`, `qKLTiltBase_eq`,
`qKLBaseTilt_eq`, and finally `deriv_qResponseFun_one : F_q'(1) = D(w̃‖w)` and
`deriv_qResponseFun_zero : F_q'(0) = −D(w‖w̃)`.

Resolvent layer started: `summable_norm_sq_of_memℓp`, `lpDiagFun`, `memℓp_lpDiagFun`, `lpDiagLM`,
`lpDiagLM_norm_le`, `lpDiagCLM`, `lpDiagCLM_opNorm_le` — the diagonal operator of a bounded
sequence on `ℓ²`, which mathlib does not have.

Also certified since: **the compact-resolvent clause** of §2 and **the analytic q-Gamma layer**.

- Diagonal operators on `ℓ²`, absent from mathlib: `lpDiagFun`, `memℓp_lpDiagFun`, `lpDiagLM`,
  `lpDiagLM_norm_le`, `lpDiagCLM`, `lpDiagCLM_opNorm_le`, `lpSingleCLM`,
  `isCompactOperator_lpSingleCLM`, `isCompactOperator_rankOne` (rank-one operators factor through
  `ℂ`, which is locally compact), `isCompactOperator_finset_rankOne`,
  `lpDiagCLM_trunc_eq_sum`, and **`isCompactOperator_lpDiagCLM`**: a diagonal operator whose
  entries tend to zero is compact, by norm approximation with finite-rank truncations
  (`isCompactOperator_of_tendsto`).
- The q-Gamma resolvent: `qResolventEntry`, `norm_qGammaAtom_sub_I`, `qResolventEntry_bound`,
  **`qResolventEntry_mul`** (the resolvent inverts `X − i` coordinatewise),
  `tendsto_qGammaAtom_atBot`, `tendsto_norm_qResolventEntry`, `qResolvent`, and
  **`isCompactOperator_qResolvent`**.  Together with `qGammaAtom_injective` (distinct eigenvalues)
  and `qMomentTerm_summable q (2k)` (`Ω ∈ Dom X^k`), this is Theorem 2.1's operator clause in the
  only form mathlib can state it: mathlib has no unbounded self-adjoint operator theory, so the
  resolvent is certified as the explicit compact diagonal operator that inverts `X − i`.
- `QGammaAnalytic.lean` — the q-Gamma as a plain analytic function of `z`, needed for the
  differential theory of §4: `qHalfPlane`, `qDenomFactor`, `qDenomProduct`, `qDenomProduct_eq`,
  `qDenomProduct_ne_zero`, `hasProdLocallyUniformlyOn_qDenomFactor` (locally uniform convergence of
  `(qᶻ;q)_∞` on `{Re z > 0}`, by the mathlib bound `Summable.hasProdUniformlyOn_one_add` against
  `q^δ qᵏ` on each compact), `differentiableOn_qDenomProduct`, `qGammaOn`, `qGammaOn_eq_qGamma`,
  `qGammaOn_ne_zero`, `differentiableOn_qGammaOn`, and `qGammaOn_shift`.

Also certified since: the **q-digamma layer** (`QDigamma.lean`), the first step of §4:
`analyticOnNhd_qGammaOn`, `qcpow_ne_one`, `hasDerivAt_qcpow`, `qDigamma` (`ψ_q = Γ_q'/Γ_q`),
`qShiftIncrement`, and **`qDigamma_shift`**:

`ψ_q(z+1) = ψ_q(z) − (log q)·qᶻ/(1 − qᶻ)`,

the q-analogue of the digamma recurrence `ψ⁽ʲ⁾(z+1) = ψ⁽ʲ⁾(z) + (−1)ʲ j!/z^{j+1}` that drives
Hölder's theorem.

Also certified since: the **q-Bell substitution layer** (`QGammaBellSubstitution.lean`):

- `analyticAt_qcpow`, `analyticAt_qDigamma`, `analyticAt_qShiftIncrement`,
  `analyticAt_iteratedDeriv_qDigamma`, `analyticAt_iteratedDeriv_qShiftIncrement`,
  `mem_qHalfPlane_add_one`;
- **`iteratedDeriv_qDigamma_shift`** — the differentiated Jackson recurrence
  `ψ_q⁽ʲ⁾(z+1) = ψ_q⁽ʲ⁾(z) + ∂ʲ(−(log q)qᶻ/(1−qᶻ))(z)`;
- **`qGamma_iteratedDeriv_eq_bellCore`** — the q-Bell chain
  `Γ_q⁽ᵏ⁾ = Γ_q·B_k(ψ_q, …, ψ_q⁽ᵏ⁻¹⁾)`, reusing the corpus's combinatorial Bell family
  `bellCore` and the jet-evaluation derivative `hasDerivAt_mvEval_jet` unchanged.

## Remaining: §4, Pastro's q-analogue of Hölder's theorem

The decisive structural point is now settled: **in the `z`-picture the q-jet substitution is
unipotent, exactly as in the classical case** — `iteratedDeriv_qDigamma_shift` gives
`Y_j ↦ Y_j + δ_j` with `δ_j = ∂ʲ(−(log q)qᶻ/(1−qᶻ))`, with no scaling factors (those would appear
only in the `u = qᶻ` picture).  Consequently the corpus's elimination engine applies verbatim
*except* for its base field.

**Step 1 is done.**  `ShiftEliminationEngine.lean` (576 lines) carries the whole Hölder elimination
over an abstract base field:

```
no_shift_stable_annihilatorGen :
  ∀ {K} [Field K] [Algebra ℂ K] (σ : K →+* K) (rj : ℕ → K) {m},
    Function.Injective σ →
    (∀ t : ℂ, σ (algebraMap ℂ K t) = algebraMap ℂ K t) →
    (∀ {w : K}, σ w = w → ∃ t : ℂ, w = algebraMap ℂ K t) →
    ∀ I : Set (MvPolynomial (Fin m) K),
      (closed under subtraction) → (closed under C-scalars) →
      (closed under jetTranslateGen σ rj m) → (contains no nonzero constant) →
      (∀ {w δ}, σ w − w = ∑ j, algebraMap ℂ K (δ j) * rj j → ∀ j, δ j = 0) →
      (∃ G ∈ I, G ≠ 0) → False
```

with the jet-translation layer `jetTranslateGen`, `transMonomialGen`, `subTopMonomialGen`,
`transMonomial_decomposition`, `coeff_transMonomial_of_degSum_eqGen`,
`coeff_transMonomial_of_degSum_succGen`, `coeff_transMonomial_of_degSum_ltGen`,
`totalDegree_transMonomial_leGen`, `jetTranslate_eq_sumGen`, `totalDegree_jetTranslate_leGen`,
`coeff_jetTranslate_of_le_degSumGen`, `coeff_jetTranslate_of_le_degSum_succGen`, all proved over an
arbitrary `K`.  `#print axioms` reports only `propext`, `Classical.choice`, `Quot.sound`; the file
compiles with no warnings.

**Step 2 is under way.**  `QShiftField.lean` builds the two-variable field and its shift:

- `qConst`, `qConst_ne_zero`, `qShiftPolyMap` (`p ↦ p^{z↦z+1}(q·X)`), `qShiftPolyMap_ne_zero`,
  `qShiftCompHom`, `qShiftCompHom_mem_nonZeroDivisors`;
- **`qShift`** — the endomorphism `f(z,u) ↦ f(z+1, q·u)` of `ℂ(z,u) = RatFunc (RatFunc ℂ)`, built
  exactly as the corpus builds `ratShift`, with `qShift_injective`, `qShift_algebraMap`,
  `qShift_coeff` and **`qShift_const`** (constants are fixed) — two of the engine's three
  σ-hypotheses;
- **`ratShift_eq_const_mul_self`** — the scaled shift brick: a nonzero `r ∈ ℂ(z)` with
  `r(z+1) = c·r(z)` for a constant `c` forces `c = 1`, proved through the polynomial form
  `shift_scaled_cross_const` by comparing leading coefficients (the unit shift preserves them).
  This is the lemma that will force `u`-monomials to have degree zero in the invariance argument.

(The two-variable field needs `set_option maxSynthPendingDepth 4`: `NoZeroDivisors` and
`IsSimpleRing` for `RatFunc (RatFunc ℂ)` are beyond the default instance-search depth.)

**Step 2b is done.**  `QShiftField.lean` now also carries the invariance theorem, which is the
third and last `σ`-hypothesis of the engine:

- `qShiftPolyMap_coeff` (`(σP)_i = ratShift(P_i)·qⁱ`), `qShiftPolyMap_natDegree`,
  `qConst_pow_eq`, `qpow_injective`;
- **`monomial_of_qShift_eigen`** — a nonzero polynomial with `σP = c·P` is a monomial: two nonzero
  coefficients would give a rational function of `z` whose unit shift is `q^{j−i}` times itself,
  which `ratShift_eq_const_mul_self` forbids;
- `exists_qShift_eigen_const` — the coprime factorisation produces the eigenrelation;
- **`qShift_fixed_eq_const`** — every `f ∈ ℂ(z,u)` with `f(z+1, qu) = f(z,u)` is a constant.  Proof:
  cross-multiply the invariance on `f = P/Q` in lowest terms, get `σP = cP` and `σQ = cQ` with the
  same `c`, conclude both are monomials, use coprimality to force one degree to vanish and the
  scaled brick to force the two degrees to be equal, and finish with the classical
  `ratShift_fixed_eq_const` on the remaining coefficient ratio.

**Step 2c is done.**  `QShiftField.lean` now also carries the coboundary obstruction:

- `evalConst` (evaluation of a polynomial over `ℂ(z)` at a complex constant), with
  **`evalConst_qShiftPolyMap`**: `σP` evaluated at `c` is `ratShift(P(q·c))` — the shift moves
  evaluation points by `q`;
- `not_both_evalConst_zero` (coprime polynomials have no common complex root),
  `finite_evalConst_zero` (the complex poles of a rational function are finite);
- **`qShift_sub_self_ne`** — no `w ∈ ℂ(z,u)` satisfies `σw − w = D` when `D` is a rational function
  whose only complex pole is `u = 1`.  The proof clears denominators to the polynomial identity
  `σP·R·B − P·σR·B = A·σR·R` and evaluates it at three kinds of points: if `w` is regular at `1`
  and at `q`, evaluation at `1` already contradicts `A(1) ≠ 0`; otherwise the pole set of `w` in
  `ℂ` is finite and nonempty, its largest-modulus point `b` forces `b/q` to be a pole of `D`, hence
  `b = q`, while its smallest nonzero-modulus point `a` forces `a` to be a pole of `D`, hence
  `a = 1` — and `1 ≤ q < 1` is absurd.

**Step 2d is done** — all four hypotheses of the elimination engine are now available for the
q-shift.  `QIncrement.lean` builds the algebraic increments and the residue condition:

- `qLog`, `qLog_ne_zero`, `qIncrNum` (the numerators `A_j`, by the recursion
  `A_{j+1} = (log q)·u·(A_j'(1−u) + (j+1)A_j)`), **`qIncrNum_eval_one`**
  (`A_j(1) = −(log q)^{j+1}·j!`) and `qIncrNum_eval_one_ne_zero`;
- `qIncrNumC`, `qPoleFactor`, `evalConst_qPoleFactor_eq_zero_iff` (the only complex root of
  `(1−u)^{j+1}` is `1`), and **`qIncr`** — the increments `δ_j = A_j(u)/(1−u)^{j+1}` in `ℂ(z,u)`;
- `qIncrCombNum`, **`qIncr_combination_eq`** (a combination supported below `N` is one fraction with
  denominator `(1−u)^{N+1}`), `evalConst_qIncrCombNum_one` (its numerator at `u = 1` is
  `c_N·A_N(1)`);
- **`qIncr_not_coboundary`** — the engine's residue condition: if `σw − w = ∑ c_j δ_j` then every
  `c_j` vanishes.  Taking `N` maximal in the support, the combination is `Num/(1−u)^{N+1}` with
  `Num(1) = c_N A_N(1) ≠ 0`, so its denominator vanishes at `1` and nowhere else, and
  `qShift_sub_self_ne` applies.

Remaining for §4:

3. **Assembly.**  Three pieces:
   (a) the embedding `ℂ(z,u) → meromorphic germs`, `z ↦ z`, `u ↦ qᶻ`, together with its
       injectivity — equivalently the transcendence of `qᶻ` over `ℂ(z)`, provable by the growth
       argument already used for `exp(z²)` in `ConstitutiveDoctrineMemoryWitnesses`
       (`eq_zero_of_tendsto_zero_atTop_real`);
   (b) the identification of `qIncr q j` with the analytic jets
       `iteratedDeriv j (qShiftIncrement q)` under that embedding;
   (c) the classical assembly: convert an algebraic differential equation for `Γ_q` into a
       `Γ_q`-power relation via `qGamma_iteratedDeriv_eq_bellCore`, eliminate the `Γ_q`-degree
       against the multiplier `(1−qᶻ)/(1−q)`, and feed the resulting jet relation into
       `no_shift_stable_annihilatorGen` with `qShift_injective`, `qShift_const`,
       `qShift_fixed_eq_const` and `qIncr_not_coboundary`.

### §4 is done — Pastro's q-analogue of Hölder's theorem is certified

**COMPLETE.**  Six new modules close the assembly.

- `QTranscendence.lean` — **the transcendence of `qᶻ` over `ℂ(z)`**: `neg_log_pos`,
  `qrpow_eq_exp`, `tendsto_pow_mul_qrpow`, `tendsto_normPoly_mul_qrpow`, and
  **`exists_qcpow_combination_ne_zero`**: if `c_{i₀} ≠ 0` and every lower coefficient vanishes,
  then `∑_i c_i(x)·(qˣ)ⁱ ≠ 0` somewhere on `[1,∞)`.  The lowest surviving power dominates because
  `q^{kx}` decays faster than any polynomial grows; the corpus's `normPoly` majorant and
  `eq_zero_of_tendsto_zero_atTop_real` finish it.
- `QIncrementAnalytic.lean` — **the analytic jets are the algebraic increments**: `qIncrFun`,
  `qIncrFun_zero`, `hasDerivAt_qIncrFun`, **`iteratedDeriv_qShiftIncrement`**
  (`∂ʲ(−(log q)qᶻ/(1−qᶻ)) = A_j(qᶻ)/(1−qᶻ)^{j+1}`, by induction: differentiating the closed form
  under `du/dz = (log q)u` reproduces exactly the recursion defining `A_{j+1}`), and
  **`iteratedDeriv_qDigamma_shift_closed`**, the closed-form differentiated Jackson recurrence.
- `ShiftEigenrelationEngine.lean` — the corpus's eigenrelation refutation ported to an abstract
  shifted field: `jetTranslateInvGen`, `jetTranslateInv_comp_jetTranslateGen`,
  `jetTranslate_comp_jetTranslateInvGen`, `jetTranslateGen_injective`,
  **`totalDegree_jetTranslateGen`**, and **`no_shift_eigenrelationGen`** — no nonzero jet
  polynomials satisfy `σ(f)·g = M·f·σ(g)` once the scalar equation `σ(r) = M·r` has only the zero
  solution.  Reduce to relatively prime parts, get `σf ∣ f` and `σg ∣ g`, note the jet substitution
  preserves total degree, so both quotients are scalars and the top-coefficient ratio solves the
  scalar equation.
- `QShiftInverse.lean` — the q-shift is an **automorphism** and Jackson's multiplier carries a
  degree obstruction: `ratShiftInv_const`, `qShiftPolyMapInv`, `qShiftPolyMapInv_ne_zero`,
  `qShiftCompHomInv`, **`qShiftInv`**, `qShiftPolyMapInv_qShiftPolyMap`,
  `qShiftPolyMap_qShiftPolyMapInv`, `qShiftInv_qShift`, `qShift_qShiftInv`; then `qOneSub`,
  `qMultPoly`, **`qMult`** (`M = (1−u)/(1−q)`), `natDegree_qMultPoly`, `qMult_ne_zero`, and
  **`qShift_eq_qMult_pow_mul_eq_zero`** — no nonzero `r ∈ ℂ(z,u)` has `r(z+1,qu) = Mᵉ·r(z,u)` for
  `e ≥ 1`, because the shift preserves `u`-degrees while `Mᵉ` raises them by `e`.
- `QDigammaHypertranscendental.lean` — **the elimination**.  `toQField` (`ℂ[z][u] → ℂ(z,u)`) with
  `toQField_injective`; `qPoint`, `qCoeffEval` (evaluation at `(z,qᶻ)`), `zShift`, `qIntShift`,
  **`toQField_qIntShift`** (the integral shift realizes `qShift`) and **`qCoeffEval_qIntShift`**
  (evaluating after the shift is evaluating at `z+1`); **`qCoeffEval_eq_zero`**, the
  transcendence statement in the form the engine consumes; `qDigammaJet`, `qPolyJetEval`,
  `AnnihilatesQDigamma`; **`exists_qClear`** (every element of `ℂ(z,u)` is a fraction of elements
  of `ℂ[z][u]`, through `IsLocalization.integerNormalization`); the annihilator set
  **`qAnnihilator`** with `qAnnihilator_sub`, `qAnnihilator_smul`, `qAnnihilator_const`; the
  cleared substitution `qDen`, `qPoleNum`, `toQField_qPoleNum`, **`qClearedShift`**,
  **`map_qClearedShift`**, **`qPolyJetEval_qClearedShift`**,
  `annihilatesQDigamma_qClearedShift`, `qAnnihilator_shift`; and finally
  **`annihilatesQDigamma_eq_zero`** — *`qᶻ` and the jets `ψ_q, ψ_q', ψ_q'', …` are algebraically
  independent over `ℂ(z)`*.
- `QGammaHypertranscendental.lean` — **Pastro's theorem**.  `qMultInt`, `toQField_qMultInt`,
  `qCoeffEval_qMultInt`; `qGamma_iteratedDeriv_eq_bellAt` and `qPolyJetEval_map_C`;
  **`QGammaPowerRel`** and **`qGammaPowerRel_eq_zero`** — a cleared `Γ_q`-power relation has all
  coefficients zero, by strong induction on the `Γ_q`-degree: Jackson's functional equation
  contributes `Mᵏ` in degree `k`, cross-multiplying against the top coefficient eliminates it, the
  inductive hypothesis kills the eliminated relation, and what survives is either a single term —
  killed by `annihilatesQDigamma_eq_zero` — or the eigenrelation `σ(f)·g = M^{e}·f·σ(g)`, refuted
  by `no_shift_eigenrelationGen` against the `u`-degree obstruction; and the capstone
  **`qGamma_jet_annihilator_eq_zero`**:

  *no nonzero `P ∈ ℂ[z, Y_0, …, Y_{n+1}]` satisfies `P(z, Γ_q(z), Γ_q'(z), …, Γ_q^{(n)}(z)) = 0`
  for all `z` with `Re z > 0`.*

  The transfer is the corpus's Bell machinery reused unchanged (`bellAt`, `bellGraded`,
  `eval₂_bell_expansion`, `eval₂_reshapeJet`, `exists_bellAt_solution`): the Bell substitution
  turns the differential polynomial into the `Γ_q`-power relation, and the triangular pointwise
  surjectivity of the Bell value map turns the vanishing of all graded coefficients back into
  `P = 0`.

No hypothesis, interface, or postulate is carried: the four `σ`-hypotheses of the elimination
engine (`qShift_injective`, `qShift_const`, `qShift_fixed_eq_const`, `qIncr_not_coboundary`), the
two inverse laws of the eigenrelation engine, the degree obstruction, and the transcendence input
are all proved.  `#print axioms` on `qGamma_jet_annihilator_eq_zero`, `qGammaPowerRel_eq_zero`,
`annihilatesQDigamma_eq_zero`, `exists_qcpow_combination_ne_zero`,
`iteratedDeriv_qDigamma_shift_closed`, `qShift_eq_qMult_pow_mul_eq_zero` and
`no_shift_eigenrelationGen` reports only `propext`, `Classical.choice`, `Quot.sound`.  The
`GaloisForLFunctions.HTGeometry.UniversalLawField` umbrella builds green (11,531 jobs).

**Scope note carried into stage 3.**  §2's operator clause is certified in the only form mathlib
can state it — the resolvent as the explicit compact diagonal operator inverting `X − i`, since
mathlib has no unbounded self-adjoint operator theory — and §3's recurrence (15) is certified at
integer times.  Everything else in §§1–5 is certified exactly as stated.
