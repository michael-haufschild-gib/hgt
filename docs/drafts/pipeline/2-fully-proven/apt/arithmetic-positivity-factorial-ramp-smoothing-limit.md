# Full Weil-energy continuity for the factorial ramp

- **ID:** APT-ROOT-RAMP-LIMIT
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** [Foundational programme, APT-05](../../../reports/arithmetic-positivity-theory/research-foundational.md#apt-05-close-the-compact-ramp-application).
- **Audit verdict:** BRIDGE. Compact approximation and domination by translation energy are classical. No literature-novelty claim is made.

## Exact statement

Let \(r_n=\texttt{sourceFactorialRamp}\,(n+1)\), let
\(\eta_k=\texttt{CHMDDoobGraph.mollifier}\ k\), and put
\(r_{n,k}=\eta_k*r_n\). Write the literal complete physical Weil energy as
\[
Q(f)=\operatorname{Re}\,\texttt{weilFullFunctional}(\Lambda)
       (\texttt{EF.weilTest}(f,f)).
\]
**[PROVED HERE, paper; Lean certificate required]** For every \(n\),
\[
\lim_{k\to\infty}Q(r_{n,k})=Q(r_n)
=\texttt{factorialSpanWeil}\ n\ 1\ 0.
\tag{1}
\]
The limit includes the prime, archimedean, and polar terms. No RH or positivity of the complete form is assumed. The theorem does not itself assert a sign for the limit.

## Discharged source inputs

- [SignedPrimePolarFactorialAtomicPacket.lean](../../../../formal/GaloisForLFunctions/BiScaleUncertainty/SignedPrimePolarFactorialAtomicPacket.lean) packages the literal ramp as the compact continuous function `factorialRampSource n`.
- [SignedPrimePolarSourceJumpDomain.lean](../../../../formal/GaloisForLFunctions/BiScaleUncertainty/SignedPrimePolarSourceJumpDomain.lean) proves `factorialSourceLeft_jump_integrable` without an analytic premise. [FactorialRampDiagonalIdentity.lean](../../../../formal/GaloisForLFunctions/BiScaleUncertainty/FactorialRampDiagonalIdentity.lean), through `factorialSourceLeft_autocorr_eq_ramp`, transfers that exact integrability statement to the ramp.
- [CHMDGraphMollification.lean](../../../../formal/GaloisForLFunctions/RHTower/CHMDGraphMollification.lean) proves nonnegativity, unit integral, smoothness, compact support, shrinking support radius, and the translation-square contraction `smooth_difference_L2_le` for this mollifier. Its `lineConvolution` uses the same scalar convolution integral as \(\eta_k*r_n\).
- [CompactFiniteJumpWeilFormula.lean](../../../../formal/GaloisForLFunctions/BiScaleUncertainty/CompactFiniteJumpWeilFormula.lean) proves the exact complete-energy formula on compact continuous sources with finite jump energy. [FactorialWeilGram.lean](../../../../formal/GaloisForLFunctions/BiScaleUncertainty/FactorialWeilGram.lean) applies that formula to the literal factorial span.
- [FactorialRampSmoothingAndGramMargin.lean](../../../../formal/GaloisForLFunctions/arithmetic-positivity-theory/FactorialRampSmoothingAndGramMargin.lean) certifies the ramp translation-increment $L^2$ contraction (`factorialRamp_smooth_difference_L2_le`), the smoothing-limit transfer (`factorialRamp_weil_limit_bounds_of_tendsto`), and the resulting Gram margin (`factorialRampTent_gram_margin_of_tendsto`).

## Proof

Fix \(n\), write \(r=r_n\), \(r_k=\eta_k*r\), and choose \(R\) with \(\operatorname{supp}r\subset[-R,R]\). The mollifiers are nonnegative, have mass one, are supported in \([-1,1]\), and their support radii tend to zero. Thus all \(r_k\) have support in the fixed interval \([-R-1,R+1]\).

The compact continuous function \(r\), extended by zero as already prescribed in its definition, is uniformly continuous on \(\mathbb R\). For every \(x\),
\[
|r_k(x)-r(x)|
\le\int\eta_k(a)|r(x-a)-r(x)|\,da
\le\sup_{|a|\le\operatorname{rad}(\eta_k),\,x\in\mathbb R}
      |r(x-a)-r(x)|\longrightarrow0.
\]
Hence \(r_k\to r\) uniformly and in \(L^2\), using their common compact support.

Put
\[
C_f(t)=\int_{\mathbb R}f(u)f(u+t)\,du,
\qquad
D_f(t)=\int_{\mathbb R}|f(u+t)-f(u)|^2\,du.
\]
Translation invariance gives \(D_f(t)=2(C_f(0)-C_f(t))\). Cauchy–Schwarz gives, uniformly in \(t\),
\[
|C_{r_k}(t)-C_r(t)|
\le\|r_k-r\|_2(\|r_k\|_2+\|r\|_2)\longrightarrow0.
\tag{2}
\]

Nonnegative unit-mass averaging contracts every translation increment. Indeed,
\[
\begin{aligned}
D_{r_k}(t)
&=\int\left|\int\eta_k(a)
        [r(u+t-a)-r(u-a)]\,da\right|^2du\\
&\le\int\!\int\eta_k(a)|r(u+t-a)-r(u-a)|^2\,da\,du
=D_r(t).
\end{aligned}
\tag{3}
\]
Jensen and Tonelli apply because the averaging measure is a probability measure and the squared integrands are nonnegative. All translation square integrals are finite by compactness. This is precisely the mechanism already formalized in `smooth_difference_L2_le`.

Let \(w(t)=\texttt{archLevySinhWeight}\ t\), positive for \(t>0\). The actual ramp's jump-domain theorem gives
\[
\int_0^\infty [C_r(0)-C_r(t)]w(t)\,dt<\infty.
\tag{4}
\]
Equations (2)–(3) imply pointwise convergence of the jump integrands and the domination
\[
0\le[C_{r_k}(0)-C_{r_k}(t)]w(t)
\le[C_r(0)-C_r(t)]w(t).
\]
Dominated convergence therefore proves convergence of the complete jump integral, including its singular endpoint at zero. It also admits every \(r_k\) to the same finite-jump domain. This is stronger than inferring energy convergence from \(L^2\) convergence alone.

All correlations have support in \([-2R-2,2R+2]\). The prime contribution samples \(C_f(\log j)\), so only the fixed finite set \(2\le j\le\exp(2R+2)\) can contribute. Equation (2) gives convergence of this finite prime sum, retaining its exact von Mangoldt weights.

The polar contribution integrates \(\texttt{polarDensity}(t)C_f(t)\) over the nonnegative half-line. Its integrands have common compact support and converge uniformly after multiplication by the continuous polar density there. Thus both polar branches converge. The zero-lag term \(\texttt{EF.gammaBracket}(0)C_f(0)\) converges by (2).

The exact identity from `re_weilFullFunctional_eq_of_compact_finite_jump` is
\[
Q(f)=\texttt{EF.gammaBracket}(0)C_f(0)
+\int_0^\infty[C_f(0)-C_f(t)]w(t)\,dt
-2\,\texttt{fullPairing}(C_f).
\]
Each term has just been controlled, proving the first equality in (1). The reflected left source has exactly the same autocorrelation as the ramp. Applying `factorialSpanWeil_eq_complete` with coefficients \((1,0)\) gives the second equality. This completes the paper proof.

## Application boundary

The [complete ramp–tent margin proof](arithmetic-positivity-factorial-ramp-gram-margin.md) combines this limit with the tail sampling theorem and corrected-source square budget. It explicitly applies `zeta_W_eq_weilFullFunctional_mixed` to identify the zero-side and complete physical energies of the smooth compact ramp before taking the limit. The full assembled Lean certificate remains required.

The support bound depends on \(n\): the theorem fixes \(n\) before taking \(k\to\infty\). This matches the application’s eventual smoothing quantifiers. A limit uniform in the growing support aperture would require an additional estimate.

The positive stability mechanism exposed here is specific: normalized nonnegative convolution contracts the positive translation-energy majorant. The complete Weil form itself contains signed prime and polar terms; their continuity is proved separately through common compact support. No monotonicity of the complete Weil form is claimed.
