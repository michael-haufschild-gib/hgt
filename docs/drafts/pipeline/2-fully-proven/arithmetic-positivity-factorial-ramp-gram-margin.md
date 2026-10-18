# A complete Weil margin on the factorial ramp–tent span

- **ID:** APT-ROOT-RAMP-MARGIN
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper; Lean certificate required)
- **Source:** [Factorial sampling task](../1-in-progress/arithmetic-positivity-factorial-tail-sampling.md), APT-04–05.
- **Audit verdict:** BRIDGE. This is a source-specific application of the sampling budget, full-form smoothing limit, and existing Gram estimates. Literature novelty is not established.

## Theorem

Put \(N=n+1\), \(L=\log N\), and let
\[
Q_n(c,d)=\texttt{factorialSpanWeil}\ n\ c\ d
\]
be the literal completed Weil energy of the actual factorial left and right sources. There is \(n_0\) such that, for all \(n\ge n_0\) and every \(c,d\in\mathbb R\),
\[
Q_n(c,d)\ge \frac{L}{8192N}c^2+\frac N2d^2.
\tag{1}
\]
Thus this two-dimensional coefficient form is positive definite for every sufficiently large arithmetic scale. Moreover, for an absolute \(C\),
\[
\frac{L}{4096N}\le Q_n(1,0)\le C\frac{1+L}{N}
\tag{2}
\]
for all sufficiently large \(n\). These are paper conclusions obtained below from unconditional source results. Their complete Lean certificates, including those of the two linked paper inputs, remain to be supplied.

## Source decomposition and exact pairing

Let \(r_n=\texttt{sourceFactorialRamp}\ N\), let \(T_n\) be the actual correction tail, and let \(H_n\) be the canonically boundary-corrected source. The exact corpus identity is \(H_n=r_n+T_n\). Convolve with the same normalized nonnegative kernel \(\eta_k=\texttt{CHMDDoobGraph.mollifier}\ k\) to obtain
\[
H_{n,k}=r_{n,k}+U_{n,k},\qquad r_{n,k}=\eta_k*r_n.
\tag{3}
\]
The source integrability and compact kernel support justify this convolution identity. All three smoothed sources have the required decay and readout integrability; \(r_{n,k}\) is smooth and compactly supported.

Use \(F_f(s)=\int e^{(s-1/2)x}f(x)\,dx\) and the actual zero divisor with multiplicities. Reflection is \(\rho^*=1-\overline\rho\), and
\[
\mathcal W(f,g)=\sum_\rho m_\rho F_f(\rho)\overline{F_g(\rho^*)},
\qquad \mathcal Z(f)=\sum_\rho m_\rho|F_f(\rho)|^2.
\]
These are the corpus's `zetaZeroConfig.W` and the independent absolute sampling mass: `gammaOf` and `reflect` give precisely this convention. Reflection preserves the zero divisor and multiplicities. Therefore square summability implies absolute convergence of each mixed sum and
\[
|\mathcal W(f,g)|\le\sqrt{\mathcal Z(f)\mathcal Z(g)}.
\tag{4}
\]
This follows from Cauchy–Schwarz on the multiplicity-weighted zero copies and reindexing by reflection. It assumes no sign for \(\mathcal W\).

## Corrected-source budget

The exact corrected-source readout is
\[
F_{H_n}(\rho)=\frac{c_n}{\rho},\qquad
c_n=\frac1{2\sqrt N},\qquad
F_{H_{n,k}}(\rho)=F_{\eta_k}(\rho)\frac{c_n}{\rho}.
\]
The corpus proves \(|F_{\eta_k}(\rho)|\le e\) for every \(k\). Put
\[
S=\sum_\rho\frac{m_\rho}{1+|\gamma_\rho|^2}<\infty,
\qquad \gamma_\rho=\frac{\rho-1/2}{i}.
\]
Finiteness is `WeilEF.zero_sum_inv_sq zetaSeam`. The actual zero-separation theorem gives \(|\operatorname{Im}\rho|\ge4\). With \(\rho=\beta+it\), the unconditional critical strip gives
\[
1+|\gamma_\rho|^2\le t^2+\frac54\le2t^2\le2|\rho|^2.
\]
Hence, for every \(n,k\),
\[
\mathcal Z(H_{n,k})\le\frac{e^2S}{2N}\le\frac{C_H}{N},
\qquad C_H=1+\frac{e^2S}{2}>0.
\tag{5}
\]
All sums used here are nonnegative and dominated by the displayed convergent series.

## The mixed term is lower order

The [sampling paper theorem](arithmetic-positivity-factorial-log-sampling.md) gives \(C_U>0\), independent of \(n,k\), with
\[
\mathcal Z(U_{n,k})\le C_U\frac{1+L}{N}.
\tag{6}
\]
The existing `factorialMuntzSmoothedTail_weil_log_rate` gives, eventually in \(n\) and then eventually in \(k\),
\[
\operatorname{Re}\mathcal W(U_{n,k},U_{n,k})\ge\frac{L}{2048N}.
\tag{7}
\]
Equations (3)–(6) make every term in the sesquilinear expansion absolutely summable. Expanding \(r_{n,k}=H_{n,k}-U_{n,k}\) and applying (4) separately to both mixed terms yields
\[
\operatorname{Re}\mathcal W(r_{n,k},r_{n,k})
\ge\frac1N\left[\frac L{2048}-C_H-2\sqrt{C_HC_U(1+L)}\right].
\tag{8}
\]
This estimate does not require positivity of the smoothed corrected-source diagonal: its absolute value is bounded by (5).

For example, if
\[
L\ge\max\{1,\ 8192C_H,\ 8\cdot8192^2C_HC_U\},
\]
then \(C_H\le L/8192\) and \(2\sqrt{C_HC_U(1+L)}\le L/8192\). Thus (8) is at least \(L/(4096N)\). Such a threshold exists since \(\log(n+1)\to\infty\). The only remaining threshold in \(k\) is the one in (7), for each fixed admitted \(n\).

For the upper bound, (4) and \(\mathcal Z(H-U)\le2\mathcal Z(H)+2\mathcal Z(U)\) give, for all \(n,k\),
\[
|\mathcal W(r_{n,k},r_{n,k})|
\le2(C_H+C_U)\frac{1+L}{N}.
\tag{9}
\]

## Removing smoothing in the complete form

`zeta_W_eq_weilFullFunctional_mixed` applies to the smooth compact source \(r_{n,k}\) in both slots. It identifies its zero-side pairing with the literal physical functional on `EF.weilTest`; this includes the prime, Gamma, and polar terms with the same normalization.

The [full smoothing-limit paper theorem](arithmetic-positivity-factorial-ramp-smoothing-limit.md) proves, for every fixed \(n\),
\[
\operatorname{Re}\mathcal W(r_{n,k},r_{n,k})\longrightarrow Q_n(1,0).
\]
Its last identification uses the exact equality of the ramp autocorrelation with that of `factorialSourceLeft n`. The limit controls the singular jump term and both completion terms; convergence of a truncated zero sum is not used. Taking \(k\to\infty\) in (8)–(9), with \(n\) fixed beyond the preceding threshold, proves (2).

## Exact Gram conclusion

The existing `factorialSpanWeil_eventual_lower` states, eventually in \(n\) and for all \(c,d\),
\[
Q_n(c,d)\ge c^2[Q_n(1,0)-E_n]+\frac{Q_n(0,1)}2d^2,
\qquad E_n=\frac{B_n^2}{2N},
\]
where `factorialWeilMixedBound_tendsto` gives \(B_n\to0\), and `factorialTentWeil_eventually_ge_scale` gives \(Q_n(0,1)\ge N\). Eventually \(B_n^2\le1\) and \(L\ge4096\), so \(E_n\le L/(8192N)\). Combining these statements with (2) proves (1), with one common threshold independent of \(c,d\).

The exact completion-of-the-square identity also gives
\[
\texttt{factorialWeilMinRamp}\ n\ge\frac{L}{8192N}>0
\]
eventually. This follows directly from `factorialWeilMinRamp_eventual_gap` and the same error bound.

## Mechanism and limits

The arithmetic tail has a positive diagonal of logarithmic size. The canonical correction has smaller absolute square-sampling mass, so Cauchy–Schwarz makes both mixed terms lower order. Exact control of the complete form under smoothing then transfers the margin to the compact ramp. The already quantified tent coupling cannot consume that margin.

This proves a paper-level instance of source-derived sign stability. It does not control combinations of ramps at different scales, give density in the full Weil form domain, or settle all-aperture RW positivity. Those require new cross-scale information. The parent questions about approximation coefficients and Gram matrices in [generalized Nyman–Beurling theory](https://arxiv.org/abs/2006.02953) and about completing [archimedean Weil positivity](https://arxiv.org/abs/2006.13771) remain relevant; this finite-family result makes no claim to resolve them.

## Exact corpus dependencies

- [FactorialMuntzUniformTail.lean](../../../../formal/GaloisForLFunctions/BiScaleUncertainty/FactorialMuntzUniformTail.lean): literal source decomposition and readout admission.
- [FactorialMuntzZeroReadout.lean](../../../../formal/GaloisForLFunctions/BiScaleUncertainty/FactorialMuntzZeroReadout.lean): corrected readout, kernel bound, and actual zero separation used in the reciprocal majorant.
- [FactorialMuntzZeroSideLimit.lean](../../../../formal/GaloisForLFunctions/BiScaleUncertainty/FactorialMuntzZeroSideLimit.lean): the summable genus-one zero majorant.
- [FactorialMuntzTailWeilGrowth.lean](../../../../formal/GaloisForLFunctions/BiScaleUncertainty/FactorialMuntzTailWeilGrowth.lean): the complete positive tail diagonal.
- [WeilPhiDoobPrimeAtoms.lean](../../../../formal/GaloisForLFunctions/RHTower/WeilPhiDoobPrimeAtoms.lean): `zeta_W_eq_weilFullFunctional_mixed`.
- [FactorialWeilGramDecoupling.lean](../../../../formal/GaloisForLFunctions/BiScaleUncertainty/FactorialWeilGramDecoupling.lean): uniform coefficient inequality and exact optimized gap.
- [RankOnePoleReadoutAndZeroNullspace.lean](../../../../formal/GaloisForLFunctions/arithmetic-positivity-theory/RankOnePoleReadoutAndZeroNullspace.lean): exact rank-one corrected-source readout, `factorialCorrected_zeroSquare_le`, and sesquilinear ramp splitting `factorialMuntzSmoothedRamp_re_W_eq`.
- [FactorialRampSmoothingAndGramMargin.lean](../../../../formal/GaloisForLFunctions/arithmetic-positivity-theory/FactorialRampSmoothingAndGramMargin.lean): smoothed compact-ramp eventual logarithmic lower bound (`factorialMuntzSmoothedRamp_weil_log_lower`), uniform upper bound (`exists_factorialMuntzSmoothedRamp_weil_norm_upper`), relative positive margin (`exists_factorialMuntzSmoothedRamp_relative_positive_margin`), smoothing-limit transfer (`factorialRamp_weil_limit_bounds_of_tendsto`), and two-dimensional Gram/Schur margin (`factorialRampTent_gram_margin_of_tendsto`).

