# Logarithmic sampling budget for the actual factorial correction tail

- **ID:** APT-ROOT-LOG-SAMPLING
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** [Factorial sampling task](../1-in-progress/arithmetic-positivity-factorial-tail-sampling.md).
- **Audit verdict:** BRIDGE. The proof combines exact corpus arithmetic with classical translation-energy, Fourier, and holomorphic sampling arguments. Novelty beyond this particular application is not established.

## Theorem

Let \(N=n+1\), let \(T_n\) be the actual `factorialMuntzCorrectedTail n`, and let \(U_{n,k}\) be its normalized smoothing `factorialMuntzSmoothedTail n k`. Write
\[
F_f(s)=\int_{\mathbb R}e^{(s-1/2)x}f(x)\,dx,
\qquad
\mathcal Z(f)=\sum_\rho m_\rho|F_f(\rho)|^2,
\]
where the sum is over distinct nontrivial zeros of the actual zeta function and \(m_\rho\) is their multiplicity.

**[PROVED HERE, paper]** There is an absolute constant \(C>0\) such that, for every \(n,k\in\mathbb N\),
\[
\mathcal Z(T_n)+\mathcal Z(U_{n,k})
\le C\frac{1+\log N}{N}.
\]
In particular, the foundational programme's \(C_U\log N/N\) target holds for \(N\ge2\), uniformly in every smoothing index. No RH or positivity premise is used. The complete theorem is not yet certified in Lean.

## Exact arithmetic inputs

Put \(\varepsilon_n=\texttt{sourceFactorialCollar}\ N\). The corpus gives
\[
0<\varepsilon_n\le1,
\qquad N\varepsilon_n\ge1/15.
\]
Indeed, `sourceFactorialCollar_budget` gives \(4N\varepsilon_n\le1\), while `sourceFactorialWidth_bounds` and `sourceFactorialWidth_le_collar` give the lower bound.

For \(y\ge0\), put \(B(y)=\{y\}(1-\{y\})/2\). Existing declarations give
\[
0\le B\le1/8,
\qquad |B(u)-B(v)|\le|u-v|/2\quad(u,v\ge0).
\]
The second bound includes integer joins: `clampedLatticeRemainder_eq_neg_bernoulli` identifies \(B\) with the negative periodic Bernoulli function, and `bernoulliPeriodic_lipschitz_bound` supplies its global Lipschitz bound.

Define the actual remainder
\[
R_n(y)=\frac{B(4(1+\varepsilon_n)y)-B(4y)}4
-2\bigl(B(2(1+\varepsilon_n)y)-B(2y)\bigr)
+4\bigl(B((1+\varepsilon_n)y)-B(y)\bigr).
\]
This is `factorialMuntzTailRemainder n y`. For \(u,v\ge0\),
\[
|R_n(u)|\le25/32<1,
\qquad
|R_n(u)-R_n(v)|\le14|u-v|.
\tag{1}
\]
For the first bound, each difference of two values of \(B\) has absolute value at most \(1/8\), and the absolute coefficients sum to \(25/4\). For the second, the three Lipschitz costs sum to
\((9/2)(2+\varepsilon_n)\le27/2<14\).

The exact identity `factorialMuntzSum_add_half_eq_remainder`, together with the definitions of completion and canonical boundary correction, gives
\[
T_n(x)=a_n e^{3x/2}R_n(Ne^{-x})\,\mathbf1_{x\le0},
\qquad
a_n=\frac1{N\varepsilon_n\sqrt N}\le\frac{15}{\sqrt N}.
\tag{2}
\]
This retains the nonzero endpoint value and the jump of the zero extension. No derivative of the fractional-part function is taken.

## Uniform weighted translation energy

For \(-1/4\le\sigma\le5/4\), put \(b=1+\sigma\in[3/4,9/4]\) and
\[
g_{n,\sigma}(x)=e^{(\sigma-1/2)x}T_n(x)
=a_ne^{bx}R_n(Ne^{-x})\mathbf1_{x\le0}.
\]
It is measurable, integrable, and square integrable by (1)–(2). In particular,
\[
\|g_{n,\sigma}\|_2^2\le\frac{225}{2bN}\le\frac{150}{N}.
\tag{3}
\]
Define
\[
D_{n,\sigma}(h)=\int_{\mathbb R}|g_{n,\sigma}(x+h)-g_{n,\sigma}(x)|^2\,dx.
\]
There is an absolute \(C_0\) such that, uniformly in \(n,\sigma\) and \(0<h\le1\),
\[
D_{n,\sigma}(h)\le C_0\min\{N^{-1},h\}.
\tag{4}
\]

Here is the full estimate. Translation invariance and \(|u-v|^2\le2|u|^2+2|v|^2\) give \(D(h)\le4\|g\|_2^2\le600/N\). On \(x\le-h\), write \(v=Ne^{-x}\) and split
\[
g(x+h)-g(x)
=a_n(e^{b(x+h)}-e^{bx})R_n(ve^{-h})
+a_ne^{bx}\bigl(R_n(ve^{-h})-R_n(v)\bigr).
\]
Since \(1-e^{-h}\le h\), (1) gives both \(|\Delta R|\le2\) and \(|\Delta R|\le14vh\). Multiplying these two bounds gives
\[
|\Delta R|^2\le28Ne^{-x}h.
\]
Also \(e^{bh}-1\le be^b h\), by integrating \(be^{bt}\) from \(0\) to \(h\). Squaring the split and integrating over \(( -\infty,-h]\), then enlarging to \(( -\infty,0]\), bounds its two terms by
\[
\frac{225b e^{2b}}N h^2
\quad\text{and}\quad
\frac{12600}{2b-1}h,
\]
respectively. On \((-h,0]\), only the untranslated source remains and its squared integral is at most \(225h/N\). On \((0,\infty)\), both sources vanish. Since \(N\ge1\), \(b\in[3/4,9/4]\), and \(h\le1\), the sum is at most
\[
\left(25425+\frac{2025}{4}e^{9/2}\right)h.
\]
Taking \(C_0\) to be the larger of this constant and \(600\) proves (4).

Splitting the following integral at \(1/N\), with the second interval empty when \(N=1\), now gives
\[
\int_0^1\frac{D_{n,\sigma}(h)}h\,dh
\le C_0\frac{1+\log N}{N}.
\tag{5}
\]
The estimate pays for the endpoint jump and for the oscillations at the arithmetic scale. It does not assert a smoothing-uniform \(H^1\) bound.

## From translations to logarithmic Fourier energy

Use the angular Fourier convention \(\widehat g(t)=\int e^{itx}g(x)\,dx\), so Plancherel gives \(\int|\widehat g|^2=2\pi\|g\|_2^2\). For every \(h\),
\[
D(h)=\frac1{2\pi}\int_{\mathbb R}|e^{ith}-1|^2|\widehat g(t)|^2\,dt.
\]
Tonelli applies to the nonnegative integrand. Consequently
\[
\int_0^1\frac{D(h)}h\,dh
=\frac1{2\pi}\int_{\mathbb R}I(t)|\widehat g(t)|^2\,dt,
\quad
I(t)=2\int_0^{|t|}\frac{1-\cos u}{u}\,du.
\tag{6}
\]
The continuous value at zero makes the scalar integral well defined. For \(T\ge1\), integration by parts yields
\[
\left|\int_1^T\frac{\cos u}{u}\,du\right|
\le\frac1T+1+\int_1^T\frac{du}{u^2}\le3.
\]
Thus \(I(t)\ge2\log|t|-6\) for \(|t|\ge1\). For \(|t|\le1\), \(\log(2+|t|)\le\log3\); for \(|t|\ge1\), \(2+|t|\le3|t|\). Therefore, for every real \(t\),
\[
\log(2+|t|)\le3+\log3+\tfrac12 I(t).
\tag{7}
\]
Equations (3), (5), (6), and (7) imply an absolute constant \(C_1\), uniform over the entire \(\sigma\)-interval, such that
\[
\int_{\mathbb R}\log(2+|t|)
 |F_{T_n}(\sigma+it)|^2\,dt
\le C_1\frac{1+\log N}{N}.
\tag{8}
\]
All exchanges above have nonnegative integrands; finiteness follows from the displayed bounds rather than being assumed.

### Equivalent Gamma-form transport

The existing Gamma–Lévy identity gives another complete route to (8), useful for reusing formal results. Put
\[
\omega(h)=\frac{e^{-h/2}}{1-e^{-2h}},\qquad
A=\int_1^\infty\omega(h)\,dh.
\]
The corpus proves \(2\omega(h)\le h^{-1}+1/2\), hence \(\omega(h)\le h^{-1}\) on \((0,1]\). On \((1,\infty)\),
\(\omega(h)\le(1-e^{-2})^{-1}e^{-h/2}\), so \(0\le A<\infty\).
Using the verified physical bounds \(\|g\|_2^2\le96/N\), \(D(h)\le384/N\), and the logarithmic translation bound with constant \(C_T\),
\[
\int_0^\infty\omega(h)D(h)\,dh
\le C_T\frac{1+\log N}{N}+\frac{384A}{N}
\le(C_T+384A)\frac{1+\log N}{N}.
\]
Both integrability and the bound follow by these nonnegative majorants, including at the singular endpoint.

For the Fourier convention \(\mathcal Fg(\xi)=\int e^{-2\pi i\xi x}g(x)\,dx\), the corpus identity equates this integral with
\[
\int_{\mathbb R}2\bigl(\theta'(2\pi\xi)-\theta'(0)\bigr)|\mathcal Fg(\xi)|^2\,d\xi.
\]
Here \(\theta'\) is `gammaHardyPhaseRate`; its displayed excess is nonnegative and even. Add Plancherel's mass term and apply the proved global comparison
\[
1+\log^+|\xi|\le C_\Gamma
\bigl[1+2(\theta'(2\pi|\xi|)-\theta'(0))\bigr].
\]
The resulting logarithmic Fourier bound has constant
\(C_\Gamma(96+C_T+384A)\), uniform in \(n,\sigma\). Finally substitute \(t=-2\pi\xi\) and use
\(\log(2+2\pi|\xi|)\le\log(2+2\pi)+\log^+|\xi|\) to obtain (8). Every input concerns the actual admitted \(L^1\cap L^2\) source; no positive-Weil-form assumption enters this transport.

## Sampling the actual zero divisor

The unconditional local zero-count theorem gives an absolute \(C_2\) with
\[
\sum_{|\operatorname{Im}\rho-t|\le1}m_\rho
\le C_2\log(2+|t|)\qquad(t\in\mathbb R).
\tag{9}
\]
The corpus's `exists_card_near_xi_zeros_le` supplies the large positive-height estimate with multiplicities; conjugation supplies negative heights, and finiteness of zeros in a bounded strip supplies the remaining compact height interval. Enlarging a constant gives (9). The critical-strip inclusion is unconditional.

The envelope for \(T_n\) makes \(F_{T_n}\) holomorphic on \(\operatorname{Re}s>-1\): on each compact substrip, all derivatives of the exponential kernel are dominated by an integrable polynomial times a decaying exponential. Use discs of radius \(r=1/4\) about the nontrivial zeros. They lie in \(-1/4<\operatorname{Re}s<5/4\). The subharmonic mean-value inequality gives
\[
|F_{T_n}(\rho)|^2
\le\frac1{\pi r^2}\int_{|s-\rho|<r}|F_{T_n}(s)|^2\,dA(s).
\]
Sum first over any finite collection of zero copies. At a point \(s=\sigma+it\), its disc-overlap count is at most the left side of (9). Nonnegativity, followed by the supremum over finite collections, therefore gives
\[
\mathcal Z(T_n)
\le\frac{C_2}{\pi r^2}
\int_{-1/4}^{5/4}\int_{\mathbb R}
\log(2+|t|)|F_{T_n}(\sigma+it)|^2\,dt\,d\sigma.
\]
Equation (8) and the finite strip width prove the claimed raw-tail budget and its square summability.

Finally, `factorialMuntzSmoothedTail_readout` and `factorialMuntzKernelReadout_bound` give
\(F_{U_{n,k}}(\rho)=F_{\eta_k}(\rho)F_{T_n}(\rho)\) and \(|F_{\eta_k}(\rho)|\le e\), uniformly in \(k\). Hence \(\mathcal Z(U_{n,k})\le e^2\mathcal Z(T_n)\), completing the theorem.

## Sharpness and the positive survivor

For sufficiently large \(n\), then sufficiently large \(k\), the existing theorem `factorialMuntzSmoothedTail_weil_log_rate` gives
\[
\frac{\log N}{2048N}\le\operatorname{Re}\mathcal W(U_{n,k},U_{n,k}).
\]
Reflection permutes the zero divisor with multiplicities. Ordinary \(\ell^2\) Cauchy–Schwarz therefore gives \(|\mathcal W(U,U)|\le\mathcal Z(U)\), without assuming positivity of \(\mathcal W\). Combining these facts with the theorem proves
\[
\frac{\log N}{2048N}
\le\operatorname{Re}\mathcal W(U_{n,k},U_{n,k})
\le\mathcal Z(U_{n,k})
\le C'\frac{\log N}{N}
\]
in the same eventual regime. Both signed energy and absolute sampling mass have the sharp order \(\log N/N\) there.

There is also a scale-independent relative sign margin. Taking \(\delta=1/(2048C')>0\) in the displayed bounds gives
\[
\operatorname{Re}\mathcal W(U_{n,k},U_{n,k})
\ge\delta\,\mathcal Z(U_{n,k})
\]
in the same eventual regime. This measures the actual family's signed energy against an independently positive spectral norm. It is the margin available to pay for a smaller corrected-source perturbation. Positivity of these individual vectors does not establish positivity on their linear span; cross-scale mixed pairings remain a separate obligation.

The existing lower square-mass bound \(1/(512N)\), together with the smoothing-uniform exponential envelope, also gives positive constants \(c',C''\) such that
\[
c'\log N
\le\frac{\operatorname{Re}\mathcal W(U_{n,k},U_{n,k})}{\|U_{n,k}\|_2^2}
\le C''\log N.
\]
The upper physical mass follows by squaring and integrating `factorialMuntzSmoothedTail_exp_bound`; the lower mass is `factorialMuntzSmoothedTail_sq_integral_eventually_lower`. Division is justified by that positive lower bound.

Thus an \(O(1/N)\) sampling budget, with constants uniform in the stated eventual regime, is false. Its positive survivor is the exact logarithmic energy scale. Physical square mass alone does not pay for this spectral energy; the logarithmic translation seminorm in (5) supplies the required scale. This is a family-specific conclusion, not a universal positivity theorem.

## Dependencies, applicability, and novelty boundary

- Exact source identities: [FactorialMuntzTailPrimitive.lean](../../../../formal/GaloisForLFunctions/BiScaleUncertainty/FactorialMuntzTailPrimitive.lean), [FactorialMuntzUniformTail.lean](../../../../formal/GaloisForLFunctions/BiScaleUncertainty/FactorialMuntzUniformTail.lean), and [ClampedRampLatticeSum.lean](../../../../formal/GaloisForLFunctions/BiScaleUncertainty/ClampedRampLatticeSum.lean).
- Periodic Lipschitz estimate: [ArithmeticClockFirstVariation.lean](../../../../formal/GaloisForLFunctions/RHTower/ArithmeticClockFirstVariation.lean).
- Actual divisor count: [XiLocalZeroDensity.lean](../../../../formal/GaloisForLFunctions/RHTower/XiLocalZeroDensity.lean); a primary quantitative external reference is [Hasanalizade–Shen–Wong](https://arxiv.org/abs/2107.06506).
- Smoothing: [FactorialMuntzTailSmoothing.lean](../../../../formal/GaloisForLFunctions/BiScaleUncertainty/FactorialMuntzTailSmoothing.lean) and [FactorialMuntzZeroReadout.lean](../../../../formal/GaloisForLFunctions/BiScaleUncertainty/FactorialMuntzZeroReadout.lean).
- Translation energies with logarithmic Fourier weights belong to established logarithmic regularity theory; see [Chen–Hauer–Weth](https://arxiv.org/abs/2312.15689). Equations (6)–(7) provide the specific elementary comparison needed here, without importing their extension theorem.
- The broader approximation/Gram difficulty already occurs in [Alouges–Darses–Hillion](https://arxiv.org/abs/2006.02953). This local budget neither resolves their global coefficient problem nor proves the universal Weil criterion.

The paper proof uses classical Plancherel, Tonelli, the holomorphic mean-value inequality, and the explicitly identified corpus theorems. The formalization obligation is to reproduce their exact application and the new source estimates in Lean. The subsequent full compact-ramp limit remains a separate task; it is not a premise of this sampling theorem and is not claimed proved here.
