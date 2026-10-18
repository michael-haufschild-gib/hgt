# Uniform physical coercivity of the factorial correction tails

- **ID:** APT-ROOT-WINDOW
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper; Lean certificate required)
- **Source:** [Foundational programme](../../../reports/arithmetic-positivity-theory/research-foundational.md), APT-06–07.
- **Audit verdict:** BRIDGE. Classical separated-frequency mean-square estimates and a dominant Fourier harmonic give this consequence of the exact source collar. No literature novelty is claimed.

## Objects and exact statement

Use the objects and source dictionary of the [Bohr coercivity proof](arithmetic-positivity-factorial-bohr-coercivity.md):
\[
C(u)=\{u\}(1-\{u\})/2,\quad
P(u)=C(4u)/4-2C(2u)+4C(u),
\]
\[
\lambda_N=N(1+\varepsilon_N),\quad
\Phi_N(v)=P(\lambda_Nv)-P(Nv),\qquad N\ge1.
\]
Here \(\varepsilon_N=\texttt{sourceFactorialCollar}\ N\). Put
\[
K=390/\pi,\qquad L=16K,
\qquad A=\frac{L}{16\pi^4(1+L)^4},\qquad
B=\frac{49(1+K)}{3\pi^4}.
\]
All four constants are positive and independent of every coefficient and source index.

For every finitely supported complex family \(b=(b_N)_{N\ge1}\), and every real \(a\),
\[
\int_a^{a+L}\left|\sum_N b_N\Phi_N(v)\right|^2dv
\ge \frac{L}{16\pi^4}\sum_N|b_N|^2.
\tag{1}
\]
Consequently,
\[
A\sum_N|b_N|^2
\le \int_1^\infty v^{-4}\left|\sum_Nb_N\Phi_N(v)\right|^2dv
\le B\sum_N|b_N|^2.
\tag{2}
\]
For the literal correction tails \(T_n=\texttt{factorialMuntzCorrectedTail}\ n\), this gives, for every finitely supported complex family \(c\),
\[
144A\sum_{n\ge0}\frac{|c_n|^2}{n+1}
\le \int_{\mathbb R}\left|\sum_n c_nT_n(x)\right|^2dx
\le225B\sum_{n\ge0}\frac{|c_n|^2}{n+1}.
\tag{3}
\]
Thus the normalized family \((\sqrt{n+1}\,T_n)\) is a Riesz sequence in physical \(L^2(\mathbb R)\). This asserts equivalence of coefficient and physical norms on its closed span, not completeness in the ambient space and not positivity of the signed Weil form.

## Frequency separation from the actual collar

The existing source bounds give
\[
1/15\le\delta_N:=N\varepsilon_N\le1/12,
\qquad\lambda_N=N+\delta_N.
\tag{4}
\]
On the positive axis the two frequency families are ordered
\[
N<N+\delta_N<N+1.
\]
Their successive gaps are at least \(1/15\) and \(11/12\), respectively. Reflection adds the negative frequencies, with a gap of at least two across zero. Therefore the distinct labeled frequencies
\[
\{N,\lambda_N,-N,-\lambda_N:N\ge1\}
\]
are uniformly separated by \(1/15\). Multiplication by an integer \(k\ge1\) gives separation \(k/15\). This uses the collar bounds alone; irrationality and separation between different harmonic layers are unnecessary.

The bounds in (4) follow from `sourceFactorialWidth_bounds`, `sourceFactorialWidth_le_collar`, and `sourceFactorialCollar_scaled_le_twelfth`. The first two also underlie the verified [tail amplitude bound](../../../../formal/GaloisForLFunctions/arithmetic-positivity-theory/FactorialTailPhase.lean); the third is in [FactorialMuntzTailPhaseCells.lean](../../../../formal/GaloisForLFunctions/BiScaleUncertainty/FactorialMuntzTailPhaseCells.lean).

## Interval control of each harmonic layer

Define
\[
H_k(v)=\sum_Nb_N\bigl(\cos(2\pi k\lambda_Nv)-\cos(2\pi kNv)\bigr).
\]
Expanding each cosine into two exponentials gives four coefficients of modulus \(|b_N|/2\) per index. Their total squared coefficient norm is exactly \(\sum_N|b_N|^2\).

The unconditional corpus theorems `interval_integral_normSq_expSum_ge` and `interval_integral_normSq_expSum_le` in [MontgomeryVaughanIntervalMeanSquare.lean](../../../../formal/GaloisForLFunctions/HTGeometry/MontgomeryVaughanIntervalMeanSquare.lean) bound a finite exponential sum with frequency gap \(D>0\) on an interval of length \(\ell\ge0\) between
\((\ell-26/(\pi D))\sum|c_r|^2\) and
\((\ell+26/(\pi D))\sum|c_r|^2\).
Applying these with \(D=k/15\) gives
\[
(\ell-K/k)\|b\|_2^2
\le \|H_k\|_{L^2(a,a+\ell)}^2
\le(\ell+K/k)\|b\|_2^2.
\tag{5}
\]
The lower estimate is useful only when its displayed coefficient is positive. No such restriction is needed for the upper estimate.

## The first harmonic dominates the remainder

The exact absolutely convergent Bernoulli expansion, established on paper in the linked Bohr proof, is
\[
\sum_Nb_N\Phi_N(v)
=-\frac2{\pi^2}\sum_{k\ge1}\frac{\chi(k)}{k^2}H_k(v),
\]
where \(\chi(k)=1\) for odd \(k\), \(-1\) for \(k\equiv2\pmod4\), and zero for \(4\mid k\). In particular,
\[
\chi(1)=1,\qquad
\sum_{k\ge2}|\chi(k)|/k^2\le3/4.
\tag{6}
\]
Uniform convergence for each finite coefficient family justifies this identity and passage to \(L^2\) on any bounded interval. Minkowski's inequality, (5), and (6) give
\[
\left\|\sum_Nb_N\Phi_N\right\|_{L^2(a,a+L)}
\ge\frac2{\pi^2}\left(\sqrt{L-K}-\frac34\sqrt{L+K}\right)\|b\|_2.
\]
Since \(K=L/16\),
\[
\sqrt{L-K}\ge\frac{15}{16}\sqrt L,
\qquad\sqrt{L+K}\le\frac{17}{16}\sqrt L.
\]
The bracket is at least \((9/64)\sqrt L\), hence at least \(\sqrt L/8\). Squaring proves (1).

The ordinary triangle inequality, applied to all harmonic layers, also gives for every \(\ell\ge0\)
\[
\int_a^{a+\ell}\left|\sum_Nb_N\Phi_N(v)\right|^2dv
\le \frac{49}{4\pi^4}(\ell+K)\sum_N|b_N|^2,
\tag{7}
\]
because the total absolute harmonic coefficient sum is at most \(7/4\). These estimates tolerate every resonance between different harmonic layers.

## Transport to the physical norm

Restricting the weighted integral to \([1,1+L]\), where \(v^{-4}\ge(1+L)^{-4}\), proves the lower half of (2). For the upper half, partition \([1,\infty)\) into the unit intervals \([j,j+1]\), \(j\ge1\). On each interval use \(v^{-4}\le j^{-4}\) and (7) with \(\ell=1\). The estimate
\[
\sum_{j\ge1}j^{-4}\le1+\int_1^\infty v^{-4}dv=4/3
\]
proves both integrability and the upper half of (2).

The literal source identity gives
\[
T_{N-1}(x)=a_{N-1}e^{3x/2}\Phi_N(e^{-x})\mathbf1_{x\le0},
\quad a_{N-1}=\frac1{N\varepsilon_N\sqrt N}.
\]
The substitution \(v=e^{-x}\) therefore turns its finite-combination square norm exactly into (2) with \(b_N=c_{N-1}a_{N-1}\). Equation (4) implies
\[
12/\sqrt N\le a_{N-1}\le15/\sqrt N.
\]
This proves (3), including integrability. Extending the finite synthesis map by continuity gives the stated Riesz-sequence interpretation.

## Audit and remaining boundary

This resolves the transport from arithmetic phase geometry to the physical \(L^2\) weight for this family on paper, with constants uniform over all finite coefficient sets. A Bohr mean alone would not prove it; the additional input is uniform separation of each fixed harmonic layer and dominance of the first layer. The constants are deliberately coarse.

The parent estimates are classical: [Montgomery–Vaughan, *Hilbert's inequality*, Theorem 2 and Corollary 2](https://personal.science.psu.edu/rcv4/personal/Publications/s2-8-1-73.pdf). Riesz questions for dilated periodic functions already have a developed theory; see [Hedenmalm–Lindqvist–Seip](https://arxiv.org/abs/math/9512211). The present proof is an application of those established analytic mechanisms to the exact factorial source, so its classification is BRIDGE.

The complete signed energy remains a separate problem. Equations (1)–(3) give neither a logarithmically weighted spectral lower bound nor a bound for the prime and polar terms relative to that lower bound. Positivity of this family's full Weil Gram matrices, density in the required form topology, and the universal RW criterion are not consequences claimed here.

**Formal certificates:** the four-branch frequency spacing (`four_branch_harmonic_freq_gap_ge` in [FactorialCollarIrrationalityAndSpacing.lean](../../../../formal/GaloisForLFunctions/arithmetic-positivity-theory/FactorialCollarIrrationalityAndSpacing.lean)), harmonic-layer Montgomery–Vaughan penalty (`harmonic_layer_mv_penalty_eq`), first-harmonic dominance (`window_first_harmonic_coercivity_sq_ge`), weighted window transport (`weighted_phase_window_transport`), and physical Riesz-sequence coefficient bounds (`factorialTail_riesz_coefficient_bounds`) are certified in [FactorialTailWindowRieszCoercivity.lean](../../../../formal/GaloisForLFunctions/arithmetic-positivity-theory/FactorialTailWindowRieszCoercivity.lean).
