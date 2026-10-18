# Full signed coercivity on the high-scale factorial tail span

- **ID:** APT-ROOT-SPAN-COERCIVITY
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper; Lean certificate required)
- **Source:** [Exact span-sign task](../1-in-progress/arithmetic-positivity-factorial-span-sign.md).
- **Audit verdict:** BRIDGE. This is a source-specific coercivity consequence of separated-frequency estimates, nonstationary phase, and the complete explicit formula. No literature novelty is established.

## Theorem and constants

Use the actual source dictionary and constants \(A,B,K,L\) from the [physical coercivity proof](arithmetic-positivity-factorial-window-coercivity.md). Thus
\[
\Phi_N(v)=P(\lambda_Nv)-P(Nv),\quad
\lambda_N=N+\delta_N,\quad1/15\le\delta_N\le1/12,
\]
and, for finite complex coefficients \(b_N\),
\[
B_b(v)=\sum_Nb_N\Phi_N(v),\qquad
f_b(x)=\sum_N\frac{b_N}{a_{N-1}}T_{N-1}(x)
=e^{3x/2}B_b(e^{-x})\mathbf1_{x\le0}.
\]
In particular, \(f_b\) is a finite combination of the literal raw correction tails, with no source replacement.

There exist absolute \(c>0\) and \(C\ge0\) such that for every integer \(M\ge2\) and every finite complex coefficient family supported on \(N\ge M\), the literal zeta Weil sum is absolutely convergent and
\[
\operatorname{Re}\mathcal W(f_b,f_b)
\ge(c\log M-C)\sum_N|b_N|^2.
\tag{1}
\]
This gives a positive form on the entire indicated tail span once its minimum index exceeds a fixed threshold. It is not a positivity assertion about all tests or about a dense form core.

Here is one explicit choice. Put
\[
J=\frac{49(1+K)}{4\pi^4},\quad D=\frac{15}{\pi^3},\quad
\eta=\min\left\{1,\pi,\frac{A\pi}{4D^2}\right\},\quad c=A/2.
\]
Let \(g(t)=\texttt{EF.gammaBracket}\ t\), and let \(G\ge0\) be the maximum of zero and the constant subtracted in `exposing_archimedean_scalar_quarter`. Set
\[
C=B(G+\log2)+c\log(1/\eta)+6J
+2B\sum_{r\ge2}\frac{\Lambda(r)}{r^2}.
\tag{2}
\]
The last series converges since \(0\le\Lambda(r)\le\log r\). Every term in (2) is finite and nonnegative.

## Physical mass and all dilated comparison norms

Write \(S=\sum_N|b_N|^2\). The physical theorem gives
\[
AS\le\|f_b\|_2^2=\int_1^\infty v^{-4}|B_b(v)|^2dv\le BS.
\tag{3}
\]
Its upper-bound proof also applies to \(B_b(rv)\) for every real \(r\ge1\): multiplication by \(r\) increases the gap in each fixed harmonic layer, so its interval error constant is \(K/r\le K\). Consequently,
\[
\int_j^{j+1}|B_b(rv)|^2dv\le JS\quad(j\ge1),
\qquad
\int_1^\infty v^{-4}|B_b(rv)|^2dv\le BS.
\tag{4}
\]
These constants do not depend on the number of coefficients. No separation between different harmonic layers is required.

## Low-frequency exclusion

For real \(t\), write
\[
F_b(t)=\int_{\mathbb R}e^{itx}f_b(x)\,dx
=\int_1^\infty v^{-5/2}B_b(v)e^{-it\log v}\,dv.
\]
If \(|\omega|\ge2\pi N\) and \(|t|\le\pi M\le\pi N\), let
\(\phi(v)=\omega v-t\log v\). Then
\(|\phi'(v)|\ge|\omega|/2\) and \(|\phi''(v)|=|t|/v^2\) on \(v\ge1\). Integration by parts, first on a finite interval and then at infinity, gives
\[
\left|\int_1^\infty v^{-5/2}e^{i\phi(v)}dv\right|
\le\frac2{|\omega|}+\frac2{|\omega|}\int_1^\infty\frac52v^{-7/2}dv
+\frac{4|t|}{|\omega|^2}\int_1^\infty v^{-9/2}dv
\le\frac5{|\omega|}.
\tag{5}
\]
All integrals of the differentiated amplitude are absolutely convergent, and the boundary term at infinity vanishes.

The exact harmonic expansion is
\[
\Phi_N(v)=-\frac2{\pi^2}\sum_{k\ge1}\frac{\chi(k)}{k^2}
\bigl(\cos(2\pi k\lambda_Nv)-\cos(2\pi kNv)\bigr).
\]
Apply (5) to both exponentials in each cosine. Since \(\lambda_N\ge N\), \(|\chi(k)|\le1\), and \(\sum k^{-3}\le3/2\), the Mellin transform of a single phase obeys
\[
\left|\int_1^\infty v^{-5/2}\Phi_N(v)e^{-it\log v}dv\right|
\le D/N.
\]
Absolute harmonic convergence against the integrable amplitude justifies termwise integration. Cauchy–Schwarz on the coefficients and \(\sum_{N\ge M}N^{-2}\le2/M\) now give
\[
|F_b(t)|^2\le\frac{2D^2}{M}S\qquad(|t|\le\pi M).
\tag{6}
\]
With the exact Plancherel normalization,
\[
\frac1{2\pi}\int_{|t|\le\eta M}|F_b(t)|^2dt
\le\frac{2\eta D^2}{\pi}S\le\frac A2S.
\tag{7}
\]
Equations (3) and (7) force at least \(AS/2\) of the physical mass outside this band.

## The complete archimedean term

The corpus scalar quarter inequality, with \(r>0\), says
\[
g(t)\ge\log r-G+\tfrac14-
\frac{r^4}{4(t^2+1/4)^2}.
\tag{8}
\]
See [WeilWorkExposingRayPacketCoercivity.lean](../../../../formal/GaloisForLFunctions/RHTower/WeilWorkExposingRayPacketCoercivity.lean), together with `gammaBracket_eq_archimedeanWeilSymbol` in [WeilPoleWeightAtMostOne.lean](../../../../formal/GaloisForLFunctions/RHTower/WeilPoleWeightAtMostOne.lean).

Taking \(r=1/2\) gives \(g(t)\ge-G-\log2\) everywhere. Taking \(r=R\) gives \(g(t)\ge\log R-G\) whenever \(|t|\ge R\). If \(R=\eta M\ge1\), (3) and (7) therefore imply
\[
\frac1{2\pi}\int_{\mathbb R}|F_b(t)|^2g(t)dt
\ge\left(c\log M-B(G+\log2)-c\log(1/\eta)\right)S.
\tag{9}
\]
If \(\eta M<1\), the global lower bound and \(c\log M\le c\log(1/\eta)\) prove the same conclusion. Thus (9) holds for every \(M\ge2\).

This is an ordinary, absolutely convergent integral. The verified raw-tail logarithmic Fourier bound extends to each finite combination by the finite-sum square inequality. The global logarithmic comparison for the Gamma symbol then supplies \(\int|F_b|^2|g|<\infty\). The comparison is available through [CCMArchimedeanLogWeightEquivalence.lean](../../../../formal/GaloisForLFunctions/RHTower/CCMArchimedeanLogWeightEquivalence.lean) and the exact Gamma-weight identities used in [FactorialTailFourierEnergy.lean](../../../../formal/GaloisForLFunctions/arithmetic-positivity-theory/FactorialTailFourierEnergy.lean). Coefficient-count constants used only to establish this integrability do not enter (9).

## Entire prime and polar budgets

Define \(C_b(t)=\int f_b(x+t)\overline{f_b(x)}dx\). For \(r\ge1\), changing variables in this actual correlation gives
\[
C_b(\log r)=r^{-3/2}\int_1^\infty v^{-4}B_b(v)\overline{B_b(rv)}dv.
\]
Equations (3)–(4) give \(|C_b(t)|\le BS e^{-3|t|/2}\), using \(C_b(-t)=\overline{C_b(t)}\). The literal prime series is therefore absolutely convergent and has modulus at most
\[
2BS\sum_{r\ge2}\Lambda(r)/r^2.
\tag{10}
\]
No prime power is omitted.

The two polar readouts are
\(P_0=\int_1^\infty v^{-2}B_b(v)dv\) and
\(P_1=\int_1^\infty v^{-3}B_b(v)dv\).
Apply (4) with \(r=1\) on each unit interval and sum their weights. Since \(\sum j^{-2}\le2\) and \(\sum j^{-3}\le3/2\),
\[
|P_0|\le2\sqrt{JS},\quad |P_1|\le\tfrac32\sqrt{JS},
\qquad |2\operatorname{Re}(P_0\overline{P_1})|\le6JS.
\tag{11}
\]
This proves convergence of both polar readouts as well as their budget.

## Exact Weil identity and removal of smoothing

For completeness, the nonsmooth endpoint is handled by the actual normalized nonnegative compact mollifier \(\eta_k\), whose support lies in \([-1,1]\) and shrinks to zero. Set \(f_{b,k}=\eta_k*f_b\). Each real and imaginary part is a finite combination of the corpus's smooth exponential-decay tests: differentiating the compact convolution kernel gives the same exponential decay, with constants allowed to depend on \(b,k\).

Apply the complete decay-class explicit formula to these smooth sources. Its real version is `archPoleEnergy_eq_re_W_add_abelPrimePairing` in [WeilPrimeBlindZeroSideIdentity.lean](../../../../formal/GaloisForLFunctions/RHTower/WeilPrimeBlindZeroSideIdentity.lean). The complex version follows by polarization and conjugation: on real sources the absolutely convergent Weil pairing is real, since conjugating its summands reindexes the conjugation-invariant zero divisor. Hermitian symmetry then makes the complex diagonal the sum of the real and imaginary diagonals. The same decomposition holds for the even Gamma integral, paired prime terms, and real polar term. Thus no complex positivity premise is introduced.

Every term has a justified limit:

- **Zero side:** [FactorialTailSampling.lean](../../../../formal/GaloisForLFunctions/arithmetic-positivity-theory/FactorialTailSampling.lean) gives absolute square sampling for each raw tail, hence for each finite combination. Reflection and \(2|uv|\le|u|^2+|v|^2\) give an absolutely summable Weil majorant. The exact mollifier readout tends to one at every zero and its reflection, with uniform strip modulus at most \(e\). Dominated convergence for the series proves \(\mathcal W(f_{b,k},f_{b,k})\to\mathcal W(f_b,f_b)\).
- **Gamma side:** on the critical line the mollifier multiplier has modulus at most one and tends to one. The admitted density \(|F_b(t)|^2|g(t)|\) dominates the smoothed densities, proving convergence of the complete integral.
- **Prime side:** smoothing convolves \(C_b\) with the difference distribution of two mollifier variables. That distribution is a probability measure supported in \([-2,2]\). Hence \(|C_{b,k}(t)|\le e^3BS e^{-3|t|/2}\), an ordinary prime-series majorant independent of \(k\). Correlations converge pointwise because normalized convolution converges in \(L^2\). Dominated convergence proves convergence of the entire prime series. For the smooth tests its ordinary sum equals the Abel value by absolute convergence; alternatively, the decay-class truncation limit identifies the two.
- **Polar side:** the two fixed Mellin multipliers tend to one; both raw readouts were admitted in (11).

Passing to the limit gives the exact identity
\[
\operatorname{Re}\mathcal W(f_b,f_b)
=\frac1{2\pi}\int|F_b(t)|^2g(t)dt
+2\operatorname{Re}(P_0\overline{P_1})
-\sum_{r\ge2}\frac{\Lambda(r)}{\sqrt r}
\bigl(C_b(\log r)+C_b(-\log r)\bigr).
\]
The sum on the right is real. Combining (9)–(11) proves (1) with (2).

## Meaning and limits

The mechanism controls complete finite coefficient families: arithmetic collar separation prevents physical collapse; oscillation excludes a fixed relative low-frequency band; logarithmic Gamma growth eventually dominates uniformly bounded prime and pole costs. The proof does not obtain small normalized mixed pairings from individual diagonal bounds.

The parent interval estimate is classical [Montgomery–Vaughan](https://personal.science.psu.edu/rcv4/personal/Publications/s2-8-1-73.pdf). Related restricted Weil forms and their low spectral directions are studied by [Connes–Consani, *Spectral triples and zeta-cycles*](https://content.ems.press/assets/public/full-texts/serials/lem/69/1/11033001/online/10.4171-lem-1049.pdf). These references support the ancestry, not a novelty claim for this particular family.

The theorem remains a paper result. Its physical Riesz input, low-band estimate, complete prime/polar coefficient budgets, and all four limiting arguments require Lean certificates. It supplies no density theorem, no all-aperture sign theorem, and no unconditional RH proof. Those are separate mathematical obligations.

The proof uses the source's offset band and harmonic filter, but not the exact cubic equation for its collar. Its prime estimate also benefits from the fast envelope \(e^{3x/2}\). This identifies where the present mechanism stops explaining critical arithmetic cancellation. If that envelope is deformed to \(e^{\beta x}\), the same correlation argument costs a prime majorant proportional to \(\sum_{r\ge2}\Lambda(r)/r^{\beta+1/2}\). It is finite for \(\beta>1/2\), whereas at \(\beta=1/2\) this majorant diverges. This is a limitation of the absolute comparison, not a negative-energy theorem at the boundary. A critical theory must control the actual dilation correlations and boundary readouts there; the positive theorem above does not supply that control.
