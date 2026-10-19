# Full signed coercivity on the high-scale factorial tail span

- **ID:** APT-ROOT-SPAN-COERCIVITY
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
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

The physical Riesz input (`FactorialTailWindowRieszCoercivity.lean`), the envelope-critical prime majorant and polar readout budgets (`EnvelopeCriticalPrimeTransitionAndDilationGain.lean`), the nonstationary Mellin low-band estimate (`nonstationary_mellin_majorant_le_five_div_abs` and `low_band_plancherel_energy_le_half_arch`), and the high-scale archimedean-to-Weil coercivity assembly (`high_scale_archimedean_log_coercivity` and `high_scale_span_weil_coercivity_bound` in [NonstationaryMellinLowFrequencyExclusion.lean](../../../../formal/GaloisForLFunctions/arithmetic-positivity-theory/NonstationaryMellinLowFrequencyExclusion.lean)) are certified in Lean. The theorem supplies no density theorem, no all-aperture sign theorem, and no unconditional RH proof. Those are separate mathematical obligations.

The proof uses the source's offset band and harmonic filter, but not the exact cubic equation for its collar. Its prime estimate also benefits from the fast envelope \(e^{3x/2}\). This identifies where the present mechanism stops explaining critical arithmetic cancellation. If that envelope is deformed to \(e^{\beta x}\), the same correlation argument costs a prime majorant proportional to \(\sum_{r\ge2}\Lambda(r)/r^{\beta+1/2}\). It is finite for \(\beta>1/2\), whereas at \(\beta=1/2\) this majorant diverges. This is a limitation of the absolute comparison, not a negative-energy theorem at the boundary. A critical theory must control the actual dilation correlations and boundary readouts there; the positive theorem above does not supply that control.

## Lean certificate

All statements are unconditional and depend only on `propext`, `Classical.choice`, `Quot.sound`. Indexing: Lean writes `n = N - 1`, so the family is `f_b = ∑_{n ∈ S} (b_n / a_n) T_n` with `M ≤ n + 1`, and `B_b = ∑_{n ∈ S} b_n Φ_{n+1}` (`factorialPhaseCombination S b`). Constants: `A = factorialWeightedPhaseLower`, `B = factorialWeightedPhaseUpper`, `J = factorialUnitIntervalUpper`, `D = factorialLowFreqConstant`, `η = lowFreqRelativeCutoff A D`, `G = factorialSpanGammaOffset = max 0 ExposingRayPrimitive.coercivityConst`, and `∑_{r ≥ 2} Λ(r)/r² = canonicalPrimeMajorantConstant`.

- (1)–(2): `factorialTailSpan_re_W_coercivity` gives `c = A/2`, `C = factorialSpanWeilOffset = factorialSpanCoercivityOffset A B G J D`, absolute summability of the Weil summands, and the bound. `factorialSpanWeilOffset_nonneg` proves `C ≥ 0`. The real-coefficient case is `factorialTailCombination_re_W_coercivity`. Both are in [FactorialTailSpanWeilCoercivity.lean](../../../../formal/GaloisForLFunctions/arithmetic-positivity-theory/FactorialTailSpanWeilCoercivity.lean).
- (3)–(4): `integral_norm_sq_sum_factorialMuntzCorrectedTail`, `factorialPhaseCombination_weighted_lower`, `factorialPhaseCombination_weighted_upper` (`r ≥ 1`) and `factorialPhaseCombination_dilated_window_upper` (gap constant `K/r ≤ K`), in [FactorialPhaseWindowAndPhysicalRieszBounds.lean](../../../../formal/GaloisForLFunctions/arithmetic-positivity-theory/FactorialPhaseWindowAndPhysicalRieszBounds.lean).
- (5): `norm_integral_Ioi_one_rpow_mul_cexp_phase_le` and its cosine form `norm_integral_Ioi_one_rpow_mul_cos_mul_cexp_le`, in [RpowMellinNonstationaryPhaseBound.lean](../../../../formal/GaloisForLFunctions/arithmetic-positivity-theory/RpowMellinNonstationaryPhaseBound.lean).
- Single-phase bound `D/N` and (6): `paperFT_factorialSpanTest` (Mellin readout), `norm_integral_factorialHarmonicLayer_mellinKernel_le`, `norm_paperFT_factorialSpanTest_le`, `norm_sq_paperFT_factorialSpanTest_le`, in [FactorialSpanTestMellinLowFrequency.lean](../../../../formal/GaloisForLFunctions/arithmetic-positivity-theory/FactorialSpanTestMellinLowFrequency.lean).
- (7): `factorialTailCombination_lowBand_energy_le` (scalar step `low_band_plancherel_energy_le_half_arch`).
- (8): `gammaBracket_quarter_lower`, `gammaBracket_ge_neg_offset`, `gammaBracket_ge_log_of_le_abs`, in [FactorialSpanTestPolarPrimeGammaBudgets.lean](../../../../formal/GaloisForLFunctions/arithmetic-positivity-theory/FactorialSpanTestPolarPrimeGammaBudgets.lean).
- (9): `factorialTailCombination_archGammaEnergy_lower`, through `archGammaEnergy_split_lower` and `high_scale_archimedean_log_coercivity`. Absolute convergence of the raw Gamma integral is `integrable_norm_sq_paperFT_factorialTailCombination_mul_gammaBracket`. It rests on the raw-tail logarithmic Fourier bound (`integrable_norm_sq_paperFT_tail_mul_log`, from `factorialTailLogFourier_integrable`), the finite-sum square inequality, and `EvenSector.abs_gammaBracket_le_log`.
- (10): `abs_crossCorr_factorialTailCombination_le_weighted` (`|C_b(y)| ≤ BS e^{-3|y|/2}`), `norm_atomTerm_factorialTailCombination_le`, `summable_norm_atomTerm_factorialTailCombination` and `abs_atomPairing_factorialTailCombination_le`. The Mellin-form correlation and prime series are `factorialSpanCorrelation`, `norm_factorialSpanCorrelation_le` and `abs_tsum_factorialSpanPrimeAtom_le`.
- (11): `paperFT_factorialSpanTest_I_div_two` and `paperFT_factorialSpanTest_neg_I_div_two` identify `F_b(±i/2)` with `P₀ = factorialSpanPolarZero` and `P₁ = factorialSpanPolarOne`. The bounds are `norm_factorialSpanPolarZero_le` (`2√(JS)`), `norm_factorialSpanPolarOne_le` (`(3/2)√(JS)`), `abs_factorialSpanPolarTerm_le` and `factorialSpanTest_polar_budget` (`6JS`).
- Smoothing and limits, in [FactorialTailCombinationSmoothingChannels.lean](../../../../formal/GaloisForLFunctions/arithmetic-positivity-theory/FactorialTailCombinationSmoothingChannels.lean):
  - smooth decay tests: `factorialTailCombinationSmoothed_expDecayTest`;
  - smoothed explicit formula: `archPoleEnergy_factorialTailCombinationSmoothed`;
  - zero side: `tendsto_W_factorialTailCombinationSmoothed`, with `factorialTailCombination_zeroSquare_summable` and `factorialMuntzKernelReadout_tendsto`;
  - polar side: `tendsto_paperFT_factorialTailCombinationSmoothed` at `s = 0, 1`;
  - prime side: `tendsto_crossCorr_factorialTailCombinationSmoothed` and `tendsto_atomPairing_factorialTailCombinationSmoothed`.
- Gamma side and the exact identity, in [FactorialTailCombinationExplicitFormula.lean](../../../../formal/GaloisForLFunctions/arithmetic-positivity-theory/FactorialTailCombinationExplicitFormula.lean): `tendsto_archGammaEnergy_factorialTailCombinationSmoothed` and the raw real identity `archPoleEnergy_factorialTailCombination`.
- Reality and Hermitian symmetry: `zetaZeroConfig_W_ofReal_conj` (conjugation reindexing via `zetaZeroConjPerm`) and `zetaZeroConfig_W_swap` (reflection reindexing).
- Complex splitting: `zetaZeroConfig_W_ofReal_add_I_mul` (`W(u+iv,u+iv) = W(u,u) + W(v,v)`).
- Complex exact identity: `factorialTailSpan_exact_weil_identity`, with the Hermitian correlation `hermitianCrossCorr`, the complex prime series `complexAtomPairing` (real, by `complexAtomPairing_factorialTailCombination`) and the integrable complex Gamma density.

**Proof route in Lean.** Two steps differ from the paper text. Each uses an equally valid majorant.
- **Gamma channel:** the mollifier readout is bounded by its strip bound `‖κ_k‖ ≤ e` (`factorialMuntzKernelReadout_bound`), not by `1`.
- **Prime channel:** dominated convergence uses the majorant `factorialTailCombinationCorrConstant · e^{-5|y|/4}`. It depends on the family but not on `k`.

The complex theorem (1) follows from the real one by splitting `b_n / a_n` into real and imaginary parts, since `∑‖b_n‖² = ∑‖Re(b_n/a_n) a_n‖² + ∑‖Im(b_n/a_n) a_n‖²`.

## Log
- 2026-10-18 — moved 2-fully-proven → 3-formalized after the unconditional Lean certificate above.
