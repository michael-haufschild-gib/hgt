# Arithmetic positivity: primary research ledger

This ledger records mathematical facts, failed mechanisms, and precise unresolved questions. It does not replace the [research programme](research-foundational.md) or its individual proof cards.

## Source facts

1. **The correction is literal.** `factorialMuntzBoundaryCorrected_sub_ramp` identifies the corrected source minus the compact ramp with `factorialMuntzCorrectedTail`, including the nonpositive endpoint convention. Source: [FactorialMuntzUniformTail.lean](../../../formal/GaloisForLFunctions/BiScaleUncertainty/FactorialMuntzUniformTail.lean).
2. **The collar costs no additional scale power.** The same module proves \(|T_n(x)|\le12e^{3x/2}/\sqrt{n+1}\) for \(x\le0\), with \(T_n=0\) for \(x>0\). Readouts are admitted for \(\operatorname{Re}s>-1\). This supplies value control on a wider strip, not a bound on the complete zero-sampling sum.
3. **Smoothing retains the actual tail.** [FactorialMuntzTailSmoothing.lean](../../../formal/GaloisForLFunctions/BiScaleUncertainty/FactorialMuntzTailSmoothing.lean) gives exact convolution readout factorization and a value envelope uniform in the smoothing index. Its smooth-test derivative constants are not asserted uniform in that index.
4. **Mixed comparison is already unconditional.** [XiWeilLineConjHilbert.lean](../../../formal/GaloisForLFunctions/RHTower/XiWeilLineConjHilbert.lean) supplies Cauchy–Schwarz using the independent absolute square-sampling form. This does not assert positivity of the signed Weil form.
5. **The arithmetic scale has a concrete translation certificate.** The new field's [phase](../../../formal/GaloisForLFunctions/arithmetic-positivity-theory/FactorialTailPhase.lean), [weighted mass](../../../formal/GaloisForLFunctions/arithmetic-positivity-theory/FactorialTailWeightedMass.lean), [translation](../../../formal/GaloisForLFunctions/arithmetic-positivity-theory/FactorialTailTranslation.lean), and [logarithmic integration](../../../formal/GaloisForLFunctions/arithmetic-positivity-theory/FactorialTailLogTranslation.lean) modules prove the exact identity, the uniform mass bound \(96/N\), \(D(h)\le C\min\{1/N,h\}\), and \(\int_0^1D(h)\,dh/h\le C(1+\log N)/N\). The chosen translation constant is \(C=4050e^6+25344\); optimizing that numerical constant is unnecessary for the scale argument.
6. **The corrected-source zero vectors occupy at most one dimension.** The exact readout \(F_{H_n}(\rho)=c_n/\rho\) gives \(F_{\sum_n a_nH_n}(\rho)=(\sum_n a_nc_n)/\rho\) for every finite coefficient family. For a common smoothing index, all vectors acquire the same kernel multiplier and still span at most one dimension. If \(\sum_n a_nc_n=0\), the smoothed compact-ramp combination and the negative smoothed-tail combination have identical zero readouts. This exact reduction exposes the cross-scale tail Gram problem; positivity on the corrected-source family alone cannot supply a dense positive test family. The claim concerns the raw family or a fixed common smoothing index, not an arbitrary mixture of smoothing indices.

## Boundaries

- A bound at every fixed zero does not bound a sum over the full zero divisor. Uniformity in height and summability must be proved.
- A smoothing-uniform value bound does not supply a smoothing-uniform derivative bound. Endpoint jumps are a specific obstruction to an unqualified \(H^1\) argument.
- The absolute square-sampling budget \(O(\log N/N)\) is sufficient for the factorial mixed application but may be stronger than necessary. A suitably uniform \(o(\log^2N/N)\) budget would also make the mixed term lower order than the known positive tail diagonal.

## Logarithmic energy mechanism

The [sampling paper proof](../../drafts/pipeline/2-fully-proven/arithmetic-positivity-factorial-log-sampling.md) establishes the following source-specific statements. Their complete Lean formalization is a separate obligation.

- The actual tail is \(a_ne^{3x/2}R_n(Ne^{-x})\mathbf1_{x\le0}\), with \(a_n\le15/\sqrt N\), \(|R_n|\le25/32\), and Lipschitz constant at most \(14\) on nonnegative arguments.
- For every Mellin weight \(\sigma\in[-1/4,5/4]\), its weighted translation square energy satisfies \(D_{n,\sigma}(h)\le C\min\{N^{-1},h\}\) for \(0<h\le1\). This retains the endpoint jump.
- Integrating against \(dh/h\) gives \(O((1+\log N)/N)\). Plancherel converts this to logarithmic Fourier energy; local zero counts and the holomorphic disk mean-value inequality convert that to absolute square sampling.
- Consequently \(\mathcal Z(T_n)+\mathcal Z(U_{n,k})\le C(1+\log N)/N\) for every \(n,k\). The smoothing threshold in the proposed upper bound is unnecessary.
- Existing positive tail energy forces a matching lower bound for fine smoothing. The sampling mass and signed tail energy both have sharp order \(\log N/N\), and their ratio to physical square mass has order \(\log N\). An \(O(1/N)\) spectral budget for this family is false.
- The same two-sided bounds give an absolute \(\delta>0\) with \(\operatorname{Re}\mathcal W(U_{n,k},U_{n,k})\ge\delta\mathcal Z(U_{n,k})\) eventually in \(n\), then in \(k\). This is a relative sign margin for actual individual sources. It does not control all cross-scale Gram matrices or imply positivity of their linear span.

## Rejected dependencies

- `norm_quantizationCompletion_le_of_le` in `WeilWorkQuantizationRadialGrowth.lean` assumes `WeilPositiveFull`. It cannot supply an independent positivity proof here. The independent absolute zero-sampling comparison remains usable.
- The existing public disk mean-square theorems in `HolomorphicBallMeanSq.lean` and `HolomorphicBallL2Submean.lean` assume an entire function. The actual tail readout is holomorphic on a half-plane; applying those declarations directly would strengthen the domain without proof. The local disk argument is valid on paper and must be implemented with local holomorphy or a justified localization.

## Available analytic transport

- [GammaHardyPhaseRateLevyKhintchine.lean](../../../formal/GaloisForLFunctions/RHTower/GammaHardyPhaseRateLevyKhintchine.lean) proves the exact extended-integral identity between weighted translation squares and the nonnegative archimedean Fourier excess for every admitted \(L^1\cap L^2\) source. [CCMArchimedeanLogWeightEquivalence.lean](../../../formal/GaloisForLFunctions/RHTower/CCMArchimedeanLogWeightEquivalence.lean) compares that form weight globally with \(1+\log^+|\xi|\). The verified [actual-tail Gamma jump module](../../../formal/GaloisForLFunctions/arithmetic-positivity-theory/FactorialTailLevyEnergy.lean) proves integrability and the bound \((C+384A)(1+\log N)/N\), where \(A=\int_1^\infty\omega(h)\,dh\) is finite and independent of the source scale. Near zero, \(\omega(h)\le1/h\); beyond unit displacement, the square-mass bound controls the cost.
- [FactorialTailFourierEnergy.lean](../../../formal/GaloisForLFunctions/arithmetic-positivity-theory/FactorialTailFourierEnergy.lean) admits the actual complexified weighted source to \(L^1\cap L^2\), identifies its positive Gamma integral with physical mass plus jump energy, and proves the logarithmic Fourier bound with constant \(C_\Gamma(96+C+384A)\). Integrability of the spectral density is proved before its integral is bounded. The constant is uniform over the whole enlarged Mellin strip; sampling the actual zeros is still a separate step.
- `hasSum_circleAverage_normSq_diskCoeffOn` in [HardyDiskSpace.lean](../../../formal/GaloisForLFunctions/HTGeometry/HardyDiskSpace.lean) already assumes only holomorphy on a ball. Its zeroth coefficient supplies the local circle estimate. Localizing the polar-integration proof is therefore sufficient; a new entire-function extension is unnecessary. The raw tail's half-plane holomorphy can also be obtained from the exact corrected-minus-ramp readout: the corrected readout is analytic on \(\operatorname{Re}s>-1\), and the compact ramp transform is entire.
- [XiGlobalPacketDensity.lean](../../../formal/GaloisForLFunctions/RHTower/XiGlobalPacketDensity.lean) supplies `exists_xiUnitHeightPacket_global_log_bound` for every real height and every multiplicity copy, including bounded and negative heights. [WeilDeletionZeroSide.lean](../../../formal/GaloisForLFunctions/RHTower/WeilDeletionZeroSide.lean) supplies `toSupport`, its injectivity, `zeroMult_eq_xiSupportMultiplicity`, and `carrier_tsum_le`. These are the exact dictionary between the literal zeta carrier and the Xi-copy count; that dictionary need not be reconstructed from zero locations alone.
- `CHMDDoobGraph.smooth_difference_L2_le` contracts each translation square under the literal nonnegative normalized mollifier. It does not assert contraction of the signed full Weil form.
- The [compact-ramp smoothing paper proof](../../drafts/pipeline/2-fully-proven/arithmetic-positivity-factorial-ramp-smoothing-limit.md) uses that contraction to dominate the singular jump integral. Common compact support separately controls the finite prime sum and polar integral. It proves full physical-energy continuity on paper, with a Lean certificate and the zero-side/physical-side application still required.

## Precise unresolved question

The [complete ramp–tent margin paper proof](../../drafts/pipeline/2-fully-proven/arithmetic-positivity-factorial-ramp-gram-margin.md) derives \(\mathcal Z(H_{n,k})\le C_H/N\) from the literal readout \(1/(2\sqrt N\rho)\). Mixed costs are therefore \(O(\sqrt{\log N}/N)\), below the positive tail diagonal. The compact mixed explicit formula identifies the smoothed ramp's zero-side and physical energies. The full-form smoothing limit and existing Gram estimate then give \(Q_n(c,d)\ge c^2\log N/(8192N)+Nd^2/2\) eventually. This is a paper result awaiting the assembled Lean certificate.

Complete the Lean certificates of sampling, full-form smoothing, and this actual-source margin. The global all-test/all-aperture sign mechanism and the cross-scale Gram problem remain unresolved.

The [scoped proof card](../../drafts/pipeline/1-in-progress/arithmetic-positivity-factorial-tail-sampling.md) states the quantifiers, competing mechanisms, and completion gates. The wider global sign problem remains separate.
