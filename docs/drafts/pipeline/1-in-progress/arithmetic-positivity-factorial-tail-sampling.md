# Factorial correction-tail sampling and mixed-energy control

- **ID:** APT-ROOT-TAIL
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper; formalization incomplete)
- **Source:** [Foundational programme](../../../reports/arithmetic-positivity-theory/research-foundational.md), APT-01–05.
- **Statement:** For the actual factorial correction tail, the absolute zero-sampling square mass is at most a constant times \(\log(n+1)/(n+1)\), uniformly under sufficiently fine normalized smoothing.

## Exact target

Put \(N=n+1\), \(T_n=\texttt{factorialMuntzCorrectedTail}\ n\),
\(U_{n,k}=\texttt{factorialMuntzSmoothedTail}\ n\ k\), and
\(F_f(s)=\int_{\mathbb R}e^{(s-1/2)x}f(x)\,dx\).
For the actual nontrivial zeta divisor, with multiplicities,
\[
\mathcal Z(f)=\sum_\rho m_\rho|F_f(\rho)|^2.
\]
Prove unconditionally
\[
\exists C>0\ \exists N_0\ge2\ \forall n,\quad
N\ge N_0\Longrightarrow
\exists k_0\ \forall k\ge k_0,\quad
\mathcal Z(U_{n,k})\le C\frac{\log N}{N}.
\]
The range restriction is part of the quantified conclusion, not an unproved analytic premise. No RH, positive-Weil-form, zero-location, or proposed sampling hypothesis may remain in the final theorem.

## Verified starting identities

- `factorialMuntzBoundaryCorrected_sub_ramp` identifies the exact tail, including its endpoint convention.
- `factorialMuntzCorrectedTail_abs_le` gives \(|T_n(x)|\le12e^{3x/2}/\sqrt N\) on \(x\le0\), and the tail is zero on \(x>0\).
- `factorialMuntzSmoothedTail_readout` factors the smoothed readout through the normalized mollifier.
- `norm_xiWeilPolarization_le` gives an unconditional comparison by absolute square-sampling masses, without assuming Weil positivity.
- Existing complete tail energy is eventually at least \(\log N/(2048N)\); the missing mixed control must retain the actual source and completion terms.

## Competing proof mechanisms

1. A holomorphic strip sampling estimate from unconditional local zero counts, followed by weighted Fourier energy control for the actual tail.
2. Direct mixed-pairing control using the corrected-source readout \(c_n/\rho\), if absolute square sampling is unnecessarily expensive.
3. The exact resummed compact-ramp expression, if neither sampling estimate supplies the required margin.

The [sampling theorem](../3-formalized/arithmetic-positivity-factorial-log-sampling.md) proves the stronger raw-plus-smoothed budget \(C(1+\log N)/N\) for all \(n,k\), with sharp logarithmic scale in the eventual lower-bound regime. [FactorialTailSampling.lean](../../../../formal/GaloisForLFunctions/arithmetic-positivity-theory/FactorialTailSampling.lean) and [FactorialTailRelativeMargin.lean](../../../../formal/GaloisForLFunctions/arithmetic-positivity-theory/FactorialTailRelativeMargin.lean) certify the upper bound, summability of both literal zero sums, sharpness lower bound, and relative positive margin. Their dependency chain passes targeted builds, actual-file audits, and axiom inspection with only Lean's standard logical axioms. The [full ramp-limit paper proof](../2-fully-proven/arithmetic-positivity-factorial-ramp-smoothing-limit.md) controls every physical energy term under removal of smoothing. The [complete ramp–tent margin paper proof](../2-fully-proven/arithmetic-positivity-factorial-ramp-gram-margin.md) identifies the zero-side pairing with the compact physical form and derives the uniform coefficient margin.

## Falsification and positive survivor

- Check endpoint jumps before proposing a smoothing-uniform derivative bound.
- Preserve the polar term of order \(\log N/N\); the Gram correction of order \(\log^2N/N^2\) cannot absorb it.
- If the proposed budget fails, determine its sharp scale. Any suitably uniform \(o(\log^2N/N)\) budget still suffices for the first mixed-term application.
- If the absolute comparison is too costly, isolate the signed mixed pairing rather than infer that the complete ramp energy is negative.
- Classify any successful analytic sampling theorem as a bridge unless a literature audit establishes additional novelty in its arithmetic application.

## Completion gates

- [x] Exact normalization and premise audit on the actual source.
- [x] Internal and primary-literature audit of the precise sampling and regularity mechanism; verdict BRIDGE, no novelty claim.
- [x] Dependency-closed paper proof of the unconditional quantitative estimate and its sharp logarithmic scale.
- [x] Upper sampling theorem under `formal/GaloisForLFunctions/arithmetic-positivity-theory/`, wired into its umbrella.
- [x] Targeted foreground builds, actual-file audits, and axiom inspection for the upper sampling certificate; no full umbrella build.
- [ ] Formal lint after integrating the completed source modules.
- [ ] Assembled sharp lower sampling scale and relative sign margin.
- [ ] Full compact-ramp energy limit and exact ramp–tent Gram margin before claiming the family application.

The full arithmetic positivity programme remains larger than this card. A completed family estimate does not prove all-aperture RW positivity or RH.
