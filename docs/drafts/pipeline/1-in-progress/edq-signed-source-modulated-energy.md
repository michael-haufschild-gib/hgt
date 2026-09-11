# EDQ signed source: modulated energy and frequency-separation audit

- **ID:** edq-signed-source-modulated-energy
- **Stage:** 1-in-progress
- **Type:** CANDIDATE; no new arithmetic upper bound
- **Statement:** Test whether weak–strong energy control or a separated-frequency bound controls the complete physical Möbius source, including the finite-head subtraction and full later tail.

## Exact target and existing input

The chain is Euler deletion → cofinal subpower control of the complete signed physical source/current → off-line exclusion → RH.

Put \(b_n=\mathrm{bdGen}(1/n)\) and \(G_N=\sum_{1\le n\le N}\mu(n)b_n\). The sign convention for the modular approximant is the opposite one, with the same norm. The corpus already proves

\[
 \|G_N\|^2=D_N+C_N,\qquad 0\le D_N\le2\,\mathrm{harmonic}(N),
\]

where \(C_N\) retains every ordered off-diagonal Gram term. The source-level upper bound for this full expression remains open. The primitive dilation kernel's positive entries, proved in the [preceding leaf](../3-formalized/edq-primitive-interference.md), do not bound this signed quadratic form.

## Attempt 1: modulated energy with a controlled reference

The broad newest-first arXiv search "relaxation" found Agazzi–Bruno–Pasqualotto–Rigollet, [Quantitative Diffusive Limits for Singular Nonlocal Transport](https://arxiv.org/pdf/2609.11837), submitted 10 September 2026. In the proof sketch of Proposition 4.4, pages 29–30, two solutions of the same nonlocal continuity equation have a relative resolvent energy whose growth is controlled only by derivatives of the smooth reference solution. A square-completion identity controls the adverse weighted term; an integrable reference-dependent rate then gives uniform-in-time stability. The use of a common evolution equation is essential to that calculation.

**Proposed transfer.** Compare the actual arithmetic cutoff source with a simple reference in its existing physical Hilbert space, and attempt to bound the error using only reference data.

**Direct source test.** For an arbitrary fixed reference \(R\), the actual cutoff update is

\[
 G_n-G_{n-1}=\mu(n)b_n,
\]
\[
 \|G_n-R\|^2-\|G_{n-1}-R\|^2
 =\mu(n)^2\|b_n\|^2
   +2\mu(n)\operatorname{Re}\langle G_{n-1}-R,b_n\rangle .
\]

Summation retains the complete signed work term. Subtracting a reference adds the known linear pairing with \(R\); it does not eliminate the pairings with \(G_{n-1}\). The latter are exactly half of the existing off-diagonal Gram sum. There is no established common dissipative evolution that cancels them as in the paper. No integrable reference-only growth coefficient for this arithmetic update was obtained.

The corpus's compensated logarithmic recurrence also retains a compulsory correction \(B_N\) with \(\|B_N\|^2\asymp N\); see [the closed forcing theorem](../3-formalized/edq-log-prime-forcing.md). Treating the arithmetic update as unforced, or discarding that correction when changing to logarithmic time, therefore does not supply the missing estimate.

**Outcome.** No justified transfer of the paper's stability estimate. The method is not disproved for every possible arithmetic evolution; the needed source identity and bound have not been constructed. No generic relative-energy receiver was added to Lean.

## Attempt 2: separate the actual rational frequencies

**Proposed bound.** Apply the corpus's large-sieve inequality to the literal periodic residue source

\[
 F_N(k)=\sum_{d\le N}\frac{\mu(d)}d(k\bmod d).
\]

After combining equal frequencies, its finite Fourier frequencies are rational with reduced denominators at most \(N\). Include the zero frequency: the period mean is not discarded. If the coefficients are \(c_\lambda\), let

\[
 P_N=\sum_\lambda |c_\lambda|^2
     =\text{complete-period mean of }|F_N|^2 .
\]

The corpus supplies separation \(N^{-2}\) and, for any integer window of length \(T\), the bound

\[
 \sum_{k=T}^{2T-1}|F_N(k)|^2
 \le \bigl(T+A_N\bigr)P_N,\qquad
 A_N=N^2\bigl(1+\log(N^2/2+1)\bigr).
\]

A translated window only multiplies the Fourier coefficients by unit phases. For \(N\ge2\), applying this to \(T=2^jN\) and retaining every dyadic window gives the paper consequence

\[
 \sum_{k\ge N}\frac{|F_N(k)|^2}{k(k+1)}
 \le
 \left(\frac2N+\frac{4A_N}{3N^2}\right)P_N.
\]

Both geometric sums are exact: \(\sum_j(2^jN)^{-1}=2/N\) and \(\sum_j(2^jN)^{-2}=4/(3N^2)\). This bounds the complete later tail, but the bound is proportional to \(P_N\), with a logarithmic coefficient. Even a prospective sharp large-sieve constant \(T+N^2\) would leave \((2/N+4/3)P_N\).

The existing theorem \(\mathrm{variance}(N)\le P_N\), together with

\[
 \mathrm{variance}(N)\ge\frac{N}{524288\log N}
 \quad\text{eventually},
\]

shows that this upper envelope itself is not subpower. This is a limitation of this estimate, not a lower bound on the physical tail. The source can be much smaller than its complete-period average, as the corpus already proves.

**Outcome.** Removing the logarithmic loss from the large sieve would not close this EDQ gate. A useful bound must retain more of the particular signed coefficient relations than the coefficient square mass \(P_N\). No missing sharp large-sieve infrastructure was built for this unsuccessful transfer.

## Attempt 3: normalized signed-channel and entropy bounds

The broad corpus search also returned the infinite signed-channel coisometry and finite incidence Gini/Fisher energy bounds. Their source statements were checked:

- The coisometry contracts against a unit-norm signed weight and still multiplies by the external source scalar \(Z\) in its incidence factorization.
- The Gini/Fisher bound controls currents of the explicitly constructed KMS amplitudes and normalized incidence probabilities.

Neither statement identifies its bounded quantity with the complete physical source norm above, with a subpower conversion cost. The scalar, normalization, and physical-carrier comparison remain necessary. No such comparison was obtained; no entropy bound was substituted for the desired source estimate.

## Evidence and current status

Source inspection included the exact Gram decomposition, the completed coprime-column estimate, the all-gcd corrected-head estimate, the existing Fourier-truncation error, and the complete-period variance lower bound. These already closed results were not rebuilt or axiom-audited.

Deep searches used the broad queries "method signed quadratic arithmetic cancellation coboundary commutator factorization", "method modulated energy weak strong stability retain signed cross terms dissipation", and "bilinear". The first two were deadline-partial. The last completed in about 98 seconds with complete source inventory at generation 839868, but incomplete semantic coverage and mostly pending compiler metadata. All inspected candidate/source-argument records were source-only. Candidate lemmas, source arguments, proof ideas, and ingredient sets were inspected; the returned ingredient set did not contain an arithmetic upper-bound producer.

No stronger arithmetic bound emerged. The exact hard obstacle remains the signed off-diagonal work, equivalently the original source energy after the known diagonal bound. No new Lean theorem, computation, frontier-map edit, or universal-ledger entry belongs to this audit.
