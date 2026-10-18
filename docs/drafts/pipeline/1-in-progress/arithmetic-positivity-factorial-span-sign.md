# Signed coercivity on the high-scale factorial tail span

- **ID:** APT-ROOT-SPAN-SIGN
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** [Foundational programme](../../../reports/arithmetic-positivity-theory/research-foundational.md), APT-06–07.
- **Audit verdict:** SURVIVES PRELIMINARY ATTACK as a source-specific conjecture. Its proposed mechanism is a classical coercivity argument; novelty is not established.

## Exact target

Use the literal phases \(\Phi_N\), amplitudes \(a_{N-1}>0\), and tails from the [finite-window coercivity paper](../2-fully-proven/arithmetic-positivity-factorial-window-coercivity.md). For a finitely supported complex coefficient family \(b\) on positive integers, set
\[
f_b(x)=\sum_{N\ge1}\frac{b_N}{a_{N-1}}T_{N-1}(x)
=e^{3x/2}\sum_Nb_N\Phi_N(e^{-x})\mathbf1_{x\le0}.
\]
Let \(\mathcal W\) be the literal zeta-zero Weil pairing, with its usual reflection and multiplicities, not the absolute square-sampling form.

**Conjecture.** There exist constants \(c>0\) and \(C\ge0\) such that for every integer \(M\ge2\) and every finitely supported \(b\) supported on \(N\ge M\),
\[
\operatorname{Re}\mathcal W(f_b,f_b)
\ge(c\log M-C)\sum_N|b_N|^2.
\tag{S}
\]
The zero pairing must be proved absolutely convergent. The existing raw-tail sampling theorem supplies summability for finite sums once the readout linearity is admitted; this is not an assumption in (S).

An eventual positive coefficient in (S) would control all finite cross-scale Gram matrices in the indicated tail span. It would not prove that this span is dense in the form domain, nor the universal RW criterion. The source restriction is essential.

## Concrete mechanism to test

Put \(B_b(v)=\sum_Nb_N\Phi_N(v)\). The finite-window theorem supplies physical coercivity and uniform interval upper bounds for \(B_b\). The same upper-bound proof applies to \(B_b(rv)\) for every \(r\ge1\), because each harmonic gap increases by \(r\). This suggests three quantitative steps.

1. **Bound the entire prime contribution on coefficient space.** The unsmoothed correlation has the exact scaling identity
   \[
   C_b(\log r)=r^{-3/2}\int_1^\infty v^{-4}B_b(v)\overline{B_b(rv)}\,dv,
   \]
   for the convention \(C_b(t)=\int f_b(x+t)\overline{f_b(x)}\,dx\). Uniform weighted square bounds and Cauchy–Schwarz then give \(|C_b(\log r)|\le C_1r^{-3/2}\|b\|_2^2\). With the literal prime-power weight \(\Lambda(r)/\sqrt r\), the full absolute prime cost is bounded by a constant times \(\sum_{r\ge2}\Lambda(r)/r^2<\infty\). Check all normalization factors against the actual explicit formula.
2. **Bound the polar contribution independently of the number of coefficients.** The two polar readouts become \(\int_1^\infty v^{-3}B_b(v)\,dv\) and \(\int_1^\infty v^{-2}B_b(v)\,dv\). Apply the uniform unit-interval square bound, Cauchy–Schwarz on each unit interval, and the convergent sums of interval weights. This avoids an invalid global Cauchy–Schwarz estimate in the single weight \(v^{-4}\).
3. **Force logarithmic archimedean energy.** For \(|t|\le\pi M\), each Mellin harmonic has phase \(\pm2\pi k\nu v-t\log v\), with \(\nu\ge M\), and no stationary point on \(v\ge1\). An admitted integration-by-parts estimate should give \(|F_{f_b}(1/2+it)|\le C_2\sum_N|b_N|/N\le C_3M^{-1/2}\|b\|_2\). A sufficiently small fixed band \(|t|\le\eta M\) then contains less than half the physical mass furnished by the Riesz lower bound. The positive logarithmic Gamma weight supplies \((c\log M-C_4)\|b\|_2^2\).

Each proposed constant must be uniform in the number, size, and spacing of the source indices. No pointwise sum of coefficient magnitudes may survive as the final norm.

## First unresolved step and falsifiers

**[OPEN CORE]** Establish the admitted low-frequency Mellin bound and the exact full-Weil transport for arbitrary finite source combinations, retaining the endpoint jump, all prime powers, and both polar readouts. The three estimates above are a proof route, not a proved signed theorem.

- A hidden coefficient-count loss in the dilated interval or low-frequency bound would defeat the uniform span claim.
- The Gamma lower bound must use the actual Fourier normalization and comparison weight, including its bounded negative part if the complete archimedean symbol is used.
- Smoothing must preserve the signed conclusion through a justified limit. Fixed-zero convergence alone is insufficient; use the certified absolute square-sampling majorant or a complete physical-energy limit.
- Coercivity in ordinary physical \(L^2\) is not already logarithmic coercivity. Supply the quantitative low-band exclusion.
- Compare against existing individual-tail logarithmic growth and restricted Weil positivity before assigning novelty. A general parent theorem may classify (S) as BRIDGE even if this source application is new to the corpus.

## Completion gates

- [x] Exact source, coefficient norm, scale range, and desired signed conclusion specified.
- [x] Dependency-closed physical Riesz proof recorded separately; its Lean certificate remains pending.
- [ ] Internal and external audit of the exact span statement and parent coercivity mechanisms.
- [ ] Complete low-frequency estimate, prime/polar budgets, and full-Weil transport on paper.
- [ ] Unconditional Lean certificate under the arithmetic positivity umbrella, actual-file audit, axiom inspection, and formal lint.
- [ ] Identify the strongest further extension or obstruction, without inferring density or RH from a restricted positive span.
