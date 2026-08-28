# Route T2 common-mode exponent triage

Date: 2026-08-29  
Status: computation complete; diagnostic only; forbidden as input to Lean proofs

## Verdict

**FALSIFIED — current direct finite-shell summation.** The present common-mode theorem interfaces do not imply the required gap-moment exponent, even after replacing the corpus gap range by the stronger published prime-gap exponent $13/25$. The claim that only finite shell summation remains is therefore false for the audited interfaces.

**FALSIFIED — generic local repairs.** Unfreezing the buffered paired-kernel gain, welding in the physical-slice estimate, or imposing reciprocal outer localization individually does not close the exponent gap. Generic $L^2/L^4$ rearrangement is also blocked by an explicit interval-cell Fourier packet with cubic additive energy.

**POSITIVE SURVIVOR — sharpened T2 research target.** A viable successor needs both:

1. cancellation-preserving target-reciprocal localization $A \lesssim x/h$, equivalently shell and gap exponents $s+g\leq1$; and
2. a genuinely arithmetic selected-cell/bad-set estimate on the paired low shells, not another generic $L^2/L^4$ estimate.

In the exponent model, extending the existing selected-cell law $m(s)=\min(1,s+\nu)$ to all shells and combining it with $s+g\leq1$ gives $g+m(s)\leq1+\nu<3/2$. This is a necessary-mechanism isolation, not a proof that such a theorem exists.

## Exact audit

Corpus definitions give

\[
\delta=\frac1{3\cdot2^{47}\cdot380}
=\frac1{160440736725073920},\qquad
\nu=\frac12-\frac\delta2,
\]

\[
\theta=\frac34-\frac\delta2,qquad
\rho=\frac{\delta}{2+3\delta},\qquad
s_{\rm buffer}=\frac1{\mu_{\rm buffer}}\approx\frac14.
\]

Here $s$ is the shell exponent $A=x^s$, $g$ is the gap exponent $h=x^g$, $m(s)$ is the bad-measure exponent, and the gap-moment exponent is $E=g+m(s)$.

- Current buffered paired-shell bound has raw exponent
  $m_{\rm fixed}(s)=1+s(1-2\rho)>1$ for every $s>0$. After intersecting with the physical block, only the trivial cap $m\leq1$ remains. At published $g=13/25$, $E-3/2=1/50$. At corpus $g=71/100$, the loss is $21/100$.
- Retaining the unfrozen small-kernel gain gives
  $m_{\rm unfrozen}(s)=2\theta-1+3s$. It reaches the trivial cap near $s=1/6$, so it still supplies no saving on upper paired shells.
- Current forced-second bound gives $m_{\rm selected}(s)=\min(1,s+\nu)$. At $s=5/8$ and the easiest handled gap $g=31/80$, it misses the route target $1+\nu$ by exactly $1/80$, and misses $3/2$ by $1/80-\delta/2>0$.
- Current packet interfaces leave the nonempty shell interval
  $(s_{\rm buffer},5/11)$, of width approximately $0.204545$, without a common-mode packet measure theorem. A scalar exponent dichotomy does not fill this packet-level gap.
- A $K$-th order absolute tail at reciprocal exponent $49/80$ has outer exponent $(49/80)(1+1/K)$. No finite $K$ reaches the exact $1+\nu$ target. Mere strict sub-$3/2$ requires
  $K>49/(40\delta)=196539902488215552$. This is not a credible repair route.

Relevant corpus declarations were located with `scripts/formal_tools.py research`:

- `volume_routeTCommonModeFixedTargetNaturalShellBadSet_le_bufferedPower`
- `eventually_routeT_fixedWidth_selectorThreshold_le_commonModeNaturalCellDefectThreshold`
- `eventually_volume_routeT_fixedWidth_canonicalNaturalShell_full_forcedSecond`
- `routeTPairedKernelBufferedMu`, `routeTPhysicalSliceBufferedReserve`, `routeTPairedKernelDecayReserve`
- `routeTGapMomentNu`, `routeTGapMomentExponent_lt_three_halves`
- `routeTPrimeGapPacketBase`, `routeTPrimeGapPacketWidth`

## Adversarial Fourier packet

For an arithmetic progression of $n$ cells in a sufficiently large cyclic group, the exact additive energy is

\[
E(S)=\frac{2n^3+n}{3}\sim\frac23n^3.
\]

Its character packet has peak $n$, second moment $n$, and fourth moment $E(S)$. Thus the interval-cell $L^4/R^\ast$ branch genuinely permits cubic fourth moment; no generic moment rearrangement can create the needed power saving. Any successful low-shell estimate must use additional arithmetic structure that excludes or defeats this packet.

Checks:

- Exhaustive search on \(\mathbb Z/31\mathbb Z\), |S|=8: all 2,035,800 translation-normalized subsets tested; maximum energy 344, exactly the progression value; 120 normalized maximizers.
- Parallel local search on \(\mathbb Z/521\mathbb Z\), |S|=64: best energy 172,484, or 98.684% of progression energy 174,784.
- Structured progression table through $n=16384$ confirms $E(S)/n^3\to2/3$.

Finite search is corroboration only. The explicit progression identity is the mathematical obstruction.

## Computed model comparison

Each model used 8,192 gap samples and shell mesh denominator 16,384. A full model/range pair contained 67,117,056 points before reciprocal-cut filtering.

| Model | Maximum, published range $31/80\leq g\leq13/25$ | Fraction $E\geq3/2$ | Consequence |
|---|---:|---:|---|
| Current interfaces | 1.52 | 14.0300% | fails |
| Unfrozen paired kernel | 1.52 | 12.8715% | fails |
| Physical-slice weld | 1.52 | 6.6955% | fails |
| Reciprocal cut + physical-slice weld | 1.52 | 3.1076% | fails |
| Reciprocal cut + all-shell selected-cell law | <1.5 on grid | 0% | only surviving model; exact bound is $1+\nu<3/2$ |

Grid values locate failures; exact rational inequalities above determine verdicts.

## Reproduction and files

Remote host had 128 CPUs and 755 GiB RAM; Python 3.12.3 and NumPy 2.1.2. BLAS/OpenMP thread counts were pinned to one per process to avoid oversubscription. Run used 128 worker processes and completed in 2.72 seconds.

```bash
python3 run_experiments.py \
  --output results \
  --workers 128 \
  --grid-denominator 16384 \
  --anneal-steps 2500

python3 verify_results.py results.json
```

- `results.json`: full exact-rational, grid, exhaustive, and local-search output
- `model_summary.csv`: compact exponent-model results
- `fourier_packets.csv`: exact structured-packet moments
- `run-output.txt`: remote run summary
- `run_experiments.py`: multicore experiment
- `verify_results.py`: independent exact/result consistency checks

The verifier reports: `verified: exact identities, route losses, grid verdicts, Fourier countermodels`.

## Literature boundary

The external comparison uses Runbo Li's published prime-in-short-interval exponent $0.52=13/25$, which is already strong enough to show that the obstruction is not an artifact of the corpus's weaker $71/100$ gap range: [arXiv:2308.04458](https://arxiv.org/abs/2308.04458). Guth–Maynard's related large-values/short-interval advance was also audited: [arXiv:2405.20552](https://arxiv.org/abs/2405.20552).

## Scope

No computation result was, or may be, imported into a Lean proof. No Lean source or umbrella was changed. The read-only frontier map was not modified.
