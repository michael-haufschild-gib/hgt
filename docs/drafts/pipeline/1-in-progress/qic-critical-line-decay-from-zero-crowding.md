# Critical-line decay from zero crowding

- **Stage:** 1-in-progress
- **Source:** [QIC](../../../reports/rh-current-frontier-map.md#qic)

**Target.** For every positive-ratio confined null state with finitely many off-line ζ zeros, prove $|y|\,|LF(iy)|\to0$ as $|y|\to\infty$.

**Arithmetic input.** Beyond the largest exceptional height, the ζ divisor lies in a strip of width zero. For each fixed $h>0$, setting $d=0$ and taking fixed $\ell\ge\max(1,D/h)$ in the [strip count](../../../../formal/GaloisForLFunctions/SquareRootThreshold/AStripGivesLittlewoodWindows.lean#L632) gives a lower bound growing proportionally to $\log y$ for the number of critical-line copies within $h$ of $y$.

**Analytic step.** The [half-plane bound](../3-formalized/qic-boundary-power-of-a-confined-state.md) makes $H(w)=(w+5)LF(w)$ uniformly Lipschitz on the imaginary axis by Cauchy's estimate. If $|H(iy)|\ge\varepsilon$, then $|H(i\gamma)|\ge\varepsilon/2$ throughout an interval of radius depending only on $\varepsilon$ and the state. The [unit-window mass bound](../3-formalized/qic-poisson-bound-on-the-critical-line-traces.md) bounds the sum of $|H(i\gamma)|^2$ on this interval independently of $y$. Formalization must identify the copies in both counts with multiplicity.
