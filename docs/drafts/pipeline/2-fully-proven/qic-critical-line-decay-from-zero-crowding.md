# Zero crowding forces decay of the confined trace

- **Stage:** 2-fully-proven
- **Source:** [QIC](../../../reports/rh-current-frontier-map.md#qic)

Let $F$ be a confined null state at a positive ratio and suppose the off-line ζ divisor is finite. For each $b>-4$,
$$
\sup_{\Re w\ge b,\ |w|\ge T}|(w+5)LF(w)|\longrightarrow0
\qquad(T\to\infty).
$$
In particular $|y|\,|LF(iy)|\to0$ at both ends of the critical line. The mean-square wall trace vanishes at every such crossing:
$$
\frac1h\int_{-h}^0 F(u)^2\,du\longrightarrow0\qquad(h\downarrow0).
$$

**Proof.** Beyond the finitely many exceptional heights, the [strip count](../../../../formal/GaloisForLFunctions/SquareRootThreshold/AStripGivesLittlewoodWindows.lean#L632) at depth zero gives at least $c_h\log y$ critical-line copies within any fixed radius $h>0$. The [half-plane bound](../3-formalized/qic-boundary-power-of-a-confined-state.md) and Cauchy's estimate give $H(w)=(w+5)LF(w)$ a bounded derivative on the imaginary axis. A peak of fixed height would persist throughout a fixed interval, contradicting the [uniform bound on rescaled sample mass](../3-formalized/qic-poisson-bound-on-the-critical-line-traces.md) as its copy count grows.

On $\Re w\ge0$, the multiplier $w/(r+w)$ suppresses the bounded part of the boundary as $r\to\infty$. The half-plane maximum principle propagates boundary decay to infinity in every direction. Vertical translates of $H$ form a locally bounded holomorphic family on $\Re w>-4$. Vitali's theorem propagates their zero limit from $\Re w>0$ to each interior line, where the same maximum principle applies.

For $x$ large, $|LF(x+iy)|^2\le\varepsilon^2/(x^2+y^2)$. Vertical Plancherel and the Cauchy integral give $2x\int_0^\infty e^{-2xv}F(-v)^2\,dv\le\varepsilon^2$. At $x=1/h$ the weight is at least $e^{-2}$ on $(0,h)$.
