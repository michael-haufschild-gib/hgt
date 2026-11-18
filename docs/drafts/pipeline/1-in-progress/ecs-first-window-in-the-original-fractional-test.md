# Absolute mass of the signed first window in the original test

Write $W(t)$ for the oriented signed sum on $(e^t,e^t+\sqrt{e^t t}]$ with the critical state. The target is
\[
 \sup_{D\ \mathrm{measurable}}\int_D |W(t)|K(T-t)\,dt\longrightarrow0.
\]
This would remove the first window even on the exceptional centers when evaluating the original signed test. Absolute values here enclose the entire signed integer sum. The adverse mass of individual coefficients stays positive at this width.

**Octave mean.** The critical-wall reading differs from $\gamma[(\psi(x+h)-\psi(x))/h-1]$ by $o(1)$, with $h=\sqrt{x\log x}$. The linear short-interval sieve gives a uniform bound $M$ for $|W(\log x)|$ at large $x$. On bounded time intervals the row ranges over finitely many integers with continuous coefficients. For $t\le0$ its width vanishes. The same $M$ can therefore be enlarged to bound $W$ globally. For each $\delta>0$, the [joint exceptional set](../3-formalized/ecs-two-sided-prime-prefixes-at-the-wall.md) has length $o(X)$ in $[X,2X]$. Thus $X^{-1}\int_X^{2X}|W(\log u)|\,du\le\delta+o(1)$. As $du/u\le du/X$, the integral of $|W|$ on $(T,T+\log 2]$ tends to zero.

**Original test.** For $H=k\log 2$ with $k$ a positive integer, $(T-H,T+H]$ splits into $2k$ such intervals and $0\le K\le1$. Outside it the kernel is bounded by $e^{-|T-t|/2}$, giving total cost at most $4Me^{-H/2}$. First let $T\to\infty$, then $k\to\infty$. The same bound applies on every measurable set. The charge $-m^2/2$ and the signed sum beyond the first window still require their full contribution. Lean verification pending.
