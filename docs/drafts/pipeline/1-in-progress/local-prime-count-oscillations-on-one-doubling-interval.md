# Local prime-count oscillations on one doubling interval

Put $b_n=\mathbf1_{n\text{ prime}}-1/\log n$ and $a_n=(\log n)b_n$. For either sign, let $D_f^\pm(Y)$ be the largest signed interval sum $\pm\sum_{h<n\le k}f_n$ with $Y\le h\le k\le2Y$. For $Y\ge2$,
$$\log(Y+1)D_b^\pm(Y)\le D_a^\pm(Y)\le\log(2Y)D_b^\pm(Y).$$
An increasing positive weight is a positive mixture of suffix indicators, with total weight its endpoint maximum. A decreasing positive weight uses prefixes. Apply both identities with $\log n$ and its reciprocal. The finite smooth Haar source at cutoff $Y$ recovers every ordinary prime count in this interval. [First prime windows](the-first-prime-windows-of-the-smooth-haar-source.md)

Under a single quartet of real part $\beta$, both signs should attain $D_a^\pm(Y)\gg_\rho Y^\beta$ at every large $Y$. The phase $\Im\rho\log x$ sweeps more than two periods on $[Y,2Y]$ by the verified height. The square-root prime-power contribution is smaller. Can actual smooth counts give $D_b^+(Y)$ or $D_b^-(Y)$ below this scale along an unbounded sequence?

For $\rho=\beta+i\gamma$, put $h=\pi/(2|\gamma|)$, $\lambda=e^h$ and $m=\operatorname{ord}_\rho\zeta$. Four consecutive quarter-period intervals fit in one octave since $|\gamma|>67$. For $E(x)=\theta(x)-x$ put $A(t)=e^{-\beta t}[E(e^{t+h})-E(e^t)]$. The single-wave formula gives
$$A(t)=-2m\Re(Ue^{i\gamma t})+o(1),\qquad U=(e^{h\rho}-1)/\rho.$$
The next reading rotates by $i$ or $-i$, so $A(t)^2+A(t+h)^2\to4m^2|U|^2>0$. The four normalized increments at $t,t+h,t+2h,t+3h$ include both signs with magnitudes at least $\sqrt2\,m|U|+o(1)$. Multiplying each ordinary centered count increment by its initial logarithm incurs $O_\rho(e^{\beta t}/t)$ through partial summation. A cofinal small value of the sum of two squares, or a cofinal upper bound on either sign over the four intervals, would exclude this quartet.
