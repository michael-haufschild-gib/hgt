# Zeros detected by the square prime weight

Let $H$ be the cubic spline autocorrelation, $W(v)=v^{-1/2}[2H(\log v)-H(\log(v/4))]$ on $v>0$. Its mean vanishes. Its prime sum on the square conductors differs from the ordinary signed prime contact by $O(1)$. The one-sided bound of order $(n+1)^{2s}$ is equivalent to zeta zero width at most $s$ for $0\le s<1/2$. In particular a constant bound detects RH. At diagonal multiplicity the reduced generator satisfies $|\log(U/V)|\ll n^2(n+1)^{2w}$ at the actual width $w$. [Dyadic prime contact](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/TheDyadicPrimeWeightOfSquareConductors.lean)

For $s=1/2+it$, $M_W(s)=(2-4^{it})\widehat B(t)\overline{\widehat B(\bar t)}$. This is nonzero off the critical line in the open strip and at every critical zero seen by $B$. Every finite combination $N$ of positive dilates of the fractional-part kernel has a factor $\zeta(s)$ in its Mellin transform. Thus no such combination equals $W$ almost everywhere.

Suppose $E=|W-N|$ is integrable, $E\le B$ and $\int E\le B/X$ for $X>0$. A zero $\rho$ with $\beta=\Re\rho$ gives
$$B\ge \beta\,|M_W(\rho)|\,X^\beta.$$
Indeed, among errors with those height and mass constraints, the initial interval of height $B$ and length $1/X$ maximizes the integral against the decreasing weight $v^{\beta-1}$. A fixed seen critical zero gives the unconditional lower bound $c\sqrt X$ with $c>0$. For $1/2\le\sigma<1/2+w$, every allowance $KX^\sigma$ eventually fails for every choice of the finite combination. [Mellin separation and cost](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/CriticalZerosSeparateThePrimeProfileFromFactorialKernels.lean)

Lean declarations include `dyadicPrimeContact_error`, `zetaZeroWidth_le_iff_dyadicPrimeContact`, `successorSquare_diagonal_log_at_width`, `squarePrimeWeight_mean_zero`, `mellin_squarePrimeWeight_off_line`, `nymanCombination_ne_squarePrimeWeight`, `factorial_cost_at_zero`, `critical_factorial_cost` and `factorial_cost_above_power`.
