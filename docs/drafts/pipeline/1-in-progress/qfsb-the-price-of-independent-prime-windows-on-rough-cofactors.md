# The price of independent prime windows on rough cofactors

- **Stage** 1-in-progress

At a frozen sieve wall \(y\ge1\), choose a set \(S\) of rough squarefree cofactors through \(Z\). For each \(m\in S\) choose its own subinterval \(y\le l_m\le u_m\le\lfloor X/m\rfloor\). Keep the ordinary primes in this window with their logarithmic weights and allow independent signed changes bounded by \(\Lambda\) on its proper powers. Subtract the original floor increment \(y(\lfloor u_m/y\rfloor-\lfloor l_m/y\rfloor)\).

For each \(\Theta<s<1\), the total absolute value of these centered window readings is
\[
 \ll_s X^s\sum_{m\in S}m^{-s}+y\,\#S
 \le C_s X^s Z^{1-s}+y\,\#S.
\]
Here \(\Theta\) is the zeta zero abscissa. At each endpoint \(|\vartheta(t)-t|\ll_s t^s\); the total variation allowed on proper powers relative to ordinary primes costs at most \(\psi(u_m)-\vartheta(u_m)\ll\sqrt{u_m}\). The two floor residues differ by less than \(y\). Summing \(m^{-s}\) proves the assertion without a sign estimate between cofactors. At the log-square cutoff the normalized bound tends to zero uniformly for \(y\le Z\le X/y\): the first term costs \(O_s((X/Z)^{s-1})\) relative to \(X\); the second costs at most the density of rough integers through \(Z\), which tends uniformly to zero.

**Sharp boundary for polynomially many windows.** Let \(Z=\lfloor T^a\rfloor\), \(a>0\), and \(X=TZ\). For the ordinary-prime reading use only prime cofactors \(Z/2<m\le Z\) and give them all the same window \((y,T]\). Each is a true subinterval of its quotient range. Every cofactor sign is negative, and the signed sum is exactly
\[
 -\big(\pi(Z)-\pi(\lfloor Z/2\rfloor)\big)
 \big(E(T)-E(y)+(T\bmod y)\big),\qquad E(t)=\vartheta(t)-t .
\]
The prime count is asymptotic to \(Z/(2\log Z)\), and \(y=b(TZ)=T^{o(1)}\). Thus at cofactor exponent \(\gamma=a/(1+a)\), uniform estimates on all these subwindows at every exponent above \(r\ge(1+\gamma)/2\) force \(\Theta\le(r-\gamma)/(1-\gamma)\). The upper estimate attains every exponent above \(\gamma+(1-\gamma)\Theta\). Littlewood excursions give both signs of order at least \(Z\sqrt T\log\log\log T/\log Z\), even under arbitrary proper-power edits in the individual rows. In particular, a half-plus estimate for independently chosen subwindows at any fixed \(\gamma>0\) is impossible. The full original reading uses prescribed upper endpoints \(\lfloor X/m\rfloor\). Its remaining mathematical question is their compensation with the lower quotient indices.
