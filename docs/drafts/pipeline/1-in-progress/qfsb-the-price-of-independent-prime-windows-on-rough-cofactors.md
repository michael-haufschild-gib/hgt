# The price of independent prime windows on rough cofactors

- **Stage** 1-in-progress

At a frozen sieve wall \(y\ge1\), choose a set \(S\) of rough squarefree cofactors through \(Z\). For each \(m\in S\) choose its own subinterval \(y\le l_m\le u_m\le\lfloor X/m\rfloor\). Keep the ordinary primes in this window with their logarithmic weights and allow independent signed changes bounded by \(\Lambda\) on its proper powers. Subtract the original floor increment \(y(\lfloor u_m/y\rfloor-\lfloor l_m/y\rfloor)\).

For each \(\Theta<s<1\), the total absolute value of these centered window readings is
\[
 \ll_s X^s\sum_{m\in S}m^{-s}+y\,\#S
 \le C_s X^s Z^{1-s}+y\,\#S.
\]
Here \(\Theta\) is the zeta zero abscissa. At each endpoint \(|\vartheta(t)-t|\ll_s t^s\); the total variation allowed on proper powers relative to ordinary primes costs at most \(\psi(u_m)-\vartheta(u_m)\ll\sqrt{u_m}\). The two floor residues differ by less than \(y\). Summing \(m^{-s}\) proves the assertion without a sign estimate between cofactors. At the log-square cutoff the normalized bound tends to zero uniformly for \(y\le Z\le X/y\): the first term costs \(O_s((X/Z)^{s-1})\) relative to \(X\); the second costs at most the density of rough integers through \(Z\), which tends uniformly to zero.

The finite estimate is formalized in `absolute_price_of_independent_quotient_subwindows`. [IndependentPrimeWindowsOnRoughCofactors.lean](../../../../formal/GaloisForLFunctions/RestrictedFactorizationCalculus/IndependentPrimeWindowsOnRoughCofactors.lean)

**Sharp boundary for polynomially many windows.** Fix \(a>0\), take \(v=T^a\), \(X=T\lceil2v\rceil\), \(y=b(X)\), and retain prime cofactors in \(S=(v,2v]\). Each cofactor can use the common physical window \((y,T]\). Write \(E(t)=\vartheta(t)-t\). For ordinary primes the signed sum is exactly
\[
 -\#S\,[E(T)-E(y)+(T\bmod y)].
\]
For arbitrary proper-power edits depending on both the row and the observation, each summand differs from \(-E(T)\) by \(O(\sqrt T)\). This uses \(y=T^{o(1)}\) and \(\psi(T)-\vartheta(T)=O(\sqrt T)\). Dividing the observed sum by \(\#S\asymp T^a/\log T\) recovers \(-E(T)\) at that precision for **each** choice of the edits.

Consequently at cofactor exponent \(\gamma=a/(1+a)\), the critical exponent in \(X\) of this single rectangle is \(\gamma+(1-\gamma)\Theta\). For every \(\beta\ge1/2\), a bound at all exponents above \((a+\beta)/(1+a)\) is equivalent to \(\Theta\le\beta\). Sufficiency follows from the prime-error bound at every strict exponent above \(\Theta\). Necessity follows by dividing the sum by the prime multiplicity, losing only a logarithm. The upper estimate for independent intervals reaches this same exponent.

Littlewood excursions give both signs of magnitude at least \(c\,T^{a+1/2}\log\log\log T/\log T\) on sequences common to every choice of proper-power weights. In particular, for each \(r<(a+1/2)/(a+1)\), either orientation exceeds every fixed multiple of \(X^r\) cofinally. A half-plus estimate for all independent subwindows at any fixed \(\gamma>0\) is impossible. The original reading has prescribed upper endpoints \(\lfloor X/m\rfloor\). The outstanding question is their compensation with the lower quotient indices.

The repeated-window identity, both cofinal signs and the strip equivalence are formalized in `one_prime_interval_at_every_selected_prime_cofactor`, `both_signs_above_every_smaller_rectangle_power` and `sharp_exponent_of_a_single_prime_rectangle`. [Repeated prime window](../../../../formal/GaloisForLFunctions/RestrictedFactorizationCalculus/RepeatingAPrimeExcursionAcrossRoughCofactors.lean)
