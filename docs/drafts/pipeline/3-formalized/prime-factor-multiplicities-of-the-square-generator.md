# Prime-factor multiplicities of the square generator

Let $U_n/V_n$ be the reduced ordinary generator of $nD_n$, $H$ the cubic-spline autocorrelation, and $M=\int_{\mathbb R}H(u)e^{u/2}\,du>0$. Then
$$
\frac{(\log n^2)^2}{n^3}\big(\Omega(U_n)-\Omega(V_n)\big)\longrightarrow 4\log4\,M .
$$
In particular every sufficiently large numerator has more prime factors counted with multiplicity. The signed log size still satisfies $(\log n^2)^k\log(U_n/V_n)=o(n^3)$ for every fixed $k$. [Prime-factor multiplicities](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/PrimeFactorMultiplicityOfTheSquareGenerator.lean)

Put $T=\log n^2$ and $e_p=v_p(U_n/V_n)$. For each bounded continuous $g$ the signed measure $n^{-3}\sum_p e_p\log p\,\delta_{\log p-T}$ converges against $g$ to
$$4\int_{\mathbb R}[g(u)-g(u+\log4)]H(u)e^{u/2}\,du.$$
Replacing the valuations by their compactly supported profile costs $O(n^2)$ in absolute logarithmic mass. The first centered profile moment is $-4\log4\,M$. The second moment without a prime log weight is $o(n^3)$ because the number of primes in the window is $o(n^2)$. Expanding $T^2=(\log p)T-(\log p)(\log p-T)+(\log p-T)^2$ and summing yields the multiplicity limit. [Prime exponent comparison](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/ThePrimeExponentsOnTheSquareDiagonal.lean) · [Profile moments](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/TheLogarithmicMomentOfTheSquarePrimeProfile.lean)

Lean declarations are `tendsto_square_generator_prime_multiplicity`, `eventually_square_generator_more_numerator_factors`, `tendsto_square_generator_prime_test` and `diagonal_log_negligible_at_every_logarithmic_order`.
