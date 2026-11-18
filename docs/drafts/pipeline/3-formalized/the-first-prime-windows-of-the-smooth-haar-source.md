# Localizing the smooth Haar energy at the first large prime

Let $H_y(t)=S(\lfloor1/t\rfloor,y)-2S(\lfloor1/(2t)\rfloor,y)$, where $S(x,y)$ counts positive integers supported on primes at most $y$. The finite-deletion Möbius source equals this smooth Haar sum. Its full energy has a positive Gram expansion. [Haar source and Gram identity](../../../../formal/GaloisForLFunctions/RHTower/PMPowerDampedMobiusFiniteDeletion.lean)

Write $k=\lfloor1/t\rfloor$. For $k<(y+1)^2$ every nonsmooth integer has a unique prime factor $p>y$, occurring once. Subtracting the two counts of multiples gives
$$H_y(t)=(k\bmod2)-\#\{y<p\le k:\lfloor k/p\rfloor\text{ odd}\}.$$
On the first interval $y\le k\le2y$ the count is $\pi(k)-\pi(y)$. At even $k=2n$ throughout the larger window the negative source counts the prime factors above $y$ of $\binom{2n}n$. [Binomial identity](dyadic-differences-of-square-root-smooth-counts.md)

For $3y^2/4\le1/t\le y^2$, every prime in $(y^2/2,2y^2/3]$ contributes with quotient one for large $y$. The prime number theorem gives $|H_y(t)|\gg y^2/\log y$ on that interval. On $y\le 1/t\le y^2$, the exact formula gives $|H_y(t)|\le1+\pi(1/t)\ll1/(t\log y)$. Hence the raw squared energy on $[y^{-2},y^{-1}]$ has order $y^2/(\log y)^2$.

Can the locally centered Gram sum control the first moment on the square-root window? Subtracting the integer reciprocal-logarithm density is necessary even there. On the smaller window $y\le k\le2y$ the centered source is exactly the difference of ordinary counting errors at the two endpoints. Bounds on centered squared energy on overlapping windows would control those differences by Cauchy–Schwarz.

[smoothHaarSource_eq_large_prime_count](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/TheFirstPrimeWindowsOfTheSmoothHaarSource.lean) · [smoothHaarSource_first_doubling](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/TheFirstPrimeWindowsOfTheSmoothHaarSource.lean) · [smoothHaarSource_square_window_energy](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/TheFirstPrimeWindowsOfTheSmoothHaarSource.lean)
