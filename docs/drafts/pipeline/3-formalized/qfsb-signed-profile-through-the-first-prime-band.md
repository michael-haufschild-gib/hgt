# Signed profile through the first prime band

- **Stage** 3-formalized

For a prime wall \(y\), a cofactor cutoff \(y\le Z\le y^2\), and \(X\ge yZ\), let \(B(X,y,Z)\) sum the rough quotient reading on indices \(\lfloor X/Z\rfloor<q\le X\). Keep every prime above \(y\) with its logarithmic weight. Each proper prime power can have any signed weight bounded by \(\Lambda\). Uniformly over all these choices,
\[
 \frac{B(X,y,Z)}X=1-\log\!\left(\frac{\log Z}{\log y}\right)+o(1)
 \qquad(y\to\infty).
\]
Transposition gives a sum of prime intervals \((\lfloor X/Z\rfloor,\lfloor X/m\rfloor]\) with coefficients \(\mu_y(m)\). Through \(Z\), only the unit and the primes above \(y\) contribute, with respective signs \(+1,-1\). The prime number theorem replaces each interval by its length. Its errors sum to \(o(X)\) because the reciprocal prime mass is bounded. The common lower endpoint costs \(o(X)\) by zero prime density. Mertens' reciprocal estimate gives the displayed profile.

At the log-square wall with \(Z=y^2\), the raw upper reading carries \((1-\log 2)X+o(X)\). When \(y^2\le X\le y^3\), taking \(Z=\lfloor X/y\rfloor\) makes the index cutoff exactly \(y\). All surviving Mangoldt atoms enter. Their convolution with \(\mu_y\) equals \(-\mu_y\log\), giving the **negative** of the displayed profile for the complete logarithmically weighted rough Möbius prefix.

**Lean.** `transpose_the_upper_quotient_cells`, `positive_smooth_center_at_an_interior_quotient_cut`, `signed_profile_through_the_first_prime_band`, `upper_prime_charge_at_the_log_square_cutoff`, and `signed_bias_between_the_square_and_cube_of_the_prime_wall` in [TheSmoothPopulationAtAnInteriorQuotientCut.lean](../../../../formal/GaloisForLFunctions/RestrictedFactorizationCalculus/TheSmoothPopulationAtAnInteriorQuotientCut.lean).

The original upper floor sector carries the same macroscopic charge. On each cofactor its correction is the difference of two residues modulo \(y\), of magnitude at most \(y\). The number of rough cofactors through \(Z\le y^2\) is \(1+\pi(Z)-\pi(y)=o(Z)\) uniformly for \(Z\ge y\). Since \(yZ\le X\), the summed residue cost is \(o(X)\). The sum after centering stays \(o(X)\) under arbitrary multipliers of modulus at most one on the individual cofactors. See `centered_first_prime_band_for_every_cofactor_selection` and `original_floor_cancels_the_first_prime_band` in [TheExactFloorCenterInTheFirstPrimeBand.lean](../../../../formal/GaloisForLFunctions/RestrictedFactorizationCalculus/TheExactFloorCenterInTheFirstPrimeBand.lean).
