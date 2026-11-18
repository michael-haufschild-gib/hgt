# The pole product from vertical graph orders

**Statement.** Every signed integer spline ray admits a rational fractional ideal whose finite valuations supply the product of the two pole moments. With the original regularized jet pairing as log radius, its signed degree divided by m² tends to the full Weil form Q(a) through every multiplicity m.

**Mixed contact limit.** For compactly supported real C² profiles f and g, move the upper divisor by log x. Write h(t) = ∫ f(u)g(u+t) du. The directed prime contact divided by √x tends to

    2 (∫ f(u) exp(−u/2) du) (∫ g(v) exp(v/2) dv).

Indeed H(y) = h(log y)/√y extends by zero to a continuous compactly supported function. The normalized degree is (2/x) Σ Λ(k)H(k/x). The scaled ordinary-prime measure tends to Lebesgue measure. Proper powers contribute at most 2‖H‖∞(ψ(Bx)−θ(Bx))/x → 0 for any upper support bound B. Substitution y = exp(t) and convolution give the product. The sampled vertical orders approximate the mixed degree on each window.

**Integral realization.** Take x = r⁴ and auxiliary graph multiplicity s. Let O₊ and O₋ be the effective restriction orders for the two signs. The log of U = (O₊/O₋)², divided by d² with d = rs, tends to the pole correction. At each original multiplicity m let r grow slowly enough that d² ≤ m, and divide the original contact generator by U raised to ⌊m²/d²⌋. The unused fraction of quadratic scale is at most 1/m. For effective divisors every opposite-sign thickening has multiplicity zero, so O₋ = 1 and U is an integer square. The two sampled pole degrees on the original ray converge after division by m to their respective moments, so this integral replacement preserves Q(a).

**Open.** The sign of the residual degree on every prescribed prime pair remains the ACS comparison.

**Lean.** `tendsto_separated_graph_pair` and `separated_graph_orders_recover_pole` give the mixed limit. [Separated contacts](../../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/Intersection/PoleMomentsFromSeparatedGraphContacts.lean)

`integerProbe_from_separated_orders_and_jets` proves the signed degree limit. `separatedPoleQuotient_effective` gives the integer square on effective rays. [Finite graph orders](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/FiniteGraphOrdersForThePoleCorrection.lean)
