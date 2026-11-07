# A one-off Euler product over rational primes

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** There exist ordinary multiplicative natural Dirichlet coefficients with positive linear counting and an Euler product over rational primes, allowing repetitions, whose continuation has exactly `3/5 ± iγ` as zeros on `Re s > 17/30`, away from its pole at `1`.

## Mechanism

`RHTower.eventually_exists_prime_short_interval_seventeenThirtieths` supplies a rational prime in `(x,x+x^α]` for every sufficiently large `x`, for every `17/30 < α < 1`. Least-prime rounding is independent of `α`. Its logarithmic displacement is eventually at most `exp(−(1−α)t)` for each such exponent. The prime-sum correction is therefore holomorphic on `Re s > 17/30`; prime-power corrections are already holomorphic on `Re s > 1/2`. The nonvanishing exponential correction preserves the isolated pair.

Collecting occupations gives natural Dirichlet coefficients. The coprime-fibre bijection proves ordinary multiplicativity. Positivity of the simple-pole residue and Wiener–Ikehara give positive linear counting.

## Lean results

- **Capstone:** `RationalPrimeOneOff.exists_rational_prime_multiplicative_linear_count_one_off`, in `ArithmeticPositiveDuality/TheRationalPrimeOneOffHasMultiplicativeCounting.lean`.
- **Euler product and divisor:** `RationalPrimeOneOff.exists_rational_prime_euler_one_off`, in `ArithmeticPositiveDuality/ARationalPrimeBeurlingOneOff.lean`.
- **Arithmetic:** `IntegerOccupation.finite_norm_fiber`, `coeff_one`, `coeff_mul_of_coprime`, and `hasSum_coeff`, in `ArithmeticPositiveDuality/IntegerOccupationCoefficients.lean`.
- The capstone passed direct `lake --old env lean` checking without warnings. Its transitive axioms are exactly `propext`, `Classical.choice`, `Quot.sound`. The unconditional prime-gap input has the same axiom closure.

## Paper proof

Let `t_k` be the existing discrete one-off atoms and put `q_k` equal to the least rational prime at least `exp(t_k)`. This choice is monotone and independent of the gap exponent. For each `17/30 < α < 1`, the unconditional Guth–Maynard theorem gives, for all sufficiently large `k`,
`0 ≤ log(q_k) − t_k ≤ exp(−(1−α)t_k)`.
The atoms tend to infinity because their cumulative mass is `k+1`. Given `σ > 17/30`, choose `17/30 < α < min(σ,1)`. For `Re s ≥ σ`, integration along the real segment between the two logarithms bounds the prime-term difference by
`|s| exp(−σt_k)(log(q_k)−t_k)`.
Its tail is bounded by `|s| exp(−(σ+1−α)t_k)`, a summable sequence since `α<σ`. The finite initial segment is entire. Thus the prime-sum correction is holomorphic on `Re s > 17/30`; both prime-power remainders are holomorphic on `Re s > 1/2`. Multiplication of the original continuation by the exponential of their difference preserves exactly the original zero pair.

For a finite occupation `v`, set `N(v)=∏_k q_k^(v_k)` and `a(n)=#{v:N(v)=n}`. Absolute convergence at `s=2` makes every fibre finite; the occupation Euler product gives the ordinary Dirichlet series for `Re s>1`. If `m,n` are coprime, prime labels in an occupation of `mn` split uniquely according to whether `q_k` divides `m` or `n`. This gives a bijection with the product of the two occupation fibres, hence `a(mn)=a(m)a(n)` and `a(1)=1`.

Removing the simple pole at `1` gives a holomorphic numerator `H` on `Re s>17/30`. Its value at `1` is nonzero. Positivity of the occupation series for real `s>1` and continuity imply `H(1)>0`. The divided difference `(H(s)−H(1))/(s−1)` supplies the continuous boundary value required by the corpus's unconditional Wiener–Ikehara theorem. Consequently `Σ_{n<N} a(n)/N → H(1)>0`.

## Scope

Prime labels may repeat. No uniform multiplicity bound, Ramanujan coefficient bound, continuation throughout `Re s>1/2`, polynomial vertical growth, unit coefficients, or Riemann functional equation is established. Actual zeta's AAL remains undecided.
