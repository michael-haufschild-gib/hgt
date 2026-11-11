# The boundary trace of the normalized prime error

- **ID:** A109
- **Stage:** 3-formalized
- **Type:** THEOREM

## Exact target

For `Θ=zetaZeroAbscissa>1/2`, define the boundary trace

`B(u)=−Σ_{Re ρ=Θ} exp(i Im(ρ)u)/ρ`,

with multiplicities. The series converges absolutely and

`(ψ(x)−x)/x^Θ − B(log x) → 0`.

The trace vanishes exactly when the top line is empty; it is a finite
trigonometric polynomial exactly when that line contains finitely many distinct zeros.
An infinite attained top gives an infinite almost-periodic trace. Thus the proposed
RH / finite isolated oscillation / zero trichotomy requires additional exclusions.
A finite boundary with zeros accumulating below it also need not have a power-saving remainder.

## Available inputs

- `exists_primeErrorFiniteOscillation_of_lt_gap`: failure of AAL gives the finite,
  isolated expansion with every remainder exponent above the secondary abscissa.
- `exists_zeroHeightBox_ncard_le_ingham_huxley`: on every fixed right substrip
  `Re s≥σ>1/2`, the zero count has exponent strictly below one, after choosing
  positive slack. `zeroHeightBox` already counts `XiZeroCopy`, including multiplicities.
- `FloorFreeArithmetic.tendsto_normTrace_zeta_zero_iff`: the analogous statement
  for the spline trace already identifies zero limit with an empty top line.

## Proof route

Choose `1/2<σ₀<Θ`. The density bound gives absolute summability of
`1/|Im ρ|` over `Re ρ>σ₀`. Fix a finite subset `F` of that right substrip
whose reciprocal tail is at most `ε`. For either adjacent window of width `H`
inside `[x/2,2x]`, the existing window-term estimates give

`|Σρ T(ρ;a,b)+Σρ∈F x^ρ/ρ|`
`≤2|F|H+2εx^Θ+16x^σ₀(x/H)^θ Σρ[|ρ| |1−ρ|^θ]^(−1)`.

Take `H=x^E` with `0<E<Θ`, and choose `0<θ≤1` such that
`σ₀+(1−E)θ<Θ`. The two-sided prime-window squeeze therefore bounds the
normalized prime error plus the finite zero sum by `2ε+o(1)`.
Each member of `F` below `Θ` vanishes after normalization; the boundary
members give the corresponding finite part of `B(log x)`. Absolute reciprocal
summability bounds the omitted boundary part uniformly by `ε`.
Letting `ε↓0` proves the asserted unsmoothed limit, without differentiating
an asymptotic expansion or exchanging an unbounded derivative with a zero sum.

Bohr coefficient uniqueness identifies each boundary coefficient as
`−mult(Θ+iγ)/(Θ+iγ)`. It distinguishes empty, finite and infinite boundary traces.
At `Θ=1`, the top is empty and the prime number theorem gives the zero limit directly.

## Lean formalization

`ZeroConfigurationGeometry/TheRightSubstripsHaveSummableReciprocalZeros.lean`
proves reciprocal summability and the dominated-convergence boundary limit for
the right-substrip zero sum. Its direct Lean check passed. It uses the global
linear density deficit, dyadic ordinate buckets and `CountableDivisor.summable_of_bucket`.
`ThePrimeErrorKeepsItsBoundaryTrace.lean` passed its direct Lean check.
`tendsto_normalized_primeError_sub_boundary` proves the unsmoothed limit at the
actual zero abscissa. `tendsto_normalized_primeError_zero_iff_empty_top` proves
the empty-top equivalence using almost periodicity and the strict sign `B(0)<0`
for a nonempty top layer.
`TheBoundaryTraceDeterminesTheTopZeros.lean` passed its direct Lean check.
It proves the real-carrier identity, nonvanishing Bohr coefficients at every
attained top ordinate, and `boundaryTraceIsFinitePolynomial_iff_finite_top`.
All three modules are wired into the zero-configuration umbrella.

The original three branches are not asserted exhaustive: the actual zeta
divisor has not been proved to exclude an infinite attained top. The exact
boundary classification above retains that case.
