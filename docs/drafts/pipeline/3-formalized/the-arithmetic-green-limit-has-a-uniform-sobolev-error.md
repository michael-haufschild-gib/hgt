# The arithmetic Green limit has a uniform Sobolev error

- **ID:** the-arithmetic-green-limit-has-a-uniform-sobolev-error
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** B133; the arithmetic-clock continuum Green coupling.
- **Statement:** Once the prime clock covers a compact packet's correlation
  support, its coupled Green energy increases to Weil's form from below, with
  `0≤weilQuad(f)−coupledGreenEnergy(r,f)≤(1−r²)∫(f')²/2` for `0≤r<1`.
  On each fixed support window the cutoff is common to all packets, so this
  is a uniform bound on bounded Sobolev sets.

## Theorem and proof

Write `M(f)=∫f²`, `H(f)=∫(f')²`, `D_f(x)=autocorr(f,0)−autocorr(f,x)`,
`K_r(x)=archDamped(r,x)` and `ω(x)=archProfile(|x|)`. Let
`J_r(f)=∫K_r D_f`, and let `E_r(f)` be the arithmetic-clock coupled Green
energy. For every real compact C² packet supported in `[-R,R]`, put
`B=⌈exp(2R)⌉+1`. If `0≤r<1` and `arithmeticClock(r)≥cumulativeCapacity(B)`, then

`0≤weilQuad(f)−E_r(f)=levyEnergy(f)−J_r(f)≤(1−r²)H(f)/2`.

For `r≤s<1`, the same cutoff at `r` implies `E_r(f)≤E_s(f)`.
Consequently convergence is uniform over all these packets with `H(f)≤M`,
for every fixed real `R,M`.

**Prime cutoff.** If `p≥B`, every positive power satisfies `p^k≥B`, hence
`log(p^k)>2R` and its autocorrelation vanishes. Thus `primeCorrelation(p,f)=0`.
At clock mass `S≥C_B`, every prime `p<B` has weight one. Expanding the finite
weighted prime channels and using `Σ a_p(S)c_p=S` gives exactly
`clockedPrimeChannel(S,f)−S M(f)=−primeSum(f)`. This threshold is independent
of the packet. The established identity `geometricScalar=2 gammaHardyPhaseRate(0)`
and Green mass splitting leave exactly the archimedean defect

`weilQuad(f)−E_r(f)=∫ (ω−K_r)D_f`.

**Uniform error.** For `t=|x|>0`, the kernel difference is

`(1−r²)e^(−5t/2)/[(1−e^(−2t))(1−r²e^(−2t))]`.

Since `1−r²e^(−2t)≥1−e^(−2t)=2e^(−t)sinh t`, the inequality `sinh t≥t` gives
`t²(archProfile(t)−archDamped(r,t))≤(1−r²)e^(−t/2)/4`.
The existing translation estimate
`autocorr(f,0)−autocorr(f,x)≤x²∫(f')²/2`, followed by
`∫e^(−|x|/2)=4`, gives the stated bound. The error integrand is nonnegative
off zero, and at zero `D_f(0)=0`. Integrability follows by subtracting the
integrable damped jump integrand from the critical Lévy integrand.

**Order and uniformity.** `K_r≤K_s` for `0≤r≤s<1`, so both self-energy and
`J_r` increase. The arithmetic clock therefore stays saturated, and the
exact defect identity proves `E_r≤E_s`. Since the clock tends to infinity,
all packets in the support window eventually satisfy the cutoff simultaneously.
On `H(f)≤M`, their errors are bounded by `(1−r²)M/2→0`.

## Boundary

This strengthens pointwise convergence to an ordered approximation with a
uniform error estimate. It supplies no positivity of the full Weil form and
no kernel descending separately to the refuted adelic quotient.

## Inputs and novelty

Reuses `autocorr_origin_deficit_le_derivative_energy`, `smoothGreen_deficit`,
`integral_archDamped_mul_eq`, `primeSum_eq_finite_channels`, the arithmetic
capacity clock, and `weilQuad_eq`. Corpus search found pointwise Green
convergence but no uniform signed Sobolev estimate for this coupling.

## Lean declarations and verification

Both modules belong to `formal/GaloisForLFunctions/HyperbolicArakelovTheory/`
and are imported by its umbrella.

- `TheSobolevErrorOfTheHyperbolicGreenDamping.lean`:
  `sq_mul_archProfile_sub_archDamped_le`, `levyEnergy_sub_dampedJump_bounds`,
  `dampedJumpEnergy_mono`.
- `TheArithmeticGreenLimitIsAnOrderedSobolevLimit.lean` (namespace `PrimeSuspension`):
  `clockedPrimeChannel_sub_mass_of_supportedIn`, `coupledGreenEnergy_error_bounds`,
  `coupledGreenEnergy_mono`, `eventually_coupledGreenEnergy_error_bounds`,
  `coupledGreenEnergy_uniform_sobolev`.

Both plain `lake --old env lean` checks pass without warnings. All seven printed
transitive axiom audits contain only `[propext, Classical.choice, Quot.sound]`.
