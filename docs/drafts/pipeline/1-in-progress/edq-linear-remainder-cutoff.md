# EDQ: linear cutoff from signed Fourier modes

- **Stage:** 1-in-progress
- **Target:** literal normalized arithmetic remainder; no assumed zero equation
- **RH chain:** Euler deletion → retained remainder → uniform tail orientation and exceptional-head comparison → exclusion of off-line zeros → RH
- **RH status:** unproved; this target confines the exceptional head but does not orient the unit value at high zeros.

## Frozen target LNC

For `0<Re(s)<=1`, `t=Im(s)>=1`, and integer `N>=1` with `t<=N`, prove

`Im(normalizedWeightedRemainder(s,N))<0`.

This strengthens the existing superlinear bound `t^3<=N^2`. It is weaker than the frozen R conjecture `t<2*pi*N`; R is not changed or claimed. No numerical input is used.

## Source ancestry and dependency-closed paper argument

The actual Bernoulli kernel has the absolutely convergent expansion

`b(x)=-1/12 + sum_(k in Z, k!=0) exp(2*pi*i*k*x)/(4*pi^2*k^2)`.

The corpus already proves this Fourier identity (`BernoulliFourierBridge`) and both signs of the weighted first-derivative test (`VanDerCorputWeighted`, `VanDerCorputWeightedAnti`). These are the starting source facts.

At positive integer N, let `u=conjugate(s)` and multiply the Bernoulli tail by `N^(u+1)`. The mean is exactly `-1/[12(u+1)]`. Each nonzero Fourier mode is an integral with real decreasing amplitude `x^(-Re(s)-2)` and phase `2*pi*k*x+t*log x`. When `|t|<=N` and x>=N, the derivative has absolute value at least five, since `2*pi>6`. Its sign and monotonicity are fixed. The existing weighted first-derivative test therefore bounds each mode by `4*N^(-Re(s)-2)/5`, uniformly in its integer frequency and upper endpoint. Conjugation handles negative frequencies. Absolute integrability passes the bound to the half-line.

The Fourier coefficients are nonnegative real numbers and have total mass exactly `1/12` (evaluate the existing series at zero). Thus the complete centered tail has the uniform norm bound

`|N^(u+1)*tail(N,u) + 1/[12(u+1)]| <= 1/(15*N)`.

Every exchange of infinite sum, integral, conjugation, and normalization must be justified in Lean. This is an estimate for the literal source, with its power weight retained.

For t>=5 and `0<Re(s)<=1`, the mean's negative imaginary margin is

`t/[12*((Re(s)+1)^2+t^2)] > 1/(15*t) >= 1/(15*N)`.

For `1<=t<=5`, reuse the already proved quartic disk bound. Its numerator is at most

`(t^2+25/2)*(t^2+4)=t^4+(33/2)*t^2+50 <= (143/2)*t^3 < 96*t^3`.

The denominator condition is at least `96*t*N^2 >= 96*t^3`. Hence the quartic phase theorem covers this remaining compact height range. Combining the two analytic bounds proves LNC.

## Audit and plan

- [ ] Check both signed logarithmic Fourier modes with actual power amplitude.
- [ ] Prove Fourier coefficient mass and justified whole-tail sum/integral transfer.
- [ ] Prove the scaled source disk and the two height comparisons.
- [ ] Scratch-check; serialize only needed leaf builds; wire modules; audit only new declarations; lint.
- [ ] Prove the independent exceptional-head comparison and unconditional RH.

This is a classical weighted Fourier/nonstationary-phase proof candidate, not a novelty claim or a new independent route label. No sign is assigned to individual Bernoulli cells. The finite cotangent identity remains exact, but the present proof controls its arithmetic source via signed-frequency cancellation rather than discarding the weight drift.
