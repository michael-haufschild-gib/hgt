# EDQ logarithmic lattice: exact cotangent orientation

- **Stage:** 1-in-progress
- **Type:** independently frozen source identity and sign targets
- **RH chain:** literal Euler deletion → retained arithmetic remainder/joint signature → source orientation including the exceptional head → exclusion of off-line zeros → RH
- **RH status:** unproved. This proposed source law is not assumed at a zero.

## Corpus origin and gap

`RHTower.Sieve.KuzminLandau` proves an exact summation-by-parts identity before taking norms. Its coefficient is `c(delta)=-1/2-i*cot(pi*delta)/2`, the inverse phase chord. The existing estimate controls absolute size. This investigation retains its imaginary part for the actual decreasing logarithmic increments. Whole-corpus searches for closed phase/sine sums, logarithmic sine sums, and cotangent imaginary orientation did not find this signed specialization. Search misses make no novelty claim.

The previously proved constant-speed Bernoulli prefix law does not pass automatically through the logarithmic clock. Fourier/Laplace remainder representations and existing nonstationary magnitude estimates supplied no sign-preserving head comparison. R, B2, and C keep their frozen statements; none is claimed from the present calculation.

## Frozen exact target LCO1

Let real phases phi_0,...,phi_M have `phi_0=0` and increments `delta_j=phi_(j+1)-phi_j` in `(0,1)`. Let `E_j=exp(2*pi*i*phi_j)` and `q_j=cot(pi*delta_j)`. For M>=1, define

`D_M = Im(sum_(j=0..M-1) E_j) + sin(2*pi*phi_M)/2`

`      - q_(M-1)*(1-cos(2*pi*phi_M))/2`.

The exact proposed identity is

`D_M = -sum_(j=0..M-2) (q_(j+1)-q_j)*(1-cos(2*pi*phi_(j+1)))/2`.

Proof attack: use `E_j=c_j*(E_(j+1)-E_j)`, finite summation by parts, and the constant real part of c. All indices, the M=1 empty sum, and the terminal correction must remain explicit. If increments decrease, cotangents increase and D_M<=0. If M>=2 and increments strictly decrease, the first interior phase lies in `(0,1)`, so its term is strictly negative and D_M<0.

## Frozen literal logarithmic target LCO2

For integer n>=1, t>0, and every M>=1, set

`phi_j=(t/(2*pi))*log((n+j)/n)`.

If `t<2*pi*n`, its increments are positive, strictly decreasing, and below one. Therefore the full corrected prefix obeys LCO1 for every finite cutoff, without a large-cutoff limit. At an exact closing phase `t*log((n+M)/n)=2*pi*K` for integer K, the terminal correction vanishes and

`sum_(j=0..M-1) sin(t*log((n+j)/n)) < 0` for M>=2.

This is a finite source statement with ordinary lattice samples. It does not silently insert the power weight, replace the Bernoulli integral, assert C/B2/R, or establish the unit boundary at a zeta zero. The next required transfer is an exact relation to the weighted head remainder with all correction terms retained.

## Adversarial audit and plan

- [ ] Verify exact sign and finite endpoint identity from the current coefficient definition.
- [ ] Prove weak and strict orientation for every finite decreasing-increment sequence.
- [ ] Prove the literal logarithmic increment bounds and specialize to every finite cutoff.
- [ ] Audit what survives introduction of the actual power weight; retain any unsigned terms.
- [ ] Check scratches, serialized leaf builds, axioms, umbrella wiring, and lint.
- [ ] Supply the independent exceptional-head law and finish the unconditional RH proof.

No numerical experiment or computational certificate is part of this proof. The generic ancestry is finite summation by parts and the corpus's Kuzmin–Landau coefficient, not a new general oscillatory-sum method.

## Independently frozen weighted identity LCO3

For arbitrary real weights w_j, replace the sum in D_M by `sum w_j*Im(E_j)` and multiply both terminal corrections by w_(M-1). Exact summation by parts predicts

`D_M(w) = sum_(j=0..M-2) (w_(j+1)-w_j)*sin(2*pi*phi_(j+1))/2`

`         - sum_(j=0..M-2) (w_(j+1)*q_(j+1)-w_j*q_j)*(1-cos(2*pi*phi_(j+1)))/2`.

This retains the drift introduced by the actual power weight `w_j=(n+j)^(-sigma)`. Neither term is silently assigned a sign. In particular, the unweighted orientation is not yet a theorem about weighted zeta prefixes. Prove the weighted equality and literal complex-power link together with LCO1/LCO2 so the RH transfer gap remains explicit.
