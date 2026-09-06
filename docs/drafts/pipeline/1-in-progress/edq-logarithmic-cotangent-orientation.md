# EDQ logarithmic lattice: exact cotangent orientation

- **Stage:** 1-in-progress
- **Type:** proved finite source transport; open weighted-head comparison
- **RH chain:** literal Euler deletion → retained arithmetic remainder/joint signature → source orientation including the exceptional head → exclusion of off-line zeros → RH
- **RH status:** unproved. LCO1–LCO5 are Lean-proved; none supplies the missing weighted-head sign at a zero.

## Corpus origin and gap

`RHTower.Sieve.KuzminLandau` proves an exact summation-by-parts identity before taking norms. Its coefficient is `c(delta)=-1/2-i*cot(pi*delta)/2`, the inverse phase chord. The existing estimate controls absolute size. This investigation retains its imaginary part for the actual decreasing logarithmic increments. Whole-corpus searches for closed phase/sine sums, logarithmic sine sums, and cotangent imaginary orientation did not find this signed specialization. Search misses make no novelty claim.

The previously proved constant-speed Bernoulli prefix law does not pass automatically through the logarithmic clock. Fourier/Laplace remainder representations and existing nonstationary magnitude estimates supplied no sign-preserving head comparison. R, B2, and C keep their frozen statements; none is claimed from the present calculation.

## Proved exact identity LCO1

Let real phases phi_0,...,phi_M have `phi_0=0` and increments `delta_j=phi_(j+1)-phi_j` in `(0,1)`. Let `E_j=exp(2*pi*i*phi_j)` and `q_j=cot(pi*delta_j)`. For M>=1, define

`D_M = Im(sum_(j=0..M-1) E_j) + sin(2*pi*phi_M)/2`

`      - q_(M-1)*(1-cos(2*pi*phi_M))/2`.

The exact proved identity is

`D_M = -sum_(j=0..M-2) (q_(j+1)-q_j)*(1-cos(2*pi*phi_(j+1)))/2`.

Proof: use `E_j=c_j*(E_(j+1)-E_j)`, finite summation by parts, and the constant real part of c. All indices, the M=1 empty sum, and the terminal correction must remain explicit. If increments decrease, cotangents increase and D_M<=0. If M>=2 and increments strictly decrease, the first interior phase lies in `(0,1)`, so its term is strictly negative and D_M<0.

## Proved literal logarithmic orientation LCO2

For integer n>=1, t>0, and every M>=1, set

`phi_j=(t/(2*pi))*log((n+j)/n)`.

If `t<2*pi*n`, its increments are positive, strictly decreasing, and below one. Therefore the full corrected prefix obeys LCO1 for every finite cutoff, without a large-cutoff limit. At an exact closing phase `t*log((n+M)/n)=2*pi*K` for integer K, the terminal correction vanishes and

`sum_(j=0..M-1) sin(t*log((n+j)/n)) < 0` for M>=2.

This is a finite source statement with ordinary lattice samples. It does not silently insert the power weight, replace the Bernoulli integral, assert C/B2/R, or establish the unit boundary at a zeta zero. LCO3/LCO4 supply the exact relation to the weighted head remainder with all correction terms retained; their combined sign is still open.

## Adversarial audit and plan

- [x] Verify exact sign and finite endpoint identity from the current coefficient definition.
- [x] Prove weak and strict orientation for every finite decreasing-increment sequence.
- [x] Prove the literal logarithmic increment bounds and specialize to every finite cutoff.
- [x] Audit what survives introduction of the actual power weight; retain any unsigned terms.
- [x] Check scratches, serialized leaf builds, new-declaration axioms, umbrella wiring, and lint. No umbrella build.
- [ ] Supply the independent exceptional-head law and finish the unconditional RH proof.

No numerical experiment or computational certificate is part of this proof. The generic ancestry is finite summation by parts and the corpus's Kuzmin–Landau coefficient, not a new general oscillatory-sum method.

## Proved weighted identity LCO3

For arbitrary real weights w_j, replace the sum in D_M by `sum w_j*Im(E_j)` and multiply both terminal corrections by w_(M-1). Exact summation by parts proves

`D_M(w) = sum_(j=0..M-2) (w_(j+1)-w_j)*sin(2*pi*phi_(j+1))/2`

`         - sum_(j=0..M-2) (w_(j+1)*q_(j+1)-w_j*q_j)*(1-cos(2*pi*phi_(j+1)))/2`.

This retains the drift introduced by the actual power weight `w_j=(n+j)^(-sigma)`. Neither term is silently assigned a sign. In particular, the unweighted orientation is not yet a theorem about weighted zeta prefixes. The weighted equality and literal complex-power link are proved together with LCO1/LCO2; the RH transfer gap is the sign of the retained terms.

## Proved universal resonance identity LCO4

The chord inverse is defined whenever `sin(pi*delta_j)!=0`, even outside the first frequency band. At an exact resonance that sine is zero and `E_(j+1)=E_j`; the lost sample must be retained separately. The universal extension is:

For arbitrary real phases with phi_0=0 and arbitrary real weights, LCO3 holds after adding

`sum_(j=0..M-1, sin(pi*delta_j)=0) w_j*sin(2*pi*phi_j)`

to its right side. This includes every resonant step and every winding band, with no phase-increment hypothesis. Its proof is the same finite summation by parts using the universal identity

`c(delta)*(exp(2*pi*i*delta)-1) = if sin(pi*delta)=0 then 0 else 1`.

For the literal logarithmic phase at arbitrary positive height, increments strictly decrease and satisfy `delta_j<t/[2*pi*(n+j)]`. Beyond the explicit head where `t>=2*pi*(n+j)`, consecutive increments lie in `(0,1)`, there are no exact resonances, and the **unweighted** cotangent differences have the proved favorable sign. The arbitrary-weight identity retains its additional drift. This extension reaches the actual unit anchor at every height as an exact decomposition; it does not assert the net sign of the head or the weighted drift.

Paper audit: the first-band sign uses only cotangent antitonicity and `1-cos>=0`; these cannot be continued through a cotangent pole without recording that event. LCO4 records it. The construction is still classical finite summation by parts applied to the fixed arithmetic phase, with no claim of a new general method or literature absence.

## Proved finite-head transport LCO5

The exact one-step consequence has this paper proof. For the unweighted corrected prefix, increasing Lean's cutoff M to M+1 changes the defect by

`-(q_(M+1)-q_M)*(1-cos(2*pi*phi_(M+1)))/2`

plus the next resonant sample. For the logarithmic lattice, if `t<2*pi*(n+M)`, both adjacent increments lie in `(0,1)` and that resonant sample is zero. Therefore the corrected unweighted defect is nonincreasing from every explicit head boundary J with `t<2*pi*(n+J)`: `D_M<=D_J` for every M>=J. This transports the **actual finite head value**, without assigning its sign. The actual weighted identity still contains its separate sine drift and product-cotangent drift. Subtracting the two finite sums proves the claim; it introduces no convergence or zero hypothesis.


## Current formal boundary

Completed source results are recorded in [the formal certificate](../3-formalized/edq-logarithmic-cotangent-transport.md). The Lean cutoff `M` uses `M+1` samples, whereas LCO1–LCO4 above use M samples. LCO5 explicitly uses the Lean convention.

The actual unit source identity is `sourcePhaseDefect_eq`, with `s=sigma-it`. It is unconditional for all real sigma and t, including resonances. Its left side retains `powerSumRemainder(s,M+1) + zeta(s) + (M+1)^(1-s)/(1-s) + kernel(s,M+1)/2`, together with the terminal phase correction. Its right side is the two weighted drifts plus the resonant prefix. The conjugate-height convention is explicit, with no alteration of the arithmetic source.

The next proof obligation is a source comparison for this **entire weighted expression**, including the initial head. An unweighted defect sign, the finite-head transport inequality, and eventual normalized-remainder negativity do not discharge it. R, B2, C, and RH remain open. No positive-height restriction or zeta-zero premise is smuggled into the universal source identity.

Validation: both new leaf builds passed; all 39 new declarations use only `propext`, `Classical.choice`, and `Quot.sound`; formal lint passed with existing large-file warnings. No numerical results or computational certificates were used.

The independent [signed Fourier tail theorem](../3-formalized/edq-linear-remainder-cutoff.md) controls the complete actual weighted remainder for every `n>=t>=1` in `0<sigma<=1`. Thus the remaining comparison concerns the finite head `n<t` and its zero-bearing unit value; it does not require another tail-convergence proof or another unweighted prefix identity.
