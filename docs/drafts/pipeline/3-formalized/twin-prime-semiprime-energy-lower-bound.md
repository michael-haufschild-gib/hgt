# Semiprimes force bulk unsigned Type II energy

- **ID:** twin-prime-semiprime-energy-lower-bound
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / BRIDGE
- **Source:** [signed determinant endpoint](../1-in-progress/twin-prime-consumed-mark-determinant.md)
- **Lean:** `formal/GaloisForLFunctions/twin-prime/SemiprimeEnergy.lean`
- **Statement:** The actual zero-frequency, empty-label Type II coefficient has energy at least `T^2/25` eventually, uniformly over all natural roughness and Vaughan cutoffs at most `T`.

## Exact statement

For natural numbers `z,V<=T`, put

`R_z(n)=1` if `n=1` or the least prime factor of `n` exceeds `z`, and zero otherwise;

`c_V(n)=sum_(d|n,d>V) Lambda(d)`;

`f_(T,z,V)(s)=sum_(mn=s,T<m,n<=2T) mu(m)R_z(m)c_V(n)R_z(n)`;

`E(T,z,V)=sum_(T^2<s<=2T^2) f_(T,z,V)(s)^2`.

Then, uniformly in those cutoffs, `E(T,z,V)>=T^2/25` for all sufficiently large `T`. In particular, for every cutoff family `z(T),V(T)<=T`, the energy is not `o(T^2)`.

The finite positive statement is stronger than the eventual numerical bound. For prime sets `P=(T,6T/5]` and `R=(6T/5,7T/5]`,

`E(T,z,V)>=4 (sum_(p in P) log p)(sum_(r in R) log r)`.

Every distinct pair of primes in the full factor block has the exact coefficient `f(pr)=-log(pr)`.

## Dependency-closed paper proof

The positive divisors of a product of distinct primes `p<r` are `1,p,r,pr`. Only `p,r` lie in the admissible factorization set, and both factors survive every cutoff at most `T`. Moreover, `mu(p)=mu(r)=-1` and `c_V(p)=log p`, `c_V(r)=log r`. Thus `f(pr)=-log p-log r`.

Unique factorization makes `(p,r)->pr` injective on ordered pairs. For `p in P` and `r in R`, the product lies in `(T^2,42T^2/25]`, hence inside the energy interval. Restricting the nonnegative energy to those products and using `(log p+log r)^2>=4 log p log r` proves the finite bound.

The unconditional theorem `chebyshev_asymptotic` in `PNTPlus/Consequences.lean` gives

`(sum_(p in P) log p)/T -> 1/5`,
`(sum_(r in R) log r)/T -> 1/5`.

Both masses eventually exceed `T/10`, proving `E>=T^2/25`. If `E=o(T^2)`, its ratio to `T^2` would eventually be below `1/50`, a contradiction. The cutoff quantifiers enter only the finite argument, so the eventual threshold is uniform in them.

The PNT dependency is the existing vendored proof, with provenance in `formal/GaloisForLFunctions/PNTPlus/PROVENANCE.md`. No conditional analytic interface was added.

## Lean surface and verification

- `TwinPrime.emptyLabelCoefficient_prime_pair`: exact semiprime coefficient.
- `TwinPrime.emptyLabelEnergy_ge_prime_log_masses`: finite positive lower bound.
- `TwinPrime.lowerFactorPrimes_log_mass_tendsto` and `TwinPrime.upperFactorPrimes_log_mass_tendsto`: fixed-ratio prime masses.
- `TwinPrime.eventually_emptyLabelEnergy_ge`: uniform eventual lower bound.
- `TwinPrime.emptyLabelEnergy_not_isLittleO`: arbitrary cutoff-family obstruction.

The leaf command `lake --old env lean GaloisForLFunctions/twin-prime/SemiprimeEnergy.lean` passed. Axiom checks for the exact coefficient, eventual bound, and non-little-o theorem returned only `[propext, Classical.choice, Quot.sound]`. No computation certificate, analytic premise, placeholder, or raised elaboration option was used. The own umbrella imports the leaf; no umbrella build was run.

## Scope and novelty

**Verdict: REDISCOVERED.** This is a direct semiprime/PNT diagnostic, not new scientific knowledge. It closes the [unsigned empty-label route](../5-failed/twin-prime-unsigned-empty-label-energy.md). It does not bound the signed determinant sum: that sum retains `mu(qh)`, absent from this nonnegative energy. Twin-prime infinitude remains unproved.

## Log

- 2026-10-23 — Completed paper proof, unconditional Lean proof, leaf check, and capstone axiom audit. Preserved the actual Type II coefficient and uniform cutoff quantifiers.
