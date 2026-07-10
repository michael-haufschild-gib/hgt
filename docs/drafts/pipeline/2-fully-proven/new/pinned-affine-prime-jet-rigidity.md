# Prime first jets retain labels in the pinned-affine quotient

- **ID:** pinned-affine-prime-jet-rigidity
- **Stage:** 2-fully-proven
- **Type:** label-sensitive source theorem / first surviving attachment
- **Status:** `[PROVED ON PAPER + LEAN]`

## Claim

The constant-source quotient forgets every finite source label, so retain the first germ derivative.
At a point `rho`, define the truncated prime germ

`J_p(rho;X) = p^(-rho) * (1 - log(p) X) mod X^2`.

For distinct positive bases `p != q`, the two classes `J_p` and `J_q` are linearly independent in
the order-two pinned-affine defect quotient at every complex point `rho`.  Equivalently,

`a[J_p] + b[J_q] = 0  iff  a=b=0`.

The constant coefficient gives `a p^(-rho)+b q^(-rho)=0`; the first coefficient gives the same
relation weighted by `log p, log q`.  Eliminating one equation leaves
`a p^(-rho)(log q-log p)=0`.  Prime amplitudes never vanish and distinct positive bases have distinct
logs, so both coefficients vanish.

## Attack and verdict

- `[BRIDGE]` The two-by-two Vandermonde argument is standard linear algebra.
- `[PROVED NATIVE SURVIVOR]` The argument remains valid after quotienting by every pinned affine
  realization because the descended Fitting boundary recovers the full order-two polynomial jet.
- `[LOCATION TEST]` The theorem holds for every `rho`, so its rigidity is label arithmetic rather
  than an encoded zero or line condition.
- `[HONEST LIMIT]` Order two is the smallest nonconstant jet.  The general `k`-prime/order-`k`
  Vandermonde theorem and an actual completed infinite-source class remain open.

## Formal theorem surface

- `oneSlotPolynomialDefect` and `fittingBoundaryClass_oneSlotPolynomial_eq` extend the exact one-slot
  calculation from constants to arbitrary polynomial sources.
- `primeFirstJet`, `primeFirstJet_coeff_zero`, and `primeFirstJet_coeff_one` define and compute the
  truncated exponential germ.
- `twoPrimeFirstJetPinnedAffineClass` is its two-source quotient class.
- `twoPrimeFirstJetPinnedAffineClass_eq_zero_iff` proves exact independence for distinct positive
  bases at every point.
- `twoPrimeFirstJetPinnedAffineClass_prime_eq_zero_iff` gives the prime-labelled specialization.
- `primeDerivativeJet` and `finitePrimeDerivativeJetPolynomial` package the first `k` derivative
  moments of an arbitrary finite base family.
- `finitePrimeDerivativeJetPinnedAffineClass_eq_zero_iff` proves the full order-`k` Vandermonde
  theorem for every injective positive base family.
- `finitePrimeDerivativeJetPinnedAffineClass_prime_eq_zero_iff` gives the arbitrary finite-prime
  specialization.
- `archimedeanDerivationMoment` isolates the fixed coefficient-extraction moment sequence
  `delta_(n,1)`.
- `no_finitePrimeMoments_eq_archimedeanDerivationMoment` proves that no finite positive-base packet
  realizes the derivation sequence; the prime-labelled specialization states the exact weld case.

The implementation is
`formal/GaloisForLFunctions/RHTower/PinnedAffinePrimeJetRigidity.lean` and is registered in the
`RHTower` umbrella.

## New open core

`[OPEN CORE]` The general finite-prime Vandermonde theorem and finite-prime/archimedean separation
are now proved.  The derivation moment is an explicit fixed constraint outside every finite prime
span—no limit construction is required.  Attach this archimedean class to the pinned-affine quotient
through the completed prime--archimedean weld, and determine the compatibility equation imposed on
the infinite prime source.

The completed step must explain how the actual arithmetic datum pairs this finite-prime-inaccessible
derivation class with the infinite prime side without becoming a carrier, cutoff, or limit flow.  A
finite truncation cannot be the source of the cancellation.

## Novelty and significance gates

- **BRIDGE INFRASTRUCTURE:** the two-by-two Vandermonde elimination is standard.
- **NOVEL NATIVE RESULT:** arbitrary finite families of distinct prime derivative jets are proved
  independent inside the new universal quotient, uniformly in the germ point.  This closes the
  complete finite-support Vandermonde tower, not only the first two-prime case.
- **SIGNIFICANT:** the live attachment moves from scalar incidence to prime-log jet rigidity, a
  constraint unavailable to the constant-source interface; the archimedean derivation is now
  formally separated from every finite prime packet.
- **NON-TAUTOLOGICAL:** the theorem assumes neither a xi zero nor a critical-line relation and holds
  for every complex point.

## Verification scope

The new module compiles directly and its exact module target builds.  The capstone axiom footprints
are `[propext, Classical.choice, Quot.sound]`.  No root build or project-wide lint was run.
