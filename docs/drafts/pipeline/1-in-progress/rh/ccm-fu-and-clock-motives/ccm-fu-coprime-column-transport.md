# CCM-FU: actual Abel transport of complete coprime columns

- Type: derived source identity and direct cancellation attempt.
- Status: all five source identities formalized; quantitative signed estimate open.
- Chain: actual divisor source → complete signed O(M) Abel bound → CCM-FU → RH.
  Frontier map read only.

## Question and exact source law

The complete floor-column theorem replaces coprime Möbius sums of
`floor(N/d)` by the number of integers whose prime factors divide the
excluded modulus. It cannot be applied unchanged to divisor-Abel channels.

For any source F, grouping the complete finite hyperbola gives

`sum_(d<=N, gcd(r,d)=1) mu(d) sum_(m<=N/d) F(floor(N/(dm)))`
`=sum_(n<=N, primes(n) subset primes(r)) F(floor(N/n))`.

The literal prime-free divisor defect is the floor-summatory transform
of `psiDefect=psi-N+2gamma`. Hence its complete coprime column is exactly
the prime-supported sum of this same signed defect. Applying the original
square-root time weights gives the coprime Abel head without discarding
any endpoint or replacing a weight.

The exact primitive cross term is

`G_1(M)=sum_(d<=M) C_d(M) H_d(M)-C_1(M)^2`,

where `H_d` is the complete coprime head. The subtracted term is exactly
the only diagonal pair with gcd one. This retains every coprime pair and
every time in the inner column.

## Attempted estimate and the missing step

The successful floor-column estimate uses an indicator/count after
cancellation. The transported actual column instead retains signed
`psiDefect` at every supported quotient. Taking a small-power bound for
the number of supported integers does not bound their signed defect
values at the required scale. In particular r=1 retains the original
complete defect; no gain follows merely from finite support.

The source identity removes the missing transport step but does not
establish an O(M^2) bound on the primitive cross term or the complete
energy. A proof needs cancellation after the signed defect is inserted
in the outer Möbius column, with the nonprimitive gcd sectors retained.
Explicitly, the pairing now exposed to estimation is

`sum_(d<=M) mu(d) U_d(M) sum_(k<M) (sqrt(k+1)-sqrt(k))`
`  * sum_(n<=k, primes(n) subset primes(d)) psiDefect(floor(k/n))`,

where `U_d` is the actual unsigned divisor channel. The `n=1` term
occurs in every inner column. Bounding the supported-index count or
applying an absolute estimate before the outer Möbius sum does not
establish the desired cancellation. The unweighted floor-column bound
therefore has no direct transfer at the required scale. This is a
failed attempt to obtain the quantitative bound from that estimate;
the exact weighted transport remains usable.

No generic positivity, independent averaging, or finite numerical sign
is used. No computation is planned: the transport is algebraically
determined and must be proved symbolically.

## Formal result

Leaf: `RHTower.MobiusDivisorCoprimeColumnTransport`, imported by
`GaloisForLFunctions.RHTower`.

- `coprime_moebius_floor_summatory`: arbitrary-source finite inversion.
- `coprime_moebius_primeFreeDivisorDefect`: exact actual signed source.
- `mobiusDivisorCoprimeHead_eq_supported_abel`: original Abel weights.
- `mobiusDivisorCoprimeHead_succ_sub`: exact terminal increment.
- `mobiusDivisorGcdCross_one_eq_coprimeHeads`: complete primitive pairing.

All are unconditional, with no assumed estimates or added axioms.
Scratch verification and repository leaf compilation passed. The single
axiom audit of these five new theorems reports only `propext`,
`Classical.choice`, and `Quot.sound`. Corpus index refreshed; formal lint
passed. Final `lake build GaloisForLFunctions.RHTower.MobiusDivisorCoprimeColumnTransport`
passed in 75 seconds against existing dependency caches, using a byte-identical
leaf copy and producing a fresh olean. No umbrella or dependency rebuild was
run. Owned scratch files and the audit directory were removed; no owned
Lean/Lake processes remain.

## Corpus evidence

Wide OR searches used the corpus tool's `--any` for coprime columns,
divisor sources, bilinear/double Abel, mixed floors, prime-supported
convolutions and inverse Euler factors. Relevant existing leaves are
`EulerDeletionCoprimeColumnCancellation`, `MoebiusFloorInversion`,
`Sieve.BivariateConvolutionSummatorySwap`,
`CCMFUSuzukiMobiusDivisorAbelProducer`, `RetainedPrimeTopHomothety`, and
`MobiusDivisorAbelGcdCross`. Existing reciprocal smooth-prime transport
has different weights; it is not substituted for the actual Abel source.
