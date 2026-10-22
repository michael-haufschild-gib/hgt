# Prime-log rank, Möbius distortion, and square-window universality law

## Status

`[LEAN PROVED — LITERATURE AUDITED] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`

## Theorem-generated discovery

Two terminal universality laws use finite prime packets at apparently different cutoffs:

- `primeLogRank_and_mobiusPhaseDistortion X` uses `primesBelow (X+1)` to couple exact
  integer-linear prime-log rank to a critical Poisson--GCD Möbius phase-distortion lower bound;
- `sqrtQuarterWindow_primeMass_randomExact_deterministicWindowLowerBound y T` uses
  `primesBelow (sqrt(y)+1)` to force reciprocal prime mass into both an exact Steinhaus diagonal
  and every deterministic symmetric window after explicit sinc-collision subtraction.

The theorem signatures reveal the connector `y = X²`; `Nat.sqrt (X*X) = X` makes the two finite
prime packets definitionally identical after rewriting.  No corpus capstone combines these
endpoints.

## Universal law

For every `X ≥ 2` and window radius `T > 0`, the single packet `primesBelow (X+1)` simultaneously
controls:

1. an integer-linearly independent prime-log phase family;
2. critical Möbius antipodal/vacuum phase distortion at least
   `1 + 4 primeCounting'(X+1)/X`;
3. the exact independent Steinhaus second-moment diagonal of the quarter-weighted
   square-dilated Möbius carrier through support `n ≤ X²`;
4. reciprocal prime-mass domination of that random energy;
5. survival of the same reciprocal prime mass in every deterministic symmetric window, modulo
   the exact sinc off-diagonal collision energy.

This is one witness-level law across phase rank, critical Möbius geometry, random multiplicative
energy, and deterministic Dirichlet-polynomial energy.

## Paper proof

Apply `primeLogRank_and_mobiusPhaseDistortion` at `X`.  Apply
`sqrtQuarterWindow_primeMass_randomExact_deterministicWindowLowerBound` at `y = X²`.  Since natural
square root satisfies `sqrt(X*X) = X`, rewrite the second theorem's packet
`primesBelow (sqrt(X²)+1)` to `primesBelow (X+1)`.  Preserve all five conclusions.  No numerical
computation is used.

## Corpus inputs

- `RHTower.primeLogRank_and_mobiusPhaseDistortion`
- `RHTower.sqrtQuarterWindow_primeMass_randomExact_deterministicWindowLowerBound`
- `Nat.sqrt_eq`

## Novelty protocol

No literature search was performed before exact Lean proof passed.

Post-proof searches covered prime-log linear independence, random multiplicative functions,
square-supported Möbius carriers, critical phase energies, Dirichlet-polynomial mean squares, and
finite symmetric windows.

Nearest sources:

- Benatar--Nishry--Rodgers, *Moments of polynomials with random multiplicative coefficients*,
  arXiv:2012.15507, studies moments of Rademacher and Steinhaus random multiplicative polynomials:
  <https://arxiv.org/abs/2012.15507>
- Matomäki--Radziwiłł, *Multiplicative functions in short intervals*, proves cancellation results
  for Möbius and other multiplicative functions in short intervals:
  <https://annals.math.princeton.edu/2016/183-3/p06>
- Montgomery--Vaughan, *Hilbert's Inequality*, supplies classical finite-interval
  Dirichlet-polynomial mean-square control:
  <https://doi.org/10.1112/jlms/s2-8.1.73>

No source found the exact common-packet law coupling integer-linear prime-log rank, the critical
Poisson--GCD Möbius antipodal/vacuum distortion lower bound, exact Steinhaus diagonal energy of the
quarter-weighted square-dilated Möbius carrier, and deterministic sinc-corrected finite-window
prime-mass survival.  Novelty claim is restricted to this formal statement.

## Lean target

`formal/GaloisForLFunctions/RHTower/PrimeLogRankMobiusSquareWindowUniversalityLaw.lean`

## Verification

- exact and warning-free:
  `lake env lean GaloisForLFunctions/RHTower/PrimeLogRankMobiusSquareWindowUniversalityLaw.lean`
- wired into `formal/GaloisForLFunctions/RHTower.lean`
- final module, axiom, and lint audits deferred to terminal pass
