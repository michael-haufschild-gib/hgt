# Exact compensation on the prime star

- **ID:** RIAC-prime-star
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [RIAC](../1-in-progress/renormalized-intersection-arithmetic-counts.md), critical torsion construction
- **Statement:** Positive diagonal completions of the actual prime-star torsion restriction are classified by a summable, sharp central payment.

## Exact theorem

Put `b(p)=log(p)/√p`, `d(p)=log(p)/(p−1)`. The actual spacing-limit kernel has
`L(1,1)=0`, `L(1,p)=−b(p)`, `L(p,p)=d(p)`, and `L(p,q)=0` for distinct primes.
Replace its central diagonal by `a∈ℝ` and its prime diagonals by arbitrary
`D(p)∈ℝ`. Its finite-star energy is

`E_S(t,x)=a t²+Σ_{p∈S}(D(p)x_p²−2t b(p)x_p)`.

The following are equivalent:

1. `E_S(t,x)≥0` for every finite prime set and every real probe.
2. Every `D(p)>0`, `Σ_p b(p)²/D(p)` converges, and its sum is at most `a`.

The sum is the exact minimal central payment. If it diverges, every finite
`a` has a negative finite probe with `t=1`, `x_p=b(p)/D(p)` on a suitable
finite prime set.

For `D_η(p)=d(p)+p^η`, such a finite payment exists **iff `η>0`**, for every
real `η`. More generally, `D(p)>0` and `D(p)≤C(log p)²` eventually exclude
every finite central payment. This conclusion concerns real finite probes.

## Proof

The prime kernel definition and the tame different give the displayed matrix.
Distinct primes divide neither one another, so their mixed entry vanishes.
The correction changes only the stated diagonals; `primeStarEnergy_eq_torsion`
identifies the energy with that original corrected matrix.

A single leaf with central coefficient zero forces `D(p)≥0`. If `D(p)=0`,
the nonzero mixed coefficient gives a negative probe, hence positivity forces
strict positivity. For positive leaf diagonals, complete squares:

`E_S(t,x)=(a−Σ_{p∈S}b(p)²/D(p))t²`
`             +Σ_{p∈S}D(p)(x_p−t b(p)/D(p))²`.

Taking the displayed minimizing probe proves necessity and sharpness.
Nonnegative finite partial payments are bounded by `a` exactly when their
series converges with total at most `a`. Divergence gives a finite partial
payment exceeding any prescribed `a`, and thus an explicit negative probe.

For `η>0`, the payment density is bounded by
`(log p)² p^(−1−η)`, summable even over all positive integers. For `η≤0`,
`p^η≤1` and `d(p)≤log p`, hence eventually `D_η(p)≤(log p)²`. More generally,
`D(p)≤C(log p)²` gives `C b(p)²/D(p)≥1/p`. Convergence would contradict
divergence of the reciprocal-prime series.

## Lean realization

Module: [PrimeStarCompensation.lean](../../../../formal/GaloisForLFunctions/RenormalizedIntersectionArithmeticCounts/PrimeStarCompensation.lean).

- `primeStarEnergy_eq_torsion`: exact original-matrix comparison.
- `primeStar_complete_classification`: unrestricted diagonal classification.
- `primeStar_minimal_completion`: explicit positive survivor at least payment.
- `primeStar_negative_of_not_summable`: explicit finite negative probes.
- `primeStar_power_completion_iff`: exact power boundary.
- `primeStar_negative_of_log_square_bound`: logarithmic-square obstruction.

Direct `lake --old env lean` module check passes. Fifteen audited declarations
have transitive axioms exactly `[propext, Classical.choice, Quot.sound]`.

## Existing work and scope

Schur complements and completing squares are classical. Corpus already proves
finite-pair indefiniteness and counterterm-rank laws. Its Möbius gluing identity
completes root squares at diagonal `Λ(k)` with a cutoff-dependent Mertens
payment. This theorem classifies arbitrary prime diagonals and uniform finite
central payments for the actual spacing-limit restriction. No priority claim.

`η` measures growth of an added diagonal; it is distinct from the Hilbert
weight `δ` in HHAC. Changing coordinates on a weighted Hilbert space does not
change the signs of finite arithmetic probes. Positive prime-star completion
does not control composite conductor interactions, construct an integer count
or prove the full archimedean compensation.

## Obstruction and positive survivor

- **Excluded class:** positive diagonal repairs retaining the original mixed
  prime row, with eventually logarithmic-square leaf growth and finite central
  payment. Nonlocal corrections are outside this class.
- **Positive survivor:** exact classification for every leaf diagonal,
  constructive minimal payment when summable, and existence precisely above
  zero power for `d(p)+p^η`.
- **New information:** finite central self-energy cannot absorb the critical
  mixed prime row at logarithmic-square cost. A successful compensation must
  alter those interactions or exceed that diagonal class.
