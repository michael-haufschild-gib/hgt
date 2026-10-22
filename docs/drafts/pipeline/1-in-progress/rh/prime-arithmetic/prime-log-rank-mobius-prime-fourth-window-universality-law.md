# Prime-log rank, Möbius distortion, and prime fourth-window universality law

- **ID:** prime-log-rank-mobius-prime-fourth-window-universality
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** Lean-corpus closure of prime-log rank, critical Möbius phase distortion,
  multiplicative convolution, and finite-window sinc transference
- **Statement:** Every finite prime packet simultaneously has independent logarithmic phase
  directions, rank-controlled critical Möbius distortion, an exact Steinhaus fourth-moment
  convolution diagonal carrying full reciprocal-prime mass, and deterministic fourth-window
  survival modulo explicit sinc-collision energy.

## Goal

Identify the same `primesBelow (N+1)` packet across its algebraic phase rank, critical Möbius
geometry, random multiplicative fourth moment, and deterministic finite-window fourth moment.

## Gates

- [x] 0 → 1 in-progress: source-pure theorem generated from verified Lean endpoints
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [ ] 2 → 3 formalized: tree source and exact `lake env lean` passed; final axiom audit pending
- [ ] 3 → 4 publication-ready: post-proof literature audit complete; final audit pending

## Corpus inputs

- `primeLogRank_and_mobiusPhaseDistortion`
- `mixedPowerSupportedPrimeMass_randomExact_deterministicWindowLowerBound`
- `dpolyConv`
- `Nat.prime_dvd_prime_iff_eq`

## Proof

`[PROVED HERE]` Let `P = primesBelow (N+1)` and put `a(p)=p⁻¹/⁴`.  For each `p∈P`, a pair
`(q,r)∈P×P` lies over the convolution label `p²` exactly when `qr=p²`.  Since `p,q,r` are
prime, Euclid's lemma and prime divisibility force `q=p=r`.  Thus the convolution fiber over
`p²` is the singleton `(p,p)` and

`dpolyConv a a P P (p²) = p⁻¹/⁴ p⁻¹/⁴ = p⁻¹/²`.

The mixed power-supported finite-window theorem at power two and forcing constant one now gives
an exact Steinhaus convolution diagonal, reciprocal-prime lower mass in the random squared
product (the fourth moment of the prime carrier), and the deterministic symmetric fourth-window
lower bound after the explicit sinc-collision deduction.  The existing prime-log/Möbius theorem
supplies independent logarithmic phases and the rank-controlled critical distortion for exactly
the same packet.  Their shared packet gives the claimed universal law.

No numerical computation is used.

## Lean certificate

- Module:
  `GaloisForLFunctions.RHTower.PrimeLogRankMobiusPrimeFourthWindowUniversalityLaw`
- Main theorem:
  `RHTower.primeLogRank_mobiusDistortion_primeQuarterFourthWindow`
- Exact source check:
  `lake env lean GaloisForLFunctions/RHTower/PrimeLogRankMobiusPrimeFourthWindowUniversalityLaw.lean`
  passed warning-free on 2026-07-23.
- Imported by `GaloisForLFunctions/RHTower.lean`.
- Final axiom audit and module build deferred to final audit.

## Novelty protocol

No literature search before exact Lean proof.

## Post-proof literature audit

Performed only after exact Lean source check passed.

- Heap and Lindqvist, *Moments of random multiplicative functions and truncated characteristic
  polynomials* ([arXiv:1505.03378](https://arxiv.org/abs/1505.03378)), proves asymptotic even
  moments for broad Steinhaus sums and discusses the weight `σ=1/2`; it does not identify this
  finite prime packet, its exact `p²` convolution fibers, finite sinc remainder, or Möbius
  distortion.
- Hofmann, Hoganson, Menon, Verreault, and Zaman, *Moments of random multiplicative functions
  over function fields* ([arXiv:2408.08309](https://arxiv.org/abs/2408.08309)), gives an exact
  fourth-moment formula in the function-field setting and asymptotic integer analogues, not this
  exact finite integer prime-support transference law.
- Benatar, Nishry, and Rodgers, *Moments of polynomials with random multiplicative coefficients*
  ([arXiv:2012.15507](https://arxiv.org/abs/2012.15507)), studies moments of Steinhaus and
  Rademacher multiplicative polynomials, without the simultaneous prime-log rank, critical
  Möbius phase distortion, and deterministic sinc-window conclusion.

No exact source was found combining all five components: finite prime-log independence,
rank-controlled critical Möbius distortion, singleton prime-square convolution fibers, exact
Steinhaus fourth-moment diagonal, and every positive symmetric deterministic fourth window with
its explicit sinc-collision deduction.  Door 2 remains open rather than claimed closed.

## Log

- 2026-07-23 — whole-corpus terminal scan exposed the unused connector from the finite prime
  packet to mixed convolution at prime-square labels.
- 2026-07-23 — paper proof closed by prime-factor uniqueness; scratch Lean certificate passed.
- 2026-07-23 — exact source check passed, umbrella import added, and post-proof literature audit
  found adjacent random-multiplicative moment results but no exact combined law.
