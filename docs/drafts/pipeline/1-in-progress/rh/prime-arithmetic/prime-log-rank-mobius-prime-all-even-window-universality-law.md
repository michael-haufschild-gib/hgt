# Prime-log rank, Möbius distortion, and prime all-even-window universality law

- **ID:** prime-log-rank-mobius-prime-all-even-window-universality
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** Lean-corpus closure of prime-log rank, critical Möbius distortion, iterated
  Dirichlet convolution, exact Steinhaus even moments, and finite-window sinc transference
- **Statement:** At every positive order `k`, one finite prime packet carries independent
  logarithmic phases, rank-controlled Möbius distortion, full reciprocal-prime mass in its exact
  random `2k`-moment, and the same mass in every shifted deterministic `2k`-moment window modulo
  explicit collision energy, with sharper sinc energy on symmetric windows and long-window
  convergence to the exact random moment.

## Goal

Replace the isolated fourth-moment packet law by its maximal all-even-moment statement and prove
formally that the fourth-moment law is the `k=2` rung.

## Gates

- [x] 0 → 1 in-progress: source-pure theorem generated from verified Lean endpoints
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [ ] 2 → 3 formalized: tree source and exact `lake env lean` passed; final axiom audit pending
- [ ] 3 → 4 publication-ready: post-proof literature audit complete; final audit pending

## Corpus inputs

- `powSupport`, `powConv`, `integral_normPow_dpoly`
- `evenMoment_symmetric_independence_error_le`
- `primeMass_le_pow_sum_of_forced`
- `primeLogRank_and_mobiusPhaseDistortion`
- `primeLogRank_mobiusDistortion_primeQuarterFourthWindow`

## Proof

`[PROVED HERE]` For a finite prime set `P`, prove inductively that
`p^k ∈ powSupport P k` and that the
`k`-fold convolution fiber over `p^k` is unique: in the final factorization `j q=p^(k+1)`,
primality forces `q=p`, cancellation forces `j=p^k`, and induction closes.  Therefore
`powConv a P k (p^k)=a(p)^k`.

Use `a_k(p)=p^(-1/(2k))`.  Real-power arithmetic gives
`powConv a_k P k (p^k)=p^(-1/2)`.  The abstract power-supported prime-mass theorem injects the
full reciprocal-prime sum into the `k`-fold convolution diagonal.  Existing exact random
`2k`-moment, arbitrary shifted-window error, and symmetric sinc-error theorems transfer that lower
mass to every deterministic window and give the sharper collision energy on `[-T,T]`.  Finally
the Bohr identity gives convergence of the long deterministic window to the exact random moment.
Finally add the existing rank/distortion conclusions for the same `P`.

No numerical computation is used.

## Lean certificate

- Module:
  `GaloisForLFunctions.RHTower.PrimeLogRankMobiusPrimeAllEvenWindowUniversalityLaw`
- Main theorem:
  `RHTower.primeLogRank_mobiusDistortion_primeAllEvenWindow`
- Reusable connectors:
  `RHTower.prime_pow_mem_powSupport`,
  `RHTower.powConv_primePower`,
  `RHTower.powConv_primeEvenMomentCoeff_primePower`
- Exact source check:
  `lake env lean GaloisForLFunctions/RHTower/PrimeLogRankMobiusPrimeAllEvenWindowUniversalityLaw.lean`
  passed warning-free on 2026-07-23.
- Imported by `GaloisForLFunctions/RHTower.lean`.
- Final axiom audit, explicit Law337 specialization connector, and module build deferred to final
  audit because source-only checks cannot import the new module before its `.olean` exists.

## Novelty protocol

No literature search before exact Lean proof.

## Post-proof literature audit

Performed only after exact Lean source check passed.

- Harper, Nikeghbali, and Radziwiłł, *A note on Helson's conjecture on moments of random
  multiplicative functions* ([arXiv:1505.01443](https://arxiv.org/abs/1505.01443)), proves
  asymptotics for even integer moments of broad random multiplicative sums, not this exact
  order-normalized prime packet or deterministic finite-window remainder.
- Heap and Lindqvist, *Moments of random multiplicative functions and truncated characteristic
  polynomials* ([arXiv:1505.03378](https://arxiv.org/abs/1505.03378)), gives asymptotic `2k`
  moments for Steinhaus sums, without the exact `p^k` singleton-fiber lower mass or its
  rank/Möbius synchronization.
- Conrey and Gamburd, *Pseudomoments of the Riemann zeta-function and pseudomagic squares*
  ([arXiv:math/0307213](https://arxiv.org/abs/math/0307213)), computes integral moments of zeta
  partial sums and their leading constants; it does not give an every-finite-window sinc
  inequality for the order-dependent prime coefficient `p^(-1/(2k))`.
- Bondarenko, Brevig, Saksman, Seip, and Zhao, *Pseudomoments of the Riemann zeta function*
  ([arXiv:1701.06842](https://arxiv.org/abs/1701.06842)), studies asymptotic pseudomoment growth,
  not simultaneous prime-log rank, Möbius phase distortion, and exact finite-order
  random/deterministic transference.

No exact source was found combining all orders `k`, the normalized prime weight
`p^(-1/(2k))`, singleton `p^k` convolution fibers, reciprocal-prime lower mass in exact
Steinhaus `2k` moments, arbitrary shifted-window collision survival, sharper symmetric sinc
survival, exact long-window convergence, prime-log independence, and critical Möbius distortion.
Door 2 remains open rather than claimed closed.

## Log

- 2026-07-23 — Law337 exact proof exposed the unused arbitrary-order `powConv`/even-sinc tower.
- 2026-07-23 — induction on unique prime-power convolution fibers closed; exact Lean source
  passed and umbrella import added.
- 2026-07-23 — post-proof literature audit found asymptotic random and deterministic moment
  theories, not the exact all-order synchronized law.
