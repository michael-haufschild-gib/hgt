# JAS critical singleton fixed-grade Bessel wall

- **ID:** JAS-CRIT-SINGLETON-FIXED-GRADE
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md` route JAS; current prime-support-synchronized sewing burden
- **Statement:** At the critical prime-Poisson state, no bounded complex-linear synthesis sends every orthonormal prime-support coordinate to its singleton prime character inside one fixed nonzero completed-theta grade.

## Goal

Kill the fixed-grade prime-support completion of JAS before attempting a full sewing. The result is
source-pure: it uses the actual critical prime-Poisson law, actual singleton prime characters, and a
fixed actual nonzero completed-theta grade. It makes no assumption about zeta zeros or RH.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorem `not_JASCriticalPrimeThetaFixedGradeSingletonSynthesis`, `lake build` green, axiom audit PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Frozen conjecture

`[CONJECTURE] [NOVELTY UNVERIFIED]` For every height `t` and completed-theta grade `r`, there is no
bounded complex-linear map from `ell²(Primes)` to the critical prime-Poisson `L²` carrier whose
value on the prime coordinate `e_p` is

`norm(completedThetaGrade(r)) * singletonPrimeCharacter(p)`.

Equivalently, placing all singleton prime-support states in one fixed theta grade cannot complete
the algebraic JAS packet system to a bounded Hilbert synthesis.

## Approach

Let `u=1` in critical prime-Poisson `L²`. If bounded synthesis `T` existed, the bounded functional
`x ↦ inner(u,T x)` would have square-summable coefficients on the orthonormal prime basis. The
coefficient at `p` is the exact Poisson moment `p^(-1/2+it)`, multiplied by the fixed nonzero theta
norm. Its squared modulus is a fixed positive scalar times `1/p`. Euler divergence contradicts
square summability. Divide out the nonzero theta scalar to reduce to the unweighted statement.

## Dependency-closed paper proof

`[PROVED HERE] [BRIDGE] [NOVELTY UNVERIFIED]`

Fix height `t` and completed-theta grade `r`. Let `mu` be the critical prime-Poisson product law,
let `chi_p` be the singleton coordinate character, and let `c_r` be the norm of the actual
completed-theta grade. Existing corpus theorems give `c_r != 0` and

`integral chi_p dmu = p^(-1/2+it)`.

Assume bounded synthesis `T` maps the prime orthonormal basis vector `e_p` to the amplified vector
supported at grade `r` with value `c_r chi_p`. Compose `T` with bounded projection onto grade `r`
and multiply by `c_r^(-1)`. This produces bounded `T0 : ell²(Primes) -> L²(mu)` satisfying
`T0 e_p = chi_p` for every prime `p`.

Let `u=1` in `L²(mu)`. The adjoint vector `T0* u` belongs to `ell²(Primes)`, so Parseval/Bessel
forces

`sum_p |inner(e_p,T0* u)|² < infinity`.

Adjointness and Hermitian symmetry give

`|inner(e_p,T0* u)| = |inner(u,T0 e_p)| = |integral chi_p dmu| = p^(-1/2)`.

Hence `sum_p 1/p < infinity`, contradicting Euler's divergence theorem. Therefore `T` does not
exist. All inputs named above already have unconditional Lean proofs in the corpus; no numerical
experiment or unproved analytic assertion enters the argument.

## Hostile audit

- Removing the completed-theta factor does not weaken the obstruction: a fixed nonzero scalar is
  invertible in the category of bounded complex-linear maps.
- Passing from finite Gram matrices to a closed completion cannot help when the requested map is
  everywhere-defined and bounded: its constant-vector observer is automatically an `ell²` vector.
- The argument does not exclude an unbounded closed relation or a prime-dependent grade assignment.
  Those are the exact surviving architectures, not hidden conclusions of this theorem.
- Corpus search found the exact prime-Poisson moment law, the exact critical summability wall, and
  Bessel/Parseval infrastructure, but no theorem coupling them to JAS singleton support synthesis.
- Literature search through 2026-08-28 found general Bessel-sequence and commuting weighted-shift
  theory, but no prime-Poisson/JAS fixed-grade classification. The Hilbert-space mechanism is
  standard; novelty claim is limited to the exact arithmetic sewing obstruction.

## No-go closure

- **Exact killing theorem/mechanism:** constant-vector observation turns bounded fixed-grade
  singleton synthesis into square summability of the critical prime means, contradicting
  divergence of the prime harmonic series.
- **Strongest positive survivor:** prime-dependent mixed prime--grade incidence is not killed.
  In particular, separating primes into orthogonal grade coordinates removes the common-grade
  rank-one accumulation responsible for the contradiction.
- **New insight:** completed-theta multiplicity is useful only when it records prime incidence.
  Repeating one theta grade, or tensoring every prime character with the same nonzero grade, cannot
  supply the missing JAS source-linear completion.
- **Status:** formalized in
  `GaloisForLFunctions.RHTower.JointAncestryCriticalSingletonFixedGradeBesselWall`; direct Lean check
  and exact leaf build pass. Axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Literature audit

- Hartz, [*Von Neumann's inequality for commuting weighted shifts*](https://arxiv.org/abs/1508.01260)
  (2015), proves general scalar
  commuting weighted shifts admit commuting unitary dilations. Therefore abstract dilation
  existence is not a novel JAS route and does not address prime-Poisson bounded landing.
- Liehr--Taylor--Yu,
  [*Grothendieck's theorem for Bessel sequences*](https://arxiv.org/abs/2608.12280) (2026), studies general Bessel
  representation/extension. It does not identify this prime-Poisson critical obstruction.

## Log

- 2026-08-28 — created directly in Stage 1 after corpus search and conjecture freeze.
- 2026-08-28 — hostile audit passed; dependency-closed paper proof completed; promoted to Stage 2.
- 2026-08-28 — formalized exact theorem in Lean; leaf build and axiom audit passed; promoted to Stage 3.
