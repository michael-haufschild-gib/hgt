# JAS critical mixed prime-grade incidence law

- **ID:** JAS-CRIT-MIXED-PRIME-GRADE
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** positive survivor of `jas-critical-singleton-fixed-grade-bessel-wall.md`
- **Statement:** Any bounded graded synthesis of critical singleton prime characters has square-summable critical prime mass in every grade fiber, while the canonical injective prime-to-grade assignment admits an explicit isometric synthesis.

## Goal

Replace the fixed-grade JAS no-go by a constructive structural law. Identify exactly what countable
theta multiplicity contributes: grade collisions retain prime-Poisson rank-one accumulation, while
collision-free prime incidence produces orthogonal packets and a bounded completion.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean module `JointAncestryCriticalMixedPrimeGradeIncidence`, leaf build green, axiom audit PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Frozen conjecture

`[CONJECTURE] [NOVELTY UNVERIFIED]` Let `g : Primes -> Nat` assign every prime singleton to a
theta-grade coordinate. If a bounded synthesis maps `e_p` to the critical prime-Poisson singleton
character in amplification coordinate `g(p)`, then for every grade `r`

`sum_{p : g(p)=r} 1/p < infinity`.

Conversely, the canonical bijective assignment `g(p)=natEquivPrimes.symm(p)` has an explicit
isometric synthesis. Thus mixed prime--grade incidence is not merely unexcluded: a collision-free
normalized completion exists.

## Approach

For necessity, project a proposed graded synthesis onto one grade `r` and apply its adjoint to the
constant prime-Poisson vector. The prime-basis coefficient is the Poisson mean
`p^(-1/2+it)` on the fiber `g(p)=r` and zero elsewhere. Parseval forces its squared modulus to be
summable, giving the fiber prime-harmonic condition.

For existence, use the canonical prime enumeration to put distinct primes in distinct grade
coordinates. Every singleton character has `L²` norm one because its pointwise modulus is one and
the prime-Poisson law is a probability measure. Distinct packets lie in distinct Hilbert direct-sum
coordinates, so the family is orthonormal. The standard orthogonal-family synthesis is therefore a
linear isometry from `ell²(Primes)` and sends each coordinate basis vector to the requested packet.

## Dependency-closed paper proof

`[PROVED HERE] [BRIDGE] [NOVELTY UNVERIFIED]`

Fix height `t`, a grade assignment `g`, and a bounded synthesis `T`. For a fixed grade `r`, compose
`T` with the norm-one coordinate projection from the amplified carrier onto grade `r`; call the
result `T_r`. Let `u=1` in critical prime-Poisson `L²`. Parseval applied to `T_r* u` gives

`sum_p |inner(e_p,T_r* u)|² < infinity`.

If `g(p)=r`, adjointness and the exact product-Poisson moment formula identify this coefficient's
modulus with `|p^(-1/2+it)|=p^(-1/2)`. If `g(p)!=r`, coordinate projection makes it zero. Therefore

`sum_{p : g(p)=r} 1/p < infinity`.

Since `r` was arbitrary, every grade fiber has square-summable critical prime mass. In particular,
no synthesis and divergent fiber can coexist.

For the positive statement, put `g0(p)=natEquivPrimes.symm(p)`. The singleton character `chi_p`
has pointwise modulus one, hence `||chi_p||_L²=1` under the probability law. If `p!=q`, injectivity
of `g0` places `chi_p` and `chi_q` in distinct amplification coordinates, so their inner product is
zero. The packet family is orthonormal. Its canonical orthogonal-family linear isometry from
`ell²(Primes)` is bounded and maps `e_p` to the grade-`g0(p)` packet. This proves existence.

All analytic facts used here are unconditional corpus theorems or defining Hilbert-space laws. No
computational evidence enters the proof.

## Hostile audit

- The positive theorem is normalized. It does not assert boundedness after multiplying grade `r`
  by the possibly unbounded actual completed-theta grade norm.
- It constructs bounded Hilbert synthesis, not a multiplicative `C(PrimeTorus)` representation and
  not a closed unbounded Gamma-insertion sewing.
- Fiberwise summability is necessary, not yet proved sufficient for arbitrary collision patterns;
  a uniform fiber bound is the likely exact sufficiency condition.
- Corpus search found direct-sum, orthogonal-family, Bessel, and exact prime-Poisson moment
  infrastructure, but no existing theorem combining them into this JAS incidence law.
- Literature search through 2026-08-28 found general frame partition/selector theory, including
  Bownik's block-diagonal Bessel selector work, but no prime-Poisson critical fiber law or JAS
  application. Standard Hilbert-space ingredients are not claimed as new.

## No-go closure

- **Exact killing theorem/mechanism:** every grade collision fiber must carry finite critical
  harmonic prime mass; any fiber of divergent mass kills bounded synthesis.
- **Strongest positive survivor:** canonical collision-free grade assignment has an explicit
  isometric synthesis.
- **New insight:** countable theta multiplicity repairs the singleton Bessel obstruction exactly by
  recording prime incidence. Mere repetition of grades does not; collision structure is the new
  invariant.
- **Status:** dependency-closed paper proof and Lean formalization complete. Direct check, leaf-only
  build, and axiom audit pass.

## Lean certificate

- Module: `GaloisForLFunctions.RHTower.JointAncestryCriticalMixedPrimeGradeIncidence`
- Necessity: `RHTower.JASCriticalPrimeGradedSingletonSynthesis.fibersSummable`
- Closed obstruction: `RHTower.not_exists_JASCriticalPrimeGradedSingletonSynthesis_with_divergentFiber`
- Positive survivor: `RHTower.jointAncestryCriticalPrimeInjectiveGradeSynthesis_exists`
- Axioms: only `propext`, `Classical.choice`, `Quot.sound`

## Literature audit

- Bownik,
  [*Selector form of Weaver's conjecture, Feichtinger's conjecture, and frame sparsification*](https://arxiv.org/abs/2405.18235)
  (2024), treats general block-diagonal Bessel partitions/selectors, not this arithmetic family.
- Liehr--Taylor--Yu,
  [*Grothendieck's theorem for Bessel sequences*](https://arxiv.org/abs/2608.12280) (2026), treats
  representation and extension of general Bessel sequences, not prime-Poisson grade fibers.

## Log

- 2026-08-28 — created in Stage 1 after corpus search, conjecture freeze, and hostile audit.
- 2026-08-28 — dependency-closed necessity and existence proofs completed; promoted to Stage 2.
- 2026-08-28 — formalized necessity, closed no-go, and canonical isometric survivor; direct check,
  leaf-only build, and axiom audit pass; promoted to Stage 3.
