# JAS critical mixed prime-grade uniform Bessel classification

- **ID:** JAS-CRIT-MIXED-UNIFORM-BESSEL
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** strongest open core exposed by `jas-critical-mixed-prime-grade-incidence-law.md`
- **Statement:** Critical graded singleton synthesis exists exactly when critical prime mass is uniformly bounded across grade fibers.

## Goal

Close arbitrary-collision Hilbert synthesis classification left open by fiberwise necessity. Separate
genuine countable-grade repair from hidden unbounded accumulation.

## Gates

- [x] 0 → 1  in-progress: corpus search, frozen statement, proof architecture, hostile audit
- [ ] 1 → 2  fully-proven: dependency-closed proof
- [ ] 2 → 3  formalized: direct check, leaf build, axiom audit, umbrella import
- [ ] 3 → 4  publication-ready: standalone theorem, proof, certificate, Door-2 audit

## Frozen conjecture

`[CONJECTURE] [NOVELTY UNVERIFIED]` Fix height `t` and grading `g : Primes -> Nat`. A bounded
synthesis sending the prime basis vector `e_p` to the critical singleton character in grade `g(p)`
exists if and only if there is `B >= 0` such that, for every grade `r`,

`sum_{p : g(p)=r} |p^(-1/2+it)|^2 <= B`.

Equivalently, grade fibers have uniformly bounded prime-harmonic mass. Pointwise fiber
summability alone is insufficient unless these masses are uniformly bounded.

## Corpus basis and proof architecture

- `JASCriticalPrimeGradedSingletonSynthesis.fibersSummable` supplies pointwise necessity.
- `besselFamilySynthesisOperator` converts a proved Bessel estimate into bounded synthesis.
- Exact product-Poisson moments give the covariance decomposition
  `chi_p = (chi_p - lambda_p * 1) + lambda_p * 1`.
- Centered singleton characters are pairwise orthogonal; their packet family contributes a uniform
  orthogonal Bessel term.
- Mean packets are block-rank-one. Uniform fiber mass bounds their finite analysis sums after
  regrouping by grades.

Necessity should strengthen the existing adjoint argument: each grade projection applied to the
constant observer gives a coefficient vector of norm at most `||T||`, so all fiber masses are
bounded by `||T||^2`.

## Hostile audit

- Claim concerns normalized critical singleton packets only, not actual completed-theta grade
  weights, multiplicativity, Gamma insertion, or Xi source sewing.
- Quantitative Bessel constant need not be sharp; target is exact existence classification.
- Main formal risk is infinite fiber regrouping. Proof will use finite analysis sums and only pass
  to `tsum` after a uniform finite-set bound.
- Corpus contains generic Bessel synthesis and fiber-sum infrastructure, but no exact
  prime-Poisson uniform-fiber classification.
- Literature search through 2026-08-28 found general Gram/Bessel and block-diagonal selector
  theory, including Bownik (2024), but no arithmetic prime-Poisson instance or this exact
  classification. Standard Hilbert-space ingredients are not claimed as novel.

## Literature audit

- Bownik, [*Selector form of Weaver's conjecture, Feichtinger's conjecture, and frame
  sparsification*](https://arxiv.org/abs/2405.18235) (2024).
- Osgooei--Rahimi, [*Gram matrix associated to controlled frames*](https://arxiv.org/abs/1709.05641)
  (2017).

## Log

- 2026-08-28 — frozen after corpus and literature audits; exact uniform-fiber iff selected as hard
  open core.
