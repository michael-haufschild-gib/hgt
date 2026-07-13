# Adams Rankin-Selberg second moment

- **ID:** adams-rankin-selberg-second-moment
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Priority:** FOUNDATIONAL
- **Source:** split from the Rankin-Selberg/`⊗`-power positivity references in `../2-fully-proven/g5-over-fq-deligne-unitarity.md` §2-§3 and the prime-block "positivity for free" clause of `../2-fully-proven/explicit-formula-as-constraint.md` §3; Lean file `formal/GaloisForLFunctions/RHTower/AdamsOperations.lean`
- **Statement:** For finite Satake parameter data, Adams power sums multiply under tensor product; in the self-dual conjugate tensor square the Adams power sum is the norm square of the original power sum, so any finite nonnegative weighted second-moment sum is nonnegative.

## Goal
This banks the exact finite Satake-side algebra behind the Rankin-Selberg second-moment positivity slogan. It does not formalize Deligne's Weil II positivity theorem, global Rankin-Selberg theory, automorphic functoriality, analytic continuation, the explicit formula, prime averages, or transfer from the Satake side to the zero side.

## Paper Proof
For a finite Satake list `alpha`, define the Adams power sum
```
p_m(alpha) = sum_i alpha_i^m.
```
For two lists `alpha`, `beta`, the tensor product has pairwise-product parameters `alpha_i beta_j`, so
```
p_m(alpha tensor beta)
  = sum_(i,j) (alpha_i beta_j)^m
  = sum_(i,j) alpha_i^m beta_j^m
  = (sum_i alpha_i^m) (sum_j beta_j^m)
  = p_m(alpha) p_m(beta).
```
For the conjugate/contragredient list `conj alpha`, conjugation commutes with finite sums and powers, hence
```
p_m(conj alpha) = conj(p_m(alpha)).
```
Therefore the self-dual tensor square satisfies
```
p_m(alpha tensor conj alpha)
  = p_m(alpha) conj(p_m(alpha))
  = normSq(p_m(alpha)).
```
Since every `normSq` is nonnegative, any finite sum
```
sum_{m<N} w_m normSq(p_m(alpha))
```
with `w_m >= 0` is nonnegative.

The determinant identity is the same finite-product reindexing:
```
prod_(i,j) alpha_i beta_j
  = (prod_i alpha_i)^(#beta) (prod_j beta_j)^(#alpha).
```

## Gates
- [x] 0 -> 1  in-progress: exact finite Adams/Rankin-Selberg second-moment algebra extracted from the parent positivity references.
- [x] 1 -> 2  fully-proven: paper proof above, by finite-sum/product reindexing, conjugation through finite sums, and nonnegativity of complex norm squares.
- [x] 2 -> 3  formalized: Lean definitions/theorems `adamsPowerSum`, `adamsPowerSum_tensor`, `adamsPowerSum_conj`, `adamsPowerSum_tensor_selfDual`, `adamsPowerSum_tensor_selfDual_normSq`, `adamsPowerSum_isobaricSum`, `adamsPowerSum_comp`, `adamsPowerSum_one`, `adams_secondMoment_weil_nonneg`, and `satakeDet_tensor`; names checked by scratch file; `#print axioms` reports only standard mathlib axioms.
- [ ] 3 -> 4  publication-ready: cite as the finite Satake-side Rankin-Selberg second-moment certificate.

## Log
- 2026-06-19 — Leaner split this exact finite Adams/Rankin-Selberg algebra from the broader G5/explicit-formula positivity references. The parent cards remain in `2-fully-proven` because Deligne positivity, global Rankin-Selberg theory, explicit-formula transfer, and zero-side period realization are not fully Lean-formalized.
