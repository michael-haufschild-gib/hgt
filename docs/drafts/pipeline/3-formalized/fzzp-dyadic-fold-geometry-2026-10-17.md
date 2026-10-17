# FZZ-P: dyadic fold geometry of the alternating Nyman–Beurling system

- **ID:** fzzp-dyadic-fold
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** docs/reports/rh-current-frontier-map.md, PM / FZZ-P open node ("control of approximants near t = 0; local (δ,1] density does not control δ↓0"); walls-ledger Wall 1
- **Statement:** The dyadic fold `(Pf)(u) = Σ_{j≥0} 2^{−j} f(2^{−j}u)` on the top octave `(1/2,1]` folds every Fermi generator onto the single direction `−1/(au)`, kills the Haar target, and pairs any `L²` function with every a.e. dyadically self-similar function: `∫_0^1 f w̄ = ∫_{1/2}^1 (Pf) w̄`. Consequences: (i) `L²` witnesses that are a.e. self-similar are exactly the self-similar functions of zero top-octave log-mean (measurable, no continuity); (ii) RH ⟺ every fold-free `L²` function is an `L²`-limit of finite generator combinations; (iii) harmonic penalty: for every finite combination, `∫_0^1|h − Σ c_j φ_{a_j}|² ≥ ½ |Σ_j c_j/a_j|²`, and for a general target the fold mean `∫_{1/2}^1 (Pf)/u` must be matched by `−Σ c_j/a_j`.

## Goal
Isolate the exact Hilbert geometry of the FZZ-P producer problem. `L²(0,1] = ker P ⊕ 𝓢` (fold-free ⊕ self-similar); the whole generator family has a one-dimensional self-similar shadow (`Pφ_a = −1/(au)`); the Haar target lies in `ker P`; the spurious witnesses are `𝓢 ∩ {log-mean = 0}`. The RH content is therefore exactly: the fold-free parts of the generators are dense in `ker P`. The harmonic-sum penalty is the fold shadow of Wall 1 (raw Möbius coefficients pay `½ H_N²`; any admissible coefficient family must have `Σ c_j/a_j → 0`).

Relation to `BiScaleUncertainty`: the penalty is an instance of the producer–consumer duality (Pillar XII) with the consumer `s₀ = P^*(1/u)`; BiScale's compression/Bessel tools give receiver floors only; the fold shows the only non-arithmetic obstruction is one-dimensional.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea
- [x] 1 → 2  fully-proven: telescoping fold identity; shell decomposition + a.e. transport + dominated interchange; Hilbert duality; weighted Cauchy–Schwarz across shells
- [x] 2 → 3  formalized: `formal/GaloisForLFunctions/RHTower/FermiNymanDyadicFoldGeometry.lean` (wired into `RHTower.lean`; `lake env lean` clean; `#print axioms` = propext, Classical.choice, Quot.sound; formal lint passed 2026-10-17)
- [ ] 3 → 4  n/a (RH-only programme)

## Lean theorems (all unconditional)
- `hasSum_dyadicFold_fermiNymanGen` — `Pφ_a(u) = −1/(au)` on `(1/2,1]`, `a ≥ 1`.
- `hasSum_dyadicFold_dyadicHaar` — `Ph = 0`; `hasSum_dyadicFold_of_selfSimilar`, `dyadicFold_ae_eq_of_ae_selfSimilar` — `Pw = 2w`.
- `integral_mul_conj_eq_integral_dyadicFold` — fold pairing identity `∫_0^1 f w̄ = ∫_{1/2}^1 (Pf) w̄` for a.e. self-similar `L²` `w`.
- `integral_fermiNymanGen_mul_conj_of_ae_selfSimilar`, `isL2FermiWitness_iff_dyadicLogMean_eq_zero_of_ae_selfSimilar` — measurable spurious classification.
- `exists_fermiNymanCombination_approx_of_orth_witness` — witness-annihilated `L²` functions are approximable (general Hilbert duality lemma).
- `riemannHypothesis_iff_foldFree_approximable` — RH ⟺ fold-free completeness.
- `norm_sq_fold_pairing_le` — fold–Cauchy–Schwarz; `dyadicHaar_approximation_harmonic_penalty` — `‖Σ c_j/a_j‖²/2 ≤ ∫_0^1 |h − Σ c_j φ_{a_j}|²`.
- `selfSimilarExtension`, `dyadicShellIndex` and their laws; `integral_normSq_selfSimilarExtension_inv = 2`, `dyadicLogMean_selfSimilarExtension_inv = 1`.
- `integral_normSq_dyadicFold_le` — `∫_{1/2}^1 |PF|² ≤ 2 ∫_0^1 |F|²` (bounded `F`); `dyadicFold_sub_combination`; `integral_normSq_sub_combination_ge_half_fold` — full self-similar shadow penalty.
- `riemannHypothesis_iff_forall_l2FermiWitness_ae_selfSimilar`, `riemannHypothesis_iff_forall_l2FermiWitness_mass_le_two_mul`, `riemannHypothesis_iff_forall_l2FermiWitness_dyadicLogMean_eq_zero`.

## What this changes in the open core
- The producer problem has an exact orthogonal split: `L²(0,1] = ker P ⊕ 𝓢`. The generators' `𝓢`-component is one-dimensional (`−1/(au)`), fully understood and already matched by the Haar target (`Ph = 0`). The entire RH content is the density of the fold-free generator parts `φ_a + s₀/(2a)` in `ker P`.
- The harmonic sum `Σ c_j/a_j` is the dyadic-average germ shadow of an approximant (`Pf = bulk partial fold + germ tail`); it is an unconditional *necessary* condition on every coefficient family (`Σ c_j/a_j → 0`). For raw Möbius coefficients it is `½ H_N²` — weaker than the known tail floor `(N+1)H_N²/6`, consistent with the main error living in `ker P` (the Chebyshev dyadic difference `2ψ(x/2) − ψ(x)` is fold-free).
- Wall 1 is untouched as expected: no fold argument can bound the `ker P`-error, which is the square-root cancellation of `2ψ(x/2) − ψ(x)` in mean square. BiScale's compression/Bessel tools produce receiver floors (they are instances of the fold–Cauchy–Schwarz / producer–consumer duality), not producer upper bounds.

## Approach
1. `Pφ_a(u) = −1/(au)` on `(1/2,1]`: with `y = 1/(au) ∈ (0,2)`, the terms `2^{−j}({2^j y} − 2{2^{j−1}y})` telescope to `−2{y/2} = −y`.
2. `Ph = 0`: `1 − Σ_{j≥1} 2^{−j} = 0`.
3. Pairing: `(0,1] = ⊔_j (2^{−j−1}, 2^{−j}]`, substitute `t = 2^{−j}u`, use `w(2^{−j}u) = w(u)` a.e., interchange sum and integral (dominated by `∫_0^1 |f||w|`).
4. Spurious classification for measurable `L²` self-similar functions; RH ⟺ fold-free completeness (via `W^⊥ = closure span` and RH ⟹ a.e. self-similar witnesses).
5. Harmonic penalty via Cauchy–Schwarz against the self-similar extension of `1/u`.

## Log
- 2026-10-17 — created in 1-in-progress; Lean construction started.
- 2026-10-17 — all statements proved in Lean, module wired, lint green; moved to 3-formalized.
