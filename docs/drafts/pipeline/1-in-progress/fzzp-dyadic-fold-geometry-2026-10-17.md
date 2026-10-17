# FZZ-P: dyadic fold geometry of the alternating Nyman–Beurling system

- **ID:** fzzp-dyadic-fold
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean, in construction)
- **Source:** docs/reports/rh-current-frontier-map.md, PM / FZZ-P open node ("control of approximants near t = 0; local (δ,1] density does not control δ↓0"); walls-ledger Wall 1
- **Statement:** The dyadic fold `(Pf)(u) = Σ_{j≥0} 2^{−j} f(2^{−j}u)` on the top octave `(1/2,1]` folds every Fermi generator onto the single direction `−1/(au)`, kills the Haar target, and pairs any `L²` function with every a.e. dyadically self-similar function: `∫_0^1 f w̄ = ∫_{1/2}^1 (Pf) w̄`. Consequences: (i) `L²` witnesses that are a.e. self-similar are exactly the self-similar functions of zero top-octave log-mean (measurable, no continuity); (ii) RH ⟺ every fold-free `L²` function is an `L²`-limit of finite generator combinations; (iii) harmonic penalty: for every finite combination, `∫_0^1|h − Σ c_j φ_{a_j}|² ≥ ½ |Σ_j c_j/a_j|²`, and for a general target the fold mean `∫_{1/2}^1 (Pf)/u` must be matched by `−Σ c_j/a_j`.

## Goal
Isolate the exact Hilbert geometry of the FZZ-P producer problem. `L²(0,1] = ker P ⊕ 𝓢` (fold-free ⊕ self-similar); the whole generator family has a one-dimensional self-similar shadow (`Pφ_a = −1/(au)`); the Haar target lies in `ker P`; the spurious witnesses are `𝓢 ∩ {log-mean = 0}`. The RH content is therefore exactly: the fold-free parts of the generators are dense in `ker P`. The harmonic-sum penalty is the fold shadow of Wall 1 (raw Möbius coefficients pay `½ H_N²`; any admissible coefficient family must have `Σ c_j/a_j → 0`).

Relation to `BiScaleUncertainty`: the penalty is an instance of the producer–consumer duality (Pillar XII) with the consumer `s₀ = P^*(1/u)`; BiScale's compression/Bessel tools give receiver floors only; the fold shows the only non-arithmetic obstruction is one-dimensional.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea
- [ ] 1 → 2  fully-proven: paper proof complete (telescoping fold identity; shell decomposition + a.e. transport + dominated interchange; Hilbert duality)
- [ ] 2 → 3  formalized: Lean module `RHTower/FermiNymanDyadicFoldGeometry.lean`
- [ ] 3 → 4  n/a (RH-only programme)

## Approach
1. `Pφ_a(u) = −1/(au)` on `(1/2,1]`: with `y = 1/(au) ∈ (0,2)`, the terms `2^{−j}({2^j y} − 2{2^{j−1}y})` telescope to `−2{y/2} = −y`.
2. `Ph = 0`: `1 − Σ_{j≥1} 2^{−j} = 0`.
3. Pairing: `(0,1] = ⊔_j (2^{−j−1}, 2^{−j}]`, substitute `t = 2^{−j}u`, use `w(2^{−j}u) = w(u)` a.e., interchange sum and integral (dominated by `∫_0^1 |f||w|`).
4. Spurious classification for measurable `L²` self-similar functions; RH ⟺ fold-free completeness (via `W^⊥ = closure span` and RH ⟹ a.e. self-similar witnesses).
5. Harmonic penalty via Cauchy–Schwarz against the self-similar extension of `1/u`.

## Log
- 2026-10-17 — created in 1-in-progress; Lean construction started.
