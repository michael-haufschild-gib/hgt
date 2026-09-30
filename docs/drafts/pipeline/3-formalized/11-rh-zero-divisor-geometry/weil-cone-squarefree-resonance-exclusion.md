# Weil positivity excludes weights bounded below on the squarefree integers

- **ID:** weil-squarefree-resonance-exclusion
- **Stage:** 3-formalized (paper proof and Lean, 2026-09-30)
- **Type:** THEOREM [P + Lean]
- **Source:** `1-in-progress/hf-positive-hodge-attack/krein-producer-loops.md`, entry L168; makes the dependent-support half of L133 (a) rigorous
- **Lean:** `RHTower.PrimorialResonance.not_forall_squarefree_le_of_weilPositiveFull`,
  `RHTower.PrimorialResonance.not_forall_squarefree_signChar_le_of_weilPositiveFull`,
  `RHTower.PrimorialResonance.not_forall_squarefree_moebius_le_of_weilPositiveFull`,
  `RHTower.PrimorialResonance.weil_twisted_divisor_resonance_bound`,
  `RHTower.PrimorialResonance.not_forall_squarefree_le_of_weilPositive`,
  `RHTower.PrimorialResonance.weil_divisor_resonance_bound`,
  `RHTower.PrimorialResonance.primorial_resonance_inequality`
  (module `RHTower/WeilPositivityPrimorialResonance`; axioms `propext`, `Classical.choice`, `Quot.sound`)

## Statement

**Divisor resonance law.** If `lam` is Weil-positive (polar, level-wise; implied by full-cone
positivity), there is an absolute `C₀` such that for every `N ≥ 1`
`2 Σ_{n ∣ N, n ≥ 2} lam(n) n^{−1/2} d(N/n) ≤ (log N + C₀) d(N)`,
where `d` is the divisor function.

**Theorem.** For every `c > 0` and `δ < 1/2`, no full-cone Weil-positive weight system satisfies
`lam(n) ≥ c n^{−δ}` for all squarefree `n ≥ 2`.

**Twisted form.** The same holds for `χ(n) lam(n) ≥ c n^{−δ}` with any multiplicative sign
`χ(n) = ∏_{p ∣ n} s(p)`, `s(p) = ±1`. The resonator `χ(m) 1_{m ∣ y#}` gives
`Σ_m c(nm) c(m) = 1_{n ∣ N} χ(n) d(N/n)` on squarefree `N`. The case `s ≡ −1` is `μ(n) lam(n) ≥ c n^{−δ}`
(Möbius-signed deviations).

No condition is imposed at non-squarefree `n`, and the values at primes may be arbitrarily small
(deficit against `Λ` need not be summable), so L156, L157 and MUST-571 (log-summable deviations) do
not apply: the deviation `lam − Λ` has `Σ |lam − Λ| n^{−1/2}(1 + log n)^{−J} = ∞` for every `J`.

## Proof

1. **Resonator.** In the multiplicative Toeplitz bound (MUST-498,
   `weil_multiplicativeToeplitz_bound`) take `c(m) = 1_{m ∣ N}`. Then `Σ_m |c(m)|² = d(N)` and
   `Σ_m c(nm) c(m) = 1_{n ∣ N} d(N/n)`, because `nm ∣ N ⟺ m ∣ N/n`. This is the divisor law.
2. **Primorial evaluation.** Put `N = y#` and `a = 1/2 + δ` (reduce to `δ ≥ 0` first). All
   divisors of `y#` are squarefree, so `lam(n) n^{−1/2} ≥ c n^{−a}` on them. The convolution
   `M_a = n^{−a} ⋆ d` is multiplicative with `M_a(p) = 2 + p^{−a}`, and `d(y#) = 2^{π(y)}`. Removing
   the divisor `1` gives
   `2c (∏_{p ≤ y} (1 + p^{−a}/2) − 1) ≤ log(y#) + C₀ ≤ y log 4 + C₀`.
3. **Growth.** `1 + x ≥ e^{x/2}` on `[0, 1]`, so the product is at least
   `exp((1/4) Σ_{p ≤ y} p^{−a}) ≥ exp(π(y) y^{−a}/4) ≥ exp(θ(y) y^{−a}/(4 log y))`. Chebyshev's
   bound `θ(y) ≥ y log 2 − log(y+1) − 2√y log y` makes the exponent at least
   `(log 2/8) y^{1−a}/log y ≥ 2 log y` for large `y`, since `1 − a = 1/2 − δ > 0`. The left side then
   exceeds `2c(y² − 1)`, which beats `y log 4 + C₀`. ∎

## What is new

- **Rigorous form of L133 (a).** L133 recorded, heuristically, that producers whose support carries
  mass on a multiplicatively dense set are killed by amplification. The theorem proves it for the
  squarefree integers with the sharp exponent range `δ < 1/2` of the primorial resonator (at
  `δ = 1/2` the product is `≍ (log y)^{1/2}` and the method gives nothing).
- **A dense-support exclusion outside the summable classes.** The rigidity theorems of
  L156–L167 and MUST-570/571 need the deviation to be summable against some logarithmic weight, or
  one-sided relative to `Λ`. This class is dense (`Σ_{n∈S} n^{−1/2} = ∞`), has no summability,
  and is sign-structured only on the squarefree integers.
- **Consequence for producers.** A producer cannot keep a uniform positive floor (even `c n^{−δ}`,
  `δ < 1/2`) on the squarefree integers. For a nonnegative producer (for example the von Mangoldt
  function of any integer-valued Beurling prime system) the divisor law is a quantitative sparsity
  condition: `Σ_{n ∣ y#, n ≥ 2} lam(n) n^{−1/2} 2^{−ω(n)} ≤ (θ(y) + C₀)/2`. A Cramér-type random
  prime set (each `n` independently with probability `1/log n`) violates it for large `y`, since the
  left side is then of order `∏_{p ≤ y}(1 + p^{−1/2}/2)` [P, heuristic in expectation].
- **Novelty audit.** The technique is the resonance/GCD-sum lower bound for multiplicative Toeplitz
  matrices (Hilberdink 2009; Bondarenko–Seip; Aistleitner–Berkes–Seip). The new content is the
  pairing with Weil positivity through MUST-498 and the resulting exclusion; no literature statement
  of this form was found. Verdict: BRIDGE-level technique, new exclusion class.

## Gates
- [x] 0 → 1: mechanism (primorial divisor resonator)
- [x] 1 → 2: paper proof above
- [x] 2 → 3: Lean, `lake build` green, wired into `RHTower`, standard axioms
- [ ] 3 → 4: not planned (no manuscripts)

## Log
- 2026-09-30: L168. Module about 610 lines, including the sign-twisted law.
