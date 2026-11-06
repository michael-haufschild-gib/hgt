# Single finite trigonometric oscillation of the Chebyshev prime error

- **ID:** pnt-error-single-finite-oscillation
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** docs/reports/review-0611/obstacles-summary.md §2.9 (tasks A31, B81, B82, F12)
- **Statement:** For every `β > 1/2`, `η > 0`, and nonzero finite trigonometric polynomial `T(u) = ∑_{j ∈ J} c_j e^{i γ_j u}` with distinct real frequencies `γ_j`, `ψ(x) - x ≠ x^β T(log x) + O(x^{β - η})` as `x → ∞`.

## Goal
Resolve §2.9 of `obstacles-summary.md`:
1. Establish the exact two-way equivalence (`A31`) between `¬ RHTower.AsymptoticAbscissaLaw` and the existence of `β > 1/2`, `η > 0`, and a nonzero finite trigonometric polynomial `T` such that `ψ(x) - x = x^β T(log x) + O(x^{β - η})` (valid across arbitrary zero multiplicities because `-ζ'/ζ` has only simple poles).
2. Decide whether the combined exact arithmetic constraints of `ℤ` (`ψ(x) = ∑_{n ≤ x} Λ(n)` integer-supported with jumps `≥ log 2`, `N(x) = ⌊x⌋` with exact sawtooth, Euler product `∏_p (1 - p^{-s})^{-1}`, and exact Riemann functional equation `ξ(1 - s) = ξ(s)`) refute `ψ(x) - x = x^β T(log x) + O(x^{β - η})`, thereby establishing `RHTower.AsymptoticAbscissaLaw` unconditionally.

## Gates
- [x] 0 → 1  in-progress: corpus & literature inventory complete; firewall models isolated
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean 4 formalization compiled clean with `lake --old env lean`, wired into umbrella

## Firewall constraints (proven countermodels that any valid proof must exclude)
1. **Continuous Beurling systems** (`overRegularZeta`, `BeurlingOneOffZeroCountermodelsAndDefectTradeoff.lean`): satisfy `ψ_B(x) - ρ x = x^β T(log x) + O(1)` and `N_B(x) - ρ x - C → 0`, violating discrete `ℕ`-support and exact Riemann FE.
2. **Discrete Beurling Euler products without FE** (`BeurlingOneOffZeroCountermodelsAndDefectTradeoff.lean`, Broucke–Debruyne–Vindas): satisfy positive Euler product with one-off off-line zero pair, violating integer norms and exact Riemann FE.
3. **Dirichlet series with exact FE and finite `ℕ`-prefix** (`functional-equation-is-blind-to-rh.md`, Davenport–Heilbronn): satisfy `s ↔ 1 - s` FE on `ℕ`-Dirichlet series with off-line zeros, violating Euler product (`Λ(n)` multiplicativity).
4. **Function-field zeta functions** (`𝔽_q[T]`): have periodic vertical zeros (`AAL` holds automatically by vertical periodicity `2πi / log q`), whereas over `ℤ` `log p` are `ℚ`-linearly independent.

## Approach
1. **Equivalence layer (`A31`):** Mellin continuation of `(ψ(x) - x) x^{-s-1}` vs. truncated Perron contour shift across the bilateral spectral-gap strip `(β₁, β_*)` (`not_asymptoticAbscissaLaw_iff_bilateral_spectralGap`).
2. **Contradiction / rigidity search in `¬AAL` (`F12`):** Test interactions between (a) exact integer jump structure of `ψ(x)` and `N(x) = ⌊x⌋`, (b) Selberg / divisor convolutions and integer-supported atomic mass floors, (c) analytic continuation of `log((s - 1)ζ(s))` on `{Re s > β₁, Im s > T_*}` coupled to `{Re s < 1 - β₁, Im s > T_*}` via `ξ(1 - s) = ξ(s)` and to the Euler Dirichlet series on `Re s > 1`.

## Turán derivative route

- **Lean:** `not_asymptoticAbscissaLaw_has_high_jet_bounds` supplies the high zero-free region and Cauchy bounds for every derivative of the actual logarithmic derivative, from `¬AAL` alone.
- **Lean:** `scaled_norm_finitePoleJet_le_uniform_in_order` proves that the finite low-height pole contribution vanishes at distant centres, uniformly in the derivative order. `tendsto_finitePoleJet_at_unique_nearest` recovers a residue at a fixed centre with a unique nearest pole.
- **Lean:** `tendsto_logDeriv_jets_at_rightmost_zero` recovers the exact multiplicity of a rightmost zero of an entire function. Global peeling and compactness produce a zero-free cofactor on a disk larger than the tangent disk; Cauchy's estimate removes its normalized jets. Finiteness of the zero set is unnecessary.
- **Lean:** `not_asymptoticAbscissaLaw_has_prime_moment_limit` proves that for an actual rightmost zeta zero `ρ`, `s₀=ρ+d`, `Re s₀>1`, the corrected moments `d^(k+1)/k! · Σ Λ(n)(log n)^k n^(-s₀) − (d/(s₀−1))^(k+1)` tend to `−mρ < 0`. The only premise is `¬AAL`; multiplicity, factorization, and the analytic remainder are discharged for the actual zeta function. Axiom audits contain only `propext`, `Classical.choice`, and `Quot.sound`.
- **Remaining:** force comparable prime-side jets at quantitatively controlled high ordinates, or prove an unconditional arithmetic theorem conflicting with this moment limit. Qualitative recurrence (`∀k ∃t`) does not supply the required relation between `k` and `t`.
- No contradiction to `¬AAL` established. The finite-oscillation question remains undecided here.

## Arithmetic bound target

The corrected von Mangoldt moment has a negative integer limit. A contradiction must bound this same corrected quantity, including its pole subtraction and normalization.

| Candidate input | Exact issue / retained target |
|---|---|
| Positivity of `Λ` | Absolute values restore the real-axis pole radius `σ−1`, smaller than the detection radius `σ−β`. They do not bound the corrected moment at the required scale. |
| Selberg / integer-counting convolution | Multiplication by `ζ` cancels the selected zero's logarithmic-derivative pole. The exact logarithmic commutator retains the prime kernel (`LogarithmicCommutatorsExposeThePrimeKernel`). |
| Quantitative phase recurrence | The radius gain has the parameter ceiling `η log((η+1−β₁)/(η+1−β)) < β−β₁ < 1/2`. Its sharp envelope is being formalized; this compares candidate bounds, not actual return times. |
| Proper prime powers | `tendsto_normalized_higher_prime_power_jets` proves decay when `d<σ−1/2`. `not_asymptoticAbscissaLaw_has_prime_only_jet_limit` retains the exact nonzero limit for the corrected prime-only current. Both audited: standard three axioms only. |
| Fixed-height mean square | A diagonal estimate alone leaves the signed off-diagonal arithmetic term uncontrolled. Typical-height bounds permit bounded-height exceptional signals. |
