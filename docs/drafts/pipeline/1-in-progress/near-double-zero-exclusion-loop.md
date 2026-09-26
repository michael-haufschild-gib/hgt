# Pointwise arithmetic input excluding near-double zeros — conjecture loop

- **ID:** near-double-zero-exclusion-loop
- **Stage:** 1-in-progress
- **Type:** CONJECTURE LOOP (user-directed, 2026-09-26)
- **Target.** An unconditional pointwise statement on the critical line excluding isolated near-line FE pairs `ρ, 1−ρ̄` (displacement `δ ≲ d/√log γ`, no companion within about `δ`). This is the exact open core of the first Laguerre inequality at all heights (`first-laguerre-all-heights.md`).

## Corpus frontier at loop start (read before conjecturing)
- `ArithmeticJointJetExclusion` [L]: an off-line zero forces `|Z(γ)|+|Z'(γ)| ≤ 48γ²δ²`. The resulting exclusion radius `√(J/96t²)` is always below `δ` at a near-double zero, since its depth is `≈ |Z''|δ²/2`. So first-jet exclusion is circular for this target.
- MUST-432 (monomial witness) [L]: an off-line zero strictly nearest to its own ordinate point is refuted by one value of `(log Ξ)^{(4n+2)}`. Exclusion therefore means "every off-line zero has a strictly closer companion", which restates the target.
- `HorizontalChargeTransfer` [L]: entry prevention must control O-charge (off-line) separately from M-charge (multiplicity). No statistic that is continuous in the divisor separates a near-line pair from a double zero.
- CANNOT-330/333: resolution. An isolated displacement `δ` at height `T` is seen only by primes beyond `T^{1+2πδ}`; real parts are resolved only at scale (window length)·(distance), never `1/log T`.
- CANNOT-437: the needed bound is an absolute constant (integrality removes slack). RH-is-criticality: `Λ = 0`, so there is no robust (open-condition) input.
- Theta-Wigner chain: BRIDGE. The open core is the archimedean spectral gate `G(σ,ξ) ≥ G(1−σ,ξ)`.

## Cycles
- **N1 (mollified transfer).** Multiply `ζ` by a nonvanishing Euler factor `E_P`. The Laguerre condition moves by an explicit `−(log|E_P|)''`, so the problem is transferred, not solved. `CIRCULAR`. *Lesson A:* no nonvanishing multiplicative modification helps; the input must see the zero set.
- **N2 (explicit formula at resolution `δ`).** The pair contributes `2h(γ) − δ²h''(γ)` against a double zero's `2h(γ)`. Seeing `δ²` needs `h` localized at scale `≤ δ`, hence primes to `e^{C/δ}`. `REDISCOVERED` (CANNOT-330/333). *Lesson B:* resolution needs Dirichlet length `≥ T^{1+2πδ}`.
- **N3 (nearest-zero sign).** For large odd `m`, `sign (log Ξ)^{(2m)}(t)` is set by the zero nearest to `½+it`; an off-line nearest zero gives the wrong sign. `REDISCOVERED` (MUST-432). Exclusion is "no off-line zero is its own ordinate's nearest zero".
- **N4 (cheapest length).** By Lesson B with `δ = c/log T`, the needed prime length is `T^{1+2πc/log T} = e^{2πc}T`. Near-line pairs are the cheapest off-line configurations to detect: Dirichlet length `≍ T`, the length of the product (ζ²) AFE, exact in the corpus (`ProductAFEExact`). `SURVIVES` as a *quantitative location of the input*: it must live at length `≍ T`, no more.
- **N5 (Riemann–Siegel reduction).** `Z = Z₀ + O(t^{−1/4})` with `Z₀` the RS main term. A near-line pair with `δ ≥ c/log T` has depth `≫ t^{−1/4}`, so the target for `δ ≥ c/log T` is equivalent to the same exclusion for `Z₀` (with jump corrections at `N(t)` changes). `SURVIVES` (paper reduction).
- **N6 (Hermite–Biehler of the analytic signal).** `Z₀(T+u) = F(u) + F^#(u)`, where `F = e^{iθ}Σ_{n≤N}n^{−½−iT}e^{i log(N/n)u}` has only nonnegative frequencies. If `|F^#| > |F|` on the upper half-plane, all zeros of `Z₀` near `T` are real. That domination is `|χ(s)D_N(1−s)|` against `|D_N(s)|` for `Re s > ½`: the corpus domination core in local form. `CIRCULAR` (= the recorded open core).
- **N7 (dominant top frequency).** If the `n = 1` amplitude exceeds the sum of the others, all zeros are real. This holds only for `N ≤ 2` (`1 < 2^{−½}+3^{−½}`). `FALSE` for the relevant `N ≈ √(T/2π)`.

## Loop state
The input must be arithmetic at Dirichlet length `≍ T` (N4). It must separate O-charge from M-charge (not continuous in the divisor), and it must give an absolute-constant, integer-type bound. No candidate satisfies all three so far.
