# The complete Weil family is positive at a critical multiple

- **Stage:** 1-in-progress
- **Type:** CONJECTURE; Lean audit incomplete
- **Target:** Some fixed `K > 0` gives eventual positive definiteness of
  `completeWeilMatrix tiltedUnitSpline c N` on the whole horizon space,
  uniformly for `1 ≤ c ≤ 2K(log N)^(1/8)`.
- **Route:** F2/A30, complete-family assembly.

## Corrected proof

Write `L = log N`, `t = 1 + log L`, `θ = t⁻⁵`,
`Q = ⌊L^(13/32)⌋`, `R₀ = ⌊exp √L⌋`, `R₁ = ⌊N^θ⌋`, and
`M = N / linearDefectCutoff c`. Split orthogonally
`x = y + u₀ + u₁ + w` along `V_Q ⊂ V_R₀ ⊂ V_R₁`.
For the far block put

`P(w) = Σ_(n≤M) w_n²`,
`S₇(w) = Σ_(M<n≤N) (N/n)⁷w_n²`.

Let `D = explicitConductorCutoffConstant` and `g = dyadicTopMassConstant`.
Both are positive absolute constants.

### Prefix leakage and far reserve

The conductor prefix estimate is

`poleDefect M w ≥ k(15P/16 − 2BS)`,

where `k = log R₁/D − 1`, `B = terminalPacketCost R₁ M N / log M`,
and `S = Σ_(M<n≤N) w_n² ≤ S₇`. It is not a leakage-free prefix gap.
The dyadic far theorem retains `7 poleDefect/8 + gL S₇/(8c⁷)` at a
prefix cost `L P/(16Dt⁵)`. Since `k ≥ θL/(4D)` and `kB = O(c)`,
a sufficiently small critical multiple pays the leakage from the collar:

`E(w) ≥ θL P/(8D) + gL S₇/(16c⁷)`.

### Two distinct rates in the band–far cross

The totient factor satisfies `Sg ≤ At` for a fixed `A ≥ 1`. Uniformly for
`1 ≤ c ≤ L^(1/8)`, eventually

`c⁸(1+log c)Sg²/L ≤ A²t³`,
`c¹¹(1+log c)³Sg L^(1/16)/L² ≤ L^(-1/16)`,
`c⁷(1+log c)/L ≤ L^(-1/16)`.

Keep the first rate separate. With `b = (gD/4)t⁵`, the critical cross cost
is `O(t³/b) = O(t⁻²)`. Every other norm cost is `O(t⁵L^(-1/16))`.
The adjunction coefficient is `O(θ) + O(t⁻²)`.
A single common upper bound for these rates loses the critical decay.

For `c ≥ L^(1/16)`, eventually `b/c⁷ ≤ 1`; thus the prefix pays the far
norm term in the cross bound. Paying both band–far crosses and the
first-band/second-band cross leaves

`E(u₀+u₁+w) ≥ 4‖u₀‖² + (3+√L/32)‖u₁‖²`
`                 + θL P/(16D) + 3gL S₇/(64c⁷)`.

The first-band error requires the corrected conductor cutoff:
`c√c(1+log c)/√Q = O(L^(-1/64)(1+log L))`.
The former choice `Q = ⌊L^(5/16)⌋` instead gives a growing power `L^(1/32)`.

### Weighted Schur payment

For `E_m = completedConductorEnergy tiltedUnitSpline c m` and
`r_m = Wv_m − E_mv_m`, the critical residual theorem gives low-packet
coercivity `⟨W'y,y⟩ ≥ ΣE_ma_m²/4`, full inverse-energy residual mass
`Ψ ≤ L^(1/4)`, and an arbitrarily small dual seventh-power collar budget.
Here `W' = W − λI`, `λ = tiltedSplineSpectralFloorConstant/(2c⁷)`.

Deep rows give `Ψ_D ≤ 1/96`; the first band's top mass satisfies
`48L^(1/4)T(u₀) ≤ ‖u₀‖²/2`. Weighted Cauchy–Schwarz therefore gives,
for one common small critical multiple,

`8Σ_(m≤Q) ⟨r_m,u₀+u₁+w⟩²/E_m`
`  ≤ ‖u₀‖² + √L‖u₁‖²/32 + pP(w) + sS₇(w)`,

where `p = θL/(32D)` and `s = gL/(64c⁷)`.
The scalar Schur inequality

`2|Σa_m z_m| ≤ ΣE_ma_m²/8 + 8Σz_m²/E_m`

then leaves

`E(x) ≥ λ‖y‖² + 3‖u₀‖² + 3‖u₁‖² + pP(w) + 2sS₇(w)`.

All coefficients are positive and `P(w)+S₇(w) ≥ ‖w‖²`, proving positivity
for nonzero `x`. The existing subcritical theorem at exponent `1/16`
covers `1 ≤ c ≤ L^(1/16)`. Taking the minimum of the far, packet, and
Schur critical constants gives the claimed uniform interval.

## Lean status

Capstone source:
[`exists_critical_multiple_completeWeilMatrix_posDef`](../../../../formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/TheCompleteWeilMatrixIsPositiveAtACriticalMultiple.lean).
Its dependency chain includes the corrected first-band cutoff, two-rate cross
budget, weighted far reserve, and weighted Schur pairing. Deep-row, first-band,
and two-rate budget modules pass Lean; the remaining dependency chain and
transitive axiom audit are pending.

- [x] Corrected cutoff and terminal-leakage accounting.
- [ ] Dependency-closed Lean checks.
- [ ] Standard-only axiom audit and umbrella import.
