# Lag receivers: almost every spacing is blind, a non-meagre set is not

- **ID:** lag-measure-versus-category
- **Stage:** 3-formalized
- **Source:** JAS goal loop row 198

## Conjecture
For every `Θ > 0` there is a locally finite configuration `ρ_i` with:
- `½ < Re ρ_i < ½ + Θ`, with the supremum `½ + Θ` not attained;
- positive summable weights `c_i`, conjugate-symmetric;
- lag function `Φ(t) = Σ_i c_i Re e^{(ρ_i − ½)t}` satisfying `sup_{m ≥ 1} Φ(mℓ) < ∞` for Lebesgue-almost every `ℓ > 0`.

The good set `{ℓ : sup_m Φ(mℓ) < ∞}` is meagre: abstract Baire–Landau, as in MUST-1363. So it has full measure and is meagre.

## Mechanism (paper proof)
1. **Fejér blocks.** Block `j` has points `½ + δ_j + i dω_j` for `0 < |d| < K_j`, with weights `c_j (K_j − |d|)/(2K_j)`. Then
   `Φ_j(t) = (c_j e^{δ_j t}/2)(F_{K_j}(ω_j t) − 1)`, where `F_K(θ) = K^{−1}|Σ_{k<K} e^{ikθ}|² ∈ [0, K]` and `F_K(θ) sin²(θ/2) ≤ 1/K`.
2. **Where Φ can be positive.**
   - Write `a_j(t) = c_j e^{δ_j t}` and `S = Σ a_j`. Then `Φ = ½(Σ a_j F_j − S)`.
   - If `Φ(t) > 0`, some `j` has `a_j F_j > 2^{−j−1} S`.
   - That forces `F_j > 2^{−j−1}`, and also `a_j K_j > 2^{−j−1} a_{j+1}`, i.e. `t < τ_j = log(K_j 2^{j+1} c_j/c_{j+1})/(δ_{j+1} − δ_j)`.
3. **Measure of the spike set.** `{t ∈ [0, τ] : |sin(ωt/2)| < ε}` has measure `≤ ετ + 4πε/ω` (Jordan). Hence `|{Φ > 0}| ≤ Σ_j (ε_j τ_j + 4πε_j/ω_j)` with `ε_j = (K_j 2^{−j−1})^{−1/2}`.
4. **Parameters.** `δ_j = Θ(1 − 2^{−j−1})`, `K_j = 2^{8(j+1)}`, `c_{j+1} = c_j/(K_j 2^{2j+2})`, `ω_j = j + 1`. Then `ε_j τ_j ≲ 2^{−2.5j} j` is summable, so `|{Φ > 0}| < ∞`.
5. **Borel–Cantelli in `ℓ`.**
   - `∫_{L₁}^{L₂} #{m : mℓ ∈ B} dℓ = ∫ 1_B(s) Σ_{s/L₂ ≤ m ≤ s/L₁} m^{−1} ds ≤ C|B|`.
   - So for a.e. `ℓ`, only finitely many `m` have `Φ(mℓ) > 0`.
6. **Category.** If `{ℓ : sup_m Φ(mℓ) ≤ M}` (closed) contained an interval, then `Φ ≤ M` on a half-line. The Laplace transform of `M − Φ ≥ 0` would then have a real singularity at its abscissa (Landau). Its continuation is the meromorphic Cauchy series with poles `ρ_i − ½`, so the abscissa is `≤ 0`, contradicting the off-line points. Hence the good set is meagre.

## Status
- Both halves are formalized, the category half by a direct spike argument (no abstract Landau needed).
- Module `RHTower/WeilLagAlmostEverySpacingBlind`. Main theorem: `exists_lag_configuration_goodSpacings_ae_and_meagre`.
- Parameter changes from the paper sketch:
  - `c_b = 2^{−5b(b+1)}`;
  - windows `ε_b = 2^{−3b−3}`;
  - upper horizon `σ_b = (10b+9)2^{b+2}log 2/Θ`.
- MUST-1382. Standard axioms.

## Positive survivor (no-go closure)
- **Statement.** For EVERY positive summable, locally finite configuration with `Re w ≤ B`, a lag function bounded above on a half-line forces `Re w_i ≤ 0`. So does boundedness along a non-meagre set of spacings.
- **Proof.** Landau across a real pole, plus a twist by `1 + cos(t Im w_j) ≥ 0`, which makes `Re w_j` a real exponent with positive weight. Baire then reduces the spacing statement to a half-line.
- **Lean.** Module `RHTower/WeilLagOneSidedConfigurationRigidity`, theorems `re_nonpos_of_lag_le` and `re_nonpos_of_not_isMeagre`. MUST-1384. Standard axioms.
- **Insight.** The category half of the dichotomy is universal on positive configurations, not ζ-specific. Measure versus category is exact for progression receivers.
- **Complex weights (row 200, MUST-1384 addendum).** For one exponent per conjugate pair, distinct and nonzero weights:
  - one-sided rigidity holds when real exponents carry `Re a > 0`;
  - two-sided rigidity holds when they carry `Re a ≠ 0`.
  - Theorems: `re_nonpos_of_lagRe_le_upper`, `re_nonpos_of_abs_lagRe_le_upper` and their non-meagre forms. This covers `ζ` and L-function weight shapes.
