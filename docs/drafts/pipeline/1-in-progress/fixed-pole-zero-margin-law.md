# The fixed exponential-pole Weil criterion has zero asymptotic margin

- **ID:** `fixed-pole-zero-margin-law`
- **Stage:** 1-in-progress (paper law closed; Lean positive survivor in progress)
- **Type:** LAW (CANNOT-323 / MUST-226) + THEOREM (Lean, the sharp constant of the diagonal entry)
- **Parent:** `weil-two-pole-compression-prime-error.md` (Route O fixed-pole criterion,
  `riemannHypothesis_iff_primeGammaPoleInequality`), `weil-pole-direct-sign-attack.md`
- **Computation:** `2-fully-proven/computations/fixed-pole-parity-profile/`

## Statement

With `κ = −γ − log 2π`, `X = e^{2a}`, `L(t) = −log(1−e^{−t})`, the corpus's exact entries are

`A(a) = κ·2sinh a − e^a + (1−2a)e^{−a} + B₁(a) − 2e^a E_M(2a) + 2e^{−a}ψ(X)`,
`C(a) = κ·2a + 2a² + (2sinh a)² + B₀(a) − Σ_{2≤n≤X}Λ(n)(1+1/n)(2a − log n)`,

and RH ⟺ `|C(a)| ≤ A(a)` for all `a > 0` (even energy `A + C`, odd energy `A − C`).

**Law.** Unconditionally,
`A(a) = c₀ e^a − 2e^a(E_M(2a) + γ) + 2e^{−a}(ψ(X) − X) + r(a)`, `c₀ = 2 + γ − log 4π = 0.046192…`,
`|r(a)| ≤ (6a + 30)e^{−a}` for `a ≥ 1`. On paper `c₀ = Σ_ρ 1/(ρ(1−ρ)) = 2Σ_ρ 1/ρ` (Hadamard
product of `ξ`), and by the explicit formula `C(a) = Σ_ρ X^ρ/ρ² + O(1)`. Hence, writing
`ρ = ½ + iγ`, `θ_ρ = arg ρ`, under RH

`(A ± C)(a) = e^a Σ_{γ>0} 2(1 ± cos(2aγ − 2θ_ρ))/|ρ|² + O(a²)`,

and off RH the terms `X^ρ/ρ²` with `Re ρ > ½` dominate. The criterion is the triangle inequality
`|Σ_ρ e^{2iaγ}/ρ²| ≤ Σ_ρ|ρ|^{−2}` to leading order: mean and oscillation amplitude of the relative
margin coincide; the margin is a Bohr almost-periodic function of `a` with infimum zero whenever
finitely many ordinates can be phase-aligned (Kronecker under linear independence).

## Derivation of the constant

`B₁(a) = (e^a/2)∫_0^{2a} e^{−t}L(2t)dt + e^{−a}∫_0^{2a}e^t(L(t) − L(2t)/2)dt`. The first integral
has the closed antiderivative `F(t) = G(e^{−t})`, `G(u) = (u−1)log(1−u) + (u+1)log(1+u) − 2u`,
`G'(u) = log(1−u²)`, `G(1) = 2log 2 − 2`, so `∫_0^{2a} = 2 − 2log 2 + G(e^{−2a})`, `|G(u)| ≤ 6u` on
`[0,½]`. The second integral lies in `[0, 2B₀ + 4a] ⊂ [0, 4a + 18]`. Then
`c₀ = κ − 1 + (1 − log 2) + 2γ + 2` from: `κ·2sinh a → κe^a`, `−e^a`, `B₁ → (1 − log 2)e^a`,
`−2e^aE_M → +2γe^a − 2e^a(E_M + γ)` (Mertens' constant for the full von Mangoldt sum is `−γ`),
`2e^{−a}ψ(X) → 2e^a + 2e^{−a}(ψ − X)`.

## Consequences

- The corpus's admitted diagonal bound `|A| ≤ K_A e^a` (`K_A ≈ 30`) overstates the room by three
  orders of magnitude; the true main term is `0.046 e^a`, and the cross fluctuation has the same
  amplitude. The parallel Route O attack (`H(a) ≥ 2a[ψ + M₁] − A − C_sm` at even minima) is a
  one-sided `√X` Chebyshev bound with the *sharp* constant `Σ_ρ|ρ|^{−2}`; sieve, mean-value, or any
  input with a constant loss cannot supply it.
- Numerically (`a ≤ 8`) both parity energies stay positive with relative margins in `[0.029, 0.063]`
  around the mean `0.0462`; `even + odd = 2A` exactly; `C(8) = −16.65` vs `−16.70` from 400 zeros.
- The positivity of `c₀` itself is not derivable from mathlib's bounds `½ < γ < ⅔`
  (`c₀ > 0 ⟺ γ > log 4π − 2 = 0.5310`); a sharper certified lower bound for `γ` would be needed to
  certify the sign of the main term in Lean.

## Lean (`RHTower.CCMRestrictedWeilPoleDiagonalSharpConstant`, in progress)

`ccmPoleSelfKernelPrimitive` (`G`), `hasDerivAt_ccmPoleSelfKernelPrimitive`,
`ccmPoleSelfKernelAntiderivative` (`F`), `hasDerivAt_…`, `continuous_…`, `…_zero`,
`integral_exp_neg_mul_ccmGammaPoleBoundaryLog_two_mul` (improper FTC via
`integral_eq_sub_of_hasDerivAt_of_tendsto`), `abs_ccmPoleSelfKernelPrimitive_le`,
`exp_mul_ccmGammaPoleBoundaryLog_le` (`e^tL(t) ≤ 2L(t) + 2`),
`integral_exp_mul_boundaryLog_diff_bounds`, `ccmWeilPoleSharpConstant`,
`ccmWeilPoleDiagonalRemainder`, `ccmWeilPoleDiagonal_eq_sharp` (exact identity),
`abs_ccmWeilPoleDiagonalRemainder_le`, `abs_ccmWeilPoleDiagonal_div_exp_sub_sharp_le`.

## Gates

- G1 (paper): constant identification `c₀ = Σ_ρ 1/(ρ(1−ρ))` and `C = Σ_ρ X^ρ/ρ² + O(1)` — classical
  (Hadamard product, explicit formula for `∫_1^X ψ(u)du/u`); not in Lean.
- G2 (Lean): the module builds, axioms clean, wired. Then stage 3.
- G3 (open, RH-strength): any proof of the parity signs must reproduce `c₀` exactly from the source.
