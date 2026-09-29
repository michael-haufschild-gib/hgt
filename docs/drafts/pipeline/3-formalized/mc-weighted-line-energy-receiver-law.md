# Weighted line-energy receiver law for Möbius prefixes

- **ID:** MC-RECEIVER-WEIGHTED-LINE
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / NO-GO (STATUS CANNOT-483)
- **Source:** MC conjecture loop, cycles 120 and 131
- **Statement:** Let `σ > 0`, `σ ≠ Θ = sup Re ρ`. Let `w : ℝ → ℝ` be measurable with `w(τ) ≥ c|Γ(σ+iτ)|²` for some `c > 0`, and `∫(1+τ²)w(τ)dτ < ∞`. Then `E_N(w,σ) = ∫|Σ_{n≤N}μ(n)n^{−σ−iτ}|² w(τ)dτ` is bounded in `N` iff `Θ < σ`.

## Lean
- `RHTower.bddAbove_range_mobiusWeightedLineEnergy_iff` (module `RHTower/MobiusWeightedLineEnergyExponentLaw.lean`).
- Components:
  - `exists_norm_edPoly_mobCoeff_line_le_of_zetaZeroAbscissa_lt`: the uniform Abel bound `‖Σ_{n≤N}μ(n)n^{−σ−iτ}‖ ≤ K(1+|τ|)` for `σ > Θ`.
  - `exists_forall_mobiusWeightedLineEnergy_le_of_zetaZeroAbscissa_lt`: the upper comparison.
  - `finiteMobiusGammaHankelEnergy_le_mobiusWeightedLineEnergy`: the lower comparison `E_N(2σ) ≤ E_N(w,σ)/(2πc)`.
- Axioms: propext, Classical.choice, Quot.sound. Wired into `RHTower.lean` after `MobiusCubicSourceExponentLaw`, and `lake build --old` passes (54 s).

## Proof mechanism
1. **Lower comparison.** Plancherel (`CubicGamma.integral_norm_sq_gamma_mul_edPoly_mobCoeff_line_sigma`) gives `2πE_N(2σ) = ∫|Γ(σ+iτ)P_N(σ+iτ)|²dτ ≤ c⁻¹E_N(w,σ)`. The Γ–Hankel divergence threshold (`bddAbove_range_finiteMobiusGammaHankelEnergy_iff`) then forces `Θ < σ`.
2. **Upper comparison.** Take `a = (Θ+σ)/2`. Littlewood's bound (`mobiusMertens_subpower_zetaZeroAbscissa`) gives `|M(k)| ≤ C(k+1)^a`. Abel summation (`Finset.sum_range_by_parts`) and the unit-difference bound `|x^{−s} − (x+1)^{−s}| ≤ |s|x^{−σ−1}` then give `|P_N(σ+iτ)| ≤ C2^a(1 + |s|ζ(1+σ−a))`. The second moment of `w` absorbs `(1+|τ|)²`.

## Consequence
Cycle 120 said that every positive-definite homogeneous Möbius energy is a receiver with threshold `Θ`; this law is its formal core. The domination hypothesis allows exponentially decaying weights, so the Γ–Hankel (Hilbert at `σ = ½`), Route L cubic (`|Γ((5+δ)/2+iτ)|² ≥ c|Γ((1+δ)/2+iτ)|²`) and similar carriers are all instances. No carrier of this class supplies the frontier's missing collective cancellation law. A producer must be non-quadratic, or use a weight vanishing on the line, which is sign-blind (cycle 116).

## Log
- 2026-09-29: formalized and wired (loop cycle 131).

## Non-quadratic extension: absolute moments and transport (cycle 132)
- **Statement:** for `p ≥ 1`, `c ≥ 1`, `c ≠ pΘ+1`: `Σ_{k≤X}|M(k)|^p = O(X^c)` iff `pΘ + 1 < c`. At `p = 1` this is the one-dimensional transport cost between `μ⁺` and `μ⁻`.
- **Lean:** `RHTower.exists_sum_norm_mertens_rpow_le_iff` (module `RHTower/MobiusMertensAbsoluteMomentExponentLaw.lean`). Components:
  - `mobiusDiscreteLaplaceDecay_of_sum_norm_mertens_le`
  - `zetaZeroAbscissa_le_of_sum_norm_mertens_le`
  - `sum_le_card_rpow_mul_sum_rpow` (Hölder)
  - `exists_sum_norm_mertens_rpow_le_of_lt`
- Axioms: propext, Classical.choice, Quot.sound. Wired after `MobiusWeightedLineEnergyExponentLaw`, and `lake build --old` passes (15 s). STATUS CANNOT-484.
- **Mechanism:**
  - Hölder reduces to `p = 1`.
  - Abel summation for power series, applied twice (once complex, once real), gives `|Σμ(n)e^{−nx}| ≤ (1−e^{−x})² Σ_N S(N)e^{−Nx}`, where `S(N) = Σ_{k≤N}|M(k)|`. The weighted exponential sum bound then gives `≪ x^{1−c}`.
  - `not_mobiusDiscreteLaplaceDecay_of_riemannZeta_eq_zero` excludes zeros with `Re ρ > c−1`.
- **Consequence:** matching and optimal-transport carriers are receivers with the same threshold as the quadratic ones. This covers cycle 55 and route E's opposite-sign edges.
