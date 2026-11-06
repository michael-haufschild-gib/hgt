# Multiplicative Dilation Annihilation of a Finite Prime-Error Oscillation and Two-Prime Pinning Equivalence

- **ID:** multiplicative-dilation-annihilation-of-prime-error
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** docs/drafts/pipeline/1-in-progress/pnt-error-single-finite-oscillation.md
- **Statement:** Every single-base multiplicative dilation operator `dilationPolyOp b (dilationSetPoly b β S)` (`b > 1`, `β < 1`) identically annihilates `x^β T(log x)` on `(0, ∞)` while preserving a strictly positive linear main term `mainTermFactor b β S · x`; conversely, for any distinct primes `p ≠ q`, joint `O(x^{σ₀})` annihilation (`σ₀ < 1`) at bases `p` and `q` confines all zeros of `ζ` in `{Re s > σ₀}` to finitely many ordinates on `Re s = β`, yielding an exact prime-dilation characterization of `¬ AsymptoticAbscissaLaw`.

## Goal
Connect the `x`-space finite prime-error oscillation to linear combinations of multiplicatively dilated Chebyshev sums `∑_k a_k ψ(x / b^k)` and characterize `¬ AsymptoticAbscissaLaw` via joint dilation annihilation at two distinct prime bases.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven: complete paper proof below, no open dependency
- [x] 2 → 3  formalized: `GaloisForLFunctions.ZeroConfigurationGeometry.MultiplicativeDilationAnnihilationOfPrimeError` (`dilationPolyOp`, `dilationPairPoly`, `dilationSetPoly`, `dilationSetOp`, `mainTermFactor`, `dilationSymbol`, `dilationSetOp_id_eq`, `dilationPolyOpC_cpow_eq`, `dilationSymbol_dilationSetPoly_eq`, `dilationSetOp_rpow_mul_finiteOscillation_eq_zero`, `mainTermFactor_ge_pos`, `abs_dilationSetOp_psi_sub_mainTerm_le`, `integral_Ioi_one_psi_div_mul_cpow`, `neg_dilationSymbol_mul_deriv_zetaResidueUnit_eq`, `dilationSymbol_eq_zero_of_zeta_eq_zero`, `re_eq_and_im_mem_periodic_of_dilation_bound`, `finite_xiZeroCopy_of_twoPrime_dilation_bound`, `not_asymptoticAbscissaLaw_iff_twoPrime_dilationAnnihilation`)

## Proof
1. **Polynomial dilation algebra.** Associate to `P ∈ ℝ[X]` and `b > 0` the operator `(dilationPolyOp b P f)(x) = ∑_{k=0}^{deg P} P_k f(x / b^k)`. For `x > 0` and `s ∈ ℂ`, `(x / b^k)^s = x^s (b^{-s})^k`, so `dilationPolyOp b P` acts on `x^s` by scalar multiplication with `P(b^{-s})` and on `id` (`s = 1`) by `P(b^{-1}) x`.
2. **Exact top-oscillation annihilation and main-term survival.** Set `dilationPairPoly b β ω (X) = 1 - 2 b^β cos(ω log b) X + b^{2β} X^2` and `dilationSetPoly b β S = ∏_{ω ∈ S} dilationPairPoly b β ω`. Over `ℂ`, `dilationPairPoly b β ω (z) = (1 - b^{β + iω} z)(1 - b^{β - iω} z)`, which vanishes at `z = b^{-(β ± iω)}`. Hence `dilationSetPoly b β S (b^{-(β + iμ)}) = 0` for every `μ ∈ S ∪ (-S)`, so `dilationPolyOp b (dilationSetPoly b β S)` annihilates `x^β finiteOscillation S c (log x)` identically on `x > 0`. At `z = b^{-1}` (`b > 1`, `β < 1`), each quadratic factor equals `(1 - b^{β - 1})^2 + 2 b^{β - 1}(1 - cos(ω log b)) ≥ (1 - b^{β - 1})^2 > 0`, so `mainTermFactor b β S = (dilationSetPoly b β S).eval (b^{-1}) > 0`, and any expansion `|ψ(x) - x - x^β T(log x)| ≤ C x^{β - η}` gives `|dilationSetOp b β S ψ (x) - mainTermFactor b β S · x| ≤ C_b x^{β - η}`.
3. **Exact Mellin clearing identity without boundary terms.** For `c = b^k ≥ 1` and `Re s > 1`, rescaling `t = c u` on `(1, ∞)` yields `∫_1^∞ ψ(t / c) t^{-s-1} dt = c^{-s} ∫_{c^{-1}}^∞ ψ(u) u^{-s-1} du = c^{-s} ∫_1^∞ ψ(u) u^{-s-1} du` because `ψ(u) = 0` for `u ≤ 1 < 2`. Summing over `k` gives on `Re s > 1`:
   `s ∫_1^∞ R_b(t) t^{-s-1} dt = D_b(s) (-ζ'(s)/ζ(s)) - D_b(1) s/(s - 1)`,
   where `D_b(s) = (dilationSetPoly b β S).map(ℝ → ℂ).eval(b^{-s})`. Multiplying by `Z(s) = (s - 1)ζ(s)` produces `-(D_b(s) Z'(s)) = Z(s) (D_b(1) - dslope D_b 1 s + s ∫_1^∞ R_b(t) t^{-s-1} dt)`, which extends holomorphically to `Re s > σ₀` via `Complex.differentiableOn_dslope` whenever `|R_b(x)| ≤ C x^{σ₀}`.
4. **Single-base periodic ordinate pinning and two-prime finiteness.** Comparing `analyticOrderAt` at any zero `ρ` of `ζ` (`ρ ≠ 1`, `Re ρ > σ₀`) forces `D_b(ρ) = 0`, hence `b^{β ± iω - ρ} = 1` for some `ω ∈ S`, so `Re ρ = β` and `Im ρ = α + m (2π / log b)` (`α ∈ S ∪ (-S)`, `m ∈ ℤ`). When this holds simultaneously for distinct primes `p ≠ q`, irrationality of `log q / log p` (`RHTower.irrational_log_ratio`) implies that each pair `(α_p, α_q) ∈ (S ∪ (-S))^2` admits at most one solution `Im ρ ∈ (α_p + (2π / log p)ℤ) ∩ (α_q + (2π / log q)ℤ)`. Thus `{ρ : ζ(ρ) = 0, Re ρ > σ₀}` has cardinality at most `|S ∪ (-S)|^2 < ∞`, establishing the exact two-prime dilation equivalence with `¬ AsymptoticAbscissaLaw`.
