# All-scale Euler dilation rulers and rational-ray zero rigidity of a single off-line quartet

- **ID:** zfc-single-quartet-rational-rays-and-dilation-poles
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `ZeroForcingCalculus/EulerDilationAndRootCoincidenceExclusion.lean`; `ExclusionOfTheCriticalState/Index/SingleQuartetSecularAndWallRigidity.lean`
- **Statement:** For every integer `k ≥ 2` and `m ∈ ℕ`, pole-freeness of `((s - 1)ζ(s))^m / ζ(ks)` on `{Re s > β / k}` is an unconditional ruler for `zetaZeroAbscissa ≤ β` on `[1/2, 1 - 20999/(24000k))` (and on `[1/2, ∞)` for `k ≥ 7`), with `β = 1/2` equivalent to `RiemannHypothesis`; under `HasSingleOffLineQuartet ρ₀`, `ζ(ρ / k) ≠ 0` holds for all `k ≥ 2` and `ρ ∈ Q(ρ₀)`, `ζ(kρ) ≠ 0` holds for all `k ≥ 4`, and at most one `r ∈ ℝ_{>0} \ {1}` (`r = 1 / (2 Re ρ₀)`, absent when `Re ρ₀ ∉ ℚ`) satisfies `ζ(r ρ₀) = 0`.

## Lean
Module `ZeroForcingCalculus/SingleQuartetRationalRaysAndDilationPoles.lean` (namespace `GaloisForLFunctions.ZeroForcingCalculus`):
`dilatedPowerQuotient_poleFree_iff_zetaZeroAbscissa_le`, `isRuler_dilatedPowerQuotient`,
`dilatedPowerQuotient_poleFree_iff_zetaZeroAbscissa_le_of_seven_le`,
`dilatedPowerQuotient_poleFree_iff_riemannHypothesis`, `riemannZeta_pos_real_mul_eq_zero_imp`,
`riemannZeta_pos_real_mul_ne_zero_of_outside`, `subsingleton_other_ray_zeros_of_singleQuartet`,
`riemannZeta_rat_ray_ne_zero_of_irrational_re`, `riemannZeta_div_nat_ne_zero_of_singleQuartet`,
`dilatedPowerQuotient_neg_order_of_singleQuartet`,
`riemannZeta_nat_mul_ne_zero_of_singleQuartet_ge_four`. Axioms: `propext`, `Classical.choice`,
`Quot.sound`.

## Paper proof
1. **Meromorphic unit representation and `k`-ary halving-reflection cascade (`k ≥ 2`).** On a punctured neighborhood of every `s ∈ ℂ`, `((w - 1)ζ(w))^m / ζ(kw) = U(w)^m (kw - 1) / U(kw)` where `U = zetaResidueUnit` is entire. If `zetaZeroAbscissa ≤ β`, `U(kw) ≠ 0` for `Re w > β / k`, giving nonnegative meromorphic order. Conversely, suppose `((s - 1)ζ(s))^m / ζ(ks)` is pole-free on `{Re s > β / k}` with `1/2 ≤ β < 1 - 20999/(24000k)` and `ζ(ρ₀) = 0` with `β < Re ρ₀ < 1`. Inductively define `ρ_{n+1} = 1 - ρ_n / k`. At each step `Re(ρ_n / k) > β / k`, so absence of a pole at `ρ_n / k` forces `ζ(ρ_n / k) = 0`; functional reflection gives `ζ(ρ_{n+1}) = 0`, while the unconditional zero-free region `Re ρ_n ≤ 20999/24000` ensures `Re ρ_{n+1} ≥ 1 - 20999/(24000k) > β` and `|Im ρ_n| = |Im ρ₀| / k^n → 0`, contradicting `|Im ρ| > 4` for strip zeros. Setting `β = 1/2` yields `RiemannHypothesis` for every `k ≥ 2`.
2. **Single-quartet ray rigidity and `k ∈ {2, 3, 4, 5, 6}` closure.** Under `HasSingleOffLineQuartet ρ₀`:
   - For `r > 0`, `r ≠ 1` with `ζ(r ρ₀) = 0`, Euler-product nonvanishing forces `0 < r Re ρ₀ < 1`, while `|Im(r ρ₀)| = r |Im ρ₀| ≠ |Im ρ₀|` excludes `Q(ρ₀)`; hence `r ρ₀` must lie on `Re s = 1/2`, fixing `r = 1 / (2 Re ρ₀) ∈ [12000/20999, 1)`. If `Irrational ρ₀.re`, no `q ∈ ℚ_{>0} \ {1}` can equal `1 / (2 Re ρ₀)`.
   - For `ρ ∈ Q(ρ₀)` and `k ≥ 2`, `0 < Re(ρ / k) < 1/2` and `|Im(ρ / k)| = |Im ρ₀| / k < |Im ρ₀|`, so `ρ / k` avoids both `Re s = 1/2` and `Q(ρ₀)`; thus `ζ(ρ / k) ≠ 0` and `ord_{ρ/k}(((s - 1)ζ(s))^m / ζ(ks)) = -ord_ρ ζ < 0` for all `k ≥ 2`.
   - Since `Re ρ ≥ 1 - Re ρ₀ ≥ 3001/24000` on `Q(ρ₀)`, for `k ≥ 4` we have `Re(kρ) ≥ 12004/24000 > 1/2` and `|Im(kρ)| = k|Im ρ₀| > |Im ρ₀|`, giving `ζ(kρ) ≠ 0`.

## What it changes
Closes the unconditional `k ∈ {2, 3, 4, 5, 6}` root-coincidence gap completely under `HasSingleOffLineQuartet`, establishes `((s - 1)ζ(s))^m / ζ(ks)` as an unconditional width ruler on `[0, 1/2 - 20999/(24000k))` and an exact `1/(2k)` criterion for `RiemannHypothesis` at every integer dilation `k ≥ 2`, and shows that along the open ray `ℝ_{>0} · ρ₀` at most one scalar `r ≠ 1` (none in `ℚ` if `Re ρ₀ ∉ ℚ`) can be a zero of `ζ`.

## Log
- 2026-11-18 — created; proved; formalized.
