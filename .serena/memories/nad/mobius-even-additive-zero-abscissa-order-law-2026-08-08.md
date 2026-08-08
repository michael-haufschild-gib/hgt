# Card `mobius-even-additive-zero-abscissa-order-law` — CLOSED, promoted to stage 3 (2026-08-08)

Now at `docs/drafts/pipeline/3-formalized/mobius-even-additive-zero-abscissa-order-law.md` with a
Stage-3 Lean certificate.  The exact law `Λ_k = 2k(1+Θ) - 1` is an unconditional Lean theorem, as
are its RH form and the unconditional Ω₊ law.  Axioms clean throughout; `lake build
GaloisForLFunctions.RHTower` green.

## New modules

| Module | Content |
|---|---|
| `RHTower/ZetaZeroAbscissa` | `zetaZeroAbscissa = sSup {Re ρ : ζ ρ = 0}`; `half_le_zetaZeroAbscissa`, `zetaZeroAbscissa_le_one`, `riemannZeta_ne_zero_of_zetaZeroAbscissa_lt`, `exists_zetaZero_mem_openStrip_lt_re`, `riemannZeta_one_sub_eq_zero_of_mem_openStrip` |
| `RHTower/MobiusMertensEvenConvolutionOrderLowerEdge` | `le_of_mertensEvenConvolution_subpower`, `mertensEvenConvolutionOrder`, `le_mertensEvenConvolutionOrder` (E16), `frequently_rpow_le_mertensEvenConvolution` (E5a) |
| **`RHTower/InvZetaAbscissaSubpolynomial`** | Θ-general three circles: `exists_three_circles_zeta_lower_bound_of_zeroFree`, `exists_zeta_lower_bound_subpolynomial_of_zeroFree`, `exists_invZeta_shift_data_of_zeroFree`, `zetaResidueUnit_ne_zero_of_zeroFree` |
| **`RHTower/MobiusMertensAbscissaLittlewood`** | `mobius_perron_shift_of_zeroFree`, `mobiusMertens_subpower_of_zeroFree`, **`mobiusMertens_subpower_zetaZeroAbscissa`** = `M(N) = O(N^{Θ+ε})` unconditional |
| `RHTower/MobiusMertensEvenConvolutionExactOrder` | `norm_mobiusAdditiveTriangleSecondCesaro_le_of_subpower`, `norm_mobiusMertensEvenConvolution_le_of_subpower`, `mertensEvenConvolutionOrder_le` (E10), **`mertensEvenConvolutionOrder_eq`** (E3), `zetaZeroAbscissa_eq_half_of_riemannHypothesis`, `riemannHypothesis_of_zetaZeroAbscissa_eq_half`, **`riemannHypothesis_iff_mertensEvenConvolutionOrder_eq`** (E4) |

Also added to `HTGeometry/LogOrderLimsupBound`: `exists_global_subpower_of_eventually`,
`exists_global_subpower_of_eventually_le`, `log_one_add_max_div_log_nonneg`.

## The generalisation that unlocked it — reusable pattern

`InvZetaRHSubpolynomial` proves the reciprocal-zeta shift datum **only** from `ζ z ≠ 0` on
`Re z > 1/2`; RH is never used otherwise.  Copying that 500-line file with
`1/2 ↦ Θ`, `hRH ↦ (hzf : ∀ z, Θ < z.re → ζ z ≠ 0)` and the three-circle centre `3 ↦ 4`
(so `r₃ = 4 - (Θ+δ/2) > 2` survives `Θ ≤ 1`; inner discs stay in `Re > 7/2`) makes it Θ-general.
At `Θ = zetaZeroAbscissa` the hypothesis is unconditional.  **`Θ < 1` is NOT needed** anywhere —
important, since `Θ < 1` is open.

The corpus's `SmoothPerronLittlewood.partialSumSeq_subpower_of_smoothPerron` was already stated for
a general `Θ`; the Dirichlet side (`DirichletLSubpolynomial`, `DirichletLShiftData`,
`TwistedMertensLittlewood`, `TwistedOrderLawTheta`) is the exact template and already closes the
twisted analogue at `zeroAbscissa χ`.  **Check for the Dirichlet analogue before building a ζ
analogue by hand.**

## Reusable outputs beyond this card

* **`mobiusMertens_subpower_zetaZeroAbscissa`** — Littlewood's `M(N) = O(N^{Θ+ε})` at the true zeta
  zero frontier, unconditional.  Any card needing "Mertens is controlled by the zero frontier" can
  cite this instead of assuming it.
* **`riemannHypothesis_of_zetaZeroAbscissa_eq_half` / `zetaZeroAbscissa_eq_half_of_riemannHypothesis`**
  — `RH ↔ Θ = 1/2` as a Lean iff.
* `exists_invZeta_shift_data_of_zeroFree` — the Perron shift datum on any strip right of a zero-free
  frontier.
