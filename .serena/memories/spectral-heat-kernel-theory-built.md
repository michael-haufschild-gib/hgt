# Spectral heat kernel theory (mathlib gap, built here)

`formal/GaloisForLFunctions/HTGeometry/SpectralHeatKernel/` — 7 modules, all wired into the
`HTGeometry` umbrella, every theorem audited to `propext`, `Classical.choice`, `Quot.sound`.

Mathlib has **no heat kernels**.  This layer builds them from a spectral datum — a nonnegative
spectrum `lam : ℕ → ℝ` and an eigenfunction family `φ : ℕ → X → ℂ` on a measure space, or a
`HilbertBasis ℕ ℂ E` — with no manifold anywhere.

| Module | Contents |
|---|---|
| `Basic` | `spectralHeatKernel`, `spectralHeatDiag`; Hermitian symmetry; diagonal is the real nonneg spectral sum; **pointwise Cauchy–Schwarz** `‖K(t,x,y)‖ ≤ √K(t,x,x)√K(t,y,y)`; trace formula `∫K(t,x,x)dμ = Σe^{−tλ}`; diagonal antitone in `t` |
| `Semigroup` | Chapman–Kolmogorov `∫K(s,x,z)K(t,z,y)dμ(z) = K(s+t,x,y)`; the AM–GM `L²` pairing bounds `∫‖f‖‖g‖ ≤ 1` and `≤ (∫‖f‖²+∫‖g‖²)/2` |
| `Operator` | `∫K(t,x,y)v(y)dμ = Σ e^{−tλ}⟪φ,v⟫φ(x)` — the kernel represents the semigroup |
| `MinMax` | **Parseval** for a `HilbertBasis` (`tsum_norm_inner_sq`, `summable_norm_inner_sq`); `spectralQuadratic`; **infinite-dimensional Courant–Fischer upper bound** `spectral_eigenvalue_le_of_trial` — the min–max principle Prop 6.1 of Dai–Yoshikawa uses |
| `Flow` | `spectralHeatFlow` as a contraction semigroup via the corpus's `lpDiagonalCLM`; coefficient formula; contractivity; semigroup law; `‖e^{−tΔ}v‖² = Σ e^{−2tλ}|c|²` |
| `Energy` | `mul_exp_neg_le_inv` (`λe^{−t₀λ} ≤ 1/(e t₀)`); **the energy identity** `d/dt Σe^{−2tλ}a = −2Σλe^{−2tλ}a` on every `(t₀,∞)` |
| `HeatEquation` | `spectralHeatKernelLaplacian`; **Lemma 2.1 in kernel form**; **the heat equation** `∂ₜK = −ΔK` |

## Reuse notes

* Differentiating a heat series term by term: `hasDerivAt_tsum_of_isPreconnected` on `Ioi t₀`, with
  the domination supplied by `DaiYoshikawa.pow_mul_exp_neg_div_le` (`PowerExpSup`).  Both `Energy`
  and `HeatEquation` follow that pattern; copy it rather than re-deriving.
* The corpus's `LpDiagonalMultiplier.lpDiagonalCLM` is the right vehicle for any spectral
  multiplier; `GreedyCourantFischer.exists_mem_ne_zero_orthogonal_of_finrank_lt` is the dimension
  count for any min–max argument.
* `HilbertBasis` needs no `[CompleteSpace E]` for any of this — do not add it, the linter rejects it.

## What this layer does *not* give

No metric, so no Gaussian off-diagonal decay; no Markov property, so no `L¹` contractivity and hence
no Nash/Carlen–Kusuoka–Stroock ultracontractivity yet.  Those need a Dirichlet-form/Markov-semigroup
layer on top (Beurling–Deny), which is the next build.  See `mem:dai-yoshikawa/small-eigenvalues-formalization-2026-08-22`.
