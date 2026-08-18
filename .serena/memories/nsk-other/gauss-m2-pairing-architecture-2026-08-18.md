# Gauss card, m ≥ 2: the correct architecture is a PAIRING estimate, not a norm estimate

Card: `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/other/gauss-component-quasi-inner-residue-hierarchy.md`

## Correction of passes 42/44/51

Those passes aimed at the one-step estimate `‖(R̃_n − a_δ) u‖ → 0` for `u` in the two-piece class,
and therefore at generalizing (T) (`tendsto_norm_gaussShiftedBlockDiag_symbol_defect_zero`) to the
two-piece class.  **That target is false.**  Heuristic sizes (m = 2, u = R·1):

- `R^i 1` has a spike at frequency `≈ −n` of exponent `i/m` and height `≍ log^L n / n`;
- `(R − M)(R^{m-1}1)` then has a spike of exponent `1` and height `≍ log^L n / n`, whose `ℓ²`
  mass is `H²n²Σ_r(1+r)^{-2} ≍ log^{2L} n` — bounded away from zero, and growing.

So the `L²` one-step error does **not** vanish at the top iterate.  What does vanish is the
*pairing against a harmonic vector*: the spike sits at distance `≍ n` from frequency `0`, and
pairing it against coefficients of size `1/(1+|j|)` costs a factor `1/n`:
`Σ_r (1/n)·H(n/r)^1 ≍ H log n → 0`.

## The master identity (all algebra already in the tree)

```
⟪e_n, G^r e_n⟫ = σ_n^r · ⟪1, R_n^r 1⟫            gaussQuasiInnerG_pow_fourierMulBlock
⟪1, M_n^r 1⟫   = A_r(fract δ_n)                  fourierCoeff_gaussAmplitudeIterate_zero
⟪1, R^r1 − M^r1⟫ = Σ_{i<r} ⟪a_δ^{r-1-i}, (R−M)(R^i 1)⟫       operator_pow_sub_eq_sum + M self-adjoint
```
σ_n = p·d_n·conj d_n sits **outside**, so any `o(1)` on the pairing is already the *relative* form.

## The two-term split, moved onto the pairing by adjointness

`R − M = B[S B^{-2}(S*−T)]B + B[(S−T^{-1})B^{-2}T]B`, and with `B`, `B^{-2}` self-adjoint and
`⟪u, S w⟫ = ⟪S* u, w⟫` (`gaussShiftedBlockOf_inner`):

```
⟪g, (R−M)v⟫ = ⟪ B^{-2}S*(Bg) , (S*−T)(Bv) ⟫  +  ⟪ Bg , (S−T^{-1})(B^{-2}T(Bv)) ⟫
```

**No `‖S·‖` ever appears**, so (T) is not needed for this card at all.  Both terms are of the form
`Σ_j ‖X̂(j)‖·‖Ŷ(j)‖·‖gaussSampleRatioDefect k p j n‖` (the defect operators act coefficientwise:
`norm_fourierCoeff_shiftedBlockOf_sub_rotation`).

## The single new analytic lemma (pairing defect lemma)

For `X`, `Y` with two-piece profiles `A_P/(1+|j|)^{θ_P} + H_P·spike(c_P)` and likewise for `Q`,
with `H_P ≤ A'_P/(1+n)^{σ_P}`:

```
Σ_j ‖X̂(j)‖ ‖Ŷ(j)‖ ‖D_j(n)‖ → 0
```
under
```
1 < θ_P + θ_Q,   c_P + 1 < θ_Q + σ_P,   c_Q + 1 < θ_P + σ_Q,   c_P + c_Q + 1 < σ_P + σ_Q.
```
Four pieces: bulk·bulk (Cauchy–Schwarz against the existing
`tendsto_gaussTranslationL2PowDefectBound_comp`), spike·bulk, bulk·spike, spike·spike.  For the
three spike pieces the **crude** band bound suffices:
`Σ_{2|r|<n}(1+|r|)^{-t}(1+(Kn/|r|)^{1/(2m)}) ≤ C·n`
(counting term `≤ 2n`; power term by `tsum_int_punctured_band_rpow_le` at `t = 1/(2m) < 1`).

Application parameters: `X = B^{-2}S*(Bg)` has `c_P = c₀+1/(2m)`, `θ_P, σ_P ≈ 1`;
`Y = B(R^i 1)`, `i ≤ m−1`, has `c_Q = c₀+i/m ≤ c₀+(m−1)/m`, `θ_Q, σ_Q ≈ 1`.  All four
inequalities hold with margin `≈ 1/m`, so the ε-budget for the `mul_symbol` exponent drops is
`≈ 1/(m·#convolutions)`.

## Already landed for this

`RHTower/GaussSpikeDefectBand.lean` (new, checks clean):
```
norm_gaussSampleRatioDefect_le_shiftRatio    ‖D_j‖ ≤ ρ_j + 1
gaussShiftRatio_sq_le_rpow                   ρ_j² ≤ (K n/|n+j|)^(1/m)     -- SHARP exponent 1/m,
                                                 no case split: ρ² = (ρ^{2m})^{1/m}
norm_gaussSampleRatioDefect_sq_le_rpow       ‖D_j‖² ≤ 2 + 2(K n)^(1/m)
tsum_spikeProfile_sq_mul_defect_sq_le        Σ_l spike² ‖D_l‖² ≤ B²n^{2c}(2+2(Kn)^{1/m})·W(2c)
```
The corpus's `gaussShiftRatio_sq_le_sqrt` (exponent 1/2) is too lossy for `m ≥ 4`; use the
`1/m` version.

## What is still needed

1. the pairing defect lemma above;
2. the two-piece class bookkeeping for `R^i 1`, `i ≤ m−1` (compose `TwoPieceAmplitude.mul_symbol`
   and `.mul_multiplier`, dropping the bulk exponent by a fixed ε per convolution and raising the
   spike exponent by `1/(2m)` per multiplier);
3. the two-regime multiplier bounds for the symbols of `S` and `S*` (feed `mul_multiplier`);
4. assembly → relative (11) for all `m`;
5. negative frequencies: either the pointwise-conjugation antiunitary `C` (`C R_i C = R_{−i}`,
   `C M C = M`, `C 1 = 1`, `δ_{−i} = δ_i`) or a ℤ-indexed restatement;
6. then `GaussDiagonalLogResidue.lean` generalizes from `m = 1` verbatim (its inputs
   `gaussPrincipalDiagonalTerm_logResidue`, `gaussLocalFactorWeight_mul_principalResidue`,
   `inner_gaussQuasiInnerGFull_pow`, `exists_gaussComponentPrimeMagnitudeEnergy_bounds`
   are already stated for general `m`).
