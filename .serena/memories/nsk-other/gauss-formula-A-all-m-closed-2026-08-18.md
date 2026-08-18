# Gauss card: formula (A) is Lean-proved for the OPERATOR at every m

Card: `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/other/gauss-component-quasi-inner-residue-hierarchy.md`
(passes 52, 53, 54 at the end of the card).

## Capstones (unconditional, axiom-clean, umbrella-wired)

```
RHTower.tendsto_gaussLocalDiagonal_logResidue        (k : Fin 1)   -- m = 1, pass 35
RHTower.tendsto_gaussLocalDiagonal_pow_logResidue    (2 ≤ m)       -- NEW
    ((p−1)/p)^(2m) · (1/log N) Σ_(n<N)( ⟪e_(n+1),G_full^m e_(n+1)⟫ + ⟪e_(−(n+1)),…⟫ )
        → gaussChannelResidue m p = 2(p−1)^(2m)(p^m−1)²/(p^(2m) m² log p)
```
`gaussChannelResidue` is literally the card's formula (A).  The card's only named Lean gap
("`⟨G^m e_n, e_n⟩ → gaussPrincipalDiagonalTerm`") is therefore closed for every m.

## The architecture that worked (and the one that did not)

**Wrong target (passes 42/44/51):** `‖(R − M)u‖ → 0` for `u` in the two-piece class.  FALSE — at the
top iterate the spike of `(R−M)(R^{m-1}1)` has exponent 1 and `ℓ²` mass `≍ log^{2L} n`.

**Right target:** the PAIRING.  `⟪e_n,G^r e_n⟫ = σ_n^r⟪1,R_n^r1⟫` puts σ outside, and
`⟪1,R^r1 − M^r1⟫ = Σ_{i<r} ⟪a_δ^{r-1-i}, (R−M)(R^i1)⟫`.  Moving `B`, `S`, `B^{-2}` onto the left
slot by adjointness gives two sums `Σ_j ‖X̂(j)‖‖Ŷ(j)‖‖defect_j‖` — **no ‖S‖ anywhere**, so (T) is
not needed for this card at all.

## New modules

- `HTGeometry/FourierInnerCoefficientBound.lean` — `‖⟪u,v⟫‖ ≤ Σ_j ‖û(j)‖‖v̂(j)‖` (+ ℝ≥0∞ form).
- `RHTower/GaussSpikeDefectBand.lean` — sharp `ρ² ≤ (Kn/|n+j|)^{1/m}` (no case split:
  `ρ² = (ρ^{2m})^{1/m}`); the corpus's `gaussShiftRatio_sq_le_sqrt` (exponent 1/2) is too lossy for m ≥ 4.
- `RHTower/GaussPairingDefect.lean` — `‖D_j‖ ≤ 3 + K·I/|I+j|` (from `2D ≤ D²+1`, LINEAR, so the
  whole `ℓ²` skeleton is reusable), the `ℓ¹` defect bound, the band mass `6I + 2KI(1+log I)`, and
  `tendsto_tsum_twoPiece_pairing_defect_zero` under
  `1 < θP+θQ`, `cP+1 < σP+θQ`, `cQ+1 < σQ+θP`, `cP+cQ+1 < σP+σQ`.
- `RHTower/GaussClassStep.lean` — the TIED class `TwoPieceAmplitude A θ (B/(1+I)^θ) c I`
  (σ = θ collapses the four conditions to `cP+cQ+1 < θP+θQ`); symbol step `θ ↦ θ−ε`, multiplier
  step `c ↦ c+1/(2m)`; `exists_gaussClass_principalStep_pow` gives `R_I^r(1)` in the class.
  The `ε` drop is exactly what absorbs the logarithm each convolution costs.
- `RHTower/GaussPairingOneStep.lean` — the two-term split and its coefficientwise bound.
- `RHTower/GaussRelativeIterate.lean` — `c₀ = 1/(8m)`, `ε = 1/(24m²)`; the numeric condition is
  `3m − 1 < 6m`.
- `RHTower/GaussRelativePower.lean` — the telescope; equation (11) in relative form.
- `RHTower/GaussConjugationSymmetry.lean` — pointwise conjugation is antiunitary, commutes with `G`
  (`conj d_(−j) = d_j`), so `⟪e_(−n),G^r e_(−n)⟫ = conj⟪e_n,G^r e_n⟫`; negative frequencies free.
- `RHTower/GaussIterateLogResidue.lean` — the capstone.

## Reusable elsewhere

`fourierCoeff_star`, `star_lp_smul`, `lp_ext_fourierCoeff`, `star_lpBoundedMulCLM_real`,
`inner_star_star` are generic `L²(ℝ/ℤ)` facts; `norm_inner_le_tsum_fourierCoeff` is the pairing
device that replaced every norm estimate.
