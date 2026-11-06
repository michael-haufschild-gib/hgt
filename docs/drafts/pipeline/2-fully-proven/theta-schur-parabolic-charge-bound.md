# Parabolic suppression of the actual theta Schur charge

- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Wall:** Σ79
- **Statement:** The actual corrected theta stages have an unconditional asymptotic quartic-charge ceiling; their small spectral nodes carry sixth-order, rather than merely fourth-order, charge.

## Statement

Write `q(z) = 600 (Re z)² (Im z)² + 2300 (Im z)⁴`, and let `C` be the uniform Hilbert–Schmidt ceiling of the corrected theta stages. All sufficiently late Schur packets have total charge at most `C²/400`. At squared-norm cutoff `δ`, for every `ε > 0` their small-spectrum charge is eventually at most `(150 δ² + 425 δ³/4 + ε) C²`.

## Proof [PROVED HERE]

Put `n=|w|²`, `v=(Im w)²`. Then `q(w)=600nv+1700v²`. For a reciprocal Xi zero, the critical strip gives `v≤n²/4`; therefore `q(w)≤150n³+425n⁴/4`.

For a nonreal Xi zero `z=γ+iδ`, existing bounds give `γ²≥431/2`; `δ²≤25/144` when `|γ|≤16`, `δ²≤49/256` when `16<|γ|≤18`, and `δ²≤1/4` otherwise. In these three cases respectively, `250000δ²≤(γ²+δ²)²` follows from `γ²≥210`, `γ²≥256`, and `γ²≥324`. Also `100δ²≤γ²+δ²`. Thus, for `w=1/z`, `v≤1/250000` and `100v≤n`. Consequently `q(w)≤617n/250000<n/400`. Real zeros have charge zero.

For either desired spectral bound, its failure on the closed source norm ball away from zero is compact. Inversion is continuous there; the inequalities just proved make normalized Xi nonzero on the inverted set. Locally uniform convergence of the honest corrected theta determinants makes them eventually zero-free there. Every nonzero Schur diagonal has its reciprocal as a determinant zero, so no such diagonal remains in the bad set. Near zero use `q(w)≤2300n²`: choose `n<1/(400·2300)` for the fixed ceiling, or `n<ε/2300` for the sixth-order estimate. The resulting stage is uniform over all Schur packets. Summing the pointwise bounds and using `Σn≤C²` proves both assertions; on `n≤δ`, monotonicity bounds the sixth-order coefficient by `150δ²+425δ³/4`.

Dependencies: `LowHeightGammaPF54`, `FiniteMatrixSchurPositiveQuarticSpectralSplit`, and `HedenmalmThetaSchurQuarticSpectralDecayEquivalence`. No zero verification or RH premise is used.

## Boundary

The ceiling is positive. Vanishing of the actual total charge remains unproved. Check novelty against the existing spectral split and skew-adjoint-energy bound before changing the wall status.
