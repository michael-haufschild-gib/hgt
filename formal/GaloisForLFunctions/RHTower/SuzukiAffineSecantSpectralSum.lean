import GaloisForLFunctions.RHTower.SuzukiProjectiveAffineSecantTensor

/-!
# Finite spectral sum of the Suzuki affine-secant tensor

The marked affine-secant tensor `(X+c)Y − (α+β)xY + αβxy` reconstructs the boundary source when its
common resolvent coordinates are given by finite spectral sums over the eigenmodes: with spectral
levels `tᵢ`, source weights `vᵢ`, and observation weights `bᵢ = B(eᵢ)`, `dᵢ = D(eᵢ)`,

```text
x = Σ bᵢvᵢ,  X = Σ tᵢbᵢvᵢ,  y = Σ dᵢvᵢ,  Y = Σ tᵢdᵢvᵢ.
```

This file proves the exact finite spectral expansion of the marked tensor into a double sum of
per-mode-pair contributions (each the two-mode kernel `tᵢtⱼ − (α+β)tⱼ + αβ` weighted by
`vᵢvⱼbᵢdⱼ`), plus the homogeneous `c`-channel — generalizing the single-pair split
`suzukiProjectiveAffineSecant_twoMode_pair_decomposition` to the whole finite spectrum.
-/

namespace RHTower

open Finset

noncomputable section

/-- **Finite spectral sum of the marked affine-secant tensor.**  With resolvent coordinates given by
finite spectral sums over the eigenmodes, the marked tensor equals the double sum of per-mode-pair
two-mode kernels plus the homogeneous `c`-channel. -/
theorem suzukiProjectiveAffineSecant_finite_spectral_sum
    {ι : Type*} [Fintype ι] (α β c : ℝ) (t b d v : ι → ℝ) :
    suzukiProjectiveAffineSecantTensor α β
        (∑ i, b i * v i) (∑ i, t i * b i * v i) (∑ i, d i * v i) (∑ i, t i * d i * v i) c
      = (∑ i, ∑ j, v i * v j * b i * d j * (t i * t j - (α + β) * t j + α * β))
        + c * ∑ j, t j * d j * v j := by
  have key : (∑ i, ∑ j, v i * v j * b i * d j * (t i * t j - (α + β) * t j + α * β))
      = (∑ i, t i * b i * v i) * (∑ j, t j * d j * v j)
        - (α + β) * ((∑ i, b i * v i) * (∑ j, t j * d j * v j))
        + α * β * ((∑ i, b i * v i) * (∑ j, d j * v j)) := by
    rw [Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.mul_sum,
      Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [suzukiProjectiveAffineSecantTensor, key]
  ring

end

end RHTower
