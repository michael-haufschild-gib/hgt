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

/-! ## Separating the diagonal

`(7)` displays the spectral sum as a per-mode diagonal part plus genuine pair terms plus the
homogeneous channel.  The double sum absorbs the diagonal; separating it is the general fact that a
double sum over a finite index set splits into its diagonal and its off-diagonal parts. -/

/-- **The diagonal split.**  A double sum is its diagonal plus its off-diagonal part. -/
theorem sum_sum_eq_diag_add_offDiag {ι : Type*} [Fintype ι] [DecidableEq ι] (F : ι → ι → ℝ) :
    ∑ i, ∑ j, F i j = (∑ i, F i i) + ∑ i, ∑ j ∈ Finset.univ.erase i, F i j := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm

/-- The off-diagonal part is what carries the spectral gaps: a diagonal term of the secant kernel
contributes only through its own mode. -/
theorem offDiag_sum_eq_sub_diag {ι : Type*} [Fintype ι] [DecidableEq ι] (F : ι → ι → ℝ) :
    (∑ i, ∑ j ∈ Finset.univ.erase i, F i j) = (∑ i, ∑ j, F i j) - ∑ i, F i i := by
  rw [sum_sum_eq_diag_add_offDiag F]
  ring

end RHTower
