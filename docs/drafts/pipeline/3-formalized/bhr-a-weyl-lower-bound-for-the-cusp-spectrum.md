# BHR — a Weyl lower bound for the cusp spectrum of the modular horizon

- **ID:** bhr-weyl-lower-bound
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** A26 (Weyl law) of review-0711; uses `bhr-the-odd-sector-is-a-cavity.md`, `bhr-the-cusp-spectrum-is-discrete.md`.
- **Statement:** There are `c > 0`, `Λ₀` with `N(Λ) ≥ cΛ` for all `Λ ≥ Λ₀`, where `N(Λ)` counts level-one
  cusp forms of Laplace eigenvalue `≤ Λ` with multiplicity.

## Paper proof
1. **Min–max.** If a symmetric `T` is diagonal on a Hilbert basis with real eigenvalues `μ_i`, and
   `re⟨f,Tf⟩ ≥ c‖f‖²` on a subspace `V`, then `dim V ≤ #{i : μ_i ≥ c}`: otherwise some `f ∈ V \ 0` is
   orthogonal to those basis vectors and `c‖f‖² - re⟨f,Tf⟩ = Σ (c - μ_i)|f_i|² > 0`.
2. **Eigenvalue against mass.** For a smooth profile `φ` the point-pair operator acts on the basis
   vector of eigenvalue `λ` by a real `κ`; the Green identity `L_{Dφ} = -λL_φ` on the eigenvector and
   `‖L_{Dφ}‖ ≤ ‖Dφ‖₁` give `λ|κ| ≤ ‖Dφ‖₁`.
3. **Narrow kernels.** `φ_R(u) = β(u/R)` with a fixed bump. The disc `u(i,w) ≤ r` (Euclidean disc of
   radius `√(8r)` about `i` at most, at least radius `√r`) has hyperbolic area in `[πr/4, 32πr]`. So
   `‖φ_R‖₁ ≥ πR/8` and `‖Dφ_R‖₁ ≤ A` independent of `R ≤ 1/32`.
4. **Localization.** If `z, z'` lie in the region `1/10 ≤ |x| ≤ 2/5`, `6/5 ≤ y ≤ 9/5` and
   `u(z, Bz') ≤ R ≤ 1/12800`, then `Bz'` is within `1/20` of `z`, so `Bz', z' ∈ 𝒟°` and `B = ±1`. Hence
   on data supported in the region the operator is the local convolution.
5. **Test vectors.** `18n²` discs of radius `1/(40n)` on a grid of spacing `1/(10n)` in `x > 0`, with
   mirror images; `s_k = 1_{D_k} - 1_{ιD_k}` is odd, hence cuspidal. With `R = 1/(204800 n²)`, the kernel
   range is `1/(80n)`: different pairs do not interact, and on the inner half discs the convolution of
   `s_k` is `±m`, `m = ‖φ_R‖₁`. So `re⟨s_k, Ks_k⟩ ≥ 2m·π(ρ/2)²/4` and `‖s_k‖² ≤ 2πρ²`: ratio `m/16`.
6. **Count.** By 1, `18n²` basis vectors have `κ ≥ m/16`, hence `λ ≤ 16A/m ≤ 128A/(πR) = Cn²`. Choosing
   `n ≍ √(Λ/C)` gives `N(Λ) ≥ (9/(2C))Λ`.

## Lean certificate
Modules `formal/GaloisForLFunctions/BlackHoleRingdown/TheWeylKernel.lean` and
`TheWeylLowerBound.lean`, wired into `BlackHoleRingdown.lean`; both checked with `lake --old env lean`,
no messages; axioms of `WeylBound.weyl_lower_bound`: `propext`, `Classical.choice`, `Quot.sound`.

| Claim | Theorems |
|---|---|
| Min–max | `WeylBound.finrank_le_card_of_form_ge` |
| Eigenvalue against mass | `WeylBound.exists_kernelEigenvalue`, `WeylBound.norm_lap_op_le` |
| Narrow kernels, disc areas | `WeylBound.narrowProfile`, `narrow_mass_ge`, `exists_narrow_lap_mass_le`, `volume_disc_le`, `volume_disc_ge` |
| Localization | `WeylBound.smul_eq_self_of_pairU`, `WeylBound.ppApply_eq_local` |
| Test vectors | `WeylBound.testVec`, `form_ge_testVec`, `form_ge_on_span`, `testVec_ne_zero` |
| Count | `WeylBound.count_ge_grid`, `WeylBound.weyl_lower_bound` |

## Not formalized
- The Weyl constant `1/12` and an upper bound `N(Λ) = O(Λ)`.

## Log
- 2026-11-07 — created and formalized.
