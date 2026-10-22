import GaloisForLFunctions.RHTower.Deninger.DeningerTensorTransport
import GaloisForLFunctions.HTGeometry.GrothendieckTensorComparison

/-!
# The tensored Poisson operator is strict

Feeding the corpus's nuclearity data — a trace-class comparison between the seminorm spaces of a
coefficient space — and the strictness of the Poisson operator into Grothendieck's comparison gives
the left end of the tensored sequence: for nuclear coefficients, `1 ⊗ Z` is a strict injection.

* `deningerTensor_poisson_strict` : **`1 ⊗ Z` is strict for nuclear coefficients.**
-/

open scoped Real SchwartzMap TensorProduct
open GaloisForLFunctions

noncomputable section

namespace RHTower

/-- **The tensored Poisson operator is strict for nuclear coefficients**: every projective tensor
seminorm on `E ⊗ ℋ_∩` is bounded by a projective tensor seminorm of the image in `E ⊗ ℋ_−`. -/
theorem deningerTensor_poisson_strict {E : Type*} [AddCommGroup E] [Module ℂ E] {ι : Type*}
    (P : SeminormFamily ℂ E ι) (hP : DeningerIsNuclearSpace P) (i : ι)
    (K₀ : Finset (ℕ × ℕ)) :
    ∃ (j : ι) (i' : Finset ℤ × (ℤ → ℕ)) (C : ℝ), 0 ≤ C ∧
      ∀ z : E ⊗[ℂ] DeningerMeyerCap,
        projTensorSeminorm (P i)
            (deningerRestrictSeminorm DeningerMeyerCap
              (K₀.sup (schwartzSeminormFamily ℂ ℝ ℂ))) z
          ≤ C * projTensorSeminorm (P j)
              (deningerRestrictSeminorm deningerRadialCompat
                (deningerPiFamily
                  (fun _ : ℤ => (shiftedSeminorm : SeminormFamily ℂ 𝓢(ℝ, ℂ) ℕ)) i'))
              (TensorProduct.map (LinearMap.id : E →ₗ[ℂ] E)
                (deningerPoissonLM : DeningerMeyerCap →ₗ[ℂ] deningerRadialCompat) z) := by
  obtain ⟨j, C₀, hle, hnuc⟩ := hP i
  obtain ⟨ι', φ, yv, hsummable, hhassum⟩ := hnuc
  obtain ⟨i', C₁, hC₁, hstrict⟩ := deningerPoissonLM_strict K₀
  refine ⟨j, i', (∑' k, ‖φ k‖ * ‖yv k‖) * C₁,
    mul_nonneg (tsum_nonneg fun k => by positivity) hC₁, fun z => ?_⟩
  exact projTensorSeminorm_le_nuclear_strict_injection (P i) (P j) _ _
    (deningerSeminormMk (P i)) (deningerSeminormMk (P j))
    (deningerSeminormComparison hle) (deningerSeminormMk_surjective _)
    (deningerSeminormMk_norm (P i)) (deningerSeminormMk_norm (P j))
    (deningerSeminormComparison_mk hle) φ yv hsummable hhassum
    deningerPoissonLM deningerPoissonLM_injective hC₁ hstrict z

end RHTower

end
