import GaloisForLFunctions.RHTower.SuzukiModelSpace

/-!
# The conjugate Hardy space and Suzuki eq. (2.7)

`L^(2 : ℕ)(R)` splits orthogonally as `L^(2 : ℕ)(-infty,0) + L^(2 : ℕ)(0,infty)`, and the Fourier transform carries
that split to `H^(2 : ℕ)` and its orthogonal complement.  Multiplication by `Theta_xi` is a *unitary*
(`thetaUnitary`), so it transports orthogonal complements, and the model space acquires its second
description

`K(Theta) = H^(2 : ℕ) cap Theta (H^(2 : ℕ))^perp`,

which is Suzuki eq. (2.7) with `(H^(2 : ℕ))^perp = F(L^(2 : ℕ)(-infty,0))` the Hardy space of the lower
half-plane.

The only slightly delicate step is `halfLineL2^perp = lowerHalfLineL2`.  One inclusion is the
pointwise vanishing of the integrand off a null set; the other applies the orthogonality hypothesis
to `1_{(0,infty)} g`, for which the pairing against `g` equals its own square norm, so that vector
is zero.
-/

open Complex Filter Topology MeasureTheory Set

namespace RHTower
noncomputable section

/-! ## The conjugate Hardy space and the alternative form of `K(Θ)` -/

theorem halfLineL2_orthogonal : halfLineL2ᗮ = lowerHalfLineL2 := by
  apply le_antisymm
  · intro g hg
    have hf : posRayProj g ∈ halfLineL2 := by
      rw [mem_halfLineL2_iff]
      filter_upwards [posRayProj_coeFn g] with x h1 hx
      rw [h1]
      have hind : posRaySymbol x = 0 := by
        unfold posRaySymbol
        rw [Set.indicator_of_notMem (by simp; linarith)]
      rw [hind, zero_mul]
    have hzero : (inner ℂ (posRayProj g) g : ℂ) = 0 :=
      Submodule.mem_orthogonal _ _ |>.mp hg _ hf
    have hself : (inner ℂ (posRayProj g) g : ℂ)
        = (inner ℂ (posRayProj g) (posRayProj g) : ℂ) := by
      rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [posRayProj_coeFn g] with x h1
      rw [h1, RCLike.inner_apply', RCLike.inner_apply', map_mul]
      unfold posRaySymbol
      by_cases hx : x ∈ Set.Ioi (0:ℝ)
      · rw [Set.indicator_of_mem hx]
        simp
      · rw [Set.indicator_of_notMem hx]
        simp
    rw [hzero] at hself
    have : posRayProj g = 0 := inner_self_eq_zero.mp hself.symm
    exact this
  · intro g hg
    refine Submodule.mem_orthogonal _ _ |>.mpr fun f hf => ?_
    rw [MeasureTheory.L2.inner_def]
    have hfz := (mem_halfLineL2_iff f).mp hf
    have hgz := (mem_lowerHalfLineL2_iff g).mp hg
    have hne : ∀ᵐ x : ℝ, x ≠ 0 := by
      rw [MeasureTheory.ae_iff]
      simp
    have hzero : (fun x : ℝ => (inner ℂ ((f : ℝ → ℂ) x) ((g : ℝ → ℂ) x) : ℂ)) =ᵐ[volume] 0 := by
      filter_upwards [hfz, hgz, hne] with x h1 h2 h3
      rcases lt_or_gt_of_ne h3 with hx | hx
      · rw [RCLike.inner_apply', h1 hx, map_zero, zero_mul]
        rfl
      · rw [RCLike.inner_apply', h2 hx, mul_zero]
        rfl
    rw [integral_congr_ae hzero]
    simp

end
end RHTower

namespace RHTower
noncomputable section
open Complex Filter Topology MeasureTheory Set

/-! ## `Θ` as a unitary, and Suzuki eq. (2.7) -/

theorem norm_thetaMul (f : Lp ℂ 2 (volume : Measure ℝ)) : ‖thetaMul f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  refine eLpNorm_congr_norm_ae ?_
  filter_upwards [thetaMul_coeFn f] with x h1
  rw [h1, norm_mul, norm_suzukiThetaSymbol, one_mul]

/-- Multiplication by `Θ_ξ` is a unitary of `L²(ℝ)`. -/
def thetaUnitary : Lp ℂ 2 (volume : Measure ℝ) ≃ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ) where
  toFun := thetaMul
  map_add' := fun f g => thetaMul.map_add f g
  map_smul' := fun c f => thetaMul.map_smul c f
  invFun := thetaMulInv
  left_inv := thetaMulInv_thetaMul
  right_inv := thetaMul_thetaMulInv
  norm_map' := norm_thetaMul

theorem lowerHalfLineL2_orthogonal : lowerHalfLineL2ᗮ = halfLineL2 := by
  haveI : CompleteSpace (halfLineL2 : Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ))) :=
    isClosed_halfLineL2.completeSpace_coe
  rw [← halfLineL2_orthogonal, Submodule.orthogonal_orthogonal]

theorem hardyL2_orthogonal :
    hardyL2ᗮ = Submodule.map
      ((MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ).toLinearEquiv.toLinearMap) halfLineL2 := by
  rw [hardyL2,
    ← Submodule.map_orthogonal_equiv lowerHalfLineL2 (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ),
    lowerHalfLineL2_orthogonal]

/-- **Suzuki eq. (2.7).**  `K(Θ) = H² ∩ Θ · (H²)^⊥`, the alternative representation of the model
space; here `(H²)^⊥ = 𝖥(L²(-∞,0))` is the Hardy space of the lower half-plane. -/
theorem suzukiModelSpace_eq_inf_map :
    suzukiModelSpace
      = hardyL2 ⊓ Submodule.map (thetaUnitary.toLinearEquiv.toLinearMap) hardyL2ᗮ := by
  rw [suzukiModelSpace, thetaHardyL2,
    Submodule.map_orthogonal_equiv hardyL2 thetaUnitary]
  rfl

end
end RHTower

