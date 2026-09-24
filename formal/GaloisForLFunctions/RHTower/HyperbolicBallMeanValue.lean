import GaloisForLFunctions.RHTower.HyperbolicPowerEigen
import GaloisForLFunctions.RHTower.SelbergMaassCuspTransport

open MeasureTheory UpperHalfPlane
open GaloisForLFunctions.RHTower
open GaloisForLFunctions.RHTower.HyperbolicRotationMean
open GaloisForLFunctions.RHTower.HyperbolicPowerEigen
open GaloisForLFunctions.RHTower.SelbergMaassCuspTransport

/-!
# Point-pair invariants at an arbitrary centre and the hyperbolic mean-value property

Transporting the Selberg transform at `i` by `SL(2,ℝ)` (which preserves `dx dy / y²` and commutes with
the Laplacian) gives `∫ φ(A⁻¹w) G(w) dμ = G(A·i) ∫ φ (Im)^s dμ` for every rotation-invariant `φ` and every
eigenfunction `G` with eigenvalue `s(1-s)` (`integral_centred_kernel`). With `φ` the indicator of the
hyperbolic ball this is the mean-value property
`∫_{B_R(z)} G dμ = G(z) ∫_{B_R(i)} (Im w)^s dμ` (`setIntegral_closedBall_eigen`).
-/

namespace GaloisForLFunctions.RHTower.HyperbolicPointPairCentre

theorem integrable_comp_smul_iff (A : GL (Fin 2) ℝ) {F : ℍ → ℂ} :
    Integrable (fun w => F (A • w)) ↔ Integrable F :=
  (measurePreserving_smul A volume).integrable_comp_emb (measurableEmbedding_const_smul A)

/-- **Point-pair invariance at an arbitrary centre.** For `A` with positive determinant, a
rotation-invariant `φ` recentred at `A·i`, and an eigenfunction `G` with eigenvalue `s(1-s)`,
`∫ φ(A⁻¹w) G(w) dμ = G(A·i) · ∫ φ (Im)^s dμ`. -/
theorem integral_centred_kernel (A : GL (Fin 2) ℝ) (hA : 0 < A.val.det) {φ G : ℍ → ℂ} {s : ℂ}
    (hφ : ∀ θ w, φ (rot θ • w) = φ w) (hφm : AEStronglyMeasurable φ volume)
    (hG : IsRealSmoothUpperHalfPlane G)
    (hGe : ∀ z, positiveHyperbolicLaplacian G z = s * (1 - s) * G z)
    (hiG : Integrable (fun w => φ (A⁻¹ • w) * G w))
    (hiE : Integrable (fun w => φ w * powerEigen s w)) :
    (∫ w, φ (A⁻¹ • w) * G w) = G (A • UpperHalfPlane.I) * ∫ w, φ w * powerEigen s w := by
  rw [← integral_smul_eq_self (G := GL (Fin 2) ℝ) (fun w => φ (A⁻¹ • w) * G w) (g := A)]
  simp only [inv_smul_smul]
  have hG' : IsRealSmoothUpperHalfPlane (fun w => G (A • w)) := smooth_pullback_gl A hA G hG
  have hGe' : ∀ z, positiveHyperbolicLaplacian (fun w => G (A • w)) z =
      s * (1 - s) * G (A • z) := by
    intro z
    rw [positive_laplacian_pullback_gl A hA G hG z, hGe]
  have hi : Integrable (fun w => φ w * G (A • w)) := by
    have := (integrable_comp_smul_iff A).mpr hiG
    simpa only [inv_smul_smul] using this
  exact integral_kernel_eq_selbergTransform hφ hφm hG' hGe' hi hiE


open Metric
open scoped MatrixGroups

/-- The rotation `k_θ` as an element of `SL(2,ℝ)`. -/
noncomputable def rotSL (θ : ℝ) : SL(2, ℝ) := ⟨rotMatrix θ, rotMatrix_det θ⟩

theorem rot_smul_eq (θ : ℝ) (w : ℍ) : rot θ • w = rotSL θ • w := rfl

theorem rot_smul_I (θ : ℝ) : rot θ • UpperHalfPlane.I = UpperHalfPlane.I := by
  apply UpperHalfPlane.ext
  rw [coe_rot_smul]
  have h : (-(UpperHalfPlane.I : ℂ) * Real.sin θ + Real.cos θ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    have him := congrArg Complex.im h
    simp at hre him
    rw [Complex.cos_ofReal_re] at hre
    rw [Complex.sin_ofReal_re] at him
    have := Real.sin_sq_add_cos_sq θ
    rw [hre, him] at this; norm_num at this
  rw [div_eq_iff h]
  simp only [UpperHalfPlane.coe_I]
  ring_nf
  rw [Complex.I_sq]
  ring

theorem dist_rot_smul_I (θ : ℝ) (w : ℍ) :
    dist (rot θ • w) UpperHalfPlane.I = dist w UpperHalfPlane.I := by
  conv_lhs => rw [← rot_smul_I θ]
  rw [rot_smul_eq, rot_smul_eq, dist_smul]

/-- The ball kernel `1_{d(w, i) ≤ R}`. -/
noncomputable def ballKernel (R : ℝ) (w : ℍ) : ℂ :=
  Set.indicator (closedBall UpperHalfPlane.I R) (fun _ => (1 : ℂ)) w

theorem ballKernel_rot (R θ : ℝ) (w : ℍ) : ballKernel R (rot θ • w) = ballKernel R w := by
  simp only [ballKernel, Set.indicator, mem_closedBall, dist_rot_smul_I]

theorem ballKernel_measurable (R : ℝ) : AEStronglyMeasurable (ballKernel R) volume :=
  (measurable_const.indicator isClosed_closedBall.measurableSet).aestronglyMeasurable

theorem ballKernel_centre (R : ℝ) (z w : ℍ) :
    ballKernel R ((toSL2R z)⁻¹ • w) = Set.indicator (closedBall z R) (fun _ => (1 : ℂ)) w := by
  simp only [ballKernel, Set.indicator, mem_closedBall]
  congr 1
  conv_rhs => rw [← toSL2R_smul_I z]
  rw [← dist_smul (toSL2R z)⁻¹ w (toSL2R z • UpperHalfPlane.I), inv_smul_smul]

theorem integrableOn_closedBall {G : ℍ → ℂ} (hG : Continuous G) (z : ℍ) (R : ℝ) :
    IntegrableOn G (closedBall z R) :=
  hG.continuousOn.integrableOn_compact (isCompact_closedBall z R)

/-- **Hyperbolic mean-value property.** For every real-`C²` eigenfunction `G` of the positive
Laplacian with eigenvalue `s(1-s)`, every centre `z` and radius `R`,
`∫_{B_R(z)} G dμ = G(z) · ∫_{B_R(i)} (Im w)^s dμ`. -/
theorem setIntegral_closedBall_eigen (z : ℍ) (R : ℝ) {G : ℍ → ℂ} {s : ℂ}
    (hG : IsRealSmoothUpperHalfPlane G)
    (hGe : ∀ z, positiveHyperbolicLaplacian G z = s * (1 - s) * G z) :
    (∫ w in closedBall z R, G w) =
      G z * ∫ w in closedBall UpperHalfPlane.I R, powerEigen s w := by
  set A : GL (Fin 2) ℝ := Matrix.SpecialLinearGroup.toGL (toSL2R z)
  have hA : 0 < A.val.det := by
    show 0 < ((toSL2R z : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ).det
    rw [(toSL2R z).2]; norm_num
  have hAI : A • UpperHalfPlane.I = z := toSL2R_smul_I z
  have hker : ∀ w, ballKernel R (A⁻¹ • w) = Set.indicator (closedBall z R) (fun _ => (1 : ℂ)) w := by
    intro w
    rw [← ballKernel_centre R z w]
    rfl
  have hcont := HyperbolicPointPair.continuous_of_smooth hG
  have hk1 : (fun w => ballKernel R (A⁻¹ • w) * G w) = Set.indicator (closedBall z R) G := by
    funext w; rw [hker]; simp only [Set.indicator]; split_ifs <;> simp
  have hk2 : (fun w => ballKernel R w * powerEigen s w) =
      Set.indicator (closedBall UpperHalfPlane.I R) (powerEigen s) := by
    funext w; simp only [ballKernel, Set.indicator]; split_ifs <;> simp
  have hiG : Integrable (fun w => ballKernel R (A⁻¹ • w) * G w) := by
    rw [hk1]
    exact (integrable_indicator_iff isClosed_closedBall.measurableSet).mpr
      (integrableOn_closedBall hcont z R)
  have hiE : Integrable (fun w => ballKernel R w * powerEigen s w) := by
    rw [hk2]
    exact (integrable_indicator_iff isClosed_closedBall.measurableSet).mpr
      (integrableOn_closedBall (HyperbolicPointPair.continuous_of_smooth (powerEigen_smooth s)) _ R)
  have h := integral_centred_kernel A hA (ballKernel_rot R) (ballKernel_measurable R) hG hGe hiG hiE
  rw [hAI, hk1, hk2] at h
  rw [integral_indicator isClosed_closedBall.measurableSet,
    integral_indicator isClosed_closedBall.measurableSet] at h
  exact h

end GaloisForLFunctions.RHTower.HyperbolicPointPairCentre
