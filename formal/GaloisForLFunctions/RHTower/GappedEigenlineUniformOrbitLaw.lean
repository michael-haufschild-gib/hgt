import GaloisForLFunctions.RHTower.RayleighGapProjective

/-!
# Gapped eigenline uniform orbit law

A perturbation of a gapped reference eigenline stays close to an eigenline of
the perturbed self-adjoint operator.  Every norm-preserving functional
calculus that fixes perturbed eigenlines therefore keeps the reference ray
close to itself uniformly in its evolution parameter.

This is deliberately formulated without a time variable.  Unitary time
evolution is one instance; the theorem exposes the exact deterministic
mechanism used by the local-Hamiltonian shortcut-floor obstruction.
-/

open scoped InnerProductSpace
open RCLike

namespace RHTower

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [Nontrivial E]

/-- A norm-bounded perturbation of a Hermitian operator with a gapped top
reference ray has a unit eigenvector with projective defect at most
`2 * delta / gap` from that ray. -/
theorem exists_gappedReference_near_eigenvector
    (H₀ H : E →L[ℂ] E) (hH : (H : E →ₗ[ℂ] E).IsSymmetric)
    {phi : E} {lambda gap delta : ℝ}
    (hphi : ‖phi‖ = 1) (hgap : 0 < gap)
    (hbase : H₀.reApplyInnerSelf phi = lambda)
    (hupper : ∀ x : E,
      H₀.reApplyInnerSelf x ≤
        lambda * ‖x‖ ^ (2 : ℕ) - gap * (‖x‖ ^ (2 : ℕ) - ‖inner ℂ phi x‖ ^ (2 : ℕ)))
    (hpert : ‖H - H₀‖ ≤ delta) :
    ∃ psi : E, ∃ mu : ℝ,
      ‖psi‖ = 1 ∧ H psi = (mu : ℂ) • psi ∧
        1 - ‖inner ℂ phi psi‖ ^ (2 : ℕ) ≤ 2 * delta / gap := by
  letI := FiniteDimensional.proper_rclike ℂ E
  have hsphere : (Metric.sphere (0 : E) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr (by norm_num)
  obtain ⟨psi, hpsi_mem, hmax⟩ :=
    (isCompact_sphere (0 : E) 1).exists_isMaxOn hsphere
      H.reApplyInnerSelf_continuous.continuousOn
  have hpsi : ‖psi‖ = 1 := by simpa using hpsi_mem
  have hpsi₀ : psi ≠ 0 := by
    rw [← norm_ne_zero_iff, hpsi]
    exact one_ne_zero
  let Hsa := hH.toSelfAdjoint
  have hHsa : Hsa.val = H := rfl
  have hmax' : IsMaxOn Hsa.val.reApplyInnerSelf
      (Metric.sphere (0 : E) ‖psi‖) psi := by
    intro x hx
    rw [hHsa]
    exact hmax (by simpa [hpsi] using hx)
  have heig := Hsa.prop.hasEigenvector_of_isMaxOn hpsi₀ hmax'
  let mu : ℝ := ⨆ x : {x : E // x ≠ 0}, Hsa.val.rayleighQuotient x
  have heig' : H psi = (mu : ℂ) • psi := by
    rw [← hHsa]
    exact heig.apply_eq_smul
  have hpert_phi_abs : |(H - H₀).rayleighQuotient phi| ≤ ‖H - H₀‖ :=
    (H - H₀).rayleighQuotient_le_norm phi
  have hpert_psi_abs : |(H - H₀).rayleighQuotient psi| ≤ ‖H - H₀‖ :=
    (H - H₀).rayleighQuotient_le_norm psi
  have hpert_phi : -delta ≤ (H - H₀).reApplyInnerSelf phi := by
    rw [ContinuousLinearMap.rayleighQuotient, hphi, one_pow, div_one] at hpert_phi_abs
    exact le_trans (neg_le_neg hpert) (neg_le_of_abs_le hpert_phi_abs)
  have hpert_psi : (H - H₀).reApplyInnerSelf psi ≤ delta := by
    rw [ContinuousLinearMap.rayleighQuotient, hpsi, one_pow, div_one] at hpert_psi_abs
    exact le_trans (le_of_abs_le hpert_psi_abs) hpert
  have hdecomp_phi :
      H.reApplyInnerSelf phi =
        H₀.reApplyInnerSelf phi + (H - H₀).reApplyInnerSelf phi := by
    simp [ContinuousLinearMap.reApplyInnerSelf_apply, inner_sub_left]
  have hdecomp_psi :
      H.reApplyInnerSelf psi =
        H₀.reApplyInnerSelf psi + (H - H₀).reApplyInnerSelf psi := by
    simp [ContinuousLinearMap.reApplyInnerSelf_apply, inner_sub_left]
  have hmax_phi : H.reApplyInnerSelf phi ≤ H.reApplyInnerSelf psi :=
    hmax (by simpa [hphi])
  have hH₀psi_lower : lambda - 2 * delta ≤ H₀.reApplyInnerSelf psi := by
    rw [hdecomp_phi, hdecomp_psi, hbase] at hmax_phi
    linarith
  have hH₀psi_upper := hupper psi
  rw [hpsi, one_pow] at hH₀psi_upper
  refine ⟨psi, mu, hpsi, heig', ?_⟩
  apply (le_div_iff₀ hgap).2
  nlinarith

/-- If an isometry fixes one ray, a nearby reference ray moves by at most
eight times its squared projective defect from the fixed ray. -/
theorem rayFixed_isometry_uniform_projective_norm_sq_le
    {phi psi : E} (hphi : ‖phi‖ = 1) (hpsi : ‖psi‖ = 1)
    (U : E →L[ℂ] E) (hUnorm : ∀ x, ‖U x‖ = ‖x‖)
    {z : ℂ} (hz : ‖z‖ = 1) (hUpsi : U psi = z • psi) :
    ‖U phi - z • phi‖ ^ (2 : ℕ) ≤
      8 * (1 - ‖inner ℂ psi phi‖ ^ (2 : ℕ)) := by
  obtain ⟨c, _hc, hcnear⟩ :=
    exists_unitScalar_norm_sub_sq_le_two_projectiveDefect
      (𝕜 := ℂ) hpsi hphi
  have hsplit :
      U phi - z • phi =
        U (phi - c • psi) + z • (c • psi - phi) := by
    rw [map_sub, map_smul, hUpsi]
    module
  have hle : ‖U phi - z • phi‖ ≤ 2 * ‖phi - c • psi‖ := by
    rw [hsplit]
    calc
      ‖U (phi - c • psi) + z • (c • psi - phi)‖
          ≤ ‖U (phi - c • psi)‖ + ‖z • (c • psi - phi)‖ := norm_add_le _ _
      _ = ‖phi - c • psi‖ + ‖c • psi - phi‖ := by
        rw [hUnorm, norm_smul, hz, one_mul]
      _ = 2 * ‖phi - c • psi‖ := by
        rw [norm_sub_rev]
        ring
  have hsq : ‖U phi - z • phi‖ ^ (2 : ℕ) ≤ 4 * ‖phi - c • psi‖ ^ (2 : ℕ) := by
    nlinarith [norm_nonneg (U phi - z • phi), norm_nonneg (phi - c • psi)]
  nlinarith

/-- **Gapped eigenline uniform orbit law.**  Under the gapped-reference
hypothesis, every norm-preserving evolution that fixes all eigenlines of the
perturbed operator moves the reference ray by squared distance at most
`16 * delta / gap`, uniformly in the evolution parameter. -/
theorem gappedReference_uniform_rayFixed_orbit
    (H₀ H : E →L[ℂ] E) (hH : (H : E →ₗ[ℂ] E).IsSymmetric)
    {phi : E} {lambda gap delta : ℝ}
    (hphi : ‖phi‖ = 1) (hgap : 0 < gap)
    (hbase : H₀.reApplyInnerSelf phi = lambda)
    (hupper : ∀ x : E,
      H₀.reApplyInnerSelf x ≤
        lambda * ‖x‖ ^ (2 : ℕ) - gap * (‖x‖ ^ (2 : ℕ) - ‖inner ℂ phi x‖ ^ (2 : ℕ)))
    (hpert : ‖H - H₀‖ ≤ delta)
    (U : E →L[ℂ] E) (hUnorm : ∀ x, ‖U x‖ = ‖x‖)
    (hevolution : ∀ (psi : E) (mu : ℝ),
      H psi = (mu : ℂ) • psi →
        ∃ z : ℂ, ‖z‖ = 1 ∧ U psi = z • psi) :
    ∃ z : ℂ, ‖z‖ = 1 ∧
      ‖U phi - z • phi‖ ^ (2 : ℕ) ≤ 16 * delta / gap := by
  obtain ⟨psi, mu, hpsi, heig, hdefect⟩ :=
    exists_gappedReference_near_eigenvector H₀ H hH hphi hgap hbase hupper hpert
  obtain ⟨z, hz, hUpsi⟩ := hevolution psi mu heig
  refine ⟨z, hz, ?_⟩
  have horbit := rayFixed_isometry_uniform_projective_norm_sq_le
    hphi hpsi U hUnorm hz hUpsi
  have hinner : ‖inner ℂ psi phi‖ = ‖inner ℂ phi psi‖ := by
    rw [← inner_conj_symm]
    exact norm_conj _
  rw [hinner] at horbit
  calc
    ‖U phi - z • phi‖ ^ (2 : ℕ)
        ≤ 8 * (1 - ‖inner ℂ phi psi‖ ^ (2 : ℕ)) := horbit
    _ ≤ 8 * (2 * delta / gap) := by gcongr
    _ = 16 * delta / gap := by ring

end RHTower
