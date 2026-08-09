import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Constitutive process tomography

The restriction of linear process responses to an intervention subspace has exactly the dual
annihilator as blind sector.  It is injective exactly for a spanning intervention space.  Every
proper instrument space therefore has a nonzero blind process direction, and every open interior
constraint retains distinct perturbations along such a direction.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

universe u v

/-- Exact blind-sector identity for a linear constitutive process. -/
theorem constitutiveProcessRestriction_ker_eq_dualAnnihilator
    {K : Type u} {E : Type v} [Field K] [AddCommGroup E] [Module K E]
    (U : Subspace K E) :
    LinearMap.ker U.dualRestrict = U.dualAnnihilator :=
  U.dualRestrict_ker_eq_dualAnnihilator

/-- A joint intervention subspace reconstructs every linear process exactly iff it spans. -/
theorem constitutiveProcessRestriction_injective_iff_eq_top
    {K : Type u} {E : Type v} [Field K] [AddCommGroup E] [Module K E]
    (U : Subspace K E) :
    Function.Injective U.dualRestrict ↔ U = ⊤ := by
  rw [← LinearMap.ker_eq_bot, U.dualRestrict_ker_eq_dualAnnihilator]
  constructor
  · intro h
    have htop : (⊤ : Subspace K E).dualAnnihilator = U.dualAnnihilator := by
      rw [Submodule.dualAnnihilator_top, h]
    exact (Subspace.dualAnnihilator_inj.mp htop).symm
  · intro h
    rw [h, Submodule.dualAnnihilator_top]

/-- A proper intervention subspace has a nonzero process direction invisible to every experiment. -/
theorem constitutiveProcess_blindDirection_exists_iff_ne_top
    {K : Type u} {E : Type v} [Field K] [AddCommGroup E] [Module K E]
    (U : Subspace K E) :
    (∃ Δ : Module.Dual K E, Δ ≠ 0 ∧ U.dualRestrict Δ = 0) ↔ U ≠ ⊤ := by
  constructor
  · rintro ⟨Δ, hΔ, hblind⟩ htop
    have hinj : Function.Injective U.dualRestrict :=
      (constitutiveProcessRestriction_injective_iff_eq_top U).2 htop
    exact hΔ (hinj (hblind.trans (map_zero U.dualRestrict).symm))
  · intro hU
    have hker : LinearMap.ker U.dualRestrict ≠ ⊥ := by
      intro hbot
      have hinj : Function.Injective U.dualRestrict := LinearMap.ker_eq_bot.mp hbot
      exact hU ((constitutiveProcessRestriction_injective_iff_eq_top U).1 hinj)
    obtain ⟨Δ, hmem, hΔ⟩ := (LinearMap.ker U.dualRestrict).ne_bot_iff.mp hker
    exact ⟨Δ, hΔ, LinearMap.mem_ker.mp hmem⟩

/-- Every scalar translate along a blind direction has the same complete experiment record. -/
theorem constitutiveProcess_affineBlindFamily_sameRecord
    {K : Type u} {E : Type v} [Field K] [AddCommGroup E] [Module K E]
    (U : Subspace K E) (W Δ : Module.Dual K E)
    (hΔ : U.dualRestrict Δ = 0) (c : K) :
    U.dualRestrict (W + c • Δ) = U.dualRestrict W := by
  rw [map_add, map_smul, hΔ, smul_zero, add_zero]

/-- An open interior constraint cannot eliminate a nonzero blind direction: sufficiently small
opposite perturbations remain admissible and distinct. -/
theorem constitutiveOpenConstraint_blindDirection_persists
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : Set E} (hP : IsOpen P) {W Δ : E} (hW : W ∈ P) (hΔ : Δ ≠ 0) :
    ∃ ε : ℝ,
      0 < ε ∧
      W + ε • Δ ∈ P ∧
      W - ε • Δ ∈ P ∧
      W + ε • Δ ≠ W - ε • Δ := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hP W hW
  let ε : ℝ := r / (2 * ‖Δ‖)
  have hnorm : 0 < ‖Δ‖ := norm_pos_iff.mpr hΔ
  have hε : 0 < ε := div_pos hr (mul_pos zero_lt_two hnorm)
  have hscale : ε * ‖Δ‖ = r / 2 := by
    dsimp [ε]
    field_simp [ne_of_gt hnorm]
  have hdist_plus : dist (W + ε • Δ) W < r := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hε,
      hscale]
    linarith
  have hdist_minus : dist (W - ε • Δ) W < r := by
    rw [dist_comm, dist_eq_norm]
    simp only [sub_sub_cancel, norm_smul, Real.norm_eq_abs, abs_of_pos hε, hscale]
    linarith
  refine ⟨ε, hε, hball hdist_plus, hball hdist_minus, ?_⟩
  intro heq
  have hv : ε • Δ = -(ε • Δ) := by
    apply add_left_cancel (a := W)
    simpa [sub_eq_add_neg] using heq
  have hzero2 : ε • Δ + ε • Δ = 0 := by
    calc
      ε • Δ + ε • Δ = -(ε • Δ) + ε • Δ := congrArg (fun x ↦ x + ε • Δ) hv
      _ = 0 := neg_add_cancel (ε • Δ)
  have hzero : (2 * ε) • Δ = 0 := by
    rw [mul_smul, two_smul]
    exact hzero2
  exact hΔ ((smul_eq_zero.mp hzero).resolve_left (mul_ne_zero two_ne_zero hε.ne'))

end GaloisForLFunctions.HTGeometry
