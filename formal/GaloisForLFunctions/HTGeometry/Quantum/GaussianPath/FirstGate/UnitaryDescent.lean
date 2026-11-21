import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.FirstGate.ContactMargin
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Complex.Basic

/-! # A local unitary direction that strictly improves a spectral contact -/
open Set Metric
open scoped InnerProductSpace
namespace GaloisForLFunctions.HTGeometry.FirstGate
noncomputable section

/-- Improving the real overlap at every minimizing vector moves an
entire unitary target strictly inside its original operator-norm ball.
Only a quadratic Taylor remainder along the physical gate is needed. -/
theorem unitary_descent {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [ProperSpace E]
    [Nonempty (sphere (0:E) 1)] (U K : E →L[ℂ] E) (V : ℝ → E →L[ℂ] E)
    {ε M : ℝ} (hε : 0 < ε) (hM : 0≤M)
    (hU : ∀ v, ‖U v‖=‖v‖) (hV : ∀ t v, ‖V t v‖=‖v‖)
    (hrem : ∀ t : ℝ, ‖V t-ContinuousLinearMap.id ℂ E-(t:ℂ) • K‖ ≤ M*t^2)
    (hface : ∀ v : E, ‖v‖=1 → 1-ε^2/2 ≤ (⟪U v,v⟫_ℂ).re)
    (hdir : ∀ v : E, ‖v‖=1 → (⟪U v,v⟫_ℂ).re=1-ε^2/2 → 0 < (⟪U v,K v⟫_ℂ).re) :
    ∃ t > (0:ℝ), ‖U-V t‖ < ε := by
  let S := sphere (0:E) 1
  let f (v : S) := (⟪U v.val,v.val⟫_ℂ).re-(1-ε^2/2)
  let g (v : S) := (⟪U v.val,K v.val⟫_ℂ).re
  have hnorm (v : S) : ‖v.val‖=1 := mem_sphere_zero_iff_norm.mp v.property
  have hf : Continuous f := (Complex.continuous_re.comp ((U.continuous.comp continuous_subtype_val).inner
    continuous_subtype_val)).sub continuous_const
  have hg : Continuous g := Complex.continuous_re.comp ((U.continuous.comp continuous_subtype_val).inner
    (K.continuous.comp continuous_subtype_val))
  obtain ⟨t,ht,c,hc,hmargin⟩ := strict_quadratic_margin f g hf hg
    (fun v => sub_nonneg.mpr (hface _ (hnorm v))) (fun v hv => hdir _ (hnorm v) (sub_eq_zero.mp hv)) hM
  let A := V t-ContinuousLinearMap.id ℂ E-(t:ℂ) • K
  have improve (v : S) : ‖(U-V t) v.val‖ < ε := by
    have hlin := hmargin t ⟨ht,le_rfl⟩ v
    have hR : |(⟪U v.val,A v.val⟫_ℂ).re| ≤ M*t^2 := by
      refine (Complex.abs_re_le_norm _).trans ((norm_inner_le_norm _ _).trans ?_)
      rw [hU,hnorm,one_mul]
      have h := A.le_opNorm v.val
      rw [hnorm,mul_one] at h
      exact h.trans (hrem t)
    have he : V t v.val=v.val+(t:ℂ) • K v.val+A v.val := by
      simp only [A,ContinuousLinearMap.sub_apply,ContinuousLinearMap.id_apply,ContinuousLinearMap.smul_apply]
      abel
    have hinner : (⟪U v.val,V t v.val⟫_ℂ).re =
        (⟪U v.val,v.val⟫_ℂ).re+t*g v+(⟪U v.val,A v.val⟫_ℂ).re := by
      rw [he,inner_add_right,inner_add_right,inner_smul_right]
      simp only [g,Complex.add_re,Complex.ofReal_mul_re]
    apply (sq_lt_sq₀ (norm_nonneg _) hε.le).mp
    rw [ContinuousLinearMap.sub_apply,norm_sub_sq (𝕜 := ℂ),hU,hV,hnorm,hinner]
    dsimp only [f] at hlin
    linarith only [hlin,(abs_le.mp hR).1,mul_pos hc ht]
  obtain ⟨w,_,hw⟩ := isCompact_univ.exists_isMaxOn (univ_nonempty : (univ : Set S).Nonempty)
    ((((U-V t).continuous.comp continuous_subtype_val).norm).continuousOn)
  refine ⟨t,ht,(ContinuousLinearMap.opNorm_le_of_unit_norm (norm_nonneg ((U-V t) w.val)) ?_).trans_lt (improve w)⟩
  intro v hv
  exact hw (mem_univ (⟨v,mem_sphere_zero_iff_norm.mpr hv⟩ : S))

#print axioms unitary_descent
end
end GaloisForLFunctions.HTGeometry.FirstGate
