import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceTransformChamber

/-! Compact frequency families retain one uniform bound on the original horizon source. -/
namespace RHTower.D4BMJointSource
open Complex Set Filter Topology D4BMLaplaceRadial
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- A compact frequency family of literal reduced sources has one common horizon profile bound. -/
theorem reducedCoefficient_family_norm_le_exp (s a J : ℂ) (T K : ℂ → ℂ) (Ω : Set ℂ)
    (hΩ : IsCompact Ω) (hT : ContinuousOn T Ω) (hK : ContinuousOn K Ω) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ w ∈ Ω, ∀ t < 0,
      ‖K w*reducedCoefficient s w a (T w) t*J‖ ≤ B*Real.exp ((w.re+2)*t) := by
  let F : ℂ × ℝ → ℂ := fun p =>
    K p.1*(T p.1*(sourceHorizonProfile s a 0 p.2+p.1*sourceHorizonProfile s a 1 p.2))*J
  have hT' : ContinuousOn (fun p : ℂ × ℝ => T p.1) (Ω ×ˢ Icc 0 1) :=
    hT.comp continuous_fst.continuousOn (fun _ h => h.1)
  have hK' : ContinuousOn (fun p : ℂ × ℝ => K p.1) (Ω ×ˢ Icc 0 1) :=
    hK.comp continuous_fst.continuousOn (fun _ h => h.1)
  have hF (i : Fin 2) : ContinuousOn (fun p : ℂ × ℝ => sourceHorizonProfile s a i p.2) (Ω ×ˢ Icc 0 1) :=
    (sourceHorizonProfile_continuousOn s a i).comp continuous_snd.continuousOn (fun _ h => h.2)
  have hc : ContinuousOn F (Ω ×ˢ Icc 0 1) :=
    (hK'.mul (hT'.mul ((hF 0).add (continuous_fst.continuousOn.mul (hF 1))))).mul continuousOn_const
  obtain ⟨C,hC⟩ := (hΩ.prod isCompact_Icc).exists_bound_of_continuousOn hc
  refine ⟨max C 0,le_max_right _ _,fun w hw t ht => ?_⟩
  have hb : ‖F (w,radialUnit t)‖ ≤ max C 0 :=
    (hC _ ⟨hw,(radialUnit_bounds t ht).1.le,(radialUnit_bounds t ht).2.le⟩).trans (le_max_left _ _)
  have he : K w*reducedCoefficient s w a (T w) t*J =
      Complex.exp ((w+2)*(t:ℂ))*F (w,radialUnit t) := by
    rw [reducedCoefficient_frequency_horizon]
    dsimp [F]
    ring
  rw [he,norm_mul,Complex.norm_exp]
  have hre : ((w+2)*(t:ℂ)).re = (w.re+2)*t := by simp
  rw [hre]
  exact (mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le).trans_eq (mul_comm _ _)

end
end RHTower.D4BMJointSource
