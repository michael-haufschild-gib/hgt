import GaloisForLFunctions.RHTower.XiMarkedMonodromyMap
import GaloisForLFunctions.RHTower.WindingNumberDegreeBridge
import GaloisForLFunctions.RHTower.WindingXi
import GaloisForLFunctions.RHTower.ArithmeticJointJetExclusion
import GaloisForLFunctions.HTGeometry.PuncturedWindingBaseChange

open Set Filter Topology Metric Complex unitInterval
open GaloisForLFunctions.HTGeometry

namespace RHTower.XiMarkedMonodromy

/-- A small circle at an actual simple Xi zero is an admissible marked-source meridian. -/
theorem exists_local_winding_one (A : Finset ℝ) :
    ∃ s : Source A, ∃ p : Path s s,
      normalizedWindingHom (xiPunctured A) s (FundamentalGroup.fromPath ⟦p⟧) =
        Multiplicative.ofAdd 1 := by
  classical
  obtain ⟨t, _, _, hz, ho⟩ := DeletionMixedRefinement.exists_high_simple_critical_xi 0
  let ρ := DeletionMixedRefinement.criticalResponsePoint t
  have hzero : xi ρ = 0 := hz
  obtain ⟨R, hR, u, _, hu, hfac⟩ := xi_peel_ball ρ
  obtain ⟨W, hW, hw⟩ := windingNumber_xi_zero ρ
  have hev : ∀ᶠ z in 𝓝 ρ, ∀ a : A, value a z ≠ -1 := by
    apply Filter.eventually_all.mpr
    intro a
    apply (value_differentiable a).continuous.continuousAt.eventually_ne
    simp [value, hzero]
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
  obtain ⟨r, hr, hrb⟩ := exists_between (lt_min hε (lt_min hR hW))
  have hrε := (lt_min_iff.mp hrb).1
  have hrR := (lt_min_iff.mp (lt_min_iff.mp hrb).2).1
  have hrW := (lt_min_iff.mp (lt_min_iff.mp hrb).2).2
  let c : ℝ → ℂ := fun θ => ρ + (r : ℂ) * exp (Complex.I * (θ : ℂ))
  have hc : Continuous c := by fun_prop
  have hdist (θ : ℝ) : dist (c θ) ρ = r := by
    simp [c, dist_eq_norm, Complex.norm_exp, abs_of_pos hr]
  have hcn (θ : ℝ) : xi (c θ) ≠ 0 := by
    have hcR : c θ ∈ ball ρ R := by rw [mem_ball, hdist θ]; exact hrR
    rw [hfac _ hcR]
    apply mul_ne_zero _ (hu _ hcR)
    apply pow_ne_zero
    have hsub : c θ - ρ ≠ 0 := by
      change ρ + (r : ℂ) * exp (Complex.I * (θ : ℂ)) - ρ ≠ 0
      simpa using mul_ne_zero (show (r : ℂ) ≠ 0 by exact_mod_cast hr.ne')
        (exp_ne_zero (Complex.I * (θ : ℂ)))
    exact hsub
  have hsource (θ : ℝ) : c θ ∈ sourceSet A := by
    refine ⟨hcn θ, fun a ha => ?_⟩
    exact hball (y := c θ) (by rw [hdist θ]; exact hrε) ⟨a, ha⟩
  have hclose : c 0 = c (2 * Real.pi) := by
    dsimp [c]
    rw [mul_zero, exp_zero]
    rw [show Complex.I * ((2 * Real.pi : ℝ) : ℂ) = 2 * (Real.pi : ℂ) * Complex.I by push_cast; ring,
      exp_two_pi_mul_I]
  let s : Source A := ⟨c 0, hsource 0⟩
  let p : Path s s :=
    { toFun := fun θ => ⟨c ((2 * Real.pi) * (θ : ℝ)), hsource _⟩
      continuous_toFun := (hc.comp
        (show Continuous (fun θ : unitInterval => (2 * Real.pi) * (θ : ℝ)) by fun_prop)).subtype_mk _
      source' := by apply Subtype.ext; simp [s]
      target' := by apply Subtype.ext; simpa [s] using hclose.symm }
  refine ⟨s, p, ?_⟩
  rw [normalizedWindingHom_mk]
  apply congrArg Multiplicative.ofAdd
  have hγ : IsLoop (fun θ => xi (c θ)) 0 (2 * Real.pi) :=
    ⟨xi_differentiable.continuous.comp hc, hcn, congrArg xi hclose⟩
  have he := bottcher_wind_eq_windingNumber
    (fun z : Source A => xi (z : ℂ))
    (xi_differentiable.continuous.comp continuous_subtype_val) (fun z => z.2.1) p hγ
    (fun θ => by simp only [zero_add, sub_zero]; rfl)
  change Bottcher.wind (fun z : Source A => xi (z : ℂ)) _ _ p = 1
  rw [he]
  simpa [c, ρ, ho] using hw r hr hrW

/-- The actual Xi winding map at the fixed source basepoint is onto the integers. -/
theorem xi_winding_surjective (A : Finset ℝ) :
    Function.Surjective (normalizedWindingHom (xiPunctured A) (sourceZero A)) := by
  obtain ⟨s, p, hp⟩ := exists_local_winding_one A
  exact normalizedWindingHom_surjective_of_one (xiPunctured A)
    (PathConnectedSpace.somePath s (sourceZero A)) (FundamentalGroup.fromPath ⟦p⟧) hp

end RHTower.XiMarkedMonodromy
