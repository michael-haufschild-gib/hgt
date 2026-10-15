import GaloisForLFunctions.RHTower.DeningerMeyerFiniteRankSourceSolvability

/-!
# Divisibility of the actual invisible Meyer sector

The kernel of the existing compact-open Xi comparison is preserved by causal
division after repairing one Xi packet. At every other Xi point the shifted
Mellin multiplier is an analytic unit, so no jet can reappear there.

Every finite product of shifted generators is consequently surjective on this
global invisible sector. This identifies a structural property of the remaining
synthesis kernel; it neither assumes nor concludes that the kernel is zero.
-/

open scoped Classical

namespace RHTower

noncomputable section

/-- The unresolved kernel of the existing literal-source Xi comparison. -/
def DeningerMeyerInvisible : Submodule ℂ DeningerMeyerStrongLogCohomology :=
  LinearMap.ker deningerMeyerCompactOpenXiComparison

/-- Centering only multiplies each jet by a nonzero power of `I`. -/
theorem mem_deningerMeyerInvisible_iff (u : DeningerMeyerStrongLogCohomology) :
    u ∈ DeningerMeyerInvisible ↔
      ∀ rho j, deningerMeyerXiSupportJetEvaluationLM rho j u = 0 := by
  induction u using Submodule.Quotient.induction_on with
  | H g =>
    change deningerMeyerCompactOpenXiComparison (Submodule.Quotient.mk g) = 0 ↔ _
    rw [deningerMeyerCompactOpenXiComparison_mk_eq_zero_iff]
    constructor
    · intro h rho j
      have hj := congrFun (congrFun h rho) j
      rw [deningerCompactOpenAllJets_apply, iteratedDeriv_deningerMeyerCenteredMellin,
        deningerMeyer_uncenter_xiSpectralPointSupport] at hj
      rw [deningerMeyerXiSupportJetEvaluationLM_mk,
        deningerMeyerStrongLogMellinJetLM_eq_iteratedDeriv]
      exact (mul_eq_zero.mp hj).resolve_left (pow_ne_zero _ Complex.I_ne_zero)
    · intro h
      funext rho j
      rw [deningerCompactOpenAllJets_apply, iteratedDeriv_deningerMeyerCenteredMellin,
        deningerMeyer_uncenter_xiSpectralPointSupport]
      have hj := h rho j
      rw [deningerMeyerXiSupportJetEvaluationLM_mk,
        deningerMeyerStrongLogMellinJetLM_eq_iteratedDeriv] at hj
      simp only [hj, mul_zero, Pi.zero_apply]

/-- Away from the shifted point, a full zero packet cannot be created by the shift. -/
theorem deningerMeyerXiJets_zero_of_shift
    (tau : XiDivisorSupport) (rho : ℂ) (hne : (tau : ℂ) ≠ rho)
    (u : DeningerMeyerStrongLogCohomology)
    (hu : ∀ j, deningerMeyerXiSupportJetEvaluationLM tau j
      (deningerMeyerCohomologyShift rho u) = 0) :
    ∀ j, deningerMeyerXiSupportJetEvaluationLM tau j u = 0 := by
  induction u using Submodule.Quotient.induction_on with
  | H g =>
    let h : DeningerMeyerStrongLogTarget := deningerMeyerStrongLogGenerator g - rho • g
    have hmk : deningerMeyerCohomologyShift rho (Submodule.Quotient.mk g) =
        Submodule.Quotient.mk h := by
      simp [deningerMeyerCohomologyShift, h]
    have hzero (i : ℕ) (hi : i < xiSupportMultiplicity tau) :
        iteratedDeriv i (deningerMeyerStrongLogMellin h) (tau : ℂ) = 0 := by
      have hz := hu ⟨i, hi⟩
      rw [hmk, deningerMeyerXiSupportJetEvaluationLM_mk,
        deningerMeyerStrongLogMellinJetLM_eq_iteratedDeriv] at hz
      exact hz
    have hfactor : deningerMeyerStrongLogMellin h =
        (fun s : ℂ => s - rho) * deningerMeyerStrongLogMellin g := by
      funext s
      change deningerMeyerStrongLogMellinLM s
        (deningerMeyerStrongLogGenerator g - rho • g) = _
      rw [map_sub, map_smul]
      change deningerMeyerStrongLogMellin (deningerMeyerStrongLogGenerator g) s -
        rho * deningerMeyerStrongLogMellin g s = (s - rho) * deningerMeyerStrongLogMellin g s
      rw [deningerMeyerStrongLogGenerator_mellin]
      ring
    have hga := analyticOnNhd_deningerMeyerStrongLogMellin g.property (tau : ℂ) (Set.mem_univ _)
    have hha := analyticOnNhd_deningerMeyerStrongLogMellin h.property (tau : ℂ) (Set.mem_univ _)
    have horder := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hha).mpr hzero
    have hunit : analyticOrderAt (fun s : ℂ => s - rho) (tau : ℂ) = 0 :=
      analyticOrderAt_eq_zero.mpr (Or.inr (sub_ne_zero.mpr hne))
    rw [hfactor, analyticOrderAt_mul (by fun_prop) hga, hunit, zero_add] at horder
    intro j
    rw [deningerMeyerXiSupportJetEvaluationLM_mk,
      deningerMeyerStrongLogMellinJetLM_eq_iteratedDeriv]
    exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hga).mp horder j j.isLt

/-- Actual invisible forcings admit invisible preimages at every complex shift. -/
theorem deningerMeyerInvisible_shift_preimage (rho : ℂ) (u : DeningerMeyerInvisible) :
    ∃ v : DeningerMeyerInvisible, deningerMeyerCohomologyShift rho v = u := by
  have hu := (mem_deningerMeyerInvisible_iff u).mp u.property
  by_cases hz : xi rho = 0
  · let tau : XiDivisorSupport := ⟨rho, mem_xi_divisor_support_of_eq_zero hz⟩
    have huS : deningerMeyerFiniteXiJetPacketLM {tau} u = 0 := by
      funext q
      exact hu q.1.val q.2
    obtain ⟨v, hv, hvu⟩ := deningerMeyerCohomologyShift_preimage_in_packet_kernel
      {tau} rho (Or.inr ⟨⟨tau, Finset.mem_singleton_self tau⟩, rfl⟩) u huS
    have hvI : v ∈ DeningerMeyerInvisible := by
      apply (mem_deningerMeyerInvisible_iff v).mpr
      intro sigma j
      by_cases hs : sigma = tau
      · subst sigma
        exact congrFun hv ⟨⟨tau, Finset.mem_singleton_self tau⟩, j⟩
      · have hne : (sigma : ℂ) ≠ rho := fun h => hs (Subtype.ext h)
        exact deningerMeyerXiJets_zero_of_shift sigma rho hne v
          (fun k => by rw [hvu]; exact hu sigma k) j
    exact ⟨⟨v, hvI⟩, hvu⟩
  · obtain ⟨v, hvu⟩ := deningerMeyerCohomologyShift_surjective_of_xi_ne_zero rho hz u
    have hvI : v ∈ DeningerMeyerInvisible := by
      apply (mem_deningerMeyerInvisible_iff v).mpr
      intro tau j
      have hne : (tau : ℂ) ≠ rho := by
        intro heq
        exact hz (heq ▸ xi_eq_zero_of_mem_divisor_support tau)
      exact deningerMeyerXiJets_zero_of_shift tau rho hne v
        (fun k => by rw [hvu]; exact hu tau k) j
    exact ⟨⟨v, hvI⟩, hvu⟩

theorem deningerMeyerInvisible_generator_mem (u : DeningerMeyerInvisible) :
    deningerMeyerCohomologyGenerator u ∈ DeningerMeyerInvisible := by
  have hu := (mem_deningerMeyerInvisible_iff u).mp u.property
  apply (mem_deningerMeyerInvisible_iff _).mpr
  intro rho j
  have hS : deningerMeyerFiniteXiJetPacketLM {rho} u = 0 := by
    funext q
    exact hu q.1.val q.2
  exact congrFun (deningerMeyerFiniteXiJetKernel_generator {rho} u hS)
    ⟨⟨rho, Finset.mem_singleton_self rho⟩, j⟩

/-- The actual generator restricted to the existing comparison kernel. -/
def deningerMeyerInvisibleGenerator : Module.End ℂ DeningerMeyerInvisible :=
  deningerMeyerCohomologyGenerator.restrict
    (fun u hu => deningerMeyerInvisible_generator_mem ⟨u, hu⟩)

/-- Every shifted invisible generator is surjective, unconditionally. -/
theorem deningerMeyerInvisibleGenerator_shift_surjective (rho : ℂ) :
    Function.Surjective (deningerMeyerInvisibleGenerator -
      rho • (LinearMap.id : Module.End ℂ DeningerMeyerInvisible)) := by
  intro u
  obtain ⟨v, hv⟩ := deningerMeyerInvisible_shift_preimage rho u
  exact ⟨v, Subtype.ext hv⟩

/-- Global invisible source divisibility by every finite product, including repeated shifts. -/
theorem deningerMeyerInvisibleGeneratorWord_surjective (L : List ℂ) :
    Function.Surjective (deningerMeyerGeneratorWord deningerMeyerInvisibleGenerator L) := by
  induction L with
  | nil => exact fun u => ⟨u, rfl⟩
  | cons rho L ih =>
    exact (deningerMeyerInvisibleGenerator_shift_surjective rho).comp ih

end
end RHTower
