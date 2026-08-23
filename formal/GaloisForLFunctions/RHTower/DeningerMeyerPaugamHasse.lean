import GaloisForLFunctions.RHTower.DeningerMeyerPaugamSpectralPairing

/-!
# Hasse classification by a Paugam zero jet and its reflection

A generalized zeta-zero jet and its reciprocal reflection form a two-coordinate local spectral
observation on genuine Meyer cohomology.  Modulo classes invisible to both coordinates, the global
cohomology is exactly the two-jet profiles that are actually realized.  No completeness or
nondegeneracy premise is imposed.
-/

namespace RHTower

noncomputable section

/-- The paired zero-jet and reflected-zero-jet observation on Meyer cohomology. -/
def deningerMeyerPaugamHasseObservation (d : DeningerMeyerZetaZeroJetDatum) :
    DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ × ℂ where
  toFun u := (d.evaluationLM u, d.reflectedEvaluationLM u)
  map_add' u v := by simp
  map_smul' c u := by simp

@[simp] theorem deningerMeyerPaugamHasseObservation_apply
    (d : DeningerMeyerZetaZeroJetDatum) (u : DeningerMeyerStrongLogCohomology) :
    deningerMeyerPaugamHasseObservation d u =
      (d.evaluationLM u, d.reflectedEvaluationLM u) :=
  rfl

/-- The paired spectral observation loses exactly the classes invisible to both the zero jet and
its reflection. -/
theorem deningerMeyerPaugamHasseObservation_ker
    (d : DeningerMeyerZetaZeroJetDatum) :
    LinearMap.ker (deningerMeyerPaugamHasseObservation d) =
      LinearMap.ker d.evaluationLM ⊓ LinearMap.ker d.reflectedEvaluationLM := by
  ext u
  constructor
  · intro hu
    have h := LinearMap.mem_ker.mp hu
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  · rintro ⟨h₁, h₂⟩
    apply LinearMap.mem_ker.mpr
    rw [Prod.ext_iff]
    exact ⟨LinearMap.mem_ker.mp h₁, LinearMap.mem_ker.mp h₂⟩

/-- Meyer cohomology modulo simultaneous two-jet invisibility is exactly the subspace of paired
spectral profiles that occurs globally. -/
noncomputable def deningerMeyerPaugamHasseQuotientEquivRealizedProfiles
    (d : DeningerMeyerZetaZeroJetDatum) :
    (DeningerMeyerStrongLogCohomology ⧸
      (LinearMap.ker d.evaluationLM ⊓ LinearMap.ker d.reflectedEvaluationLM)) ≃ₗ[ℂ]
      LinearMap.range (deningerMeyerPaugamHasseObservation d) :=
  (Submodule.quotEquivOfEq _ _
    (deningerMeyerPaugamHasseObservation_ker d).symm).trans
      (LinearMap.quotKerEquivRange _)

/-- Two Meyer classes represent the same paired-jet quotient class exactly when their zero-jet and
reflected-zero-jet coordinates both agree. -/
theorem deningerMeyerPaugam_congr_hasse_iff
    (d : DeningerMeyerZetaZeroJetDatum)
    (u v : DeningerMeyerStrongLogCohomology) :
    u - v ∈ LinearMap.ker d.evaluationLM ⊓ LinearMap.ker d.reflectedEvaluationLM ↔
      d.evaluationLM u = d.evaluationLM v ∧
        d.reflectedEvaluationLM u = d.reflectedEvaluationLM v := by
  simp only [Submodule.mem_inf, LinearMap.mem_ker, map_sub, sub_eq_zero]

end

end RHTower
