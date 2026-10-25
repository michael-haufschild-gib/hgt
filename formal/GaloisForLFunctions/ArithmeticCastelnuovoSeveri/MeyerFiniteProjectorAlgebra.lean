import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.MeyerFiniteJetAlgebra

/-!
# Finite causal projectors are genuine convolution multipliers

Full Xi jet separation identifies causal projection with block selection.
Local Hasse multiplication then makes each projection a central multiplier;
the value idempotent acts as the identity on its entire local jet block.
-/

noncomputable section
open Complex RHTower
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-- The actual causal projector is exact block selection on every lower Xi jet. -/
theorem meyerFiniteXiCausalProjector_jet (S : Finset XiDivisorSupport)
    (u : DeningerMeyerStrongLogCohomology) (rho : XiDivisorSupport)
    (j : DeningerArithmeticJetIndex rho) :
    deningerMeyerXiSupportJetEvaluationLM rho j (deningerMeyerFiniteXiCausalProjector S u) =
      if rho ∈ S then deningerMeyerXiSupportJetEvaluationLM rho j u else 0 := by
  classical
  by_cases hr : rho ∈ S
  · rw [if_pos hr]
    exact congrFun (deningerMeyerFiniteXiCausalProjector_jets S u) ⟨⟨rho, hr⟩, j⟩
  · rw [if_neg hr]
    exact deningerMeyerFiniteXiCausalSection_other_jet_zero S rho hr j _

private theorem product_local_jet_congr
    (u v w : DeningerMeyerStrongLogCohomology) (rho : XiDivisorSupport)
    (he : ∀ j : DeningerArithmeticJetIndex rho,
      deningerMeyerXiSupportJetEvaluationLM rho j u =
        deningerMeyerXiSupportJetEvaluationLM rho j v)
    (j : DeningerArithmeticJetIndex rho) :
    deningerMeyerXiSupportJetEvaluationLM rho j (deningerMeyerCohomologyConvolution u w) =
      deningerMeyerXiSupportJetEvaluationLM rho j (deningerMeyerCohomologyConvolution v w) := by
  induction u using Submodule.Quotient.induction_on with
  | H g =>
    induction v using Submodule.Quotient.induction_on with
    | H h =>
      induction w using Submodule.Quotient.induction_on with
      | H f =>
        have hm : deningerMeyerHasseMoment (deningerMeyerSourceConvolution g f) j.val (rho : ℂ) =
            deningerMeyerHasseMoment (deningerMeyerSourceConvolution h f) j.val (rho : ℂ) := by
          rw [deningerMeyerHasseMoment_convolution, deningerMeyerHasseMoment_convolution]
          apply Finset.sum_congr rfl
          intro k hk
          have hkm : k < xiSupportMultiplicity rho :=
            lt_of_le_of_lt (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) j.isLt
          have hjet := he ⟨k, hkm⟩
          change deningerMeyerStrongLogMellinJetLM k (rho : ℂ) g =
            deningerMeyerStrongLogMellinJetLM k (rho : ℂ) h at hjet
          simp only [deningerMeyerHasseMoment, hjet]
        have hf : (j.val.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j.val
        have hmul := congrArg (fun z : ℂ => z * (j.val.factorial : ℂ)) hm
        simpa only [deningerMeyerCohomologyConvolution_mk,
          deningerMeyerXiSupportJetEvaluationLM_mk, deningerMeyerHasseMoment,
          div_mul_cancel₀ _ hf] using hmul

/-- Full finite causal projectors are central multipliers of the genuine source algebra. -/
theorem meyerFiniteXiCausalProjector_mul_left (S : Finset XiDivisorSupport)
    (u v : DeningerMeyerStrongLogCohomology) :
    deningerMeyerCohomologyConvolution (deningerMeyerFiniteXiCausalProjector S u) v =
      deningerMeyerFiniteXiCausalProjector S (deningerMeyerCohomologyConvolution u v) := by
  classical
  apply deningerMeyerCohomology_eq_of_XiJets_eq
  intro rho j
  by_cases hr : rho ∈ S
  · rw [meyerFiniteXiCausalProjector_jet, if_pos hr]
    exact product_local_jet_congr _ u v rho
      (fun k => by rw [meyerFiniteXiCausalProjector_jet, if_pos hr]) j
  · rw [meyerFiniteXiCausalProjector_jet, if_neg hr]
    have hz := product_local_jet_congr (deningerMeyerFiniteXiCausalProjector S u) 0 v rho
      (fun k => by rw [meyerFiniteXiCausalProjector_jet, if_neg hr, map_zero]) j
    simpa only [map_zero, LinearMap.zero_apply] using hz

theorem meyerFiniteXiCausalProjector_mul_right (S : Finset XiDivisorSupport)
    (u v : DeningerMeyerStrongLogCohomology) :
    deningerMeyerCohomologyConvolution u (deningerMeyerFiniteXiCausalProjector S v) =
      deningerMeyerFiniteXiCausalProjector S (deningerMeyerCohomologyConvolution u v) := by
  rw [deningerMeyerCohomologyConvolution_comm, meyerFiniteXiCausalProjector_mul_left,
    deningerMeyerCohomologyConvolution_comm v u]

/-- A value idempotent belongs to its own complete causal block. -/
theorem meyerHasseValueClass_projector_fixed (rho : XiDivisorSupport) :
    deningerMeyerFiniteXiCausalProjector {rho}
      (meyerHasseJetClass rho ⟨0, xiSupportMultiplicity_pos rho⟩) =
        meyerHasseJetClass rho ⟨0, xiSupportMultiplicity_pos rho⟩ := by
  classical
  apply deningerMeyerCohomology_eq_of_XiJets_eq
  intro sigma j
  rw [meyerFiniteXiCausalProjector_jet, meyerHasseJetClass_raw_jet]
  by_cases hs : sigma = rho
  · simp only [Finset.mem_singleton, hs, if_true]
  · simp only [Finset.mem_singleton, hs, false_and, if_false]

/-- The local value idempotent acts as the entire finite causal block projector. -/
theorem meyerHasseValueClass_mul_eq_projector (rho : XiDivisorSupport)
    (u : DeningerMeyerStrongLogCohomology) :
    deningerMeyerCohomologyConvolution u
      (meyerHasseJetClass rho ⟨0, xiSupportMultiplicity_pos rho⟩) =
        deningerMeyerFiniteXiCausalProjector {rho} u := by
  classical
  have hp : deningerMeyerCohomologyConvolution
      (deningerMeyerFiniteXiCausalProjector {rho} u)
      (meyerHasseJetClass rho ⟨0, xiSupportMultiplicity_pos rho⟩) =
        deningerMeyerFiniteXiCausalProjector {rho} u := by
    change deningerMeyerCohomologyConvolution
      (deningerMeyerFiniteXiCausalSection {rho} (deningerMeyerFiniteXiJetPacketLM {rho} u)) _ =
        deningerMeyerFiniteXiCausalSection {rho} (deningerMeyerFiniteXiJetPacketLM {rho} u)
    rw [meyerFiniteXiCausalSection_eq_hasse_sum]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
    apply Finset.sum_congr rfl
    intro q _
    obtain ⟨⟨sigma, hs⟩, j⟩ := q
    have he : sigma = rho := Finset.mem_singleton.mp hs
    subst sigma
    rw [meyerHasseJetClass_product_unit]
  calc
    _ = deningerMeyerCohomologyConvolution u
        (deningerMeyerFiniteXiCausalProjector {rho}
          (meyerHasseJetClass rho ⟨0, xiSupportMultiplicity_pos rho⟩)) := by
      rw [meyerHasseValueClass_projector_fixed]
    _ = deningerMeyerFiniteXiCausalProjector {rho}
        (deningerMeyerCohomologyConvolution u
          (meyerHasseJetClass rho ⟨0, xiSupportMultiplicity_pos rho⟩)) :=
      meyerFiniteXiCausalProjector_mul_right _ _ _
    _ = _ := by rw [← meyerFiniteXiCausalProjector_mul_left, hp]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerFiniteXiCausalProjector_jet
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerFiniteXiCausalProjector_mul_left
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerFiniteXiCausalProjector_mul_right
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerHasseValueClass_mul_eq_projector
