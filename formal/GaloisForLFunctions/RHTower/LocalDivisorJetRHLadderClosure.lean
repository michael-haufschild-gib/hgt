import GaloisForLFunctions.RHTower.LocalDivisorJetRelativeKOne
import GaloisForLFunctions.RHTower.LocalDivisorJetAdamsIsometric

/-!
# Exact RH closure of local-divisor-jet ladder interfaces

Several local-divisor-jet conditions force simplicity only at hypothetical right-half Xi zeros.
The first divisor rung then contradicts that simplicity.  Conversely RH empties the indexing
locus, so every such local condition is automatic.  This module records the resulting exact
criteria for every positive ladder rung.
-/

namespace RHTower

noncomputable section

/-- A positive Xi divisor rung paired with reversible prime-power action on every hypothetical
right-half local jet is exactly RH. -/
theorem rhLadder_and_rightLocalPrimePowerEquiv_iff_riemannHypothesis
    {k : ℕ} (hk : 1 ≤ k) :
    (RHLadder k ∧
      (∀ ρ ∈ rightHalf, xi ρ = 0 →
        ∃ n : ℕ, (analyticOrderAt xi ρ).toNat ≤ n ∧
          ∃ F : LocalDivisorJet ℂ (analyticOrderAt xi ρ).toNat ≃+*
              LocalDivisorJet ℂ (analyticOrderAt xi ρ).toNat,
            F (localDivisorJetVariable ℂ (analyticOrderAt xi ρ).toNat) =
              (localDivisorJetVariable ℂ (analyticOrderAt xi ρ).toNat) ^ n)) ↔
      RiemannHypothesis := by
  constructor
  · rintro ⟨hladder, hprime⟩
    exact riemannHypothesis_of_rhLadder_one_of_rightLocalPrimePowerEquiv
      (rhLadder_imp_one hk hladder) hprime
  · intro hRH
    refine ⟨(rh_iff_forall_ladder.mp hRH) k, ?_⟩
    intro ρ hρ hzero
    exact ((rh_iff_xi_ne_zero_right.mp hRH) ρ hρ hzero).elim

/-- A positive Xi divisor rung paired with triviality of every hypothetical right-half
infinitesimal relative unit is exactly RH. -/
theorem rhLadder_and_rightInfinitesimalUnitTrivial_iff_riemannHypothesis
    {k : ℕ} (hk : 1 ≤ k) :
    (RHLadder k ∧
      (∀ ρ ∈ rightHalf, xi ρ = 0 →
        localDivisorJetInfinitesimalUnit ℂ
          (analyticOrderAt xi ρ).toNat = 1)) ↔
      RiemannHypothesis := by
  constructor
  · rintro ⟨hladder, hunit⟩
    exact riemannHypothesis_of_rhLadder_one_of_rightInfinitesimalUnitTrivial
      (rhLadder_imp_one hk hladder) hunit
  · intro hRH
    refine ⟨(rh_iff_forall_ladder.mp hRH) k, ?_⟩
    intro ρ hρ hzero
    exact ((rh_iff_xi_ne_zero_right.mp hRH) ρ hρ hzero).elim

/-- A positive Xi divisor rung paired with vanishing of every hypothetical right-half logarithmic
relative regulator is exactly RH. -/
theorem rhLadder_and_rightLogUnitVanishing_iff_riemannHypothesis
    {k : ℕ} (hk : 1 ≤ k) :
    (RHLadder k ∧
      (∀ ρ ∈ rightHalf, xi ρ = 0 →
        localDivisorJetLogUnit (analyticOrderAt xi ρ).toNat = 0)) ↔
      RiemannHypothesis := by
  constructor
  · rintro ⟨hladder, hlog⟩
    exact riemannHypothesis_of_rhLadder_one_of_rightLogUnitVanishing
      (rhLadder_imp_one hk hladder) hlog
  · intro hRH
    refine ⟨(rh_iff_forall_ladder.mp hRH) k, ?_⟩
    intro ρ hρ hzero
    exact ((rh_iff_xi_ne_zero_right.mp hRH) ρ hρ hzero).elim

/-- A positive Xi divisor rung paired with pure Adams-dilation weights on every hypothetical
right-half local jet is exactly RH. -/
theorem rhLadder_and_rightAdamsDilationPure_iff_riemannHypothesis
    {k : ℕ} (hk : 1 ≤ k) :
    (RHLadder k ∧
      (∀ ρ ∈ rightHalf, xi ρ = 0 →
        ∃ n : ℕ, 2 ≤ n ∧
          ∃ r : ℝ, ∀ j : Fin (analyticOrderAt xi ρ).toNat,
            ‖((n : ℂ) ^ (j : ℕ))‖ = r)) ↔
      RiemannHypothesis := by
  constructor
  · rintro ⟨hladder, hpure⟩
    exact riemannHypothesis_of_rhLadder_one_of_rightAdamsDilationPure
      (rhLadder_imp_one hk hladder) hpure
  · intro hRH
    refine ⟨(rh_iff_forall_ladder.mp hRH) k, ?_⟩
    intro ρ hρ hzero
    exact ((rh_iff_xi_ne_zero_right.mp hRH) ρ hρ hzero).elim

/-- Symplectic right-half local jets with quasi-unipotent genuine Adams dilation are exactly RH. -/
theorem
    rightSymplecticRealization_and_rightAdamsDilationQuasiUnipotent_iff_riemannHypothesis :
    ((∀ ρ ∈ rightHalf, xi ρ = 0 → SymplecticRealization ρ) ∧
      (∀ ρ ∈ rightHalf, xi ρ = 0 →
        ∃ n : ℕ, 2 ≤ n ∧
          AdamsDilationQuasiUnipotent (analyticOrderAt xi ρ).toNat n)) ↔
      RiemannHypothesis := by
  constructor
  · rintro ⟨hsymplectic, hquasi⟩
    exact
      riemannHypothesis_of_rightSymplecticRealization_of_rightAdamsDilationQuasiUnipotent
        hsymplectic hquasi
  · intro hRH
    refine ⟨?_, ?_⟩
    · intro ρ hρ hzero
      exact ((rh_iff_xi_ne_zero_right.mp hRH) ρ hρ hzero).elim
    · intro ρ hρ hzero
      exact ((rh_iff_xi_ne_zero_right.mp hRH) ρ hρ hzero).elim

/-- Symplectic right-half local jets with power-bounded genuine Adams dilation are exactly RH. -/
theorem
    rightSymplecticRealization_and_rightAdamsDilationPowerBounded_iff_riemannHypothesis :
    ((∀ ρ ∈ rightHalf, xi ρ = 0 → SymplecticRealization ρ) ∧
      (∀ ρ ∈ rightHalf, xi ρ = 0 →
        ∃ n : ℕ, 2 ≤ n ∧
          AdamsDilationPowerBounded (analyticOrderAt xi ρ).toNat n)) ↔
      RiemannHypothesis := by
  constructor
  · rintro ⟨hsymplectic, hbounded⟩
    exact
      riemannHypothesis_of_rightSymplecticRealization_of_rightAdamsDilationPowerBounded
        hsymplectic hbounded
  · intro hRH
    refine ⟨?_, ?_⟩
    · intro ρ hρ hzero
      exact ((rh_iff_xi_ne_zero_right.mp hRH) ρ hρ hzero).elim
    · intro ρ hρ hzero
      exact ((rh_iff_xi_ne_zero_right.mp hRH) ρ hρ hzero).elim

/-- A symplectic right-half realization with a faithful isometric Adams eigenpacket is exactly
RH. -/
theorem
    rightSymplecticRealization_and_rightAdamsDilationIsometricEigenpacket_iff_riemannHypothesis
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] :
    ((∀ ρ ∈ rightHalf, xi ρ = 0 → SymplecticRealization ρ) ∧
      (∀ ρ ∈ rightHalf, xi ρ = 0 →
        ∃ n : ℕ, 2 ≤ n ∧
          ∃ v : Fin (analyticOrderAt xi ρ).toNat → H,
            (∀ j, v j ≠ 0) ∧
            ∃ U : H →ₗᵢ[ℂ] H,
              ∀ j, U (v j) = ((n : ℂ) ^ (j : ℕ)) • v j)) ↔
      RiemannHypothesis := by
  constructor
  · rintro ⟨hsymplectic, hiso⟩
    exact
      riemannHypothesis_of_rightSymplecticRealization_of_rightAdamsDilationIsometricEigenpacket
        hsymplectic hiso
  · intro hRH
    refine ⟨?_, ?_⟩
    · intro ρ hρ hzero
      exact ((rh_iff_xi_ne_zero_right.mp hRH) ρ hρ hzero).elim
    · intro ρ hρ hzero
      exact ((rh_iff_xi_ne_zero_right.mp hRH) ρ hρ hzero).elim

/-- A polarized right-half Adams packet faithfully embedded in one isometry is exactly RH. -/
theorem rightPolarizedAdamsIsometricEigenpacket_iff_riemannHypothesis
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] :
    ((∀ ρ ∈ rightHalf, xi ρ = 0 →
        LocalAdamsSymplecticPolarization (analyticOrderAt xi ρ).toNat) ∧
      (∀ ρ ∈ rightHalf, xi ρ = 0 →
        ∃ n : ℕ, 2 ≤ n ∧
          ∃ v : Fin (analyticOrderAt xi ρ).toNat → H,
            (∀ j, v j ≠ 0) ∧
            ∃ U : H →ₗᵢ[ℂ] H,
              ∀ j, U (v j) = ((n : ℂ) ^ (j : ℕ)) • v j)) ↔
      RiemannHypothesis := by
  constructor
  · rintro ⟨hpol, hiso⟩
    exact riemannHypothesis_of_rightPolarizedAdamsIsometricEigenpacket hpol hiso
  · intro hRH
    refine ⟨?_, ?_⟩
    · intro ρ hρ hzero
      exact ((rh_iff_xi_ne_zero_right.mp hRH) ρ hρ hzero).elim
    · intro ρ hρ hzero
      exact ((rh_iff_xi_ne_zero_right.mp hRH) ρ hρ hzero).elim

/-- A polarized right-half Adams packet faithfully embedded in one contraction is exactly RH. -/
theorem rightPolarizedAdamsContractiveEigenpacket_iff_riemannHypothesis
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] :
    ((∀ ρ ∈ rightHalf, xi ρ = 0 →
        LocalAdamsSymplecticPolarization (analyticOrderAt xi ρ).toNat) ∧
      (∀ ρ ∈ rightHalf, xi ρ = 0 →
        ∃ n : ℕ, 2 ≤ n ∧
          ∃ v : Fin (analyticOrderAt xi ρ).toNat → H,
            (∀ j, v j ≠ 0) ∧
            ∃ U : H →L[ℂ] H,
              (∀ x, ‖U x‖ ≤ ‖x‖) ∧
              ∀ j, U (v j) = ((n : ℂ) ^ (j : ℕ)) • v j)) ↔
      RiemannHypothesis := by
  constructor
  · rintro ⟨hpol, hcontractive⟩
    exact riemannHypothesis_of_rightPolarizedAdamsContractiveEigenpacket hpol hcontractive
  · intro hRH
    refine ⟨?_, ?_⟩
    · intro ρ hρ hzero
      exact ((rh_iff_xi_ne_zero_right.mp hRH) ρ hρ hzero).elim
    · intro ρ hρ hzero
      exact ((rh_iff_xi_ne_zero_right.mp hRH) ρ hρ hzero).elim

end

end RHTower
