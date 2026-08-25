import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaStokesCubicDiagonalReesTransversality

/-!
# Cubic Xi moving-charge Rees dissipation

Fixed-charge transport between complete threshold contraction and unit Rees scale is impossible.
This module classifies the surviving moving-charge alternative.  Every contracted/unit landing pair
obeys an exact rank--terminal--block balance.  Terminal isometry forces physical-rank inflation;
preserving rank magnitude instead forces terminal microstalk energy to strictly decrease by exactly
the positive canonical block coarea activated at unit scale.

No moving landing pair or RH conclusion is asserted.
-/

open GaloisForLFunctions
open GaloisForLFunctions.IrregularStokes
open GaloisForLFunctions.IrregularStokes.GlobalPuiseuxWitt

namespace RHTower

noncomputable section

private theorem cubicMalgrangeLanding_totalBlockEnergy_pos
    {p : ℕ} {n m K N : Fin (p + 1) → ℕ}
    {genus : ℕ} {d : LocalData p n m K N} {parameter : ReesParameter d}
    (x : routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber
      genus d parameter) :
    0 < ∑ a, (d a).toOrbitCoareaDatum.blockEnergy (x.1.1 a) := by
  have hxne :=
    routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber_charge_ne_zero x
  have hlocal : ∃ a, x.1.1 a ≠ 0 := by
    by_contra h
    push Not at h
    apply hxne
    apply Subtype.ext
    funext a i
    exact congrFun (h a) i
  obtain ⟨a, ha⟩ := hlocal
  have hlift :
      (d a).toOrbitCoareaDatum.liftCharge (x.1.1 a) ≠ 0 := by
    intro hlift
    apply ha
    funext i
    obtain ⟨branch, hbranch⟩ :=
      (d a).toOrbitCoareaDatum.orbit_surjective i
    have hzero := congrFun hlift branch
    simpa [OrbitCoareaDatum.liftCharge, hbranch] using hzero
  have hblockpos :
      0 < (d a).toOrbitCoareaDatum.blockEnergy (x.1.1 a) := by
    simpa [OrbitCoareaDatum.blockEnergy] using
      (d a).toOrbitCoareaDatum.cuts.toPositivePendantCutFamily.positive_edge_energy hlift
  apply Finset.sum_pos'
  · intro b _
    exact (d b).toOrbitCoareaDatum.blockEnergy_nonneg (x.1.1 b)
  · exact ⟨a, Finset.mem_univ _, hblockpos⟩

/-- Arbitrary contracted and unit cubic Xi landings obey one exact exchange law between terminal
microstalk energy, activated block coarea, and the unique physical-rank square.  In particular,
terminal-isometric transport must strictly increase physical-rank magnitude. -/
theorem routePPrimitiveGammaJuliaStokesCubicMovingLanding_rankTerminalBlock_balance
    {p : ℕ} {n m K N : Fin (p + 1) → ℕ}
    {genus : ℕ} {d : LocalData p n m K N}
    (x₀ : routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber
      genus d (fun _ _ => 0))
    (x₁ : routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber
      genus d (fun _ _ => 1)) :
    (∑ a, (d a).toOrbitCoareaDatum.terminalEnergy (x₀.1.1 a)) +
          (-globalRankCoefficient genus d) * commonRankLinear d x₁.1 ^ 2 =
        (∑ a, (d a).toOrbitCoareaDatum.terminalEnergy (x₁.1.1 a)) +
          (∑ a, (d a).toOrbitCoareaDatum.blockEnergy (x₁.1.1 a)) +
          (-globalRankCoefficient genus d) * commonRankLinear d x₀.1 ^ 2 ∧
      0 < -globalRankCoefficient genus d ∧
      0 < ∑ a, (d a).toOrbitCoareaDatum.blockEnergy (x₁.1.1 a) ∧
      ((∑ a, (d a).toOrbitCoareaDatum.terminalEnergy (x₀.1.1 a)) =
          ∑ a, (d a).toOrbitCoareaDatum.terminalEnergy (x₁.1.1 a) →
        commonRankLinear d x₀.1 ^ 2 < commonRankLinear d x₁.1 ^ 2) := by
  have hpositiveZero :
      globalReesPositiveForm d (fun _ _ => 0) x₀.1 =
        ∑ a, (d a).toOrbitCoareaDatum.terminalEnergy (x₀.1.1 a) := by
    simp [globalReesPositiveForm, localReesPositiveForm_apply,
      OrbitCoareaDatum.reesBlockEnergy]
  have hpositiveOne :
      globalReesPositiveForm d (fun _ _ => 1) x₁.1 =
        (∑ a, (d a).toOrbitCoareaDatum.terminalEnergy (x₁.1.1 a)) +
          ∑ a, (d a).toOrbitCoareaDatum.blockEnergy (x₁.1.1 a) := by
    simp [globalReesPositiveForm, localReesPositiveForm_apply,
      OrbitCoareaDatum.reesBlockEnergy, OrbitCoareaDatum.blockEnergy,
      OrbitCoareaDatum.cutCharge, Finset.sum_add_distrib]
  have hdecompZero := globalReesWittForm_eq_positive_add_oneRank
    genus d (fun _ _ => 0) x₀.1
  have hdecompOne := globalReesWittForm_eq_positive_add_oneRank
    genus d (fun _ _ => 1) x₁.1
  rw [hpositiveZero] at hdecompZero
  rw [hpositiveOne] at hdecompOne
  have hbalance :
      (∑ a, (d a).toOrbitCoareaDatum.terminalEnergy (x₀.1.1 a)) +
            (-globalRankCoefficient genus d) * commonRankLinear d x₁.1 ^ 2 =
          (∑ a, (d a).toOrbitCoareaDatum.terminalEnergy (x₁.1.1 a)) +
            (∑ a, (d a).toOrbitCoareaDatum.blockEnergy (x₁.1.1 a)) +
            (-globalRankCoefficient genus d) * commonRankLinear d x₀.1 ^ 2 := by
    linarith [x₀.2, x₁.2]
  have hcoefficient : 0 < -globalRankCoefficient genus d :=
    neg_pos.mpr
      (routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber_rankCoefficient_neg
        (fun _ _ => le_rfl) x₀)
  have hblock := cubicMalgrangeLanding_totalBlockEnergy_pos x₁
  refine ⟨hbalance, hcoefficient, hblock, ?_⟩
  intro hterminal
  nlinarith

/-- Any common-rank-magnitude-preserving moving cubic Xi landing from contracted to unit Rees
scale dissipates terminal microstalk energy by exactly the activated positive Stokes block coarea.
In particular, terminal-isometric moving transport is impossible. -/
theorem routePPrimitiveGammaJuliaStokesCubicRankMagnitudePreservingMovingLanding_terminalEnergy_dissipation
    {p : ℕ} {n m K N : Fin (p + 1) → ℕ}
    {genus : ℕ} {d : LocalData p n m K N}
    (x₀ : routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber
      genus d (fun _ _ => 0))
    (x₁ : routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber
      genus d (fun _ _ => 1))
    (hrank : commonRankLinear d x₀.1 ^ 2 = commonRankLinear d x₁.1 ^ 2) :
    (∑ a, (d a).toOrbitCoareaDatum.terminalEnergy (x₀.1.1 a)) =
        (∑ a, (d a).toOrbitCoareaDatum.terminalEnergy (x₁.1.1 a)) +
          ∑ a, (d a).toOrbitCoareaDatum.blockEnergy (x₁.1.1 a) ∧
      0 < ∑ a, (d a).toOrbitCoareaDatum.blockEnergy (x₁.1.1 a) ∧
      (∑ a, (d a).toOrbitCoareaDatum.terminalEnergy (x₁.1.1 a)) <
        ∑ a, (d a).toOrbitCoareaDatum.terminalEnergy (x₀.1.1 a) := by
  obtain ⟨hbalance, _, hblock, _⟩ :=
    routePPrimitiveGammaJuliaStokesCubicMovingLanding_rankTerminalBlock_balance x₀ x₁
  have hexact :
      (∑ a, (d a).toOrbitCoareaDatum.terminalEnergy (x₀.1.1 a)) =
        (∑ a, (d a).toOrbitCoareaDatum.terminalEnergy (x₁.1.1 a)) +
          ∑ a, (d a).toOrbitCoareaDatum.blockEnergy (x₁.1.1 a) := by
    nlinarith
  exact ⟨hexact, hblock, by linarith⟩

end

end RHTower
