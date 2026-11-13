import GaloisForLFunctions.HTGeometry.HardyBoundary.HalfLineCausalCyclicity
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.TheCriticalHalfLineLaplaceMultiplierIsOuter

/-!
# Causal translations of the critical half-line state are dense

The actual critical state's Cayley Laplace multiplier is outer. Exact
Paley–Wiener transport therefore makes the reflected state cyclic for causal
translations on the positive half-line.
-/

noncomputable section
open MeasureTheory Set Filter Topology Metric Zeta23
open _root_.RHTower

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory ArithmeticCastelnuovoSeveri HTGeometry WindowTowerOfSpecZ
open _root_.HTGeometry

/-- The actual critical profile reflected into positive-half-line L². -/
def reflectedCriticalHalfLineDatum {W₀ : ℝ} {F : ℝ → ℝ}
    (hF : IsCriticalHalfLineGroundState W₀ F) : BurnolHalfLineL2 :=
  (memLp_reflected_negativeProfile
    (criticalHalfLineEnergyDomain_of_groundState hF).memLp_complex).toLp
      (fun u => cx F (-u))

/-- The L² representative retains the exact critical-state Laplace transform. -/
theorem criticalLaplaceMultiplier_fn_eq_reflectedDatum {W₀ : ℝ} {F : ℝ → ℝ}
    (hF : IsCriticalHalfLineGroundState W₀ F) (z : ℂ) :
    (criticalHalfLineGroundStateLaplaceMultiplier hF).fn z =
      laplaceRay (reflectedCriticalHalfLineDatum hF) (diskToRight z) := by
  have hs : ∀ u, 0 ≤ u → cx F u = 0 := by
    intro u hu
    change (F u : ℂ) = 0
    rw [(criticalHalfLineEnergyDomain_of_groundState hF).support u hu, Complex.ofReal_zero]
  change negativeHalfLineLaplace (cx F) (diskToRight z) = _
  rw [negativeHalfLineLaplace_eq_laplaceRay_reflect (cx F) hs]
  unfold laplaceRay
  have hae : (reflectedCriticalHalfLineDatum hF : ℝ → ℂ) =ᵐ[volume.restrict (Ioi 0)]
      (fun u => cx F (-u)) :=
    MemLp.coeFn_toLp (memLp_reflected_negativeProfile
      (criticalHalfLineEnergyDomain_of_groundState hF).memLp_complex)
  apply integral_congr_ae
  filter_upwards [hae] with u hu
  rw [hu]

/-- The reflected critical state generates all positive-half-line L² by causal translations. -/
theorem criticalHalfLineGroundState_causalCyclicSubspace_eq_top
    {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    causalCyclicSubspace (reflectedCriticalHalfLineDatum hF) = ⊤ :=
  causalCyclicSubspace_eq_top_of_outerLaplace (reflectedCriticalHalfLineDatum hF)
    (criticalHalfLineGroundStateLaplaceMultiplier hF)
    (fun z _ => criticalLaplaceMultiplier_fn_eq_reflectedDatum hF z)
    (criticalHalfLineGroundState_laplaceMultiplier_outer hW hthreshold hF)

/-- Failure of RH supplies a critical state cyclic for the actual causal shift semigroup. -/
theorem riemannHypothesis_or_exists_causalCyclic_criticalHalfLineGroundState :
    RiemannHypothesis ∨ ∃ (W₀ : ℝ) (F : ℝ → ℝ)
      (hF : IsCriticalHalfLineGroundState W₀ F), 0 < W₀ ∧
      (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal) ∧
      causalCyclicSubspace (reflectedCriticalHalfLineDatum hF) = ⊤ := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with hRH | ⟨W₀, F, hW, ht, hF⟩
  · exact Or.inl hRH
  · exact Or.inr ⟨W₀, F, hF, hW, ht,
      criticalHalfLineGroundState_causalCyclicSubspace_eq_top hW ht hF⟩

#print axioms riemannHypothesis_or_exists_causalCyclic_criticalHalfLineGroundState

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
