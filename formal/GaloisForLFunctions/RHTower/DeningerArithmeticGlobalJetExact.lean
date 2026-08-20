import GaloisForLFunctions.RHTower.DeningerArithmeticGlobalJetInterpolation

/-!
# Global-to-local exactness for Xi jets

The all-jets map records the local multiplicity-bounded Xi jets of a compact-open entire source.
The results assembled here give a Hasse-shaped local--global statement: a source has vanishing
local obstruction exactly when it is globally divisible by Xi, and every local jet family is
globally realized.  This is an analytic local--global principle, not a claim of the classical
arithmetic Hasse principle.
-/

namespace RHTower

noncomputable section

/-- The Xi multiplication map is exact with the all-local-jets observation: all local Xi jets of
a source vanish exactly when the source is globally Xi-divisible. -/
theorem deningerCompactOpenXi_allJets_exact :
    Function.Exact deningerCompactOpenXiMul deningerCompactOpenAllJets := by
  intro F
  change deningerCompactOpenAllJets F = 0 ↔ F ∈ deningerCompactOpenXiRange
  rw [deningerCompactOpenXiRange_eq_allJets_ker]
  rfl

/-- The global compact-open cohomology is completely and uniquely described by the full family of
local Xi jets. -/
theorem deningerCompactOpenH1AllJets_bijective :
    Function.Bijective deningerCompactOpenH1AllJets :=
  ⟨deningerCompactOpenH1AllJets_injective, deningerCompactOpenH1AllJets_surjective⟩

/-- Global compact-open Xi cohomology is linearly equivalent to all local multiplicity-bounded
Xi jet data. -/
noncomputable def deningerCompactOpenH1AllJetsEquiv :
    DeningerArithmeticCompactOpenH1 ≃ₗ[ℂ] DeningerArithmeticJetProduct :=
  LinearEquiv.ofBijective deningerCompactOpenH1AllJets.toLinearMap
    deningerCompactOpenH1AllJets_bijective

/-- The global-to-local equivalence is induced by the original all-jets observation. -/
theorem deningerCompactOpenH1AllJetsEquiv_apply (x : DeningerArithmeticCompactOpenH1) :
    deningerCompactOpenH1AllJetsEquiv x = deningerCompactOpenH1AllJets x := rfl

end

end RHTower
