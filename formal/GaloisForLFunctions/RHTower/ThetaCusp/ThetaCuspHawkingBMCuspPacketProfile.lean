import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMCuspWindowMoments
import Mathlib.Analysis.Complex.RealDeriv

/-!
Actual expanding wave packets in the original modular operator domain.
-/

open MeasureTheory Set Filter Topology
open scoped ContDiff ComplexConjugate
namespace RHTower.D4BMModularCore
noncomputable section

def cuspPacketCenter (L : ℝ) : ℝ := Real.log 2+2*L+1
def cuspPacketCoordinate (L t : ℝ) : ℝ := (t-cuspPacketCenter L)/L
def cuspPacketPhase (tau t : ℝ) : ℂ := Complex.exp ((tau:ℂ)*Complex.I*(t:ℂ))

/-- The expanding oscillatory packet in the original logarithmic cusp coordinate. -/
def cuspPacketField (tau L t : ℝ) : ℂ :=
  cuspPacketPhase tau t*(cuspWindow (cuspPacketCoordinate L t):ℂ)

theorem cuspPacketPhase_smooth (tau : ℝ) : ContDiff ℝ ∞ (cuspPacketPhase tau) := by
  exact Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff)

theorem cuspPacketPhase_norm (tau t : ℝ) : ‖cuspPacketPhase tau t‖ = 1 := by
  simp [cuspPacketPhase,Complex.norm_exp]

theorem cuspPacketField_smooth (tau L : ℝ) : ContDiff ℝ ∞ (cuspPacketField tau L) :=
  (cuspPacketPhase_smooth tau).mul (Complex.ofRealCLM.contDiff.comp
    (cuspWindow_smooth.comp ((contDiff_id.sub contDiff_const).div_const L)))

theorem cuspPacketField_support (tau : ℝ) {L : ℝ} (hL : 0 < L) :
    tsupport (cuspPacketField tau L) ⊆ Icc (cuspPacketCenter L-L) (cuspPacketCenter L+L) := by
  apply closure_minimal _ isClosed_Icc
  intro t ht
  have hw : cuspWindow (cuspPacketCoordinate L t) ≠ 0 := by
    intro hz
    exact ht (by simp [cuspPacketField,hz])
  have hc := cuspWindow_support (subset_tsupport _ hw)
  change -1 ≤ (t-cuspPacketCenter L)/L ∧ (t-cuspPacketCenter L)/L ≤ 1 at hc
  have hl := (le_div_iff₀ hL).mp hc.1
  have hr := (div_le_iff₀ hL).mp hc.2
  constructor <;> linarith

/-- The full packet is admitted to the actual modular operator via its constructed log-height test. -/
def cuspPacketTest (tau : ℝ) (L : ℝ) (hL : 0 < L) : CuspLogTest where
  field := cuspPacketField tau L
  smooth := cuspPacketField_smooth tau L
  compact := isCompact_Icc.of_isClosed_subset isClosed_closure (cuspPacketField_support tau hL)
  support := by
    intro t ht
    have hs := (cuspPacketField_support tau hL ht).1
    change Real.log 2 < t
    dsimp [cuspPacketCenter] at hs
    linarith

/-- The carrier's modulus is exactly the real compact window, since its phase has unit norm. -/
theorem cuspPacketField_norm_sq (tau L t : ℝ) :
    ‖cuspPacketField tau L t‖^(2 : ℕ) = cuspWindow (cuspPacketCoordinate L t)^(2 : ℕ) := by
  rw [cuspPacketField,norm_mul,cuspPacketPhase_norm,one_mul,Complex.norm_real,
    Real.norm_eq_abs,sq_abs]

end
end RHTower.D4BMModularCore
