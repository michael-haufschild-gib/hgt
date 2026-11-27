import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.WeakBondDeficit.PrecisionProfile.PowerCut
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.WeakBondDeficit.Frames.MissingMass

/-! # A linear error floor from the Pauli mass across a disconnected circuit -/

open Finset Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit
noncomputable section
variable {n : ℕ}

/-- Let V be a lower bound for the coefficient mass in a chosen frame.
Once V dominates the total Euclidean coefficient norm, every sufficiently
short time already has projective fitting error at least |t| V/(8π).
Repeating the same circuit until the cut sees a half-turn gives the bound. -/
theorem cut_speed (u : PathShell n) (C : TwoQubitCircuit (n+2)) (c : Cut C)
    (b : Fin (n+1)→Fin 3×Fin 3) (V : ℝ) (hV : 0<V)
    (hmass : V≤∑ e∈crossed c, |u (.inr (e,b e))|)
    (hbulk : 200*π*‖u‖≤V) (t : ℝ) (ht : |t| * V≤π) (z : ℂ) (hz : ‖z‖=1) :
    |t| * V/(8*π)≤‖unitaryEvolution (pathHamiltonian u) t-z • C.eval.val‖ := by
  by_cases ht₀ : t=0
  · rw [ht₀,abs_zero,zero_mul,zero_div]
    exact norm_nonneg _
  let v := |t| * V
  have hv : 0<v := mul_pos (abs_pos.mpr ht₀) hV
  let r := ⌈π/v⌉₊
  have hl : π≤(r:ℝ)*v := (div_le_iff₀ hv).mp (Nat.le_ceil _)
  have hu : (r:ℝ)*v≤2*π := by
    have he := mul_le_mul_of_nonneg_right (Nat.ceil_lt_add_one (div_nonneg pi_pos.le hv.le)).le hv.le
    rw [add_mul,div_mul_cancel₀ _ hv.ne',one_mul] at he
    change v≤π at ht
    linarith only [he,ht]
  have hshort : (r:ℝ)*|t| * ‖u‖≤1/100 := by
    apply le_of_mul_le_mul_right _ hV
    have h := mul_le_mul_of_nonneg_right hu (norm_nonneg u)
    dsimp only [v] at h
    linarith only [h,hbulk]
  let E := ‖unitaryEvolution (pathHamiltonian u) t-z • C.eval.val‖
  have hfit : 1/4<(r:ℝ)*E := by
    by_contra! hbad
    have he := power_cut_mass u C c b t z hz r hbad hshort
    have hh := mul_le_mul_of_nonneg_left hmass (show 0≤(r:ℝ)*4*|t| by positivity)
    dsimp only [v] at hl
    linarith only [he,hh,hl,pi_pos]
  apply (div_le_iff₀ (by positivity : 0<8*π)).mpr
  change v≤E*(8*π)
  have h₁ := mul_le_mul_of_nonneg_right hfit.le hv.le
  have h₂ := mul_le_mul_of_nonneg_right hu (show 0≤E from norm_nonneg _)
  linarith only [h₁,h₂]

#print axioms cut_speed
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit
