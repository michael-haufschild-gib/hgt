import GaloisForLFunctions.HTGeometry.TorsionPolygonRecurrenceShadowing
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-! # Angular coverage by a packet of identical fields -/
open Real Complex
namespace GaloisForLFunctions.HTGeometry.MaximalError
noncomputable section

/-- When m steps reach each end of the principal angular interval,
one of the m+1 packet phases is within two field steps of any target. -/
theorem packet_phase_mesh (m : ℕ) {h : ℝ} (hh : 0 < h) (hcover : π ≤ h*m)
    (z : ℂ) (hz : ‖z‖=1) :
    ∃ j ≤ m, ‖z-Complex.exp (((-(h*((m:ℝ)-2*j)):ℝ):ℂ)*I)‖ ≤ 2*h := by
  let a := z.arg
  have hlo : 0 ≤ a+h*m := by linarith only [Complex.neg_pi_lt_arg z,hcover]
  have hhi : a+h*m ≤ (m:ℝ)*(2*h) := by linarith only [Complex.arg_le_pi z,hcover]
  let x := (a+h*m)/(2*h)
  have hpos : 0 < 2*h := by positivity
  have hx : 0 ≤ x := div_nonneg hlo hpos.le
  let j := ⌊x⌋₊
  have hjl : (j:ℝ)*(2*h) ≤ a+h*m := (le_div_iff₀ hpos).mp (Nat.floor_le hx)
  have hju : a+h*m < ((j:ℝ)+1)*(2*h) := (div_lt_iff₀ hpos).mp (Nat.lt_floor_add_one x)
  have hdist : |a-(-(h*((m:ℝ)-2*j)))| ≤ 2*h := by
    rw [abs_of_nonneg (by linarith only [hjl])]
    linarith only [hju]
  have hp : Complex.exp ((a:ℂ)*I)=z := by
    simpa only [hz,Complex.ofReal_one,one_mul,a] using Complex.norm_mul_exp_arg_mul_I z
  refine ⟨j,Nat.floor_le_of_le ((div_le_iff₀ hpos).mpr hhi),?_⟩
  exact hp ▸ (norm_exp_ofReal_mul_I_sub_le a (-(h*((m:ℝ)-2*j)))).trans hdist

#print axioms packet_phase_mesh
end
end GaloisForLFunctions.HTGeometry.MaximalError
