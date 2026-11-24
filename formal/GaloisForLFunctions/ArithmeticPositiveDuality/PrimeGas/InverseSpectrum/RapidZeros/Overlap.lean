import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.RapidZeros.ClockReadout
import GaloisForLFunctions.HTGeometry.BoundedDiagonalOperatorLp

/-! # Orthogonality of the two oppositely timed divisor splits -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open scoped ComplexConjugate

/-- Isometric divisor splitting at time t, with the arithmetic multiplicities of each order class. -/
def clockSplit (t : ℝ) : Gas →ₗᵢ[ℂ] PairGas := splitIsometry ⟨criticalTime t,criticalTime_re t⟩

/-- The critical response is exactly the overlap between the oppositely timed two-copy states, divided by the input mass. -/
theorem split_pair_overlap (v : MissingWave) (t : ℝ) :
    inner ℂ (clockSplit (-t) v.val) (clockSplit t v.val) =
      (‖v.val‖^2:ℝ)*compositionResponse v (criticalTime t) := by
  let w : Gas := HTGeometry.LpDiagonal.lpDiag (splitPhase t) 1 zero_le_one (fun n => (splitPhase_norm t n).le) v.val
  have hw (n : ℕ+) : w n = splitPhase t n*v.val n := rfl
  have ht : criticalTime (-t)+(2*criticalTime t-1) = criticalTime t := by
    unfold criticalTime
    push_cast
    ring
  have hsplit : clockSplit t v.val = clockSplit (-t) w := by
    apply lp.ext
    funext x
    change channel (criticalTime t) (x.1*x.2) x.1*v.val (x.1*x.2) =
      channel (criticalTime (-t)) (x.1*x.2) x.1*w (x.1*x.2)
    have hheat : heat (criticalTime (-t)) (x.1*x.2)*splitPhase t (x.1*x.2) = heat (criticalTime t) (x.1*x.2) := by
      rw [splitPhase,← heat_add,ht]
    rw [hw,channel,channel,← hheat]
    ring
  rw [hsplit,LinearIsometry.inner_map_map,lp.inner_eq_tsum,compositionResponse,← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [RCLike.inner_apply,hw]
  change splitPhase t n*v.val n*conj (v.val n) = ((‖v.val‖^2:ℝ):ℂ)*((occupationProbability v n:ℂ)*splitPhase t n)
  have hM : ‖v.val‖^2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr (missingWave_ne_zero v))
  have hmass : ((‖v.val‖^2:ℝ):ℂ)*(occupationProbability v n:ℂ) = ((‖v.val n‖^2:ℝ):ℂ) := by
    rw [← Complex.ofReal_mul,occupationProbability,mul_comm (‖v.val‖^2),div_mul_cancel₀ _ hM]
  rw [← mul_assoc,hmass,mul_assoc,Complex.mul_conj,Complex.sq_norm,mul_comm]

theorem split_pair_orthogonal_iff (v : MissingWave) (t : ℝ) :
    inner ℂ (clockSplit (-t) v.val) (clockSplit t v.val) = 0 ↔ compositionResponse v (criticalTime t) = 0 := by
  rw [split_pair_overlap,mul_eq_zero]
  exact or_iff_right (Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 (norm_ne_zero_iff.mpr (missingWave_ne_zero v))))

#print axioms split_pair_overlap
#print axioms split_pair_orthogonal_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
