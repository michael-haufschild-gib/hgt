import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.EmissionRate.Limit
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.UniversalResponse.Vacuum

/-! # Initial energy measurement for all multiplicative conserving responses -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.EmissionRate

open ModeCapacities UniversalResponse Filter Topology
open scoped ENNReal

/-- Short-time loss is insensitive even to discontinuous multiplicative phases. -/
theorem vacuum_norm_sq (A : Response) (s : Conserving) (f : Gas) (t : Duration) :
    ‖vacuum A t f‖ ^ 2 = ‖noEmission s t f‖ ^ 2 := by
  apply (mass_sum (vacuum A t f)).unique
  refine (mass_sum (noEmission s t f)).congr_fun fun n => ?_
  rw [vacuum_mass, coordinate_mass]

def responseLoss (A : Response) (f : Gas) (t : Duration) : ℝ :=
  (‖f‖ ^ 2 - ‖vacuum A t f‖ ^ 2) / t.val

theorem response_initial_rate (A : Response) (f : Gas) :
    Tendsto (fun t : ℝ => if ht : 0 < t then ENNReal.ofReal (responseLoss A f ⟨t,ht⟩) else 0)
      (𝓝[>] 0) (𝓝 (form f)) := by
  let s : Conserving := ⟨1/2,by norm_num⟩
  have eqn (t : Duration) : responseLoss A f t = loss s f t := by
    rw [responseLoss, loss, vacuum_norm_sq A s]
  apply (initial_rate s f).congr'
  filter_upwards [(self_mem_nhdsWithin : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t)] with t ht
  change 0 < t at ht
  simp only [reading, dif_pos ht, eqn]

#print axioms vacuum_norm_sq
#print axioms response_initial_rate

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.EmissionRate
