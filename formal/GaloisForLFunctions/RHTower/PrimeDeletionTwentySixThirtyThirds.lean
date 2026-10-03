import GaloisForLFunctions.RHTower.PrimeDeletionThreeQuarters
import GaloisForLFunctions.RHTower.PrimeShortIntervalsTwentyThirtyThirds

/-!
# Concrete half-dimension uncertainty for every `κ < 26/33`

The greedy prime deletion needs every-window prime mass at one exponent `α` with
`1 - κ ≤ α < 1 - κ/2`.  The every-window law now holds for every `α > 20/33`
(`exists_theta_window_lower_twenty_thirtyThirds`), and `α = 53/66 - κ/4` lies in
`(20/33, 1 - κ/2)` exactly when `κ < 26/33`.  For each `κ ∈ (1/2, 26/33)` this gives a set of primes
whose `Q`-free integers admit no power saving below `x^{κ/2}`.
-/

open Filter Topology Asymptotics

namespace RHTower

noncomputable section

namespace PrimeDeletion

/-- **A concrete half-dimension uncertainty for every `κ ∈ (1/2, 26/33)`.** -/
theorem exists_prime_deletion_half_dimension_uncertainty_twentySix_thirtyThirds {κ : ℝ}
    (hκ : 1 / 2 < κ) (hκ' : κ < 26 / 33) :
    ∃ Q : Set ℕ, (∀ q ∈ Q, q.Prime) ∧
      (∃ η < κ / 2, (fun x : ℝ => deletedChebyshev Q x - (1 / κ) * (x ^ κ + x ^ (κ / 2)))
        =O[atTop] fun x => x ^ η) ∧
      ∀ a θ : ℝ, 0 ≤ θ → θ < κ / 2 →
        ¬(fun x : ℝ => qFreeCount Q x - a * x) =O[atTop] fun x => x ^ θ := by
  set α : ℝ := 53 / 66 - κ / 4 with hαdef
  have hα : (20 / 33 : ℝ) < α := by rw [hαdef]; linarith
  have hα1 : α < 1 := by rw [hαdef]; linarith
  have hακ : κ - 1 + α < κ / 2 := by rw [hαdef]; linarith
  have he : 0 ≤ κ - 1 + α := by rw [hαdef]; linarith
  have hκ0 : 0 < κ := by linarith
  have hκ1 : κ < 1 := by linarith
  obtain ⟨X, hX1, hwin⟩ := exists_theta_window_lower_twenty_thirtyThirds hα hα1
  obtain ⟨η, hη, hO⟩ := greedy_chebyshev_expansion hκ0 hκ1 hα1 he hακ (by norm_num : (0 : ℝ) < 2)
    (by linarith : (0 : ℝ) ≤ X) hwin
  refine ⟨greedyDeletion κ, fun q hq => hq.1, ⟨η, hη, hO⟩, ?_⟩
  intro a θ hθ hθκ
  refine not_isBigO_qFreeCount_of_odd (greedyDeletion κ) (l := 1) odd_one hθ hθκ hη hκ0 hκ1 ?_
  simpa using hO

end PrimeDeletion

end

end RHTower
