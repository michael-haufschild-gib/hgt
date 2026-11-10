import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.MinimalStructure
import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.CarryWeightComparison

/-!
# Unique optimality of greedy carry-free compositions

For every base at least two and every positive residue degree, the greedy
composition uniquely maximizes the weighted sum of numerical part values.
A putative different optimum reduces to a normalized singleton last part;
the interval carry modification strictly increases its weight.
-/

open Finset
namespace GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition
variable {p s m : ℕ} [NeZero s] {S : Finset (Digit p)}

/-- Every optimum has the same numerical part values as every greedy composition. -/
theorem optimal_values_eq_greedy {O G : DigitComposition p s m S}
    (hp : 2 ≤ p) (hO : O.IsOptimal) (hG : G.IsGreedy) : O.value = G.value := by
  by_contra hne
  obtain ⟨k, T, C, D, x, y, _, hs, hC, _, _, hnorm, hlast, hy, hxy, _, hweight, hbelow⟩ :=
    exists_singleton_normalized_counterexample hp ⟨m, S, O, G, hO, hG, hne⟩
  obtain ⟨Z, hZ⟩ := C.exists_strict_weight_improvement D hp hs (hC.tauMonotone hp)
    hlast hnorm hy hxy hweight hbelow
  exact (not_lt_of_ge (hC Z)) hZ

/-- Greediness and weight optimality coincide for every positive residue degree. -/
theorem isOptimal_iff_isGreedy (C : DigitComposition p s m S) (hp : 2 ≤ p) :
    C.IsOptimal ↔ C.IsGreedy := by
  constructor
  · intro hC
    obtain ⟨G, hG⟩ := exists_greedy ⟨C⟩
    exact (isGreedy_congr_values (optimal_values_eq_greedy hp hC hG)).mpr hG
  · intro hC
    obtain ⟨O, hO⟩ := exists_optimal ⟨C⟩
    exact (isOptimal_congr_values (optimal_values_eq_greedy hp hO hC)).mp hO

/-- The maximizing numerical composition is unique. Equal digit labels may vary. -/
theorem IsOptimal.values_eq {C D : DigitComposition p s m S}
    (hp : 2 ≤ p) (hC : C.IsOptimal) (hD : D.IsOptimal) : C.value = D.value :=
  optimal_values_eq_greedy hp hC ((isOptimal_iff_isGreedy D hp).mp hD)

/-- Every greedy composition is a weight maximum. -/
theorem IsGreedy.isOptimal {C : DigitComposition p s m S}
    (hp : 2 ≤ p) (hC : C.IsGreedy) : C.IsOptimal :=
  (isOptimal_iff_isGreedy C hp).mpr hC

end GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition

#print axioms GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition.isOptimal_iff_isGreedy
#print axioms GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition.IsOptimal.values_eq
