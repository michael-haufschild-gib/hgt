import GaloisForLFunctions.FiniteFreeProbability.EulerRootFilters
import GaloisForLFunctions.FiniteFreeProbability.FactorialConnection

/-!
# Generalized Stirling normal ordering on Jensen polynomials

An arithmetic progression of Euler weights acts diagonally by a stepped
factorial in the monomial degree. Changing the step of that progression
expresses the entire operator as a signed sum of shorter Euler words.
Although the coefficients can have both signs, the resulting combination
retains the root localization of a single word.
-/

open Polynomial Finset
open GaloisForLFunctions.HTGeometry

namespace FiniteFreeProbability

noncomputable section

/-- Successive integer weights in an arithmetic progression with first weight `base+1`. -/
def progressionWord (base step : ℕ) : ℕ → List ℕ
  | 0 => []
  | n+1 => (base + step*n) :: progressionWord base step n

private theorem progression_coeff (base step n : ℕ) (p : ℂ[X]) (j : ℕ) :
    (eulerWord (progressionWord base step n) p).coeff j =
      (fallPoly (-(step : ℂ)) n).eval ((base : ℂ)+1+j) * p.coeff j := by
  induction n generalizing p with
  | zero => simp [progressionWord, eulerWord]
  | succ n ih =>
    rw [progressionWord, eulerWord, ih, eulerFilter_coeff, fallPoly_succ, eval_mul, eval_sub,
      eval_X, eval_C]
    push_cast
    ring

/-- Normal ordering between any two integral progressions, as an identity of operators
on arbitrary complex polynomials. -/
theorem progressionWord_normal_order (base s t n : ℕ) (p : ℂ[X]) :
    eulerWord (progressionWord base s n) p =
      ∑ k ∈ range (n+1), C (factorialConnection (-(s : ℂ)) (-(t : ℂ)) n k) *
        eulerWord (progressionWord base t k) p := by
  ext j
  simp only [finsetSum_coeff, coeff_C_mul, progression_coeff]
  have h := congrArg (Polynomial.eval ((base : ℂ)+1+j))
    (fallPoly_change_step (-(s : ℂ)) (-(t : ℂ)) n)
  simp only [eval_finsetSum, eval_mul, eval_C] at h
  rw [h, Finset.sum_mul]
  exact sum_congr rfl fun _ _ => by ring

/-- Signed Stirling superpositions of a full row retain the anchored root hull. -/
theorem normal_ordered_root_hull (base s t n : ℕ) (p : ℂ[X]) :
    (∑ k ∈ range (n+1), C (factorialConnection (-(s : ℂ)) (-(t : ℂ)) n k) *
        eulerWord (progressionWord base t k) p).rootSet ℂ ⊆ convexHull ℝ (insert 0 (p.rootSet ℂ)) := by
  rw [← progressionWord_normal_order]
  exact eulerWord_root_hull _ _

private theorem map_eulerWord (w : List ℕ) (p : ℝ[X]) :
    (eulerWord w p).map Complex.ofRealHom = eulerWord w (p.map Complex.ofRealHom) := by
  ext j
  simp only [coeff_map, eulerWord_coeff, map_mul, map_list_prod, List.map_map]
  simp [Function.comp_def]

/-- Signed normal ordering commutes with complexification of a real input. -/
theorem normal_ordered_eq_real_map (base s t n : ℕ) (p : ℝ[X]) :
    ∑ k ∈ range (n+1), C (factorialConnection (-(s : ℂ)) (-(t : ℂ)) n k) *
      eulerWord (progressionWord base t k) (p.map Complex.ofRealHom) =
        (eulerWord (progressionWord base s n) p).map Complex.ofRealHom := by
  rw [← progressionWord_normal_order, map_eulerWord]

#print axioms normal_ordered_root_hull
#print axioms normal_ordered_eq_real_map

end

end FiniteFreeProbability
