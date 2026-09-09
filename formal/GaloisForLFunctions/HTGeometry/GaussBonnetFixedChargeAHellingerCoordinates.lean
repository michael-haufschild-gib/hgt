import GaloisForLFunctions.HTGeometry.FixedSourceFormationCapital

/-!
Coordinate calculus for the corpus Hellinger distance, needed by the information
application of the critical Gibbs Markov chain derived from arXiv:2609.00025.
These coordinate identities hold even for arbitrary real input arrays.
-/
namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Hellinger square is the exact sum of squared square-root coordinate differences. -/
theorem egbFixedChargeAHellinger_coordinate_square
    (n : ℕ) (u v : Fin n → ℝ) :
    finitePacketHellinger u v ^ 2 =
      ∑ i : Fin n, (Real.sqrt (u i) - Real.sqrt (v i)) ^ 2 := by
  rw [finitePacketHellinger, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  apply Finset.sum_congr rfl
  intro i _
  change ‖Real.sqrt (u i) - Real.sqrt (v i)‖ ^ 2 = _
  rw [Real.norm_eq_abs, sq_abs]

/-- The coordinate formula also recovers the unsquared Hellinger distance. -/
theorem egbFixedChargeAHellinger_coordinate_formula
    (n : ℕ) (u v : Fin n → ℝ) :
    finitePacketHellinger u v =
      Real.sqrt (∑ i : Fin n, (Real.sqrt (u i) - Real.sqrt (v i)) ^ 2) := by
  rw [← egbFixedChargeAHellinger_coordinate_square,
    Real.sqrt_sq (finitePacketHellinger_nonneg u v)]

/-- Hellinger distance is jointly continuous on the entire space of finite real arrays. -/
theorem egbFixedChargeAHellinger_continuous (n : ℕ) :
    Continuous (fun p : (Fin n → ℝ) × (Fin n → ℝ) => finitePacketHellinger p.1 p.2) := by
  simp_rw [egbFixedChargeAHellinger_coordinate_formula]
  fun_prop

end

end GaloisForLFunctions.HTGeometry
