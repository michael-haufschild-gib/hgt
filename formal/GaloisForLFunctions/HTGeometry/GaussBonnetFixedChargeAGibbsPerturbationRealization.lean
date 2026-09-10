import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsPerturbationProbability

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A real finite energy landscape realizing an arbitrary centered probability perturbation. -/
def egbFixedChargeAGibbsPerturbationEnergy (n : ℕ)
    (f : Fin (2 ^ (n + 3)) → ℝ) : Fin (2 ^ (n + 3)) → ℝ :=
  fun i => -Real.log (egbFixedChargeAGibbsPerturbationProbability n f i)

/-- Unit inverse temperature gives partition function exactly one. -/
theorem egbFixedChargeAGibbsPerturbation_partition (n : ℕ)
    (f : Fin (2 ^ (n + 3)) → ℝ) :
    _root_.HTGeometry.finiteGibbsPartition 1 (egbFixedChargeAGibbsPerturbationEnergy n f) = 1 := by
  unfold _root_.HTGeometry.finiteGibbsPartition egbFixedChargeAGibbsPerturbationEnergy
  simp only [neg_mul, one_mul, neg_neg]
  simp_rw [Real.exp_log (egbFixedChargeAGibbsPerturbationProbability_pos n f _)]
  exact egbFixedChargeAGibbsPerturbationProbability_mass n f

/-- The existing finite Gibbs construction realizes the encoded probability exactly. -/
theorem egbFixedChargeAGibbsPerturbation_realization (n : ℕ)
    (f : Fin (2 ^ (n + 3)) → ℝ) :
    _root_.HTGeometry.finiteGibbsStateWeight 1 (egbFixedChargeAGibbsPerturbationEnergy n f) =
      egbFixedChargeAGibbsPerturbationProbability n f := by
  funext i
  rw [_root_.HTGeometry.finiteGibbsStateWeight, egbFixedChargeAGibbsPerturbation_partition, div_one]
  simp only [egbFixedChargeAGibbsPerturbationEnergy, neg_mul, one_mul, neg_neg]
  exact Real.exp_log (egbFixedChargeAGibbsPerturbationProbability_pos n f i)

/-- The initial Gibbs population is exactly the positive perturbation. -/
theorem egbFixedChargeAGibbsPerturbation_initial (n : ℕ)
    (f : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsMarkovPopulation n 0 1 (egbFixedChargeAGibbsPerturbationEnergy n f) =
      egbFixedChargeAGibbsPerturbationProbability n f := by
  rw [egbFixedChargeAGibbsMarkovPopulation_zero, egbFixedChargeAGibbsPerturbation_realization]

end
end GaloisForLFunctions.HTGeometry
