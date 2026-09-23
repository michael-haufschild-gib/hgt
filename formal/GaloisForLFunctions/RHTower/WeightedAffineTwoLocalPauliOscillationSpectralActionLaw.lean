import GaloisForLFunctions.RHTower.AffineTwoLocalPauliOscillationSpectralActionLaw

open scoped BigOperators Matrix ComplexConjugate Matrix.Norms.L2Operator
open Matrix Set MeasureTheory ProbabilityTheory

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Arbitrary pre-draw probability designs retain the dimension-linear
two-local trace-deficit exponent with the oscillation-adaptive remainder. -/
theorem stdGaussian_measure_weightedScaledAffineTwoLocalOscillationNearAction_gap_le_traceDeficit
    {n : ℕ}
    {H₀ : Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ} (hH₀ : H₀.IsHermitian)
    {scale : ℝ} (hscale : scale ≠ 0)
    {C : Type*} [Fintype C]
    (U : C → Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ)
    (w : C → ℝ) (hw : w ∈ stdSimplex ℝ C)
    (r : ℕ) (δ : ℝ) {κ : ℝ} (hκ : 0 < κ) :
    (stdGaussian (TwoLocalPauliCoefficientSpace n)).real
        {x |
          (∑ c, w c * staticChoiOscillationAdaptiveReplicaBase
            ((twoLocalPauliGaussianHermitianPencil n).scaledAffineSpectralEnergy
              hH₀ scale x)
            ((Fintype.card (FiniteQubitConfiguration (Fin n)) : ℝ)⁻¹ *
              (scale ^ (2 : ℕ) *
                (twoLocalPauliGaussianHermitianPencil n).commutatorActivation
                  (U c))) ^ r) + κ ≤
          ∑ c, w c * directStaticChoiTargetNearActionMass
            (GaloisForLFunctions.RHTower.choiVector
              ((twoLocalPauliGaussianHermitianPencil n).scaledAffineSpectralEndpoint
                  hH₀ scale x (U c) :
                Matrix (Fin (Fintype.card (FiniteQubitConfiguration (Fin n))))
                  (Fin (Fintype.card (FiniteQubitConfiguration (Fin n)))) ℂ))
            ((twoLocalPauliGaussianHermitianPencil n).scaledAffineSpectralEnergy
              hH₀ scale x) r δ} ≤
      (∑ c, w c * Real.exp
        (-(gaussianIntervalActivationMass ^ (2 : ℕ) / 2) *
          (((6 * n - 4 : ℕ) : ℝ) * unitaryProjectiveTraceDeficit (U c)))) / κ := by
  have hbase :=
    FiniteGaussianHermitianPencil.stdGaussian_measure_weightedScaledAffineOscillationNearAction_gap_le
      (twoLocalPauliGaussianHermitianPencil n) hH₀ hscale U w hw r δ hκ
  apply hbase.trans
  apply div_le_div_of_nonneg_right _ hκ.le
  apply Finset.sum_le_sum
  intro c _
  apply mul_le_mul_of_nonneg_left _ (hw.1 c)
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonpos_left
    (twoLocalPauliGaussianHermitianPencil_stableRatio_ge_projectiveTraceDeficit
      (U c))
  exact neg_nonpos.mpr (by positivity)

end

end RHTower
