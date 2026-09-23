import GaloisForLFunctions.RHTower.GaussianAffineHermitianPencilSpectralActionLaw

/-!
# Scale-covariant affine Gaussian spectral action law

An arbitrarily weak nonzero Gaussian perturbation retains the full
observer-Jacobian stable-rank exponent.  Its activation rescales quadratically
while deterministic drift is divided by the perturbation scale inside the
affine tube.
-/

open scoped BigOperators Matrix ComplexConjugate Matrix.Norms.L2Operator
open Matrix Set MeasureTheory ProbabilityTheory

namespace RHTower

open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower

noncomputable section

attribute [local instance] Classical.propDecidable

variable {E ι : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Drift centre after dividing out a nonzero fluctuation scale. -/
def scaledHermitianPencilCommutatorDrift
    (scale : ℝ) (H₀ : Matrix ι ι ℂ)
    (U : Matrix.unitaryGroup ι ℂ) : EuclideanSpace ℂ (ι × ι) :=
  scale⁻¹ • hermitianPencilCommutatorDrift H₀ U

omit [FiniteDimensional ℝ E] in
/-- Exact norm scaling after affine drift normalization. -/
theorem FiniteGaussianHermitianPencil.scaledAffineCommutatorEnergy
    (P : FiniteGaussianHermitianPencil E ι)
    {scale : ℝ} (hscale : scale ≠ 0)
    (H₀ : Matrix ι ι ℂ) (x : E)
    (U : Matrix.unitaryGroup ι ℂ) :
    ‖P.commutatorMap U (scale • x) - hermitianPencilCommutatorDrift H₀ U‖ ^ (2 : ℕ) =
      scale ^ (2 : ℕ) *
        ‖P.commutatorMap U x - scaledHermitianPencilCommutatorDrift scale H₀ U‖ ^ (2 : ℕ) := by
  rw [LinearMap.map_smul]
  have hvec :
      scale • P.commutatorMap U x - hermitianPencilCommutatorDrift H₀ U =
        scale • (P.commutatorMap U x -
          scaledHermitianPencilCommutatorDrift scale H₀ U) := by
    unfold scaledHermitianPencilCommutatorDrift
    rw [smul_sub, smul_smul, mul_inv_cancel₀ hscale, one_smul]
  rw [hvec, norm_smul, Real.norm_eq_abs, mul_pow]
  congr 1
  exact sq_abs scale

/-- Spectral energy of a deterministic seed plus a scale-times Gaussian draw. -/
abbrev FiniteGaussianHermitianPencil.scaledAffineSpectralEnergy
    (P : FiniteGaussianHermitianPencil E ι)
    {H₀ : Matrix ι ι ℂ} (hH₀ : H₀.IsHermitian)
    (scale : ℝ) (x : E) :=
  P.affineSpectralEnergy hH₀ (scale • x)

/-- Physical endpoint in the eigenbasis of the same scaled affine draw. -/
abbrev FiniteGaussianHermitianPencil.scaledAffineSpectralEndpoint
    (P : FiniteGaussianHermitianPencil E ι)
    {H₀ : Matrix ι ι ℂ} (hH₀ : H₀.IsHermitian)
    (scale : ℝ) (x : E) (U : Matrix.unitaryGroup ι ℂ) :=
  P.affineSpectralEndpoint hH₀ (scale • x) U

/-- **Scale-covariant affine action--carrier law.**  Weakening perturbation
changes activation by `scale²` but does not change observer stable rank. -/
theorem FiniteGaussianHermitianPencil.scaledAffineNearAction_le_adaptive_add_carrier
    [Nonempty ι]
    (P : FiniteGaussianHermitianPencil E ι)
    {H₀ : Matrix ι ι ℂ} (hH₀ : H₀.IsHermitian)
    {scale : ℝ} (hscale : scale ≠ 0) (x : E)
    (U : Matrix.unitaryGroup ι ℂ) (r : ℕ) (δ : ℝ) :
    directStaticChoiTargetNearActionMass
        (choiVector
          (P.scaledAffineSpectralEndpoint hH₀ scale x U :
            Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ))
        (P.scaledAffineSpectralEnergy hH₀ scale x) r δ ≤
      staticChoiAdaptiveReplicaBase (P.scaledAffineSpectralEnergy hH₀ scale x)
          ((Fintype.card ι : ℝ)⁻¹ *
            (scale ^ (2 : ℕ) * P.commutatorActivation U)) ^ r +
        if x ∈ gaussianAffineHalfActivationTube
            (n := Module.finrank ℝ E) (P.commutatorMap U)
              (scaledHermitianPencilCommutatorDrift scale H₀ U)
          then 1 else 0 := by
  have h :=
    directStaticChoiTargetNearActionMass_hermitianSpectralEndpoint_le_adaptivePhysicalAction
      (d := Fintype.card ι) Fintype.card_pos
      (P.affineReindexedHamiltonian_isHermitian hH₀ (scale • x))
      (finiteGaussianHermitianPencilReindexedEndpoint U) r δ
      (scale ^ (2 : ℕ) * P.commutatorActivation U)
  rw [P.affineReindexedCommutatorEnergy H₀ (scale • x) U,
    P.scaledAffineCommutatorEnergy hscale H₀ x U] at h
  have hscaleSq : 0 < scale ^ (2 : ℕ) := sq_pos_of_ne_zero hscale
  by_cases hc : ‖P.commutatorMap U x -
      scaledHermitianPencilCommutatorDrift scale H₀ U‖ ^ (2 : ℕ) ≤
      P.commutatorActivation U
  · have hcScaled :
        scale ^ (2 : ℕ) * ‖P.commutatorMap U x -
            scaledHermitianPencilCommutatorDrift scale H₀ U‖ ^ (2 : ℕ) ≤
          scale ^ (2 : ℕ) * P.commutatorActivation U :=
      mul_le_mul_of_nonneg_left hc hscaleSq.le
    rw [if_pos hcScaled] at h
    rw [if_pos]
    · exact h
    · exact hc
  · have hcScaled : ¬
        scale ^ (2 : ℕ) * ‖P.commutatorMap U x -
            scaledHermitianPencilCommutatorDrift scale H₀ U‖ ^ (2 : ℕ) ≤
          scale ^ (2 : ℕ) * P.commutatorActivation U := by
      exact fun hs => hc (le_of_mul_le_mul_left hs hscaleSq)
    rw [if_neg hcScaled] at h
    rw [if_neg]
    · exact h
    · exact hc

/-- Pointwise probability-design scaled affine carrier. -/
theorem FiniteGaussianHermitianPencil.weightedScaledAffineNearAction_le_transverse_add_tubeMass
    [Nonempty ι]
    (P : FiniteGaussianHermitianPencil E ι)
    {H₀ : Matrix ι ι ℂ} (hH₀ : H₀.IsHermitian)
    {scale : ℝ} (hscale : scale ≠ 0)
    {C : Type*} [Fintype C]
    (U : C → Matrix.unitaryGroup ι ℂ)
    (w : C → ℝ) (hw : w ∈ stdSimplex ℝ C)
    (x : E) (r : ℕ) (δ : ℝ) :
    (∑ c, w c * directStaticChoiTargetNearActionMass
        (choiVector
          (P.scaledAffineSpectralEndpoint hH₀ scale x (U c) :
            Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ))
        (P.scaledAffineSpectralEnergy hH₀ scale x) r δ) ≤
      (∑ c, w c * staticChoiAdaptiveReplicaBase
        (P.scaledAffineSpectralEnergy hH₀ scale x)
        ((Fintype.card ι : ℝ)⁻¹ *
          (scale ^ (2 : ℕ) * P.commutatorActivation (U c))) ^ r) +
      gaussianWeightedAffineHalfActivationTubeMass
        (n := Module.finrank ℝ E) (fun c => P.commutatorMap (U c))
          (fun c => scaledHermitianPencilCommutatorDrift scale H₀ (U c)) w x := by
  calc
    _ ≤ ∑ c, w c *
        (staticChoiAdaptiveReplicaBase
            (P.scaledAffineSpectralEnergy hH₀ scale x)
            ((Fintype.card ι : ℝ)⁻¹ *
              (scale ^ (2 : ℕ) * P.commutatorActivation (U c))) ^ r +
          if x ∈ gaussianAffineHalfActivationTube
              (n := Module.finrank ℝ E) (P.commutatorMap (U c))
                (scaledHermitianPencilCommutatorDrift scale H₀ (U c))
            then 1 else 0) := by
      apply Finset.sum_le_sum
      intro c _
      exact mul_le_mul_of_nonneg_left
        (P.scaledAffineNearAction_le_adaptive_add_carrier
          hH₀ hscale x (U c) r δ) (hw.1 c)
    _ = _ := by
      unfold gaussianWeightedAffineHalfActivationTubeMass
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
      congr 1

/-- **Scale-free quenched exponent.**  Every nonzero perturbation scale,
however weak, obeys the same exact stable-rank probability bound. -/
theorem FiniteGaussianHermitianPencil.stdGaussian_measure_weightedScaledAffineNearAction_gap_le
    [Nonempty ι] [MeasurableSpace E] [BorelSpace E]
    (P : FiniteGaussianHermitianPencil E ι)
    {H₀ : Matrix ι ι ℂ} (hH₀ : H₀.IsHermitian)
    {scale : ℝ} (hscale : scale ≠ 0)
    {C : Type*} [Fintype C]
    (U : C → Matrix.unitaryGroup ι ℂ)
    (w : C → ℝ) (hw : w ∈ stdSimplex ℝ C)
    (r : ℕ) (δ : ℝ) {κ : ℝ} (hκ : 0 < κ) :
    (stdGaussian E).real
        {x |
          (∑ c, w c * staticChoiAdaptiveReplicaBase
            (P.scaledAffineSpectralEnergy hH₀ scale x)
            ((Fintype.card ι : ℝ)⁻¹ *
              (scale ^ (2 : ℕ) * P.commutatorActivation (U c))) ^ r) + κ ≤
          ∑ c, w c * directStaticChoiTargetNearActionMass
            (choiVector
              (P.scaledAffineSpectralEndpoint hH₀ scale x (U c) :
                Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ))
            (P.scaledAffineSpectralEnergy hH₀ scale x) r δ} ≤
      (∑ c, w c * Real.exp
        (-(gaussianIntervalActivationMass ^ (2 : ℕ) / 2) *
          (((∑ i : Fin (Module.finrank ℝ E),
              (P.commutatorMap (U c)).singularValues i ^ (2 : ℕ)) ^ (2 : ℕ)) /
            ∑ i : Fin (Module.finrank ℝ E),
              (P.commutatorMap (U c)).singularValues i ^ (4 : ℕ)))) / κ := by
  apply (measureReal_mono ?_).trans
    (stdGaussian_measure_weightedAffineHalfActivationTubeMass_ge_le
      (n := Module.finrank ℝ E) (fun c => P.commutatorMap (U c))
      (fun c => scaledHermitianPencilCommutatorDrift scale H₀ (U c))
      (by rfl) w hw hκ)
  intro x hx
  have hdet := P.weightedScaledAffineNearAction_le_transverse_add_tubeMass
    hH₀ hscale U w hw x r δ
  change κ ≤ gaussianWeightedAffineHalfActivationTubeMass
    (n := Module.finrank ℝ E) (fun c => P.commutatorMap (U c))
      (fun c => scaledHermitianPencilCommutatorDrift scale H₀ (U c)) w x
  change _ + κ ≤ _ at hx
  linarith

/-- Canonical pre-draw optimal-design specialization of the scale-free
quenched law. -/
theorem FiniteGaussianHermitianPencil.stdGaussian_measure_optimalDesignScaledAffineNearAction_gap_le
    [Nonempty ι] [MeasurableSpace E] [BorelSpace E]
    (P : FiniteGaussianHermitianPencil E ι)
    {H₀ : Matrix ι ι ℂ} (hH₀ : H₀.IsHermitian)
    {scale : ℝ} (hscale : scale ≠ 0)
    {C : Type*} [Fintype C] [Nonempty C] [DecidableEq C]
    (r : ℕ) (U : C → Matrix.unitaryGroup ι ℂ)
    (δ : ℝ) {κ : ℝ} (hκ : 0 < κ) :
    (stdGaussian E).real
        {x |
          (∑ c, finiteUnitaryChoiOptimalDesignWeight r U c *
            staticChoiAdaptiveReplicaBase
              (P.scaledAffineSpectralEnergy hH₀ scale x)
              ((Fintype.card ι : ℝ)⁻¹ *
                (scale ^ (2 : ℕ) * P.commutatorActivation (U c))) ^ r) + κ ≤
          ∑ c, finiteUnitaryChoiOptimalDesignWeight r U c *
            directStaticChoiTargetNearActionMass
              (choiVector
                (P.scaledAffineSpectralEndpoint hH₀ scale x (U c) :
                  Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ))
              (P.scaledAffineSpectralEnergy hH₀ scale x) r δ} ≤
      (∑ c, finiteUnitaryChoiOptimalDesignWeight r U c * Real.exp
        (-(gaussianIntervalActivationMass ^ (2 : ℕ) / 2) *
          (((∑ i : Fin (Module.finrank ℝ E),
              (P.commutatorMap (U c)).singularValues i ^ (2 : ℕ)) ^ (2 : ℕ)) /
            ∑ i : Fin (Module.finrank ℝ E),
              (P.commutatorMap (U c)).singularValues i ^ (4 : ℕ)))) / κ := by
  exact P.stdGaussian_measure_weightedScaledAffineNearAction_gap_le
    hH₀ hscale U (finiteUnitaryChoiOptimalDesignWeight r U)
      (finiteUnitaryChoiOptimalDesignWeight_mem_stdSimplex r U) r δ hκ

end

end RHTower
