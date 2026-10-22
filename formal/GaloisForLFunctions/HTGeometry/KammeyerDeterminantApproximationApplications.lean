import GaloisForLFunctions.HTGeometry.KammeyerDeterminantApproximationCore
import GaloisForLFunctions.RHTower.Suzuki.SuzukiFiniteMatrixHeisenberg
import GaloisForLFunctions.RHTower.RealSpectrumWithoutSelfAdjointness
import GaloisForLFunctions.HilbertMetric.PremiseWitnesses
import GaloisForLFunctions.HTGeometry.FiniteMatrixSchurQuarticQuadraticTraceEnergyDefect
import GaloisForLFunctions.HTGeometry.KukolNilpotentExponential
import GaloisForLFunctions.HTGeometry.KerrNewmanBelinskiZakharovBridge
import GaloisForLFunctions.RHTower.EulerSquarefreeWickGammaSixLaxCurvature
import GaloisForLFunctions.HTGeometry.GomesFockTaylorGauge
import GaloisForLFunctions.HTGeometry.FokasLenellsUniformization
import GaloisForLFunctions.HTGeometry.StrictlyLoweringFiltration
import GaloisForLFunctions.HTGeometry.FeedForwardChainResolvent
import GaloisForLFunctions.HTGeometry.HankelTerminalFlux
import GaloisForLFunctions.HTGeometry.ProjectiveHorizonLaurentResidueSeam
import GaloisForLFunctions.HTGeometry.PolynomialSignedPoissonProduct
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaSourceConormalSocle
import GaloisForLFunctions.RHTower.RankOnePolarizedExchangeCurvature
import GaloisForLFunctions.RHTower.LiftedGluingFaces
import GaloisForLFunctions.HTGeometry.ConservativeDissipativeSpinLindblad
import GaloisForLFunctions.HTGeometry.CorcoranDeLeeuwModelOne
import GaloisForLFunctions.RHTower.Suzuki.SuzukiXiRealFEBipolarizationCompletion
import GaloisForLFunctions.HTGeometry.ConstitutiveParitySuspensionHodge
import GaloisForLFunctions.HTGeometry.CassidySl2Graded
import GaloisForLFunctions.HTGeometry.SeibergWittenBRSTHodgeBridge
import GaloisForLFunctions.RHTower.SuperPoincareProjectionFamily
import GaloisForLFunctions.HTGeometry.GomesTruncatedJetUnipotentLogarithm
import GaloisForLFunctions.HTGeometry.KerrNewmanBelinskiZakharovLaxDressingBridge
import GaloisForLFunctions.RHTower.RankOnePolarizedExchangeHorizon
import GaloisForLFunctions.HTGeometry.QuadraticQuantumDetectorRepresentation
import GaloisForLFunctions.HTGeometry.ConstitutiveOnShellWronskianInternalization
import GaloisForLFunctions.RHTower.XiHedenmalmJordanMatrix
import GaloisForLFunctions.RHTower.TruncatedJetWeylBoundary
import GaloisForLFunctions.RHTower.XiNodalDefectSuperselection
import GaloisForLFunctions.HTGeometry.QuadraticWidthPrincipalSymbolCompletion
import GaloisForLFunctions.HTGeometry.ConstraintRelativity.TruncatedHardCoreFock
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaSourceConormalSocle
import GaloisForLFunctions.RHTower.EulerSquarefreeWickCompletedJetBundleLanding
import GaloisForLFunctions.HTGeometry.JordanWignerSpinFermionBridge
import GaloisForLFunctions.HTGeometry.LinearWidthPrincipalSymbolCompletion
import GaloisForLFunctions.HTGeometry.CrossPrimeCurvature
import GaloisForLFunctions.HTGeometry.FiniteQuantumGrassmannRepresentation
import GaloisForLFunctions.HTGeometry.UniversalPrincipalSymbolCompletion
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmEssentialInverseFlowTrace
import GaloisForLFunctions.HTGeometry.NomologicalHomotopyGeometry.LeadingCurvatureDescent

/-!
# Kammeyer determinant-approximation applications

Mechanical applications of finite-dimensional mechanisms isolated from Kammeyer's
determinant-approximation counterexample. Each theorem closes an existing corpus nilpotence proof
into an exact determinant-one statement. Families cover matrix, linear-map, and continuous-linear-
map models; no approximation limit, spectral conjecture, or new axiom is assumed.

Interpretation is deliberately local: ordinary determinant cannot see these nilpotent directions.
This does not identify unrelated corpus models with the paper's Heisenberg-group counterexample.
-/

open Matrix

namespace GaloisForLFunctions.HTGeometry.Kammeyer

private theorem negOne_isPrimitiveRoot_two {K : Type*} [Field K] [CharZero K] :
    IsPrimitiveRoot (-1 : K) 2 :=
  IsPrimitiveRoot.neg_one 0 (by omega)

theorem nilpotentShift2_det_resolvent (z : ℝ) :
    ((1 : Matrix Bool Bool ℝ) - z • RHTower.nilpotentShift2).det = 1 := by
  apply det_one_sub_smul_of_isNilpotent
  refine ⟨2, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pow_two, RHTower.nilpotentShift2, Matrix.mul_apply, Fintype.sum_bool]

theorem jordanBlock_det_resolvent (z : ℂ) :
    ((1 : Matrix (Fin 2) (Fin 2) ℂ) - z • RHTower.jordanBlock).det = 1 := by
  apply det_one_sub_smul_of_isNilpotent
  exact ⟨2, by simpa [pow_two] using RHTower.jordanBlock_sq⟩

theorem jordanNilpotentTwo_det_resolvent (z : ℝ) :
    ((1 : Matrix (Fin 2) (Fin 2) ℝ) -
      z • HilbertMetric.jordanNilpotentTwo).det = 1 := by
  apply det_one_sub_smul_of_isNilpotent
  refine ⟨2, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pow_two, HilbertMetric.jordanNilpotentTwo, Matrix.mul_apply, Fin.sum_univ_two]

theorem quadraticTraceEnergyDefectJordanBlock_det_resolvent (z : ℂ) :
    ((1 : Matrix (Fin 2) (Fin 2) ℂ) -
      z • quadraticTraceEnergyDefectJordanBlock).det = 1 := by
  apply det_one_sub_smul_of_isNilpotent
  refine ⟨2, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two, quadraticTraceEnergyDefectJordanBlock, Matrix.mul_apply, Fin.sum_univ_two]

theorem kukolNilpotentMatrix_det_resolvent (u z : ℂ) :
    ((1 : Matrix (Fin 3) (Fin 3) ℂ) - z • kukolNilpotentMatrix u).det = 1 := by
  apply det_one_sub_smul_of_isNilpotent
  exact ⟨3, kukolNilpotentMatrix_cube u⟩

theorem belinskiZakharovNilpotentResidue_det_resolvent (residue z : ℝ) :
    ((1 : Matrix (Fin 2) (Fin 2) ℝ) -
      z • belinskiZakharovNilpotentResidue residue).det = 1 := by
  apply det_one_sub_smul_of_isNilpotent
  exact ⟨2, by simpa [pow_two] using belinskiZakharovNilpotentResidue_sq residue⟩

theorem gammaSixForwardNilpotentResidue_det_resolvent (a z : ℝ) :
    ((1 : Matrix (Fin 2) (Fin 2) ℝ) -
      z • RHTower.gammaSixForwardNilpotentResidue a).det = 1 := by
  apply det_one_sub_smul_of_isNilpotent
  refine ⟨2, ?_⟩
  simpa [pow_two, RHTower.gammaSixForwardNilpotentResidue] using
    belinskiZakharovNilpotentResidue_sq (Real.exp a - 1)

theorem gammaSixReflectedNilpotentResidue_det_resolvent (a z : ℝ) :
    ((1 : Matrix (Fin 2) (Fin 2) ℝ) -
      z • RHTower.gammaSixReflectedNilpotentResidue a).det = 1 := by
  apply det_one_sub_smul_of_isNilpotent
  refine ⟨2, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two, RHTower.gammaSixReflectedNilpotentResidue,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem fockShiftMatrix_det_resolvent (N : ℕ) (z : ℂ) :
    ((1 : Matrix (Fin N) (Fin N) ℂ) -
      z • GammaFactorialFock.fockShiftMatrix N).det = 1 := by
  apply det_one_sub_smul_of_isNilpotent
  exact ⟨N, GammaFactorialFock.fockShiftMatrix_nilpotent N⟩

theorem effectivePotential_leftBoundary_det_resolvent (u w z : ℂ) :
    ((1 : Matrix (Fin 2) (Fin 2) ℂ) -
      z • FokasLenells.effectivePotential u 0 w).det = 1 := by
  apply det_one_sub_smul_of_isNilpotent
  exact (FokasLenells.effectivePotential_isNilpotent_iff u 0 w).mpr (Or.inl rfl)

theorem effectivePotential_rightBoundary_det_resolvent (u v z : ℂ) :
    ((1 : Matrix (Fin 2) (Fin 2) ℂ) -
      z • FokasLenells.effectivePotential u v 0).det = 1 := by
  apply det_one_sub_smul_of_isNilpotent
  exact (FokasLenells.effectivePotential_isNilpotent_iff u v 0).mpr (Or.inr rfl)

theorem feedForwardChainShift_det_resolvent (N : ℕ) (z : ℂ) :
    ((1 : Matrix (Fin N) (Fin N) ℂ) - z • feedForwardChainShift N).det = 1 := by
  apply det_one_sub_smul_of_isNilpotent
  have hupper : StrictlyLowering.StrictlyUpper (feedForwardChainShift N)ᵀ := by
    intro i j hji
    simp [feedForwardChainShift, Matrix.transpose_apply]
    omega
  apply Matrix.isNilpotent_transpose_iff.mp
  exact ⟨N, StrictlyLowering.pow_eq_zero_of_strictlyUpper hupper⟩

theorem feedForwardChainOperator_det (N : ℕ) (q : ℂ) :
    (feedForwardChainOperator N q).det = 1 := by
  exact feedForwardChainShift_det_resolvent N q

theorem hankelWeightedUpperShift_det_resolvent (n : ℕ) (z : ℝ) :
    ((1 : Matrix (Fin n) (Fin n) ℝ) - z • hankelWeightedUpperShift n).det = 1 := by
  apply det_one_sub_smul_of_isNilpotent
  have hupper : StrictlyLowering.StrictlyUpper (hankelWeightedUpperShift n) := by
    intro i j hji
    simp [hankelWeightedUpperShift]
    omega
  exact ⟨n, StrictlyLowering.pow_eq_zero_of_strictlyUpper hupper⟩

theorem a2ConstantE01_det_resolvent {K : Type*} [Field K] (z : K) :
    ((1 : Matrix (Fin 3) (Fin 3) K) - z • a2ConstantE01 K).det = 1 := by
  apply det_one_sub_smul_of_isNilpotent
  refine ⟨2, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two, a2ConstantE01, Matrix.mul_apply, Fin.sum_univ_succ]

theorem a2ConstantE10_det_resolvent {K : Type*} [Field K] (z : K) :
    ((1 : Matrix (Fin 3) (Fin 3) K) - z • a2ConstantE10 K).det = 1 := by
  apply det_one_sub_smul_of_isNilpotent
  refine ⟨2, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two, a2ConstantE10, Matrix.mul_apply, Fin.sum_univ_succ]

theorem a2ConstantE02_det_resolvent {K : Type*} [Field K] (z : K) :
    ((1 : Matrix (Fin 3) (Fin 3) K) - z • a2ConstantE02 K).det = 1 := by
  apply det_one_sub_smul_of_isNilpotent
  refine ⟨2, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two, a2ConstantE02, Matrix.mul_apply, Fin.sum_univ_succ]

theorem a2ConstantE20_det_resolvent {K : Type*} [Field K] (z : K) :
    ((1 : Matrix (Fin 3) (Fin 3) K) - z • a2ConstantE20 K).det = 1 := by
  apply det_one_sub_smul_of_isNilpotent
  refine ⟨2, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two, a2ConstantE20, Matrix.mul_apply, Fin.sum_univ_succ]

theorem a2ConstantE12_det_resolvent {K : Type*} [Field K] (z : K) :
    ((1 : Matrix (Fin 3) (Fin 3) K) - z • a2ConstantE12 K).det = 1 := by
  apply det_one_sub_smul_of_isNilpotent
  refine ⟨2, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two, a2ConstantE12, Matrix.mul_apply, Fin.sum_univ_succ]

theorem a2ConstantE21_det_resolvent {K : Type*} [Field K] (z : K) :
    ((1 : Matrix (Fin 3) (Fin 3) K) - z • a2ConstantE21 K).det = 1 := by
  apply det_one_sub_smul_of_isNilpotent
  refine ⟨2, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two, a2ConstantE21, Matrix.mul_apply, Fin.sum_univ_succ]

theorem exchangeE12_det_resolvent {K : Type*} [Field K] (z : K) :
    ((1 : Matrix (Fin 2) (Fin 2) K) - z • RHTower.exchangeE12 K).det = 1 :=
  det_one_sub_smul_of_mul_self_eq_zero _ (RHTower.exchangeE12_sq (k := K)) z

theorem crossNilpℚ_det_resolvent (z : ℚ) :
    ((1 : Matrix (Fin 2) (Fin 2) ℚ) - z • RHTower.crossNilpℚ).det = 1 :=
  det_one_sub_smul_of_mul_self_eq_zero _ RHTower.crossNilpℚ_sq z

theorem spinLowering_det_resolvent (z : ℂ) :
    ((1 : Matrix (Fin 2) (Fin 2) ℂ) - z • SchafferExl.spinLowering).det = 1 := by
  apply det_one_sub_smul_of_isNilpotent
  refine ⟨2, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two, SchafferExl.spinLowering, Matrix.mul_apply, Fin.sum_univ_two]

theorem modelOneNilpotent_det_resolvent (z : ℂ) :
    ((1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) -
      z • modelOneNilpotent).det = 1 :=
  det_one_sub_smul_of_mul_self_eq_zero _ modelOneNilpotent_sq z

theorem modelOneBraid_sub_one_det_resolvent (f g z : ℂ) :
    ((1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) -
      z • (modelOneBraid 0 f g - 1)).det = 1 :=
  det_one_sub_smul_of_mul_self_eq_zero _ (modelOneBraid_sub_one_sq f g) z

theorem signedPoissonDifference_det_resolvent (n : ℕ) (z : ℝ) :
    LinearMap.det
      ((1 : Module.End ℝ (_root_.HTGeometry.SignedPoisson.PolyBelow n)) -
        z • _root_.HTGeometry.SignedPoisson.difference n) = 1 :=
  linearMap_det_one_sub_smul_of_isNilpotent _
    (_root_.HTGeometry.SignedPoisson.difference_isNilpotent n) z

theorem thetaRootNilpotentPart_det_resolvent
    (mu : RHTower.HedenmalmThetaSource.ThetaNonzeroSpectrum) (z : ℂ) :
    LinearMap.det
      ((1 : Module.End ℂ (RHTower.HedenmalmThetaSource.ThetaRootBlock mu)) -
        z • RHTower.HedenmalmThetaSource.thetaRootNilpotentPart mu) = 1 :=
  linearMap_det_one_sub_smul_of_isNilpotent _
    (RHTower.HedenmalmThetaSource.thetaRootNilpotentPart_isNilpotent mu) z

theorem suzukiWeldPositiveTriangleLinear_det_resolvent (z : ℝ) :
    LinearMap.det ((1 : Module.End ℝ (ℝ × ℝ)) -
      z • RHTower.suzukiWeldPositiveTriangleLinear) = 1 := by
  apply linearMap_det_one_sub_smul_of_isNilpotent
  refine ⟨2, ?_⟩
  rw [pow_two]
  change RHTower.suzukiWeldPositiveTriangleLinear.comp
      RHTower.suzukiWeldPositiveTriangleLinear = 0
  exact RHTower.suzukiWeldPositiveTriangleLinear_sq

theorem suzukiWeldNegativeTriangleLinear_det_resolvent (z : ℝ) :
    LinearMap.det ((1 : Module.End ℝ (ℝ × ℝ)) -
      z • RHTower.suzukiWeldNegativeTriangleLinear) = 1 := by
  apply linearMap_det_one_sub_smul_of_isNilpotent
  refine ⟨2, ?_⟩
  rw [pow_two]
  change RHTower.suzukiWeldNegativeTriangleLinear.comp
      RHTower.suzukiWeldNegativeTriangleLinear = 0
  exact RHTower.suzukiWeldNegativeTriangleLinear_sq

theorem paritySuspensionCharge_det_resolvent
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (J : Module.End K V) (z : K) :
    LinearMap.det ((1 : Module.End K (V × V)) - z • paritySuspensionCharge J) = 1 := by
  apply linearMap_det_one_sub_smul_of_isNilpotent
  exact ⟨2, by simpa [pow_two] using paritySuspensionCharge_sq J⟩

theorem sl2E_det_resolvent {K : Type*} [Field K] (z : K) :
    ((1 : Matrix (Fin 2) (Fin 2) K) - z • sl2E K).det = 1 := by
  apply det_one_sub_smul_of_isNilpotent
  refine ⟨2, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two, sl2E, Matrix.mul_apply, Fin.sum_univ_two]

theorem sl2F_det_resolvent {K : Type*} [Field K] (z : K) :
    ((1 : Matrix (Fin 2) (Fin 2) K) - z • sl2F K).det = 1 := by
  apply det_one_sub_smul_of_isNilpotent
  refine ⟨2, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two, sl2F, Matrix.mul_apply, Fin.sum_univ_two]

theorem polynomialLowerCrossing_det_resolvent (z : Polynomial ℚ) :
    ((1 : Matrix (Fin 2) (Fin 2) (Polynomial ℚ)) -
      z • RHTower.polynomialLowerCrossing).det = 1 := by
  apply det_one_sub_smul_of_isNilpotent
  refine ⟨2, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two, RHTower.polynomialLowerCrossing, Matrix.mul_apply, Fin.sum_univ_two]

theorem crossWitness_det_resolvent (z : ℚ) :
    ((1 : Matrix (Fin 2) (Fin 2) ℚ) - z • RHTower.crossWitness).det = 1 := by
  apply det_one_sub_smul_of_isNilpotent
  refine ⟨2, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two, RHTower.crossWitness, Matrix.mul_apply, Fin.sum_univ_two]

theorem finiteBrstCharge_det_resolvent (z : ℂ) :
    ContinuousLinearMap.det
      ((1 : SeibergWitten.HilbertSeibergWittenSpinor →L[ℂ]
          SeibergWitten.HilbertSeibergWittenSpinor) -
        z • SeibergWitten.finiteBrstCharge) = 1 :=
  continuousLinearMap_det_one_sub_smul_of_mul_self_eq_zero _
    SeibergWitten.finiteBrstCharge_sq_eq_zero z

theorem projectionPhaseNormal_det_resolvent (z : ℂ) :
    ContinuousLinearMap.det
      ((1 : RHTower.ProjectionPhaseEnd) - z • RHTower.projectionPhaseNormal) = 1 :=
  continuousLinearMap_det_one_sub_smul_of_mul_self_eq_zero _
    RHTower.projectionPhaseNormal_sq z

theorem hilbertParitySuspensionCharge_det_resolvent
    {K E : Type*} [RCLike K] [NormedAddCommGroup E] [InnerProductSpace K E]
    [FiniteDimensional K E] (J : E →L[K] E) (z : K) :
    ContinuousLinearMap.det
      ((1 : HilbertParityDouble (E := E) →L[K] HilbertParityDouble (E := E)) -
        z • hilbertParitySuspensionCharge J) = 1 :=
  continuousLinearMap_det_one_sub_smul_of_mul_self_eq_zero _
    (hilbertParitySuspensionCharge_sq J) z

theorem gomesTruncatedJetJointNilpotentPart_det_resolvent
    (n : ℕ) (phase w : ℂ)
    (E : GammaFactorialFock.gomesTruncatedJetJointAlgebra n phase) :
    ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) -
      w • (E.val - algebraMap ℂ (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
        (GammaFactorialFock.gomesTruncatedJetAugmentation n phase E))).det = 1 :=
  det_one_sub_smul_of_pow_eq_zero _ (n + 1)
    (GammaFactorialFock.gomesTruncatedJetJointAlgebra_sub_scalar_pow n phase E) w

theorem gomesTruncatedJetNilpotentCoordinate_det_resolvent
    (n : ℕ) (phase w : ℂ)
    (E : GammaFactorialFock.gomesTruncatedJetNilpotentSpace n phase) :
    ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) - w • E.val.val).det = 1 :=
  det_one_sub_smul_of_pow_eq_zero _ (n + 1)
    (GammaFactorialFock.gomesTruncatedJetNilpotentSpace_pow n phase E) w

theorem gomesTruncatedJetUnipotentLogarithm_det_resolvent
    (n : ℕ) (phase w : ℂ)
    (u : GammaFactorialFock.gomesTruncatedJetUnipotentGroup n phase) :
    ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) -
      w • (GammaFactorialFock.gomesTruncatedJetUnipotentLogarithm n phase u).val.val).det = 1 :=
  det_one_sub_smul_of_pow_eq_zero _ (n + 1)
    (GammaFactorialFock.gomesTruncatedJetUnipotentLogarithm_pow n phase u) w

theorem fockTaylorMatrix_det (N : ℕ) (z : ℂ) :
    (GammaFactorialFock.fockTaylorMatrix N z).det = 1 := by
  apply det_normed_exp_of_pow_eq_zero
  rw [smul_pow, GammaFactorialFock.fockShiftMatrix_nilpotent, smul_zero]

theorem belinskiZakharovNilpotentLaxU_det_resolvent
    (residue rho coordinate z : ℝ) :
    ((1 : Matrix (Fin 2) (Fin 2) ℝ) -
      z • belinskiZakharovNilpotentLaxU residue rho coordinate).det = 1 := by
  apply det_one_sub_smul_of_isNilpotent
  refine ⟨2, ?_⟩
  rw [pow_two]
  unfold belinskiZakharovNilpotentLaxU
  rw [Matrix.smul_mul, Matrix.mul_smul, belinskiZakharovNilpotentResidue_sq,
    smul_zero, smul_zero]

theorem belinskiZakharovNilpotentLaxV_det_resolvent
    (residue rho coordinate z : ℝ) :
    ((1 : Matrix (Fin 2) (Fin 2) ℝ) -
      z • belinskiZakharovNilpotentLaxV residue rho coordinate).det = 1 := by
  apply det_one_sub_smul_of_isNilpotent
  refine ⟨2, ?_⟩
  rw [pow_two]
  unfold belinskiZakharovNilpotentLaxV
  rw [Matrix.smul_mul, Matrix.mul_smul, belinskiZakharovNilpotentResidue_sq,
    smul_zero, smul_zero]

theorem belinskiZakharovOnePoleDressedNilpotentLaxU_det_resolvent
    (spectral pole dressingResidue laxResidue rho coordinate z : ℝ) :
    ((1 : Matrix (Fin 2) (Fin 2) ℝ) - z •
      belinskiZakharovOnePoleDressedNilpotentLaxU
        spectral pole dressingResidue laxResidue rho coordinate).det = 1 := by
  rw [belinskiZakharovOnePoleDressedNilpotentLaxU_eq]
  exact belinskiZakharovNilpotentLaxU_det_resolvent laxResidue rho coordinate z

theorem belinskiZakharovOnePoleDressedNilpotentLaxV_det_resolvent
    (spectral pole dressingResidue laxResidue rho coordinate z : ℝ) :
    ((1 : Matrix (Fin 2) (Fin 2) ℝ) - z •
      belinskiZakharovOnePoleDressedNilpotentLaxV
        spectral pole dressingResidue laxResidue rho coordinate).det = 1 := by
  rw [belinskiZakharovOnePoleDressedNilpotentLaxV_eq]
  exact belinskiZakharovNilpotentLaxV_det_resolvent laxResidue rho coordinate z

/-! ## Further square-zero and truncated-chain closures -/

theorem exchangeDifferential_det_resolvent
    {K : Type*} [Field K] (chi : ℕ+ →* Kˣ) (n : ℕ+) (z : K) :
    ((1 : Matrix (Fin 2) (Fin 2) K) -
      z • RHTower.exchangeDifferential chi n).det = 1 :=
  det_one_sub_smul_of_mul_self_eq_zero _ (RHTower.exchangeDifferential_sq chi n) z

theorem quadraticQuantumDetectorGenerator_det_resolvent
    {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    [FiniteDimensional K M] {n : ℕ} (q : K) (i : Fin n) (z : K) :
    LinearMap.det
      ((1 : Module.End K (QuadraticQuantumDetectorState M n)) -
        z • quadraticQuantumDetectorGenerator (M := M) q i) = 1 := by
  apply linearMap_det_one_sub_smul_of_isNilpotent
  exact ⟨2, quadraticQuantumDetectorGenerator_sq (M := M) q i⟩

theorem polynomialEquationWronskian_det_resolvent
    {K : Type*} [Field K] (m : ℕ) (z : K) :
    LinearMap.det
      ((1 : Module.End K
          (EquationFibre ((Polynomial.X : Polynomial K) ^ (m + 2)))) -
        z • (equationWronskianQuotient (Polynomial.derivative' (R := K))
          (Polynomial.X ^ (m + 2))).restrictScalars K) = 1 := by
  apply linearMap_det_one_sub_smul_of_isNilpotent
  refine ⟨2, ?_⟩
  rw [pow_two]
  apply LinearMap.ext
  intro x
  exact LinearMap.congr_fun
    (polynomialEquationWronskian_sq_zero (K := K) (m + 2) (by omega)) x

theorem xiLocalJordanNilpotentPart_det_resolvent
    (rho : RHTower.XiDivisorSupport) (z : ℂ) :
    ((1 : Matrix (Fin (RHTower.xiSupportMultiplicity rho))
        (Fin (RHTower.xiSupportMultiplicity rho)) ℂ) -
      z • (RHTower.xiLocalJordanMatrix rho -
        RHTower.xiSpectralPointSupport rho • 1)).det = 1 := by
  apply det_one_sub_smul_of_isNilpotent
  refine ⟨RHTower.xiSupportMultiplicity rho,
    StrictlyLowering.pow_eq_zero_of_strictlyUpper ?_⟩
  intro i j hji
  simp only [RHTower.xiLocalJordanMatrix, Matrix.sub_apply,
    Matrix.smul_apply, Matrix.one_apply]
  by_cases hij : i = j
  · simp [hij]
  · simp [hij]
    omega

/-! ## Finite clocks, fermions, and completed divisor channels -/

theorem truncatedJetOneSidedShift_det_resolvent (n : ℕ) (z : ℂ) :
    ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) -
      z • RHTower.boundaryCompletedJetShift n 0).det = 1 := by
  apply det_one_sub_smul_of_isNilpotent
  apply Matrix.isNilpotent_transpose_iff.mp
  refine ⟨n + 1, StrictlyLowering.pow_eq_zero_of_strictlyUpper ?_⟩
  intro i j hji
  simp only [Matrix.transpose_apply, RHTower.boundaryCompletedJetShift]
  have hstep : (i : ℕ) + 1 ≠ (j : ℕ) := by omega
  simp [hstep]

theorem xiNodalGradeDifferential_det_resolvent
    (q : RHTower.XiZeroCopy) (z : ℝ) :
    ((1 : Matrix (Fin 2) (Fin 2) ℝ) -
      z • RHTower.xiNodalGradeDifferential q).det = 1 :=
  det_one_sub_smul_of_mul_self_eq_zero _
    (RHTower.xiNodalGradeDifferential_sq_zero q) z

theorem xiNodalPhaseDifferential_det_resolvent
    (q : RHTower.XiZeroCopy) (z : ℝ) :
    ((1 : Matrix (Fin 2) (Fin 2) ℝ) -
      z • RHTower.xiNodalPhaseDifferential q).det = 1 :=
  det_one_sub_smul_of_mul_self_eq_zero _
    (RHTower.xiNodalPhaseDifferential_sq_zero q) z

theorem quadraticCompletionDetectorGenerator_det_resolvent
    {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    [FiniteDimensional K M] (d : ℕ) {n : ℕ} (q : K) (i : Fin n) (z : K) :
    LinearMap.det
      ((1 : Module.End K (QuadraticPrincipalCompletionState M n (d + 1))) -
        z • quadraticCompletionDetectorGenerator (M := M) (d := d + 1) q i) = 1 :=
  linearMap_det_one_sub_smul_of_pow_eq_zero _ 2
    (quadraticCompletionDetectorGenerator_sq (M := M) (d := d + 1) q i) z

theorem truncatedCreator_det_resolvent (d : ℕ) (i : Fin d) (z : ℂ) :
    LinearMap.det
      ((1 : Module.End ℂ (_root_.HTGeometry.ConstraintRelativity.TruncatedFaceFock d)) -
        z • _root_.HTGeometry.ConstraintRelativity.truncatedCreator i) = 1 := by
  apply linearMap_det_one_sub_smul_of_pow_eq_zero _ 2
  rw [pow_two]
  apply LinearMap.ext
  exact _root_.HTGeometry.ConstraintRelativity.truncatedCreator_sq_zero i

theorem thetaSourceConormalParityCharge_det_resolvent
    (mu : RHTower.HedenmalmThetaSource.ThetaNonzeroSpectrum) (z : ℂ) :
    ContinuousLinearMap.det
      ((1 : RHTower.HedenmalmThetaSource.ThetaSourceConormalParityDouble mu →L[ℂ]
          RHTower.HedenmalmThetaSource.ThetaSourceConormalParityDouble mu) -
        z • RHTower.HedenmalmThetaSource.thetaSourceConormalParityCharge mu) = 1 :=
  continuousLinearMap_det_one_sub_smul_of_mul_self_eq_zero _
    (RHTower.HedenmalmThetaSource.thetaSourceConormalParityCharge_sq mu) z

theorem eulerWickTriangularCompletedExtension_det_resolvent
    (q : RHTower.XiZeroCopy) (z : ℂ) :
    ((1 : Matrix (Fin 2) (Fin 2) ℂ) -
      z • RHTower.eulerWickTriangularCompletedExtension q.1).det = 1 := by
  apply det_one_sub_smul_of_mul_self_eq_zero
  exact (RHTower.eulerWickTriangularCompletedExtension_sq_eq_zero_iff q.1).mpr
    (RHTower.xi_eq_zero_of_mem_divisor_support q.1)

theorem exists_eulerWickCompletedJetExtension_det_resolvent
    (q : RHTower.XiZeroCopy) (z : ℂ) :
    ∃ n : ℕ,
      ((1 : Matrix (Fin 2) (Fin 2) ℂ) -
        z • RHTower.eulerWickCompletedJetExtension q.1 n).det = 1 := by
  have hsq := (RHTower.eulerWickCompletedJetExtension_nonzero_squareZero_iff q.1).mpr
    (RHTower.xi_eq_zero_of_mem_divisor_support q.1)
  obtain ⟨n, _, hn⟩ := hsq
  exact ⟨n, det_one_sub_smul_of_mul_self_eq_zero _ hn z⟩

theorem jordanWignerCreation_det_resolvent
    {n : ℕ} (j : Fin n) (z : ℂ) :
    ((1 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) -
      z • jordanWignerCreation j).det = 1 :=
  det_one_sub_smul_of_mul_self_eq_zero _ (jordanWignerCreation_sq_zero j) z

theorem jordanWignerAnnihilation_det_resolvent
    {n : ℕ} (j : Fin n) (z : ℂ) :
    ((1 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) -
      z • jordanWignerAnnihilation j).det = 1 :=
  det_one_sub_smul_of_mul_self_eq_zero _ (jordanWignerAnnihilation_sq_zero j) z

theorem linearWidthDetectorSymbol_det_resolvent
    {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    [FiniteDimensional K M] {n : ℕ} (c : Fin n → K) (z : K) :
    LinearMap.det
      ((1 : Module.End K (LinearWidthDetectorState M n)) -
        z • linearWidthDetectorSymbol (K := K) (M := M) c) = 1 :=
  linearMap_det_one_sub_smul_of_pow_eq_zero _ 3
    (linearWidthDetectorSymbol_cube_zero (K := K) (M := M) c) z

theorem linearCompletionDetectorSymbol_det_resolvent
    {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    [FiniteDimensional K M] (d : ℕ) {n : ℕ} (c : Fin n → K) (z : K) :
    LinearMap.det
      ((1 : Module.End K (LinearPrincipalCompletionState M n (d + 1))) -
        z • linearCompletionDetectorSymbol
          (K := K) (M := M) (d := d + 1) c) = 1 :=
  linearMap_det_one_sub_smul_of_pow_eq_zero _ 3
    (linearCompletionDetectorSymbol_cube_zero
      (K := K) (M := M) (d := d + 1) c) z

theorem upperUnipotentE_nilpotentPart_det_resolvent
    {K : Type*} [Field K] (a z : K) :
    ((1 : Matrix (Fin 2) (Fin 2) K) -
      z • (GaloisForLFunctions.upperUnipotentE K a - 1)).det = 1 := by
  apply det_one_sub_smul_of_mul_self_eq_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [GaloisForLFunctions.upperUnipotentE, Matrix.mul_apply, Fin.sum_univ_two]

theorem upperUnipotentE_det {K : Type*} [Field K] (a : K) :
    (GaloisForLFunctions.upperUnipotentE K a).det = 1 := by
  have h := upperUnipotentE_nilpotentPart_det_resolvent a (-1 : K)
  simpa [sub_eq_add_neg] using h

/-! ## Aggregate quantum packets and complete theta root blocks -/

theorem finiteQuantumGrassmannSymbol_negOne_det_resolvent
    {K : Type*} [Field K] [CharZero K] (n : ℕ) (c : Fin n → K) (z : K) :
    LinearMap.det
      ((1 : Module.End K (FiniteQuantumState (Fin n) 2 → K)) -
        z • quantumGeneratorSymbol
          (fun i : Fin n ↦ finiteQuantumGrassmannGenerator 2 (-1 : K)
            (negOne_isPrimitiveRoot_two (K := K)).pow_eq_one i) c) = 1 :=
  linearMap_det_one_sub_smul_of_pow_eq_zero _ 2
    (finiteQuantumGrassmannSymbol_pow_degree_zero (-1 : K)
      (negOne_isPrimitiveRoot_two (K := K)) c) z

theorem quadraticQuantumDetectorSymbol_negOne_det_resolvent
    {K M : Type*} [Field K] [CharZero K] [AddCommGroup M] [Module K M]
    [FiniteDimensional K M] {n : ℕ} (c : Fin n → K) (z : K) :
    LinearMap.det
      ((1 : Module.End K (QuadraticQuantumDetectorState M n)) -
        z • quadraticQuantumDetectorSymbol (M := M) (-1 : K) c) = 1 :=
  linearMap_det_one_sub_smul_of_pow_eq_zero _ 2
    (quadraticQuantumDetectorSymbol_pow_degree_zero (d := 2) (-1 : K)
      (negOne_isPrimitiveRoot_two (K := K)) c) z

theorem quantumCompletionDetectorSymbol_negOne_det_resolvent
    {K M : Type*} [Field K] [CharZero K] [AddCommGroup M] [Module K M]
    [FiniteDimensional K M] {n : ℕ} (c : Fin n → K) (z : K) :
    LinearMap.det
      ((1 : Module.End K (QuantumPrincipalCompletionState M n 2)) -
        z • quantumCompletionDetectorSymbol (M := M) (-1 : K)
          (negOne_isPrimitiveRoot_two (K := K)).pow_eq_one c) = 1 :=
  linearMap_det_one_sub_smul_of_pow_eq_zero _ 2
    (quantumCompletionDetectorSymbol_pow_degree_zero (-1 : K)
      (negOne_isPrimitiveRoot_two (K := K)) c) z

theorem thetaRootBlockOperator_nilpotentPart_det_resolvent
    (mu : RHTower.HedenmalmThetaSource.ThetaNonzeroSpectrum) (z : ℂ) :
    LinearMap.det
      (1 - z • (RHTower.HedenmalmThetaSource.thetaRootBlockOperator mu -
        algebraMap ℂ _ (mu : ℂ))) = 1 :=
  linearMap_det_one_sub_smul_of_isNilpotent _
    (RHTower.HedenmalmThetaSource.thetaRootBlockOperator_sub_isNilpotent mu) z

/-! ## Flat differentials and descended homology connections -/

theorem flatDifferential_det_resolvent
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    [FiniteDimensional K E]
    (C : _root_.HTGeometry.NomologicalHomotopyGeometry.FlatSuperconnection.Differential
      (k := K) (E := E)) (z : K) :
    LinearMap.det ((1 : Module.End K E) - z • C.d) = 1 := by
  apply linearMap_det_one_sub_smul_of_pow_eq_zero _ 2
  rw [pow_two]
  exact C.sq_zero

theorem leadingHomologyConnection_det_resolvent
    {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (L : _root_.HTGeometry.NomologicalHomotopyGeometry.LeadingCurvatureDescent.LeadingLayer
      (E := E)) (z : ℝ) :
    LinearMap.det
      (1 - z •
        _root_.HTGeometry.NomologicalHomotopyGeometry.LeadingCurvatureDescent.LeadingLayer.homologyConnection
          L) = 1 := by
  apply linearMap_det_one_sub_smul_of_pow_eq_zero _ 2
  rw [pow_two]
  exact _root_.HTGeometry.NomologicalHomotopyGeometry.LeadingCurvatureDescent.LeadingLayer.homologyConnection_sq_eq_zero
    L

end GaloisForLFunctions.HTGeometry.Kammeyer
