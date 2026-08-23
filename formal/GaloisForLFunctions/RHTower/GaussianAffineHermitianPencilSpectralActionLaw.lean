import GaloisForLFunctions.RHTower.GaussianHermitianPencilSpectralActionLaw
import GaloisForLFunctions.HTGeometry.GaussianAffineStableRankLowerTail

/-!
# Universal affine-Gaussian spectral action law

A deterministic Hermitian drift may be added to every finite Gaussian
Hermitian pencil without weakening observer anti-concentration.  Thus a
Gaussian ensemble may be centered on a laboratory-growth witness while the
same exact stable-rank action carrier controls its circuit endpoints.
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

/-- Half-activation tube for an affine observer `A x - y`. -/
def gaussianAffineHalfActivationTube
    {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (A : E →ₗ[ℝ] F) (y : F) : Set E :=
  {x | ‖A x - y‖ ^ 2 ≤
    (gaussianIntervalActivationMass / 2) *
      ∑ i : Fin n, A.singularValues i ^ 2}

theorem measurableSet_gaussianAffineHalfActivationTube
    {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace E] [BorelSpace E]
    (A : E →ₗ[ℝ] F) (y : F) :
    MeasurableSet (gaussianAffineHalfActivationTube (n := n) A y) := by
  exact measurableSet_le
    ((((LinearMap.continuous_of_finiteDimensional A).sub continuous_const).norm.pow 2).measurable)
    measurable_const

/-- Probability-design mass of affine observer tubes. -/
def gaussianWeightedAffineHalfActivationTubeMass
    {n : ℕ} {C F : Type*} [Fintype C]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (A : C → E →ₗ[ℝ] F) (y : C → F) (w : C → ℝ) (x : E) : ℝ :=
  ∑ c, w c * Set.indicator
    (gaussianAffineHalfActivationTube (n := n) (A c) (y c)) (1 : E → ℝ) x

theorem gaussianWeightedAffineHalfActivationTubeMass_nonneg
    {n : ℕ} {C F : Type*} [Fintype C]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (A : C → E →ₗ[ℝ] F) (y : C → F) (w : C → ℝ)
    (hw : ∀ c, 0 ≤ w c) (x : E) :
    0 ≤ gaussianWeightedAffineHalfActivationTubeMass (n := n) A y w x := by
  unfold gaussianWeightedAffineHalfActivationTubeMass
  exact Finset.sum_nonneg fun c _ =>
    mul_nonneg (hw c) (Set.indicator_nonneg (fun _ _ => zero_le_one) _)

theorem gaussianWeightedAffineHalfActivationTubeMass_le_one
    {n : ℕ} {C F : Type*} [Fintype C]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (A : C → E →ₗ[ℝ] F) (y : C → F) (w : C → ℝ)
    (hw : w ∈ stdSimplex ℝ C) (x : E) :
    gaussianWeightedAffineHalfActivationTubeMass (n := n) A y w x ≤ 1 := by
  unfold gaussianWeightedAffineHalfActivationTubeMass
  calc
    _ ≤ ∑ c, w c * 1 := by
      apply Finset.sum_le_sum
      intro c _
      apply mul_le_mul_of_nonneg_left _ (hw.1 c)
      by_cases hc : x ∈ gaussianAffineHalfActivationTube (n := n) (A c) (y c)
      · simp [Set.indicator_of_mem hc]
      · simp [Set.indicator_of_notMem hc]
    _ = 1 := by rw [← Finset.sum_mul, hw.2, one_mul]

theorem measurable_gaussianWeightedAffineHalfActivationTubeMass
    {n : ℕ} {C F : Type*} [Fintype C]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace E] [BorelSpace E]
    (A : C → E →ₗ[ℝ] F) (y : C → F) (w : C → ℝ) :
    Measurable (gaussianWeightedAffineHalfActivationTubeMass (n := n) A y w) := by
  unfold gaussianWeightedAffineHalfActivationTubeMass
  apply Finset.measurable_sum
  intro c _
  exact (measurable_one.indicator
    (measurableSet_gaussianAffineHalfActivationTube (n := n) (A c) (y c))).const_mul (w c)

/-- Weighted affine observer law: arbitrary deterministic drifts cost
nothing, endpoint cardinality disappears, and only averaged stable ranks
remain. -/
theorem stdGaussian_measure_weightedAffineHalfActivationTubeMass_ge_le
    {n : ℕ} {C F : Type*} [Fintype C]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace E] [BorelSpace E]
    (A : C → E →ₗ[ℝ] F) (y : C → F)
    (hn : Module.finrank ℝ E = n)
    (w : C → ℝ) (hw : w ∈ stdSimplex ℝ C)
    {κ : ℝ} (hκ : 0 < κ) :
    (stdGaussian E).real {x |
        κ ≤ gaussianWeightedAffineHalfActivationTubeMass (n := n) A y w x} ≤
      (∑ c, w c * Real.exp
        (-(gaussianIntervalActivationMass ^ 2 / 2) *
          (((∑ i : Fin n, (A c).singularValues i ^ 2) ^ 2) /
            ∑ i : Fin n, (A c).singularValues i ^ 4))) / κ := by
  have hmeas := measurable_gaussianWeightedAffineHalfActivationTubeMass
    (n := n) A y w
  have hnonneg : 0 ≤ᵐ[stdGaussian E]
      gaussianWeightedAffineHalfActivationTubeMass (n := n) A y w :=
    Filter.Eventually.of_forall fun x =>
      gaussianWeightedAffineHalfActivationTubeMass_nonneg A y w hw.1 x
  have hint : Integrable
      (gaussianWeightedAffineHalfActivationTubeMass (n := n) A y w)
      (stdGaussian E) := by
    apply Integrable.of_bound hmeas.aestronglyMeasurable 1
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg
      (gaussianWeightedAffineHalfActivationTubeMass_nonneg A y w hw.1 x)]
    exact gaussianWeightedAffineHalfActivationTubeMass_le_one A y w hw x
  have hmark := mul_meas_ge_le_integral_of_nonneg hnonneg hint κ
  have hintEq :
      (∫ x, gaussianWeightedAffineHalfActivationTubeMass (n := n) A y w x
          ∂(stdGaussian E)) =
        ∑ c, w c * (stdGaussian E).real
          (gaussianAffineHalfActivationTube (n := n) (A c) (y c)) := by
    unfold gaussianWeightedAffineHalfActivationTubeMass
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro c _
      rw [integral_const_mul, integral_indicator_one
        (measurableSet_gaussianAffineHalfActivationTube
          (n := n) (A c) (y c))]
    · intro c _
      exact ((integrable_const (1 : ℝ)).indicator
        (measurableSet_gaussianAffineHalfActivationTube
          (n := n) (A c) (y c))).const_mul (w c)
  rw [hintEq] at hmark
  apply (le_div_iff₀ hκ).2
  rw [mul_comm]
  refine hmark.trans ?_
  apply Finset.sum_le_sum
  intro c _
  exact mul_le_mul_of_nonneg_left
    (stdGaussian_measure_linearMap_affine_norm_sq_le_halfActivation
      (A c) (y c) hn) (hw.1 c)

/-- Reindexed Hilbert--Schmidt commutator energy of an arbitrary physical
matrix equals the Euclidean norm of its physical commutator. -/
theorem finiteMatrixHilbertSchmidtEnergy_reindexedCommutator
    (H : Matrix ι ι ℂ) (U : Matrix.unitaryGroup ι ℂ) :
    finiteMatrixHilbertSchmidtEnergy
        (Matrix.reindexAlgEquiv ℂ ℂ (Fintype.equivFin ι) H *
            (finiteGaussianHermitianPencilReindexedEndpoint U :
              Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ) -
          (finiteGaussianHermitianPencilReindexedEndpoint U :
              Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ) *
            Matrix.reindexAlgEquiv ℂ ℂ (Fintype.equivFin ι) H) =
      ‖matVec (H * (U : Matrix ι ι ℂ) -
        (U : Matrix ι ι ℂ) * H)‖ ^ 2 := by
  have hmatrix :
      Matrix.reindexAlgEquiv ℂ ℂ (Fintype.equivFin ι) H *
            (finiteGaussianHermitianPencilReindexedEndpoint U :
              Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ) -
          (finiteGaussianHermitianPencilReindexedEndpoint U :
              Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ) *
            Matrix.reindexAlgEquiv ℂ ℂ (Fintype.equivFin ι) H =
        Matrix.reindexAlgEquiv ℂ ℂ (Fintype.equivFin ι)
          (H * (U : Matrix ι ι ℂ) -
            (U : Matrix ι ι ℂ) * H) := by
    change
      Matrix.reindexAlgEquiv ℂ ℂ (Fintype.equivFin ι) H *
          Matrix.reindexAlgEquiv ℂ ℂ (Fintype.equivFin ι) (U : Matrix ι ι ℂ) -
        Matrix.reindexAlgEquiv ℂ ℂ (Fintype.equivFin ι) (U : Matrix ι ι ℂ) *
          Matrix.reindexAlgEquiv ℂ ℂ (Fintype.equivFin ι) H = _
    rw [← map_mul, ← map_mul, ← map_sub]
  rw [hmatrix, finiteMatrixHilbertSchmidtEnergy_reindexAlgEquiv,
    finiteMatrixHilbertSchmidtEnergy_eq_hsNorm_sq]
  rfl

/-- A deterministic Hermitian drift plus one Gaussian linear pencil draw. -/
def FiniteGaussianHermitianPencil.affineReindexedHamiltonian
    (P : FiniteGaussianHermitianPencil E ι)
    (H₀ : Matrix ι ι ℂ) (x : E) :
    Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ :=
  Matrix.reindexAlgEquiv ℂ ℂ (Fintype.equivFin ι) (H₀ + P.hamiltonian x)

omit [FiniteDimensional ℝ E] in
theorem FiniteGaussianHermitianPencil.affineReindexedHamiltonian_isHermitian
    (P : FiniteGaussianHermitianPencil E ι)
    {H₀ : Matrix ι ι ℂ} (hH₀ : H₀.IsHermitian) (x : E) :
    (P.affineReindexedHamiltonian H₀ x).IsHermitian := by
  simpa [FiniteGaussianHermitianPencil.affineReindexedHamiltonian,
    Matrix.coe_reindexAlgEquiv] using
    (hH₀.add (P.isHermitian x)).reindex (Fintype.equivFin ι)

/-- Physical endpoint in the eigenbasis of the drifted same draw. -/
def FiniteGaussianHermitianPencil.affineSpectralEndpoint
    (P : FiniteGaussianHermitianPencil E ι)
    {H₀ : Matrix ι ι ℂ} (hH₀ : H₀.IsHermitian) (x : E)
    (U : Matrix.unitaryGroup ι ℂ) :
    Matrix.unitaryGroup (Fin (Fintype.card ι)) ℂ :=
  hermitianSpectralEndpoint
    (P.affineReindexedHamiltonian_isHermitian hH₀ x)
    (finiteGaussianHermitianPencilReindexedEndpoint U)

/-- Spectrum of the deterministic drift plus the same Gaussian draw. -/
def FiniteGaussianHermitianPencil.affineSpectralEnergy
    (P : FiniteGaussianHermitianPencil E ι)
    {H₀ : Matrix ι ι ℂ} (hH₀ : H₀.IsHermitian) (x : E) :
    Fin (Fintype.card ι) → ℝ :=
  (P.affineReindexedHamiltonian_isHermitian hH₀ x).eigenvalues

/-- The affine observer target induced by deterministic Hamiltonian drift. -/
def hermitianPencilCommutatorDrift
    (H₀ : Matrix ι ι ℂ) (U : Matrix.unitaryGroup ι ℂ) :
    EuclideanSpace ℂ (ι × ι) :=
  -matVec (H₀ * (U : Matrix ι ι ℂ) -
    (U : Matrix ι ι ℂ) * H₀)

omit [FiniteDimensional ℝ E] in
/-- Exact affine physical realization of drifted commutator energy. -/
theorem FiniteGaussianHermitianPencil.affineReindexedCommutatorEnergy
    (P : FiniteGaussianHermitianPencil E ι)
    (H₀ : Matrix ι ι ℂ) (x : E)
    (U : Matrix.unitaryGroup ι ℂ) :
    finiteMatrixHilbertSchmidtEnergy
        (P.affineReindexedHamiltonian H₀ x *
            (finiteGaussianHermitianPencilReindexedEndpoint U :
              Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ) -
          (finiteGaussianHermitianPencilReindexedEndpoint U :
              Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ) *
            P.affineReindexedHamiltonian H₀ x) =
      ‖P.commutatorMap U x - hermitianPencilCommutatorDrift H₀ U‖ ^ 2 := by
  rw [FiniteGaussianHermitianPencil.affineReindexedHamiltonian,
    finiteMatrixHilbertSchmidtEnergy_reindexedCommutator]
  have hmatrix :
      (H₀ + P.hamiltonian x) * (U : Matrix ι ι ℂ) -
          (U : Matrix ι ι ℂ) * (H₀ + P.hamiltonian x) =
        (P.hamiltonian x * (U : Matrix ι ι ℂ) -
            (U : Matrix ι ι ℂ) * P.hamiltonian x) +
          (H₀ * (U : Matrix ι ι ℂ) -
            (U : Matrix ι ι ℂ) * H₀) := by
    noncomm_ring
  rw [hmatrix]
  change
    ‖matVec
      ((P.hamiltonian x * (U : Matrix ι ι ℂ) -
          (U : Matrix ι ι ℂ) * P.hamiltonian x) +
        (H₀ * (U : Matrix ι ι ℂ) -
          (U : Matrix ι ι ℂ) * H₀))‖ ^ 2 =
      ‖matVec
          (P.hamiltonian x * (U : Matrix ι ι ℂ) -
            (U : Matrix ι ι ℂ) * P.hamiltonian x) -
        -matVec
          (H₀ * (U : Matrix ι ι ℂ) -
            (U : Matrix ι ι ℂ) * H₀)‖ ^ 2
  rw [sub_neg_eq_add]
  rfl

theorem FiniteGaussianHermitianPencil.mem_affineHalfActivationTube_iff
    (P : FiniteGaussianHermitianPencil E ι) (H₀ : Matrix ι ι ℂ)
    (x : E) (U : Matrix.unitaryGroup ι ℂ) :
    x ∈ gaussianAffineHalfActivationTube
        (n := Module.finrank ℝ E) (P.commutatorMap U)
          (hermitianPencilCommutatorDrift H₀ U) ↔
      ‖P.commutatorMap U x - hermitianPencilCommutatorDrift H₀ U‖ ^ 2 ≤
        P.commutatorActivation U := by
  rfl

/-- **Universal affine same-draw action--carrier law.**  Arbitrary
deterministic Hermitian drift changes only the centres of observer tubes;
the exact stable-rank activation and replica decay are unchanged. -/
theorem FiniteGaussianHermitianPencil.affineNearAction_le_adaptive_add_carrier
    [Nonempty ι]
    (P : FiniteGaussianHermitianPencil E ι)
    {H₀ : Matrix ι ι ℂ} (hH₀ : H₀.IsHermitian) (x : E)
    (U : Matrix.unitaryGroup ι ℂ) (r : ℕ) (δ : ℝ) :
    directStaticChoiTargetNearActionMass
        (choiVector
          (P.affineSpectralEndpoint hH₀ x U :
            Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ))
        (P.affineSpectralEnergy hH₀ x) r δ ≤
      staticChoiAdaptiveReplicaBase (P.affineSpectralEnergy hH₀ x)
          ((Fintype.card ι : ℝ)⁻¹ * P.commutatorActivation U) ^ r +
        if x ∈ gaussianAffineHalfActivationTube
            (n := Module.finrank ℝ E) (P.commutatorMap U)
              (hermitianPencilCommutatorDrift H₀ U)
          then 1 else 0 := by
  have h :=
    directStaticChoiTargetNearActionMass_hermitianSpectralEndpoint_le_adaptivePhysicalAction
      (d := Fintype.card ι) Fintype.card_pos
      (P.affineReindexedHamiltonian_isHermitian hH₀ x)
      (finiteGaussianHermitianPencilReindexedEndpoint U) r δ
      (P.commutatorActivation U)
  rw [P.affineReindexedCommutatorEnergy H₀ x U] at h
  by_cases hc : ‖P.commutatorMap U x - hermitianPencilCommutatorDrift H₀ U‖ ^ 2 ≤
      P.commutatorActivation U
  · rw [if_pos hc] at h
    rw [if_pos]
    · simpa [FiniteGaussianHermitianPencil.affineSpectralEndpoint,
        FiniteGaussianHermitianPencil.affineSpectralEnergy] using h
    · exact (P.mem_affineHalfActivationTube_iff H₀ x U).2 hc
  · rw [if_neg hc] at h
    rw [if_neg]
    · simpa [FiniteGaussianHermitianPencil.affineSpectralEndpoint,
        FiniteGaussianHermitianPencil.affineSpectralEnergy] using h
    · exact fun hx => hc ((P.mem_affineHalfActivationTube_iff H₀ x U).1 hx)

/-- Pointwise probability-design affine action carrier. -/
theorem FiniteGaussianHermitianPencil.weightedAffineNearAction_le_transverse_add_tubeMass
    [Nonempty ι]
    (P : FiniteGaussianHermitianPencil E ι)
    {H₀ : Matrix ι ι ℂ} (hH₀ : H₀.IsHermitian)
    {C : Type*} [Fintype C]
    (U : C → Matrix.unitaryGroup ι ℂ)
    (w : C → ℝ) (hw : w ∈ stdSimplex ℝ C)
    (x : E) (r : ℕ) (δ : ℝ) :
    (∑ c, w c * directStaticChoiTargetNearActionMass
        (choiVector
          (P.affineSpectralEndpoint hH₀ x (U c) :
            Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ))
        (P.affineSpectralEnergy hH₀ x) r δ) ≤
      (∑ c, w c * staticChoiAdaptiveReplicaBase
        (P.affineSpectralEnergy hH₀ x)
        ((Fintype.card ι : ℝ)⁻¹ * P.commutatorActivation (U c)) ^ r) +
      gaussianWeightedAffineHalfActivationTubeMass
        (n := Module.finrank ℝ E) (fun c => P.commutatorMap (U c))
          (fun c => hermitianPencilCommutatorDrift H₀ (U c)) w x := by
  calc
    _ ≤ ∑ c, w c *
        (staticChoiAdaptiveReplicaBase (P.affineSpectralEnergy hH₀ x)
            ((Fintype.card ι : ℝ)⁻¹ * P.commutatorActivation (U c)) ^ r +
          if x ∈ gaussianAffineHalfActivationTube
              (n := Module.finrank ℝ E) (P.commutatorMap (U c))
                (hermitianPencilCommutatorDrift H₀ (U c))
            then 1 else 0) := by
      apply Finset.sum_le_sum
      intro c _
      exact mul_le_mul_of_nonneg_left
        (P.affineNearAction_le_adaptive_add_carrier hH₀ x (U c) r δ)
        (hw.1 c)
    _ = _ := by
      unfold gaussianWeightedAffineHalfActivationTubeMass
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
      congr 1

/-- **Universal quenched affine growing-replica law.**  A deterministic
laboratory-growth centre costs exactly zero in the observer-Jacobian exponent. -/
theorem FiniteGaussianHermitianPencil.stdGaussian_measure_weightedAffineNearAction_gap_le
    [Nonempty ι] [MeasurableSpace E] [BorelSpace E]
    (P : FiniteGaussianHermitianPencil E ι)
    {H₀ : Matrix ι ι ℂ} (hH₀ : H₀.IsHermitian)
    {C : Type*} [Fintype C]
    (U : C → Matrix.unitaryGroup ι ℂ)
    (w : C → ℝ) (hw : w ∈ stdSimplex ℝ C)
    (r : ℕ) (δ : ℝ) {κ : ℝ} (hκ : 0 < κ) :
    (stdGaussian E).real
        {x |
          (∑ c, w c * staticChoiAdaptiveReplicaBase
            (P.affineSpectralEnergy hH₀ x)
            ((Fintype.card ι : ℝ)⁻¹ * P.commutatorActivation (U c)) ^ r) + κ ≤
          ∑ c, w c * directStaticChoiTargetNearActionMass
            (choiVector
              (P.affineSpectralEndpoint hH₀ x (U c) :
                Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ))
            (P.affineSpectralEnergy hH₀ x) r δ} ≤
      (∑ c, w c * Real.exp
        (-(gaussianIntervalActivationMass ^ 2 / 2) *
          (((∑ i : Fin (Module.finrank ℝ E),
              (P.commutatorMap (U c)).singularValues i ^ 2) ^ 2) /
            ∑ i : Fin (Module.finrank ℝ E),
              (P.commutatorMap (U c)).singularValues i ^ 4))) / κ := by
  apply (measureReal_mono ?_).trans
    (stdGaussian_measure_weightedAffineHalfActivationTubeMass_ge_le
      (n := Module.finrank ℝ E) (fun c => P.commutatorMap (U c))
      (fun c => hermitianPencilCommutatorDrift H₀ (U c))
      (by rfl) w hw hκ)
  intro x hx
  have hdet :=
    P.weightedAffineNearAction_le_transverse_add_tubeMass hH₀ U w hw x r δ
  change κ ≤ gaussianWeightedAffineHalfActivationTubeMass
    (n := Module.finrank ℝ E) (fun c => P.commutatorMap (U c))
      (fun c => hermitianPencilCommutatorDrift H₀ (U c)) w x
  change _ + κ ≤ _ at hx
  linarith

/-- **Affine pre-draw optimal-design quenched law.**  Canonical physical
endpoint weights are selected before the random perturbation; an arbitrary
Hermitian growth witness may be used as ensemble centre without changing the
observer stable-rank exponent. -/
theorem FiniteGaussianHermitianPencil.stdGaussian_measure_optimalDesignAffineNearAction_gap_le
    [Nonempty ι] [MeasurableSpace E] [BorelSpace E]
    (P : FiniteGaussianHermitianPencil E ι)
    {H₀ : Matrix ι ι ℂ} (hH₀ : H₀.IsHermitian)
    {C : Type*} [Fintype C] [Nonempty C] [DecidableEq C]
    (r : ℕ) (U : C → Matrix.unitaryGroup ι ℂ)
    (δ : ℝ) {κ : ℝ} (hκ : 0 < κ) :
    (stdGaussian E).real
        {x |
          (∑ c, finiteUnitaryChoiOptimalDesignWeight r U c *
            staticChoiAdaptiveReplicaBase (P.affineSpectralEnergy hH₀ x)
              ((Fintype.card ι : ℝ)⁻¹ * P.commutatorActivation (U c)) ^ r) + κ ≤
          ∑ c, finiteUnitaryChoiOptimalDesignWeight r U c *
            directStaticChoiTargetNearActionMass
              (choiVector
                (P.affineSpectralEndpoint hH₀ x (U c) :
                  Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ))
              (P.affineSpectralEnergy hH₀ x) r δ} ≤
      (∑ c, finiteUnitaryChoiOptimalDesignWeight r U c * Real.exp
        (-(gaussianIntervalActivationMass ^ 2 / 2) *
          (((∑ i : Fin (Module.finrank ℝ E),
              (P.commutatorMap (U c)).singularValues i ^ 2) ^ 2) /
            ∑ i : Fin (Module.finrank ℝ E),
              (P.commutatorMap (U c)).singularValues i ^ 4))) / κ := by
  exact P.stdGaussian_measure_weightedAffineNearAction_gap_le hH₀ U
    (finiteUnitaryChoiOptimalDesignWeight r U)
    (finiteUnitaryChoiOptimalDesignWeight_mem_stdSimplex r U) r δ hκ

end

end RHTower
