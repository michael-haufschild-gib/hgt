import GaloisForLFunctions.RHTower.PairQubitProjectiveSeedSpectralCompatibleFirstReturnLaw

open scoped BigOperators Matrix Matrix.Norms.L2Operator NNReal
open Matrix Set

namespace RHTower

open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw

noncomputable section

/-- Spectral oscillation loses no matrix dimension: it is bounded by twice
the physical operator norm plus one. -/
theorem staticChoiOscillationScale_eigenvalues_le_two_norm_add_one
    {d : ℕ} [Nonempty (Fin d)]
    {H : Matrix (Fin d) (Fin d) ℂ} (hH : H.IsHermitian) :
    staticChoiOscillationScale hH.eigenvalues ≤ 2 * ‖H‖ + 1 := by
  let M : ℝ≥0 := Finset.univ.sup fun i => ‖hH.eigenvalues i‖₊
  have hpoint (i : Fin d) : ‖hH.eigenvalues i‖₊ ≤ ⟨‖H‖, norm_nonneg H⟩ := by
    have hreal : |hH.eigenvalues i| ≤ ‖H‖ := by
      simpa [Real.norm_eq_abs] using spectrum.norm_le_norm_of_mem
        (hH.eigenvalues_mem_spectrum_real i)
    exact_mod_cast hreal
  have hsup : M ≤ ⟨‖H‖, norm_nonneg H⟩ := by
    exact Finset.sup_le fun i _ => hpoint i
  unfold staticChoiOscillationScale
  change 2 * (M : ℝ) + 1 ≤ 2 * ‖H‖ + 1
  gcongr
  exact NNReal.coe_le_coe.mpr hsup

/-- After Hilbert-space normalization, complete two-local Pauli activation
has a dimension-free linear floor in qubit count and projective trace
deficit. -/
theorem normalized_twoLocalPauliCommutatorActivation_ge_traceDeficit
    {n : ℕ}
    (U : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ) :
    2 * gaussianIntervalActivationMass * ((n - 1 : ℕ) : ℝ) *
        unitaryProjectiveTraceDeficit U ≤
      (Fintype.card (FiniteQubitConfiguration (Fin n)) : ℝ)⁻¹ *
        (twoLocalPauliGaussianHermitianPencil n).commutatorActivation U := by
  have hsum :=
    sum_sq_twoLocalPauliUnitaryCommutator_singularValues_ge_traceDeficit U
  have hcard :
      (Fintype.card (FiniteQubitConfiguration (Fin n)) : ℝ) =
        (2 : ℝ) ^ n := by simp
  rw [FiniteGaussianHermitianPencil.commutatorActivation,
    twoLocalPauliGaussianHermitianPencil_commutatorMap,
    show Module.finrank ℝ (TwoLocalPauliCoefficientSpace n) =
      Fintype.card (PauliTracelessLabel n 2) from finrank_euclideanSpace,
    hcard]
  have hpow : 0 < (2 : ℝ) ^ n := by positivity
  have hmass : 0 ≤ gaussianIntervalActivationMass / 2 := by
    positivity [gaussianIntervalActivationMass_pos]
  have hmul := mul_le_mul_of_nonneg_left hsum hmass
  calc
    2 * gaussianIntervalActivationMass * ((n - 1 : ℕ) : ℝ) *
          unitaryProjectiveTraceDeficit U =
        ((2 : ℝ) ^ n)⁻¹ *
          ((gaussianIntervalActivationMass / 2) *
            (4 * ((n - 1 : ℕ) : ℝ) * (2 : ℝ) ^ n *
              unitaryProjectiveTraceDeficit U)) := by
      field_simp
      ring
    _ ≤ ((2 : ℝ) ^ n)⁻¹ *
          ((gaussianIntervalActivationMass / 2) *
            ∑ i : Fin (Fintype.card (PauliTracelessLabel n 2)),
              (twoLocalPauliUnitaryCommutatorMap U).singularValues i ^ 2) := by
      exact mul_le_mul_of_nonneg_left hmul (inv_nonneg.mpr hpow.le)

/-- Any uniform oscillation and activation estimates immediately give a
uniform contraction of the adaptive replica base. -/
theorem staticChoiOscillationAdaptiveReplicaBase_le_of_activation_of_scale
    {d : ℕ} (energy : Fin d → ℝ) {activation a B : ℝ}
    (ha0 : 0 ≤ a) (ha : a ≤ activation)
    (hscale : staticChoiOscillationScale energy ≤ B) (hB : 0 < B) :
    staticChoiOscillationAdaptiveReplicaBase energy activation ≤
      max 0 (1 - a / B ^ 2) := by
  have hspos : 0 < staticChoiOscillationScale energy ^ 2 :=
    sq_pos_of_pos (staticChoiOscillationScale_pos energy)
  have hB0 : 0 ≤ B := hB.le
  have hs0 : 0 ≤ staticChoiOscillationScale energy :=
    (staticChoiOscillationScale_pos energy).le
  have hsq : staticChoiOscillationScale energy ^ 2 ≤ B ^ 2 :=
    (sq_le_sq₀ hs0 hB0).2 hscale
  have hratio : a / B ^ 2 ≤
      activation / staticChoiOscillationScale energy ^ 2 := by
    exact (div_le_div_of_nonneg_left ha0 hspos hsq).trans
      (div_le_div_of_nonneg_right ha hspos.le)
  unfold staticChoiOscillationAdaptiveReplicaBase
  exact max_le_max le_rfl (sub_le_sub_left hratio 1)

theorem inverseSquareMatchingEnergy_le_length
    {L : ℕ} (x : Config (PairQubit L)) :
    inverseSquareMatchingEnergy x ≤ L := by
  unfold inverseSquareMatchingEnergy
  calc
    (∑ j : Fin L, if x (j, false) = true ∧ x (j, true) = true
        then 1 / (((j.val + 1 : ℕ) : ℝ) ^ 2) else 0) ≤
        ∑ _j : Fin L, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro j _
      split_ifs
      · rw [div_le_one (by positivity)]
        have hj : (1 : ℝ) ≤ ((j.val + 1 : ℕ) : ℝ) := by
          exact_mod_cast Nat.succ_le_succ (Nat.zero_le j.val)
        nlinarith
      · norm_num
    _ = L := by simp

theorem inverseSquareChainEnergy_nonneg
    {L : ℕ} (x : Config (PairQubit L)) :
    0 ≤ inverseSquareChainEnergy x := by
  unfold inverseSquareChainEnergy inverseSquareMatchingEnergy
  apply add_nonneg
  · apply Finset.sum_nonneg
    intro j _
    split_ifs <;> positivity
  · exact inverseCubeBridgeEnergy_nonneg x

/-- The inverse-square growth seed has only linear operator norm. -/
theorem norm_inverseSquareChainHamiltonian_le_length_add_one
    {L : ℕ} (hL : 1 ≤ L) :
    ‖inverseSquareChainHamiltonian L‖ ≤ (L : ℝ) + 1 := by
  rw [inverseSquareChainHamiltonian, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (by positivity)).2
  intro x
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (inverseSquareChainEnergy_nonneg x)]
  have hm := inverseSquareMatchingEnergy_le_length x
  have hb := inverseCubeBridgeEnergy_le (lt_of_lt_of_le Nat.zero_lt_one hL) x
  have hb1 : 1 / (L : ℝ) ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]
    norm_num
    exact_mod_cast hL
  unfold inverseSquareChainEnergy
  exact add_le_add hm (hb.trans hb1)

/-- Matrix reindexing cannot increase the physical operator norm. -/
theorem norm_reindexAlgEquiv_le
    {I J : Type*} [Fintype I] [Fintype J]
    [Nonempty I] [Nonempty J]
    [DecidableEq I] [DecidableEq J]
    (e : I ≃ J) (A : Matrix I I ℂ) :
    ‖Matrix.reindexAlgEquiv ℂ ℂ e A‖ ≤ ‖A‖ := by
  let V : EuclideanSpace ℂ I ≃ₗᵢ[ℂ] EuclideanSpace ℂ J :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
  rw [Matrix.l2_opNorm_def, Matrix.l2_opNorm_def]
  change ‖(Matrix.toEuclideanCLM (n := J) (𝕜 := ℂ))
      (Matrix.reindexAlgEquiv ℂ ℂ e A)‖ ≤
    ‖(Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ)) A‖
  apply ((Matrix.toEuclideanCLM (n := J) (𝕜 := ℂ))
    (Matrix.reindexAlgEquiv ℂ ℂ e A)).opNorm_le_bound (norm_nonneg _)
  intro y
  have hyrel :
      (Matrix.toEuclideanCLM (n := J) (𝕜 := ℂ))
          (Matrix.reindexAlgEquiv ℂ ℂ e A) y =
        V ((Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ)) A (V.symm y)) := by
    ext j
    simp [V, Matrix.reindex_apply, Matrix.mulVec, Equiv.piCongrLeft']
    unfold dotProduct
    refine (Fintype.sum_equiv e _ _ fun i => ?_).symm
    simp
  rw [hyrel, V.norm_map]
  calc
    ‖(Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ)) A (V.symm y)‖ ≤
        ‖(Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ)) A‖ * ‖V.symm y‖ :=
      ((Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ)) A).le_opNorm _
    _ = ‖(Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ)) A‖ * ‖y‖ := by
      rw [V.symm.norm_map]

/-- Matrix reindexing is an isometry for the physical operator norm. -/
theorem norm_reindexAlgEquiv_eq
    {I J : Type*} [Fintype I] [Fintype J]
    [Nonempty I] [Nonempty J]
    [DecidableEq I] [DecidableEq J]
    (e : I ≃ J) (A : Matrix I I ℂ) :
    ‖Matrix.reindexAlgEquiv ℂ ℂ e A‖ = ‖A‖ := by
  apply le_antisymm (norm_reindexAlgEquiv_le e A)
  have h := norm_reindexAlgEquiv_le e.symm
    (Matrix.reindexAlgEquiv ℂ ℂ e A)
  simpa using h

theorem norm_projectiveSeedWeakTwoLocalHamiltonian_le
    {L : ℕ} (hL : 1 ≤ L)
    {p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ}
    {rho scale : ℝ}
    (hseed : ‖nearestNeighborPathLocalHamiltonian L p -
        inverseSquareChainHamiltonian L‖ ≤
      rho * nearestNeighborPathLocalGeneratorMass L)
    {x : TwoLocalPauliCoefficientSpace (L * 2)}
    (hx : x ∈ weakTwoLocalPauliCertifiedGrowthSet L) :
    ‖projectiveSeedWeakTwoLocalHamiltonian L p scale x‖ ≤
      (L : ℝ) + 1 + rho * nearestNeighborPathLocalGeneratorMass L +
        |scale| * (18 * ((L * 2 : ℕ) : ℝ) ^ 3) := by
  have hbase : ‖nearestNeighborPathLocalHamiltonian L p‖ ≤
      rho * nearestNeighborPathLocalGeneratorMass L + ((L : ℝ) + 1) := by
    calc
      ‖nearestNeighborPathLocalHamiltonian L p‖ =
          ‖(nearestNeighborPathLocalHamiltonian L p -
              inverseSquareChainHamiltonian L) +
            inverseSquareChainHamiltonian L‖ := by
        congr 1
        abel
      _ ≤ ‖nearestNeighborPathLocalHamiltonian L p -
            inverseSquareChainHamiltonian L‖ +
          ‖inverseSquareChainHamiltonian L‖ := norm_add_le _ _
      _ ≤ rho * nearestNeighborPathLocalGeneratorMass L + ((L : ℝ) + 1) :=
        add_le_add hseed (norm_inverseSquareChainHamiltonian_le_length_add_one hL)
  rw [projectiveSeedWeakTwoLocalHamiltonian]
  calc
    ‖nearestNeighborPathLocalHamiltonian L p +
        (scale : ℂ) • pairQubitReindexedTwoLocalPauliHamiltonian L x‖ ≤
      ‖nearestNeighborPathLocalHamiltonian L p‖ +
        ‖(scale : ℂ) • pairQubitReindexedTwoLocalPauliHamiltonian L x‖ :=
      norm_add_le _ _
    _ ≤ (rho * nearestNeighborPathLocalGeneratorMass L + ((L : ℝ) + 1)) +
        |scale| * (18 * ((L * 2 : ℕ) : ℝ) ^ 3) := by
      apply add_le_add hbase
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
      gcongr
      exact
        norm_pairQubitReindexedTwoLocalPauliHamiltonian_le_eighteen_mul_cube_of_mem_box
          hL hx
    _ = (L : ℝ) + 1 + rho * nearestNeighborPathLocalGeneratorMass L +
        |scale| * (18 * ((L * 2 : ℕ) : ℝ) ^ 3) := by ring

/-- On the certified growth draw, the spectral oscillation scale of the
same Hamiltonian is polynomial rather than Hilbert-dimension sized. -/
theorem pairQubitProjectiveSeedWeakTwoLocalSpectralOscillationScale_le
    {L : ℕ} (hL : 1 ≤ L)
    {p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ}
    {rho scale : ℝ}
    (hseed : ‖nearestNeighborPathLocalHamiltonian L p -
        inverseSquareChainHamiltonian L‖ ≤
      rho * nearestNeighborPathLocalGeneratorMass L)
    {x : TwoLocalPauliCoefficientSpace (L * 2)}
    (hx : x ∈ weakTwoLocalPauliCertifiedGrowthSet L) :
    staticChoiOscillationScale
        (pairQubitProjectiveSeedWeakTwoLocalSpectralEnergy L p scale x) ≤
      2 * ((L : ℝ) + 1 + rho * nearestNeighborPathLocalGeneratorMass L +
        |scale| * (18 * ((L * 2 : ℕ) : ℝ) ^ 3)) + 1 := by
  let P := twoLocalPauliGaussianHermitianPencil (L * 2)
  let H₀ := pairQubitProjectivePauliSeed L p
  let H := P.affineReindexedHamiltonian H₀ (scale • x)
  let hH : H.IsHermitian :=
    P.affineReindexedHamiltonian_isHermitian
      (pairQubitProjectivePauliSeed_isHermitian L p) (scale • x)
  have hspectral :=
    staticChoiOscillationScale_eigenvalues_le_two_norm_add_one hH
  have hmatrix : H₀ + P.hamiltonian (scale • x) =
      Matrix.reindexAlgEquiv ℂ ℂ (pairQubitPathConfigurationEquiv L)
        (projectiveSeedWeakTwoLocalHamiltonian L p scale x) := by
    simpa [P, H₀, twoLocalPauliGaussianHermitianPencil_hamiltonian,
      realActivePauliHamiltonian_smul] using
        pairQubitProjectiveSeed_reindexedHamiltonian_eq_physical
          L p scale x
  have hnorm : ‖H‖ ≤
      (L : ℝ) + 1 + rho * nearestNeighborPathLocalGeneratorMass L +
        |scale| * (18 * ((L * 2 : ℕ) : ℝ) ^ 3) := by
    change ‖P.affineReindexedHamiltonian H₀ (scale • x)‖ ≤ _
    rw [FiniteGaussianHermitianPencil.affineReindexedHamiltonian,
      hmatrix, norm_reindexAlgEquiv_eq, norm_reindexAlgEquiv_eq]
    exact norm_projectiveSeedWeakTwoLocalHamiltonian_le hL hseed hx
  change staticChoiOscillationScale hH.eigenvalues ≤ _
  exact hspectral.trans (by gcongr)

/-- Every circuit endpoint with projective deficit at least `eta` has the
same explicit replica contraction on the certified growth draw. -/
theorem pairQubitProjectiveSeedWeakTwoLocalOscillationAdaptiveReplicaBase_pow_le
    {L : ℕ} (hL : 1 ≤ L)
    {p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ}
    {rho scale : ℝ}
    (hseed : ‖nearestNeighborPathLocalHamiltonian L p -
        inverseSquareChainHamiltonian L‖ ≤
      rho * nearestNeighborPathLocalGeneratorMass L)
    {x : TwoLocalPauliCoefficientSpace (L * 2)}
    (hx : x ∈ weakTwoLocalPauliCertifiedGrowthSet L)
    {eta : ℝ} (heta0 : 0 ≤ eta)
    (U : Matrix.unitaryGroup (Config (PairQubit L)) ℂ)
    (heta : eta ≤ pairQubitUnitaryProjectiveTraceDeficit U)
    (r : ℕ) :
    staticChoiOscillationAdaptiveReplicaBase
        (pairQubitProjectiveSeedWeakTwoLocalSpectralEnergy L p scale x)
        ((Fintype.card
            (FiniteQubitConfiguration (Fin (L * 2))) : ℝ)⁻¹ *
          (scale ^ 2 *
            (twoLocalPauliGaussianHermitianPencil
              (L * 2)).commutatorActivation
                (pairQubitPathUnitaryReindex L U))) ^ r ≤
      (max 0 (1 -
        (scale ^ 2 *
          (2 * gaussianIntervalActivationMass *
            (((L * 2 - 1 : ℕ) : ℝ)) * eta)) /
          (2 * ((L : ℝ) + 1 +
            rho * nearestNeighborPathLocalGeneratorMass L +
            |scale| * (18 * ((L * 2 : ℕ) : ℝ) ^ 3)) + 1) ^ 2)) ^ r := by
  let energy :=
    pairQubitProjectiveSeedWeakTwoLocalSpectralEnergy L p scale x
  let activation :=
    (Fintype.card
        (FiniteQubitConfiguration (Fin (L * 2))) : ℝ)⁻¹ *
      (scale ^ 2 *
        (twoLocalPauliGaussianHermitianPencil
          (L * 2)).commutatorActivation
            (pairQubitPathUnitaryReindex L U))
  let a := scale ^ 2 *
    (2 * gaussianIntervalActivationMass *
      (((L * 2 - 1 : ℕ) : ℝ)) * eta)
  let B := 2 * ((L : ℝ) + 1 +
    rho * nearestNeighborPathLocalGeneratorMass L +
    |scale| * (18 * ((L * 2 : ℕ) : ℝ) ^ 3)) + 1
  have hcoef0 : 0 ≤ 2 * gaussianIntervalActivationMass *
      (((L * 2 - 1 : ℕ) : ℝ)) := by
    exact mul_nonneg
      (mul_nonneg (by norm_num) gaussianIntervalActivationMass_pos.le)
      (Nat.cast_nonneg _)
  have hnormalized :=
    normalized_twoLocalPauliCommutatorActivation_ge_traceDeficit
      (pairQubitPathUnitaryReindex L U)
  have hactivationBase :
      2 * gaussianIntervalActivationMass *
          (((L * 2 - 1 : ℕ) : ℝ)) * eta ≤
        (Fintype.card
            (FiniteQubitConfiguration (Fin (L * 2))) : ℝ)⁻¹ *
          (twoLocalPauliGaussianHermitianPencil
            (L * 2)).commutatorActivation
              (pairQubitPathUnitaryReindex L U) := by
    calc
      2 * gaussianIntervalActivationMass *
          (((L * 2 - 1 : ℕ) : ℝ)) * eta ≤
        2 * gaussianIntervalActivationMass *
          (((L * 2 - 1 : ℕ) : ℝ)) *
            unitaryProjectiveTraceDeficit
              (pairQubitPathUnitaryReindex L U) := by
        apply mul_le_mul_of_nonneg_left _ hcoef0
        simpa [pairQubitUnitaryProjectiveTraceDeficit] using heta
      _ ≤ _ := hnormalized
  have ha : a ≤ activation := by
    dsimp [a, activation]
    have hmul := mul_le_mul_of_nonneg_left hactivationBase (sq_nonneg scale)
    nlinarith
  have ha0 : 0 ≤ a := by
    dsimp [a]
    apply mul_nonneg (sq_nonneg scale)
    exact mul_nonneg hcoef0 heta0
  have hscale : staticChoiOscillationScale energy ≤ B := by
    exact pairQubitProjectiveSeedWeakTwoLocalSpectralOscillationScale_le
      hL hseed hx
  have hB : 0 < B :=
    lt_of_lt_of_le (staticChoiOscillationScale_pos energy) hscale
  have hbase :=
    staticChoiOscillationAdaptiveReplicaBase_le_of_activation_of_scale
      energy ha0 ha hscale hB
  have hbase0 : 0 ≤
      staticChoiOscillationAdaptiveReplicaBase energy activation := by
    unfold staticChoiOscillationAdaptiveReplicaBase
    exact le_max_left _ _
  exact pow_le_pow_left₀ hbase0 hbase r

/-- Determinant-optimal pre-draw weights turn the entire circuit image into
one endpoint-count-free explicit replica contraction. -/
theorem pairQubitSpectralCompatibleOptimalDesignWeight_sum_oscillationBase_pow_le
    {L : ℕ} (hL : 1 ≤ L)
    {p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ}
    {rho scale : ℝ}
    (hseed : ‖nearestNeighborPathLocalHamiltonian L p -
        inverseSquareChainHamiltonian L‖ ≤
      rho * nearestNeighborPathLocalGeneratorMass L)
    {x : TwoLocalPauliCoefficientSpace (L * 2)}
    (hx : x ∈ weakTwoLocalPauliCertifiedGrowthSet L)
    {C : Type*} [Fintype C] [Nonempty C] [DecidableEq C]
    (r : ℕ) (U : C → Matrix.unitaryGroup (Config (PairQubit L)) ℂ)
    {eta : ℝ} (heta0 : 0 ≤ eta)
    (heta : ∀ c, eta ≤ pairQubitUnitaryProjectiveTraceDeficit (U c)) :
    (∑ c, pairQubitSpectralCompatibleOptimalDesignWeight r U c *
      staticChoiOscillationAdaptiveReplicaBase
        (pairQubitProjectiveSeedWeakTwoLocalSpectralEnergy L p scale x)
        ((Fintype.card
            (FiniteQubitConfiguration (Fin (L * 2))) : ℝ)⁻¹ *
          (scale ^ 2 *
            (twoLocalPauliGaussianHermitianPencil
              (L * 2)).commutatorActivation
                (pairQubitPathUnitaryReindex L (U c)))) ^ r) ≤
      (max 0 (1 -
        (scale ^ 2 *
          (2 * gaussianIntervalActivationMass *
            (((L * 2 - 1 : ℕ) : ℝ)) * eta)) /
          (2 * ((L : ℝ) + 1 +
            rho * nearestNeighborPathLocalGeneratorMass L +
            |scale| * (18 * ((L * 2 : ℕ) : ℝ) ^ 3)) + 1) ^ 2)) ^ r := by
  let w := pairQubitSpectralCompatibleOptimalDesignWeight r U
  let q := max 0 (1 -
    (scale ^ 2 *
      (2 * gaussianIntervalActivationMass *
        (((L * 2 - 1 : ℕ) : ℝ)) * eta)) /
      (2 * ((L : ℝ) + 1 +
        rho * nearestNeighborPathLocalGeneratorMass L +
        |scale| * (18 * ((L * 2 : ℕ) : ℝ) ^ 3)) + 1) ^ 2)
  have hw : w ∈ stdSimplex ℝ C :=
    pairQubitSpectralCompatibleOptimalDesignWeight_mem_stdSimplex r U
  calc
    (∑ c, w c *
      staticChoiOscillationAdaptiveReplicaBase
        (pairQubitProjectiveSeedWeakTwoLocalSpectralEnergy L p scale x)
        ((Fintype.card
            (FiniteQubitConfiguration (Fin (L * 2))) : ℝ)⁻¹ *
          (scale ^ 2 *
            (twoLocalPauliGaussianHermitianPencil
              (L * 2)).commutatorActivation
                (pairQubitPathUnitaryReindex L (U c)))) ^ r) ≤
        ∑ c, w c * q ^ r := by
      apply Finset.sum_le_sum
      intro c _
      apply mul_le_mul_of_nonneg_left _ (hw.1 c)
      exact
        pairQubitProjectiveSeedWeakTwoLocalOscillationAdaptiveReplicaBase_pow_le
          hL hseed hx heta0 (U c) (heta c) r
    _ = q ^ r := by
      rw [← Finset.sum_mul, hw.2, one_mul]

/-- Explicit first-return compiler: the complete finite circuit image is
excluded once occupied replica rank, the Haar factorial floor, the uniform
oscillation contraction, and the far-time Gaussian tail fit one budget. -/
theorem no_forward_pairQubitProjectiveSeedWeakTwoLocalCircuitReturn_of_explicitOscillationBudget
    {L : ℕ} (hL : 1 ≤ L)
    {p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ}
    {rho scale : ℝ}
    (hseed : ‖nearestNeighborPathLocalHamiltonian L p -
        inverseSquareChainHamiltonian L‖ ≤
      rho * nearestNeighborPathLocalGeneratorMass L)
    {x : TwoLocalPauliCoefficientSpace (L * 2)}
    (hx : x ∈ weakTwoLocalPauliCertifiedGrowthSet L)
    {C : Type*} [Fintype C] [Nonempty C] [DecidableEq C]
    {r : ℕ} (U : C → Matrix.unitaryGroup (Config (PairQubit L)) ℂ)
    {eta : ℝ} (heta0 : 0 ≤ eta)
    (heta : ∀ c, eta ≤ pairQubitUnitaryProjectiveTraceDeficit (U c))
    {delta kappa : ℝ}
    (hmax : MaximallyProjectiveEnergy
      (pairQubitProjectiveSeedWeakTwoLocalSpectralEnergy L p scale x))
    (hxgap : x ∉ pairQubitSpectralCompatibleOscillationNearActionGapEvent
      p scale r U delta kappa)
    {T epsn epsw : ℝ}
    (hTpos : 0 < T) (hdelta : 0 < delta)
    (hepsn : 0 ≤ epsn) (hgap : epsn < epsw)
    (hepswOne : epsw < 1)
    (hT : epsw /
        staticChoiSpeed
          (pairQubitProjectiveSeedWeakTwoLocalSpectralEnergy L p scale x) ≤ T)
    (hbudget :
      (Module.finrank ℂ
          (replicaTargetSpan r (fun c =>
            (pairQubitProjectiveSeedWeakTwoLocalSpectralChoiTarget
              p scale x U c).ofLp)) : ℝ) *
        ((r.factorial : ℝ) *
            (Fintype.card
              (FiniteQubitConfiguration (Fin (L * 2))) : ℝ)⁻¹ ^ r +
          (max 0 (1 -
            (scale ^ 2 *
              (2 * gaussianIntervalActivationMass *
                (((L * 2 - 1 : ℕ) : ℝ)) * eta)) /
              (2 * ((L : ℝ) + 1 +
                rho * nearestNeighborPathLocalGeneratorMass L +
                |scale| * (18 * ((L * 2 : ℕ) : ℝ) ^ 3)) + 1) ^ 2)) ^ r +
          kappa + Real.exp (-((T * delta) ^ 2) / 2)) <
        gaussianFloorTwo *
          ((epsw - epsn) /
              staticChoiSpeed
                (pairQubitProjectiveSeedWeakTwoLocalSpectralEnergy
                  L p scale x) / (2 * T)) *
          (1 - epsw ^ 2) ^ r) :
    ¬ ∃ t ∈ Icc
        (epsw /
            staticChoiSpeed
              (pairQubitProjectiveSeedWeakTwoLocalSpectralEnergy L p scale x) +
          (epsw - epsn) /
            staticChoiSpeed
              (pairQubitProjectiveSeedWeakTwoLocalSpectralEnergy L p scale x)) T,
      ∃ c, pureStateTraceDistance
        (staticSpectralChoiVector
          (Fintype.card (FiniteQubitConfiguration (Fin (L * 2)))) t
          (pairQubitProjectiveSeedWeakTwoLocalSpectralEnergy L p scale x))
        (pairQubitProjectiveSeedWeakTwoLocalSpectralChoiTarget
          p scale x U c) ≤ epsn := by
  have hweighted :=
    pairQubitSpectralCompatibleOptimalDesignWeight_sum_oscillationBase_pow_le
      (rho := rho) (scale := scale) hL hseed hx r U heta0 heta
  apply
    no_forward_pairQubitProjectiveSeedWeakTwoLocalCircuitReturn_of_not_spectralCompatibleGap
      U hmax hxgap hTpos hdelta hepsn hgap hepswOne hT
  apply lt_of_le_of_lt _ hbudget
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  gcongr

end

end RHTower
