import GaloisForLFunctions.RHTower.StaticChoiCentralizerCarrierReplicaLaw
import GaloisForLFunctions.RHTower.StaticChoiOscillationActionCarrierLaw
import GaloisForLFunctions.RHTower.StaticChoiReturnShellCoareaIncidenceLaw
import GaloisForLFunctions.RHTower.StaticChoiKrylovCarrierDichotomyLaw
import GaloisForLFunctions.HTGeometry.ChoiShortcutEnergyDefectKurtosisLaw
import GaloisForLFunctions.HTGeometry.GaussianStableRankDeterminantLaw
import GaloisForLFunctions.RHTower.GaussianScaledAffineHermitianPencilSpectralActionLaw
import GaloisForLFunctions.RHTower.GaussianGrowingReplicaPseudodeterminantLaw

open scoped BigOperators ComplexConjugate Matrix.Norms.L2Operator
open Set Matrix

namespace RHTower

open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw

noncomputable section

theorem directStaticChoiCentralizerMass_le_norm
    {d : ℕ} (hd : 0 < d)
    (target : EuclideanSpace ℂ (Fin d × Fin d)) :
    directStaticChoiCentralizerMass target ≤ ‖target‖ := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hsqrtPos : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.2 hdR
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt
    (Finset.univ : Finset (Fin d)) (fun _ => (1 : ℝ))
      (fun i => ‖target (i, i)‖)
  simp only [one_mul, one_pow, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hcs
  have hdiagSq :
      Real.sqrt (∑ i : Fin d, ‖target (i, i)‖ ^ (2 : ℕ)) =
        ‖directStaticChoiTargetDiagonal target‖ := by
    rw [← Real.sqrt_sq (norm_nonneg (directStaticChoiTargetDiagonal target))]
    congr 1
    rw [EuclideanSpace.norm_sq_eq]
    rfl
  unfold directStaticChoiCentralizerMass directStaticChoiTargetWeight
  rw [← Finset.mul_sum]
  calc
    (Real.sqrt (d : ℝ))⁻¹ * ∑ i : Fin d, ‖target (i, i)‖ ≤
        (Real.sqrt (d : ℝ))⁻¹ *
          (Real.sqrt (d : ℝ) *
            Real.sqrt (∑ i : Fin d, ‖target (i, i)‖ ^ (2 : ℕ))) :=
      mul_le_mul_of_nonneg_left hcs (inv_nonneg.mpr hsqrtPos.le)
    _ = Real.sqrt (∑ i : Fin d, ‖target (i, i)‖ ^ (2 : ℕ)) := by
      rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hsqrtPos), one_mul]
    _ = ‖directStaticChoiTargetDiagonal target‖ := hdiagSq
    _ ≤ ‖target‖ := norm_directStaticChoiTargetDiagonal_le target

theorem directStaticChoiTargetNearActionMass_nonneg
    {d : ℕ} (target : EuclideanSpace ℂ (Fin d × Fin d))
    (energy : Fin d → ℝ) (r : ℕ) (δ : ℝ) :
    0 ≤ directStaticChoiTargetNearActionMass target energy r δ := by
  unfold directStaticChoiTargetNearActionMass
  rw [fidelityReplicaNearActionMass_eq_finset]
  apply Finset.sum_nonneg
  intro p _
  apply Finset.sum_nonneg
  intro q _
  split_ifs
  · exact fidelityReplicaMultiplicityWeight_nonneg
      (directStaticChoiTargetWeight_nonneg target) p q
  · exact le_rfl

theorem directStaticChoiCentralizerMass_sq_le_diagonalMass
    {d : ℕ} (hd : 0 < d)
    (target : EuclideanSpace ℂ (Fin d × Fin d)) :
    directStaticChoiCentralizerMass target ^ (2 : ℕ) ≤
      ∑ i : Fin d, ‖target (i, i)‖ ^ (2 : ℕ) := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hsqrtPos : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.2 hdR
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt
    (Finset.univ : Finset (Fin d)) (fun _ => (1 : ℝ))
      (fun i => ‖target (i, i)‖)
  simp only [one_mul, one_pow, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hcs
  have hmass : directStaticChoiCentralizerMass target ≤
      Real.sqrt (∑ i : Fin d, ‖target (i, i)‖ ^ (2 : ℕ)) := by
    unfold directStaticChoiCentralizerMass directStaticChoiTargetWeight
    rw [← Finset.mul_sum]
    calc
      (Real.sqrt (d : ℝ))⁻¹ * ∑ i : Fin d, ‖target (i, i)‖ ≤
          (Real.sqrt (d : ℝ))⁻¹ *
            (Real.sqrt (d : ℝ) *
              Real.sqrt (∑ i : Fin d, ‖target (i, i)‖ ^ (2 : ℕ))) :=
        mul_le_mul_of_nonneg_left hcs (inv_nonneg.mpr hsqrtPos.le)
      _ = Real.sqrt (∑ i : Fin d, ‖target (i, i)‖ ^ (2 : ℕ)) := by
        rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hsqrtPos), one_mul]
  have hsum0 : 0 ≤ ∑ i : Fin d, ‖target (i, i)‖ ^ (2 : ℕ) :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hsquare := pow_le_pow_left₀
    (directStaticChoiCentralizerMass_nonneg target) hmass 2
  simpa [Real.sq_sqrt hsum0] using hsquare

theorem diagonalMass_add_offDiagonalMass_eq_norm_sq
    {d : ℕ} (target : EuclideanSpace ℂ (Fin d × Fin d)) :
    (∑ i : Fin d, ‖target (i, i)‖ ^ (2 : ℕ)) +
        ∑ i : Fin d, ∑ j : Fin d,
          (if i = j then 0 else ‖target (i, j)‖ ^ (2 : ℕ)) =
      ‖target‖ ^ (2 : ℕ) := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [show ‖target (i, i)‖ ^ (2 : ℕ) =
      ∑ j : Fin d, if i = j then ‖target (i, j)‖ ^ (2 : ℕ) else 0 by simp]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij]

theorem offDiagonalMass_staticChoiAnchorResidual_choiVector_eq
    {d : ℕ} (hd : 0 < d) (energy : Fin d → ℝ) (anchor : ℝ)
    (W : Matrix (Fin d) (Fin d) ℂ) :
    (∑ i : Fin d, ∑ j : Fin d,
        (if i = j then 0 else
          ‖staticChoiAnchorResidual energy anchor
            (GaloisForLFunctions.RHTower.choiVector W) (i, j)‖ ^ (2 : ℕ))) =
      normalizedSpectralOffDiagonalMass W := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hsqrt : Real.sqrt (d : ℝ) ^ (2 : ℕ) = d := Real.sq_sqrt hdR.le
  have hsqrtNe : Real.sqrt (d : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr hdR
  unfold normalizedSpectralOffDiagonalMass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i = j
  · simp [hij]
  · simp only [hij, ↓reduceIte]
    have horbit : staticSpectralChoiVector d anchor energy (i, j) = 0 := by
      simp [staticSpectralChoiVector, fullUniformPhaseChoiVector_apply, hij]
    rw [staticChoiAnchorResidual]
    simp only [PiLp.sub_apply, PiLp.smul_apply, horbit, smul_zero, sub_zero]
    unfold GaloisForLFunctions.RHTower.choiVector
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    field_simp [hsqrtNe]
    simp only [Fintype.card_fin]
    rw [hsqrt]

/-- Return overlap and observer action are additive defects before replica
amplification.  This removes one common recurrence sector once, while every
surviving active target pays its normalized commutator energy. -/
theorem directStaticChoiTargetNearActionMass_anchorResidual_choiVector_le_jointDefect
    {d : ℕ} (hd : 0 < d) (energy : Fin d → ℝ) (anchor : ℝ)
    {W : Matrix (Fin d) (Fin d) ℂ}
    (hW : W ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (r : ℕ) (δ : ℝ) :
    directStaticChoiTargetNearActionMass
        (staticChoiAnchorResidual energy anchor
          (GaloisForLFunctions.RHTower.choiVector W)) energy r δ ≤
      (1 - ‖staticChoiAnchorComponent energy anchor
          (GaloisForLFunctions.RHTower.choiVector W)‖ ^ (2 : ℕ) -
        normalizedSpectralCommutatorEnergy energy W /
          staticChoiOscillationScale energy ^ (2 : ℕ)) ^ r := by
  let target : EuclideanSpace ℂ (Fin d × Fin d) :=
    GaloisForLFunctions.RHTower.choiVector W
  let residual := staticChoiAnchorResidual energy anchor target
  have htarget : ‖target‖ = 1 := by
    apply GaloisForLFunctions.RHTower.norm_choiVector_eq_one
      (by simpa using hd)
    simpa [target, Matrix.star_eq_conjTranspose] using
      (Matrix.mem_unitaryGroup_iff'.mp hW)
  have hnormResidual : ‖residual‖ ^ (2 : ℕ) =
      1 - ‖staticChoiAnchorComponent energy anchor target‖ ^ (2 : ℕ) := by
    exact norm_sq_staticChoiAnchorResidual_eq_one_sub_norm_sq_component
      hd energy anchor htarget
  have hsplit := diagonalMass_add_offDiagonalMass_eq_norm_sq residual
  have hoff :
      (∑ i : Fin d, ∑ j : Fin d,
        (if i = j then 0 else ‖residual (i, j)‖ ^ (2 : ℕ))) =
        normalizedSpectralOffDiagonalMass W := by
    simpa [residual, target] using
      offDiagonalMass_staticChoiAnchorResidual_choiVector_eq
        hd energy anchor W
  rw [hoff, hnormResidual] at hsplit
  have hdiag :
      (∑ i : Fin d, ‖residual (i, i)‖ ^ (2 : ℕ)) =
        1 - ‖staticChoiAnchorComponent energy anchor target‖ ^ (2 : ℕ) -
          normalizedSpectralOffDiagonalMass W := by
    linarith
  have hscale : 0 < staticChoiOscillationScale energy ^ (2 : ℕ) :=
    sq_pos_of_pos (staticChoiOscillationScale_pos energy)
  have hcomm :=
    normalizedSpectralCommutatorEnergy_le_oscillation_sq_mul_offDiagonal
      energy W
  have hratio : normalizedSpectralCommutatorEnergy energy W /
      staticChoiOscillationScale energy ^ (2 : ℕ) ≤
        normalizedSpectralOffDiagonalMass W := by
    exact (div_le_iff₀ hscale).2 (by simpa [mul_comm] using hcomm)
  have hmassSq := directStaticChoiCentralizerMass_sq_le_diagonalMass
    hd residual
  rw [hdiag] at hmassSq
  have hbase : directStaticChoiCentralizerMass residual ^ (2 : ℕ) ≤
      1 - ‖staticChoiAnchorComponent energy anchor target‖ ^ (2 : ℕ) -
        normalizedSpectralCommutatorEnergy energy W /
          staticChoiOscillationScale energy ^ (2 : ℕ) := by
    linarith
  calc
    directStaticChoiTargetNearActionMass residual energy r δ ≤
        directStaticChoiCentralizerMass residual ^ (2 * r) :=
      directStaticChoiTargetNearActionMass_le_centralizerMass_pow
        residual energy r δ
    _ = (directStaticChoiCentralizerMass residual ^ (2 : ℕ)) ^ r := by
      rw [pow_mul]
    _ ≤ (1 - ‖staticChoiAnchorComponent energy anchor target‖ ^ (2 : ℕ) -
          normalizedSpectralCommutatorEnergy energy W /
            staticChoiOscillationScale energy ^ (2 : ℕ)) ^ r :=
      pow_le_pow_left₀ (sq_nonneg _) hbase r

theorem returnObserverJointDefect_nonneg
    {d : ℕ} (hd : 0 < d) (energy : Fin d → ℝ) (anchor : ℝ)
    {W : Matrix (Fin d) (Fin d) ℂ}
    (hW : W ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    0 ≤ 1 - ‖staticChoiAnchorComponent energy anchor
        (GaloisForLFunctions.RHTower.choiVector W)‖ ^ (2 : ℕ) -
      normalizedSpectralCommutatorEnergy energy W /
        staticChoiOscillationScale energy ^ (2 : ℕ) := by
  have h :=
    directStaticChoiTargetNearActionMass_anchorResidual_choiVector_le_jointDefect
      hd energy anchor hW 1 0
  have hnonneg := directStaticChoiTargetNearActionMass_nonneg
    (staticChoiAnchorResidual energy anchor
      (GaloisForLFunctions.RHTower.choiVector W)) energy 1 0
  simpa using hnonneg.trans h

theorem directStaticChoiTargetNearActionMass_anchorResidual_choiVector_le_exp_jointDefect
    {d : ℕ} (hd : 0 < d) (energy : Fin d → ℝ) (anchor : ℝ)
    {W : Matrix (Fin d) (Fin d) ℂ}
    (hW : W ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (r : ℕ) (δ : ℝ) :
    directStaticChoiTargetNearActionMass
        (staticChoiAnchorResidual energy anchor
          (GaloisForLFunctions.RHTower.choiVector W)) energy r δ ≤
      Real.exp (-(r : ℝ) *
        (‖staticChoiAnchorComponent energy anchor
            (GaloisForLFunctions.RHTower.choiVector W)‖ ^ (2 : ℕ) +
          normalizedSpectralCommutatorEnergy energy W /
            staticChoiOscillationScale energy ^ (2 : ℕ))) := by
  let q := ‖staticChoiAnchorComponent energy anchor
      (GaloisForLFunctions.RHTower.choiVector W)‖ ^ (2 : ℕ) +
    normalizedSpectralCommutatorEnergy energy W /
      staticChoiOscillationScale energy ^ (2 : ℕ)
  have hbase : 0 ≤ 1 - q := by
    simpa [q, sub_sub] using
      returnObserverJointDefect_nonneg hd energy anchor hW
  have hpower :=
    directStaticChoiTargetNearActionMass_anchorResidual_choiVector_le_jointDefect
      hd energy anchor hW r δ
  have hexpBase : 1 - q ≤ Real.exp (-q) := by
    linarith [Real.add_one_le_exp (-q)]
  calc
    directStaticChoiTargetNearActionMass
        (staticChoiAnchorResidual energy anchor
          (GaloisForLFunctions.RHTower.choiVector W)) energy r δ ≤
      (1 - q) ^ r := by simpa [q, sub_sub] using hpower
    _ ≤ Real.exp (-q) ^ r := pow_le_pow_left₀ hbase hexpBase r
    _ = Real.exp (-(r : ℝ) * q) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ = _ := by rfl

theorem choiVector_one_eq_staticSpectralChoiVector_zero_general
    {d : ℕ} (_hd : 0 < d) (energy : Fin d → ℝ) :
    GaloisForLFunctions.RHTower.choiVector
        (1 : Matrix (Fin d) (Fin d) ℂ) =
      staticSpectralChoiVector d 0 energy := by
  ext ij
  rw [staticSpectralChoiVector, fullUniformPhaseChoiVector_apply]
  rw [fourier_finiteHamiltonianAddCirclePhase]
  simp [GaloisForLFunctions.RHTower.choiVector,
    finiteObserverHamiltonianVertexPhase, Matrix.one_apply]
  split <;> ring

theorem staticChoiAnchorComponent_zero_choiVector_eq_normalizedTrace
    {d : ℕ} (hd : 0 < d) (energy : Fin d → ℝ)
    (W : Matrix (Fin d) (Fin d) ℂ) :
    staticChoiAnchorComponent energy 0
        (GaloisForLFunctions.RHTower.choiVector W) =
      Matrix.trace W / (d : ℂ) := by
  unfold staticChoiAnchorComponent
  rw [← choiVector_one_eq_staticSpectralChoiVector_zero_general hd energy]
  rw [GaloisForLFunctions.RHTower.inner_choiVector (by simpa using hd)]
  simp

theorem norm_staticChoiAnchorComponent_zero_hermitianSpectralEndpoint
    {d : ℕ} (hd : 0 < d)
    {H : Matrix (Fin d) (Fin d) ℂ} (hH : H.IsHermitian)
    (U : Matrix.unitaryGroup (Fin d) ℂ) :
    ‖staticChoiAnchorComponent hH.eigenvalues 0
        (GaloisForLFunctions.RHTower.choiVector
          (hermitianSpectralEndpoint hH U : Matrix (Fin d) (Fin d) ℂ))‖ =
      ‖Matrix.trace (U : Matrix (Fin d) (Fin d) ℂ)‖ / d := by
  rw [staticChoiAnchorComponent_zero_choiVector_eq_normalizedTrace hd]
  change ‖Matrix.trace
      (star (hH.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) *
        (U : Matrix (Fin d) (Fin d) ℂ) *
          (hH.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)) / (d : ℂ)‖ = _
  rw [GaloisForLFunctions.HTGeometry.trace_unitaryConjugate]
  rw [norm_div, Complex.norm_natCast]

theorem directStaticChoiTargetNearActionMass_zeroAnchorResidual_hermitianSpectralEndpoint_le_jointDefect
    {d : ℕ} (hd : 0 < d)
    {H : Matrix (Fin d) (Fin d) ℂ} (hH : H.IsHermitian)
    (U : Matrix.unitaryGroup (Fin d) ℂ)
    (r : ℕ) (δ : ℝ) :
    directStaticChoiTargetNearActionMass
        (staticChoiAnchorResidual hH.eigenvalues 0
          (GaloisForLFunctions.RHTower.choiVector
            (hermitianSpectralEndpoint hH U :
              Matrix (Fin d) (Fin d) ℂ))) hH.eigenvalues r δ ≤
      (1 - (‖Matrix.trace (U : Matrix (Fin d) (Fin d) ℂ)‖ / d) ^ (2 : ℕ) -
        ((d : ℝ)⁻¹ * finiteMatrixHilbertSchmidtEnergy
          (H * (U : Matrix (Fin d) (Fin d) ℂ) -
            (U : Matrix (Fin d) (Fin d) ℂ) * H)) /
          staticChoiOscillationScale hH.eigenvalues ^ (2 : ℕ)) ^ r := by
  have h :=
    directStaticChoiTargetNearActionMass_anchorResidual_choiVector_le_jointDefect
      hd hH.eigenvalues 0 (hermitianSpectralEndpoint hH U).2 r δ
  rw [norm_staticChoiAnchorComponent_zero_hermitianSpectralEndpoint hd hH U,
    normalizedSpectralCommutatorEnergy_hermitianSpectralEndpoint hd hH U] at h
  exact h

theorem directStaticChoiTargetNearActionMass_zeroAnchorResidual_hermitianSpectralEndpoint_le_exp_trace_mul_action_of_scale
    {d : ℕ} (hd : 0 < d)
    {H : Matrix (Fin d) (Fin d) ℂ} (hH : H.IsHermitian)
    (U : Matrix.unitaryGroup (Fin d) ℂ)
    (r : ℕ) (δ B : ℝ)
    (hscale : staticChoiOscillationScale hH.eigenvalues ≤ B)
    (hB : 0 < B) :
    directStaticChoiTargetNearActionMass
        (staticChoiAnchorResidual hH.eigenvalues 0
          (GaloisForLFunctions.RHTower.choiVector
            (hermitianSpectralEndpoint hH U :
              Matrix (Fin d) (Fin d) ℂ))) hH.eigenvalues r δ ≤
      Real.exp (-(r : ℝ) *
          (‖Matrix.trace (U : Matrix (Fin d) (Fin d) ℂ)‖ / d) ^ (2 : ℕ)) *
        Real.exp (-(((r : ℝ) * (d : ℝ)⁻¹ / B ^ (2 : ℕ)) *
          finiteMatrixHilbertSchmidtEnergy
            (H * (U : Matrix (Fin d) (Fin d) ℂ) -
              (U : Matrix (Fin d) (Fin d) ℂ) * H))) := by
  have hraw :=
    directStaticChoiTargetNearActionMass_anchorResidual_choiVector_le_exp_jointDefect
      hd hH.eigenvalues 0 (hermitianSpectralEndpoint hH U).2 r δ
  rw [norm_staticChoiAnchorComponent_zero_hermitianSpectralEndpoint hd hH U,
    normalizedSpectralCommutatorEnergy_hermitianSpectralEndpoint hd hH U] at hraw
  rw [← Real.exp_add]
  refine hraw.trans (Real.exp_le_exp.mpr ?_)
  have hspos : 0 < staticChoiOscillationScale hH.eigenvalues :=
    staticChoiOscillationScale_pos hH.eigenvalues
  have hsq : staticChoiOscillationScale hH.eigenvalues ^ (2 : ℕ) ≤ B ^ (2 : ℕ) :=
    (sq_le_sq₀ hspos.le hB.le).2 hscale
  have hinv : (B ^ (2 : ℕ))⁻¹ ≤
      (staticChoiOscillationScale hH.eigenvalues ^ (2 : ℕ))⁻¹ :=
    (inv_le_inv₀ (sq_pos_of_pos hB) (sq_pos_of_pos hspos)).2 hsq
  have hE : 0 ≤ finiteMatrixHilbertSchmidtEnergy
      (H * (U : Matrix (Fin d) (Fin d) ℂ) -
        (U : Matrix (Fin d) (Fin d) ℂ) * H) :=
    finiteMatrixHilbertSchmidtEnergy_nonneg _
  have hcoef := mul_le_mul_of_nonneg_left hinv
    (mul_nonneg (Nat.cast_nonneg r)
      (inv_nonneg.mpr (Nat.cast_nonneg d)))
  have hfull := mul_le_mul_of_nonneg_right hcoef hE
  let u := (‖Matrix.trace (U : Matrix (Fin d) (Fin d) ℂ)‖ / d) ^ (2 : ℕ)
  calc
    -(r : ℝ) * (u + (d : ℝ)⁻¹ *
        finiteMatrixHilbertSchmidtEnergy
          (H * (U : Matrix (Fin d) (Fin d) ℂ) -
            (U : Matrix (Fin d) (Fin d) ℂ) * H) /
        staticChoiOscillationScale hH.eigenvalues ^ (2 : ℕ)) =
      -(r : ℝ) * u -
        (((r : ℝ) * (d : ℝ)⁻¹) *
          (staticChoiOscillationScale hH.eigenvalues ^ (2 : ℕ))⁻¹ *
            finiteMatrixHilbertSchmidtEnergy
              (H * (U : Matrix (Fin d) (Fin d) ℂ) -
                (U : Matrix (Fin d) (Fin d) ℂ) * H)) := by ring
    _ ≤ -(r : ℝ) * u -
        (((r : ℝ) * (d : ℝ)⁻¹) * (B ^ (2 : ℕ))⁻¹ *
          finiteMatrixHilbertSchmidtEnergy
            (H * (U : Matrix (Fin d) (Fin d) ℂ) -
              (U : Matrix (Fin d) (Fin d) ℂ) * H)) :=
      sub_le_sub_left hfull _
    _ = -(r : ℝ) * u +
        -(((r : ℝ) * (d : ℝ)⁻¹ / B ^ (2 : ℕ)) *
          finiteMatrixHilbertSchmidtEnergy
            (H * (U : Matrix (Fin d) (Fin d) ℂ) -
              (U : Matrix (Fin d) (Fin d) ℂ) * H)) := by ring

variable {E ι : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem FiniteGaussianHermitianPencil.affineZeroAnchorResidualNearAction_le_exp_trace_mul_action_of_scale
    [Nonempty ι]
    (P : FiniteGaussianHermitianPencil E ι)
    {H₀ : Matrix ι ι ℂ} (hH₀ : H₀.IsHermitian) (x : E)
    (U : Matrix.unitaryGroup ι ℂ) (r : ℕ) (δ B : ℝ)
    (hscale : staticChoiOscillationScale
      (P.affineSpectralEnergy hH₀ x) ≤ B)
    (hB : 0 < B) :
    directStaticChoiTargetNearActionMass
        (staticChoiAnchorResidual (P.affineSpectralEnergy hH₀ x) 0
          (GaloisForLFunctions.RHTower.choiVector
            (P.affineSpectralEndpoint hH₀ x U :
              Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ)))
        (P.affineSpectralEnergy hH₀ x) r δ ≤
      Real.exp (-(r : ℝ) *
          (‖Matrix.trace (U : Matrix ι ι ℂ)‖ / Fintype.card ι) ^ (2 : ℕ)) *
        Real.exp (-(((r : ℝ) * (Fintype.card ι : ℝ)⁻¹ / B ^ (2 : ℕ)) *
          ‖P.commutatorMap U x - hermitianPencilCommutatorDrift H₀ U‖ ^ (2 : ℕ))) := by
  let Ufin := finiteGaussianHermitianPencilReindexedEndpoint U
  have h :=
    directStaticChoiTargetNearActionMass_zeroAnchorResidual_hermitianSpectralEndpoint_le_exp_trace_mul_action_of_scale
      (d := Fintype.card ι) Fintype.card_pos
      (P.affineReindexedHamiltonian_isHermitian hH₀ x) Ufin r δ B hscale hB
  rw [P.affineReindexedCommutatorEnergy H₀ x U] at h
  have htrace : Matrix.trace
      (Ufin : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ) =
      Matrix.trace (U : Matrix ι ι ℂ) := by
    change Matrix.trace
      (Matrix.reindexAlgEquiv ℂ ℂ (Fintype.equivFin ι)
        (U : Matrix ι ι ℂ)) = Matrix.trace (U : Matrix ι ι ℂ)
    rw [GaloisForLFunctions.HTGeometry.reindexAlgEquiv_trace]
  rw [htrace] at h
  exact h

omit [FiniteDimensional ℝ E] in
theorem FiniteGaussianHermitianPencil.scaledAffineZeroAnchorResidualNearAction_le_exp_trace_mul_action_of_scale
    [Nonempty ι]
    (P : FiniteGaussianHermitianPencil E ι)
    {H₀ : Matrix ι ι ℂ} (hH₀ : H₀.IsHermitian)
    {scale : ℝ} (hscale : scale ≠ 0) (x : E)
    (U : Matrix.unitaryGroup ι ℂ) (r : ℕ) (δ B : ℝ)
    (hosc : staticChoiOscillationScale
      (P.scaledAffineSpectralEnergy hH₀ scale x) ≤ B)
    (hB : 0 < B) :
    directStaticChoiTargetNearActionMass
        (staticChoiAnchorResidual
          (P.scaledAffineSpectralEnergy hH₀ scale x) 0
          (GaloisForLFunctions.RHTower.choiVector
            (P.scaledAffineSpectralEndpoint hH₀ scale x U :
              Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ)))
        (P.scaledAffineSpectralEnergy hH₀ scale x) r δ ≤
      Real.exp (-(r : ℝ) *
          (‖Matrix.trace (U : Matrix ι ι ℂ)‖ / Fintype.card ι) ^ (2 : ℕ)) *
        Real.exp (-(((r : ℝ) * (Fintype.card ι : ℝ)⁻¹ * scale ^ (2 : ℕ) / B ^ (2 : ℕ)) *
          ‖P.commutatorMap U x -
            scaledHermitianPencilCommutatorDrift scale H₀ U‖ ^ (2 : ℕ))) := by
  have h := P.affineZeroAnchorResidualNearAction_le_exp_trace_mul_action_of_scale
    hH₀ (scale • x) U r δ B hosc hB
  rw [P.scaledAffineCommutatorEnergy hscale H₀ x U] at h
  exact h.trans_eq (by
    congr 1
    congr 1
    ring)

/-- Quenched, incidence-normalized return-excised replica law.  The common
orbit sheet is charged once by normalized trace mass, while every remaining
occupied target sheet is charged by the observer-Jacobian pseudodeterminant. -/
theorem FiniteGaussianHermitianPencil.stdGaussian_measure_weightedScaledAffineZeroAnchorResidualNearAction_on_scaleSet_ge_le
    [Nonempty ι] [MeasurableSpace E] [BorelSpace E]
    (P : FiniteGaussianHermitianPencil E ι)
    {H₀ : Matrix ι ι ℂ} (hH₀ : H₀.IsHermitian)
    {scale : ℝ} (hscale : scale ≠ 0)
    {C : Type*} [Fintype C]
    (G : Set E) (U : C → Matrix.unitaryGroup ι ℂ)
    (w : C → ℝ) (hw : w ∈ stdSimplex ℝ C)
    (r : ℕ) (δ B : ℝ)
    (hosc : ∀ x ∈ G, staticChoiOscillationScale
      (P.scaledAffineSpectralEnergy hH₀ scale x) ≤ B)
    (hB : 0 < B) (n : ℕ) (hn : Module.finrank ℝ E = n)
    {κ : ℝ} (hκ : 0 < κ) :
    (ProbabilityTheory.stdGaussian E).real
        {x | x ∈ G ∧ κ ≤ ∑ c, w c * directStaticChoiTargetNearActionMass
          (staticChoiAnchorResidual
            (P.scaledAffineSpectralEnergy hH₀ scale x) 0
            (GaloisForLFunctions.RHTower.choiVector
              (P.scaledAffineSpectralEndpoint hH₀ scale x (U c) :
                Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ)))
          (P.scaledAffineSpectralEnergy hH₀ scale x) r δ} ≤
      (∑ c, w c *
        Real.exp (-(r : ℝ) *
          (‖Matrix.trace (U c : Matrix ι ι ℂ)‖ / Fintype.card ι) ^ (2 : ℕ)) *
        ∏ i : Fin n, (Real.sqrt (2 * Real.pi))⁻¹ *
          Real.sqrt (Real.pi /
            (((r : ℝ) * (Fintype.card ι : ℝ)⁻¹ * scale ^ (2 : ℕ) / B ^ (2 : ℕ)) *
              (P.commutatorMap (U c)).singularValues i ^ (2 : ℕ) + 1 / 2))) / κ := by
  let tau : ℝ :=
    (r : ℝ) * (Fintype.card ι : ℝ)⁻¹ * scale ^ (2 : ℕ) / B ^ (2 : ℕ)
  let prefactor : C → ℝ := fun c =>
    Real.exp (-(r : ℝ) *
      (‖Matrix.trace (U c : Matrix ι ι ℂ)‖ / Fintype.card ι) ^ (2 : ℕ))
  have htau : 0 ≤ tau := by
    dsimp [tau]
    positivity
  have hprefactor0 : ∀ c, 0 ≤ prefactor c := by
    intro c
    exact (Real.exp_pos _).le
  have hprefactor1 : ∀ c, prefactor c ≤ 1 := by
    intro c
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (Nat.cast_nonneg r)) (sq_nonneg _)
  apply GaloisForLFunctions.HTGeometry.stdGaussian_measure_weightedReporter_on_set_ge_le_of_prefactoredAffineLaplace
    G (fun c => P.commutatorMap (U c))
      (fun c => scaledHermitianPencilCommutatorDrift scale H₀ (U c))
      prefactor hprefactor0 hprefactor1
      (fun c x => directStaticChoiTargetNearActionMass
        (staticChoiAnchorResidual
          (P.scaledAffineSpectralEnergy hH₀ scale x) 0
          (GaloisForLFunctions.RHTower.choiVector
            (P.scaledAffineSpectralEndpoint hH₀ scale x (U c) :
              Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ)))
        (P.scaledAffineSpectralEnergy hH₀ scale x) r δ)
      w hw hn tau htau
  · intro x hx c
    have hpoint :=
      P.scaledAffineZeroAnchorResidualNearAction_le_exp_trace_mul_action_of_scale
        hH₀ hscale x (U c) r δ B (hosc x hx) hB
    simpa [tau, prefactor] using hpoint
  · exact hκ

/-- Stable-rank form of the quenched growing-replica law.  The determinant
product is compressed to the harmonic mean of replica activation and the
observer-Jacobian stable rank, with no minimum singular-value premise. -/
theorem FiniteGaussianHermitianPencil.stdGaussian_measure_weightedScaledAffineZeroAnchorResidualNearAction_on_scaleSet_ge_le_stableRank
    [Nonempty ι] [MeasurableSpace E] [BorelSpace E]
    (P : FiniteGaussianHermitianPencil E ι)
    {H₀ : Matrix ι ι ℂ} (hH₀ : H₀.IsHermitian)
    {scale : ℝ} (hscale : scale ≠ 0)
    {C : Type*} [Fintype C]
    (G : Set E) (U : C → Matrix.unitaryGroup ι ℂ)
    (w : C → ℝ) (hw : w ∈ stdSimplex ℝ C)
    (r : ℕ) (hr : 0 < r) (δ B : ℝ)
    (hosc : ∀ x ∈ G, staticChoiOscillationScale
      (P.scaledAffineSpectralEnergy hH₀ scale x) ≤ B)
    (hB : 0 < B) (n : ℕ) (hn : Module.finrank ℝ E = n)
    {κ : ℝ} (hκ : 0 < κ) :
    (ProbabilityTheory.stdGaussian E).real
        {x | x ∈ G ∧ κ ≤ ∑ c, w c * directStaticChoiTargetNearActionMass
          (staticChoiAnchorResidual
            (P.scaledAffineSpectralEnergy hH₀ scale x) 0
            (GaloisForLFunctions.RHTower.choiVector
              (P.scaledAffineSpectralEndpoint hH₀ scale x (U c) :
                Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ)))
          (P.scaledAffineSpectralEnergy hH₀ scale x) r δ} ≤
      (∑ c, w c *
        Real.exp (-(r : ℝ) *
          (‖Matrix.trace (U c : Matrix ι ι ℂ)‖ / Fintype.card ι) ^ (2 : ℕ)) *
        Real.exp (-((
          ((r : ℝ) * (Fintype.card ι : ℝ)⁻¹ * scale ^ (2 : ℕ) / B ^ (2 : ℕ)) *
            (∑ i : Fin n, (P.commutatorMap (U c)).singularValues i ^ (2 : ℕ)) ^ (2 : ℕ)) /
          (((r : ℝ) * (Fintype.card ι : ℝ)⁻¹ * scale ^ (2 : ℕ) / B ^ (2 : ℕ)) *
              (∑ i : Fin n, (P.commutatorMap (U c)).singularValues i ^ (4 : ℕ)) +
            ∑ i : Fin n, (P.commutatorMap (U c)).singularValues i ^ (2 : ℕ))))) / κ := by
  have hbase :=
    P.stdGaussian_measure_weightedScaledAffineZeroAnchorResidualNearAction_on_scaleSet_ge_le
      hH₀ hscale G U w hw r δ B hosc hB n hn hκ
  refine hbase.trans ?_
  apply div_le_div_of_nonneg_right _ hκ.le
  apply Finset.sum_le_sum
  intro c _
  apply mul_le_mul_of_nonneg_left
  · exact (P.commutatorMap (U c)).gaussianLaplaceSingularProduct_le_exp_stableRatio_total
      (n := n) (by
        have hrR : (0 : ℝ) < r := by exact_mod_cast hr
        positivity)
  · exact mul_nonneg (hw.1 c) (Real.exp_pos _).le

/-- Same ordinary two-local draw carries both certified laboratory growth and
the return-excised growing-replica pseudodeterminant bound. -/
theorem stdGaussian_measure_pairQubitProjectiveSeedWeightedReturnExcisedGrowingReplicaNearAction_on_growthSet_ge_le
    {L : ℕ} (hL : 1 ≤ L)
    {p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ}
    {rho scale : ℝ} (hrho : 0 ≤ rho)
    (hseed : ‖nearestNeighborPathLocalHamiltonian L p -
        inverseSquareChainHamiltonian L‖ ≤
      rho * nearestNeighborPathLocalGeneratorMass L)
    (hscale : scale ≠ 0)
    {C : Type*} [Fintype C]
    (U : C → Matrix.unitaryGroup (Config (PairQubit L)) ℂ)
    (w : C → ℝ) (hw : w ∈ stdSimplex ℝ C)
    (r : ℕ) (δ : ℝ) {κ : ℝ} (hκ : 0 < κ) :
    (ProbabilityTheory.stdGaussian
        (TwoLocalPauliCoefficientSpace (L * 2))).real
        {x | x ∈ weakTwoLocalPauliCertifiedGrowthSet L ∧
          κ ≤ ∑ c, w c * directStaticChoiTargetNearActionMass
            (staticChoiAnchorResidual
              (pairQubitProjectiveSeedWeakTwoLocalSpectralEnergy
                L p scale x) 0
              (GaloisForLFunctions.RHTower.choiVector
                (pairQubitProjectiveSeedWeakTwoLocalSpectralEndpoint
                    L p scale x (U c) :
                  Matrix (Fin (Fintype.card
                    (FiniteQubitConfiguration (Fin (L * 2)))))
                    (Fin (Fintype.card
                      (FiniteQubitConfiguration (Fin (L * 2))))) ℂ)))
            (pairQubitProjectiveSeedWeakTwoLocalSpectralEnergy
              L p scale x) r δ} ≤
      (∑ c, w c *
        Real.exp (-(r : ℝ) *
          (‖Matrix.trace
              (pairQubitPathUnitaryReindex L (U c) :
                Matrix (FiniteQubitConfiguration (Fin (L * 2)))
                  (FiniteQubitConfiguration (Fin (L * 2))) ℂ)‖ /
            Fintype.card (FiniteQubitConfiguration (Fin (L * 2)))) ^ (2 : ℕ)) *
        ∏ i : Fin (Module.finrank ℝ
            (TwoLocalPauliCoefficientSpace (L * 2))),
          (Real.sqrt (2 * Real.pi))⁻¹ *
            Real.sqrt (Real.pi /
              (((r : ℝ) *
                  (Fintype.card
                    (FiniteQubitConfiguration (Fin (L * 2))) : ℝ)⁻¹ *
                  scale ^ (2 : ℕ) /
                    pairQubitProjectiveSeedGrowingReplicaOscillationCeiling
                      L rho scale ^ (2 : ℕ)) *
                ((twoLocalPauliGaussianHermitianPencil
                    (L * 2)).commutatorMap
                      (pairQubitPathUnitaryReindex L (U c))).singularValues i ^ (2 : ℕ) +
                1 / 2))) / κ := by
  let P := twoLocalPauliGaussianHermitianPencil (L * 2)
  let B := pairQubitProjectiveSeedGrowingReplicaOscillationCeiling L rho scale
  have hB : 0 < B :=
    pairQubitProjectiveSeedGrowingReplicaOscillationCeiling_pos L hrho
  have hosc : ∀ x ∈ weakTwoLocalPauliCertifiedGrowthSet L,
      staticChoiOscillationScale
        (P.scaledAffineSpectralEnergy
          (pairQubitProjectivePauliSeed_isHermitian L p) scale x) ≤ B := by
    intro x hx
    simpa [P, B, pairQubitProjectiveSeedWeakTwoLocalSpectralEnergy,
      pairQubitProjectiveSeedGrowingReplicaOscillationCeiling] using
      pairQubitProjectiveSeedWeakTwoLocalSpectralOscillationScale_le
        hL hseed hx
  exact P.stdGaussian_measure_weightedScaledAffineZeroAnchorResidualNearAction_on_scaleSet_ge_le
    (pairQubitProjectivePauliSeed_isHermitian L p) hscale
    (weakTwoLocalPauliCertifiedGrowthSet L)
    (fun c => pairQubitPathUnitaryReindex L (U c))
    w hw r δ B hosc hB
    (Module.finrank ℝ (TwoLocalPauliCoefficientSpace (L * 2))) rfl hκ

noncomputable def pairQubitProjectiveSeedWeightedReturnExcisedGrowingReplicaNearAction
    {L : ℕ}
    (p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ)
    (scale : ℝ) {C : Type*} [Fintype C]
    (U : C → Matrix.unitaryGroup (Config (PairQubit L)) ℂ)
    (w : C → ℝ) (r : ℕ) (δ : ℝ)
    (x : TwoLocalPauliCoefficientSpace (L * 2)) : ℝ :=
  ∑ c, w c * directStaticChoiTargetNearActionMass
    (staticChoiAnchorResidual
      (pairQubitProjectiveSeedWeakTwoLocalSpectralEnergy L p scale x) 0
      (GaloisForLFunctions.RHTower.choiVector
        (pairQubitProjectiveSeedWeakTwoLocalSpectralEndpoint
            L p scale x (U c) :
          Matrix (Fin (Fintype.card
            (FiniteQubitConfiguration (Fin (L * 2)))))
            (Fin (Fintype.card
              (FiniteQubitConfiguration (Fin (L * 2))))) ℂ)))
    (pairQubitProjectiveSeedWeakTwoLocalSpectralEnergy L p scale x) r δ

noncomputable def pairQubitProjectiveSeedWeightedReturnExcisedGrowingReplicaBudget
    (L : ℕ) (rho scale : ℝ) {C : Type*} [Fintype C]
    (U : C → Matrix.unitaryGroup (Config (PairQubit L)) ℂ)
    (w : C → ℝ) (r : ℕ) (κ : ℝ) : ℝ :=
  (∑ c, w c *
    Real.exp (-(r : ℝ) *
      (‖Matrix.trace
          (pairQubitPathUnitaryReindex L (U c) :
            Matrix (FiniteQubitConfiguration (Fin (L * 2)))
              (FiniteQubitConfiguration (Fin (L * 2))) ℂ)‖ /
        Fintype.card (FiniteQubitConfiguration (Fin (L * 2)))) ^ (2 : ℕ)) *
    ∏ i : Fin (Module.finrank ℝ
        (TwoLocalPauliCoefficientSpace (L * 2))),
      (Real.sqrt (2 * Real.pi))⁻¹ *
        Real.sqrt (Real.pi /
          (((r : ℝ) *
              (Fintype.card
                (FiniteQubitConfiguration (Fin (L * 2))) : ℝ)⁻¹ *
              scale ^ (2 : ℕ) /
                pairQubitProjectiveSeedGrowingReplicaOscillationCeiling
                  L rho scale ^ (2 : ℕ)) *
            ((twoLocalPauliGaussianHermitianPencil
                (L * 2)).commutatorMap
                  (pairQubitPathUnitaryReindex L (U c))).singularValues i ^ (2 : ℕ) +
            1 / 2))) / κ

theorem stdGaussian_measure_pairQubitProjectiveSeedWeightedReturnExcisedGrowingReplicaBadSet_le
    {L : ℕ} (hL : 1 ≤ L)
    {p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ}
    {rho scale : ℝ} (hrho : 0 ≤ rho)
    (hseed : ‖nearestNeighborPathLocalHamiltonian L p -
        inverseSquareChainHamiltonian L‖ ≤
      rho * nearestNeighborPathLocalGeneratorMass L)
    (hscale : scale ≠ 0)
    {C : Type*} [Fintype C]
    (U : C → Matrix.unitaryGroup (Config (PairQubit L)) ℂ)
    (w : C → ℝ) (hw : w ∈ stdSimplex ℝ C)
    (r : ℕ) (δ : ℝ) {κ : ℝ} (hκ : 0 < κ) :
    (ProbabilityTheory.stdGaussian
      (TwoLocalPauliCoefficientSpace (L * 2))).real
        {x | x ∈ weakTwoLocalPauliCertifiedGrowthSet L ∧
          κ ≤ pairQubitProjectiveSeedWeightedReturnExcisedGrowingReplicaNearAction
            p scale U w r δ x} ≤
      pairQubitProjectiveSeedWeightedReturnExcisedGrowingReplicaBudget
        L rho scale U w r κ := by
  simpa [pairQubitProjectiveSeedWeightedReturnExcisedGrowingReplicaNearAction,
    pairQubitProjectiveSeedWeightedReturnExcisedGrowingReplicaBudget] using
    stdGaussian_measure_pairQubitProjectiveSeedWeightedReturnExcisedGrowingReplicaNearAction_on_growthSet_ge_le
      hL hrho hseed hscale U w hw r δ hκ

/-- Same-draw selection: growth carrier, return-excised complete-image
pseudodeterminant suppression, and maximal projective spectrum coexist. -/
theorem exists_pairQubitProjectiveSeedWeightedReturnExcisedGrowingReplica_sameDraw
    {L : ℕ} (hL : 1 ≤ L)
    {p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ}
    (hp : p ∈ nearestNeighborPathLocalMaximalSet L)
    {rho scale : ℝ} (hrho : 0 ≤ rho)
    (hseed : ‖nearestNeighborPathLocalHamiltonian L p -
        inverseSquareChainHamiltonian L‖ ≤
      rho * nearestNeighborPathLocalGeneratorMass L)
    (hscale : scale ≠ 0)
    {C : Type*} [Fintype C]
    (U : C → Matrix.unitaryGroup (Config (PairQubit L)) ℂ)
    (w : C → ℝ) (hw : w ∈ stdSimplex ℝ C)
    (r : ℕ) (δ : ℝ) {κ : ℝ} (hκ : 0 < κ)
    (hjoint : pairQubitWeakTwoLocalGrowthFailureBudget L +
        pairQubitProjectiveSeedWeightedReturnExcisedGrowingReplicaBudget
          L rho scale U w r κ < 1) :
    ∃ x : TwoLocalPauliCoefficientSpace (L * 2),
      x ∈ weakTwoLocalPauliCertifiedGrowthSet L ∧
      pairQubitProjectiveSeedWeightedReturnExcisedGrowingReplicaNearAction
        p scale U w r δ x < κ ∧
      MaximallyProjectiveEnergy
        (pairQubitProjectiveSeedWeakTwoLocalSpectralEnergy L p scale x) := by
  let μ := ProbabilityTheory.stdGaussian
    (TwoLocalPauliCoefficientSpace (L * 2))
  let G := weakTwoLocalPauliCertifiedGrowthSet L
  let S : Set (TwoLocalPauliCoefficientSpace (L * 2)) :=
    {x | x ∈ G ∧ κ ≤
      pairQubitProjectiveSeedWeightedReturnExcisedGrowingReplicaNearAction
        p scale U w r δ x}
  let M : Set (TwoLocalPauliCoefficientSpace (L * 2)) :=
    {x | MaximallyProjectiveEnergy
      (pairQubitProjectiveSeedWeakTwoLocalSpectralEnergy L p scale x)}
  have hGc : μ.real Gᶜ ≤ pairQubitWeakTwoLocalGrowthFailureBudget L := by
    exact stdGaussian_weakTwoLocalPauliCertifiedGrowthSet_compl_le L
  have hS : μ.real S ≤
      pairQubitProjectiveSeedWeightedReturnExcisedGrowingReplicaBudget
        L rho scale U w r κ := by
    exact stdGaussian_measure_pairQubitProjectiveSeedWeightedReturnExcisedGrowingReplicaBadSet_le
      hL hrho hseed hscale U w hw r δ hκ
  have hae : ∀ᵐ x ∂μ, x ∈ M := by
    exact pairQubitProjectiveSeedWeakTwoLocalSpectralEnergy_maximallyProjective_ae
      hp scale
  have hMnull : μ Mᶜ = 0 := by
    rw [MeasureTheory.ae_iff] at hae
    change μ {x | x ∉ M} = 0
    exact hae
  have hMreal : μ.real Mᶜ = 0 := by
    simp [MeasureTheory.measureReal_def, hMnull]
  by_contra hnone
  have hcover : Set.univ ⊆ Gᶜ ∪ S ∪ Mᶜ := by
    intro x _
    by_cases hxG : x ∈ G
    · by_cases hxS : x ∈ S
      · exact Or.inl (Or.inr hxS)
      · exact Or.inr (by
          intro hxM
          apply hnone
          refine ⟨x, hxG, ?_, hxM⟩
          have hnot : ¬ κ ≤
              pairQubitProjectiveSeedWeightedReturnExcisedGrowingReplicaNearAction
                p scale U w r δ x := by
            intro hle
            exact hxS ⟨hxG, hle⟩
          exact lt_of_not_ge hnot)
    · exact Or.inl (Or.inl hxG)
  have hone : 1 ≤ μ.real Gᶜ + μ.real S + μ.real Mᶜ := by
    calc
      1 = μ.real Set.univ := by simp [μ]
      _ ≤ μ.real (Gᶜ ∪ S ∪ Mᶜ) := MeasureTheory.measureReal_mono hcover
      _ ≤ μ.real (Gᶜ ∪ S) + μ.real Mᶜ := MeasureTheory.measureReal_union_le _ _
      _ ≤ (μ.real Gᶜ + μ.real S) + μ.real Mᶜ := by
        gcongr
        exact MeasureTheory.measureReal_union_le _ _
  rw [hMreal, add_zero] at hone
  linarith

theorem directStaticChoiTargetNearActionMass_le_norm_pow
    {d : ℕ} (hd : 0 < d)
    (target : EuclideanSpace ℂ (Fin d × Fin d))
    (energy : Fin d → ℝ) (r : ℕ) (δ : ℝ) :
    directStaticChoiTargetNearActionMass target energy r δ ≤
      ‖target‖ ^ (2 * r) := by
  exact (directStaticChoiTargetNearActionMass_le_centralizerMass_pow
      target energy r δ).trans
    (pow_le_pow_left₀ (directStaticChoiCentralizerMass_nonneg target)
      (directStaticChoiCentralizerMass_le_norm hd target) (2 * r))

theorem directStaticChoiTargetNearActionMass_anchorResidual_le
    {d : ℕ} (hd : 0 < d)
    (energy : Fin d → ℝ) (anchor : ℝ)
    {target : EuclideanSpace ℂ (Fin d × Fin d)}
    (htarget : ‖target‖ = 1) (r : ℕ) (δ : ℝ) :
    directStaticChoiTargetNearActionMass
        (staticChoiAnchorResidual energy anchor target) energy r δ ≤
      (1 - ‖staticChoiAnchorComponent energy anchor target‖ ^ (2 : ℕ)) ^ r := by
  calc
    directStaticChoiTargetNearActionMass
        (staticChoiAnchorResidual energy anchor target) energy r δ ≤
      ‖staticChoiAnchorResidual energy anchor target‖ ^ (2 * r) :=
        directStaticChoiTargetNearActionMass_le_norm_pow hd _ energy r δ
    _ = (‖staticChoiAnchorResidual energy anchor target‖ ^ (2 : ℕ)) ^ r := by
      rw [pow_mul]
    _ = (1 - ‖staticChoiAnchorComponent energy anchor target‖ ^ (2 : ℕ)) ^ r := by
      rw [norm_sq_staticChoiAnchorResidual_eq_one_sub_norm_sq_component
        hd energy anchor htarget]

end

end RHTower
