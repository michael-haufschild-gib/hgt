import GaloisForLFunctions.HTGeometry.PauliEnsembleTracelessBridge
import GaloisForLFunctions.HTGeometry.GaussianCoordinateSelection
import GaloisForLFunctions.HTGeometry.CliffordEnsembleCollisionMean

/-!
# Almost sure simple spectrum of the weighted Pauli Gaussian ensemble

The coefficient vector of the traceless bounded-weight family produced by the ensemble is a
rescaled selection of distinct coordinates of the centred product Gaussian, so its law is a centred
product Gaussian with nonzero variances and therefore absolutely continuous.  The genericity of the
traceless family then gives an almost surely simple spectrum, and hence an almost surely simple
orthonormal eigenbasis for the ensemble.
-/

open MeasureTheory ProbabilityTheory Matrix

open QuantumAlg

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem isHermitian_eigenvalues_congr {A B : Matrix α α ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (h : A = B) : hA.eigenvalues = hB.eigenvalues := by
  subst h
  rfl

section Ensemble

variable {n q : ℕ}

/-- The coefficient vector of the traceless bounded-weight family produced by the ensemble. -/
def tracelessCoefficients (w : (Fin n → Option (Fin 3)) → ℝ) (q : ℕ)
    (J : (Fin n → Option (Fin 3)) → ℝ) : Fin (Fintype.card (PauliTracelessLabel n q)) → ℝ :=
  fun t => w (((pauliTracelessLabelEquivFin n q).symm t).1) *
    J (((pauliTracelessLabelEquivFin n q).symm t).1)

theorem measurable_tracelessCoefficients (w : (Fin n → Option (Fin 3)) → ℝ) (q : ℕ) :
    Measurable (tracelessCoefficients w q) := by
  refine measurable_pi_lambda _ fun t => ?_
  exact measurable_const.mul (measurable_pi_apply _)

theorem map_tracelessCoefficients (w : (Fin n → Option (Fin 3)) → ℝ) (v : NNReal) :
    (centredProductGaussian (Fin n → Option (Fin 3)) v).map (tracelessCoefficients w q) =
      Measure.pi fun t : Fin (Fintype.card (PauliTracelessLabel n q)) =>
        gaussianReal 0 (⟨(w (((pauliTracelessLabelEquivFin n q).symm t).1)) ^ 2,
          sq_nonneg _⟩ * v) :=
  map_selection_centredProductGaussian
    (fun P : Fin n → Option (Fin 3) => pauliWeight P ≤ q ∧ P ≠ pauliIdentityLabel n)
    (pauliTracelessLabelEquivFin n q).symm
    (fun t => w (((pauliTracelessLabelEquivFin n q).symm t).1)) v

theorem absolutelyContinuous_map_tracelessCoefficients (w : (Fin n → Option (Fin 3)) → ℝ)
    {v : NNReal} (hv : v ≠ 0)
    (hwne : ∀ t : Fin (Fintype.card (PauliTracelessLabel n q)),
      w (((pauliTracelessLabelEquivFin n q).symm t).1) ≠ 0) :
    (centredProductGaussian (Fin n → Option (Fin 3)) v).map (tracelessCoefficients w q) ≪
      volume := by
  rw [map_tracelessCoefficients w v, volume_pi]
  refine pi_absolutelyContinuous_pi _ _ _ fun t => ?_
  refine gaussianReal_absolutelyContinuous 0 ?_
  refine mul_ne_zero ?_ hv
  intro hcon
  apply hwne t
  have h2 : (w (((pauliTracelessLabelEquivFin n q).symm t).1)) ^ 2 = 0 := by
    have h3 := Subtype.ext_iff.mp hcon
    simpa using h3
  exact sq_eq_zero_iff.mp h2

/-- **Almost sure simple spectrum of the weighted Pauli Gaussian ensemble.** -/
theorem injective_eigenvalues_pauliEnsemble_ae (w : (Fin n → Option (Fin 3)) → ℝ) (hq : 2 ≤ q)
    (hw : ∀ P : Fin n → Option (Fin 3),
      ¬ (pauliWeight P ≤ q ∧ P ≠ pauliIdentityLabel n) → w P = 0)
    {v : NNReal} (hv : v ≠ 0)
    (hwne : ∀ t : Fin (Fintype.card (PauliTracelessLabel n q)),
      w (((pauliTracelessLabelEquivFin n q).symm t).1) ≠ 0) :
    ∀ᵐ J ∂(centredProductGaussian (Fin n → Option (Fin 3)) v),
      Function.Injective (isHermitian_pauliEnsemble w J).eigenvalues := by
  classical
  have hAC := absolutelyContinuous_map_tracelessCoefficients (q := q) w hv hwne
  have hgen := pauliTraceless_projectivelyIndependent_ae n hq hAC
  have hqmp : Measure.QuasiMeasurePreserving (tracelessCoefficients w q)
      (centredProductGaussian (Fin n → Option (Fin 3)) v)
      ((centredProductGaussian (Fin n → Option (Fin 3)) v).map (tracelessCoefficients w q)) :=
    ⟨measurable_tracelessCoefficients w q, Measure.AbsolutelyContinuous.rfl⟩
  filter_upwards [hqmp.ae hgen] with J hJ
  have hEq : pauliEnsemble w J =
      (pauliTracelessFinPolynomialMatrix n q).map (MvPolynomial.eval₂Hom (RingHom.id ℂ)
        fun t => ((tracelessCoefficients w q J t : ℝ) : ℂ)) :=
    pauliEnsemble_eq_tracelessFinEval w J hw
  have hval := isHermitian_eigenvalues_congr (isHermitian_pauliEnsemble w J)
    (isHermitian_pauliTracelessFinEval (tracelessCoefficients w q J)) hEq
  rw [hval]
  exact hJ.1

/-- **The almost sure eigenbasis datum of the ensemble.**  This is exactly the hypothesis consumed
by the quenched collision bounds. -/
theorem isOrthoEigenBasis_injective_pauliEnsemble_ae (w : (Fin n → Option (Fin 3)) → ℝ)
    (hq : 2 ≤ q)
    (hw : ∀ P : Fin n → Option (Fin 3),
      ¬ (pauliWeight P ≤ q ∧ P ≠ pauliIdentityLabel n) → w P = 0)
    {v : NNReal} (hv : v ≠ 0)
    (hwne : ∀ t : Fin (Fintype.card (PauliTracelessLabel n q)),
      w (((pauliTracelessLabelEquivFin n q).symm t).1) ≠ 0) :
    ∀ᵐ J ∂(centredProductGaussian (Fin n → Option (Fin 3)) v),
      IsOrthoEigenBasis (pauliEnsemble w J)
          (hermitianEigenBasis (pauliEnsemble w J) (isHermitian_pauliEnsemble w J))
          (isHermitian_pauliEnsemble w J).eigenvalues ∧
        Function.Injective (isHermitian_pauliEnsemble w J).eigenvalues := by
  filter_upwards [injective_eigenvalues_pauliEnsemble_ae w hq hw hv hwne] with J hJ
  exact ⟨isOrthoEigenBasis_hermitian _ (isHermitian_pauliEnsemble w J), hJ⟩

/-- **Maximal projective spectral rank of the ensemble, almost surely.** -/
theorem maximallyProjectiveEnergy_pauliEnsemble_ae (w : (Fin n → Option (Fin 3)) → ℝ) (hq : 2 ≤ q)
    (hw : ∀ P : Fin n → Option (Fin 3),
      ¬ (pauliWeight P ≤ q ∧ P ≠ pauliIdentityLabel n) → w P = 0)
    {v : NNReal} (hv : v ≠ 0)
    (hwne : ∀ t : Fin (Fintype.card (PauliTracelessLabel n q)),
      w (((pauliTracelessLabelEquivFin n q).symm t).1) ≠ 0) :
    ∀ᵐ J ∂(centredProductGaussian (Fin n → Option (Fin 3)) v),
      MaximallyProjectiveEnergy (isHermitian_pauliEnsemble w J).eigenvalues := by
  classical
  have hAC := absolutelyContinuous_map_tracelessCoefficients (q := q) w hv hwne
  have hgen := pauliTraceless_projectivelyIndependent_ae n hq hAC
  have hqmp : Measure.QuasiMeasurePreserving (tracelessCoefficients w q)
      (centredProductGaussian (Fin n → Option (Fin 3)) v)
      ((centredProductGaussian (Fin n → Option (Fin 3)) v).map (tracelessCoefficients w q)) :=
    ⟨measurable_tracelessCoefficients w q, Measure.AbsolutelyContinuous.rfl⟩
  filter_upwards [hqmp.ae hgen] with J hJ
  have hEq : pauliEnsemble w J =
      (pauliTracelessFinPolynomialMatrix n q).map (MvPolynomial.eval₂Hom (RingHom.id ℂ)
        fun t => ((tracelessCoefficients w q J t : ℝ) : ℂ)) :=
    pauliEnsemble_eq_tracelessFinEval w J hw
  have hval := isHermitian_eigenvalues_congr (isHermitian_pauliEnsemble w J)
    (isHermitian_pauliTracelessFinEval (tracelessCoefficients w q J)) hEq
  rw [hval]
  exact hJ.2

/-- **The quenched collision law of the fixed product input, unconditionally.**  For a centred
Pauli Gaussian ensemble with support-invariant weights that are nonzero on every nonidentity
bounded-weight label, the mean collision at the all-zero product state is at most `(2/3)ⁿ`. -/
theorem integral_collision_pauliEnsemble_zeroProductState_le
    (w : (Fin n → Option (Fin 3)) → ℝ) (hq : 2 ≤ q) (hwsupp : SupportInvariantWeight w)
    (hw : ∀ P : Fin n → Option (Fin 3),
      ¬ (pauliWeight P ≤ q ∧ P ≠ pauliIdentityLabel n) → w P = 0)
    {v : NNReal} (hv : v ≠ 0)
    (hwne : ∀ t : Fin (Fintype.card (PauliTracelessLabel n q)),
      w (((pauliTracelessLabelEquivFin n q).symm t).1) ≠ 0) :
    (∫ J, spectralCollision
        (hermitianEigenBasis (pauliEnsemble w J) (isHermitian_pauliEnsemble w J))
        (zeroProductState (Fin n))
        ∂(centredProductGaussian (Fin n → Option (Fin 3)) v)) ≤ (2 / 3 : ℝ) ^ n :=
  integral_spectralCollision_zeroProductState_le w hwsupp v
    (isOrthoEigenBasis_injective_pauliEnsemble_ae w hq hw hv hwne)

/-- **Markov form of the quenched collision law, unconditionally.** -/
theorem measureReal_collision_pauliEnsemble_zeroProductState_ge_le
    (w : (Fin n → Option (Fin 3)) → ℝ) (hq : 2 ≤ q) (hwsupp : SupportInvariantWeight w)
    (hw : ∀ P : Fin n → Option (Fin 3),
      ¬ (pauliWeight P ≤ q ∧ P ≠ pauliIdentityLabel n) → w P = 0)
    {v : NNReal} (hv : v ≠ 0)
    (hwne : ∀ t : Fin (Fintype.card (PauliTracelessLabel n q)),
      w (((pauliTracelessLabelEquivFin n q).symm t).1) ≠ 0)
    {L : ℝ} (hL : 0 < L) :
    (centredProductGaussian (Fin n → Option (Fin 3)) v).real
        {J | L * (2 / 3 : ℝ) ^ n ≤ spectralCollision
          (hermitianEigenBasis (pauliEnsemble w J) (isHermitian_pauliEnsemble w J))
          (zeroProductState (Fin n))} ≤ 1 / L :=
  measureReal_spectralCollision_zeroProductState_ge_le w hwsupp v
    (isOrthoEigenBasis_injective_pauliEnsemble_ae w hq hw hv hwne) hL

end Ensemble

end GaloisForLFunctions.HTGeometry
