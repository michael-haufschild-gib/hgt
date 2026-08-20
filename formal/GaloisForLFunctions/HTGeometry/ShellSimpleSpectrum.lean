/-
# Almost every direction of the fixed shell has a simple spectrum

Simplicity of the spectrum is a closed, scale-invariant condition on the coefficient vector: closed
because the canonically sorted spectrum is continuous, scale-invariant because scaling a Hermitian
matrix scales its eigenvalue multiset.  A scale-invariant Lebesgue-null set is null on the sphere,
and the degenerate locus is Lebesgue-null because the centred product Gaussian -- which is
equivalent to Lebesgue measure -- gives it probability zero.

Main results:
* `pi_absolutelyContinuous_pi_fintype` — the product absolute-continuity law, any finite index.
* `volume_absolutelyContinuous_centredProductGaussian` — Lebesgue measure is dominated by the
  centred product Gaussian.
* `pauliEnsemble_smul`, `injective_eigenvalues_pauliEnsemble_smul_iff` — the degenerate locus is a
  cone.
* `isClosed_pauliEnsemble_degenerate` — **it is closed**.
-/
import GaloisForLFunctions.HTGeometry.FintypeSortedSpectrum
import GaloisForLFunctions.HTGeometry.HermitianEigenvalueScaling
import GaloisForLFunctions.HTGeometry.SphereHomogeneousNullSet
import GaloisForLFunctions.HTGeometry.PauliEnsembleSimpleSpectrum
import GaloisForLFunctions.HTGeometry.PiMeasureAbsoluteContinuity
import GaloisForLFunctions.HTGeometry.ShellProbabilityMeasure

open Matrix MeasureTheory ProbabilityTheory
open QuantumAlg

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Product absolute continuity over an arbitrary finite index -/

theorem pi_absolutelyContinuous_pi_fintype {ι : Type u} [Fintype ι] {α : ι → Type u}
    [∀ i, MeasurableSpace (α i)] (μ ν : ∀ i, Measure (α i))
    [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (ν i)] (h : ∀ i, μ i ≪ ν i) :
    Measure.pi μ ≪ Measure.pi ν := by
  classical
  set e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm with he
  have hbase : Measure.pi (fun i' => μ (e i')) ≪ Measure.pi (fun i' => ν (e i')) :=
    pi_absolutelyContinuous_pi (Fintype.card ι) _ _ fun i' => h (e i')
  have hμ : Measure.map (MeasurableEquiv.piCongrLeft α e)
      (Measure.pi fun i' => μ (e i')) = Measure.pi μ :=
    (measurePreserving_piCongrLeft μ e).map_eq
  have hν : Measure.map (MeasurableEquiv.piCongrLeft α e)
      (Measure.pi fun i' => ν (e i')) = Measure.pi ν :=
    (measurePreserving_piCongrLeft ν e).map_eq
  rw [← hμ, ← hν]
  exact hbase.map (MeasurableEquiv.piCongrLeft α e).measurable

theorem volume_absolutelyContinuous_centredProductGaussian (ι : Type) [Fintype ι] {v : NNReal}
    (hv : v ≠ 0) : (volume : Measure (ι → ℝ)) ≪ centredProductGaussian ι v := by
  rw [centredProductGaussian, volume_pi]
  exact pi_absolutelyContinuous_pi_fintype _ _ fun _ => gaussianReal_absolutelyContinuous' 0 hv

/-! ## The degenerate locus of the Pauli ensemble -/

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

theorem continuous_pauliEnsemble (w : (σ → Option (Fin 3)) → ℝ) :
    Continuous fun J : (σ → Option (Fin 3)) → ℝ => pauliEnsemble w J := by
  refine continuous_pi fun x => continuous_pi fun y => ?_
  have hrw : ∀ J : (σ → Option (Fin 3)) → ℝ, pauliEnsemble w J x y =
      ∑ P, ((w P * J P : ℝ) : ℂ) * finitePauliMatrix P x y := by
    intro J
    rw [pauliEnsemble]
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  simp only [hrw]
  refine continuous_finsetSum _ fun P _ => ?_
  exact (Complex.continuous_ofReal.comp
    (continuous_const.mul (continuous_apply P))).mul continuous_const

/-- **Scaling the coefficients scales the ensemble.** -/
theorem pauliEnsemble_smul (w : (σ → Option (Fin 3)) → ℝ) (t : ℝ)
    (J : (σ → Option (Fin 3)) → ℝ) :
    pauliEnsemble w (fun P => t * J P) = ((t : ℂ)) • pauliEnsemble w J := by
  rw [pauliEnsemble, pauliEnsemble, Finset.smul_sum]
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [smul_smul]
  congr 1
  push_cast
  ring

/-- **Simplicity of the ensemble spectrum is scale invariant.** -/
theorem injective_eigenvalues_pauliEnsemble_smul_iff (w : (σ → Option (Fin 3)) → ℝ) {t : ℝ}
    (ht : t ≠ 0) (J : (σ → Option (Fin 3)) → ℝ) :
    Function.Injective (isHermitian_pauliEnsemble w (fun P => t * J P)).eigenvalues
      ↔ Function.Injective (isHermitian_pauliEnsemble w J).eigenvalues := by
  have hA' : (((t : ℂ)) • pauliEnsemble w J).IsHermitian := by
    rw [← pauliEnsemble_smul w t J]
    exact isHermitian_pauliEnsemble w _
  have heig : (isHermitian_pauliEnsemble w (fun P => t * J P)).eigenvalues = hA'.eigenvalues :=
    isHermitian_eigenvalues_congr _ _ (pauliEnsemble_smul w t J)
  rw [heig]
  exact injective_eigenvalues_smul_iff (isHermitian_pauliEnsemble w J) ht hA'

/-- **The degenerate locus of the Pauli ensemble is closed.** -/
theorem isClosed_pauliEnsemble_degenerate (w : (σ → Option (Fin 3)) → ℝ) :
    IsClosed {J : (σ → Option (Fin 3)) → ℝ |
      ¬ Function.Injective (isHermitian_pauliEnsemble w J).eigenvalues} :=
  isClosed_repeatedSpectrum (continuous_pauliEnsemble w) (isHermitian_pauliEnsemble w)

/-! ## The shell has almost surely simple spectrum -/

section Shell

variable {n q : ℕ}

/-- **The degenerate locus is Lebesgue null.**  The centred product Gaussian gives it probability
zero, and Lebesgue measure is dominated by that Gaussian. -/
theorem volume_pauliEnsemble_degenerate_eq_zero (w : (Fin n → Option (Fin 3)) → ℝ) (hq : 2 ≤ q)
    (hw : ∀ P : Fin n → Option (Fin 3),
      ¬ (pauliWeight P ≤ q ∧ P ≠ pauliIdentityLabel n) → w P = 0)
    (hwne : ∀ t : Fin (Fintype.card (PauliTracelessLabel n q)),
      w (((pauliTracelessLabelEquivFin n q).symm t).1) ≠ 0) :
    (volume : Measure ((Fin n → Option (Fin 3)) → ℝ))
      {J | ¬ Function.Injective (isHermitian_pauliEnsemble w J).eigenvalues} = 0 :=
  volume_absolutelyContinuous_centredProductGaussian _ (v := 1) one_ne_zero
    (injective_eigenvalues_pauliEnsemble_ae (q := q) w hq hw (v := 1) one_ne_zero hwne)

/-- The degenerate locus, read in Euclidean coordinates. -/
def euclideanDegenerate (w : (Fin n → Option (Fin 3)) → ℝ) :
    Set (EuclideanSpace ℝ (Fin n → Option (Fin 3))) :=
  {x | ¬ Function.Injective
    (isHermitian_pauliEnsemble w (WithLp.ofLp x)).eigenvalues}

theorem measurableSet_euclideanDegenerate (w : (Fin n → Option (Fin 3)) → ℝ) :
    MeasurableSet (euclideanDegenerate w) := by
  have hpre : euclideanDegenerate w
      = (fun x : EuclideanSpace ℝ (Fin n → Option (Fin 3)) => WithLp.ofLp x) ⁻¹'
        {J : (Fin n → Option (Fin 3)) → ℝ |
          ¬ Function.Injective (isHermitian_pauliEnsemble w J).eigenvalues} := rfl
  rw [hpre]
  exact ((isClosed_pauliEnsemble_degenerate w).measurableSet).preimage
    (PiLp.continuous_ofLp 2 _).measurable

theorem volume_euclideanDegenerate_eq_zero (w : (Fin n → Option (Fin 3)) → ℝ) (hq : 2 ≤ q)
    (hw : ∀ P : Fin n → Option (Fin 3),
      ¬ (pauliWeight P ≤ q ∧ P ≠ pauliIdentityLabel n) → w P = 0)
    (hwne : ∀ t : Fin (Fintype.card (PauliTracelessLabel n q)),
      w (((pauliTracelessLabelEquivFin n q).symm t).1) ≠ 0) :
    (volume : Measure (EuclideanSpace ℝ (Fin n → Option (Fin 3)))) (euclideanDegenerate w) = 0 := by
  have hmp := PiLp.volume_preserving_ofLp (Fin n → Option (Fin 3))
  have hpre : euclideanDegenerate w
      = (fun x : EuclideanSpace ℝ (Fin n → Option (Fin 3)) => WithLp.ofLp x) ⁻¹'
        {J : (Fin n → Option (Fin 3)) → ℝ |
          ¬ Function.Injective (isHermitian_pauliEnsemble w J).eigenvalues} := rfl
  rw [hpre, hmp.measure_preimage
    ((isClosed_pauliEnsemble_degenerate w).measurableSet).nullMeasurableSet]
  exact volume_pauliEnsemble_degenerate_eq_zero (q := q) w hq hw hwne

/-- **Almost every direction of the fixed shell has a simple spectrum.** -/
theorem injective_eigenvalues_pauliEnsemble_shell_ae (w : (Fin n → Option (Fin 3)) → ℝ)
    (hq : 2 ≤ q)
    (hw : ∀ P : Fin n → Option (Fin 3),
      ¬ (pauliWeight P ≤ q ∧ P ≠ pauliIdentityLabel n) → w P = 0)
    (hwne : ∀ t : Fin (Fintype.card (PauliTracelessLabel n q)),
      w (((pauliTracelessLabelEquivFin n q).symm t).1) ≠ 0) :
    ∀ᵐ J ∂(shellProbability (Fin n → Option (Fin 3))),
      Function.Injective (isHermitian_pauliEnsemble w J).eigenvalues := by
  have hcone : ∀ r : ℝ, 0 < r → ∀ x ∈ euclideanDegenerate w, r • x ∈ euclideanDegenerate w := by
    intro r hr x hx
    have hofLp : (WithLp.ofLp (r • x)) = fun i => r * (WithLp.ofLp x) i := rfl
    show ¬ Function.Injective (isHermitian_pauliEnsemble w (WithLp.ofLp (r • x))).eigenvalues
    rw [hofLp]
    intro hinj
    exact hx ((injective_eigenvalues_pauliEnsemble_smul_iff w hr.ne' _).mp hinj)
  have hsphere : (volume : Measure (EuclideanSpace ℝ (Fin n → Option (Fin 3)))).toSphere
      {θ | (θ : EuclideanSpace ℝ (Fin n → Option (Fin 3))) ∈ euclideanDegenerate w} = 0 := by
    refine toSphere_eq_zero_of_scaleInvariant
      (volume_euclideanDegenerate_eq_zero (q := q) w hq hw hwne) hcone
      ((measurableSet_euclideanDegenerate w).preimage measurable_subtype_coe) ?_
    intro θ hθ
    exact hθ
  have hbad : MeasurableSet {J : (Fin n → Option (Fin 3)) → ℝ |
      ¬ Function.Injective (isHermitian_pauliEnsemble w J).eigenvalues} :=
    (isClosed_pauliEnsemble_degenerate w).measurableSet
  rw [Filter.eventually_iff, mem_ae_iff]
  have hcompl : {J : (Fin n → Option (Fin 3)) → ℝ |
      Function.Injective (isHermitian_pauliEnsemble w J).eigenvalues}ᶜ
      = {J : (Fin n → Option (Fin 3)) → ℝ |
        ¬ Function.Injective (isHermitian_pauliEnsemble w J).eigenvalues} := rfl
  have hsphere' : (volume : Measure (EuclideanSpace ℝ (Fin n → Option (Fin 3)))).toSphere
      (shellCoefficientMap (Fin n → Option (Fin 3)) ⁻¹'
        {J : (Fin n → Option (Fin 3)) → ℝ |
          ¬ Function.Injective (isHermitian_pauliEnsemble w J).eigenvalues}) = 0 := hsphere
  rw [hcompl, shellProbability, Measure.smul_apply, shellCoefficientMeasure,
    Measure.map_apply measurable_shellCoefficientMap hbad, hsphere', smul_eq_mul, mul_zero]

/-- **The almost sure eigenbasis datum on the fixed shell.** -/
theorem isOrthoEigenBasis_injective_pauliEnsemble_shell_ae (w : (Fin n → Option (Fin 3)) → ℝ)
    (hq : 2 ≤ q)
    (hw : ∀ P : Fin n → Option (Fin 3),
      ¬ (pauliWeight P ≤ q ∧ P ≠ pauliIdentityLabel n) → w P = 0)
    (hwne : ∀ t : Fin (Fintype.card (PauliTracelessLabel n q)),
      w (((pauliTracelessLabelEquivFin n q).symm t).1) ≠ 0) :
    ∀ᵐ J ∂(shellProbability (Fin n → Option (Fin 3))),
      IsOrthoEigenBasis (pauliEnsemble w J)
          (hermitianEigenBasis (pauliEnsemble w J) (isHermitian_pauliEnsemble w J))
          (isHermitian_pauliEnsemble w J).eigenvalues ∧
        Function.Injective (isHermitian_pauliEnsemble w J).eigenvalues := by
  filter_upwards [injective_eigenvalues_pauliEnsemble_shell_ae (q := q) w hq hw hwne] with J hJ
  exact ⟨isOrthoEigenBasis_hermitian _ (isHermitian_pauliEnsemble w J), hJ⟩

end Shell

end

end GaloisForLFunctions.HTGeometry
