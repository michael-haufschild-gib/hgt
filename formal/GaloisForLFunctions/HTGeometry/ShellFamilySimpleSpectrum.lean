/-
# Almost every direction of a fixed shell has a simple spectrum

Simplicity of the spectrum of `∑ₐ θₐ Pₐ` is exactly nonvanishing of the spectral discriminant
polynomial at `θ`.  For a family with one simple-spectrum member the discriminant is a nonzero real
polynomial, so its zero set is Lebesgue-null; it is a cone because scaling a Hermitian matrix scales
its spectrum, and a scale-invariant null set is null on the unit sphere.

This is the family-generic form of the corpus's Pauli-shell law, which requires the weight to be
nonzero on every two-local label and therefore does not apply to a proper subfamily.

Main results:
* `injective_eigenvalues_iff_eval_spectralDiscriminantPoly_ne_zero` — the discriminant criterion.
* `injective_eigenvalues_spectralEnsemble_shell_ae` — **almost every shell direction is simple**.
* `toSphere_degenerate_eq_zero` — the same on the sphere measure itself.
* `isOrthoEigenBasis_injective_spectralEnsemble_shell_ae` — with the eigenbasis datum.
-/
import GaloisForLFunctions.HTGeometry.ShellSimpleSpectrum
import GaloisForLFunctions.HTGeometry.RealPolynomialZeroMeasure

open Matrix MeasureTheory Metric

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {N D : ℕ}

/-- **A simple spectrum is exactly nonvanishing of the spectral discriminant.** -/
theorem injective_eigenvalues_iff_eval_spectralDiscriminantPoly_ne_zero
    {P : Fin N → Matrix (Fin D) (Fin D) ℂ} (hP : ∀ a, (P a).IsHermitian) (θ : Fin N → ℝ) :
    Function.Injective (isHermitian_spectralEnsembleMatrix hP θ).eigenvalues
      ↔ MvPolynomial.eval θ (spectralDiscriminantPoly P) ≠ 0 := by
  classical
  constructor
  · intro hinj
    rw [eval_spectralDiscriminantPoly hP θ]
    refine pow_ne_zero 2 ?_
    refine Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr fun j hj => ?_
    have hne : i ≠ j := (Finset.mem_Ioi.mp hj).ne
    intro hzero
    exact hne (hinj (sub_eq_zero.mp hzero)).symm
  · intro hne i j hij
    by_contra hcon
    refine hne ?_
    rw [eval_spectralDiscriminantPoly hP θ, sq_eq_zero_iff]
    refine Finset.prod_eq_zero_iff.mpr ?_
    rcases lt_or_gt_of_ne hcon with hlt | hlt
    · exact ⟨i, Finset.mem_univ i, Finset.prod_eq_zero_iff.mpr
        ⟨j, Finset.mem_Ioi.mpr hlt, sub_eq_zero.mpr hij.symm⟩⟩
    · exact ⟨j, Finset.mem_univ j, Finset.prod_eq_zero_iff.mpr
        ⟨i, Finset.mem_Ioi.mpr hlt, sub_eq_zero.mpr hij⟩⟩

theorem eigenvalues_congr_of_eq {ι : Type*} [Fintype ι] [DecidableEq ι] {A B : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (h : A = B) : hA.eigenvalues = hB.eigenvalues := by
  subst h
  rfl

theorem spectralEnsembleMatrix_smul_shellFamilySimpleSpectrum (P : Fin N → Matrix (Fin D) (Fin D) ℂ) (t : ℝ)
    (θ : Fin N → ℝ) :
    spectralEnsembleMatrix P (fun a => t * θ a) = ((t : ℂ)) • spectralEnsembleMatrix P θ := by
  rw [spectralEnsembleMatrix, spectralEnsembleMatrix, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [smul_smul]
  push_cast
  ring_nf

theorem injective_eigenvalues_spectralEnsemble_smul_iff
    {P : Fin N → Matrix (Fin D) (Fin D) ℂ} (hP : ∀ a, (P a).IsHermitian) {t : ℝ} (ht : t ≠ 0)
    (θ : Fin N → ℝ) :
    Function.Injective
        (isHermitian_spectralEnsembleMatrix hP (fun a => t * θ a)).eigenvalues
      ↔ Function.Injective (isHermitian_spectralEnsembleMatrix hP θ).eigenvalues := by
  have hsm : (spectralEnsembleMatrix P fun a => t * θ a)
      = ((t : ℂ)) • spectralEnsembleMatrix P θ := spectralEnsembleMatrix_smul_shellFamilySimpleSpectrum P t θ
  have hherm : (((t : ℂ)) • spectralEnsembleMatrix P θ).IsHermitian := by
    rw [← hsm]
    exact isHermitian_spectralEnsembleMatrix hP _
  have hiff := injective_eigenvalues_smul_iff (isHermitian_spectralEnsembleMatrix hP θ) ht hherm
  refine Iff.trans ?_ hiff
  rw [eigenvalues_congr_of_eq (isHermitian_spectralEnsembleMatrix hP (fun a => t * θ a))
    hherm hsm]

/-- The degeneracy locus of a family, read in Euclidean coordinates. -/
def euclideanSpectralDegenerate (P : Fin N → Matrix (Fin D) (Fin D) ℂ) :
    Set (EuclideanSpace ℝ (Fin N)) :=
  {x | MvPolynomial.eval (WithLp.ofLp x) (spectralDiscriminantPoly P) = 0}

theorem isClosed_euclideanSpectralDegenerate (P : Fin N → Matrix (Fin D) (Fin D) ℂ) :
    IsClosed (euclideanSpectralDegenerate P) := by
  have hcont : Continuous fun x : EuclideanSpace ℝ (Fin N) =>
      MvPolynomial.eval (WithLp.ofLp x) (spectralDiscriminantPoly P) :=
    (MvPolynomial.continuous_eval _).comp (PiLp.continuous_ofLp 2 _)
  exact isClosed_eq hcont continuous_const

theorem volume_euclideanSpectralDegenerate_eq_zero {P : Fin N → Matrix (Fin D) (Fin D) ℂ}
    (hdisc : spectralDiscriminantPoly P ≠ 0) :
    (volume : Measure (EuclideanSpace ℝ (Fin N))) (euclideanSpectralDegenerate P) = 0 := by
  have hmp := PiLp.volume_preserving_ofLp (Fin N)
  have hpre : euclideanSpectralDegenerate P
      = WithLp.ofLp ⁻¹'
        {θ : Fin N → ℝ | MvPolynomial.eval θ (spectralDiscriminantPoly P) = 0} := rfl
  have hmeas : MeasurableSet {θ : Fin N → ℝ |
      MvPolynomial.eval θ (spectralDiscriminantPoly P) = 0} :=
    (MvPolynomial.continuous_eval _).measurable (measurableSet_singleton (0 : ℝ))
  rw [hpre, hmp.measure_preimage hmeas.nullMeasurableSet]
  exact realMvPolynomial_zero_set_volume_fin N (spectralDiscriminantPoly P) hdisc

/-- **Almost every direction of the fixed shell of a family with one simple-spectrum member has a
simple spectrum.** -/
theorem injective_eigenvalues_spectralEnsemble_shell_ae
    {P : Fin N → Matrix (Fin D) (Fin D) ℂ} (hP : ∀ a, (P a).IsHermitian)
    (hdisc : spectralDiscriminantPoly P ≠ 0) :
    ∀ᵐ θ ∂(shellProbability (Fin N)),
      Function.Injective (isHermitian_spectralEnsembleMatrix hP θ).eigenvalues := by
  classical
  have hcone : ∀ r : ℝ, 0 < r → ∀ x ∈ euclideanSpectralDegenerate P,
      r • x ∈ euclideanSpectralDegenerate P := by
    intro r hr x hx
    have hofLp : (WithLp.ofLp (r • x)) = fun i => r * (WithLp.ofLp x) i := rfl
    show MvPolynomial.eval (WithLp.ofLp (r • x)) (spectralDiscriminantPoly P) = 0
    rw [hofLp]
    by_contra hne
    have h1 : Function.Injective (isHermitian_spectralEnsembleMatrix hP
        (fun i => r * (WithLp.ofLp x) i)).eigenvalues :=
      (injective_eigenvalues_iff_eval_spectralDiscriminantPoly_ne_zero hP _).mpr hne
    have h2 : Function.Injective (isHermitian_spectralEnsembleMatrix hP
        (WithLp.ofLp x)).eigenvalues :=
      (injective_eigenvalues_spectralEnsemble_smul_iff hP hr.ne' _).mp h1
    exact ((injective_eigenvalues_iff_eval_spectralDiscriminantPoly_ne_zero hP _).mp h2) hx
  have hbad : MeasurableSet {θ : Fin N → ℝ |
      ¬ Function.Injective (isHermitian_spectralEnsembleMatrix hP θ).eigenvalues} := by
    have hset : {θ : Fin N → ℝ |
        ¬ Function.Injective (isHermitian_spectralEnsembleMatrix hP θ).eigenvalues}
        = {θ : Fin N → ℝ | MvPolynomial.eval θ (spectralDiscriminantPoly P) = 0} := by
      ext θ
      simp only [Set.mem_setOf_eq]
      rw [injective_eigenvalues_iff_eval_spectralDiscriminantPoly_ne_zero hP θ]
      exact not_not
    rw [hset]
    exact (MvPolynomial.continuous_eval _).measurable (measurableSet_singleton (0 : ℝ))
  have hsphere : (volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere
      (shellCoefficientMap (Fin N) ⁻¹'
        {θ : Fin N → ℝ |
          ¬ Function.Injective (isHermitian_spectralEnsembleMatrix hP θ).eigenvalues}) = 0 := by
    refine toSphere_eq_zero_of_scaleInvariant
      (volume_euclideanSpectralDegenerate_eq_zero hdisc) hcone
      (hbad.preimage measurable_shellCoefficientMap) ?_
    intro θ hθ
    show MvPolynomial.eval (WithLp.ofLp ((θ : EuclideanSpace ℝ (Fin N))))
      (spectralDiscriminantPoly P) = 0
    by_contra hne
    exact hθ ((injective_eigenvalues_iff_eval_spectralDiscriminantPoly_ne_zero hP _).mpr hne)
  rw [Filter.eventually_iff, mem_ae_iff]
  have hcompl : {θ : Fin N → ℝ |
      Function.Injective (isHermitian_spectralEnsembleMatrix hP θ).eigenvalues}ᶜ
      = {θ : Fin N → ℝ |
        ¬ Function.Injective (isHermitian_spectralEnsembleMatrix hP θ).eigenvalues} := rfl
  rw [hcompl, shellProbability, Measure.smul_apply, shellCoefficientMeasure,
    Measure.map_apply measurable_shellCoefficientMap hbad, hsphere, smul_eq_mul, mul_zero]

/-- **The degenerate locus is null for the sphere measure itself.** -/
theorem toSphere_degenerate_eq_zero
    {P : Fin N → Matrix (Fin D) (Fin D) ℂ} (hP : ∀ a, (P a).IsHermitian)
    (hdisc : spectralDiscriminantPoly P ≠ 0) :
    (volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere
      (shellCoefficientMap (Fin N) ⁻¹'
        {θ : Fin N → ℝ |
          ¬ Function.Injective (isHermitian_spectralEnsembleMatrix hP θ).eigenvalues}) = 0 := by
  classical
  have hcone : ∀ r : ℝ, 0 < r → ∀ x ∈ euclideanSpectralDegenerate P,
      r • x ∈ euclideanSpectralDegenerate P := by
    intro r hr x hx
    have hofLp : (WithLp.ofLp (r • x)) = fun i => r * (WithLp.ofLp x) i := rfl
    show MvPolynomial.eval (WithLp.ofLp (r • x)) (spectralDiscriminantPoly P) = 0
    rw [hofLp]
    by_contra hne
    have h1 : Function.Injective (isHermitian_spectralEnsembleMatrix hP
        (fun i => r * (WithLp.ofLp x) i)).eigenvalues :=
      (injective_eigenvalues_iff_eval_spectralDiscriminantPoly_ne_zero hP _).mpr hne
    have h2 : Function.Injective (isHermitian_spectralEnsembleMatrix hP
        (WithLp.ofLp x)).eigenvalues :=
      (injective_eigenvalues_spectralEnsemble_smul_iff hP hr.ne' _).mp h1
    exact ((injective_eigenvalues_iff_eval_spectralDiscriminantPoly_ne_zero hP _).mp h2) hx
  have hbad : MeasurableSet {θ : Fin N → ℝ |
      ¬ Function.Injective (isHermitian_spectralEnsembleMatrix hP θ).eigenvalues} := by
    have hset : {θ : Fin N → ℝ |
        ¬ Function.Injective (isHermitian_spectralEnsembleMatrix hP θ).eigenvalues}
        = {θ : Fin N → ℝ | MvPolynomial.eval θ (spectralDiscriminantPoly P) = 0} := by
      ext θ
      simp only [Set.mem_setOf_eq]
      rw [injective_eigenvalues_iff_eval_spectralDiscriminantPoly_ne_zero hP θ]
      exact not_not
    rw [hset]
    exact (MvPolynomial.continuous_eval _).measurable (measurableSet_singleton (0 : ℝ))
  refine toSphere_eq_zero_of_scaleInvariant
    (volume_euclideanSpectralDegenerate_eq_zero hdisc) hcone
    (hbad.preimage measurable_shellCoefficientMap) ?_
  intro θ hθ
  show MvPolynomial.eval (WithLp.ofLp ((θ : EuclideanSpace ℝ (Fin N))))
    (spectralDiscriminantPoly P) = 0
  by_contra hne
  exact hθ ((injective_eigenvalues_iff_eval_spectralDiscriminantPoly_ne_zero hP _).mpr hne)

/-- **The almost sure eigenbasis datum on the fixed shell of a family.** -/
theorem isOrthoEigenBasis_injective_spectralEnsemble_shell_ae
    {P : Fin N → Matrix (Fin D) (Fin D) ℂ} (hP : ∀ a, (P a).IsHermitian)
    (hdisc : spectralDiscriminantPoly P ≠ 0) :
    ∀ᵐ θ ∂(shellProbability (Fin N)),
      IsOrthoEigenBasis (spectralEnsembleMatrix P θ)
          (hermitianEigenBasis (spectralEnsembleMatrix P θ)
            (isHermitian_spectralEnsembleMatrix hP θ))
          (isHermitian_spectralEnsembleMatrix hP θ).eigenvalues ∧
        Function.Injective (isHermitian_spectralEnsembleMatrix hP θ).eigenvalues := by
  filter_upwards [injective_eigenvalues_spectralEnsemble_shell_ae hP hdisc] with θ hθ
  exact ⟨isOrthoEigenBasis_hermitian _ (isHermitian_spectralEnsembleMatrix hP θ), hθ⟩

end

end GaloisForLFunctions.HTGeometry
