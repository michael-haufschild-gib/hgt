import GaloisForLFunctions.HTGeometry.ActivePauliShellCliffordLaw
import GaloisForLFunctions.HTGeometry.ShellSimpleSpectrum

/-!
# Spectral law of the corrected active Pauli shell

This module transports the active Pauli shell to the numbered coordinates used by the corpus's
spectral genericity theorem.  It proves exact Hamiltonian rate, product-Clifford covariance and
shell invariance, and almost-sure simple spectrum on the corrected active measure.
-/

open Matrix MeasureTheory ProbabilityTheory
open QuantumAlg

noncomputable section

namespace GaloisForLFunctions.HTGeometry

abbrev ActivePauliCoordinate (n q : ℕ) :=
  Fin (Fintype.card (PauliTracelessLabel n q))

/-- Corrected active Hamiltonian in the numbered coordinates used by spectral genericity. -/
def activePauliFinHamiltonian {n q : ℕ} (p : ActivePauliCoordinate n q → ℝ) :
    Matrix (Fin n → Bool) (Fin n → Bool) ℂ :=
  activePauliHamiltonian
    (fun P => (p (pauliTracelessLabelEquivFin n q P) : ℂ))

theorem activePauliFinHamiltonian_eq_tracelessFinEval {n q : ℕ}
    (p : ActivePauliCoordinate n q → ℝ) :
    activePauliFinHamiltonian p =
      (pauliTracelessFinPolynomialMatrix n q).map
        (MvPolynomial.eval₂Hom (RingHom.id ℂ) fun t => (p t : ℂ)) := by
  rw [map_eval_pauliTracelessFinPolynomialMatrix]
  ext x y
  rw [eval_pauliTracelessPolynomialMatrix]
  simp [activePauliFinHamiltonian, activePauliHamiltonian, Matrix.sum_apply,
    Matrix.smul_apply]

/-- Every corrected numbered-shell point has the same exact Hamiltonian rate. -/
theorem frobSq_activePauliFinShellHamiltonian {n q : ℕ}
    (θ : Metric.sphere (0 : EuclideanSpace ℝ (ActivePauliCoordinate n q)) 1) :
    frobSq (activePauliFinHamiltonian (shellCoefficientMap (ActivePauliCoordinate n q) θ)) =
      2 ^ n := by
  rw [activePauliFinHamiltonian, frobSq_activePauliHamiltonian]
  have hnorm : ‖(θ : EuclideanSpace ℝ (ActivePauliCoordinate n q))‖ = 1 := by
    simpa [dist_eq_norm] using θ.property
  have hsq := congrArg (fun x : ℝ => x ^ (2 : ℕ)) hnorm
  rw [EuclideanSpace.norm_sq_eq] at hsq
  have hsum : (∑ P : PauliTracelessLabel n q,
      ‖((shellCoefficientMap (ActivePauliCoordinate n q) θ
        (pauliTracelessLabelEquivFin n q P) : ℝ) : ℂ)‖ ^ (2 : ℕ)) = 1 := by
    rw [Fintype.sum_equiv (pauliTracelessLabelEquivFin n q)
      (fun P => ‖((shellCoefficientMap (ActivePauliCoordinate n q) θ
        (pauliTracelessLabelEquivFin n q P) : ℝ) : ℂ)‖ ^ (2 : ℕ))
      (fun t => ‖((shellCoefficientMap (ActivePauliCoordinate n q) θ t : ℝ) : ℂ)‖ ^ (2 : ℕ))
      (fun _ => rfl)]
    simpa [shellCoefficientMap, Real.norm_eq_abs, sq_abs] using hsq
  rw [hsum, mul_one]

/-- Product-Clifford permutation transported to numbered active coordinates. -/
def productCliffordActiveFinRelabelEquiv {n q : ℕ}
    (g : Fin n → QubitTwoDesign.BinaryOctahedral) :
    Equiv.Perm (ActivePauliCoordinate n q) :=
  (pauliTracelessLabelEquivFin n q).symm.trans
    ((productCliffordActiveRelabelEquiv (q := q) g).trans
      (pauliTracelessLabelEquivFin n q))

/-- Signed product-Clifford action in numbered active coordinates. -/
def activeFinCliffordCoefficientMap {n q : ℕ}
    (g : Fin n → QubitTwoDesign.BinaryOctahedral)
    (p : ActivePauliCoordinate n q → ℝ) : ActivePauliCoordinate n q → ℝ :=
  fun t => productCliffordSign g
      ((pauliTracelessLabelEquivFin n q).symm
        ((productCliffordActiveFinRelabelEquiv (q := q) g).symm t)).1 *
    p ((productCliffordActiveFinRelabelEquiv (q := q) g).symm t)

/-- Corrected active Hamiltonians are covariant under the numbered signed permutation. -/
theorem activePauliFinHamiltonian_conj {n q : ℕ}
    (g : Fin n → QubitTwoDesign.BinaryOctahedral)
    (p : ActivePauliCoordinate n q → ℝ) :
    finiteProductCliffordGate g * activePauliFinHamiltonian p *
        (finiteProductCliffordGate g)ᴴ =
      activePauliFinHamiltonian (activeFinCliffordCoefficientMap g p) := by
  rw [activePauliFinHamiltonian, activePauliHamiltonian_conj]
  congr 1
  funext Q
  simp [activeCliffordCoefficientMap, activeFinCliffordCoefficientMap,
    productCliffordActiveFinRelabelEquiv]

/-- Numbered corrected shell law is invariant under product-Clifford conjugation. -/
theorem measurePreserving_activeFinCliffordCoefficientMap_shell {n q : ℕ}
    (g : Fin n → QubitTwoDesign.BinaryOctahedral) :
    MeasurePreserving (activeFinCliffordCoefficientMap (q := q) g)
      (shellProbability (ActivePauliCoordinate n q))
      (shellProbability (ActivePauliCoordinate n q)) := by
  exact measurePreserving_signedPerm_shellProbability
    (productCliffordActiveFinRelabelEquiv (q := q) g).symm
    (ε := fun t => productCliffordSign g
      ((pauliTracelessLabelEquivFin n q).symm
        ((productCliffordActiveFinRelabelEquiv (q := q) g).symm t)).1)
    (fun _ => productCliffordSign_eq_one_or_neg_one g _)

theorem isHermitian_activePauliFinHamiltonian {n q : ℕ}
    (p : ActivePauliCoordinate n q → ℝ) :
    (activePauliFinHamiltonian p).IsHermitian := by
  rw [activePauliFinHamiltonian_eq_tracelessFinEval]
  exact isHermitian_pauliTracelessFinEval p

theorem continuous_activePauliFinHamiltonian {n q : ℕ} :
    Continuous (activePauliFinHamiltonian :
      (ActivePauliCoordinate n q → ℝ) → Matrix (Fin n → Bool) (Fin n → Bool) ℂ) := by
  refine continuous_pi fun x => continuous_pi fun y => ?_
  simp only [activePauliFinHamiltonian, activePauliHamiltonian, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul]
  exact continuous_finsetSum _ fun P _ =>
    (Complex.continuous_ofReal.comp
      (continuous_apply (pauliTracelessLabelEquivFin n q P))).mul continuous_const

theorem measurable_activePauliFinHamiltonian_entry {n q : ℕ} (x y : Fin n → Bool) :
    Measurable fun p : ActivePauliCoordinate n q → ℝ => activePauliFinHamiltonian p x y :=
  ((continuous_apply y).comp ((continuous_apply x).comp
    (continuous_activePauliFinHamiltonian (n := n) (q := q)))).measurable

theorem activePauliFinHamiltonian_smul {n q : ℕ} (t : ℝ)
    (p : ActivePauliCoordinate n q → ℝ) :
    activePauliFinHamiltonian (fun i => t * p i) =
      (t : ℂ) • activePauliFinHamiltonian p := by
  rw [activePauliFinHamiltonian, activePauliFinHamiltonian,
    activePauliHamiltonian, activePauliHamiltonian, Finset.smul_sum]
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [smul_smul]
  congr 1
  push_cast
  ring

theorem injective_eigenvalues_activePauliFinHamiltonian_smul_iff {n q : ℕ}
    {t : ℝ} (ht : t ≠ 0) (p : ActivePauliCoordinate n q → ℝ) :
    Function.Injective
        (isHermitian_activePauliFinHamiltonian (fun i => t * p i)).eigenvalues ↔
      Function.Injective (isHermitian_activePauliFinHamiltonian p).eigenvalues := by
  have hscaled : (((t : ℂ)) • activePauliFinHamiltonian p).IsHermitian := by
    rw [← activePauliFinHamiltonian_smul t p]
    exact isHermitian_activePauliFinHamiltonian _
  have heig :
      (isHermitian_activePauliFinHamiltonian (fun i => t * p i)).eigenvalues =
        hscaled.eigenvalues :=
    isHermitian_eigenvalues_congr _ _ (activePauliFinHamiltonian_smul t p)
  rw [heig]
  exact injective_eigenvalues_smul_iff (isHermitian_activePauliFinHamiltonian p) ht hscaled

/-- Degenerate corrected active Hamiltonians form a closed coefficient set. -/
theorem isClosed_activePauliFin_degenerate {n q : ℕ} :
    IsClosed {p : ActivePauliCoordinate n q → ℝ |
      ¬ Function.Injective (isHermitian_activePauliFinHamiltonian p).eigenvalues} :=
  isClosed_repeatedSpectrum continuous_activePauliFinHamiltonian
    isHermitian_activePauliFinHamiltonian

theorem injective_activePauliFin_iff_tracelessFinEval {n q : ℕ}
    (p : ActivePauliCoordinate n q → ℝ) :
    Function.Injective (isHermitian_activePauliFinHamiltonian p).eigenvalues ↔
      Function.Injective (isHermitian_pauliTracelessFinEval p).eigenvalues := by
  have heig := isHermitian_eigenvalues_congr
    (isHermitian_activePauliFinHamiltonian p)
    (isHermitian_pauliTracelessFinEval p)
    (activePauliFinHamiltonian_eq_tracelessFinEval p)
  rw [heig]

/-- Lebesgue-almost every corrected active coefficient vector has simple spectrum. -/
theorem volume_activePauliFin_degenerate_eq_zero (n : ℕ) {q : ℕ} (hq : 2 ≤ q) :
    (volume : Measure (ActivePauliCoordinate n q → ℝ))
      {p | ¬ Function.Injective (isHermitian_activePauliFinHamiltonian p).eigenvalues} = 0 := by
  obtain ⟨-, -, hvolume, hgeneric⟩ :=
    pauliTraceless_simple_and_projectivelyIndependent_generically n hq
  refine measure_mono_null (fun p hp => ?_) hvolume
  intro hmem
  exact hp ((injective_activePauliFin_iff_tracelessFinEval p).mpr (hgeneric p hmem).1)

/-- Degenerate active Hamiltonians in Euclidean shell coordinates. -/
def euclideanActivePauliFinDegenerate (n q : ℕ) :
    Set (EuclideanSpace ℝ (ActivePauliCoordinate n q)) :=
  {x | ¬ Function.Injective
    (isHermitian_activePauliFinHamiltonian (WithLp.ofLp x)).eigenvalues}

theorem measurableSet_euclideanActivePauliFinDegenerate (n q : ℕ) :
    MeasurableSet (euclideanActivePauliFinDegenerate n q) := by
  exact (isClosed_activePauliFin_degenerate (n := n) (q := q)).measurableSet.preimage
    (PiLp.continuous_ofLp 2 _).measurable

theorem volume_euclideanActivePauliFinDegenerate_eq_zero (n : ℕ) {q : ℕ}
    (hq : 2 ≤ q) :
    (volume : Measure (EuclideanSpace ℝ (ActivePauliCoordinate n q)))
      (euclideanActivePauliFinDegenerate n q) = 0 := by
  have hmp := PiLp.volume_preserving_ofLp (ActivePauliCoordinate n q)
  change (volume : Measure (EuclideanSpace ℝ (ActivePauliCoordinate n q)))
    ((fun x : EuclideanSpace ℝ (ActivePauliCoordinate n q) => WithLp.ofLp x) ⁻¹'
      {p | ¬ Function.Injective
        (isHermitian_activePauliFinHamiltonian p).eigenvalues}) = 0
  rw [hmp.measure_preimage
    (isClosed_activePauliFin_degenerate (n := n) (q := q)).measurableSet.nullMeasurableSet]
  exact volume_activePauliFin_degenerate_eq_zero n hq

/-- Almost every point of the corrected active shell has simple spectrum. -/
theorem injective_eigenvalues_activePauliFin_shell_ae (n : ℕ) {q : ℕ} (hq : 2 ≤ q) :
    ∀ᵐ p ∂(shellProbability (ActivePauliCoordinate n q)),
      Function.Injective (isHermitian_activePauliFinHamiltonian p).eigenvalues := by
  have hcone : ∀ r : ℝ, 0 < r → ∀ x ∈ euclideanActivePauliFinDegenerate n q,
      r • x ∈ euclideanActivePauliFinDegenerate n q := by
    intro r hr x hx
    have hofLp : WithLp.ofLp (r • x) =
        fun i => r * WithLp.ofLp x i := rfl
    show ¬ Function.Injective
      (isHermitian_activePauliFinHamiltonian (WithLp.ofLp (r • x))).eigenvalues
    rw [hofLp]
    intro hinj
    exact hx ((injective_eigenvalues_activePauliFinHamiltonian_smul_iff hr.ne' _).mp hinj)
  have hsphere : (volume : Measure (EuclideanSpace ℝ (ActivePauliCoordinate n q))).toSphere
      {θ | (θ : EuclideanSpace ℝ (ActivePauliCoordinate n q)) ∈
        euclideanActivePauliFinDegenerate n q} = 0 := by
    refine toSphere_eq_zero_of_scaleInvariant
      (volume_euclideanActivePauliFinDegenerate_eq_zero n hq) hcone
      ((measurableSet_euclideanActivePauliFinDegenerate n q).preimage measurable_subtype_coe) ?_
    intro θ hθ
    exact hθ
  rw [Filter.eventually_iff, mem_ae_iff]
  have hbad : MeasurableSet {p : ActivePauliCoordinate n q → ℝ |
      ¬ Function.Injective (isHermitian_activePauliFinHamiltonian p).eigenvalues} :=
    (isClosed_activePauliFin_degenerate (n := n) (q := q)).measurableSet
  have hsphere' : (volume : Measure (EuclideanSpace ℝ (ActivePauliCoordinate n q))).toSphere
      (shellCoefficientMap (ActivePauliCoordinate n q) ⁻¹'
        {p | ¬ Function.Injective
          (isHermitian_activePauliFinHamiltonian p).eigenvalues}) = 0 := hsphere
  rw [show {p : ActivePauliCoordinate n q → ℝ |
      Function.Injective (isHermitian_activePauliFinHamiltonian p).eigenvalues}ᶜ =
      {p | ¬ Function.Injective
        (isHermitian_activePauliFinHamiltonian p).eigenvalues} by rfl]
  rw [shellProbability, Measure.smul_apply, shellCoefficientMeasure,
    Measure.map_apply measurable_shellCoefficientMap hbad, hsphere', smul_eq_mul, mul_zero]

/-- Almost-sure orthonormal eigenbasis with simple spectrum on the corrected active shell. -/
theorem isOrthoEigenBasis_injective_activePauliFin_shell_ae (n : ℕ) {q : ℕ} (hq : 2 ≤ q) :
    ∀ᵐ p ∂(shellProbability (ActivePauliCoordinate n q)),
      IsOrthoEigenBasis (activePauliFinHamiltonian p)
          (hermitianEigenBasis (activePauliFinHamiltonian p)
            (isHermitian_activePauliFinHamiltonian p))
          (isHermitian_activePauliFinHamiltonian p).eigenvalues ∧
        Function.Injective (isHermitian_activePauliFinHamiltonian p).eigenvalues := by
  filter_upwards [injective_eigenvalues_activePauliFin_shell_ae n hq] with p hp
  exact ⟨isOrthoEigenBasis_hermitian _ (isHermitian_activePauliFinHamiltonian p), hp⟩

end GaloisForLFunctions.HTGeometry
