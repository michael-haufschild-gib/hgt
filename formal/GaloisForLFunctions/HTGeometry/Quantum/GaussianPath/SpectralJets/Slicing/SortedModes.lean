import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Slicing.SortedRows
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Elimination.LineLevels

/-! # Measurable weighted spectral derivatives in the sorted labeling -/

open Matrix MvPolynomial Set
namespace GaloisForLFunctions.HTGeometry.SpectralJets
noncomputable section
variable {n D : ℕ} {P : Fin n → Matrix (Fin D) (Fin D) ℂ}

/-- The rational representation defines a Borel function also at collisions. -/
def sortedMode (hP : ∀ a, (P a).IsHermitian) (p : MvPolynomial (Option (Fin n)) ℂ)
    (m : Fin D → ℝ) (w : List (Fin n)) (θ : Fin n → ℝ) : ℝ :=
  ∑ j, m j * (sortedEval hP (numerator p w) θ j / sortedEval hP (pderiv none p) θ j^(2*w.length)).re

theorem measurable_sortedMode (hP : ∀ a, (P a).IsHermitian) (p : MvPolynomial (Option (Fin n)) ℂ)
    (m : Fin D → ℝ) (w : List (Fin n)) : Measurable (sortedMode hP p m w) := by
  apply Finset.measurable_fun_sum
  intro j _
  apply measurable_const.mul
  apply Complex.measurable_re.comp
  exact (continuous_sortedEval hP _ _).measurable.div ((continuous_sortedEval hP _ _).measurable.pow_const _)

variable {R : Type*} [CommRing R]

/-- For every derivative order the regular packet locus is exactly the simple spectrum locus. -/
theorem regularPacket_sorted_iff (A : Fin n → Matrix (Fin D) (Fin D) R) (φ : R →+* ℂ)
    (hmap : (fun a => (A a).map φ) = P) (hP : ∀ a, (P a).IsHermitian) (θ : Fin n → ℝ) (s : ℕ) :
    regularPacket (realEmbed θ) (fun j => (sortedEnsembleSpectrum hP θ j : ℂ))
      ((pderiv none (map φ (characteristic A)))^s) ↔ θ ∈ simpleEnsembleLocus hP := by
  constructor
  · intro h i j he
    let E := (isHermitian_spectralEnsembleMatrix hP θ).eigenvalues
    apply (Tuple.sort E).symm.injective
    apply h.1
    change (sortedTuple E ((Tuple.sort E).symm i) : ℂ) = (sortedTuple E ((Tuple.sort E).symm j) : ℂ)
    simpa only [sortedTuple_symm_apply] using congrArg Complex.ofReal he
  · intro hθ
    refine ⟨Complex.ofReal_injective.comp (injective_sortedEnsembleSpectrum hP hθ),fun j => ?_⟩
    rw [map_pow]
    exact pow_ne_zero _ (sorted_root_differentials A φ P hmap hP θ hθ j).1

/-- The sorted rational mode is the weighted real mixed derivative at a simple spectrum. -/
theorem sortedMode_eq_real_sum (A : Fin n → Matrix (Fin D) (Fin D) R) (φ : R →+* ℂ)
    (hmap : (fun a => (A a).map φ) = P) (hP : ∀ a, (P a).IsHermitian)
    (m : Fin D → ℝ) (w : List (Fin n)) {θ : Fin n → ℝ} (hθ : θ ∈ simpleEnsembleLocus hP) :
    sortedMode hP (map φ (characteristic A)) m w θ =
      ∑ j, m j * realMixed w (fun y => sortedEnsembleSpectrum hP y j) θ := by
  apply Finset.sum_congr rfl
  intro j _
  rw [← ((sorted_root_differentials A φ P hmap hP θ hθ j).2 w).2,Complex.ofReal_re]

/-- On the simple locus the rational representation is continuous. -/
theorem continuousAt_sortedMode (A : Fin n → Matrix (Fin D) (Fin D) R) (φ : R →+* ℂ)
    (hmap : (fun a => (A a).map φ) = P) (hP : ∀ a, (P a).IsHermitian)
    (m : Fin D → ℝ) (w : List (Fin n)) {θ : Fin n → ℝ} (hθ : θ ∈ simpleEnsembleLocus hP) :
    ContinuousAt (sortedMode hP (map φ (characteristic A)) m w) θ := by
  unfold sortedMode ContinuousAt
  apply tendsto_finsetSum
  intro j _
  apply continuousAt_const.mul
  apply Complex.continuous_re.continuousAt.comp
  exact (continuous_sortedEval hP _ j).continuousAt.div
    ((continuous_sortedEval hP _ j).continuousAt.pow _) (pow_ne_zero _
      (sorted_root_differentials A φ P hmap hP θ hθ j).1)

/-- The complex rational level equation measures exactly the real sorted mode
on the simple locus. -/
theorem sortedMode_eq_rationalValue (A : Fin n → Matrix (Fin D) (Fin D) R) (φ : R →+* ℂ)
    (hmap : (fun a => (A a).map φ) = P) (hP : ∀ a, (P a).IsHermitian)
    (m : Fin D → ℝ) (w : List (Fin n)) {θ : Fin n → ℝ} (hθ : θ ∈ simpleEnsembleLocus hP) :
    let p := map φ (characteristic A)
    (sortedMode hP p m w θ : ℂ) =
      rationalValue (realEmbed θ) (fun j => (sortedEnsembleSpectrum hP θ j : ℂ)) (fun j => (m j:ℂ))
        (numerator p w) ((pderiv none p)^(2*w.length)) id := by
  intro p
  rw [sortedMode_eq_real_sum A φ hmap hP m w hθ,Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Complex.ofReal_mul,((sorted_root_differentials A φ P hmap hP θ hθ j).2 w).2]
  simp only [id_eq,map_pow,sortedEval,p,mul_div_assoc]

#print axioms measurable_sortedMode
#print axioms sortedMode_eq_rationalValue
end
end GaloisForLFunctions.HTGeometry.SpectralJets
