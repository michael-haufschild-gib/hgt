import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Slicing.SortedModes
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Slicing.CoordinateLines

/-! # Differentiating a sorted spectral mode along a real coupling line -/

open Matrix MvPolynomial Filter Topology Set
namespace GaloisForLFunctions.HTGeometry.SpectralJets
noncomputable section
variable {n D : ℕ} {R : Type*} [CommRing R] {P : Fin n → Matrix (Fin D) (Fin D) ℂ}

/-- At each simple point, differentiating the weighted mode along the line
adds its varying coordinate to the derivative word. -/
theorem hasDerivAt_sortedMode_update (A : Fin n → Matrix (Fin D) (Fin D) R) (φ : R →+* ℂ)
    (hmap : (fun a => (A a).map φ) = P) (hP : ∀ a, (P a).IsHermitian)
    (m : Fin D → ℝ) (w : List (Fin n)) (x : Fin n → ℝ) (i : Fin n) (t : ℝ)
    (ht : Function.update x i t ∈ simpleEnsembleLocus hP) :
    let p := map φ (characteristic A)
    HasDerivAt (fun u => sortedMode hP p m w (Function.update x i u))
      (sortedMode hP p m (i::w) (Function.update x i t)) t := by
  intro p
  let g (j : Fin D) (y : Fin n → ℝ) := sortedEnsembleSpectrum hP y j
  let z := Function.update x i
  have hd := differentiable_updateLine x i t
  have hj (j) : HasDerivAt (fun u => m j * realMixed w (g j) (z u))
      (m j * realMixed (i::w) (g j) (z t)) t := by
    have h := (((sorted_root_differentials A φ P hmap hP (z t) ht j).2 w).1.differentiableAt.comp t hd)
    have h' : HasDerivAt (fun u => realMixed w (g j) (z u)) (deriv (fun u => realMixed w (g j) (z u)) t) t :=
      h.hasDerivAt
    simpa only [z,deriv_realMixed_update] using h'.const_mul (m j)
  rw [sortedMode_eq_real_sum A φ hmap hP m (i::w) ht]
  apply (HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => hj j)).congr_of_eventuallyEq
  filter_upwards [hd.continuousAt.tendsto ((isOpen_simpleEnsembleLocus hP).mem_nhds ht)] with u hu
  exact sortedMode_eq_real_sum A φ hmap hP m w hu

/-- The derivative is continuous along the regular part of the line. -/
theorem continuousAt_deriv_sortedMode_update (A : Fin n → Matrix (Fin D) (Fin D) R) (φ : R →+* ℂ)
    (hmap : (fun a => (A a).map φ) = P) (hP : ∀ a, (P a).IsHermitian)
    (m : Fin D → ℝ) (w : List (Fin n)) (x : Fin n → ℝ) (i : Fin n) (t : ℝ)
    (ht : Function.update x i t ∈ simpleEnsembleLocus hP) :
    ContinuousAt (deriv (fun u => sortedMode hP (map φ (characteristic A)) m w (Function.update x i u))) t := by
  have hc := (differentiable_updateLine x i t).continuousAt
  apply ((continuousAt_sortedMode A φ hmap hP m (i::w) ht).comp hc).congr_of_eventuallyEq
  filter_upwards [hc.tendsto ((isOpen_simpleEnsembleLocus hP).mem_nhds ht)] with u hu
  exact (hasDerivAt_sortedMode_update A φ hmap hP m w x i u hu).deriv

#print axioms hasDerivAt_sortedMode_update
#print axioms continuousAt_deriv_sortedMode_update
end
end GaloisForLFunctions.HTGeometry.SpectralJets
