import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SpectralApproximation.NearbySpectrum
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.Width

/-! # Moving spectral edges and levels under a local perturbation -/

open Finset Matrix Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.FirstAscent.EnergyMesh
noncomputable section

variable {I : Type*} [Fintype I] [Nonempty I] [DecidableEq I]
local instance {J : Type*} [Fintype J] [DecidableEq J] : CStarAlgebra (Matrix J J ℂ) where

abbrev EnergyOperator (I : Type*) [Fintype I] [DecidableEq I] := selfAdjoint (Matrix I I ℂ)

def upper (H : EnergyOperator I) := univ.sup' univ_nonempty H.2.isHermitian.eigenvalues
def lower (H : EnergyOperator I) := univ.inf' univ_nonempty H.2.isHermitian.eigenvalues

/-- Every eigenvalue moves by at most the perturbation norm to the nearest
level of the other matrix. Finiteness upgrades the open resolvent bound
to a closed bound. -/
theorem matching (H K : EnergyOperator I) (j : I) :
    ∃ i, |H.2.isHermitian.eigenvalues j-K.2.isHermitian.eigenvalues i| ≤ ‖H.val-K.val‖ := by
  let E := H.2.isHermitian.eigenvalues
  let F := K.2.isHermitian.eigenvalues
  let d (i : I) := |E j-F i|
  obtain ⟨i,_,hi⟩ := exists_mem_eq_inf' univ_nonempty d
  refine ⟨i,?_⟩
  change d i ≤ ‖H.val-K.val‖
  by_contra! h
  have hz : ((E j : ℝ) : ℂ) ∈ spectrum ℂ H.val := by
    rw [H.2.isHermitian.spectrum_eq_image_range]
    exact ⟨_,mem_range_self j,rfl⟩
  letI : IsStarNormal K.val := K.2.isStarNormal
  obtain ⟨z,hz',hd⟩ := SpectralApproximation.nearby_spectral_point
    (U:=H.val) (V:=K.val) (z:=((E j:ℝ):ℂ)) (r:=d i) hz h
  rw [K.2.isHermitian.spectrum_eq_image_range] at hz'
  obtain ⟨_,⟨k,rfl⟩,rfl⟩ := hz'
  change ‖((E j : ℝ):ℂ)-((F k : ℝ):ℂ)‖ < d i at hd
  rw [←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] at hd
  apply hd.not_ge
  change d i ≤ d k
  rw [←hi]
  exact inf'_le d (mem_univ k)

private theorem upper_le (H K : EnergyOperator I) :
    upper H ≤ upper K+‖H.val-K.val‖ := by
  apply sup'_le
  intro i _
  obtain ⟨j,hj⟩ := matching H K i
  have he : K.2.isHermitian.eigenvalues j ≤ upper K := le_sup' _ (mem_univ j)
  linarith only [(abs_le.mp hj).2,he]

private theorem lower_le (H K : EnergyOperator I) :
    lower K ≤ lower H+‖H.val-K.val‖ := by
  obtain ⟨i,_,hi⟩ := exists_mem_eq_inf' univ_nonempty H.2.isHermitian.eigenvalues
  obtain ⟨j,hj⟩ := matching H K i
  have he : lower K ≤ K.2.isHermitian.eigenvalues j := inf'_le _ (mem_univ j)
  change univ.inf' univ_nonempty H.2.isHermitian.eigenvalues=_ at hi
  change lower H=H.2.isHermitian.eigenvalues i at hi
  rw [hi]
  linarith only [(abs_le.mp hj).1,he]

theorem upper_stability (H K : EnergyOperator I) : |upper H-upper K| ≤ ‖H.val-K.val‖ := by
  have h := upper_le K H
  rw [norm_sub_rev] at h
  exact abs_le.mpr ⟨by linarith only [h],by linarith only [upper_le H K]⟩

theorem lower_stability (H K : EnergyOperator I) : |lower H-lower K| ≤ ‖H.val-K.val‖ := by
  have h := lower_le K H
  rw [norm_sub_rev] at h
  exact abs_le.mpr ⟨by linarith only [lower_le H K],by linarith only [h]⟩

#print axioms matching
end
end GaloisForLFunctions.HTGeometry.FirstAscent.EnergyMesh
