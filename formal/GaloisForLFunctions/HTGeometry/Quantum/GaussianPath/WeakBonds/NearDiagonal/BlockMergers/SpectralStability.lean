import GaloisForLFunctions.HTGeometry.KroneckerSumSpectrum
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SpectralApproximation.NearbySpectrum

/-! # Stability of the gaps after restoring a joining bond -/
open Matrix Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.WeakBonds.NearDiagonal.BlockMergers
noncomputable section
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- Every separated reference level has a distinct neighbor in the
perturbed Hermitian spectrum. Equal dimensions exhaust all new levels. -/
theorem stable_spacing (U V : Matrix I I ℂ) (hV : V.IsHermitian) (d : I→ℝ)
    (hs : ∀ i, (d i:ℂ)∈spectrum ℂ U) {g : ℝ} (hg : 0<g)
    (hsep : ∀ i j, i≠j → g≤|d i-d j|) (hd : ‖U-V‖<g/4) :
    ∀ i j, i≠j → g/2 ≤ |hV.eigenvalues i-hV.eigenvalues j| := by
  classical
  letI : CStarAlgebra (Matrix I I ℂ) := {}
  letI : IsStarNormal V := hV.isSelfAdjoint.isStarNormal
  have hnear (i : I) : ∃ j, |d i-hV.eigenvalues j|<g/4 := by
    obtain ⟨w,hw,hw'⟩ := SpectralApproximation.nearby_spectral_point (hs i) hd
    rw [hV.spectrum_eq_image_range] at hw
    obtain ⟨_,⟨j,rfl⟩,rfl⟩ := hw
    change ‖((d i:ℝ):ℂ)-((hV.eigenvalues j:ℝ):ℂ)‖<g/4 at hw'
    rw [←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] at hw'
    exact ⟨j,hw'⟩
  choose f hf using hnear
  have hpair i j : |d i-d j| ≤
      |d i-hV.eigenvalues (f i)|+|hV.eigenvalues (f i)-hV.eigenvalues (f j)|+
        |d j-hV.eigenvalues (f j)| := by
    simpa only [Real.dist_eq,abs_sub_comm (hV.eigenvalues (f j)) (d j)] using
      dist_triangle4 (d i) (hV.eigenvalues (f i)) (hV.eigenvalues (f j)) (d j)
  have hinj : Function.Injective f := by
    intro i j he
    by_contra hij
    have h := hpair i j
    rw [he,sub_self,abs_zero,add_zero] at h
    have hi := hf i
    rw [he] at hi
    linarith only [h,hsep i j hij,hi,hf j,hg]
  intro i j hij
  obtain ⟨x,rfl⟩ := Finite.surjective_of_injective hinj i
  obtain ⟨y,rfl⟩ := Finite.surjective_of_injective hinj j
  have hxy : x≠y := fun h => hij (congrArg f h)
  linarith only [hsep x y hxy,hpair x y,hf x,hf y]

/-- A seam perturbation smaller than a quarter of the separated sum
gap preserves at least half that gap in the complete joined spectrum. -/
theorem restored_bond_spacing {A : Matrix I I ℂ} {B : Matrix J J ℂ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (V : Matrix (I×J) (I×J) ℂ) (hV : V.IsHermitian) {g : ℝ} (hg : 0<g)
    (hsep : ∀ u v : I×J, u≠v → g ≤ |(hA.eigenvalues u.1+hB.eigenvalues u.2)-
       (hA.eigenvalues v.1+hB.eigenvalues v.2)|) (hd : ‖kroneckerSum A B-V‖<g/4) :
    ∀ i j, i≠j → g/2 ≤ |hV.eigenvalues i-hV.eigenvalues j| := by
  apply stable_spacing _ V hV (fun p : I×J => hA.eigenvalues p.1+hB.eigenvalues p.2) _ hg hsep hd
  intro i
  rw [(isHermitian_kroneckerSum hA hB).spectrum_eq_image_range,
    range_eigenvalues_kroneckerSum hA hB]
  exact ⟨_,⟨i,rfl⟩,rfl⟩

#print axioms restored_bond_spacing
end
end GaloisForLFunctions.HTGeometry.WeakBonds.NearDiagonal.BlockMergers
