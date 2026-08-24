import GaloisForLFunctions.RHTower.XiShiftEulerUncancelledPoleWitness
import GaloisForLFunctions.RHTower.XiEulerSafePairedRationalCriterion

/-!
# Gaussian-rational Euler-region shifted-Xi witnesses

Gaussian-rational nodes remain an accumulation uniqueness set inside every Euler sampling
half-plane. Thus one uncancelled shifted pole has a finite negative-inertia witness whose every
sample coordinate is rational.
-/

open Complex Set Topology Filter
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- Gaussian-rational points lying in the shifted Euler sampling half-plane. -/
def xiShiftEulerGaussianRationalSet (omega : ℝ) : Set ℂ :=
  xiShiftEulerUpperSet omega ∩ gaussianRationalSet

/-- Gaussian-rational Euler nodes accumulate at an interior point. -/
theorem xiShiftEulerGaussianRationalSet_accumulates (omega : ℝ) :
    ∃ p : ℂ, p ∈ xiShiftEulerUpperSet omega ∧
      ∃ᶠ z in nhdsWithin p ({p}ᶜ),
        z ∈ xiShiftEulerGaussianRationalSet omega := by
  obtain ⟨p, hpU⟩ := xiShiftEulerUpperSet_nonempty omega
  have hdense : Dense (gaussianRationalSet ∩ ({p}ᶜ : Set ℂ)) :=
    dense_gaussianRationalSet.inter_of_isOpen_right
      (dense_compl_singleton p) isOpen_compl_singleton
  have hpclose : p ∈ closure
      (xiShiftEulerUpperSet omega ∩ (gaussianRationalSet ∩ ({p}ᶜ : Set ℂ))) :=
    hdense.open_subset_closure_inter (isOpen_xiShiftEulerUpperSet omega) hpU
  have hfreq : ∃ᶠ z in nhds p,
      z ∈ xiShiftEulerUpperSet omega ∩
        (gaussianRationalSet ∩ ({p}ᶜ : Set ℂ)) :=
    mem_closure_iff_frequently.mp hpclose
  refine ⟨p, hpU, frequently_nhdsWithin_iff.mpr ?_⟩
  exact hfreq.mono fun z hz => ⟨⟨hz.1, hz.2.1⟩, hz.2.2⟩

/-- One uncancelled shifted pole remains one negative square after restricting every sample point
to Gaussian rationals in the Euler region. -/
theorem eulerXiShiftPick_gaussianRational_has_negativeDimension_one_of_uncancelled
    {omega : ℝ} (homega : 0 < omega) (q : XiShiftRightZeroCopy omega)
    (huncancel : suzukiCanonicalE omega (-xiShiftPoleCoordinate omega q) ≠ 0) :
    HasFiniteKernelNegativeDimension
      (fun z w : xiShiftEulerGaussianRationalSet omega =>
        eulerXiShiftPick omega z.1 w.1) 1 := by
  obtain ⟨p, hpU, hfreq⟩ := xiShiftEulerGaussianRationalSet_accumulates omega
  have hsub : xiShiftEulerGaussianRationalSet omega ⊆ upperHalfPlaneSet := by
    intro z hz
    exact xiShiftEulerUpperSet_subset_upperHalfPlane homega hz.1
  have hregular : ∀ z ∈ xiShiftEulerGaussianRationalSet omega,
      suzukiCanonicalE omega z ≠ 0 := by
    intro z hz
    exact suzukiCanonicalE_ne_zero_of_mem_xiShiftEulerUpperSet homega z hz.1
  have hglobal : HasFiniteKernelNegativeDimension
      (xiShiftRegularUpperKernel omega) 1 :=
    (xiShiftRegularUpperKernel_openRegion_negativeDimension_iff
      omega (xiShiftEulerUpperSet omega)
      (isOpen_xiShiftEulerUpperSet omega)
      (xiShiftEulerUpperSet_subset_upperHalfPlane homega)
      (suzukiCanonicalE_ne_zero_of_mem_xiShiftEulerUpperSet homega)
      (xiShiftEulerUpperSet_nonempty omega) 1).mp
        (by simpa only [eulerXiShiftPick_eq_upperHalfPlaneSchurKernel] using
          eulerXiShiftPick_has_negativeDimension_one_of_uncancelled homega q huncancel)
  have hlocal :=
    (xiShiftRegularUpperKernel_accumulationSet_negativeDimension_iff
      omega (xiShiftEulerGaussianRationalSet omega) hsub hregular p
      (xiShiftEulerUpperSet_subset_upperHalfPlane homega hpU) hfreq 1).mpr hglobal
  simpa only [eulerXiShiftPick_eq_upperHalfPlaneSchurKernel] using hlocal

/-- An uncancelled shifted pole has a finite negative-inertia Euler Pick witness with rational real
and imaginary sample coordinates. -/
theorem exists_gaussianRational_eulerXiShiftPick_sample_negIndex_pos_of_uncancelled
    {omega : ℝ} (homega : 0 < omega) (q : XiShiftRightZeroCopy omega)
    (huncancel : suzukiCanonicalE omega (-xiShiftPoleCoordinate omega q) ≠ 0) :
    ∃ (N : ℕ) (w : Fin N → xiShiftEulerGaussianRationalSet omega),
      0 < hermNegIndex (Matrix.of fun i j =>
        eulerXiShiftPick omega (w j).1 (w i).1) := by
  obtain ⟨N, w, hle⟩ := exists_finite_sample_negIndex_ge
    (fun z w : xiShiftEulerGaussianRationalSet omega =>
      eulerXiShiftPick omega z.1 w.1)
    (eulerXiShiftPick_gaussianRational_has_negativeDimension_one_of_uncancelled
      homega q huncancel)
  exact ⟨N, w, lt_of_lt_of_le Nat.zero_lt_one hle⟩

end

end RHTower
