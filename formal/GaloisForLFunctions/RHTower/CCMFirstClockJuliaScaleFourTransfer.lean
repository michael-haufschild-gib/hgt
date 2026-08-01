import GaloisForLFunctions.HTGeometry.JuliaDefectSpectralEquilibrium
import GaloisForLFunctions.RHTower.CCMFirstClockBlockSubdivisionTransfer

/-!
# CCM first-clock Julia scale-four transfer

The critical centered log-Beta/Dirichlet Lévy density, the scalar Gamma--Julia equilibrium law,
and the CCM odd block-Fock Gamma density are three presentations of one scale-four object.

This file proves their exact change of coordinates.  The resulting innovation is strictly
positive and gives a finite multiscale decomposition of the CCM archimedean density.  No RH
statement is assumed or concluded: the theorem isolates a positive Gamma-side resource and makes
the remaining arithmetic sign obstruction explicit.
-/

namespace RHTower

noncomputable section

open HTGeometry

/-- The critical symmetric log-Beta/Dirichlet radial density is the CCM `1 mod 4` block-Fock
resolvent at doubled aperture, multiplied by the complementary `3 mod 4` sector. -/
theorem criticalDirichletLevyRadialDensity_eq_ccmArchimedean
    {x : ℝ} (hx : 0 < x) :
    criticalDirichletLevyRadialDensity x =
      (1 + Real.exp (-2 * x)) * ccmPublishedArchimedeanDensity (2 * x) := by
  have h2x : 0 < 2 * x := by linarith
  have hden2 : 1 - Real.exp (-2 * x) ≠ 0 :=
    (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))).ne'
  have hden4 : 1 - Real.exp (-4 * x) ≠ 0 :=
    (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))).ne'
  have hsq : Real.exp (-4 * x) = Real.exp (-2 * x) * Real.exp (-2 * x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [criticalDirichletLevyRadialDensity_eq_exp_neg_div hx,
    ccmPublishedArchimedeanDensity_eq_exp_neg_half_div h2x,
    show -(2 * x) / 2 = -x by ring,
    show -2 * (2 * x) = -4 * x by ring,
    ← mul_div_assoc, hsq]
  have hden4' :
      1 - Real.exp (-2 * x) * Real.exp (-2 * x) ≠ 0 := by
    rw [← hsq]
    exact hden4
  rw [div_eq_div_iff hden2 hden4']
  ring_nf

/-- Equivalent block-Fock form: the full odd Dirichlet ladder is the sum of the `1 mod 4` and
`3 mod 4` sectors of the CCM block ladder. -/
theorem criticalDirichletLevyRadialDensity_eq_oddBlockFock
    {x : ℝ} (hx : 0 < x) :
    criticalDirichletLevyRadialDensity x =
      (1 + Real.exp (-2 * x)) *
        oddBlockFockRadialSum (Real.exp (-x)) := by
  rw [criticalDirichletLevyRadialDensity_eq_ccmArchimedean hx]
  congr 1
  have h := oddBlockFockRadialSum_exp_eq_archimedeanDensity
    (h := 2 * x) (by linarith)
  simpa only [show -(2 * x) / 2 = -x by ring] using h.symm

/-- Inverse coordinate: the literal CCM archimedean density is a normalized critical Dirichlet
radial density. -/
theorem ccmPublishedArchimedeanDensity_eq_criticalDirichlet
    {h : ℝ} (hh : 0 < h) :
    ccmPublishedArchimedeanDensity h =
      criticalDirichletLevyRadialDensity (h / 2) /
        (1 + Real.exp (-h)) := by
  have hhalf : 0 < h / 2 := by linarith
  have hw := criticalDirichletLevyRadialDensity_eq_ccmArchimedean hhalf
  rw [show -2 * (h / 2) = -h by ring,
    show 2 * (h / 2) = h by ring] at hw
  have hden : 1 + Real.exp (-h) ≠ 0 := by positivity
  rw [eq_div_iff hden, hw]
  ring

/-- **Exact first-clock Dirichlet coordinate.**  The complete continuous Gamma--polar reflection
gap is the difference of two normalized critical Dirichlet densities plus the explicit polar
reflection.  The scale-four Julia telescope applies separately to both Dirichlet terms. -/
theorem ccmFirstClockContinuousReflectionGap_eq_dirichletPolar
    {L h : ℝ} (hL : 0 < L) (hh : 0 < h) :
    ccmFirstClockContinuousReflectionGap L h =
      criticalDirichletLevyRadialDensity (h / 2) /
          (1 + Real.exp (-h)) -
        criticalDirichletLevyRadialDensity ((h + L / 2) / 2) /
          (1 + Real.exp (-(h + L / 2))) +
        2 * (Real.cosh ((h + L / 2) / 2) - Real.cosh (h / 2)) := by
  rw [ccmFirstClockContinuousReflectionGap,
    ccmFirstClockContinuousSourceDensity,
    ccmFirstClockContinuousSourceDensity,
    ccmPublishedArchimedeanDensity_eq_criticalDirichlet hh,
    ccmPublishedArchimedeanDensity_eq_criticalDirichlet
      (by linarith : 0 < h + L / 2)]
  ring

/-- **CCM--Julia scale-four residue law.**  The positive Julia innovation is exactly the
scale-four subtraction of two explicitly weighted CCM odd block-Fock Gamma densities. -/
theorem juliaScaleFourInnovationDensity_eq_ccmResidue
    {x : ℝ} (hx : 0 < x) :
    juliaScaleFourInnovationDensity x =
      (1 + Real.exp (-2 * x)) * ccmPublishedArchimedeanDensity (2 * x) -
        4 * (1 + Real.exp (-8 * x)) * ccmPublishedArchimedeanDensity (8 * x) := by
  rw [juliaScaleFourInnovationDensity,
    criticalDirichletLevyRadialDensity_eq_ccmArchimedean hx,
    criticalDirichletLevyRadialDensity_eq_ccmArchimedean
      (by linarith : 0 < 4 * x)]
  ring_nf

/-- The weighted CCM Gamma density contracts strictly by a factor four under one fourfold radial
dilation.  This is the CCM coordinate form of strict Julia Lévy positivity. -/
theorem ccmArchimedean_scaleFour_strictContraction
    {x : ℝ} (hx : 0 < x) :
    4 * (1 + Real.exp (-8 * x)) * ccmPublishedArchimedeanDensity (8 * x) <
      (1 + Real.exp (-2 * x)) * ccmPublishedArchimedeanDensity (2 * x) := by
  have hpos := juliaScaleFourInnovationDensity_pos hx
  rw [juliaScaleFourInnovationDensity_eq_ccmResidue hx] at hpos
  linarith

/-- **Finite CCM Julia-innovation tower.**  At every finite scale resolution, the weighted CCM
Gamma density is exactly the sum of strictly positive Julia innovations plus one unresolved
fourfold tail. -/
theorem ccmArchimedean_scaleFour_innovation_telescope
    {x : ℝ} (hx : 0 < x) (n : ℕ) :
    (1 + Real.exp (-2 * x)) * ccmPublishedArchimedeanDensity (2 * x) =
      (∑ j ∈ Finset.range n,
        (4 : ℝ) ^ j * juliaScaleFourInnovationDensity ((4 : ℝ) ^ j * x)) +
      (4 : ℝ) ^ n *
        ((1 + Real.exp (-2 * ((4 : ℝ) ^ n * x))) *
          ccmPublishedArchimedeanDensity (2 * ((4 : ℝ) ^ n * x))) := by
  have hxn : 0 < (4 : ℝ) ^ n * x :=
    mul_pos (pow_pos (by norm_num) n) hx
  rw [← criticalDirichletLevyRadialDensity_eq_ccmArchimedean hx,
    ← criticalDirichletLevyRadialDensity_eq_ccmArchimedean hxn]
  exact criticalDirichletLevyRadialDensity_scaleFour_telescope x n

end

end RHTower
