import GaloisForLFunctions.RHTower.MaassCongruenceL2
import GaloisForLFunctions.RHTower.MaassModelIntertwiner
import GaloisForLFunctions.RHTower.SelbergMaassCharacterSeamFlux
import GaloisForLFunctions.RHTower.SelbergMaassStripGap

/-!
# Actual first Maass ladder vectors in L2

The original raising and lowering vectors over the finite congruence family
are identified pointwise with the actual first derivatives. Existing source
Stokes and cusp flux decay prove their L2 admission and the exact combined
energy identity. The normalized model coefficients at indices 1 and -1 inherit
this admission. No quotient unitarity or higher-order domain is assumed.
-/

open UpperHalfPlane ModularGroup MeasureTheory Set Filter Topology Complex
open scoped MatrixGroups ContDiff
namespace GaloisForLFunctions.RHTower.MaassLadderL2
open MaassCongruenceL2 SelbergMaassCongruenceTrace SelbergMaassCongruenceAverage
  SelbergMaassCharacterSeamFlux SelbergMaassTraceEnergy SelbergMaassSourceCurrents
  SelbergMaassFullGradient
noncomputable section

variable (N : ℕ) {lam : ℝ}
  (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)

/-- Continuity of the original vector of first derivatives follows from actual C2 regularity. -/
theorem sourceDerivative_continuous (v : ℂ) : Continuous (sourceDerivative N f v) := by
  have hd := (SelbergMaassCharacterGradient.sourceVector_contDiffOn N f).continuousOn_fderiv_of_isOpen
    isOpen_upperHalfPlaneSet (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hc := hd.clm_apply (continuousOn_const (c := v))
  apply continuous_iff_continuousAt.mpr
  intro z
  have h := (hc.continuousAt (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)).comp
    UpperHalfPlane.continuous_coe.continuousAt
  have he : sourceDerivative N f v = (fun w : ℍ =>
      fderiv ℝ (fun u => sourceVector N f (ofComplex u)) (w : ℂ) v) :=
    funext (sourceDerivative_eq_dir N f v)
  rw [he]
  simpa only [Function.comp_def] using h

/-- First actual raising of every original congruence translate. -/
def firstRaised (z : ℍ) : EuclideanSpace ℂ (Deck N) :=
  WithLp.toLp 2 (fun q => MaassSmooth.raised (MaassSmooth.ofMaass (quotientForm N f q)) 1 z)

/-- First actual lowering of every original congruence translate. -/
def firstLowered (z : ℍ) : EuclideanSpace ℂ (Deck N) :=
  WithLp.toLp 2 (fun q => MaassSmooth.lowered (MaassSmooth.ofMaass (quotientForm N f q)) 1 z)

theorem firstRaised_eq (z : ℍ) : firstRaised N f z =
    Complex.I • ((z.im : ℂ) • sourceDerivative N f 1 z) -
      (z.im : ℂ) • sourceDerivative N f Complex.I z := by
  ext q
  change (MaassSmooth.raise 0 (MaassSmooth.ofMaass (quotientForm N f q))) z =
    Complex.I * ((z.im : ℂ) * dir 1 (field N f q) (z : ℂ)) -
      (z.im : ℂ) * dir Complex.I (field N f q) (z : ℂ)
  rw [MaassSmooth.raise_apply]
  simp only [Int.cast_zero, zero_smul, sub_zero, MaassSmooth.X_apply, MaassSmooth.Y_apply]
  rfl

theorem firstLowered_eq (z : ℍ) : firstLowered N f z =
    -(Complex.I • ((z.im : ℂ) • sourceDerivative N f 1 z)) -
      (z.im : ℂ) • sourceDerivative N f Complex.I z := by
  ext q
  change (MaassSmooth.lower 0 (MaassSmooth.ofMaass (quotientForm N f q))) z =
    -(Complex.I * ((z.im : ℂ) * dir 1 (field N f q) (z : ℂ))) -
      (z.im : ℂ) * dir Complex.I (field N f q) (z : ℂ)
  rw [MaassSmooth.lower_apply]
  simp only [Int.cast_zero, zero_smul, add_zero, MaassSmooth.X_apply, MaassSmooth.Y_apply]
  rfl

theorem firstRaised_continuous : Continuous (firstRaised N f) := by
  change Continuous (fun z : ℍ => firstRaised N f z)
  simp_rw [firstRaised_eq]
  exact (((Complex.continuous_ofReal.comp UpperHalfPlane.continuous_im).smul
    (sourceDerivative_continuous N f 1)).const_smul Complex.I).sub
    ((Complex.continuous_ofReal.comp UpperHalfPlane.continuous_im).smul
      (sourceDerivative_continuous N f Complex.I))

theorem firstLowered_continuous : Continuous (firstLowered N f) := by
  change Continuous (fun z : ℍ => firstLowered N f z)
  simp_rw [firstLowered_eq]
  exact (((Complex.continuous_ofReal.comp UpperHalfPlane.continuous_im).smul
    (sourceDerivative_continuous N f 1)).const_smul Complex.I).neg.sub
    ((Complex.continuous_ofReal.comp UpperHalfPlane.continuous_im).smul
      (sourceDerivative_continuous N f Complex.I))

/-- The actual first ladder pair retains exactly twice the full hyperbolic gradient energy. -/
theorem firstLadder_energy (z : ℍ) :
    ‖firstRaised N f z‖ ^ (2 : ℕ) + ‖firstLowered N f z‖ ^ (2 : ℕ) = 2 * hyperbolicGradient N f z := by
  have hn (u v : EuclideanSpace ℂ (Deck N)) : -u - v = -(u + v) := by abel
  rw [firstRaised_eq, firstLowered_eq, hn, norm_neg, add_comm,
    parallelogram_law_with_norm ℂ]
  simp only [norm_smul, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs, mul_pow, sq_abs]
  rw [← mul_add, sourceDerivative_gradient]
  rfl

section Exceptional
variable (lam : SelbergExceptionalEigenvalue)
  (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam.1)

/-- Original full-gradient integrability admits the first raised vector into actual L2. -/
theorem firstRaised_memLp : MemLp (firstRaised N f) 2 cellMeasure := by
  apply (memLp_two_iff_integrable_sq_norm (firstRaised_continuous N f).aestronglyMeasurable).mpr
  apply ((cell_gradient_integrable N lam f).const_mul 2).mono'
    ((firstRaised_continuous N f).norm.pow 2).aestronglyMeasurable
  filter_upwards with z
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← firstLadder_energy N f z]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- Original full-gradient integrability admits the first lowered vector into actual L2. -/
theorem firstLowered_memLp : MemLp (firstLowered N f) 2 cellMeasure := by
  apply (memLp_two_iff_integrable_sq_norm (firstLowered_continuous N f).aestronglyMeasurable).mpr
  apply ((cell_gradient_integrable N lam f).const_mul 2).mono'
    ((firstLowered_continuous N f).norm.pow 2).aestronglyMeasurable
  filter_upwards with z
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← firstLadder_energy N f z]
  exact le_add_of_nonneg_left (sq_nonneg _)

/-- The first raised source as its actual almost-everywhere class. -/
def firstRaisedLp : Lp (EuclideanSpace ℂ (Deck N)) 2 cellMeasure :=
  (firstRaised_memLp N lam f).toLp (firstRaised N f)

/-- The first lowered source as its actual almost-everywhere class. -/
def firstLoweredLp : Lp (EuclideanSpace ℂ (Deck N)) 2 cellMeasure :=
  (firstLowered_memLp N lam f).toLp (firstLowered N f)

private theorem norm_toLp_sq {v : ℍ → EuclideanSpace ℂ (Deck N)} (h : MemLp v 2 cellMeasure) :
    ‖h.toLp v‖ ^ (2 : ℕ) = ∫ z in fd, ‖v z‖ ^ (2 : ℕ) ∂volume := by
  rw [@norm_sq_eq_re_inner ℂ, L2.inner_def,
    ← integral_re (L2.integrable_inner (h.toLp v) (h.toLp v))]
  apply integral_congr_ae
  filter_upwards [h.coeFn_toLp] with z hz
  rw [hz, ← norm_sq_eq_re_inner]

/-- Exact first-order Hilbert energy, with source norm and cusp boundary terms discharged. -/
theorem firstLadderLp_energy :
    ‖firstRaisedLp N lam f‖ ^ (2 : ℕ) + ‖firstLoweredLp N lam f‖ ^ (2 : ℕ) =
      2 * lam.1 * ‖sourceLp N f‖ ^ (2 : ℕ) := by
  have hR := (memLp_two_iff_integrable_sq_norm
    (firstRaised_continuous N f).aestronglyMeasurable).mp (firstRaised_memLp N lam f)
  have hL := (memLp_two_iff_integrable_sq_norm
    (firstLowered_continuous N f).aestronglyMeasurable).mp (firstLowered_memLp N lam f)
  rw [firstRaisedLp, firstLoweredLp, norm_toLp_sq, norm_toLp_sq, ← integral_add hR hL]
  simp_rw [firstLadder_energy]
  rw [integral_const_mul, cell_gradient_identity N lam f,
    ← SelbergMaassStripGap.cell_mass_identity N lam f, ← sourceLp_norm_sq N f]
  ring

/-- The intertwiner's source coefficient at index 1 belongs to actual L2. -/
theorem modelSource_one_memLp :
    MemLp (fun z : ℍ => WithLp.toLp 2 (fun q : Deck N =>
      MaassSmooth.modelSource lam (quotientForm N f q) 1 z)) 2 cellMeasure := by
  convert! (firstRaised_memLp N lam f).const_smul (MaassSmooth.ladderScale lam 1)⁻¹ using 1

/-- The intertwiner's source coefficient at index -1 belongs to actual L2. -/
theorem modelSource_neg_one_memLp :
    MemLp (fun z : ℍ => WithLp.toLp 2 (fun q : Deck N =>
      MaassSmooth.modelSource lam (quotientForm N f q) (-1) z)) 2 cellMeasure := by
  convert! (firstLowered_memLp N lam f).const_smul (MaassSmooth.ladderScale lam 1)⁻¹ using 1

end Exceptional
end
end GaloisForLFunctions.RHTower.MaassLadderL2
