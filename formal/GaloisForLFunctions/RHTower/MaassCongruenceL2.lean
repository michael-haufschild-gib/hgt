import GaloisForLFunctions.RHTower.SelbergMaassTraceMass
import GaloisForLFunctions.RHTower.SelbergMaassCongruenceAverage
import GaloisForLFunctions.HTGeometry.ModularFundamentalDomainVolume
import Mathlib.NumberTheory.ModularForms.Bounds
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Actual congruence Maass sources in L2

Cusp decay and finite-index invariance give global boundedness for every real
eigenvalue. The existing finite-coset source vector belongs to L2 of actual
hyperbolic measure on the modular cell. Its norm is the literal trace integral,
is strictly positive, and equality of L2 classes recovers the original form.

The finite-coset convention retains the central multiplicity of -I. Right-SL2R
invariance and Hilbert globalization are separate obligations.
-/

open UpperHalfPlane ModularGroup MeasureTheory Set Filter Topology
open scoped MatrixGroups
namespace GaloisForLFunctions.RHTower.MaassCongruenceL2
open SelbergMaassCongruenceTrace SelbergMaassTraceMass SelbergMaassCongruenceAverage
noncomputable section

private theorem source_continuous {Γ : Subgroup SL2R} {lam : ℝ}
    (f : MaassCuspEigenform Γ lam) : Continuous f.1.1 := by
  apply continuous_iff_continuousAt.mpr
  intro z
  have h := (f.2.2.1.1.continuousOn.continuousAt
    (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)).comp UpperHalfPlane.continuous_coe.continuousAt
  simpa only [Function.comp_def, ofComplex_apply] using h

variable (N : ℕ) {lam : ℝ}
  (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)

/-- The original congruence Maass function is globally bounded for every real eigenvalue. -/
theorem source_bounded : ∃ C : ℝ, ∀ z : ℍ, ‖f.1.1 z‖ ≤ C := by
  have hinfty (A : SL2Z) : (fun z : ℍ => f.1.1 (A • z)) =O[atImInfty]
      (fun z : ℍ => z.im ^ (0 : ℝ)) := by
    simpa only [Real.rpow_zero, Pi.one_def] using
      (show (fun z : ℍ => f.1.1 (A • z)) =O[atImInfty] (1 : ℍ → ℝ) from
        (f.2.2.2 A).isBoundedAtImInfty)
  obtain ⟨C, hC⟩ := exists_bound_of_subgroup_invariant_of_isBigO
    (source_continuous f) (le_refl (0 : ℝ)) hinfty
    (Γ := CongruenceSubgroup.Gamma (N + 1))
    (fun A hA z => f.1.2 ⟨integralSL2ToReal A, ⟨A, hA, rfl⟩⟩ z)
  exact ⟨C, by simpa only [Real.rpow_zero, mul_one] using hC⟩

/-- The finite congruence trace has a global bound derived from its actual cusp decay. -/
theorem density_bounded : ∃ C : ℝ, ∀ z : ℍ, ‖density N f z‖ ≤ C := by
  have hinfty : density N f =O[atImInfty] (fun z : ℍ => z.im ^ (0 : ℝ)) := by
    simpa only [Real.rpow_zero, Pi.one_def] using
      (show density N f =O[atImInfty] (1 : ℍ → ℝ) from
        (density_decay N f).isBoundedAtImInfty)
  obtain ⟨C, hC⟩ := exists_bound_of_invariant_of_isBigO
    (density_continuous N f) (le_refl (0 : ℝ)) hinfty (density_invariant N f)
  exact ⟨C, by simpa only [Real.rpow_zero, mul_one] using hC⟩

/-- The measure in the source norm is the actual hyperbolic measure restricted to the modular cell. -/
abbrev cellMeasure : Measure ℍ := volume.restrict fd

instance cellMeasure_finite : IsFiniteMeasure cellMeasure :=
  isFiniteMeasure_restrict.mpr HTGeometry.volume_fd_ne_top

/-- Actual trace density is integrable across both compact core and all cusps. -/
theorem density_integrable : Integrable (density N f) cellMeasure := by
  obtain ⟨C, hC⟩ := density_bounded N f
  exact (MemLp.of_bound (p := 1) (density_continuous N f).aestronglyMeasurable C
    (ae_of_all _ hC)).integrable (by simp)

theorem sourceVector_continuous : Continuous (sourceVector N f) :=
  (PiLp.continuous_toLp 2 _).comp (continuous_pi (fun q => source_continuous (quotientForm N f q)))

/-- Unconditional L2 admission of the original finite-coset Maass source. -/
theorem sourceVector_memLp : MemLp (sourceVector N f) 2 cellMeasure := by
  apply (memLp_two_iff_integrable_sq_norm (sourceVector_continuous N f).aestronglyMeasurable).mpr
  simpa only [sourceVector_norm_sq] using density_integrable N f

/-- Actual nonzero source in a Hilbert space, using finite cosets and hyperbolic integration. -/
def sourceLp : Lp (EuclideanSpace ℂ (Deck N)) 2 cellMeasure :=
  (sourceVector_memLp N f).toLp (sourceVector N f)

theorem sourceLp_ae : sourceLp N f =ᵐ[cellMeasure] sourceVector N f :=
  (sourceVector_memLp N f).coeFn_toLp

/-- The Hilbert norm is the literal hyperbolic integral of the actual congruence trace. -/
theorem sourceLp_norm_sq : ‖sourceLp N f‖ ^ 2 = ∫ z in fd, density N f z ∂volume := by
  rw [@norm_sq_eq_re_inner ℂ, L2.inner_def,
    ← integral_re (L2.integrable_inner (sourceLp N f) (sourceLp N f))]
  apply integral_congr_ae
  filter_upwards [sourceLp_ae N f] with z hz
  rw [hz, ← norm_sq_eq_re_inner, sourceVector_norm_sq]

/-- Original nonvanishing survives passage to hyperbolic almost-everywhere classes. -/
theorem source_mass_pos : 0 < ∫ z in fd, density N f z ∂volume := by
  apply (setIntegral_pos_iff_support_of_nonneg_ae
    (ae_of_all _ (density_nonneg N f)) (density_integrable N f)).mpr
  obtain ⟨z, hz, hpos⟩ := density_pos_interior N f
  have hU : IsOpen ((density N f) ⁻¹' Ioi 0 ∩ fdo) :=
    (isOpen_Ioi.preimage (density_continuous N f)).inter isOpen_fdo
  have hmeasure := hU.measure_pos volume ⟨z, hpos, hz⟩
  exact hmeasure.trans_le (measure_mono (fun w hw =>
    ⟨Function.mem_support.mpr (ne_of_gt hw.1), fdo_subset_fd hw.2⟩))

theorem sourceLp_ne_zero : sourceLp N f ≠ 0 := by
  intro h
  have hpos := source_mass_pos N f
  rw [← sourceLp_norm_sq N f, h, norm_zero, zero_pow (by norm_num : 2 ≠ 0)] at hpos
  exact (lt_irrefl 0) hpos


/-- Equality in the actual L2 space recovers the original Maass eigenform pointwise. -/
theorem sourceLp_injective : Function.Injective (sourceLp N (lam := lam)) := by
  intro f g h
  have hae : sourceVector N f =ᵐ[cellMeasure] sourceVector N g := by
    filter_upwards [sourceLp_ae N f, sourceLp_ae N g] with z hf hg
    rw [← hf, ← hg, h]
  have hfd : EqOn (sourceVector N f) (sourceVector N g) fd :=
    Measure.eqOn_of_ae_eq (μ := (volume : Measure ℍ)) hae (sourceVector_continuous N f).continuousOn
      (sourceVector_continuous N g).continuousOn
      (by rw [← fdo_eq_interior_fd, ← fd_eq_closure_fdo])
  apply Subtype.ext
  apply Subtype.ext
  funext z
  obtain ⟨A, hA⟩ := exists_smul_mem_fd z
  have hv := congrArg (fun v : EuclideanSpace ℂ (Deck N) =>
    v (QuotientGroup.mk A⁻¹)) (hfd hA)
  simpa only [sourceVector, PiLp.toLp_apply, quotientForm_mk,
    SelbergMaassCuspTransport.translate_apply, inv_smul_smul] using hv

end
end GaloisForLFunctions.RHTower.MaassCongruenceL2
