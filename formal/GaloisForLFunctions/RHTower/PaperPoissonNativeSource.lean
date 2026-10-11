import GaloisForLFunctions.RHTower.PaperPoissonContinuumPort
import GaloisForLFunctions.RHTower.XiSliceHeatMomentConcentration

/-!
# The actual Xi source in the full Poisson continuum port

The cosine-producer densities belong to Lebesgue `L²` by their existing super-exponential
bounds. The full Poisson multiplier transports these exact densities, and their original
Fourier integrals recover the original cosine producers. No surrogate source is introduced.
-/

namespace RHTower
noncomputable section
open MeasureTheory GaloisForLFunctions.HTGeometry Filter
open scoped Topology ENNReal NNReal

private theorem superExpKernel_memLp_two_complex {g : ℝ → ℝ}
    (hg : DeBruijn.SuperExpKernel g) : MemLp (fun u => (g u : ℂ)) 2 volume := by
  obtain ⟨M, _, hM⟩ := hg.exists_bound
  have hi : Integrable g := by simpa using hg.integrable_mul_exp 0
  have hsq : Integrable (fun u => g u ^ 2) := by
    refine (hi.const_mul M).mono' (hg.continuous.pow 2).aestronglyMeasurable
      (Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simpa only [pow_two] using mul_le_mul_of_nonneg_right (hM u) (hg.nonneg u)
  apply (memLp_two_iff_integrable_sq_norm
    (Complex.continuous_ofReal.comp hg.continuous).aestronglyMeasurable).2
  simpa only [Function.comp_apply, Complex.norm_real, Real.norm_eq_abs, sq_abs] using hsq

theorem memLp_paperCosineSource (h : ℝ≥0) :
    MemLp (fun u => ((riemannKernelReal u * Real.cosh ((h : ℝ) * u) : ℝ) : ℂ)) 2 volume :=
  superExpKernel_memLp_two_complex (DeBruijn.riemannKernel_mul_cosh_superExp h)

/-- The actual cosine-producer density as a full Lebesgue Hilbert-space vector. -/
def paperCosineSourceProfile (h : ℝ≥0) : PaperPoissonSpace := (memLp_paperCosineSource h).toLp _

theorem paperCosineSourceProfile_apply_ae (h : ℝ≥0) :
    (paperCosineSourceProfile h : ℝ → ℂ) =ᵐ[volume]
      fun u => ((riemannKernelReal u * Real.cosh ((h : ℝ) * u) : ℝ) : ℂ) :=
  MemLp.coeFn_toLp _

/-- The source vector is nonzero at every depth, unconditionally. -/
theorem paperCosineSourceProfile_ne_zero (h : ℝ≥0) : paperCosineSourceProfile h ≠ 0 := by
  intro hz
  have hzero : (paperCosineSourceProfile h : ℝ → ℂ) =ᵐ[volume] fun _ => (0 : ℂ) := by
    rw [hz]
    exact Lp.coeFn_zero ℂ 2 volume
  have hi : (∫ u : ℝ, ((riemannKernelReal u * Real.cosh ((h : ℝ) * u) : ℝ) : ℂ)) = 0 := by
    calc
      _ = ∫ _u : ℝ, (0 : ℂ) :=
        integral_congr_ae ((paperCosineSourceProfile_apply_ae h).symm.trans hzero)
      _ = 0 := integral_zero _ _
  rw [integral_complex_ofReal] at hi
  have hr : (∫ u : ℝ, riemannKernelReal u * Real.cosh ((h : ℝ) * u)) = 0 := by
    exact_mod_cast hi
  exact (ne_of_gt (DeBruijn.riemannKernel_mul_cosh_superExp h).integral_pos) hr

/-- The exact source vector lands at its prescribed lower depth. -/
theorem paperPoissonPort_source_transfer (h d : ℝ≥0) :
    paperPoissonPort h d (paperCosineSourceProfile (h + d)) = paperCosineSourceProfile h := by
  apply Lp.ext
  filter_upwards [paperPoissonPort_apply_ae h d (paperCosineSourceProfile (h + d)),
    paperCosineSourceProfile_apply_ae (h + d), paperCosineSourceProfile_apply_ae h]
    with u hu hv hw
  rw [hu, hv, hw, ← Complex.ofReal_mul, paperPoissonSymbol_source_transfer]

/-- The native source energy is monotone under the exact positive transfer. -/
theorem norm_paperCosineSourceProfile_le (h d : ℝ≥0) :
    ‖paperCosineSourceProfile h‖ ≤ ‖paperCosineSourceProfile (h + d)‖ := by
  have hn := (paperPoissonPort h d).le_opNorm (paperCosineSourceProfile (h + d))
  rwa [paperPoissonPort_source_transfer, norm_paperPoissonPort, one_mul] at hn

/-- The original Fourier integral of the actual source vector is the original producer. -/
theorem paperCosineSourceProfile_transform (h : ℝ≥0) (t : ℝ) :
    cosProducer h t = ∫ u : ℝ, (paperCosineSourceProfile h : ℝ → ℂ) u *
      Complex.exp (Complex.I * (t : ℂ) * u) := by
  have hn : cosProducer h t = ∫ u : ℝ,
      ((riemannKernelReal u * Real.cosh ((h : ℝ) * u) : ℝ) : ℂ) *
        Complex.exp (Complex.I * (t : ℂ) * u) := by
    rw [cosProducer, ← DeBruijn.cosTransform_riemannKernel_mul_cosh]
    rfl
  rw [hn]
  apply integral_congr_ae
  filter_upwards [paperCosineSourceProfile_apply_ae h] with u hu
  rw [hu]

/-- At depth zero this source is precisely Xi, with the native Fourier convention. -/
theorem paperCosineSourceProfile_zero_transform (t : ℝ) :
    XiC t = ∫ u : ℝ, (paperCosineSourceProfile 0 : ℝ → ℂ) u *
      Complex.exp (Complex.I * (t : ℂ) * u) := by
  simpa [cosProducer] using paperCosineSourceProfile_transform 0 t

/-- The unconditional horizon source reaches the literal Xi source through this port. -/
theorem paperPoissonPort_horizon_source :
    paperPoissonPort 0 (1 / 2) (paperCosineSourceProfile (1 / 2)) =
      paperCosineSourceProfile 0 := by
  simpa using paperPoissonPort_source_transfer 0 (1 / 2)

/-- Recovering Xi after the full continuum transfer uses exactly the original source. -/
theorem paperPoissonPort_horizon_transform (t : ℝ) :
    XiC t = ∫ u : ℝ,
      (paperPoissonPort 0 (1 / 2) (paperCosineSourceProfile (1 / 2)) : ℝ → ℂ) u *
        Complex.exp (Complex.I * (t : ℂ) * u) := by
  rw [paperPoissonPort_horizon_source]
  exact paperCosineSourceProfile_zero_transform t

end
end RHTower
