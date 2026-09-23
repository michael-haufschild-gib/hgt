import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMInteriorDistributionEquation

/-!
Compact interior localization transfers the original hyperbolic L² domain and full forced equation to planar measure, retaining inverse-height coefficients.
-/

open MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open scoped ContDiff ComplexConjugate ENNReal
namespace RHTower.D4BMModularCore
noncomputable section

/-- A compact interior localization of the actual angular L² representative. -/
def InteriorTest.localValue (g : InteriorTest) (u : Space) (z : ℂ) : ℂ :=
  g.field z*u (UpperHalfPlane.ofComplex z)

private theorem localValue_support (g : InteriorTest) (u : Space) :
    Function.support (g.localValue u) ⊆ cellChart := by
  intro z hz
  have hg : z ∈ Function.support g.field := by
    intro he
    exact hz (by simp [InteriorTest.localValue,he])
  exact (Set.image_mono fdo_subset_fd) (g.support (subset_tsupport _ hg))

private theorem density_measurable : Measurable chartDensity := by
  unfold chartDensity
  fun_prop

private theorem weighted_local_memLp (g : InteriorTest) (u : Space) (n : ℕ) :
    MemLp (fun z : ℂ => (z.im : ℂ)^n*g.localValue u z) 2
      (Measure.map UpperHalfPlane.coe measure) := by
  let U : ℂ → ℂ := fun z => u (UpperHalfPlane.ofComplex z)
  have hU : MemLp U 2 (Measure.map UpperHalfPlane.coe measure) := by
    apply UpperHalfPlane.measurableEmbedding_coe.memLp_map_measure_iff.mpr
    simpa only [U,Function.comp_def,UpperHalfPlane.ofComplex_apply] using Lp.memLp u
  let a : ℂ → ℂ := fun z => (z.im : ℂ)^n*g.field z
  have ha : Continuous a := ((Complex.ofRealCLM.continuous.comp Complex.continuous_im).pow n).mul
    g.smooth.continuous
  have hk : HasCompactSupport a := g.compact.mono (by
    intro z hz he
    exact hz (by simp [a,he]))
  obtain ⟨C,hC⟩ := hk.exists_bound_of_continuous ha
  have hp : MemLp (a*U) 2 (Measure.map UpperHalfPlane.coe measure) := by
    apply hU.of_le_mul (ha.aestronglyMeasurable.mul hU.aestronglyMeasurable)
    filter_upwards with z
    change ‖a z*U z‖ ≤ C*‖U z‖
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hC z) (norm_nonneg _)
  change MemLp (fun z : ℂ => ((z.im : ℂ)^n*g.field z)*u (UpperHalfPlane.ofComplex z)) 2 _ at hp
  simpa only [InteriorTest.localValue,mul_assoc] using hp

private theorem localValue_integrable (g : InteriorTest) (u : Space) :
    Integrable (g.localValue u) (volume : Measure ℂ) := by
  have h := (weighted_local_memLp g u 2).integrable (by norm_num)
  rw [map_measure_eq] at h
  have hh := (integrable_withDensity_iff_integrable_smul density_measurable).mp h
  apply (integrableOn_iff_integrable_of_support_subset (localValue_support g u)).mp
  apply hh.congr
  filter_upwards [ae_restrict_mem
    (UpperHalfPlane.measurableEmbedding_coe.measurableSet_image.mpr isClosed_fd.measurableSet)] with z hz
  obtain ⟨w,hw,rfl⟩ := hz
  have hy : (w.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr w.im_ne_zero
  simp only [chartDensity,NNReal.smul_def,NNReal.coe_pow,NNReal.coe_div,NNReal.coe_one,
    coe_nnnorm,Real.norm_eq_abs,abs_of_pos w.im_pos,Complex.real_smul,
    Complex.ofReal_pow,Complex.ofReal_div,Complex.ofReal_one,coe_im]
  field_simp

/-- Every compact interior localization of an angular L² vector is planar L².
The proof cancels the native density after retaining the required height factors. -/
theorem InteriorTest.localValue_memLp (g : InteriorTest) (u : Space) :
    MemLp (g.localValue u) 2 (volume : Measure ℂ) := by
  have hi := localValue_integrable g u
  apply (memLp_two_iff_integrable_sq_norm hi.aestronglyMeasurable).mpr
  have h := (weighted_local_memLp g u 1).integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0)
  rw [map_measure_eq] at h
  have hh := (integrable_withDensity_iff_integrable_smul density_measurable).mp h
  apply (integrableOn_iff_integrable_of_support_subset ?_).mp
  · apply hh.congr
    filter_upwards [ae_restrict_mem
      (UpperHalfPlane.measurableEmbedding_coe.measurableSet_image.mpr isClosed_fd.measurableSet)] with z hz
    obtain ⟨w,hw,rfl⟩ := hz
    simp only [chartDensity,NNReal.smul_def,NNReal.coe_pow,NNReal.coe_div,NNReal.coe_one,
      coe_nnnorm,Real.norm_eq_abs,coe_im,smul_eq_mul,pow_one,norm_mul,
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos w.im_pos,mul_pow]
    field_simp
  · intro z hz
    apply localValue_support g u
    intro he
    apply hz
    simp [he]

/-- The actual weak response and both completed gradients admit every compact planar localization. -/
theorem full_response_local_L2 (q : XiZeroCopy) (minusBranch : Bool) (g : InteriorTest) :
    MemLp (g.localValue (embedding (weakResponse q minusBranch))) 2 (volume : Measure ℂ) ∧
      ∀ i : Fin 2, MemLp (g.localValue ((weakResponse q minusBranch : EnergySpace) i.succ))
        2 (volume : Measure ℂ) :=
  ⟨g.localValue_memLp _,fun _ => g.localValue_memLp _⟩

end
end RHTower.D4BMModularCore

open MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open scoped ContDiff ComplexConjugate ENNReal
namespace RHTower.D4BMModularCore
open D4BMGlobalAngularResponse
noncomputable section

/-- Multiply a local test by a globally smooth scalar coefficient. -/
def InteriorTest.mulSmooth (g : InteriorTest) (a : ℂ → ℂ) (ha : ContDiff ℝ ∞ a) : InteriorTest where
  field z := g.field z*a z
  smooth := g.smooth.mul ha
  compact := g.compact.mono (by intro z hz he; exact hz (by simp [he]))
  support := (closure_mono (by intro z hz he; exact hz (by simp [he]))).trans g.support

/-- Division by any height power is smooth for a compact interior test, including across
its zero extension away from the upper half-plane. -/
def InteriorTest.divHeight (g : InteriorTest) (n : ℕ) : InteriorTest where
  field z := g.field z/(z.im : ℂ)^n
  smooth := by
    apply contDiff_iff_contDiffAt.mpr
    intro z
    by_cases hz : z ∈ tsupport g.field
    · obtain ⟨w,hw,he⟩ := g.support hz
      have hy : (z.im : ℂ) ≠ 0 := by
        rw [← he]
        exact Complex.ofReal_ne_zero.mpr w.im_ne_zero
      have hp : ContDiffAt ℝ ∞ (fun w : ℂ => (w.im : ℂ)^n) z :=
        ((Complex.ofRealCLM.contDiff.comp Complex.imCLM.contDiff).pow n).contDiffAt
      simpa only [div_eq_mul_inv] using g.smooth.contDiffAt.mul (hp.fun_inv (pow_ne_zero n hy))
    · apply (contDiffAt_const (c := (0:ℂ))).congr_of_eventuallyEq
      filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hz] with w hw
      simp [image_eq_zero_of_notMem_tsupport hw]
  compact := g.compact.mono (by intro z hz he; exact hz (by simp [he]))
  support := (closure_mono (by intro z hz he; exact hz (by simp [he]))).trans g.support

private theorem local_support (g : InteriorTest) (u : Space) :
    Function.support (g.localValue u) ⊆ cellChart := by
  intro z hz
  have hg : z ∈ Function.support g.field := by
    intro he
    exact hz (by simp [InteriorTest.localValue,he])
  exact (Set.image_mono fdo_subset_fd) (g.support (subset_tsupport _ hg))

private theorem local_integral_cell (g : InteriorTest) (u : Space) :
    (∫ z in cellChart, g.localValue u z) = ∫ z : ℂ, g.localValue u z := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro z hz
  exact Function.notMem_support.mp (fun h => hz (local_support g u h))

/-- Exact transport of an unweighted native scalar moment to its planar density. -/
theorem InteriorTest.scalar_planar (g : InteriorTest) (u : Space) :
    (∫ z : UpperHalfPlane, g.field z*u z ∂measure) =
      ∫ z : ℂ, (g.divHeight 2).localValue u z := by
  rw [← local_integral_cell,← integral_height_sq_chart]
  apply integral_congr_ae
  filter_upwards with z
  have hy : (z.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr z.im_ne_zero
  simp only [InteriorTest.localValue,InteriorTest.divHeight,UpperHalfPlane.ofComplex_apply,coe_im]
  field_simp

/-- Exact transport of the height-squared scalar moment to ordinary planar measure. -/
theorem InteriorTest.height_sq_planar (g : InteriorTest) (u : Space) :
    (∫ z : UpperHalfPlane, (z.im : ℂ)^(2 : ℕ)*g.field z*u z ∂measure) =
      ∫ z : ℂ, g.localValue u z := by
  rw [← local_integral_cell,← integral_height_sq_chart]
  apply integral_congr_ae
  filter_upwards with z
  simp [InteriorTest.localValue,mul_assoc]

private theorem planar_support (g : InteriorTest) :
    Function.support g.planarLaplacian ⊆ tsupport g.field := by
  intro z hz
  by_contra hn
  have he (i : Fin 2) : fderiv ℝ (g.derivative (direction i)).field z (direction i) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
      (f := fun x : ℂ => fderiv ℝ (g.derivative (direction i)).field x (direction i))
    intro h
    exact hn ((tsupport_fderiv_apply_subset ℝ (direction i)).trans
      (tsupport_fderiv_apply_subset ℝ (direction i)) h)
  exact hz (by simp only [InteriorTest.planarLaplacian,he,Finset.sum_const_zero])

/-- The planar Laplacian itself remains a compact interior test. -/
def InteriorTest.laplacianTest (g : InteriorTest) : InteriorTest where
  field := g.planarLaplacian
  smooth := by
    apply ContDiff.sum
    intro i hi
    exact ((g.derivative (direction i)).derivative (direction i)).smooth
  compact := HasCompactSupport.of_support_subset_isCompact g.compact (planar_support g)
  support := (closure_minimal (planar_support g) isClosed_closure).trans g.support

/-- Every actual Xi response satisfies its full planar distributional equation
with the original potential and original forcing density explicitly retained. -/
theorem full_response_planar_equation (q : XiZeroCopy) (minusBranch : Bool)
    (g : InteriorTest) :
    (∫ z : ℂ, g.laplacianTest.localValue (embedding (weakResponse q minusBranch)) z) -
      parameter q minusBranch*(∫ z : ℂ, (g.divHeight 2).localValue
        (embedding (weakResponse q minusBranch)) z) =
      ∫ z : ℂ, (g.divHeight 2).localValue (forcingVector q minusBranch) z := by
  have he := full_response_distribution_equation q minusBranch g
  rw [g.laplace_pairing,g.scalar_pairing,g.scalar_pairing] at he
  rw [g.scalar_planar,g.scalar_planar] at he
  rw [← g.laplacianTest.height_sq_planar]
  exact he

end
end RHTower.D4BMModularCore
