import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ComplexCausalLaplaceWeight
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ModulatedCausalReflectionCommutation

/-!
# A conjugate pair of causal reflections has a real representative

Conjugation reverses the modulation. The two resulting reflections commute
on L¹ profiles, so their composition preserves real data almost everywhere.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Convolution

namespace GaloisForLFunctions.HTGeometry

/-- Conjugation reverses the imaginary part of the physical rate. -/
theorem conj_modulatedLaplaceRate (a b : ℝ) :
    (starRingEnd ℂ) (modulatedLaplaceRate a b) = modulatedLaplaceRate a (-b) := by
  apply Complex.ext <;> simp [modulatedLaplaceRate] <;> ring

/-- The literal causal kernel respects complex conjugation. -/
theorem conj_complexRateCausalKernel (z : ℂ) (u : ℝ) :
    (starRingEnd ℂ) (complexRateCausalKernel z u) =
      complexRateCausalKernel ((starRingEnd ℂ) z) u := by
  unfold complexRateCausalKernel
  by_cases hu : u ∈ Ioi (0 : ℝ)
  · have he : (starRingEnd ℂ) (Complex.exp ((-z) * (u : ℂ))) =
        Complex.exp ((-(starRingEnd ℂ) z) * (u : ℂ)) := by
      rw [← Complex.exp_conj, map_mul, map_neg, Complex.conj_ofReal]
    rw [indicator_of_mem hu, indicator_of_mem hu, map_mul, Complex.conj_ofReal, he]
  · rw [indicator_of_notMem hu, indicator_of_notMem hu, map_zero]

/-- Conjugation distributes across the actual convolution integral. -/
theorem conj_complexConvolution (k f : ℝ → ℂ) :
    (fun u => (starRingEnd ℂ) ((k ⋆[ContinuousLinearMap.mul ℂ ℂ] f) u)) =
      (fun u => (starRingEnd ℂ) (k u)) ⋆[ContinuousLinearMap.mul ℂ ℂ]
        (fun u => (starRingEnd ℂ) (f u)) := by
  funext u
  rw [convolution_def, convolution_def, ← integral_conj]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  change (starRingEnd ℂ) (k t * f (u - t)) =
    (starRingEnd ℂ) (k t) * (starRingEnd ℂ) (f (u - t))
  exact map_mul _ _ _

/-- Conjugating a modulated kernel reverses its modulation. -/
theorem conj_modulatedCausalExponential (a b : ℝ) :
    (fun u => (starRingEnd ℂ) (modulatedCausalExponential a b u)) =
      modulatedCausalExponential a (-b) := by
  funext u
  rw [modulatedCausalExponential_eq_complexRate,
    modulatedCausalExponential_eq_complexRate, conj_complexRateCausalKernel,
    conj_modulatedLaplaceRate]

/-- Conjugation exchanges the two complex resolvents. -/
theorem conj_modulatedCausalConvolution (a b : ℝ) (f : ℝ → ℂ) :
    (fun u => (starRingEnd ℂ) (modulatedCausalConvolution a b f u)) =
      modulatedCausalConvolution a (-b) (fun u => (starRingEnd ℂ) (f u)) := by
  unfold modulatedCausalConvolution
  rw [conj_complexConvolution, conj_modulatedCausalExponential]

/-- Conjugation exchanges the two complex reflections. -/
theorem conj_modulatedCausalReflection (a b : ℝ) (f : ℝ → ℂ) :
    (fun u => (starRingEnd ℂ) (modulatedCausalReflection a b f u)) =
      modulatedCausalReflection a (-b) (fun u => (starRingEnd ℂ) (f u)) := by
  funext u
  have hc : (starRingEnd ℂ) (2 * a : ℂ) = 2 * a := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  have hk := congrFun (conj_modulatedCausalConvolution a b f) u
  change (starRingEnd ℂ) (-f u + (2 * a : ℂ) * modulatedCausalConvolution a b f u) =
    -(starRingEnd ℂ) (f u) + (2 * a : ℂ) *
      modulatedCausalConvolution a (-b) (fun t => (starRingEnd ℂ) (f t)) u
  rw [map_add, map_neg, map_mul, hc, hk]

/-- Reflection at a complex rate followed by reflection at its conjugate. -/
def pairedCausalReflection (a b : ℝ) (f : ℝ → ℂ) : ℝ → ℂ :=
  modulatedCausalReflection a (-b) (modulatedCausalReflection a b f)

/-- The sum of the two actual weighted resolvent energies in a conjugate pair. -/
def pairedCausalResolventEnergy (a b x : ℝ) (f : ℝ → ℂ) : ℝ :=
  (∫ u, ‖_root_.RHTower.causalLaplaceWeighted x (modulatedCausalConvolution a b f) u‖ ^ 2) +
    ∫ u, ‖_root_.RHTower.causalLaplaceWeighted x
      (modulatedCausalConvolution a (-b) (modulatedCausalReflection a b f)) u‖ ^ 2

theorem pairedCausalResolventEnergy_nonneg (a b x : ℝ) (f : ℝ → ℂ) :
    0 ≤ pairedCausalResolventEnergy a b x f :=
  add_nonneg (integral_nonneg fun _ => sq_nonneg _) (integral_nonneg fun _ => sq_nonneg _)

/-- The two exact reflection defects add to the paired resolvent energy. -/
theorem integral_weighted_pairedCausalReflection_energy {a x : ℝ} (hx : 0 < a + x)
    (b : ℝ) {f : ℝ → ℂ}
    (hf : MemLp (_root_.RHTower.causalLaplaceWeighted x f) 2 volume) :
    (∫ u, ‖_root_.RHTower.causalLaplaceWeighted x f u‖ ^ 2) =
      (∫ u, ‖_root_.RHTower.causalLaplaceWeighted x (pairedCausalReflection a b f) u‖ ^ 2) +
        (4 * a * x) * pairedCausalResolventEnergy a b x f := by
  have hfirst := integral_weighted_modulatedCausalReflection_energy hx b hf
  have hsecond := integral_weighted_modulatedCausalReflection_energy hx (-b)
    (memLp_weighted_modulatedCausalReflection hx b hf)
  rw [hsecond] at hfirst
  unfold pairedCausalReflection pairedCausalResolventEnergy
  calc
    _ = _ := hfirst
    _ = _ := by ring

/-- The conjugate pair preserves real integrable data almost everywhere. -/
theorem conj_pairedCausalReflection_ae {a : ℝ} (ha : 0 < a) (b : ℝ)
    {f : ℝ → ℂ} (hf : Integrable f) (hreal : ∀ u, (starRingEnd ℂ) (f u) = f u) :
    (fun u => (starRingEnd ℂ) (pairedCausalReflection a b f u)) =ᵐ[volume]
      pairedCausalReflection a b f := by
  unfold pairedCausalReflection
  rw [conj_modulatedCausalReflection, conj_modulatedCausalReflection,
    neg_neg, funext hreal]
  exact modulatedCausalReflections_commute_ae ha ha b (-b) hf

/-- A literal real representative of the paired reflection. -/
def realPairedCausalReflection (a b : ℝ) (F : ℝ → ℝ) (u : ℝ) : ℝ :=
  (pairedCausalReflection a b (fun t => (F t : ℂ)) u).re

/-- Taking the real part changes the paired profile only on a null set. -/
theorem coe_realPairedCausalReflection_ae {a : ℝ} (ha : 0 < a) (b : ℝ)
    {F : ℝ → ℝ} (hF : Integrable F) :
    (fun u => (realPairedCausalReflection a b F u : ℂ)) =ᵐ[volume]
      pairedCausalReflection a b (fun u => (F u : ℂ)) := by
  have hc := conj_pairedCausalReflection_ae ha b (hF.ofReal (𝕜 := ℂ))
    (fun u => Complex.conj_ofReal (F u))
  filter_upwards [hc] with u hu
  apply Complex.ext
  · rfl
  · have hi := congrArg Complex.im hu
    change -(pairedCausalReflection a b (fun t => (F t : ℂ)) u).im =
      (pairedCausalReflection a b (fun t => (F t : ℂ)) u).im at hi
    change 0 = (pairedCausalReflection a b (fun t => (F t : ℂ)) u).im
    linarith only [hi]

/-- The literal real representative is measurable. -/
theorem measurable_realPairedCausalReflection (a b : ℝ) {F : ℝ → ℝ}
    (hF : Measurable F) : Measurable (realPairedCausalReflection a b F) :=
  Complex.continuous_re.measurable.comp
    (measurable_modulatedCausalReflection a (-b)
      (measurable_modulatedCausalReflection a b (Complex.continuous_ofReal.measurable.comp hF)))

/-- The literal real representative retains actual L¹ admission. -/
theorem integrable_realPairedCausalReflection {a : ℝ} (ha : 0 < a) (b : ℝ)
    {F : ℝ → ℝ} (hF : Integrable F) : Integrable (realPairedCausalReflection a b F) :=
  (integrable_modulatedCausalReflection ha (-b)
    (integrable_modulatedCausalReflection ha b (hF.ofReal (𝕜 := ℂ)))).re

/-- The real representative has the same unweighted square domain as the complex pair. -/
theorem memLp_realPairedCausalReflection {a : ℝ} (ha : 0 < a) (b : ℝ)
    {F : ℝ → ℝ} (hF : Integrable F) (hF2 : MemLp (fun u => (F u : ℂ)) 2 volume) :
    MemLp (fun u => (realPairedCausalReflection a b F u : ℂ)) 2 volume := by
  exact (memLp_congr_ae (coe_realPairedCausalReflection_ae ha b hF)).mpr
    (memLp_modulatedCausalReflection ha (-b) (memLp_modulatedCausalReflection ha b hF2))

/-- The real representative retains every admitted exponential square weight. -/
theorem memLp_weighted_realPairedCausalReflection {a x : ℝ} (ha : 0 < a)
    (hx : 0 < a + x) (b : ℝ) {F : ℝ → ℝ} (hF : Integrable F)
    (hFx : MemLp (_root_.RHTower.causalLaplaceWeighted x (fun u => (F u : ℂ))) 2 volume) :
    MemLp (_root_.RHTower.causalLaplaceWeighted x
      (fun u => (realPairedCausalReflection a b F u : ℂ))) 2 volume := by
  have hP := memLp_weighted_modulatedCausalReflection hx (-b)
    (memLp_weighted_modulatedCausalReflection hx b hFx)
  have he : _root_.RHTower.causalLaplaceWeighted x
      (fun u => (realPairedCausalReflection a b F u : ℂ)) =ᵐ[volume]
      _root_.RHTower.causalLaplaceWeighted x
        (pairedCausalReflection a b (fun u => (F u : ℂ))) := by
    filter_upwards [coe_realPairedCausalReflection_ae ha b hF] with u hu
    exact congrArg (fun z : ℂ => Complex.exp (-(Real.pi * x * u : ℝ)) * z) hu
  exact (memLp_congr_ae he).mpr hP

end GaloisForLFunctions.HTGeometry
