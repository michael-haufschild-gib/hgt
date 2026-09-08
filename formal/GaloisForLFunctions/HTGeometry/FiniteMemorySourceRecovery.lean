import GaloisForLFunctions.HTGeometry.VolterraSourceRecovery
import GaloisForLFunctions.HTGeometry.NonMarkovianLangevinVolterra

/-!
# Source recovery for finite bath memory, including resonances

The forward-image inverse in Zhang, arXiv:2608.22995v1, applies to the
corpus's actual positive finite bath kernels. Integrating the kernel before
forming the Volterra operator avoids division by frequencies and includes zero
frequencies. Arbitrary continuous driving histories are recoverable from every
response prefix. For nonzero detunings this is exactly the existing bath model.
-/

open scoped BigOperators NNReal
namespace GaloisForLFunctions.HTGeometry
noncomputable section
variable {ι : Type*} [Fintype ι]

/-- The positive finite spectral memory is continuous for arbitrary real frequencies. -/
theorem continuous_finitePositiveMemory (w : ι → ℝ≥0) (ω : ι → ℝ) :
    Continuous (finitePositiveMemoryKernel w ω) := by
  classical
  unfold finitePositiveMemoryKernel realFourierCharacter
  fun_prop

/-- A memory primitive defined without any frequency denominator. -/
def finiteMemoryPrimitive (w : ι → ℝ≥0) (ω : ι → ℝ) : C(ℝ, ℂ) :=
  ⟨fun t => ∫ s in (0 : ℝ)..t, finitePositiveMemoryKernel w ω s,
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun (_ : ℝ) s => finitePositiveMemoryKernel w ω s)
      ((continuous_finitePositiveMemory w ω).comp continuous_snd) continuous_id⟩

/-- The actual retarded bath operator, with resonance allowed. -/
def finiteMemoryVolterraOperator (w : ι → ℝ≥0) (ω : ι → ℝ) :
    C(ℝ × ℝ, ℂ →L[ℝ] ℂ) := by
  refine ⟨fun p => ((ContinuousLinearMap.mul ℂ ℂ)
    (-finiteMemoryPrimitive w ω (p.1 - p.2))).restrictScalars ℝ, ?_⟩
  exact (ContinuousLinearMap.restrictScalarsIsometry ℂ ℂ ℂ ℝ ℝ).continuous.comp
    ((ContinuousLinearMap.mul ℂ ℂ).continuous.comp
      (((finiteMemoryPrimitive w ω).continuous.comp
        (continuous_fst.sub continuous_snd)).neg))

/-- All-time continuous bath response to an arbitrary continuous mild source. -/
def finiteMemoryResponse (w : ι → ℝ≥0) (ω : ι → ℝ) (f : C(ℝ, ℂ)) : C(ℝ, ℂ) :=
  continuousVolterraResponse (finiteMemoryVolterraOperator w ω) f

/-- The complete bath response determines the entire source. -/
theorem finiteMemoryResponse_injective (w : ι → ℝ≥0) (ω : ι → ℝ) :
    Function.Injective (finiteMemoryResponse w ω) :=
  continuousVolterraResponse_injective (finiteMemoryVolterraOperator w ω)

/-- A source is identifiable from precisely the same observed time prefix. -/
theorem finiteMemoryResponse_prefix_iff (w : ι → ℝ≥0) (ω : ι → ℝ)
    (f g : C(ℝ, ℂ)) (T : ℝ) :
    Set.EqOn (finiteMemoryResponse w ω f) (finiteMemoryResponse w ω g) (Set.uIcc 0 T) ↔
      Set.EqOn f g (Set.uIcc 0 T) :=
  continuousVolterraResponse_prefix_iff (finiteMemoryVolterraOperator w ω) f g T

/-- An explicit retarded-memory formula reconstructs the source at every time. -/
theorem finiteMemoryResponse_source_formula (w : ι → ℝ≥0) (ω : ι → ℝ)
    (f : C(ℝ, ℂ)) (t : ℝ) :
    finiteMemoryResponse w ω f t +
      (∫ s in (0 : ℝ)..t, finiteMemoryPrimitive w ω (t - s) * finiteMemoryResponse w ω f s) =
        f t := by
  have h := congrArg (fun u : C(ℝ, ℂ) => u t)
    (continuousVolterraSource_response (finiteMemoryVolterraOperator w ω) f)
  change finiteMemoryResponse w ω f t -
    (∫ s in (0 : ℝ)..t, -finiteMemoryPrimitive w ω (t - s) * finiteMemoryResponse w ω f s) = f t at h
  simpa only [neg_mul, intervalIntegral.integral_neg, sub_neg_eq_add] using h

/-- On nonzero detunings the integral primitive agrees with the existing closed form. -/
theorem finiteMemoryPrimitive_nonresonant (ω : ι → ℝˣ) (c : ι → ℂ) (t : ℝ) :
    finiteMemoryPrimitive (finiteBathMemoryWeight c) (fun i => (ω i : ℝ)) t =
      finiteNonresonantBathMemoryPrimitive ω c t :=
  intervalIntegral_finiteNonresonantBathMemoryKernel_eq_primitive ω c t

/-- The newly constructed memory operator is the existing nonresonant bath operator. -/
theorem finiteMemoryVolterraOperator_nonresonant (ω : ι → ℝˣ) (c : ι → ℂ) (t s : ℝ) :
    finiteMemoryVolterraOperator (finiteBathMemoryWeight c) (fun i => (ω i : ℝ)) (t, s) =
      finiteNonresonantBathVolterraKernel ω c t s := by
  change ((ContinuousLinearMap.mul ℂ ℂ) (-finiteMemoryPrimitive _ _ (t - s))).restrictScalars ℝ = _
  rw [finiteMemoryPrimitive_nonresonant]
  rfl

/-- Existing bath trajectories are instances of the arbitrary-source response. -/
theorem finiteMemoryResponse_existing_bath (a : ℂ) (ω : ι → ℝˣ) (c b : ι → ℂ) :
    (finiteMemoryResponse (finiteBathMemoryWeight c) (fun i => (ω i : ℝ))
      ⟨finiteNonresonantBathMildSource a ω c b,
        continuous_finiteNonresonantBathMildSource a ω c b⟩ : ℝ → ℂ) =
      finiteNonresonantBathVolterraSolution a ω c b := by
  have hK : (fun t s => finiteMemoryVolterraOperator
      (finiteBathMemoryWeight c) (fun i => (ω i : ℝ)) (t, s)) =
      finiteNonresonantBathVolterraKernel ω c := by
    funext t s
    exact finiteMemoryVolterraOperator_nonresonant ω c t s
  change volterraSolution (finiteNonresonantBathMildSource a ω c b)
    (fun t s => finiteMemoryVolterraOperator (finiteBathMemoryWeight c)
      (fun i => (ω i : ℝ)) (t, s)) = _
  rw [hK]
  rfl

/-- Purely resonant memory has a linear primitive, with no singular denominator. -/
theorem finiteMemoryPrimitive_zero_frequency (w : ι → ℝ≥0) (t : ℝ) :
    finiteMemoryPrimitive w (fun _ => 0) t =
      (t : ℂ) * ∑ i, ((w i : ℝ) : ℂ) := by
  change (∫ s in (0 : ℝ)..t, finitePositiveMemoryKernel w (fun _ => 0) s) = _
  simp only [finitePositiveMemoryKernel, realFourierCharacter, zero_mul, mul_zero,
    Complex.ofReal_zero, Complex.exp_zero, mul_one, intervalIntegral.integral_const,
    sub_zero, Complex.real_smul]

end
end GaloisForLFunctions.HTGeometry
