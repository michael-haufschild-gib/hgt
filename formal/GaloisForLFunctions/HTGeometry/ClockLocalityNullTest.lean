import GaloisForLFunctions.HTGeometry.ClockLocalityDistributionKernel

/-!
# The two-clock locality law as a falsifiable null test

The two-mass inverse residual of the common-model class is a zeroth-order multiplication operator
with a diagonal-supported kernel. This file states the contrapositives that make the law a null
test, and proves the one consequence that is not a restatement of the operator identity: the
residual carries no memory tail, whatever memory the individual dressed responses carry.

* **Derivative channels.** A measured residual with a nonzero first- or second-order coefficient is
  not a two-mass inverse difference of the model class.
* **Kernel support.** A residual kernel charging any point off the diagonal is not one either.
* **Memory.** A residual acting by pointwise multiplication is memoryless. Response operators with
  genuine memory can nevertheless have a memoryless difference, so locality of the residual is not
  inherited from locality of the responses — it is created by the cancellation.
-/

namespace GaloisForLFunctions.HTGeometry

/-! ## Derivative-channel null test -/

namespace ScalarSecondOrderOperator

variable {ι R : Type*} [CommRing R] [Fintype ι]

theorem first_eq_zero_of_eq_twoMassDifference
    {Rop P : ScalarSecondOrderOperator ι R} {sourceGainInv : R}
    {receiverGainInv : ScalarTwoJet ι R} {μ₁ μ₂ : R}
    (h : Rop =
      sub (measuredClockInverseOperator P sourceGainInv receiverGainInv μ₁)
        (measuredClockInverseOperator P sourceGainInv receiverGainInv μ₂)) (k : ι) :
    Rop.first k = 0 := by
  rw [h, measuredClockInverseOperator_difference]
  rfl

theorem second_eq_zero_of_eq_twoMassDifference
    {Rop P : ScalarSecondOrderOperator ι R} {sourceGainInv : R}
    {receiverGainInv : ScalarTwoJet ι R} {μ₁ μ₂ : R}
    (h : Rop =
      sub (measuredClockInverseOperator P sourceGainInv receiverGainInv μ₁)
        (measuredClockInverseOperator P sourceGainInv receiverGainInv μ₂)) (i j : ι) :
    Rop.second i j = 0 := by
  rw [h, measuredClockInverseOperator_difference]
  rfl

/-- **Converse null test, first-order channel.** A residual carrying a nonzero first-order
coefficient falsifies the common local single-metric model. -/
theorem ne_twoMassDifference_of_first_ne_zero
    (Rop P : ScalarSecondOrderOperator ι R) (sourceGainInv : R)
    (receiverGainInv : ScalarTwoJet ι R) (μ₁ μ₂ : R)
    {k : ι} (hk : Rop.first k ≠ 0) :
    Rop ≠
      sub (measuredClockInverseOperator P sourceGainInv receiverGainInv μ₁)
        (measuredClockInverseOperator P sourceGainInv receiverGainInv μ₂) :=
  fun h => hk (first_eq_zero_of_eq_twoMassDifference h k)

/-- **Converse null test, second-order channel.** A residual carrying a nonzero second-order
coefficient falsifies the common local single-metric model. -/
theorem ne_twoMassDifference_of_second_ne_zero
    (Rop P : ScalarSecondOrderOperator ι R) (sourceGainInv : R)
    (receiverGainInv : ScalarTwoJet ι R) (μ₁ μ₂ : R)
    {i j : ι} (hij : Rop.second i j ≠ 0) :
    Rop ≠
      sub (measuredClockInverseOperator P sourceGainInv receiverGainInv μ₁)
        (measuredClockInverseOperator P sourceGainInv receiverGainInv μ₂) :=
  fun h => hij (second_eq_zero_of_eq_twoMassDifference h i j)

end ScalarSecondOrderOperator

/-! ## Kernel-support null test -/

noncomputable section

open scoped Distributions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {Ω : TopologicalSpace.Opens E} {n : ℕ∞} {ι : Type*} [Fintype ι]

omit [Fintype ι] in
/-- **Converse null test, kernel support.** No point off the diagonal lies in the support of a
two-mass residual kernel fiber. -/
theorem notMem_dsupport_twoMassClockLocalityKernel_of_ne [FiniteDimensional ℝ E]
    (sourceGainInv : E → ℝ) (receiverGainInv : E → ScalarTwoJet ι ℝ)
    (μ₁ μ₂ : ℝ) (x : E) (hx : x ∈ Ω) {y : E} (hy : y ≠ x) :
    y ∉ Distribution.dsupport
      (twoMassClockLocalityKernel (Ω := Ω) (n := n)
        sourceGainInv receiverGainInv μ₁ μ₂ x) := by
  intro hmem
  exact hy
    (dsupport_twoMassClockLocalityKernel_subset (Ω := Ω) (n := n)
      sourceGainInv receiverGainInv μ₁ μ₂ x hx hmem)

end

/-! ## No memory tail -/

section Memory

variable {T : Type*}

/-- A response operator is memoryless when its output at each instant depends only on the input at
that instant. -/
def Memoryless {V W : Type*} (Op : (T → V) → (T → W)) : Prop :=
  ∀ (f g : T → V) (t : T), f t = g t → Op f t = Op g t

/-- Pointwise multiplication by a coefficient field is memoryless. -/
theorem memoryless_pointwiseMul (kappa : T → ℝ) :
    Memoryless (fun f : T → ℝ => fun t => kappa t * f t) := by
  intro f g t h
  simp only
  rw [h]

/-- **No memory tail.** A residual that acts by pointwise multiplication is memoryless, whatever
memory the individual dressed responses carry. -/
theorem memoryless_residual_of_pointwiseMul
    {Q₁ Q₂ : (T → ℝ) → (T → ℝ)} (kappa : T → ℝ)
    (hres : ∀ (f : T → ℝ) (t : T), Q₁ f t - Q₂ f t = kappa t * f t) :
    Memoryless (fun f : T → ℝ => fun t => Q₁ f t - Q₂ f t) := by
  intro f g t h
  simp only
  rw [hres f t, hres g t, h]

/-- A delayed response has memory. -/
theorem not_memoryless_delay :
    ¬ Memoryless (fun f : ℝ → ℝ => fun t => f (t - 1)) := by
  intro hmem
  have h := hmem (fun _ => 0) (fun s => 1 - s ^ (2 : ℕ)) 1 (by norm_num)
  norm_num at h

/-- **Locality of the residual is created by the cancellation, not inherited.** Two response
operators can both carry memory while their difference is a pointwise multiplication and hence
memoryless. -/
theorem exists_memoryful_responses_with_memoryless_residual :
    ∃ Q₁ Q₂ : (ℝ → ℝ) → (ℝ → ℝ),
      ¬ Memoryless Q₁ ∧ ¬ Memoryless Q₂ ∧
        Memoryless (fun f : ℝ → ℝ => fun t => Q₁ f t - Q₂ f t) := by
  refine ⟨fun f => fun t => f (t - 1) + f t, fun f => fun t => f (t - 1), ?_, ?_, ?_⟩
  · intro hmem
    have h := hmem (fun _ => 0) (fun s => 1 - s ^ (2 : ℕ)) 1 (by norm_num)
    norm_num at h
  · exact not_memoryless_delay
  · refine memoryless_residual_of_pointwiseMul (fun _ => 1) ?_
    intro f t
    ring

end Memory

end GaloisForLFunctions.HTGeometry
