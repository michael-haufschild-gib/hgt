import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.UniversalResponse.Classification

/-! # Thermal trace of an unknown conserving response -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.UniversalResponse

open Set ModeCapacities CoherentRay CoassociativeSplitting

abbrev TraceDuration := Set.Ioi (2:ℝ)

def duration (t : TraceDuration) : Duration := ⟨t.val,lt_trans (by norm_num : (0:ℝ)<2) t.property⟩

def thermalPoint (s : Conserving) (t : TraceDuration) : TracePoint :=
  ⟨(t.val:ℂ)*s.val,by
    rw [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,s.property]
    linarith only [show 2<t.val from t.property]⟩

/-- The actual apparatus at forward time t has the Gibbs operator of
parameter ts as its emitted-vacuum branch. -/
def thermalRead (A : ℝ → ℂ) (s : Conserving) (t : TraceDuration) :=
  ∃ T : Gas →ₗᵢ[ℂ] PairGas,
    (∀ f x, T f x=wave (routing A (emit t.val) (survive t.val)) f x) ∧
    vacuumSlice ∘L T.toContinuousLinearMap=gibbsOperator (thermalPoint s t) ∧
    ContinuousLinearMap.opTrace (vacuumSlice ∘L T.toContinuousLinearMap)=riemannZeta ((t.val:ℂ)*s.val)

private theorem thermal_of_power {A : ℝ → ℂ} {s : Conserving} (h : ∀ x ∈ Shares, A x=power s.val x)
    (t : TraceDuration) : thermalRead A s t := by
  have eqn : routing A (emit t.val) (survive t.val)=kernel s.val (emit t.val) (survive t.val) :=
    funext fun a => funext fun b => h _ (branch_mem (emit_pos (duration t).property) (survive_pos t.val) a b)
  have op : noEmission s (duration t)=gibbsOperator (thermalPoint s t) := by
    apply ContinuousLinearMap.ext
    intro f
    apply lp.ext
    funext n
    rw [noEmission_apply,gibbsOperator_apply]
    rfl
  refine ⟨instrument s (duration t),?_,op,?_⟩
  · intro f x
    rw [eqn]
    exact instrument_apply _ _ _ _
  · change ContinuousLinearMap.opTrace (noEmission s (duration t))=_
    rw [op,partition_eq_zeta]
    rfl

/-- The equal-split measurement on a bounded sequential response determines
a unique critical-line exponent for both the waves and all its thermal traces. -/
theorem thermal_classification (A : ℝ → ℂ) :
    ContinuousOn A Shares ∧ sequential A ∧ bounded A ∧ balanced A ↔
      ∃! s : Conserving, (∀ x ∈ Shares, A x=power s.val x) ∧ ∀ t, thermalRead A s t := by
  rw [balanced_classification]
  constructor
  · rintro ⟨s,h,unique⟩
    exact ⟨s,⟨h,thermal_of_power h⟩,fun w hw => unique w hw.1⟩
  · rintro ⟨s,⟨h,_⟩,_⟩
    exact ⟨s,h,fun w hw => Subtype.ext (unique_power fun x hx => (hw x hx).symm.trans (h x hx))⟩

#print axioms thermal_classification

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.UniversalResponse
