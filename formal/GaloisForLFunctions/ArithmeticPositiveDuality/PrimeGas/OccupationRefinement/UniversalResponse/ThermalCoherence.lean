import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.UniversalResponse.GibbsReturn

/-! # One real thermal readout at the origin selects the full zeta evolution -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.UniversalResponse

open Filter Topology ModeCapacities CoherentRay
open scoped NNReal

private def shifted (β : TraceTemperature) (s : Conserving) (t : ℝ≥0) : TracePoint :=
  ⟨(β.val:ℂ) + ((t:ℝ):ℂ)*s.val,by
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, s.property]
    exact lt_of_lt_of_le β.property (le_add_of_nonneg_right
      (mul_nonneg t.property (by norm_num)))⟩

private theorem shifted_partition {A : Response} {s : Conserving}
    (law : ∀ x ∈ Shares, A.val x = power s.val x) (β : TraceTemperature) (t : ℝ≥0) :
    ContinuousLinearMap.opTrace (prepared A β t) = riemannZeta ((β.val:ℂ)+((t:ℝ):ℂ)*s.val) := by
  have mode (n : ℕ+) : survivalAmplitude A n t = heat (((t:ℝ):ℂ)*s.val) n := by
    refine (law (Real.exp (-(t:ℝ) * energy n)) (survival_share t.property n)).trans ?_
    rw [power, Real.log_exp, heat, Complex.ofReal_mul, Complex.ofReal_neg]
    congr 1
    ring
  have op : prepared A β t = gibbsOperator (shifted β s t) := by
    apply ContinuousLinearMap.ext
    intro f
    apply lp.ext
    funext n
    rw [prepared, ContinuousLinearMap.comp_apply, evolution_apply, gibbsOperator_apply,
      gibbsOperator_apply, mode]
    change _ = heat ((β.val:ℂ)+((t:ℝ):ℂ)*s.val) n * f n
    rw [heat_add]
    ring
  rw [op, partition_eq_zeta]
  rfl

/-- At a single real Gibbs temperature, continuity of the real vacuum
trace at zero is equivalent to one power law and all shifted zeta traces. -/
theorem thermal_coherence_iff (A : Response) (β : TraceTemperature) :
    ContinuousAt (fun t => (ContinuousLinearMap.opTrace (prepared A β t)).re) 0 ↔
      ∃! s : Conserving, (∀ x ∈ Shares, A.val x = power s.val x) ∧
        ∀ (γ : TraceTemperature) (t : ℝ≥0),
          ContinuousLinearMap.opTrace (prepared A γ t) = riemannZeta ((γ.val:ℂ)+((t:ℝ):ℂ)*s.val) := by
  simp only [prepared_real]
  have two : 0 < energy 2 := Real.log_pos (by norm_num)
  rw [weighted_iff A (fun n => (thermalWeight_pos β n).le) (thermalWeight_summable β)
    ⟨2,two,thermalWeight_pos β 2⟩]
  constructor
  · rintro ⟨s,law,unique⟩
    exact ⟨s,⟨law,shifted_partition law⟩,fun z hz => unique z hz.1⟩
  · rintro ⟨s,⟨law,_⟩,_⟩
    exact ⟨s,law,fun z hz => Subtype.ext (unique_power fun x hx => (hz x hx).symm.trans (law x hx))⟩

#print axioms thermal_coherence_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.UniversalResponse
