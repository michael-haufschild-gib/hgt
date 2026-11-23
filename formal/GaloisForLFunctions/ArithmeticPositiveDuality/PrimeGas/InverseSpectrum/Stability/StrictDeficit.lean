import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.Stability.FaithfulPairing
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.Stability.TraceBound

/-! # Strict Hilbert–Schmidt stability of positive conserving propagation

The fourth-trace loss splits into squared Hilbert–Schmidt error and a
faithful positive pairing. Equality in the sharp stability estimate
therefore singles out critical heat.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open ContinuousLinearMap

def squareError (G : GasOp) := criticalOperator^2-G^2

private theorem square_facts (G : Propagator) :
    (G.val^2).IsPositive ∧ (G.val^2).IsHilbertSchmidt ∧ Function.Injective (G.val^2 : GasOp) := by
  obtain ⟨U,hu,_⟩ := (full_isometry_iff G.val).mp G.property.2
  have hsa := G.property.1.isSelfAdjoint.star_eq
  have hgram : G.val^2 = star U.toContinuousLinearMap*(squareHeat.val*U.toContinuousLinearMap) := by
    rw [show G.val^2 = star G.val*G.val by rw [hsa,pow_two],hu,star_mul,critical_isPositive.isSelfAdjoint.star_eq]
    change _ = star U.toContinuousLinearMap*(criticalOperator^2*U.toContinuousLinearMap)
    rw [pow_two,mul_assoc,mul_assoc]
  have hi : Function.Injective G.val := hu ▸ critical_injective.comp U.injective
  have hh : (G.val^2).IsHilbertSchmidt := by
    rw [hgram]
    exact (squareHeat.property.2.comp_right _).comp_left _
  refine ⟨?_,hh,hi.comp hi⟩
  have hp := isPositive_adjoint_comp_self G.val
  change (star G.val*G.val).IsPositive at hp
  rwa [hsa,← pow_two] at hp

private theorem mass_difference (G : Propagator) : traceLoss G.val = hsNormSq squareHeat.val-hsNormSq (G.val^2) := by
  have hA := _root_.HTGeometry.opTrace_sq_eq_ofReal_hsNormSq squareHeat.property.2 squareHeat.property.1.star_eq
  have hB := _root_.HTGeometry.opTrace_sq_eq_ofReal_hsNormSq (square_facts G).2.1 (G.property.1.isSelfAdjoint.pow 2).star_eq
  change opTrace ((criticalOperator^2)^2) = _ at hA
  rw [critical_fourth_trace] at hA
  rw [traceLoss,hA,show (4:ℕ) = 2*2 from rfl,pow_mul,hB,Complex.ofReal_re,Complex.ofReal_re]

/-- Exact polarization identity for squared heat and its fourth moment. -/
theorem hs_trace_decomposition (G : Propagator) :
    traceLoss G.val = hsNormSq (squareError G.val)+2*(hsInner (squareError G.val) (G.val^2)).re := by
  have hB := (square_facts G).2.1
  have he := hsNormSq_sub squareHeat.property.2 hB
  change hsNormSq (squareError G.val) = hsNormSq squareHeat.val-2*(hsInner squareHeat.val (G.val^2)).re+
    hsNormSq (G.val^2) at he
  have hh := congrArg Complex.re (hsInner_sub_left squareHeat.property.2 hB hB)
  rw [Complex.sub_re] at hh
  have hself : (hsInner (G.val^2) (G.val^2)).re = hsNormSq (G.val^2) := hsInner_self_re hB
  change (hsInner (squareError G.val) (G.val^2)).re = _ at hh
  rw [mass_difference,he,hh,hself]
  ring

private theorem error_zero_iff (G : Propagator) : squareError G.val = 0 ↔ G.val = criticalOperator := by
  change criticalOperator^2-G.val^2 = 0 ↔ _
  rw [sub_eq_zero]
  constructor
  · intro h
    exact (positiveRoot_sq G.property.1).symm.trans
      ((congrArg (fun A : GasOp => positiveRoot A) h.symm).trans (positiveRoot_sq critical_isPositive))
  · rintro he
    rw [he]

/-- The Hilbert–Schmidt error exhausts the trace loss exactly at critical heat. -/
theorem hs_trace_equality_iff (G : Propagator) :
    hsNormSq (squareError G.val) ≤ traceLoss G.val ∧
      (hsNormSq (squareError G.val) = traceLoss G.val ↔ G.val = criticalOperator) := by
  obtain ⟨hb,hh,hi⟩ := square_facts G
  have hc : (squareError G.val).IsHilbertSchmidt := squareHeat.property.2.sub hh
  obtain ⟨hpos,hzero⟩ := faithful_hs_pairing hb hh hi (square_trace_stability G).1 hc
  change 0 ≤ (hsInner (squareError G.val) (G.val^2)).re at hpos
  change (hsInner (squareError G.val) (G.val^2)).re = 0 ↔ squareError G.val = 0 at hzero
  have h := hs_trace_decomposition G
  refine ⟨by linarith only [h,hpos],?_⟩
  rw [← error_zero_iff G,← hzero]
  constructor <;> intro he <;> linarith only [h,he]

/-- Every physical nonzero error lies strictly above the fourth-power boundary in trace loss. -/
theorem strict_trace_stability_iff (G : Propagator) :
    ‖criticalOperator-G.val‖^4 < traceLoss G.val ↔ G.val ≠ criticalOperator := by
  obtain ⟨hh,he⟩ := hs_trace_equality_iff G
  constructor
  · intro h eq
    have hz : squareError G.val = 0 := (error_zero_iff G).mpr eq
    have ht := he.mpr eq
    rw [hz,hsNormSq_zero] at ht
    rw [← ht] at h
    rw [eq,sub_self,norm_zero,zero_pow (by decide : 4 ≠ 0)] at h
    exact lt_irrefl _ h
  · intro h
    have hb := (positive_square_comparison critical_isPositive G.property.1 (square_trace_stability G).1).2.2
    have hc : (squareError G.val).IsHilbertSchmidt := squareHeat.property.2.sub (square_facts G).2.1
    have hs := (pow_le_pow_left₀ (norm_nonneg _) (norm_le_hsNorm hc) 2).trans_eq (sq_hsNorm _)
    change ‖criticalOperator-G.val‖^2 ≤ ‖squareError G.val‖ at hb
    rw [show (4:ℕ) = 2*2 from rfl,pow_mul]
    exact ((pow_le_pow_left₀ (sq_nonneg _) hb 2).trans hs).trans_lt (lt_of_le_of_ne hh (fun e => h (he.mp e)))

#print axioms hs_trace_decomposition
#print axioms hs_trace_equality_iff
#print axioms strict_trace_stability_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
