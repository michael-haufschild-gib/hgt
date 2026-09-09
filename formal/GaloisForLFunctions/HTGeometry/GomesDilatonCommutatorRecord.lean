import GaloisForLFunctions.HTGeometry.GomesDilatonDualShiftRigidity

/-!
# The exact invisible sector of polynomial dilaton commutator data

Experimental application of the invisible-kernel reconstruction question in
arXiv:2607.24901v1 section 4 to the corpus's actual common-connection operators.
Their commutator measures minus the second derivative of the polynomial log-weight.
The forgotten sector is exactly affine. Recording the value and slope at the origin
removes that ambiguity completely. This is a polynomial-operator analogue of the
paper's information-loss mechanism, not an identification of its gauge categories.
-/

noncomputable section
open Polynomial

namespace GaloisForLFunctions.HTGeometry

/-- The polynomial multiplier measured by the common-connection commutator. -/
def gomesDilatonCommutatorRecord : ℝ[X] →ₗ[ℝ] ℝ[X] where
  toFun H := -H.derivative.derivative
  map_add' H K := by simp only [derivative_add, neg_add]
  map_smul' c H := by
    simp only [derivative_smul, smul_neg]
    rfl

/-- The record is exactly the multiplier already proved for the Schwartz commutator. -/
theorem gomesDilatonCommutatorRecord_apply (H : ℝ[X]) :
    gomesDilatonCommutatorRecord H = -H.derivative.derivative := rfl

/-- The complete invisible sector consists of affine log-weights. -/
theorem gomesDilatonCommutatorRecord_zero_iff (H : ℝ[X]) :
    gomesDilatonCommutatorRecord H = 0 ↔ ∃ d e : ℝ, H = C d * X + C e := by
  change -H.derivative.derivative = 0 ↔ _
  rw [neg_eq_zero]
  simpa only [zero_div, C_0, zero_mul, zero_add] using
    gomesDilaton_secondDerivative_constant_iff H 0

/-- Two profiles have the same complete commutator record exactly when they differ affinely. -/
theorem gomesDilatonCommutatorRecord_eq_iff (H K : ℝ[X]) :
    gomesDilatonCommutatorRecord H = gomesDilatonCommutatorRecord K ↔
      ∃ d e : ℝ, H = K + C d * X + C e := by
  rw [← sub_eq_zero, ← map_sub, gomesDilatonCommutatorRecord_zero_iff]
  constructor
  · rintro ⟨d, e, h⟩
    refine ⟨d, e, ?_⟩
    linear_combination h
  · rintro ⟨d, e, h⟩
    refine ⟨d, e, ?_⟩
    linear_combination h

/-- Every affine perturbation is completely invisible to the commutator. -/
theorem gomesDilatonCommutatorRecord_affine (H : ℝ[X]) (d e : ℝ) :
    gomesDilatonCommutatorRecord (H + C d * X + C e) = gomesDilatonCommutatorRecord H :=
  (gomesDilatonCommutatorRecord_eq_iff _ _).mpr ⟨d, e, rfl⟩

/-- Two origin jets together with the commutator record recover the entire polynomial. -/
theorem gomesDilatonCommutatorRecord_origin_iff (H K : ℝ[X]) :
    (gomesDilatonCommutatorRecord H = gomesDilatonCommutatorRecord K ∧
      H.eval 0 = K.eval 0 ∧ H.derivative.eval 0 = K.derivative.eval 0) ↔ H = K := by
  constructor
  · rintro ⟨hr, hv, hs⟩
    obtain ⟨d, e, h⟩ := (gomesDilatonCommutatorRecord_eq_iff H K).mp hr
    have he := congrArg (fun p : ℝ[X] => p.eval 0) h
    simp only [eval_add, eval_mul, eval_C, eval_X, mul_zero, add_zero] at he
    have hezero : e = 0 := by linarith
    have hd := congrArg (fun p : ℝ[X] => p.derivative.eval 0) h
    simp only [derivative_add, derivative_C_mul, derivative_X, mul_one, derivative_C,
      eval_add, eval_C, add_zero] at hd
    have hdzero : d = 0 := by linarith
    simpa only [hdzero, hezero, C_0, zero_mul, add_zero] using h
  · rintro rfl
    exact ⟨rfl, rfl, rfl⟩

/-- The complete observation record with the two missing boundary numbers restored. -/
def gomesDilatonOriginRecord (H : ℝ[X]) : ℝ[X] × ℝ × ℝ :=
  (gomesDilatonCommutatorRecord H, H.eval 0, H.derivative.eval 0)

/-- The augmented record is faithful on every polynomial profile. -/
theorem gomesDilatonOriginRecord_injective : Function.Injective gomesDilatonOriginRecord := by
  intro H K h
  apply (gomesDilatonCommutatorRecord_origin_iff H K).mp
  exact ⟨congrArg Prod.fst h, congrArg (fun r => r.2.1) h, congrArg (fun r => r.2.2) h⟩

/-- The commutator record alone is not injective, even before considering higher-degree profiles. -/
theorem gomesDilatonCommutatorRecord_not_injective :
    ¬ Function.Injective gomesDilatonCommutatorRecord := by
  intro h
  have he : gomesDilatonCommutatorRecord (1 : ℝ[X]) = gomesDilatonCommutatorRecord 0 := by
    simp [gomesDilatonCommutatorRecord_apply]
  exact one_ne_zero (h he)

end GaloisForLFunctions.HTGeometry
