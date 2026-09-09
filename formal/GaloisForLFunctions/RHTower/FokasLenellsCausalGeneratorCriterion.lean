import GaloisForLFunctions.RHTower.FokasLenellsCausalOrbitIntegral

/-!
# Actual infinitesimal-generator criterion for causal Cauchy evolution

The right derivative at zero exists with value v exactly when every finite
time satisfies T_t u - u = integral_0^t T_s v ds. Right derivatives propagate
by the actual semigroup law; the one-sided fundamental theorem of calculus
then gives the integrated identity. The converse differentiates the genuine
vector primitive. No generator-domain hypothesis is supplied externally.
-/

open Complex MeasureTheory Set Filter Topology
open scoped NNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

local instance : CompleteSpace (hardyL2ᗮ) := hardyL2.isClosed_orthogonal.completeSpace_coe

/-- The literal forward orbit with the identity extension before time zero. -/
def causalForwardOrbit (u : hardyL2ᗮ) (r : ℝ) : hardyL2ᗮ :=
  causalLowerCauchyEvolution r.toNNReal u

/-- The actual extended vector orbit is continuous. -/
theorem causalForwardOrbit_continuous (u : hardyL2ᗮ) : Continuous (causalForwardOrbit u) :=
  (causalLowerCauchyEvolution_continuous u).comp continuous_real_toNNReal

/-- The actual orbit starts at its original datum. -/
theorem causalForwardOrbit_zero (u : hardyL2ᗮ) : causalForwardOrbit u 0 = u := by
  simp only [causalForwardOrbit,Real.toNNReal_zero,causalLowerCauchyEvolution_zero]

private theorem right_derivative_shift (u v : hardyL2ᗮ)
    (h : HasDerivWithinAt (causalForwardOrbit u) v (Ioi 0) 0) (t : ℝ≥0) :
    HasDerivWithinAt (causalForwardOrbit u) (causalLowerCauchyEvolution t v) (Ioi (t:ℝ)) (t:ℝ) := by
  have hbase : HasDerivWithinAt (causalForwardOrbit u) v (Ioi 0) ((t:ℝ)-(t:ℝ)) := by
    simpa only [sub_self] using h
  have hsub : HasDerivWithinAt (fun r : ℝ => r-(t:ℝ)) 1 (Ioi (t:ℝ)) (t:ℝ) :=
    ((hasDerivAt_id (t:ℝ)).sub_const (t:ℝ)).hasDerivWithinAt
  have hm : MapsTo (fun r : ℝ => r-(t:ℝ)) (Ioi (t:ℝ)) (Ioi 0) := by
    intro r hr
    change (t:ℝ) < r at hr
    change 0 < r-(t:ℝ)
    exact sub_pos.mpr hr
  have hs : HasDerivWithinAt (fun r : ℝ => causalForwardOrbit u (r-(t:ℝ))) v (Ioi (t:ℝ)) (t:ℝ) := by
    simpa only [Function.comp_def,one_smul] using
      hbase.scomp (h := fun r : ℝ => r-(t:ℝ)) (t:ℝ) hsub hm
  have ht := ((causalLowerCauchyEvolution t).restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt (t:ℝ) hs
  change HasDerivWithinAt (fun r : ℝ => causalLowerCauchyEvolution t (causalForwardOrbit u (r-(t:ℝ))))
    (causalLowerCauchyEvolution t v) (Ioi (t:ℝ)) (t:ℝ) at ht
  apply ht.congr
  · intro r hr
    have hr0 : 0 ≤ r := t.property.trans hr.le
    have hrt : 0 ≤ r-(t:ℝ) := sub_nonneg.mpr hr.le
    have he : t+(r-(t:ℝ)).toNNReal = r.toNNReal := by
      apply Subtype.ext
      change ((t+(r-(t:ℝ)).toNNReal : ℝ≥0) : ℝ) = (r.toNNReal : ℝ)
      rw [NNReal.coe_add,Real.coe_toNNReal (r-(t:ℝ)) hrt,Real.coe_toNNReal r hr0]
      ring
    change causalLowerCauchyEvolution r.toNNReal u =
      causalLowerCauchyEvolution t (causalLowerCauchyEvolution (r-(t:ℝ)).toNNReal u)
    rw [← causalLowerCauchyEvolution_add,he]
  · simp only [sub_self,causalForwardOrbit,Real.toNNReal_coe,Real.toNNReal_zero,causalLowerCauchyEvolution_zero]

/-- Exact full-domain criterion for the actual right infinitesimal derivative of the forward orbit. -/
theorem causalForwardOrbit_rightDerivative_iff (u v : hardyL2ᗮ) :
    HasDerivWithinAt (causalForwardOrbit u) v (Ioi 0) 0 ↔
      ∀ t : ℝ≥0, causalLowerCauchyEvolution t u-u = causalOrbitIntegral t v := by
  constructor
  · intro h t
    have hd : ∀ x ∈ Ioo 0 (t:ℝ), HasDerivWithinAt (causalForwardOrbit u)
        (causalForwardOrbit v x) (Ioi x) x := by
      intro x hx
      have hh := right_derivative_shift u v h ⟨x,hx.1.le⟩
      change HasDerivWithinAt (causalForwardOrbit u) (causalLowerCauchyEvolution ⟨x,hx.1.le⟩ v)
        (Ioi x) x at hh
      have he : x.toNNReal = (⟨x,hx.1.le⟩ : ℝ≥0) := Real.toNNReal_of_nonneg hx.1.le
      change HasDerivWithinAt (causalForwardOrbit u) (causalLowerCauchyEvolution x.toNNReal v) (Ioi x) x
      rw [he]
      exact hh
    have hi := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le t.property
      (causalForwardOrbit_continuous u).continuousOn hd
      ((causalForwardOrbit_continuous v).intervalIntegrable 0 (t:ℝ))
    rw [causalForwardOrbit_zero] at hi
    have he : (t:ℝ).toNNReal = t := Real.toNNReal_coe
    change (∫ r in (0:ℝ)..(t:ℝ), causalLowerCauchyEvolution r.toNNReal v) =
      causalLowerCauchyEvolution (t:ℝ).toNNReal u-u at hi
    rw [he] at hi
    exact hi.symm
  · intro h
    have hd := (causalOrbitPrimitive_hasDerivAt_zero v).const_add u
    apply hd.hasDerivWithinAt.congr
    · intro r hr
      have he := h r.toNNReal
      change causalLowerCauchyEvolution r.toNNReal u-u = causalOrbitPrimitive (r.toNNReal:ℝ) v at he
      rw [Real.coe_toNNReal r hr.le] at he
      change causalLowerCauchyEvolution r.toNNReal u = u+causalOrbitPrimitive r v
      rw [← he,← add_sub_assoc,add_sub_cancel_left]
    · rw [causalForwardOrbit_zero,causalOrbitPrimitive_zero,add_zero]

end
end RHTower.FokasLenells
