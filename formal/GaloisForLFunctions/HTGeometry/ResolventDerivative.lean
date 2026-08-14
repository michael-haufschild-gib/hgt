import GaloisForLFunctions.HTGeometry.BoundedResolventNeumann
import GaloisForLFunctions.HTGeometry.GammaPhaseFactor
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Differentiating the shifted-symbol resolvent along the frequency ray

Along a ray the shift `c(η) = L + r(η)/2` varies with the symbol, and the resolvent
`B(c(η))⁻¹` inherits the classical resolvent derivative

`d/dη B(c(η))⁻¹ = -c'(η) B(c(η))⁻¹ B(c(η))⁻¹`.

Combined with the Neumann bound this makes the resolvent an admissible integrating factor for the
oscillatory transport: one integration by parts converts an oscillatory integral into two
absolutely convergent ones, each carrying an extra power of the frequency.
-/

open Complex

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]

variable {T : 𝔸}

/-- The shifted symbol operator as a unit. -/
def shiftedSymbolUnit (c : ℝ) (T : 𝔸) (hT : ‖T‖ / 2 < c) : 𝔸ˣ :=
  ⟨shiftedSymbolOp c T, shiftedSymbolInv c T, shiftedSymbolOp_mul_inv hT,
    inv_mul_shiftedSymbolOp hT⟩

omit [NormOneClass 𝔸] in
@[simp] theorem shiftedSymbolUnit_val {c : ℝ} (hT : ‖T‖ / 2 < c) :
    ((shiftedSymbolUnit c T hT : 𝔸ˣ) : 𝔸) = shiftedSymbolOp c T := rfl

omit [NormOneClass 𝔸] in
@[simp] theorem shiftedSymbolUnit_inv_val {c : ℝ} (hT : ‖T‖ / 2 < c) :
    (((shiftedSymbolUnit c T hT)⁻¹ : 𝔸ˣ) : 𝔸) = shiftedSymbolInv c T := rfl

omit [NormOneClass 𝔸] in
theorem ringInverse_shiftedSymbolOp {c : ℝ} (hT : ‖T‖ / 2 < c) :
    Ring.inverse (shiftedSymbolOp c T) = shiftedSymbolInv c T := by
  have h := Ring.inverse_unit (shiftedSymbolUnit c T hT)
  simpa using h

omit [CompleteSpace 𝔸] [NormOneClass 𝔸] in
/-- The shift enters the symbol operator linearly. -/
theorem hasDerivAt_shiftedSymbolOp {c c' : ℝ → ℝ} {η : ℝ} (T : 𝔸)
    (hc : HasDerivAt c (c' η) η) :
    HasDerivAt (fun x => shiftedSymbolOp (c x) T) ((((c' η : ℝ)) : ℂ) • (1 : 𝔸)) η := by
  have h1 : HasDerivAt (fun x : ℝ => (((c x : ℝ)) : ℂ)) (((c' η : ℝ)) : ℂ) η := hc.ofReal_comp
  have h2 : HasDerivAt (fun x : ℝ => (((c x : ℝ)) : ℂ) • (1 : 𝔸))
      ((((c' η : ℝ)) : ℂ) • (1 : 𝔸)) η := h1.smul_const (1 : 𝔸)
  exact h2.sub_const _

omit [NormOneClass 𝔸] in
/-- **The resolvent derivative along the ray.** -/
theorem hasDerivAt_shiftedSymbolInv {c c' : ℝ → ℝ} {η : ℝ}
    (hT : ‖T‖ / 2 < c η) (hc : HasDerivAt c (c' η) η) :
    HasDerivAt (fun x => shiftedSymbolInv (c x) T)
      (-((((c' η : ℝ)) : ℂ) • (shiftedSymbolInv (c η) T * shiftedSymbolInv (c η) T))) η := by
  have hbase := hasDerivAt_shiftedSymbolOp (c := c) (c' := c') T hc
  have hunit := hasFDerivAt_ringInverse (𝕜 := ℝ) (shiftedSymbolUnit (c η) T hT)
  have hcomp := hunit.comp_hasDerivAt η hbase
  have hval : (-((ContinuousLinearMap.mulLeftRight ℝ 𝔸)
        (((shiftedSymbolUnit (c η) T hT)⁻¹ : 𝔸ˣ) : 𝔸))
        (((shiftedSymbolUnit (c η) T hT)⁻¹ : 𝔸ˣ) : 𝔸)) ((((c' η : ℝ)) : ℂ) • (1 : 𝔸))
      = -((((c' η : ℝ)) : ℂ) • (shiftedSymbolInv (c η) T * shiftedSymbolInv (c η) T)) := by
    simp only [neg_apply, ContinuousLinearMap.mulLeftRight_apply,
      shiftedSymbolUnit_inv_val]
    rw [mul_smul_comm, smul_mul_assoc, mul_one]
  rw [hval] at hcomp
  have hnear : ∀ᶠ x in nhds η, shiftedSymbolInv (c x) T
      = Ring.inverse (shiftedSymbolOp (c x) T) := by
    filter_upwards [continuousAt_const.eventually_lt hc.continuousAt hT] with x hx
    exact (ringInverse_shiftedSymbolOp hx).symm
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [hnear] with x hx using hx

/-- The Neumann bound is monotone in the shift: a larger shift gives a smaller resolvent. -/
theorem norm_shiftedSymbolInv_le_of_le {c d : ℝ} (hT : ‖T‖ / 2 < d) (hdc : d ≤ c) :
    ‖shiftedSymbolInv c T‖ ≤ (d - ‖T‖ / 2)⁻¹ := by
  have hTc : ‖T‖ / 2 < c := lt_of_lt_of_le hT hdc
  refine le_trans (norm_shiftedSymbolInv_le hTc) ?_
  have hd : (0:ℝ) < d - ‖T‖ / 2 := by linarith
  exact inv_anti₀ hd (by linarith)

end

end GaloisForLFunctions.HTGeometry
