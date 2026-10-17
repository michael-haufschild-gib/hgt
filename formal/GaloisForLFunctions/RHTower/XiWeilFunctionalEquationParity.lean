import GaloisForLFunctions.RHTower.DeningerArithmeticOrientedHilbertHodge
import GaloisForLFunctions.RHTower.XiWeilLineConjHilbert
import GaloisForLFunctions.RHTower.CCMFirstClockLandauCompleteness

/-!
# The two functional-equation Weil sectors are isometric

The Deninger orientation multiplier reverses pure functional-equation
parity and commutes with critical-line reflection. Its Hilbert extension
therefore preserves the complete Weil form and identifies the two FE
sectors. These are the sectors for `z -> -z`, not the positive and negative
sectors for `z -> conj z`.
-/

open Complex

namespace RHTower

noncomputable section

/-- The source height gap makes FE orientation invariant under critical-line reflection. -/
theorem deningerArithmeticFEOrientation_lineConj (q : XiZeroCopy) :
    deningerArithmeticFEOrientation (xiZeroCopyLineConjEquiv q) =
      deningerArithmeticFEOrientation q := by
  have hre : (xiSpectralPoint q).re ≠ 0 := by
    intro h
    have hgap := four_lt_abs_re_xiSpectralPoint q
    rw [h, abs_zero] at hgap
    norm_num at hgap
  simp only [deningerArithmeticFEOrientation, xiSpectralPoint_lineConj,
    Complex.conj_re, Complex.conj_im]
  by_cases hpos : 0 < (xiSpectralPoint q).re
  · simp [hpos]
  · have hneg : (xiSpectralPoint q).re < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hre
    simp [hpos, hneg]

/-- The bounded FE orientation multiplier on the complete Xi divisor Hilbert carrier. -/
def xiFEOrientationLp (v : lp (fun _ : XiZeroCopy => ℂ) 2) :
    lp (fun _ : XiZeroCopy => ℂ) 2 :=
  ⟨fun q => deningerArithmeticFEOrientation q * v q,
    HilbertSchmidt.memℓp_of_sq
      ((HilbertSchmidt.summable_coe_sq v).congr fun q => by simp)⟩

@[simp] theorem xiFEOrientationLp_apply
    (v : lp (fun _ : XiZeroCopy => ℂ) 2) (q : XiZeroCopy) :
    xiFEOrientationLp v q = deningerArithmeticFEOrientation q * v q := rfl

/-- The orientation multiplier is its own inverse. -/
theorem xiFEOrientationLp_sq (v : lp (fun _ : XiZeroCopy => ℂ) 2) :
    xiFEOrientationLp (xiFEOrientationLp v) = v := by
  apply Subtype.ext
  funext q
  simp only [xiFEOrientationLp_apply, ← mul_assoc, deningerArithmeticFEOrientation_sq,
    one_mul]

theorem norm_xiFEOrientationLp (v : lp (fun _ : XiZeroCopy => ℂ) 2) :
    ‖xiFEOrientationLp v‖ = ‖v‖ := by
  have hs : ‖xiFEOrientationLp v‖ ^ (2 : ℕ) = ‖v‖ ^ (2 : ℕ) := by
    rw [HilbertSchmidt.lp_norm_sq_eq, HilbertSchmidt.lp_norm_sq_eq]
    simp only [xiFEOrientationLp_apply, norm_mul, norm_deningerArithmeticFEOrientation,
      one_mul]
  nlinarith [norm_nonneg (xiFEOrientationLp v), norm_nonneg v]

/-- Involutive complex-linear isometry carrying one FE sector to the other. -/
def xiFEOrientationLinearIsometry :
    lp (fun _ : XiZeroCopy => ℂ) 2 →ₗᵢ[ℂ] lp (fun _ : XiZeroCopy => ℂ) 2 where
  toFun := xiFEOrientationLp
  map_add' v w := by
    apply Subtype.ext
    funext q
    change deningerArithmeticFEOrientation q * (v q + w q) =
      deningerArithmeticFEOrientation q * v q + deningerArithmeticFEOrientation q * w q
    ring
  map_smul' c v := by
    apply Subtype.ext
    funext q
    change deningerArithmeticFEOrientation q * (c * v q) =
      c * (deningerArithmeticFEOrientation q * v q)
    ring
  norm_map' := norm_xiFEOrientationLp

/-- Orientation transport commutes with the exact Weil reflection. -/
theorem xiWeilLineConjLp_xiFEOrientationLp (v : lp (fun _ : XiZeroCopy => ℂ) 2) :
    xiWeilLineConjLp (xiFEOrientationLp v) = xiFEOrientationLp (xiWeilLineConjLp v) := by
  apply Subtype.ext
  funext q
  simp only [xiWeilLineConjLp_apply, xiFEOrientationLp_apply,
    deningerArithmeticFEOrientation_lineConj]

/-- The full sesquilinear Weil form, including every mixed term, is preserved. -/
theorem xiWeilForm_xiFEOrientationLp (v w : lp (fun _ : XiZeroCopy => ℂ) 2) :
    inner ℂ (xiWeilLineConjLp (xiFEOrientationLp v)) (xiFEOrientationLp w) =
      inner ℂ (xiWeilLineConjLp v) w := by
  rw [xiWeilLineConjLp_xiFEOrientationLp]
  exact xiFEOrientationLinearIsometry.inner_map_map _ _

theorem xiWeilHilbertQuadratic_xiFEOrientationLp
    (v : lp (fun _ : XiZeroCopy => ℂ) 2) :
    xiWeilHilbertQuadratic (xiFEOrientationLp v) = xiWeilHilbertQuadratic v := by
  exact congrArg Complex.re (xiWeilForm_xiFEOrientationLp v v)

/-- Pure functional-equation parity on the multiplicity-exact Hilbert carrier. -/
def XiFunctionalEquationParity (s : ℂ) (v : lp (fun _ : XiZeroCopy => ℂ) 2) : Prop :=
  ∀ q, v (xiZeroCopyReflectEquiv q) = s * v q

/-- Orientation multiplication reverses FE parity without changing Weil energy. -/
theorem xiFEOrientationLp_parity {s : ℂ} {v : lp (fun _ : XiZeroCopy => ℂ) 2}
    (hv : XiFunctionalEquationParity s v) :
    XiFunctionalEquationParity (-s) (xiFEOrientationLp v) := by
  intro q
  rw [xiFEOrientationLp_apply, xiFEOrientationLp_apply,
    deningerArithmeticFEOrientation_reflect, hv q]
  ring

theorem xiFEOrientationLp_parity_iff (s : ℂ) (v : lp (fun _ : XiZeroCopy => ℂ) 2) :
    XiFunctionalEquationParity (-s) (xiFEOrientationLp v) ↔
      XiFunctionalEquationParity s v := by
  constructor
  · intro h
    simpa only [neg_neg, xiFEOrientationLp_sq] using xiFEOrientationLp_parity h
  · exact xiFEOrientationLp_parity

/-- Positivity on either FE sector is exactly positivity on the other. -/
theorem xiWeilHilbertQuadratic_FE_sector_nonnegative_iff (s : ℂ) :
    (∀ v, XiFunctionalEquationParity s v → 0 ≤ xiWeilHilbertQuadratic v) ↔
      (∀ v, XiFunctionalEquationParity (-s) v → 0 ≤ xiWeilHilbertQuadratic v) := by
  constructor
  · intro h v hv
    have hp : XiFunctionalEquationParity s (xiFEOrientationLp v) := by
      simpa only [neg_neg] using xiFEOrientationLp_parity hv
    simpa only [xiWeilHilbertQuadratic_xiFEOrientationLp] using h (xiFEOrientationLp v) hp
  · intro h v hv
    simpa only [xiWeilHilbertQuadratic_xiFEOrientationLp] using
      h (xiFEOrientationLp v) (xiFEOrientationLp_parity hv)

end

end RHTower
