import GaloisForLFunctions.RHTower.MobiusCausalFlatLimit
import GaloisForLFunctions.RHTower.ZetaPoleSplit

/-!
# The pole-unit form of the coupled causal multiplier

Writing every zeta value through the entire pole unit `Z(s) = (s-1)ζ(s)`, the coupled causal
multiplier becomes an explicit quotient by `z`:

```text
M_ω(z) = N_ω(z)/z,
N_ω(z) = Z(1+z)·q_ω(z) - q_ω(0),      q_ω(z) = (2ω+z)/[(1+ω+z)Z(1+2ω+z)],
```

because `Z(1) = 1`.  In this form the apparent pole at `z = 0` is visibly absent — `N_ω(0) = 0` —
and the same cancellation persists after differentiating in the parameter:

```text
∂_ω M_ω(z) = [Z(1+z)·q̇_ω(z) - q̇_ω(0)]/z .
```

This is the representation in which the boundary estimates near `z = 0` are uniform in `ω`.
-/

open Filter Topology

namespace RHTower

noncomputable section

theorem zetaPoleUnit_one_add_two_mul_add_ne_zero {ω : ℝ} (hω : 0 < ω) {z : ℂ} (hz : 0 ≤ z.re) :
    zetaPoleUnit (1 + 2 * (ω : ℂ) + z) ≠ 0 :=
  zetaPoleUnit_ne_zero (one_add_two_mul_add_ne_one hω hz)
    (riemannZeta_one_add_two_mul_add_ne_zero hω hz)

theorem zetaPoleUnit_one_add_two_mul_ne_zero {ω : ℝ} (hω : 0 < ω) :
    zetaPoleUnit (1 + 2 * (ω : ℂ)) ≠ 0 := by
  have h := zetaPoleUnit_one_add_two_mul_add_ne_zero hω (z := 0) (by simp)
  simpa using h

theorem one_add_ofReal_ne_zero {ω : ℝ} (hω : 0 < ω) : (1 : ℂ) + (ω : ℂ) ≠ 0 := by
  intro h
  have hre : ((1 : ℂ) + (ω : ℂ)).re = 0 := by rw [h]; simp
  simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re] at hre
  linarith

/-- The shifted pole-unit quotient `q_ω(z) = (2ω+z)/[(1+ω+z)Z(1+2ω+z)]`. -/
def mobiusCausalQ (ω : ℝ) (z : ℂ) : ℂ :=
  (2 * (ω : ℂ) + z) / ((1 + (ω : ℂ) + z) * zetaPoleUnit (1 + 2 * (ω : ℂ) + z))

/-- The pole-free numerator `N_ω` of the coupled causal multiplier. -/
def mobiusCausalNumerator (ω : ℝ) (z : ℂ) : ℂ :=
  zetaPoleUnit (1 + z) * mobiusCausalQ ω z - mobiusCausalQ ω 0

@[simp] theorem mobiusCausalNumerator_zero (ω : ℝ) : mobiusCausalNumerator ω 0 = 0 := by
  rw [mobiusCausalNumerator]
  norm_num [zetaPoleUnit_one]

theorem mobiusCausalQ_zero_eq (ω : ℝ) :
    mobiusCausalQ ω 0 = 2 * (ω : ℂ) / ((1 + (ω : ℂ)) * zetaPoleUnit (1 + 2 * (ω : ℂ))) := by
  rw [mobiusCausalQ]
  norm_num

/-- **The pole-unit form of `M_ω`.** -/
theorem mobiusCausalMultiplier_eq_numerator_div {ω : ℝ} (hω : 0 < ω) {z : ℂ} (hz : 0 ≤ z.re)
    (hz0 : z ≠ 0) :
    mobiusCausalMultiplier ω z = mobiusCausalNumerator ω z / z := by
  have hζ := riemannZeta_one_add_two_mul_add_ne_zero hω hz
  have hζ0 := riemannZeta_one_add_two_mul_ne_zero hω
  have hlin := one_add_ofReal_add_ne_zero hω hz
  have hω0 := one_add_ofReal_ne_zero hω
  have hZ := zetaPoleUnit_one_add_two_mul_add_ne_zero hω hz
  have hZ0 := zetaPoleUnit_one_add_two_mul_ne_zero hω
  have hshift : (2 : ℂ) * (ω : ℂ) + z ≠ 0 := by
    intro h
    have hre : ((2 : ℂ) * (ω : ℂ) + z).re = 0 := by rw [h]; simp
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.re_ofNat, Complex.im_ofNat, mul_zero, sub_zero] at hre
    linarith
  have hωC : ((ω : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt hω
  have hω2 : (2 : ℂ) * (ω : ℂ) ≠ 0 := mul_ne_zero two_ne_zero hωC
  -- rewrite the three zeta values through the pole unit
  have e1 : riemannZeta (1 + z) = zetaPoleUnit (1 + z) / z := by
    have hne : (1 : ℂ) + z ≠ 1 := one_add_ne_one hz0
    rw [zetaPoleUnit_of_ne hne]
    have : (1 : ℂ) + z - 1 = z := by ring
    rw [this]
    field_simp
  have e2 : riemannZeta (1 + 2 * (ω : ℂ) + z)
      = zetaPoleUnit (1 + 2 * (ω : ℂ) + z) / (2 * (ω : ℂ) + z) := by
    have hne : (1 : ℂ) + 2 * (ω : ℂ) + z ≠ 1 := one_add_two_mul_add_ne_one hω hz
    rw [zetaPoleUnit_of_ne hne]
    have : (1 : ℂ) + 2 * (ω : ℂ) + z - 1 = 2 * (ω : ℂ) + z := by ring
    rw [this]
    field_simp
  have e3 : riemannZeta (1 + 2 * (ω : ℂ))
      = zetaPoleUnit (1 + 2 * (ω : ℂ)) / (2 * (ω : ℂ)) := by
    have hne : (1 : ℂ) + 2 * (ω : ℂ) ≠ 1 := by
      have h := one_add_two_mul_add_ne_one hω (z := 0) (by simp)
      simpa using h
    rw [zetaPoleUnit_of_ne hne]
    have : (1 : ℂ) + 2 * (ω : ℂ) - 1 = 2 * (ω : ℂ) := by ring
    rw [this]
    field_simp
  rw [mobiusCausalMultiplier, mobiusCausalNumerator, mobiusCausalQ, mobiusCausalQ_zero_eq,
    e1, e2, e3]
  field_simp

/-! ### The parameter derivative in pole-unit form -/

theorem hasDerivAt_zetaPoleUnit_shift (z : ℂ) (ω : ℝ) :
    HasDerivAt (fun w : ℝ => zetaPoleUnit (1 + 2 * (w : ℂ) + z))
      (2 * deriv zetaPoleUnit (1 + 2 * (ω : ℂ) + z)) ω := by
  have hlin := hasDerivAt_linear_shift 2 z ω
  have hZ : HasDerivAt zetaPoleUnit (deriv zetaPoleUnit (1 + 2 * (ω : ℂ) + z))
      (1 + 2 * (ω : ℂ) + z) := (differentiable_zetaPoleUnit _).hasDerivAt
  have h := hZ.scomp ω hlin
  simpa [Function.comp, smul_eq_mul] using h

/-- The parameter derivative of the shifted pole-unit quotient. -/
def mobiusCausalQDeriv (ω : ℝ) (z : ℂ) : ℂ :=
  (2 * ((1 + (ω : ℂ) + z) * zetaPoleUnit (1 + 2 * (ω : ℂ) + z)) -
      (2 * (ω : ℂ) + z) * (zetaPoleUnit (1 + 2 * (ω : ℂ) + z) +
        (1 + (ω : ℂ) + z) * (2 * deriv zetaPoleUnit (1 + 2 * (ω : ℂ) + z)))) /
    ((1 + (ω : ℂ) + z) * zetaPoleUnit (1 + 2 * (ω : ℂ) + z)) ^ 2

theorem hasDerivAt_mobiusCausalQ {ω : ℝ} (hω : 0 < ω) {z : ℂ} (hz : 0 ≤ z.re) :
    HasDerivAt (fun w : ℝ => mobiusCausalQ w z) (mobiusCausalQDeriv ω z) ω := by
  have hlin : HasDerivAt (fun w : ℝ => 1 + (w : ℂ) + z) 1 ω := by
    simpa using hasDerivAt_linear_shift 1 z ω
  have hnum : HasDerivAt (fun w : ℝ => 2 * (w : ℂ) + z) 2 ω := by
    have h : HasDerivAt (fun w : ℝ => ((w : ℝ) : ℂ)) 1 ω := Complex.ofRealCLM.hasDerivAt
    simpa using (h.const_mul (2 : ℂ)).add_const z
  have hden := hlin.mul (hasDerivAt_zetaPoleUnit_shift z ω)
  have hdenne : (1 + (ω : ℂ) + z) * zetaPoleUnit (1 + 2 * (ω : ℂ) + z) ≠ 0 :=
    mul_ne_zero (one_add_ofReal_add_ne_zero hω hz)
      (zetaPoleUnit_one_add_two_mul_add_ne_zero hω hz)
  have h := hnum.div hden hdenne
  refine h.congr_deriv ?_
  simp only [Pi.mul_apply]
  rw [mobiusCausalQDeriv]
  ring

/-- The parameter derivative of the pole-free numerator. -/
def mobiusCausalNumeratorDeriv (ω : ℝ) (z : ℂ) : ℂ :=
  zetaPoleUnit (1 + z) * mobiusCausalQDeriv ω z - mobiusCausalQDeriv ω 0

theorem hasDerivAt_mobiusCausalNumerator {ω : ℝ} (hω : 0 < ω) {z : ℂ} (hz : 0 ≤ z.re) :
    HasDerivAt (fun w : ℝ => mobiusCausalNumerator w z) (mobiusCausalNumeratorDeriv ω z) ω := by
  have h1 := (hasDerivAt_mobiusCausalQ hω hz).const_mul (zetaPoleUnit (1 + z))
  have h2 := hasDerivAt_mobiusCausalQ hω (z := 0) (by simp)
  exact h1.sub h2

/-- **The parameter derivative vanishes at the origin.** -/
theorem mobiusCausalNumeratorDeriv_zero {ω : ℝ} (hω : 0 < ω) :
    mobiusCausalNumeratorDeriv ω 0 = 0 := by
  have h := hasDerivAt_mobiusCausalNumerator hω (z := 0) (by simp)
  have hconst : HasDerivAt (fun w : ℝ => mobiusCausalNumerator w 0) 0 ω := by
    have : (fun w : ℝ => mobiusCausalNumerator w (0 : ℂ)) = fun _ : ℝ => (0 : ℂ) :=
      funext fun w => mobiusCausalNumerator_zero w
    rw [this]
    exact hasDerivAt_const ω 0
  exact h.unique hconst

/-- **The pole-unit form of the parameter derivative.** -/
theorem mobiusCausalMultiplierDeriv_eq_numeratorDeriv_div {ω : ℝ} (hω : 0 < ω) {z : ℂ}
    (hz : 0 ≤ z.re) (hz0 : z ≠ 0) :
    mobiusCausalMultiplierDeriv ω z = mobiusCausalNumeratorDeriv ω z / z := by
  have hM := hasDerivAt_mobiusCausalMultiplier hω hz hz0
  have hN := (hasDerivAt_mobiusCausalNumerator hω hz).div_const z
  have heq : (fun w : ℝ => mobiusCausalMultiplier w z)
      =ᶠ[nhds ω] fun w : ℝ => mobiusCausalNumerator w z / z := by
    filter_upwards [(isOpen_Ioi (a := (0 : ℝ))).mem_nhds hω] with w hw
    exact mobiusCausalMultiplier_eq_numerator_div hw hz hz0
  exact hM.unique (hN.congr_of_eventuallyEq heq)

end

end RHTower
