import GaloisForLFunctions.HTGeometry.IntervalCutoff
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# The cut-off integrating factor of the Gamma frequency transport

On the positive frequency half-line the Gamma equation in logarithmic normal form has the scalar
coefficient `-1/(2η) + (i/2) r(η)`, whose integrating factor is `η^{1/2} exp(-(i/2)∫ r)`.  Neither
the coefficient nor the factor extends smoothly across the origin, so both are multiplied by a
cutoff that is one near the interval under study and vanishes near the origin.  The resulting
functions are globally smooth, compactly supported, and of temperate growth, hence admissible
multipliers on Schwartz space, and they satisfy the integrating-factor identities on the interval.
-/

open Set Complex

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {χ : ℝ → ℝ} {Rint r : ℝ → ℝ} {a : ℝ}

/-- A cutoff multiple of a function smooth on the positive half-line is globally smooth. -/
theorem contDiff_cutoff_mul {F : ℝ → ℂ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (ha : 0 < a)
    (hzero : ∀ x, x ≤ a / 2 → χ x = 0)
    (hF : ∀ x : ℝ, 0 < x → ContDiffAt ℝ (⊤ : ℕ∞) F x) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => ((χ x : ℝ) : ℂ) * F x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  rcases lt_or_ge x (a / 2) with hx | hx
  · have hev : (fun y : ℝ => ((χ y : ℝ) : ℂ) * F y) =ᶠ[nhds x] fun _ => (0 : ℂ) := by
      filter_upwards [(isOpen_Iio (a := a / 2)).mem_nhds hx] with y hy
      rw [hzero y (le_of_lt hy)]
      simp
    exact (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq hev
  · have hxpos : 0 < x := lt_of_lt_of_le (by linarith) hx
    exact (Complex.ofRealCLM.contDiff.comp hχ).contDiffAt.mul (hF x hxpos)

/-- A cutoff multiple has compact support. -/
theorem hasCompactSupport_cutoff_mul {F : ℝ → ℂ} (hcs : HasCompactSupport χ) :
    HasCompactSupport (fun x : ℝ => ((χ x : ℝ) : ℂ) * F x) := by
  refine HasCompactSupport.intro hcs.isCompact fun x hx => ?_
  rw [image_eq_zero_of_notMem_tsupport hx]
  simp

/-- The cut-off reciprocal coordinate. -/
def invCut (χ : ℝ → ℝ) : ℝ → ℂ := fun x => ((χ x : ℝ) : ℂ) * ((x : ℂ))⁻¹

/-- The cut-off square-root integrating factor of the Gamma transport. -/
def sqrtFactor (χ : ℝ → ℝ) (Rint : ℝ → ℝ) : ℝ → ℂ :=
  fun x => ((χ x : ℝ) : ℂ) * (((Real.sqrt x : ℝ) : ℂ) * Complex.exp (-(I / 2) * ((Rint x : ℝ) : ℂ)))

/-- The reciprocal cut-off integrating factor. -/
def sqrtFactorInv (χ : ℝ → ℝ) (Rint : ℝ → ℝ) : ℝ → ℂ :=
  fun x => ((χ x : ℝ) : ℂ)
    * ((((Real.sqrt x : ℝ) : ℂ))⁻¹ * Complex.exp ((I / 2) * ((Rint x : ℝ) : ℂ)))

/-- The cut-off scalar coefficient of the Gamma frequency equation. -/
def gammaMultiplier (χ : ℝ → ℝ) (r : ℝ → ℝ) : ℝ → ℂ :=
  fun x => -(invCut χ x) / 2 + (I / 2) * ((χ x * r x : ℝ) : ℂ)

theorem contDiff_invCut (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (ha : 0 < a)
    (hzero : ∀ x, x ≤ a / 2 → χ x = 0) : ContDiff ℝ (⊤ : ℕ∞) (invCut χ) := by
  refine contDiff_cutoff_mul hχ ha hzero fun x hx => ?_
  exact (Complex.ofRealCLM.contDiff.contDiffAt).inv (by
    simpa using ne_of_gt hx)

theorem contDiff_sqrtFactor (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (ha : 0 < a)
    (hzero : ∀ x, x ≤ a / 2 → χ x = 0) (hR : ContDiff ℝ (⊤ : ℕ∞) Rint) :
    ContDiff ℝ (⊤ : ℕ∞) (sqrtFactor χ Rint) := by
  refine contDiff_cutoff_mul hχ ha hzero fun x hx => ?_
  have hsq : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : ℝ => ((Real.sqrt y : ℝ) : ℂ)) x :=
    Complex.ofRealCLM.contDiff.comp_contDiffAt x (Real.contDiffAt_sqrt (ne_of_gt hx))
  have hexp : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun y : ℝ => Complex.exp (-(I / 2) * ((Rint y : ℝ) : ℂ))) x :=
    Complex.contDiff_exp.contDiffAt.comp x
      (contDiffAt_const.mul (Complex.ofRealCLM.contDiff.comp hR).contDiffAt)
  exact hsq.mul hexp

theorem contDiff_sqrtFactorInv (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (ha : 0 < a)
    (hzero : ∀ x, x ≤ a / 2 → χ x = 0) (hR : ContDiff ℝ (⊤ : ℕ∞) Rint) :
    ContDiff ℝ (⊤ : ℕ∞) (sqrtFactorInv χ Rint) := by
  refine contDiff_cutoff_mul hχ ha hzero fun x hx => ?_
  have hsqne : (((Real.sqrt x : ℝ) : ℂ)) ≠ 0 := by
    simpa using ne_of_gt (Real.sqrt_pos.mpr hx)
  have hsq : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : ℝ => (((Real.sqrt y : ℝ) : ℂ))⁻¹) x :=
    (Complex.ofRealCLM.contDiff.comp_contDiffAt x (Real.contDiffAt_sqrt (ne_of_gt hx))).inv hsqne
  have hexp : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun y : ℝ => Complex.exp ((I / 2) * ((Rint y : ℝ) : ℂ))) x :=
    Complex.contDiff_exp.contDiffAt.comp x
      (contDiffAt_const.mul (Complex.ofRealCLM.contDiff.comp hR).contDiffAt)
  exact hsq.mul hexp

theorem contDiff_gammaMultiplier (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (ha : 0 < a)
    (hzero : ∀ x, x ≤ a / 2 → χ x = 0) (hr : ContDiff ℝ (⊤ : ℕ∞) r) :
    ContDiff ℝ (⊤ : ℕ∞) (gammaMultiplier χ r) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => -(invCut χ x) / 2) :=
    ((contDiff_invCut hχ ha hzero).neg).div_const 2
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => (I / 2) * ((χ x * r x : ℝ) : ℂ)) :=
    contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (hχ.mul hr))
  exact h1.add h2

theorem hasCompactSupport_gammaMultiplier (hcs : HasCompactSupport χ) :
    HasCompactSupport (gammaMultiplier χ r) := by
  refine HasCompactSupport.intro hcs.isCompact fun x hx => ?_
  have hχx : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
  rw [gammaMultiplier, invCut, hχx]
  simp

theorem hasTemperateGrowth_invCut (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hcs : HasCompactSupport χ)
    (ha : 0 < a) (hzero : ∀ x, x ≤ a / 2 → χ x = 0) :
    Function.HasTemperateGrowth (invCut χ) :=
  (hasCompactSupport_cutoff_mul (F := fun x : ℝ => ((x : ℂ))⁻¹) hcs).hasTemperateGrowth
    (contDiff_invCut hχ ha hzero)

theorem hasTemperateGrowth_sqrtFactor (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hcs : HasCompactSupport χ)
    (ha : 0 < a) (hzero : ∀ x, x ≤ a / 2 → χ x = 0) (hR : ContDiff ℝ (⊤ : ℕ∞) Rint) :
    Function.HasTemperateGrowth (sqrtFactor χ Rint) :=
  (hasCompactSupport_cutoff_mul (F := fun x : ℝ =>
      ((Real.sqrt x : ℝ) : ℂ) * Complex.exp (-(I / 2) * ((Rint x : ℝ) : ℂ))) hcs).hasTemperateGrowth
    (contDiff_sqrtFactor hχ ha hzero hR)

theorem hasTemperateGrowth_sqrtFactorInv (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hcs : HasCompactSupport χ)
    (ha : 0 < a) (hzero : ∀ x, x ≤ a / 2 → χ x = 0) (hR : ContDiff ℝ (⊤ : ℕ∞) Rint) :
    Function.HasTemperateGrowth (sqrtFactorInv χ Rint) :=
  (hasCompactSupport_cutoff_mul (F := fun x : ℝ =>
      (((Real.sqrt x : ℝ) : ℂ))⁻¹ * Complex.exp ((I / 2) * ((Rint x : ℝ) : ℂ)))
      hcs).hasTemperateGrowth (contDiff_sqrtFactorInv hχ ha hzero hR)

theorem hasTemperateGrowth_gammaMultiplier (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hcs : HasCompactSupport χ) (ha : 0 < a) (hzero : ∀ x, x ≤ a / 2 → χ x = 0)
    (hr : ContDiff ℝ (⊤ : ℕ∞) r) : Function.HasTemperateGrowth (gammaMultiplier χ r) :=
  (hasCompactSupport_gammaMultiplier hcs).hasTemperateGrowth
    (contDiff_gammaMultiplier hχ ha hzero hr)

theorem hasTemperateGrowth_rCut (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hcs : HasCompactSupport χ)
    (hr : ContDiff ℝ (⊤ : ℕ∞) r) :
    Function.HasTemperateGrowth (fun x : ℝ => ((χ x * r x : ℝ) : ℂ)) := by
  refine HasCompactSupport.hasTemperateGrowth ?_ (Complex.ofRealCLM.contDiff.comp (hχ.mul hr))
  refine HasCompactSupport.intro hcs.isCompact fun x hx => ?_
  have hχx : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
  rw [hχx]
  simp

/-- On the region where the cutoff is one the reciprocal coordinate is exactly `1/η`. -/
theorem invCut_mul_self {x : ℝ} (hx : 0 < x) (h1 : χ x = 1) : invCut χ x * (x : ℂ) = 1 := by
  have hne : ((x : ℂ)) ≠ 0 := by simpa using ne_of_gt hx
  rw [invCut, h1]
  push_cast
  field_simp

/-- The reciprocal coordinate solves its own Riccati equation where the cutoff is one. -/
theorem deriv_invCut {x : ℝ} (hx : 0 < x) (h1 : ∀ᶠ y in nhds x, χ y = 1) :
    deriv (invCut χ) x = -(invCut χ x * invCut χ x) := by
  have hne : ((x : ℂ)) ≠ 0 := by simpa using ne_of_gt hx
  have hev : invCut χ =ᶠ[nhds x] fun y : ℝ => ((y : ℂ))⁻¹ := by
    filter_upwards [h1] with y hy
    rw [invCut, hy]
    simp
  have hbase : HasDerivAt (fun y : ℝ => ((y : ℂ))) 1 x := by
    have h0 := (hasDerivAt_id x).ofReal_comp
    rw [Complex.ofReal_one] at h0
    exact h0
  have hd : HasDerivAt (fun y : ℝ => ((y : ℂ))⁻¹) (-1 / ((x : ℂ)) ^ 2) x := hbase.inv hne
  have hx1 : χ x = 1 := h1.self_of_nhds
  rw [hev.deriv_eq, hd.deriv, invCut, hx1]
  push_cast
  field_simp

/-- The integrating factor is the reciprocal of the inverse integrating factor on the interval. -/
theorem sqrtFactor_mul_inv {x : ℝ} (hx : 0 < x) (h1 : χ x = 1) :
    sqrtFactor χ Rint x * sqrtFactorInv χ Rint x = 1 := by
  have hsq : (((Real.sqrt x : ℝ) : ℂ)) ≠ 0 := by
    simpa using ne_of_gt (Real.sqrt_pos.mpr hx)
  have hexp : Complex.exp (-(I / 2) * ((Rint x : ℝ) : ℂ))
      * Complex.exp ((I / 2) * ((Rint x : ℝ) : ℂ)) = 1 := by
    rw [← Complex.exp_add]
    have : -(I / 2) * ((Rint x : ℝ) : ℂ) + (I / 2) * ((Rint x : ℝ) : ℂ) = 0 := by ring
    rw [this, Complex.exp_zero]
  rw [sqrtFactor, sqrtFactorInv, h1]
  push_cast
  rw [show ((1 : ℂ) * (((Real.sqrt x : ℝ) : ℂ) * Complex.exp (-(I / 2) * ((Rint x : ℝ) : ℂ))))
        * ((1 : ℂ) * ((((Real.sqrt x : ℝ) : ℂ))⁻¹ * Complex.exp ((I / 2) * ((Rint x : ℝ) : ℂ))))
      = (((Real.sqrt x : ℝ) : ℂ) * (((Real.sqrt x : ℝ) : ℂ))⁻¹)
        * (Complex.exp (-(I / 2) * ((Rint x : ℝ) : ℂ))
          * Complex.exp ((I / 2) * ((Rint x : ℝ) : ℂ))) from by ring]
  rw [mul_inv_cancel₀ hsq, hexp, one_mul]

/-- **The integrating-factor identity.**  Where the cutoff is one, the cut-off square-root factor
solves `g' = -m g` for the cut-off Gamma coefficient. -/
theorem deriv_sqrtFactor {x : ℝ} (hx : 0 < x) (h1 : ∀ᶠ y in nhds x, χ y = 1)
    (hRderiv : ∀ y : ℝ, HasDerivAt Rint (r y) y) :
    deriv (sqrtFactor χ Rint) x = -(gammaMultiplier χ r x * sqrtFactor χ Rint x) := by
  have hx1 : χ x = 1 := h1.self_of_nhds
  set s : ℝ := Real.sqrt x with hs
  have hspos : 0 < s := Real.sqrt_pos.mpr hx
  have hss : s * s = x := Real.mul_self_sqrt hx.le
  have hev : sqrtFactor χ Rint =ᶠ[nhds x]
      fun y : ℝ => ((Real.sqrt y : ℝ) : ℂ) * Complex.exp (-(I / 2) * ((Rint y : ℝ) : ℂ)) := by
    filter_upwards [h1] with y hy
    rw [sqrtFactor, hy]
    simp
  have hdsqrt : HasDerivAt (fun y : ℝ => ((Real.sqrt y : ℝ) : ℂ))
      (((1 / (2 * s) : ℝ) : ℂ)) x := (Real.hasDerivAt_sqrt (ne_of_gt hx)).ofReal_comp
  have hdexp : HasDerivAt (fun y : ℝ => Complex.exp (-(I / 2) * ((Rint y : ℝ) : ℂ)))
      (Complex.exp (-(I / 2) * ((Rint x : ℝ) : ℂ)) * (-(I / 2) * ((r x : ℝ) : ℂ))) x :=
    HasDerivAt.cexp (((hRderiv x).ofReal_comp).const_mul (-(I / 2)))
  have hprod : HasDerivAt (fun y : ℝ => ((Real.sqrt y : ℝ) : ℂ)
      * Complex.exp (-(I / 2) * ((Rint y : ℝ) : ℂ)))
      (((1 / (2 * s) : ℝ) : ℂ) * Complex.exp (-(I / 2) * ((Rint x : ℝ) : ℂ))
        + ((Real.sqrt x : ℝ) : ℂ)
          * (Complex.exp (-(I / 2) * ((Rint x : ℝ) : ℂ)) * (-(I / 2) * ((r x : ℝ) : ℂ)))) x :=
    hdsqrt.mul hdexp
  rw [hev.deriv_eq, hprod.deriv]
  have hsC : ((s : ℝ) : ℂ) ≠ 0 := by simpa using ne_of_gt hspos
  have hxC : ((x : ℂ)) ≠ 0 := by simpa using ne_of_gt hx
  have hssC : ((s : ℝ) : ℂ) * ((s : ℝ) : ℂ) = ((x : ℂ)) := by
    rw [← Complex.ofReal_mul, hss]
  rw [gammaMultiplier, sqrtFactor, invCut, hx1, ← hs]
  push_cast
  rw [← hssC]
  field_simp
  ring

end

end GaloisForLFunctions.HTGeometry
