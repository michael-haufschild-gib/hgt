import GaloisForLFunctions.RHTower.DeningerCompactOrbitWeightNoGo
import GaloisForLFunctions.RHTower.DeningerMeyerSeminorm

/-!
# Compact traces forget the noncompact escape direction

The damped translates `h_s = e^{-as}T_s\psi` disappear from every compact orbit — periodization
turns the translation into a rotation and leaves the damping factor `e^{-as}` in front — while the
Meyer seminorm `q_{a,0}(h) = \sup_t e^{a|t|}\|h(t)\|` reads them at the translated point and cancels
the damping exactly.  So the family stays bounded away from `0` in the source while its trace tends
to `0`, which is the precise datum the compact tomography loses.

* `deningerPeriodizationSum_expShift` : periodization intertwines translation with rotation.
* `deningerPeriodizationSum_periodic` : `Per_L h` is `L`-periodic.
* `deningerEscapeFamily_periodizationSum` : **the trace carries the damping factor.**
* `deningerEscapeFamily_meyer_ge` : **the Meyer seminorm cancels the damping.**
-/

namespace RHTower

open SchwartzMap

noncomputable section

/-- **Periodization intertwines translation with rotation of the orbit.** -/
theorem deningerPeriodizationSum_expShift (f : 𝓢(ℝ, ℂ)) (a L t : ℝ) :
    deningerPeriodizationSum (deningerExpShift a f) L t
      = deningerPeriodizationSum f L (t + a) := by
  rw [deningerPeriodizationSum, deningerPeriodizationSum]
  refine tsum_congr fun j => ?_
  show ((deningerExpShift a f : 𝓢(ℝ, ℂ)) : ℝ → ℂ) (t + (j : ℝ) * L)
    = (f : ℝ → ℂ) (t + a + (j : ℝ) * L)
  rw [deningerExpShift_apply]
  congr 1
  ring

/-- **The periodization is periodic.** -/
theorem deningerPeriodizationSum_periodic (f : 𝓢(ℝ, ℂ)) (L t : ℝ) :
    deningerPeriodizationSum f L (t + L) = deningerPeriodizationSum f L t := by
  rw [← deningerPeriodizationSum_expShift f L L t, deningerPeriodizationSum_shift]

/-- The damped escape family `h_s = e^{-as}T_s h`. -/
def deningerEscapeFamily (a s : ℝ) (h : DeningerExpSchwartz) : DeningerExpSchwartz :=
  ((Real.exp (-(a * s)) : ℝ) : ℂ) • deningerExpShiftSource (-s) h

theorem deningerEscapeFamily_apply (a s : ℝ) (h : DeningerExpSchwartz) (t : ℝ) :
    ((deningerEscapeFamily a s h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) t
      = ((Real.exp (-(a * s)) : ℝ) : ℂ) * ((h : 𝓢(ℝ, ℂ)) : ℝ → ℂ) (t - s) := by
  show ((Real.exp (-(a * s)) : ℝ) : ℂ)
      * ((deningerExpShiftSource (-s) h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) t = _
  rw [deningerExpShiftSource_apply, sub_eq_add_neg]

/-- **Every compact trace of the escape family carries the damping factor**, so it tends to zero as
the translation runs to infinity. -/
theorem deningerEscapeFamily_periodizationSum (a s L t : ℝ) (h : DeningerExpSchwartz) :
    deningerPeriodizationSum ((deningerEscapeFamily a s h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) L t
      = ((Real.exp (-(a * s)) : ℝ) : ℂ)
        * deningerPeriodizationSum ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) L (t - s) := by
  rw [deningerPeriodizationSum, deningerPeriodizationSum, ← tsum_mul_left]
  refine tsum_congr fun j => ?_
  rw [deningerEscapeFamily_apply]
  congr 2
  ring

/-- **The Meyer seminorm cancels the damping factor exactly.**  Reading the weight at the translated
point `s + u` contributes `e^{a(s+u)}e^{-as}\|h(u)\| = e^{au}\|h(u)\|`, independently of `s`. -/
theorem deningerEscapeFamily_meyer_ge {a s u : ℝ} (hsu : 0 ≤ s + u) (h : DeningerExpSchwartz) :
    Real.exp (a * u) * ‖((h : 𝓢(ℝ, ℂ)) : ℝ → ℂ) u‖
      ≤ deningerMeyerSeminormFun a 0 (deningerEscapeFamily a s h) := by
  refine le_trans (le_of_eq ?_) (deningerMeyerWeight_le a 0 (deningerEscapeFamily a s h) (s + u))
  rw [deningerMeyerWeight, norm_iteratedFDeriv_zero, deningerEscapeFamily_apply,
    abs_of_nonneg hsu, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), show s + u - s = u by ring, ← mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- **The escape family is bounded away from zero in the source.**  If `h` does not vanish at some
point, no member of its escape family is small in the Meyer seminorm, uniformly in the escape
parameter. -/
theorem deningerEscapeFamily_meyer_pos {a u : ℝ}
    {h : DeningerExpSchwartz} (hu : ((h : 𝓢(ℝ, ℂ)) : ℝ → ℂ) u ≠ 0) {s : ℝ} (hsu : 0 ≤ s + u) :
    0 < deningerMeyerSeminormFun a 0 (deningerEscapeFamily a s h) := by
  refine lt_of_lt_of_le ?_ (deningerEscapeFamily_meyer_ge hsu h)
  have h1 : 0 < Real.exp (a * u) := Real.exp_pos _
  have h2 : 0 < ‖((h : 𝓢(ℝ, ℂ)) : ℝ → ℂ) u‖ := norm_pos_iff.2 hu
  positivity

end

end RHTower
