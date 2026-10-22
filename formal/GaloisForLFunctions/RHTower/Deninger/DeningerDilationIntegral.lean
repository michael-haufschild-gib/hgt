import GaloisForLFunctions.RHTower.Deninger.DeningerPullIntegrable

/-!
# Dilation scaling of the pullback integral

Dilating the argument scales the ray integral by the reciprocal, so one Abel difference integrates
to exactly `-1/(i(i+1))` times the mass of the pullback:

`∫_0^∞ (H_h((i+1)x) - H_h(ix)) dx = -(1/(i(i+1))) ∫_0^∞ H_h`.

Summing against the summatory function therefore produces the harmonic limit times that mass — and
the harmonic limit is zero.  This is the shape of the card's zero-mass statement.

* `deningerLogPull_dilation_integral` : dilation scales the ray integral.
* `deningerAbelDifference_integral` : **one Abel difference integrates to `-1/(i(i+1))` times the
  mass.**
-/

namespace RHTower

open SchwartzMap MeasureTheory

noncomputable section

/-- The mass of the pullback on the ray. -/
def deningerPullMass (h : 𝓢(ℝ, ℂ)) : ℂ := ∫ x in Set.Ioi (0 : ℝ), deningerLogPull h x

/-- **Dilation scales the ray integral by the reciprocal.** -/
theorem deningerLogPull_dilation_integral (h : 𝓢(ℝ, ℂ)) {c : ℝ} (hc : 0 < c) :
    (∫ x in Set.Ioi (0 : ℝ), deningerLogPull h (c * x)) = c⁻¹ • deningerPullMass h := by
  have hmain := integral_comp_mul_left_Ioi (deningerLogPull h) 0 hc
  rw [mul_zero] at hmain
  rw [hmain, deningerPullMass]

/-- Dilating preserves integrability on the ray. -/
theorem deningerLogPull_dilation_integrable {h : 𝓢(ℝ, ℂ)} (hh : h ∈ DeningerExpSchwartz)
    {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun x : ℝ => deningerLogPull h (c * x)) (Set.Ioi 0) := by
  refine (integrableOn_Ioi_comp_mul_left_iff (deningerLogPull h) 0 hc).mpr ?_
  rw [mul_zero]
  exact deningerLogPull_integrable hh

/-- **One Abel difference integrates to `-1/(i(i+1))` times the mass of the pullback.** -/
theorem deningerAbelDifference_integral {h : 𝓢(ℝ, ℂ)} (hh : h ∈ DeningerExpSchwartz)
    {i : ℕ} (hi : 0 < i) :
    (∫ x in Set.Ioi (0 : ℝ),
        (deningerLogPull h (((i : ℝ) + 1) * x) - deningerLogPull h ((i : ℝ) * x)))
      = (-(1 / ((i : ℝ) * ((i : ℝ) + 1)))) • deningerPullMass h := by
  have hir : (0 : ℝ) < (i : ℝ) := by exact_mod_cast hi
  have hi1 : (0 : ℝ) < (i : ℝ) + 1 := by linarith
  have hA := deningerLogPull_dilation_integrable hh hi1
  have hB := deningerLogPull_dilation_integrable hh hir
  rw [integral_sub hA hB, deningerLogPull_dilation_integral h hi1,
    deningerLogPull_dilation_integral h hir, ← sub_smul]
  congr 1
  field_simp
  ring

end

end RHTower
