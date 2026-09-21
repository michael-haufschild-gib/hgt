import GaloisForLFunctions.RHTower.FZZCigarParityExternalBRSTSingleBranchAngularNoGo

/-!
# FZZ external-BRST branch primitive on a cyclic arc

The marked external-BRST branch factor is the literal compact holonomy
character. This leaf evaluates its primitive on a variable cyclic arc. It is
the analytic input needed to test the genuinely ordered two-vertex branch
kernel, rather than an unweighted or same-point compact average.
-/

open Complex MeasureTheory

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Complex angular frequency of the literal compact branch character. -/
def fzzCigarExternalBRSTAngularFrequency (p : ℤ) : ℂ :=
  ((2 * Real.pi * (p : ℝ) : ℝ) : ℂ) * Complex.I

private theorem fzzCigarExternalBRSTAngularFrequency_ne_zero
    {p : ℤ} (hp : p ≠ 0) : fzzCigarExternalBRSTAngularFrequency p ≠ 0 := by
  unfold fzzCigarExternalBRSTAngularFrequency
  apply mul_ne_zero
  · exact Complex.ofReal_ne_zero.mpr
      (mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) (by exact_mod_cast hp))
  · exact Complex.I_ne_zero

/-- Exact primitive of a nontrivial literal branch character over a cyclic
arc beginning at the fixed cut base point. -/
theorem intervalIntegral_fzzCigarExternalBRSTAngularBranch_to
    (p : ℤ) (t : ℝ) (hp : p ≠ 0) :
    (∫ s in (0 : ℝ)..t, RHTower.fzzTorusHolonomyCharacter p s) =
      (RHTower.fzzTorusHolonomyCharacter p t - 1) /
        fzzCigarExternalBRSTAngularFrequency p := by
  let c : ℂ := fzzCigarExternalBRSTAngularFrequency p
  have hc : c ≠ 0 := fzzCigarExternalBRSTAngularFrequency_ne_zero hp
  have hderiv : ∀ x : ℝ, HasDerivAt
      (fun s : ℝ => RHTower.fzzTorusHolonomyCharacter p s / c)
      (RHTower.fzzTorusHolonomyCharacter p x) x := by
    intro x
    change HasDerivAt (fun s : ℝ => Complex.exp (c * (s : ℂ)) / c)
      (Complex.exp (c * (x : ℂ))) x
    have hlin : HasDerivAt (fun s : ℝ => c * (s : ℂ)) c x := by
      simpa only [mul_one] using (Complex.hasDerivAt_ofReal x).const_mul c
    have hd := hlin.cexp.div_const c
    have hval : Complex.exp (c * (x : ℂ)) * c / c =
        Complex.exp (c * (x : ℂ)) := by
      field_simp
    rw [hval] at hd
    exact hd
  have hint : IntervalIntegrable (RHTower.fzzTorusHolonomyCharacter p)
      volume 0 t :=
    RHTower.continuous_fzzTorusHolonomyCharacter p |>.intervalIntegrable 0 t
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := t) (fun x _ => hderiv x) hint
  rw [hFTC]
  change Complex.exp (c * (t : ℂ)) / c - Complex.exp (c * (0 : ℂ)) / c =
    (Complex.exp (c * (t : ℂ)) - 1) / c
  rw [mul_zero, Complex.exp_zero]
  ring

end

end GaloisForLFunctions.RHTower
