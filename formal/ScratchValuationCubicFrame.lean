import GaloisForLFunctions.RHTower.RoutePPrimeGammaBaseCubicWeight
import GaloisForLFunctions.HTGeometry.TanhSubstitution

namespace RHTower

noncomputable section

def testContrast (c a : ℝ) : ℝ := Real.tanh (c * a)

theorem testContrast_iteratedDeriv_three_zero (c : ℝ) :
    iteratedDeriv 3 (testContrast c) 0 = -2 * c ^ 3 := by
  let f : ℝ → ℝ := fun a => Real.tanh (c * a)
  let g : ℝ → ℝ := fun a => c * (1 - f a ^ 2)
  let h : ℝ → ℝ := fun a => -2 * c ^ 2 * f a * (1 - f a ^ 2)
  have hf (a : ℝ) : HasDerivAt f (g a) a := by
    have ht := (HTGeometry.hasDerivAt_tanh (c * a)).comp a
      ((hasDerivAt_id a).const_mul c)
    have ht' : HasDerivAt f ((1 / Real.cosh (c * a) ^ 2) * (c * 1)) a :=
      ht.congr_of_eventuallyEq (Filter.Eventually.of_forall (by
        intro x
        rfl))
    have hcoef : (1 / Real.cosh (c * a) ^ 2) * (c * 1) = g a := by
      rw [← HTGeometry.one_sub_tanh_sq]
      dsimp only [f, g]
      ring
    rw [hcoef] at ht'
    exact ht'
  have hg (a : ℝ) : HasDerivAt g (h a) a := by
    have hsq := (hf a).pow 2
    have honeSub := (hasDerivAt_const a (1 : ℝ)).sub hsq
    have hc := honeSub.const_mul c
    have hc' : HasDerivAt g (c * (0 - (2 : ℝ) * f a ^ (2 - 1) * g a)) a :=
      hc.congr_of_eventuallyEq (Filter.Eventually.of_forall (by
        intro y
        simp [g]))
    have hcoef : c * (0 - (2 : ℝ) * f a ^ (2 - 1) * g a) = h a := by
      dsimp only [f, g, h]
      ring
    rw [hcoef] at hc'
    exact hc'
  have hh0 : HasDerivAt h (-2 * c ^ 3) 0 := by
    have hfactor := (hasDerivAt_const 0 (1 : ℝ)).sub ((hf 0).pow 2)
    have hprod := (hf 0).mul hfactor
    have hscaled := hprod.const_mul (-2 * c ^ 2)
    have hscaled' : HasDerivAt h
        (-2 * c ^ 2 *
          (g 0 * (1 - f 0 ^ 2) + f 0 * (0 - (2 : ℝ) * f 0 ^ (2 - 1) * g 0))) 0 :=
      hscaled.congr_of_eventuallyEq (Filter.Eventually.of_forall (by
        intro y
        simp only [Pi.mul_apply, Pi.sub_apply, Pi.pow_apply]
        dsimp only [h]
        ring))
    convert hscaled' using 1 <;> simp [f, g] <;> ring
  have hderivf : deriv f = g := by
    funext a
    exact (hf a).deriv
  have hderivg : deriv g = h := by
    funext a
    exact (hg a).deriv
  change iteratedDeriv 3 f 0 = _
  simp only [iteratedDeriv_succ, iteratedDeriv_zero]
  rw [hderivf, hderivg]
  exact hh0.deriv

end
end RHTower
