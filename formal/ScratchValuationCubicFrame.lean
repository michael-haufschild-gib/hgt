import GaloisForLFunctions.RHTower.RestrictedUnitaryCubicRelativeIndex

open Complex Matrix

namespace RHTower

noncomputable section

def testContrast (c a : ℝ) : ℝ := Real.tanh (c * a)

theorem testContrast_iteratedDeriv_three_zero (c : ℝ) :
    iteratedDeriv 3 (testContrast c) 0 = -2 * c ^ 3 := by
  let f : ℝ → ℝ := fun a => Real.tanh (c * a)
  let g : ℝ → ℝ := fun a => c * (1 - f a ^ 2)
  let h : ℝ → ℝ := fun a => -2 * c ^ 2 * f a * (1 - f a ^ 2)
  have hf (a : ℝ) : HasDerivAt f (g a) a := by
    have hlin : HasDerivAt (fun x : ℝ => c * x) c a := by
      simpa using (hasDerivAt_id a).const_mul c
    have ht := (HTGeometry.hasDerivAt_tanh (c * a)).comp a hlin
    rw [HTGeometry.one_sub_tanh_sq] at ht
    simpa [f, g, mul_comm, mul_left_comm, mul_assoc] using ht
  have hg (a : ℝ) : HasDerivAt g (h a) a := by
    have hsq := (hf a).pow 2
    have honeSub := (hasDerivAt_const a (1 : ℝ)).sub hsq
    have hc := honeSub.const_mul c
    convert hc using 1 <;> simp [f, g, h] <;> ring
  have hh0 : HasDerivAt h (-2 * c ^ 3) 0 := by
    have hfactor := (hasDerivAt_const 0 (1 : ℝ)).sub (hf 0).pow 2
    have hprod := (hf 0).mul hfactor
    have hscaled := hprod.const_mul (-2 * c ^ 2)
    convert hscaled using 1 <;> simp [f, g, h] <;> ring
  have hderivf : deriv f = g := by
    funext a
    exact (hf a).deriv
  have hderivg : deriv g = h := by
    funext a
    exact (hg a).deriv
  change iteratedDeriv 3 f 0 = _
  rw [show (3 : ℕ) = 2 + 1 by omega, iteratedDeriv_succ]
  rw [show (2 : ℕ) = 1 + 1 by omega, iteratedDeriv_succ]
  rw [show (1 : ℕ) = 0 + 1 by omega, iteratedDeriv_succ]
  simp only [iteratedDeriv_zero]
  rw [hderivf, hderivg]
  exact hh0.deriv

end
end RHTower
