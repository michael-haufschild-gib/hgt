import GaloisForLFunctions.RHTower.FieldOneFiniteStageFiniteFourierSelfMap

/-!
# Polarized finite-stage nonarchimedean Fourier Parseval

This file upgrades the exact norm Plancherel theorem for the finite nonarchimedean factor of
Connes--Marcolli's finite-stage adeles to the full Hermitian Parseval identity.  Polarization is
proved inside Lean and applied to the actual transported Bruhat Fourier endomorphism; no
factorization hypothesis is imposed on the test functions.
-/

namespace GaloisForLFunctions.RHTower
noncomputable section
open IsDedekindDomain MeasureTheory Set TopologicalSpace
open scoped BigOperators ComplexConjugate

private theorem fieldOneComplex_star_mul_polarization (a b : ℂ) :
    star a * b =
      ((Complex.normSq (a + b) : ℂ) -
          (Complex.normSq (a - b) : ℂ) -
        Complex.I * (Complex.normSq (a + Complex.I * b) : ℂ) +
        Complex.I * (Complex.normSq (a - Complex.I * b) : ℂ)) / 4 := by
  change conj a * b = _
  simp only [Complex.normSq_eq_conj_mul_self, map_add, map_sub, map_mul,
    Complex.conj_I]
  ring_nf
  simp [Complex.I_sq]
  ring

theorem fieldOneFiniteStageFiniteBruhat_normSq_integrable
    (S : Finset (HeightOneSpectrum ℤ))
    (f : FieldOneFiniteStageFiniteBruhatSchwartz S) :
    Integrable (fun x => (Complex.normSq (f.1 x) : ℂ))
      (Measure.pi fun v : ↑S => fieldOneLocalSelfDualAddHaar v.1) := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact Complex.continuous_ofReal.comp
      (Complex.continuous_normSq.comp f.1.continuous)
  · change HasCompactSupport
      ((fun z : ℂ => (Complex.normSq z : ℂ)) ∘ f.1)
    exact f.2.comp_left (g := fun z : ℂ => (Complex.normSq z : ℂ)) (by simp)

def fieldOneFiniteStageFiniteBruhatPair
    (S : Finset (HeightOneSpectrum ℤ))
    (f g : FieldOneFiniteStageFiniteBruhatSchwartz S) : ℂ :=
  ∫ x, star (f.1 x) * g.1 x
    ∂(Measure.pi fun v : ↑S => fieldOneLocalSelfDualAddHaar v.1)

theorem fieldOneFiniteStageFiniteBruhatPair_eq_polarization
    (S : Finset (HeightOneSpectrum ℤ))
    (f g : FieldOneFiniteStageFiniteBruhatSchwartz S) :
    fieldOneFiniteStageFiniteBruhatPair S f g =
      ((∫ x, (Complex.normSq ((f + g).1 x) : ℂ)
          ∂(Measure.pi fun v : ↑S => fieldOneLocalSelfDualAddHaar v.1)) -
        (∫ x, (Complex.normSq ((f - g).1 x) : ℂ)
          ∂(Measure.pi fun v : ↑S => fieldOneLocalSelfDualAddHaar v.1)) -
        Complex.I *
          (∫ x, (Complex.normSq ((f + Complex.I • g).1 x) : ℂ)
            ∂(Measure.pi fun v : ↑S => fieldOneLocalSelfDualAddHaar v.1)) +
        Complex.I *
          (∫ x, (Complex.normSq ((f - Complex.I • g).1 x) : ℂ)
            ∂(Measure.pi fun v : ↑S => fieldOneLocalSelfDualAddHaar v.1))) / 4 := by
  let μ := Measure.pi fun v : ↑S => fieldOneLocalSelfDualAddHaar v.1
  let A : FieldOneFiniteStageFinitePart S → ℂ := fun x =>
    (Complex.normSq ((f + g).1 x) : ℂ)
  let B : FieldOneFiniteStageFinitePart S → ℂ := fun x =>
    (Complex.normSq ((f - g).1 x) : ℂ)
  let C : FieldOneFiniteStageFinitePart S → ℂ := fun x =>
    (Complex.normSq ((f + Complex.I • g).1 x) : ℂ)
  let D : FieldOneFiniteStageFinitePart S → ℂ := fun x =>
    (Complex.normSq ((f - Complex.I • g).1 x) : ℂ)
  have hA : Integrable A μ :=
    fieldOneFiniteStageFiniteBruhat_normSq_integrable S (f + g)
  have hB : Integrable B μ :=
    fieldOneFiniteStageFiniteBruhat_normSq_integrable S (f - g)
  have hC : Integrable C μ :=
    fieldOneFiniteStageFiniteBruhat_normSq_integrable S (f + Complex.I • g)
  have hD : Integrable D μ :=
    fieldOneFiniteStageFiniteBruhat_normSq_integrable S (f - Complex.I • g)
  change (∫ x, star (f.1 x) * g.1 x ∂μ) = _
  rw [show (fun x => star (f.1 x) * g.1 x) =
      fun x => (A x - B x - Complex.I * C x + Complex.I * D x) / 4 by
    funext x
    change star (f.1 x) * g.1 x =
      ((Complex.normSq (f.1 x + g.1 x) : ℂ) -
          (Complex.normSq (f.1 x - g.1 x) : ℂ) -
        Complex.I * (Complex.normSq (f.1 x + Complex.I * g.1 x) : ℂ) +
        Complex.I * (Complex.normSq (f.1 x - Complex.I * g.1 x) : ℂ)) / 4
    exact fieldOneComplex_star_mul_polarization (f.1 x) (g.1 x)]
  rw [integral_div]
  rw [integral_add]
  · rw [integral_sub]
    · rw [integral_sub]
      · rw [integral_const_mul, integral_const_mul]
      · exact hA
      · exact hB
    · exact hA.sub hB
    · exact hC.const_mul Complex.I
  · exact (hA.sub hB).sub (hC.const_mul Complex.I)
  · exact hD.const_mul Complex.I

theorem fieldOneFiniteStageFiniteBruhatFourier_plancherel_complex
    (S : Finset (HeightOneSpectrum ℤ))
    (f : FieldOneFiniteStageFiniteBruhatSchwartz S) :
    ∫ y, (Complex.normSq (fieldOneFiniteStageFiniteBruhatFourier S f y) : ℂ)
        ∂(Measure.pi fun v : ↑S => fieldOneLocalSelfDualAddHaar v.1) =
      ∫ x, (Complex.normSq (f.1 x) : ℂ)
        ∂(Measure.pi fun v : ↑S => fieldOneLocalSelfDualAddHaar v.1) := by
  rw [integral_complex_ofReal, integral_complex_ofReal,
    fieldOneFiniteStageFiniteBruhatFourier_plancherel]

theorem fieldOneFiniteStageFiniteBruhatFourier_parseval
    (S : Finset (HeightOneSpectrum ℤ))
    (f g : FieldOneFiniteStageFiniteBruhatSchwartz S) :
    fieldOneFiniteStageFiniteBruhatPair S
        (fieldOneFiniteStageFiniteBruhatFourierBruhat S f)
        (fieldOneFiniteStageFiniteBruhatFourierBruhat S g) =
      fieldOneFiniteStageFiniteBruhatPair S f g := by
  let L := fieldOneFiniteStageFiniteBruhatFourierLinear S
  rw [fieldOneFiniteStageFiniteBruhatPair_eq_polarization]
  change
    ((∫ x, (Complex.normSq (((L f) + (L g)).1 x) : ℂ)
          ∂(Measure.pi fun v : ↑S => fieldOneLocalSelfDualAddHaar v.1)) -
        (∫ x, (Complex.normSq (((L f) - (L g)).1 x) : ℂ)
          ∂(Measure.pi fun v : ↑S => fieldOneLocalSelfDualAddHaar v.1)) -
        Complex.I *
          (∫ x, (Complex.normSq (((L f) + Complex.I • (L g)).1 x) : ℂ)
            ∂(Measure.pi fun v : ↑S => fieldOneLocalSelfDualAddHaar v.1)) +
        Complex.I *
          (∫ x, (Complex.normSq (((L f) - Complex.I • (L g)).1 x) : ℂ)
            ∂(Measure.pi fun v : ↑S => fieldOneLocalSelfDualAddHaar v.1))) / 4 = _
  rw [← map_add, ← map_sub]
  rw [show L f + Complex.I • L g = L (f + Complex.I • g) by
    rw [map_add, map_smul]]
  rw [show L f - Complex.I • L g = L (f - Complex.I • g) by
    rw [map_sub, map_smul]]
  have hL : ∀ (h : FieldOneFiniteStageFiniteBruhatSchwartz S)
      (x : FieldOneFiniteStageFinitePart S),
      (L h).1 x = fieldOneFiniteStageFiniteBruhatFourier S h x := by
    intro h x
    exact fieldOneFiniteStageFiniteBruhatFourierBruhat_apply S h x
  simp_rw [hL]
  rw [fieldOneFiniteStageFiniteBruhatFourier_plancherel_complex S (f + g)]
  rw [fieldOneFiniteStageFiniteBruhatFourier_plancherel_complex S (f - g)]
  rw [fieldOneFiniteStageFiniteBruhatFourier_plancherel_complex S (f + Complex.I • g)]
  rw [fieldOneFiniteStageFiniteBruhatFourier_plancherel_complex S (f - Complex.I • g)]
  exact (fieldOneFiniteStageFiniteBruhatPair_eq_polarization S f g).symm

end
end GaloisForLFunctions.RHTower
