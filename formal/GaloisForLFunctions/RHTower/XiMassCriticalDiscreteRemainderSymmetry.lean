import GaloisForLFunctions.RHTower.XiMassCriticalDiscreteRemainder

/-!
# Conjugation reduction for the discrete critical Xi mass current

On the real source axis the analytic mass root is real, while the mass test is even in the source
frequency.  These two facts make reflection of the vertical parameter `u` exact complex
conjugation for the strip Fourier kernel, its true frequency derivative, the outgoing derivative,
and finally the infinite discrete Selberg-remainder current.

Thus the exact mass-shifted spectral-face open core needs control on only one vertical half-line.
No pointwise remainder estimate, cancellation hypothesis, or Riemann-hypothesis input is used.
-/

open Complex Filter MeasureTheory Set Topology
open scoped ComplexConjugate

namespace RHTower

noncomputable section

/-- Conjugating vertical time reflects its sign in the real-axis mass test. -/
theorem conj_xiMassAnalyticTest_ofReal {a sigma u x : ℝ} (ha : 0 < a) :
    conj (xiMassAnalyticTest a ((sigma : ℂ) + (u : ℂ) * I) (x : ℂ)) =
      xiMassAnalyticTest a ((sigma : ℂ) + ((-u : ℝ) : ℂ) * I) (x : ℂ) := by
  rw [xiMassAnalyticTest, xiMassAnalyticTest, ← Complex.exp_conj,
    map_mul, map_neg, xiMassAnalyticSqrt_ofReal_eq ha]
  push_cast
  simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  ring

/-- The actual strip Fourier integral at reflected vertical time is the complex conjugate. -/
theorem conj_stripFourier_xiMassAnalyticTest
    {a sigma : ℝ} (ha : 0 < a) (u h : ℝ) :
    conj (stripFourier
      (xiMassAnalyticTest a ((sigma : ℂ) + (u : ℂ) * I)) (h : ℂ)) =
      stripFourier
        (xiMassAnalyticTest a ((sigma : ℂ) + ((-u : ℝ) : ℂ) * I)) (h : ℂ) := by
  rw [stripFourier, ← integral_conj, stripFourier]
  have href := MeasureTheory.integral_neg_eq_self
    (fun x : ℝ =>
      xiMassAnalyticTest a ((sigma : ℂ) + ((-u : ℝ) : ℂ) * I) x *
        Complex.exp (-(I * (h : ℂ) * x))) volume
  calc
    (∫ x : ℝ, conj
        (xiMassAnalyticTest a ((sigma : ℂ) + (u : ℂ) * I) x *
          Complex.exp (-(I * (h : ℂ) * x)))) =
        ∫ x : ℝ,
          xiMassAnalyticTest a ((sigma : ℂ) + ((-u : ℝ) : ℂ) * I) (-x) *
            Complex.exp (-(I * (h : ℂ) * (-x))) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      rw [map_mul, conj_xiMassAnalyticTest_ofReal ha, ← Complex.exp_conj]
      push_cast
      rw [map_neg, map_mul, map_mul, Complex.conj_I, Complex.conj_ofReal,
        Complex.conj_ofReal, xiMassAnalyticTest_neg]
      ring_nf
    _ = _ := by simpa only [Complex.ofReal_neg] using href

/-- Conjugation-reflection law for the actual differentiated Fourier integral. -/
theorem conj_xiMassFourierDerivative
    {a sigma : ℝ} (ha : 0 < a) (u h : ℝ) :
    conj (xiMassFourierDerivative a sigma u h) =
      xiMassFourierDerivative a sigma (-u) h := by
  rw [xiMassFourierDerivative, ← integral_conj, xiMassFourierDerivative]
  have href := MeasureTheory.integral_neg_eq_self
    (fun x : ℝ =>
      xiMassAnalyticTest a ((sigma : ℂ) + ((-u : ℝ) : ℂ) * I) x *
        (Complex.exp (-(I * (h : ℂ) * x)) * (-(I * x)))) volume
  calc
    (∫ x : ℝ, conj
        (xiMassAnalyticTest a ((sigma : ℂ) + (u : ℂ) * I) x *
          (Complex.exp (-(I * (h : ℂ) * x)) * (-(I * x))))) =
        ∫ x : ℝ,
          xiMassAnalyticTest a ((sigma : ℂ) + ((-u : ℝ) : ℂ) * I) (-x) *
            (Complex.exp (-(I * (h : ℂ) * (-x))) * (-(I * (-x)))) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      rw [map_mul, map_mul, conj_xiMassAnalyticTest_ofReal ha, ← Complex.exp_conj]
      push_cast
      rw [map_neg, map_mul, map_mul, Complex.conj_I, Complex.conj_ofReal,
        Complex.conj_ofReal, map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal,
        xiMassAnalyticTest_neg]
      ring_nf
    _ = _ := by simpa only [Complex.ofReal_neg] using href

/-- The outgoing Volterra-adjoint derivative inherits the same reflection law. -/
theorem conj_xiMassCriticalOutgoingDerivative
    {a sigma : ℝ} (ha : 0 < a) (u h : ℝ) :
    conj (xiMassCriticalOutgoingDerivative a sigma u h) =
      xiMassCriticalOutgoingDerivative a sigma (-u) h := by
  rw [xiMassCriticalOutgoingDerivative, xiMassCriticalOutgoingDerivative,
    map_sub, map_mul, conj_stripFourier_xiMassAnalyticTest ha,
    conj_xiMassFourierDerivative ha]
  simp only [map_div₀, map_one, map_ofNat]

/-- The real discrete Selberg-remainder coefficient preserves outgoing conjugation. -/
theorem conj_xiMassCriticalDiscreteRemainderDensity
    {a sigma : ℝ} (ha : 0 < a) (u h : ℝ) :
    conj (xiMassCriticalDiscreteRemainderDensity a sigma u h) =
      xiMassCriticalDiscreteRemainderDensity a sigma (-u) h := by
  rw [xiMassCriticalDiscreteRemainderDensity,
    xiMassCriticalDiscreteRemainderDensity, map_mul,
    Complex.conj_ofReal, conj_xiMassCriticalOutgoingDerivative ha]

/-- Exact conjugation-reflection law for the infinite discrete critical current. -/
theorem conj_xiMassCriticalDiscreteRemainderFlux
    {a sigma : ℝ} (ha : 0 < a) (u : ℝ) :
    conj (xiMassCriticalDiscreteRemainderFlux a sigma u) =
      xiMassCriticalDiscreteRemainderFlux a sigma (-u) := by
  rw [xiMassCriticalDiscreteRemainderFlux, ← integral_conj,
    xiMassCriticalDiscreteRemainderFlux]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with h
  exact conj_xiMassCriticalDiscreteRemainderDensity ha u h

theorem norm_xiMassCriticalDiscreteRemainderFlux_neg
    {a sigma : ℝ} (ha : 0 < a) (u : ℝ) :
    ‖xiMassCriticalDiscreteRemainderFlux a sigma (-u)‖ =
      ‖xiMassCriticalDiscreteRemainderFlux a sigma u‖ := by
  rw [← conj_xiMassCriticalDiscreteRemainderFlux ha u, norm_conj]

/-- Uniform bound restricted to the nonnegative vertical half-line. -/
def XiMassCriticalDiscreteRemainderFluxNonnegativeLineBound (a sigma : ℝ) : Prop :=
  ∃ C : ℝ, ∀ u : ℝ, 0 ≤ u →
    ‖xiMassCriticalDiscreteRemainderFlux a sigma u‖ ≤ C

/-- Negative vertical heights are exactly redundant, rather than estimated separately. -/
theorem xiMassCriticalDiscreteRemainderFluxLineBound_iff_nonnegative
    {a sigma : ℝ} (ha : 0 < a) :
    XiMassCriticalDiscreteRemainderFluxLineBound a sigma ↔
      XiMassCriticalDiscreteRemainderFluxNonnegativeLineBound a sigma := by
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨C, fun u _hu => hC u⟩
  · rintro ⟨C, hC⟩
    refine ⟨C, fun u => ?_⟩
    by_cases hu : 0 ≤ u
    · exact hC u hu
    · have hnegu : 0 ≤ -u := neg_nonneg.mpr (le_of_not_ge hu)
      rw [← norm_xiMassCriticalDiscreteRemainderFlux_neg ha u]
      exact hC (-u) hnegu

/-- **One-cone exact open core.**  RH is equivalent to uniform control of the raw discrete
Selberg-remainder current for nonnegative vertical height alone. -/
theorem riemannHypothesis_iff_xiMassCriticalDiscreteRemainderFluxNonnegativeLineBound
    {a c sigma : ℝ} (hhalf : 1 / 2 < c) (hca : c < a) (hsigma : 0 < sigma) :
    RiemannHypothesis ↔
      XiMassCriticalDiscreteRemainderFluxNonnegativeLineBound a sigma := by
  have ha : 0 < a := lt_trans (lt_trans (by norm_num) hhalf) hca
  exact (riemannHypothesis_iff_xiMassCriticalDiscreteRemainderFluxLineBound
    hhalf hca hsigma).trans
      (xiMassCriticalDiscreteRemainderFluxLineBound_iff_nonnegative ha)

end


end RHTower
