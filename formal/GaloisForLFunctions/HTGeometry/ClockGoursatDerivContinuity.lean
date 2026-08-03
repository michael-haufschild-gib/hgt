import GaloisForLFunctions.HTGeometry.ClockParametricDerivative

/-!
# Joint continuity of the first derivatives of the Goursat solution

The regularity bootstrap differentiates the identities

`∂ξ u(ξ,η) = ∫_b^η K(ξ,t) u(ξ,t) dt`,  `∂η u(ξ,η) = ∫_{ξ₀}^{ξ} K(τ,η) u(τ,η) dτ`

once more. The Leibniz rule of the previous file asks for the integrand and its parameter derivative
to be jointly continuous, and the parameter derivative of the first identity involves `∂ξ u` itself.

So both first derivatives of the solution must be known to be jointly continuous before the
bootstrap can start. Both are parametric interval integrals of a jointly continuous integrand, with
a continuous limit of integration, so both are.
-/

namespace GaloisForLFunctions.HTGeometry

open Set MeasureTheory

/-- **The `ξ`-derivative of the Goursat solution is jointly continuous.** -/
theorem continuous_goursatXiDeriv {K u : ℝ → ℝ → ℝ}
    (hK : Continuous fun p : ℝ × ℝ => K p.1 p.2)
    (hu : Continuous fun p : ℝ × ℝ => u p.1 p.2) (b b' c c' : ℝ) :
    Continuous fun p : ℝ × ℝ => volterraFun (K (clampTo c c' p.1)) b b' (u p.1) p.2 := by
  have hker : Continuous fun q : (ℝ × ℝ) × ℝ => K (clampTo c c' q.1.1) q.2 :=
    hK.comp (((continuous_clampTo c c').comp (continuous_fst.comp continuous_fst)).prodMk
      continuous_snd)
  have hval : Continuous fun q : (ℝ × ℝ) × ℝ => u q.1.1 q.2 :=
    hu.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)
  have huncurry : Continuous
      (Function.uncurry fun p : ℝ × ℝ => fun t => K (clampTo c c' p.1) t * u p.1 t) :=
    hker.mul hval
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous huncurry
    ((continuous_clampTo b b').comp continuous_snd)

/-- **The `η`-derivative of the Goursat solution is jointly continuous.** -/
theorem continuous_goursatEtaDeriv {K u : ℝ → ℝ → ℝ}
    (hK : Continuous fun p : ℝ × ℝ => K p.1 p.2)
    (hu : Continuous fun p : ℝ × ℝ => u p.1 p.2) (c c' ξ₀ : ℝ) :
    Continuous fun p : ℝ × ℝ => ∫ τ in ξ₀..p.1, K (clampTo c c' τ) p.2 * u τ p.2 := by
  have hker : Continuous fun q : (ℝ × ℝ) × ℝ => K (clampTo c c' q.2) q.1.2 :=
    hK.comp (((continuous_clampTo c c').comp continuous_snd).prodMk
      (continuous_snd.comp continuous_fst))
  have hval : Continuous fun q : (ℝ × ℝ) × ℝ => u q.2 q.1.2 :=
    hu.comp (continuous_snd.prodMk (continuous_snd.comp continuous_fst))
  have huncurry : Continuous
      (Function.uncurry fun p : ℝ × ℝ => fun τ => K (clampTo c c' τ) p.2 * u τ p.2) :=
    hker.mul hval
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous huncurry
    continuous_fst

end GaloisForLFunctions.HTGeometry
