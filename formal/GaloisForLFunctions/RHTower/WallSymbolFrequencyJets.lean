import GaloisForLFunctions.HTGeometry.PolygammaVerticalSharpDecay
import GaloisForLFunctions.HTGeometry.DigammaGammaFactorialBlowUp

/-!
# The Gamma-wall phase symbol and its frequency derivatives

On the shifted line the phase symbol is

`r(x+iσ) = ψ((1−σ)+ix) + ψ((1+σ)−ix) + 2γ`,

so each frequency derivative is a difference of polygamma jets at the two conjugate abscissas,
carried by the chain rule with the constant inner derivatives `±i`.  Past unit height the sharp
vertical polygamma order gives each jet the exact power `|x|^{-(j)}`, with a constant independent of
the abscissa; the two abscissas `1−σ` and `1+σ` are both positive for `0 < σ < 1`, which is the only
place the strip restriction is used.

The resulting bounds are the card's `(4)`: the symbol's `j`-th frequency derivative is
`O(|x|^{-j})`, and hence so is the `j`-th derivative of the phase operator, whose remaining terms
are the constant self-adjoint part and the explicitly differentiable `i/(2z)`.
-/

open Complex

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

/-- The abscissa `1−σ` is off the digamma poles for `σ < 1`. -/
theorem offPoles_lower {σ x : ℝ} (hσ1 : σ < 1) :
    ∀ p : ℕ, (((1 - σ : ℝ) : ℂ) + (x : ℂ) * Complex.I) ≠ -(p : ℂ) := by
  intro p hp
  have hre := congrArg Complex.re hp
  simp at hre
  have hn : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  linarith

/-- The abscissa `1+σ` is off the digamma poles for `σ > 0`. -/
theorem offPoles_upper {σ x : ℝ} (hσ0 : 0 < σ) :
    ∀ p : ℕ, (((1 + σ : ℝ) : ℂ) + (x : ℂ) * Complex.I) ≠ -(p : ℂ) := by
  intro p hp
  have hre := congrArg Complex.re hp
  simp at hre
  have hn : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  linarith

/-- The Gamma-wall phase symbol on the line of height `σ`. -/
def wallSymbol (σ x : ℝ) : ℂ :=
  Complex.digamma (((1 - σ : ℝ) : ℂ) + (x : ℂ) * Complex.I)
    + Complex.digamma (((1 + σ : ℝ) : ℂ) + ((-x : ℝ) : ℂ) * Complex.I)
    + 2 * (Real.eulerMascheroniConstant : ℂ)

/-- The `j`-th frequency jet of the symbol: a difference of polygamma jets at the two abscissas. -/
def wallSymbolJet (σ : ℝ) (j : ℕ) (x : ℝ) : ℂ :=
  Complex.I ^ j * iteratedDeriv j Complex.digamma (((1 - σ : ℝ) : ℂ) + (x : ℂ) * Complex.I)
    + (-Complex.I) ^ j
      * iteratedDeriv j Complex.digamma (((1 + σ : ℝ) : ℂ) + ((-x : ℝ) : ℂ) * Complex.I)

theorem wallSymbolJet_zero (σ x : ℝ) :
    wallSymbolJet σ 0 x + 2 * (Real.eulerMascheroniConstant : ℂ) = wallSymbol σ x := by
  rw [wallSymbolJet, wallSymbol]
  simp

/-- **The jets differentiate into each other.**  Each frequency derivative advances the polygamma
order and multiplies by the constant inner derivative. -/
theorem hasDerivAt_wallSymbolJet {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (j : ℕ) (x : ℝ) :
    HasDerivAt (wallSymbolJet σ j) (wallSymbolJet σ (j + 1) x) x := by
  -- the two inner affine maps
  have hin₁ : HasDerivAt (fun y : ℝ => ((1 - σ : ℝ) : ℂ) + (y : ℂ) * Complex.I)
      Complex.I x := by
    have h1 : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := Complex.ofRealCLM.hasDerivAt
    simpa using (h1.mul_const Complex.I).const_add (((1 - σ : ℝ) : ℂ))
  have hin₂ : HasDerivAt (fun y : ℝ => ((1 + σ : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * Complex.I)
      (-Complex.I) x := by
    have h1 : HasDerivAt (fun y : ℝ => ((-y : ℝ) : ℂ)) (-1) x := by
      have h0 : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := Complex.ofRealCLM.hasDerivAt
      have hneg : HasDerivAt (fun y : ℝ => -(y : ℂ)) (-1) x := h0.neg
      refine hneg.congr_of_eventuallyEq ?_
      filter_upwards with y
      push_cast
      ring
    simpa using (h1.mul_const Complex.I).const_add (((1 + σ : ℝ) : ℂ))
  -- the two outer jets
  have hout₁ : HasDerivAt (iteratedDeriv j Complex.digamma)
      (iteratedDeriv (j + 1) Complex.digamma (((1 - σ : ℝ) : ℂ) + (x : ℂ) * Complex.I))
      (((1 - σ : ℝ) : ℂ) + (x : ℂ) * Complex.I) := by
    have hana := analyticAt_iteratedDeriv_of_analyticAt
      (analyticAt_digamma_of_offPoles (offPoles_lower (x := x) hσ1)) j
    have hd := hana.differentiableAt.hasDerivAt
    refine hd.congr_deriv ?_
    rw [iteratedDeriv_succ]
  have hout₂ : HasDerivAt (iteratedDeriv j Complex.digamma)
      (iteratedDeriv (j + 1) Complex.digamma
        (((1 + σ : ℝ) : ℂ) + ((-x : ℝ) : ℂ) * Complex.I))
      (((1 + σ : ℝ) : ℂ) + ((-x : ℝ) : ℂ) * Complex.I) := by
    have hana := analyticAt_iteratedDeriv_of_analyticAt
      (analyticAt_digamma_of_offPoles (offPoles_upper (x := -x) hσ0)) j
    have hd := hana.differentiableAt.hasDerivAt
    refine hd.congr_deriv ?_
    rw [iteratedDeriv_succ]
  -- compose
  have hc₁ := hout₁.comp x hin₁
  have hc₂ := hout₂.comp x hin₂
  have hsum := ((hc₁.const_mul (Complex.I ^ j)).add (hc₂.const_mul ((-Complex.I) ^ j)))
  refine hsum.congr_deriv ?_ |>.congr_of_eventuallyEq ?_
  · rw [wallSymbolJet]
    ring
  · filter_upwards with y
    simp [wallSymbolJet, Function.comp]

/-! ## The magnitude bound -/

/-- **`(4)`: the jets decay at the exact order.**  Past unit frequency the `j+1`-st jet of the
symbol is `O(|x|^{-(j+1)})`, with a constant depending only on the order. -/
theorem norm_wallSymbolJet_succ_le {σ x : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (hx : 1 ≤ |x|) (m : ℕ) :
    ‖wallSymbolJet σ (m + 1) x‖
      ≤ 2 * ((m + 1).factorial : ℝ) * (1 + Real.pi / 2) / |x| ^ (m + 1) := by
  have hlow : (0 : ℝ) < 1 - σ := by linarith
  have hup : (0 : ℝ) < 1 + σ := by linarith
  have hxne : x ≠ 0 := by
    intro h
    rw [h] at hx
    simp at hx
    linarith
  have hb₁ := norm_iteratedDeriv_succ_digamma_vertical_pow (σ := 1 - σ) (t := x) hlow hx m
  have hb₂ := norm_iteratedDeriv_succ_digamma_vertical_pow (σ := 1 + σ) (t := -x) hup
    (by rwa [abs_neg]) m
  rw [abs_neg] at hb₂
  have hIpow : ‖(Complex.I : ℂ) ^ (m + 1)‖ = 1 := by
    rw [norm_pow, Complex.norm_I, one_pow]
  have hIpow' : ‖(-Complex.I : ℂ) ^ (m + 1)‖ = 1 := by
    rw [norm_pow, norm_neg, Complex.norm_I, one_pow]
  calc ‖wallSymbolJet σ (m + 1) x‖
      ≤ ‖(Complex.I : ℂ) ^ (m + 1)
          * iteratedDeriv (m + 1) Complex.digamma
            (((1 - σ : ℝ) : ℂ) + (x : ℂ) * Complex.I)‖
        + ‖(-Complex.I : ℂ) ^ (m + 1)
          * iteratedDeriv (m + 1) Complex.digamma
            (((1 + σ : ℝ) : ℂ) + ((-x : ℝ) : ℂ) * Complex.I)‖ := norm_add_le _ _
    _ = ‖iteratedDeriv (m + 1) Complex.digamma
            (((1 - σ : ℝ) : ℂ) + (x : ℂ) * Complex.I)‖
        + ‖iteratedDeriv (m + 1) Complex.digamma
            (((1 + σ : ℝ) : ℂ) + ((-x : ℝ) : ℂ) * Complex.I)‖ := by
        rw [norm_mul, norm_mul, hIpow, hIpow', one_mul, one_mul]
    _ ≤ ((m + 1).factorial : ℝ) * (1 + Real.pi / 2) / |x| ^ (m + 1)
        + ((m + 1).factorial : ℝ) * (1 + Real.pi / 2) / |x| ^ (m + 1) := add_le_add hb₁ hb₂
    _ = 2 * ((m + 1).factorial : ℝ) * (1 + Real.pi / 2) / |x| ^ (m + 1) := by ring

end GaloisForLFunctions.RHTower
