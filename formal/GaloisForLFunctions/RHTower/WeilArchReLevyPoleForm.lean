import GaloisForLFunctions.RHTower.WeilFullConeOneSidedCriterion
import GaloisForLFunctions.RHTower.GammaHardyPhaseRateLevyKhintchine
import GaloisForLFunctions.RHTower.LebesgueAtomWeilPositivity

/-!
# The pole and archimedean part of the Weil functional in Lévy form

For a real test `f ∈ C²_c(ℝ)` and its autocorrelation `k = f ⋆ f̃`, the pole and archimedean part
of the Weil functional is (`weilArchRe_eq_levy_pole`)

`W_∞(k) = A(0)‖f‖² + ∫_0^∞ ω(x) ‖f − f(· + x)‖² dx + 2 ∫∫ f(u) f(v) cosh((u − v)/2) du dv`,

where `A(r) = Re ψ(¼ + ir/2) − log π` is the archimedean symbol and
`ω(x) = e^{−x/2}/(1 − e^{−2x})` its Lévy density.

* **Pole.** `k̂(±i/2) = (∫ f e^{u/2})(∫ f e^{−u/2})`, and `(∫ f e^{u/2})(∫ f e^{−v/2}) =
  ∫∫ f(u) f(v) cosh((u − v)/2)` after symmetrizing in `(u, v)`.
* **Archimedean part.** On the real line `k̂(r) = |f̂(r)|²` with `f̂(r) = 𝓕f(−r/2π)`, and
  `A = 2θ'` with `θ' = gammaHardyPhaseRate`. So `(1/2π)∫ k̂ A = ∫ 2θ'(2πξ)|𝓕f(ξ)|² dξ`, which is the
  Lévy–Khintchine splitting `integral_archSymbol_mul_normSq_fourier_eq`.
-/

open Complex MeasureTheory Set Filter Topology
open scoped FourierTransform ComplexConjugate
open Zeta23

namespace RHTower.WeilLevyPole

noncomputable section

theorem gammaBracket_eq_two_mul_gammaHardyPhaseRate (r : ℝ) :
    EF.gammaBracket r = 2 * gammaHardyPhaseRate r := by
  rw [gammaHardyPhaseRate, linePt_div_two, EF.gammaBracket]
  have : (1 / 4 + Complex.I * (r : ℂ) / 2) = ((1 / 4 : ℝ) : ℂ) + ((r / 2 : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this]
  ring

variable {f : ℝ → ℝ}

theorem paperFT_ofReal_I_div_two (f : ℝ → ℝ) :
    paperFT (fun u => (f u : ℂ)) (Complex.I / 2) = ((∫ u, f u * Real.exp (-u / 2) : ℝ) : ℂ) := by
  rw [← integral_complex_ofReal]
  show ∫ u : ℝ, (f u : ℂ) * Complex.exp (Complex.I * (Complex.I / 2) * u) = _
  congr 1
  funext u
  rw [show Complex.I * (Complex.I / 2) * (u : ℂ) = ((-u / 2 : ℝ) : ℂ) by
    push_cast; ring_nf; rw [Complex.I_sq]; ring, ← Complex.ofReal_exp]
  push_cast
  ring

theorem paperFT_ofReal_neg_I_div_two (f : ℝ → ℝ) :
    paperFT (fun u => (f u : ℂ)) (-Complex.I / 2) = ((∫ u, f u * Real.exp (u / 2) : ℝ) : ℂ) := by
  rw [← integral_complex_ofReal]
  show ∫ u : ℝ, (f u : ℂ) * Complex.exp (Complex.I * (-Complex.I / 2) * u) = _
  congr 1
  funext u
  rw [show Complex.I * (-Complex.I / 2) * (u : ℂ) = ((u / 2 : ℝ) : ℂ) by
    push_cast; ring_nf; rw [Complex.I_sq]; ring, ← Complex.ofReal_exp]
  push_cast
  ring

/-- `(∫ f e^{u/2})(∫ f e^{−u/2}) = ∫∫ f(u) f(v) cosh((u − v)/2)`. -/
theorem integral_prod_cosh_eq (hfc : HasCompactSupport f) (hf : Continuous f) :
    ∫ p : ℝ × ℝ, f p.1 * f p.2 * Real.cosh ((p.1 - p.2) / 2) =
      (∫ u, f u * Real.exp (u / 2)) * ∫ u, f u * Real.exp (-u / 2) := by
  have hp : Integrable fun u => f u * Real.exp (u / 2) :=
    (hf.mul (by fun_prop)).integrable_of_hasCompactSupport (hfc.mul_right)
  have hm : Integrable fun u => f u * Real.exp (-u / 2) :=
    (hf.mul (by fun_prop)).integrable_of_hasCompactSupport (hfc.mul_right)
  have h1 := integral_prod_mul (μ := volume) (ν := volume) (fun u => f u * Real.exp (u / 2))
    (fun v => f v * Real.exp (-v / 2))
  have h2 := integral_prod_mul (μ := volume) (ν := volume) (fun u => f u * Real.exp (-u / 2))
    (fun v => f v * Real.exp (v / 2))
  have hcosh : ∀ p : ℝ × ℝ, f p.1 * f p.2 * Real.cosh ((p.1 - p.2) / 2) =
      ((f p.1 * Real.exp (p.1 / 2)) * (f p.2 * Real.exp (-p.2 / 2)) +
        (f p.1 * Real.exp (-p.1 / 2)) * (f p.2 * Real.exp (p.2 / 2))) / 2 := fun p => by
    rw [Real.cosh_eq, show -((p.1 - p.2) / 2) = -p.1 / 2 + p.2 / 2 by ring,
      show (p.1 - p.2) / 2 = p.1 / 2 + -p.2 / 2 by ring, Real.exp_add, Real.exp_add]
    ring
  simp_rw [hcosh]
  rw [Measure.volume_eq_prod, integral_div, integral_add (hp.mul_prod hm) (hm.mul_prod hp), h1, h2]
  ring

/-- `(1/2π) ∫ |f̂(r)|² A(r) dr = ∫ 2θ'(2πξ) |𝓕f(ξ)|² dξ`, by the substitution `r = −2πξ`. -/
theorem integral_paperFT_sq_mul_gammaBracket (g : ℝ → ℂ) :
    1 / (2 * Real.pi) * ∫ r : ℝ, ‖paperFT g r‖ ^ 2 * EF.gammaBracket r =
      ∫ ξ : ℝ, 2 * gammaHardyPhaseRate (2 * Real.pi * ξ) * ‖𝓕 g ξ‖ ^ 2 := by
  have h := Measure.integral_comp_mul_left
    (fun r : ℝ => ‖paperFT g r‖ ^ 2 * EF.gammaBracket r) (-(2 * Real.pi))
  rw [abs_inv, abs_neg, abs_of_pos (by positivity), smul_eq_mul] at h
  rw [one_div, ← h]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only
  rw [fourier_eq_paperFT_neg_two_pi_mul, gammaBracket_eq_two_mul_gammaHardyPhaseRate,
    show -(2 * Real.pi) * ξ = -(2 * Real.pi * ξ) by ring, gammaHardyPhaseRate_neg]
  push_cast
  ring

/-- **The pole and archimedean part of the Weil functional in Lévy form.** -/
theorem weilArchRe_eq_levy_pole (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) =
      EF.gammaBracket 0 * (∫ u, f u ^ 2) +
        (∫⁻ x in Ioi 0, ENNReal.ofReal (archLevyDensity x * ∫ u, (f u - f (u + x)) ^ 2)).toReal +
        2 * ∫ p : ℝ × ℝ, f p.1 * f p.2 * Real.cosh ((p.1 - p.2) / 2) := by
  set F : ℝ → ℂ := fun u => (f u : ℂ) with hFdef
  have hFc : Continuous F := Complex.continuous_ofReal.comp hf.continuous
  have hFcs : HasCompactSupport F := hfc.comp_left Complex.ofReal_zero
  have hF2 : ContDiff ℝ 2 F := Complex.ofRealCLM.contDiff.comp hf
  have hF1 : Integrable F := hFc.integrable_of_hasCompactSupport hFcs
  have hFL2 : MemLp F 2 := hFc.memLp_of_hasCompactSupport hFcs
  -- the transform of the autocorrelation
  have hk : ∀ z : ℂ, paperFT (EF.weilTest F F) z = paperFT F z * conj (paperFT F (conj z)) :=
    EF.paperFT_weilTest hFc hFc hFcs hFcs
  -- the pole
  have hpole : paperFT (EF.weilTest F F) (Complex.I / 2) +
      paperFT (EF.weilTest F F) (-Complex.I / 2) =
      ((2 * ((∫ u, f u * Real.exp (u / 2)) * ∫ u, f u * Real.exp (-u / 2)) : ℝ) : ℂ) := by
    rw [hk, hk, show conj (Complex.I / 2) = -Complex.I / 2 by
        rw [map_div₀, Complex.conj_I, map_ofNat],
      show conj (-Complex.I / 2) = Complex.I / 2 by
        rw [map_div₀, map_neg, Complex.conj_I, neg_neg, map_ofNat],
      paperFT_ofReal_I_div_two f, paperFT_ofReal_neg_I_div_two f,
      Complex.conj_ofReal, Complex.conj_ofReal]
    push_cast
    ring
  -- the archimedean integral
  have hreal : ∀ r : ℝ, paperFT (EF.weilTest F F) r * (EF.gammaBracket r : ℂ) =
      ((‖paperFT F r‖ ^ 2 * EF.gammaBracket r : ℝ) : ℂ) := fun r => by
    rw [hk, Complex.conj_ofReal, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  have harch : ∫ r : ℝ, paperFT (EF.weilTest F F) r * (EF.gammaBracket r : ℂ) =
      ((∫ r : ℝ, ‖paperFT F r‖ ^ 2 * EF.gammaBracket r : ℝ) : ℂ) := by
    simp_rw [hreal]
    exact integral_complex_ofReal
  -- integrability of the symbol against the spectral density
  have hintC := LebesgueAtomWeil.integrable_paperFT_weilTest_mul_gammaBracket hF2 hFcs hF2 hFcs
  have hintR : Integrable fun r : ℝ => ‖paperFT F r‖ ^ 2 * EF.gammaBracket r := by
    refine hintC.re.congr (Eventually.of_forall fun r => ?_)
    show (paperFT (EF.weilTest F F) r * (EF.gammaBracket r : ℂ)).re = _
    rw [hreal, Complex.ofReal_re]
  have hint : Integrable fun ξ : ℝ => gammaHardyPhaseRate (2 * Real.pi * ξ) * ‖𝓕 F ξ‖ ^ 2 := by
    have h := (hintR.comp_mul_left' (R := -(2 * Real.pi)) (by
      have := Real.pi_pos; intro h; linarith)).div_const 2
    refine h.congr (Eventually.of_forall fun ξ => ?_)
    simp only
    rw [fourier_eq_paperFT_neg_two_pi_mul, gammaBracket_eq_two_mul_gammaHardyPhaseRate,
      show -(2 * Real.pi) * ξ = -(2 * Real.pi * ξ) by ring, gammaHardyPhaseRate_neg]
    ring
  have hsplit := integral_archSymbol_mul_normSq_fourier_eq hF1 hFL2 hint
  -- assemble
  rw [WeilOneSided.weilArchRe, hpole, harch, show ((1 / (2 * Real.pi) : ℂ)) =
    ((1 / (2 * Real.pi) : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_mul, ← Complex.ofReal_add,
    Complex.ofReal_re, integral_paperFT_sq_mul_gammaBracket, hsplit, integral_prod_cosh_eq hfc
    hf.continuous, gammaBracket_eq_two_mul_gammaHardyPhaseRate]
  have hnorm : ∫ u : ℝ, ‖F u‖ ^ 2 = ∫ u : ℝ, f u ^ 2 := by
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp [hFdef, Complex.norm_real, sq_abs]
  have hlev : (∫⁻ x in Ioi (0 : ℝ),
      ENNReal.ofReal (archLevyDensity x * ∫ u : ℝ, ‖F u - F (u + x)‖ ^ 2)) =
      ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (archLevyDensity x * ∫ u : ℝ, (f u - f (u + x)) ^ 2) := by
    refine lintegral_congr fun x => ?_
    congr 3
    funext u
    simp only [hFdef]
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [hnorm, hlev]
  ring

end

end RHTower.WeilLevyPole
