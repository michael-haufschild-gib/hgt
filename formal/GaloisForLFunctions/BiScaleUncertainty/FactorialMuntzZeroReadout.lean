import GaloisForLFunctions.BiScaleUncertainty.FactorialMuntzWeilSmoothing
import GaloisForLFunctions.BiScaleUncertainty.FactorialMuntzAnalyticRepair
import Zeta23.Tail

/-! Exact zero-side summands and a smoothing-independent strip bound for the
literal corrected factorial Müntz source. No critical-line premise enters. -/

open MeasureTheory Complex Filter Set
open scoped Topology ComplexConjugate
namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open _root_.Zeta23 _root_.RHTower _root_.RHTower.WeilSpectral
open _root_.RHTower.CHMDDoobGraph
noncomputable section
set_option autoImplicit false

def factorialMuntzKernelReadout (k : ℕ) (s : ℂ) : ℂ :=
  ∫ x : ℝ, Complex.exp ((s-1/2)*(x : ℂ))*(CHMDDoobGraph.mollifier k x : ℂ)

private theorem mollifier_support_abs_le_one (k : ℕ) {x : ℝ}
    (hx : CHMDDoobGraph.mollifier k x ≠ 0) : |x| ≤ 1 := by
  have hm : x ∈ Function.support ((WeilOneSided.narrowBump k).normed volume) := hx
  rw [(WeilOneSided.narrowBump k).support_normed_eq] at hm
  have hr : (WeilOneSided.narrowBump k).rOut ≤ 1 := by
    change 1/(4*((k : ℝ)+1)) ≤ 1
    apply (div_le_iff₀ (by positivity)).2
    nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hxout : |x| < (WeilOneSided.narrowBump k).rOut := by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hm
  exact hxout.le.trans hr

/-- The kernel bound is independent of the ordinate and the smoothing index. -/
theorem factorialMuntzKernelReadout_bound (k : ℕ) {s : ℂ}
    (hs0 : 0 ≤ s.re) (hs1 : s.re ≤ 1) :
    ‖factorialMuntzKernelReadout k s‖ ≤ Real.exp 1 := by
  have hb : ∀ᵐ x : ℝ, ‖Complex.exp ((s-1/2)*(x : ℂ))*
      (CHMDDoobGraph.mollifier k x : ℂ)‖ ≤
      Real.exp 1*CHMDDoobGraph.mollifier k x := by
    filter_upwards [] with x
    by_cases hx : CHMDDoobGraph.mollifier k x = 0
    · simp only [hx, Complex.ofReal_zero, mul_zero, norm_zero, le_refl]
    have hx1 := mollifier_support_abs_le_one k hx
    have ha : |s.re-1/2| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    have he : ((s-1/2)*(x : ℂ)).re ≤ 1 := by
      have hp := mul_le_mul ha hx1 (abs_nonneg x) (by norm_num : (0 : ℝ) ≤ 1)
      have hab := le_abs_self ((s.re-1/2)*x)
      simp only [one_mul] at hp
      rw [abs_mul] at hab
      have hre : ((s-1/2)*(x : ℂ)).re = (s.re-1/2)*x := by
        norm_num [Complex.mul_re, Complex.sub_re]
      rw [hre]
      exact hab.trans hp
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (mollifier_nonneg k x), Complex.norm_exp]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr he) (mollifier_nonneg k x)
  have h := norm_integral_le_of_norm_le ((mollifier_integrable k).const_mul (Real.exp 1)) hb
  simpa only [factorialMuntzKernelReadout, integral_const_mul, mollifier_integral, mul_one] using h

private theorem paperFT_gamma_readout (f : ℝ → ℝ) (s : ℂ) :
    paperFT (fun x => (f x : ℂ)) (gammaOf s) =
      ∫ x : ℝ, Complex.exp ((s-1/2)*(x : ℂ))*(f x : ℂ) := by
  simp only [paperFT, gammaOf, mul_div_cancel₀ _ Complex.I_ne_zero, mul_comm]

theorem factorialMuntzBoundaryCorrected_paperFT_gamma (n : ℕ)
    (ρ : zetaZeroConfig.carrier) :
    paperFT (fun x => (factorialMuntzBoundaryCorrected n
      (factorialMuntzBoundaryCoefficient n) x : ℂ)) (gammaOf ρ) =
        (factorialMuntzBoundaryCoefficient n : ℂ)/(ρ : ℂ) := by
  have hz : IsNontrivialZero (ρ : ℂ) := ρ.2
  rw [paperFT_gamma_readout, factorialMuntzBoundaryCorrected_zeta_readout n _ hz.2.1 hz.1]

theorem factorialMuntzSmoothed_paperFT_gamma (n k : ℕ) (ρ : zetaZeroConfig.carrier) :
    paperFT (fun x => (factorialMuntzSmoothed n k x : ℂ)) (gammaOf ρ) =
      factorialMuntzKernelReadout k ρ*((factorialMuntzBoundaryCoefficient n : ℂ)/(ρ : ℂ)) := by
  have hz : IsNontrivialZero (ρ : ℂ) := ρ.2
  rw [paperFT_gamma_readout, factorialMuntzSmoothed_zeta_readout n k hz.2.1 hz.1]
  rfl

/-- The canonical boundary repair produces a positive-real-part reciprocal
summand at every actual nontrivial zero, including off-line zeros. -/
theorem factorialMuntzBoundaryCorrected_Wsummand_eq (n : ℕ) (ρ : zetaZeroConfig.carrier) :
    zetaZeroConfig.Wsummand
      (fun x => (factorialMuntzBoundaryCorrected n (factorialMuntzBoundaryCoefficient n) x : ℂ))
      (fun x => (factorialMuntzBoundaryCorrected n (factorialMuntzBoundaryCoefficient n) x : ℂ)) ρ =
      (zetaZeroConfig.mult ρ : ℂ)*(factorialMuntzBoundaryCoefficient n : ℂ)^2/
        ((ρ : ℂ)*(1-(ρ : ℂ))) := by
  let σ : zetaZeroConfig.carrier := ⟨reflect ρ, zetaZeroConfig.reflect_mem _ ρ.2⟩
  have hγ : gammaOf (σ : ℂ) = conj (gammaOf (ρ : ℂ)) := Tail.gammaOf_reflect _
  rw [ZeroConfig.Wsummand, factorialMuntzBoundaryCorrected_paperFT_gamma n ρ, ← hγ,
    factorialMuntzBoundaryCorrected_paperFT_gamma n σ]
  simp only [σ, reflect, map_div₀, map_sub, map_one, Complex.conj_conj, Complex.conj_ofReal]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Exact kernel multiplication holds for this noncompact, nonsmooth source. -/
theorem factorialMuntzSmoothed_Wsummand_factor (n k : ℕ) (ρ : zetaZeroConfig.carrier) :
    zetaZeroConfig.Wsummand (fun x => (factorialMuntzSmoothed n k x : ℂ))
      (fun x => (factorialMuntzSmoothed n k x : ℂ)) ρ =
      (factorialMuntzKernelReadout k ρ*conj (factorialMuntzKernelReadout k (reflect ρ)))*
        zetaZeroConfig.Wsummand
          (fun x => (factorialMuntzBoundaryCorrected n (factorialMuntzBoundaryCoefficient n) x : ℂ))
          (fun x => (factorialMuntzBoundaryCorrected n (factorialMuntzBoundaryCoefficient n) x : ℂ)) ρ := by
  let σ : zetaZeroConfig.carrier := ⟨reflect ρ, zetaZeroConfig.reflect_mem _ ρ.2⟩
  have hγ : gammaOf (σ : ℂ) = conj (gammaOf (ρ : ℂ)) := Tail.gammaOf_reflect _
  simp only [ZeroConfig.Wsummand, ← hγ, factorialMuntzSmoothed_paperFT_gamma,
    factorialMuntzBoundaryCorrected_paperFT_gamma, map_mul]
  change _ = (factorialMuntzKernelReadout k ρ*conj (factorialMuntzKernelReadout k σ))*_
  ring

theorem factorialMuntzSmoothed_Wsummand_tendsto (n : ℕ) (ρ : zetaZeroConfig.carrier) :
    Tendsto (fun k : ℕ => zetaZeroConfig.Wsummand
      (fun x => (factorialMuntzSmoothed n k x : ℂ))
      (fun x => (factorialMuntzSmoothed n k x : ℂ)) ρ) atTop
      (𝓝 (zetaZeroConfig.Wsummand
        (fun x => (factorialMuntzBoundaryCorrected n (factorialMuntzBoundaryCoefficient n) x : ℂ))
        (fun x => (factorialMuntzBoundaryCorrected n (factorialMuntzBoundaryCoefficient n) x : ℂ)) ρ)) := by
  have h1 : Tendsto (fun k => factorialMuntzKernelReadout k ρ) atTop (𝓝 1) :=
    mollifier_readout_tendsto _
  have h2 : Tendsto (fun k => conj (factorialMuntzKernelReadout k (reflect ρ))) atTop (𝓝 1) := by
    simpa only [factorialMuntzKernelReadout, Function.comp_def, map_one] using
      (Complex.continuous_conj.tendsto 1).comp (mollifier_readout_tendsto (reflect ρ))
  have h := (h1.mul h2).mul_const
    (zetaZeroConfig.Wsummand
      (fun x => (factorialMuntzBoundaryCorrected n (factorialMuntzBoundaryCoefficient n) x : ℂ))
      (fun x => (factorialMuntzBoundaryCorrected n (factorialMuntzBoundaryCoefficient n) x : ℂ)) ρ)
  simpa only [one_mul, ← factorialMuntzSmoothed_Wsummand_factor] using h

/-- Actual zero separation converts the reciprocal product into the corpus's
summable genus-one majorant. -/
theorem factorialMuntzBoundaryCorrected_Wsummand_norm_bound (n : ℕ)
    (ρ : zetaZeroConfig.carrier) :
    ‖zetaZeroConfig.Wsummand
      (fun x => (factorialMuntzBoundaryCorrected n (factorialMuntzBoundaryCoefficient n) x : ℂ))
      (fun x => (factorialMuntzBoundaryCorrected n (factorialMuntzBoundaryCoefficient n) x : ℂ)) ρ‖ ≤
      (2*(factorialMuntzBoundaryCoefficient n)^2)*
        ((zetaZeroConfig.mult ρ : ℝ)/(1+Complex.normSq (gammaOf ρ))) := by
  have hz : IsNontrivialZero (ρ : ℂ) := ρ.2
  have h4 := _root_.RHTower.four_le_abs_im_of_zeta_zero hz.2.1 hz.2.2 hz.1
  have ha : |(ρ : ℂ).im| ≤ ‖(ρ : ℂ)‖ := Complex.abs_im_le_norm _
  have hb : |(ρ : ℂ).im| ≤ ‖1-(ρ : ℂ)‖ := by
    simpa only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg] using
      Complex.abs_im_le_norm (1-(ρ : ℂ))
  have hIm := WeilEF.abs_gammaOf_im_lt ⟨hz.2.1, hz.2.2⟩
  have hg : Complex.normSq (gammaOf (ρ : ℂ)) ≤ (ρ : ℂ).im^2+1/4 := by
    rw [Complex.normSq_apply, WeilEF.gammaOf_re]
    nlinarith [sq_abs (gammaOf (ρ : ℂ)).im, abs_nonneg (gammaOf (ρ : ℂ)).im]
  have hp : (ρ : ℂ).im^2 ≤ ‖(ρ : ℂ)‖*‖1-(ρ : ℂ)‖ := by
    have h := mul_le_mul ha hb (abs_nonneg _) (norm_nonneg _)
    nlinarith [sq_abs (ρ : ℂ).im]
  have hd : 1+Complex.normSq (gammaOf (ρ : ℂ)) ≤ 2*(‖(ρ : ℂ)‖*‖1-(ρ : ℂ)‖) := by
    nlinarith [sq_abs (ρ : ℂ).im]
  have hprod : 0 < ‖(ρ : ℂ)‖*‖1-(ρ : ℂ)‖ := mul_pos (by linarith) (by linarith)
  have hden : 0 < 1+Complex.normSq (gammaOf (ρ : ℂ)) := by
    linarith [Complex.normSq_nonneg (gammaOf (ρ : ℂ))]
  rw [factorialMuntzBoundaryCorrected_Wsummand_eq]
  simp only [norm_div, norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_real,
    Real.norm_eq_abs, sq_abs]
  rw [← mul_div_assoc, div_le_div_iff₀ hprod hden]
  have hm : 0 ≤ (zetaZeroConfig.mult ρ : ℝ)*(factorialMuntzBoundaryCoefficient n)^2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hd hm]

theorem factorialMuntzBoundaryCorrected_Wsummand_re_nonneg (n : ℕ)
    (ρ : zetaZeroConfig.carrier) :
    0 ≤ (zetaZeroConfig.Wsummand
      (fun x => (factorialMuntzBoundaryCorrected n (factorialMuntzBoundaryCoefficient n) x : ℂ))
      (fun x => (factorialMuntzBoundaryCorrected n (factorialMuntzBoundaryCoefficient n) x : ℂ)) ρ).re := by
  have hz : IsNontrivialZero (ρ : ℂ) := ρ.2
  have hd : 0 ≤ ((ρ : ℂ)*(1-(ρ : ℂ))).re := by
    simp only [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.one_re,
      Complex.one_im, zero_sub]
    nlinarith [mul_pos hz.2.1 (sub_pos.mpr hz.2.2), sq_nonneg (ρ : ℂ).im]
  rw [factorialMuntzBoundaryCorrected_Wsummand_eq]
  have hc : (zetaZeroConfig.mult ρ : ℂ)*(factorialMuntzBoundaryCoefficient n : ℂ)^2 =
      (((zetaZeroConfig.mult ρ : ℝ)*(factorialMuntzBoundaryCoefficient n)^2 : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hc, div_eq_mul_inv, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Complex.inv_re]
  exact mul_nonneg (by positivity) (div_nonneg hd (Complex.normSq_nonneg _))

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
