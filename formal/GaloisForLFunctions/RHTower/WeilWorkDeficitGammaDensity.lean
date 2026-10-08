import GaloisForLFunctions.RHTower.XiEntireReal
import GaloisForLFunctions.RHTower.ZetaVerticalSqrtBound
import GaloisForLFunctions.HTGeometry.LogWeightedPoisson

/-!
# Literal reciprocal-Gamma weights of the Xi-square density

Gamma recurrence identifies the exact rational zeta-square density. The
reciprocal-Gamma continuation is entire and agrees with that density on the
critical line. The existing square-root zeta bound gives a common Poisson
envelope at every integer order at least four, including logarithmic
integrability. Integer-dilation correlation signs and the positive-coefficient
mixture assembly remain separate obligations; no deficit estimate is asserted.
-/

noncomputable section
open MeasureTheory Set Complex
open scoped BigOperators
namespace RHTower.WeilWorkDeficitGamma

/-- The actual Xi-square density with its reciprocal-Gamma weight. -/
def density (N : ℕ) (t : ℝ) : ℝ :=
  ‖XiC (t:ℂ)‖^2 / ‖Complex.Gamma ((N:ℂ)+1/4+(t:ℂ)*I/2)‖^2

/-- Entire continuation of the literal weighted density in the Mellin variable. -/
def spectralMellin (N : ℕ) (s : ℂ) : ℂ :=
  xi s^2 / (Complex.Gamma ((N:ℂ)+s/2) * Complex.Gamma ((N:ℂ)+1/2-s/2))

/-- Reciprocal Gamma cancels poles without any zero-location hypothesis. -/
theorem differentiable_spectralMellin (N : ℕ) : Differentiable ℂ (spectralMellin N) := by
  have h1 : Differentiable ℂ (fun s : ℂ => (Complex.Gamma ((N:ℂ)+s/2))⁻¹) :=
    Complex.differentiable_one_div_Gamma.comp (by fun_prop)
  have h2 : Differentiable ℂ (fun s : ℂ => (Complex.Gamma ((N:ℂ)+1/2-s/2))⁻¹) :=
    Complex.differentiable_one_div_Gamma.comp (by fun_prop)
  have hform : spectralMellin N = fun s : ℂ => xi s^2 *
      ((Complex.Gamma ((N:ℂ)+s/2))⁻¹ *
        (Complex.Gamma ((N:ℂ)+1/2-s/2))⁻¹) := by
    funext s
    simp [spectralMellin, div_eq_mul_inv, mul_comm]
  rw [hform]
  exact (xi_differentiable.pow 2).mul (h1.mul h2)

/-- The entire Mellin extension is exactly the actual density on the critical line. -/
theorem spectralMellin_critical (N : ℕ) (t : ℝ) :
    spectralMellin N (1/2+(t:ℂ)*I) = (density N t:ℂ) := by
  have hfirst : (N:ℂ)+((1/2:ℂ)+(t:ℂ)*I)/2 = (N:ℂ)+1/4+(t:ℂ)*I/2 := by ring
  have hsecond : (N:ℂ)+1/2-((1/2:ℂ)+(t:ℂ)*I)/2 =
      (starRingEnd ℂ) ((N:ℂ)+1/4+(t:ℂ)*I/2) := by
    simp only [map_add, map_div₀, map_natCast, map_one, map_ofNat,
      map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  have hxi : (XiC (t:ℂ))^2 = ((‖XiC (t:ℂ)‖^2:ℝ):ℂ) := by
    rw [XiC_ofReal]
    simp [Complex.norm_real, sq_abs]
  rw [spectralMellin, hfirst, hsecond, Complex.Gamma_conj,
    Complex.mul_conj, Complex.normSq_eq_norm_sq, ← XiC, hxi]
  simp only [density, Complex.ofReal_div]

private theorem gamma_norm_step (N : ℕ) (t : ℝ) :
    ‖Complex.Gamma (((N+1:ℕ):ℂ)+1/4+(t:ℂ)*I/2)‖^2 =
      (((N:ℝ)+1/4)^2+t^2/4) *
        ‖Complex.Gamma ((N:ℂ)+1/4+(t:ℂ)*I/2)‖^2 := by
  have hz : (N:ℂ)+1/4+(t:ℂ)*I/2 ≠ 0 :=
    Complex.ne_zero_of_re_pos (by simp; positivity)
  rw [show ((N+1:ℕ):ℂ)+1/4+(t:ℂ)*I/2 =
      ((N:ℂ)+1/4+(t:ℂ)*I/2)+1 by push_cast; ring,
    Complex.Gamma_add_one _ hz, norm_mul, mul_pow, Complex.sq_norm,
    Complex.normSq_apply]
  congr 1
  simp
  ring

private theorem gamma_norm_pos (N : ℕ) (t : ℝ) :
    0 < ‖Complex.Gamma ((N:ℂ)+1/4+(t:ℂ)*I/2)‖^2 := by
  exact sq_pos_of_pos (norm_pos_iff.2
    (Complex.Gamma_ne_zero_of_re_pos (by simp; positivity)))

private theorem xi_norm (t : ℝ) :
    ‖XiC (t:ℂ)‖^2 = (t^2+1/4)^2/(4*Real.sqrt Real.pi) *
      ‖Complex.Gamma (1/4+(t:ℂ)*I/2)‖^2 *
      ‖riemannZeta (1/2+(t:ℂ)*I)‖^2 := by
  have hs0 : (1/2:ℂ)+(t:ℂ)*I ≠ 0 :=
    Complex.ne_zero_of_re_pos (by norm_num)
  have hs1 : (1/2:ℂ)+(t:ℂ)*I ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
  have hG := Complex.Gammaℝ_ne_zero_of_re_pos
    (s := (1/2:ℂ)+(t:ℂ)*I) (by norm_num)
  have hnorm1 : ‖(1/2:ℂ)+(t:ℂ)*I‖^2 = t^2+1/4 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  have hnorm2 : ‖(1/2:ℂ)+(t:ℂ)*I-1‖^2 = t^2+1/4 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  have hpi : ‖(Real.pi:ℂ)^(-((1/2:ℂ)+(t:ℂ)*I)/2)‖^2 =
      (Real.sqrt Real.pi)⁻¹ := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    norm_num
    rw [← Real.rpow_mul_natCast Real.pi_pos.le (-(1/4:ℝ)) 2]
    norm_num
    rw [Real.rpow_neg Real.pi_pos.le, ← Real.sqrt_eq_rpow]
  rw [XiC, xi_eq_archFactor_mul_zeta hs0 hs1 hG, archFactor, Complex.Gammaℝ_def]
  simp only [norm_mul, norm_div, mul_pow, div_pow, Complex.norm_ofNat]
  rw [hnorm1, hnorm2, hpi,
    show ((1/2:ℂ)+(t:ℂ)*I)/2 = 1/4+(t:ℂ)*I/2 by ring]
  ring

private theorem density_step (N : ℕ) (t : ℝ) :
    density (N+1) t = density N t / (((N:ℝ)+1/4)^2+t^2/4) := by
  unfold density
  rw [gamma_norm_step]
  rw [mul_comm (((N:ℝ)+1/4)^2+t^2/4), ← div_div]

/-- Exact rational zeta-square density of every positive integer Gamma weight. -/
theorem density_succ (N : ℕ) (t : ℝ) :
    density (N+1) t = 4^N / Real.sqrt Real.pi * (t^2+1/4) *
      ‖riemannZeta (1/2+(t:ℂ)*I)‖^2 /
      ∏ j ∈ Finset.range N, (t^2+(2*(j:ℝ)+5/2)^2) := by
  induction N with
  | zero =>
    have hg : ‖Complex.Gamma (1/4+(t:ℂ)*I/2)‖ ≠ 0 := norm_ne_zero_iff.2
      (Complex.Gamma_ne_zero_of_re_pos (by norm_num))
    rw [density_step]
    simp only [density, Nat.cast_zero, zero_add]
    rw [xi_norm]
    simp only [pow_zero, Finset.prod_range_zero, div_one]
    generalize hgg : ‖Complex.Gamma (1/4+(t:ℂ)*I/2)‖ = g at *
    field_simp [hg]
    ring
  | succ N ih =>
    have hstep : density (N+1+1) t =
        density (N+1) t / (((N:ℝ)+1+1/4)^2+t^2/4) := by
      simpa only [Nat.cast_add, Nat.cast_one] using density_step (N+1) t
    rw [hstep, ih, Finset.prod_range_succ]
    have heq : ((N:ℝ)+1+1/4)^2+t^2/4 = (t^2+(2*(N:ℝ)+5/2)^2)/4 := by ring
    rw [heq, pow_succ (4:ℝ) N]
    field_simp

private theorem density_nonneg (N : ℕ) (t : ℝ) : 0 ≤ density N t := by
  unfold density
  positivity

private theorem continuous_density (N : ℕ) : Continuous (density N) := by
  have hG : Continuous fun t : ℝ => Complex.Gamma ((N:ℂ)+1/4+(t:ℂ)*I/2) := by
    rw [continuous_iff_continuousAt]
    intro t
    apply (Complex.differentiableAt_Gamma _ ?_).continuousAt.comp
      (by fun_prop : ContinuousAt (fun t : ℝ => (N:ℂ)+1/4+(t:ℂ)*I/2) t)
    intro m h
    have hre := congrArg Complex.re h
    simp at hre
    have hn : 0 ≤ (N:ℝ) := Nat.cast_nonneg _
    have hm : 0 ≤ (m:ℝ) := Nat.cast_nonneg _
    linarith
  unfold density
  exact ((XiC_differentiable.continuous.comp Complex.continuous_ofReal).norm.pow 2).div
    (hG.norm.pow 2) fun t => (gamma_norm_pos N t).ne'

private theorem zeta_sq_bound (t : ℝ) :
    ‖riemannZeta (1/2+(t:ℂ)*I)‖^2 ≤ 108*(1+t^2) := by
  have hsep : (1/2:ℝ) ≤ ‖(1/2:ℂ)+(t:ℂ)*I-1‖ := by
    have h := Complex.abs_re_le_norm ((1/2:ℂ)+(t:ℂ)*I-1)
    norm_num at h ⊢
    exact h
  have h := norm_riemannZeta_le_sqrt_norm_add_two_half
    (s := (1/2:ℂ)+(t:ℂ)*I) (by norm_num) (by norm_num : (0:ℝ)<1/2) hsep
  norm_num at h
  have hs := Real.sq_sqrt (show 0 ≤ ‖(1/2:ℂ)+(t:ℂ)*I‖+2 by positivity)
  have hn := Complex.norm_le_abs_re_add_abs_im ((1/2:ℂ)+(t:ℂ)*I)
  norm_num at hn
  have ha : |t| ≤ t^2+1/2 := by nlinarith [sq_nonneg (|t|-1/2), sq_abs t]
  nlinarith [norm_nonneg (riemannZeta (1/2+(t:ℂ)*I)),
    Real.sqrt_nonneg (‖(1/2:ℂ)+(t:ℂ)*I‖+2)]

private theorem density_four_bound (t : ℝ) :
    density 4 t ≤ (6912/Real.sqrt Real.pi) * (1+t^2)⁻¹ := by
  have hx : 0 < 1+t^2 := by positivity
  have hs : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  rw [show 4=3+1 by rfl, density_succ]
  norm_num [Finset.prod_range_succ]
  have hden : (1+t^2)^3 ≤ (t^2+25/4)*(t^2+81/4)*(t^2+169/4) := by
    calc _ = (1+t^2)*(1+t^2)*(1+t^2) := by ring
         _ ≤ _ := mul_le_mul
           (mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity))
           (by linarith) (by positivity) (by positivity)
  calc
    _ ≤ (64/Real.sqrt Real.pi)*(1+t^2)*(108*(1+t^2)) /
        ((t^2+25/4)*(t^2+81/4)*(t^2+169/4)) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
        (zeta_sq_bound t) (sq_nonneg _) (by positivity)
    _ ≤ (64/Real.sqrt Real.pi)*(1+t^2)*(108*(1+t^2)) / (1+t^2)^3 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ = _ := by field_simp; ring

private theorem density_add_four_le (N : ℕ) (t : ℝ) :
    density (N+4) t ≤ density 4 t := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hfac : 1 ≤ ((N+4:ℕ):ℝ)+1/4 := by
      push_cast
      linarith [show (0:ℝ) ≤ (N:ℝ) from Nat.cast_nonneg N]
    have hsq : 1 ≤ (((N+4:ℕ):ℝ)+1/4)^2+t^2/4 := by nlinarith [sq_nonneg t]
    rw [show N+1+4=(N+4)+1 by omega, density_step]
    exact (div_le_self (density_nonneg _ _) hsq).trans ih

/-- One common Poisson envelope for all literal Gamma weights of order at least four. -/
theorem density_add_four_bound (N : ℕ) (t : ℝ) :
    density (N+4) t ≤ (6912/Real.sqrt Real.pi)*(1+t^2)⁻¹ :=
  (density_add_four_le N t).trans (density_four_bound t)

/-- Absolute integrability of the literal Gamma-weighted Xi density. -/
theorem integrable_density_add_four (N : ℕ) : Integrable (density (N+4)) := by
  refine (integrable_inv_one_add_sq.const_mul (6912/Real.sqrt Real.pi)).mono'
    (continuous_density _).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun t => by
    rw [Real.norm_eq_abs, abs_of_nonneg (density_nonneg _ _)]
    exact density_add_four_bound N t

/-- The actual density also pays the logarithmic moment required by C15. -/
theorem integrable_log_density_add_four (N : ℕ) :
    Integrable fun t => Real.log (2+|t|)*density (N+4) t := by
  have hi := GaloisForLFunctions.HTGeometry.integrable_log_mul_inv_sq_add_sq
    (by norm_num : (0:ℝ)<1)
  norm_num only [one_pow] at hi
  refine (hi.const_mul (6912/Real.sqrt Real.pi)).mono' ?_ ?_
  · exact ((continuous_const.add continuous_abs).log
      (fun t => ne_of_gt (by positivity : (0:ℝ)<2+|t|))).mul
      (continuous_density _) |>.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun t => by
    have hl : 0 ≤ Real.log (2+|t|) := Real.log_nonneg (by linarith [abs_nonneg t])
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hl (density_nonneg _ _))]
    have hb := mul_le_mul_of_nonneg_left (density_add_four_bound N t) hl
    simpa only [mul_left_comm] using hb
end RHTower.WeilWorkDeficitGamma
