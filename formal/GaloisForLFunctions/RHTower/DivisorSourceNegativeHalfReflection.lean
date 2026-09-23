import GaloisForLFunctions.RHTower.DivisorSourceEntire
import GaloisForLFunctions.RHTower.SmoothAFEZetaChiShiftDerivative
import GaloisForLFunctions.RHTower.SeamDivisionSourceSplit
import GaloisForLFunctions.RHTower.ZetaFisherVariance

/-!
# Reflection of the literal divisor source at the negative half argument

Gamma recurrence and the quarter digamma identities evaluate the reflection
factor and its logarithmic derivative exactly. Differentiating the actual
zeta functional equation expresses the source at -1/2 through two real,
absolutely convergent Dirichlet series at 3/2.
-/

noncomputable section
open Complex Filter Set Topology
namespace RHTower

private lemma neg_half_gamma_ne : Complex.Gammaℝ (-(1/2)) ≠ 0 := by
  intro h
  obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp h
  have hr := congrArg Complex.re hn
  norm_num at hr
  cases n with
  | zero => norm_num at hr
  | succ n => simp only [Nat.cast_add, Nat.cast_one] at hr; nlinarith [Nat.cast_nonneg (α := ℝ) n]

/-- The exact functional-equation factor at the negative half argument. -/
theorem zetaChi_negative_half : zetaChi (-(1/2)) = -1/(4*(Real.pi:ℂ)) := by
  have hg := Complex.Gammaℝ_add_two (s := -(1/2)) (by norm_num)
  norm_num at hg
  have hg' : Complex.Gammaℝ (3/2) = Complex.Gammaℝ (-(1/2))*(-1/(4*(Real.pi:ℂ))) := by
    rw [hg]
    ring
  rw [zetaChi, show (1:ℂ)-(-(1/2))=3/2 by ring, hg', mul_comm,
    mul_div_assoc, div_self neg_half_gamma_ne, mul_one]

private lemma quarter_off_poles : ∀ n : ℕ, (-(1/4):ℂ) ≠ -(n:ℂ) := by
  intro n hn
  have hr := congrArg Complex.re hn
  norm_num at hr
  cases n with
  | zero => norm_num at hr
  | succ n => simp only [Nat.cast_add, Nat.cast_one] at hr; nlinarith [Nat.cast_nonneg (α := ℝ) n]

/-- The exact logarithmic derivative of the reflection factor at -(1/2). -/
theorem logDeriv_zetaChi_negative_half :
    logDeriv zetaChi (-(1/2)) =
      ((Real.log (8*Real.pi)+Real.eulerMascheroniConstant-2-Real.pi/2:ℝ):ℂ) := by
  have hq : Complex.digamma (3/4:ℂ) =
      -(Real.eulerMascheroniConstant:ℂ)-3*Complex.log 2+(Real.pi:ℂ)/2 := by
    have hd := GaloisForLFunctions.SeamSplit.digamma_three_quarters_sub_quarter
    rw [GaloisForLFunctions.SeamSplit.digamma_one_quarter] at hd
    linear_combination hd
  have hr := Complex.digamma_apply_add_one (-(1/4)) quarter_off_poles
  norm_num at hr
  have hn : Complex.digamma (-(1/4):ℂ) = Complex.digamma (3/4:ℂ)+4 := by
    linear_combination -hr
  have h := logDeriv_zetaChi_off_poles (z := -(1/2))
    (by convert quarter_off_poles using 1; norm_num)
    (by intro n hn; have he := congrArg Complex.re hn; norm_num at he; nlinarith [Nat.cast_nonneg (α := ℝ) n])
  norm_num at h
  rw [h,hn,hq]
  have hl : Real.log (8*Real.pi)=3*Real.log 2+Real.log Real.pi := by
    rw [Real.log_mul (by norm_num) Real.pi_ne_zero,
      show (8:ℝ)=2^(3 : ℕ) by norm_num, Real.log_pow]
    norm_num
  rw [hl]
  push_cast
  have hl2 : (Real.log 2:ℂ)=Complex.log 2 := by
    simpa only [Nat.cast_ofNat] using (Complex.natCast_log (n := 2))
  rw [← hl2]
  ring

private lemma reflected_zeta_derivative :
    deriv riemannZeta (-(1/2)) =
      deriv zetaChi (-(1/2))*riemannZeta (3/2)-zetaChi (-(1/2))*deriv riemannZeta (3/2) := by
  have he : riemannZeta =ᶠ[𝓝 (-(1/2):ℂ)] (fun s => zetaChi s*riemannZeta (1-s)) := by
    filter_upwards [(isOpen_lt Complex.continuous_re continuous_const).mem_nhds
      (by norm_num : (-(1/2):ℂ).re < 0)] with s hs
    apply zeta_eq_zetaChi_mul
    · intro h; norm_num [h] at hs
    · intro h; norm_num [h] at hs
    · apply Complex.Gammaℝ_ne_zero_of_re_pos
      simp only [Complex.sub_re,Complex.one_re]
      linarith
  have hc := (zetaChi_analyticAt (z := -(1/2))
    (Complex.Gammaℝ_ne_zero_of_re_pos (by norm_num))).differentiableAt.hasDerivAt
  have hz : HasDerivAt riemannZeta (deriv riemannZeta (3/2)) (1-(-(1/2):ℂ)) := by
    simpa only [show (1:ℂ)-(-(1/2))=3/2 by ring] using
      (differentiableAt_riemannZeta (s := (3/2:ℂ)) (by norm_num)).hasDerivAt
  have hd := hc.mul (hz.comp (-(1/2)) ((hasDerivAt_id (-(1/2):ℂ)).const_sub 1))
  rw [he.deriv_eq]
  simpa only [Pi.mul_def,Function.comp_def,id_eq,
    show (1:ℂ)-(-(1/2))=3/2 by ring,mul_neg_one,mul_neg,mul_one,← sub_eq_add_neg] using hd.deriv

/-- Reflection expresses the actual entire divisor source at -(1/2) using
two real absolutely convergent Dirichlet series at 3/2. -/
theorem divisorSourceEntire_negative_half_eq :
    divisorSourceEntire (-(1/2)) =
      (((eulerLogMass (3/2)+(Real.log (8*Real.pi)-Real.eulerMascheroniConstant-2-Real.pi/2)*
        eulerMass (3/2)-(eulerMass (3/2))^(2 : ℕ)/(4*Real.pi))/(4*Real.pi):ℝ):ℂ) := by
  have hc : deriv zetaChi (-(1/2)) = logDeriv zetaChi (-(1/2))*zetaChi (-(1/2)) := by
    rw [logDeriv_apply,div_mul_cancel₀]
    rw [zetaChi_negative_half]
    exact div_ne_zero (by norm_num) (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  have hz := zeta_eq_zetaChi_mul (s := -(1/2)) (by norm_num) (by norm_num)
    (Complex.Gammaℝ_ne_zero_of_re_pos (by norm_num))
  norm_num at hz
  rw [divisorSourceEntire_eq (by norm_num),reflected_zeta_derivative,hc,hz,
    zetaChi_negative_half,logDeriv_zetaChi_negative_half]
  have hzr := riemannZeta_ofReal_eq_eulerMass (σ := 3/2) (by norm_num)
  have hdr := deriv_riemannZeta_ofReal (σ := 3/2) (by norm_num)
  norm_num at hzr hdr
  rw [hzr,hdr]
  push_cast
  ring

end RHTower
