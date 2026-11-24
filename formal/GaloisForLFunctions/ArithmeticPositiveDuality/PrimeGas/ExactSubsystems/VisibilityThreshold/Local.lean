import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BoundaryLoss.Envelope

/-! # Monotonicity of finite Euler visibility in damping and prime support -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems

open InverseSpectrum.ShellMixing
open _root_.RHTower.PrimeCoShift

def thermalPoint (β t : ℝ) : ℂ := (β:ℂ)+(t:ℂ)*Complex.I

@[simp] theorem thermalPoint_re (β t : ℝ) : (thermalPoint β t).re = β := by simp [thermalPoint]
@[simp] theorem thermalPoint_im (β t : ℝ) : (thermalPoint β t).im = t := by simp [thermalPoint]

private theorem local_norm_sq (r : ℝ) (u : ℂ) (hu : ‖u‖ = 1) :
    ‖1-(r:ℂ)*u‖^2 = (1-r)^2 + r*‖1-u‖^2 := by
  have hU := congrArg (·^2) hu
  simp only [Complex.sq_norm,Complex.normSq_apply,one_pow] at hU
  simp only [Complex.sq_norm,Complex.normSq_apply,Complex.sub_re,Complex.sub_im,Complex.mul_re,
    Complex.mul_im,Complex.one_re,Complex.one_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,
    add_zero,sub_zero,zero_sub]
  linear_combination (r^2-r)*hU

private theorem local_visibility_antitone {x y : ℝ} (hy : 0 < y) (hxy : y ≤ x) (hx : x < 1)
    (u : ℂ) (hu : ‖u‖ = 1) :
    (1-x)/‖1-(x:ℂ)*u‖ ≤ (1-y)/‖1-(y:ℂ)*u‖ := by
  have hpos (r : ℝ) (hr : 0 < r) (hr' : r < 1) : 0 < ‖1-(r:ℂ)*u‖ := by
    apply norm_pos_iff.mpr
    intro he
    have hn := congrArg norm (sub_eq_zero.mp he)
    rw [norm_one,norm_mul,hu,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr] at hn
    exact hr'.ne hn.symm
  have hxb := hy.trans_le hxy
  have hyb := hxy.trans_lt hx
  apply (div_le_div_iff₀ (hpos x hxb hx) (hpos y hy hyb)).mpr
  apply (sq_le_sq₀ (mul_nonneg (sub_nonneg.mpr hx.le) (norm_nonneg _))
    (mul_nonneg (sub_nonneg.mpr hyb.le) (norm_nonneg _))).mp
  rw [mul_pow,mul_pow,local_norm_sq _ _ hu,local_norm_sq _ _ hu]
  have hz : 0 ≤ (x-y)*(1-x*y)*‖1-u‖^2 :=
    mul_nonneg (mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr
      (mul_le_one₀ hx.le hy.le hyb.le))) (sq_nonneg _)
  linarith only [hz]

private theorem local_heat (β : ℝ) (p : Nat.Primes) :
    heat (β:ℂ) (primePNat p) = (Real.exp (-β*energy (primePNat p)):ℂ) := by
  rw [Complex.ofReal_exp,Complex.ofReal_mul,Complex.ofReal_neg,heat]

/-- At a fixed clock phase, increasing inverse temperature increases finite Euler visibility. -/
theorem envelope_mono_temperature (P : Finset Nat.Primes) (t : ℝ) {β σ : ℝ} (hβ : 0 < β) (h : β ≤ σ) :
    eulerEnvelope P (thermalPoint β t) ≤ eulerEnvelope P (thermalPoint σ t) := by
  unfold eulerEnvelope
  apply Finset.prod_le_prod (fun _ _ => div_nonneg (norm_nonneg _) (norm_nonneg _))
  intro p _
  let E := energy (primePNat p)
  let u := heat ((t:ℂ)*Complex.I) (primePNat p)
  have hu : ‖u‖ = 1 := by simp [u,norm_heat]
  have hE := prime_energy_pos p
  let x := Real.exp (-β*E)
  let y := Real.exp (-σ*E)
  have hx : x < 1 := Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_lt_zero.mpr hβ) hE)
  have hxy : y ≤ x := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg h) hE.le)
  have hn (r : ℝ) (hr : r ≤ 1) : ‖1-(r:ℂ)‖ = 1-r := by
    rw [← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hr)]
  simp only [thermalPoint_re]
  simp only [thermalPoint,heat_add,local_heat]
  change ‖1-(x:ℂ)‖/‖1-(x:ℂ)*u‖ ≤ ‖1-(y:ℂ)‖/‖1-(y:ℂ)*u‖
  rw [hn x hx.le,hn y (hxy.trans hx.le)]
  exact local_visibility_antitone (Real.exp_pos _) hxy hx u hu

/-- Adding prime modes can only decrease the Euler visibility. -/
theorem envelope_antitone_window {P Q : Finset Nat.Primes} (h : P ⊆ Q) {s : ℂ} (hs : 0 < s.re) :
    eulerEnvelope Q s ≤ eulerEnvelope P s := by
  classical
  let f (p : Nat.Primes) := ‖1-heat (s.re:ℂ) (primePNat p)‖ / ‖1-heat s (primePNat p)‖
  have hlocal (p : Nat.Primes) : f p ≤ 1 := by
    have hp := prime_heat_lt_one hs p
    have hd : heat s (primePNat p) ≠ 1 := by intro he; rw [he,norm_one] at hp; exact lt_irrefl _ hp
    apply (div_le_one (norm_pos_iff.mpr (sub_ne_zero.mpr hd.symm))).mpr
    rw [real_heat_eq_norm s,← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr hp.le)]
    simpa only [norm_one,Complex.ofReal_one] using norm_sub_norm_le (1:ℂ) (heat s (primePNat p))
  change ∏ p ∈ Q, f p ≤ ∏ p ∈ P, f p
  exact Finset.prod_le_prod_of_subset_of_le_one h (fun _ _ => div_nonneg (norm_nonneg _) (norm_nonneg _))
    (fun p _ _ => hlocal p)

#print axioms thermalPoint_re
#print axioms thermalPoint_im
#print axioms envelope_mono_temperature
#print axioms envelope_antitone_window

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems
