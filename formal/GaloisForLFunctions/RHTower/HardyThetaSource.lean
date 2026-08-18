import GaloisForLFunctions.RHTower.JacobiThetaBoundaryLimits
import GaloisForLFunctions.RHTower.XiThetaCriticalTrace

/-!
# The Hardy source: the logarithmic theta tail on its strip of holomorphy

The completed zeta function on the critical line is the Fourier transform of the logarithmic theta
source `e^{u/4}(θ(I e^u) - 1)/2 - e^{-u/4}/2`.  Unlike mathlib's `xiThetaLogSource`, which has a
corner at the origin, this normalization is holomorphic on the whole strip `|Im u| < π/2` — the
preimage of the right half-plane under `u ↦ e^u`, which is where the theta series converges.

The theta functional equation makes the source even, and the two functions differ exactly by the
elementary even kernel `e^{-|u|/4}`, whose Fourier transform is the rational polar part of the
completion.
-/

namespace RHTower

open Complex Filter Topology HurwitzZeta

open scoped Real

noncomputable section

/-! ## The strip -/

/-- The open strip `|Im u| < π/2`, the exact holomorphy domain of the logarithmic theta source. -/
def hardyStrip : Set ℂ := {u : ℂ | |u.im| < π / 2}

theorem mem_hardyStrip {u : ℂ} : u ∈ hardyStrip ↔ |u.im| < π / 2 := Iff.rfl

theorem im_I_mul_exp (u : ℂ) : (I * cexp u).im = Real.exp u.re * Real.cos u.im := by
  rw [Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add, Complex.exp_re]

theorem im_I_mul_exp_pos {u : ℂ} (hu : u ∈ hardyStrip) : 0 < (I * cexp u).im := by
  rw [im_I_mul_exp]
  have habs : |u.im| < π / 2 := hu
  have hcos : 0 < Real.cos u.im := by
    refine Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩
    · have := (abs_lt.1 habs).1
      linarith
    · exact (abs_lt.1 habs).2
  positivity

theorem neg_mem_hardyStrip {u : ℂ} (hu : u ∈ hardyStrip) : -u ∈ hardyStrip := by
  rw [mem_hardyStrip, Complex.neg_im, abs_neg]
  exact hu

theorem ofReal_mem_hardyStrip (a : ℝ) : (a : ℂ) ∈ hardyStrip := by
  rw [mem_hardyStrip, Complex.ofReal_im, abs_zero]
  linarith [Real.pi_pos]

/-! ## The source -/

/-- The Hardy source `(e^{u/4}(θ(I e^u) - 1) - e^{-u/4})/2`. -/
def hardySource (u : ℂ) : ℂ :=
  (cexp (u / 4) * (jacobiTheta (I * cexp u) - 1) - cexp (-u / 4)) / 2

/-- The `S`-transformation in source coordinates. -/
theorem jacobiTheta_I_mul_exp_neg {u : ℂ} (hu : u ∈ hardyStrip) :
    jacobiTheta (I * cexp (-u)) = cexp (u / 2) * jacobiTheta (I * cexp u) := by
  have hneg : (-u) ∈ hardyStrip := neg_mem_hardyStrip hu
  have hw : 0 < (I * cexp (-u)).im := im_I_mul_exp_pos hneg
  have hinv : -(I * cexp (-u))⁻¹ = I * cexp u := by
    have hexp : cexp (-u) ≠ 0 := Complex.exp_ne_zero _
    field_simp
    rw [Complex.I_sq, mul_assoc, ← Complex.exp_add]
    simp
  have hfac : I / (I * cexp (-u)) = cexp u := by
    have hexp : cexp (-u) ≠ 0 := Complex.exp_ne_zero _
    field_simp
    rw [← Complex.exp_add]
    simp
  have hS := jacobiTheta_eq_cpow_mul hw
  rw [hinv, hfac] at hS
  have habs : |u.im| < π / 2 := hu
  have hhalf : (cexp u) ^ (1 / 2 : ℂ) = cexp (u / 2) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero u), Complex.log_exp]
    · congr 1
      ring
    · have := (abs_lt.1 habs).1
      linarith [Real.pi_pos]
    · have := (abs_lt.1 habs).2
      linarith [Real.pi_pos]
  rw [hhalf] at hS
  exact hS

/-- **The source is even.**  This is the theta functional equation in logarithmic coordinates. -/
theorem hardySource_neg {u : ℂ} (hu : u ∈ hardyStrip) : hardySource (-u) = hardySource u := by
  have hsplit : cexp (-u / 4) * cexp (u / 2) = cexp (u / 4) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have hneg : cexp (-(-u) / 4) = cexp (u / 4) := by
    congr 1
    ring
  rw [hardySource, hardySource, jacobiTheta_I_mul_exp_neg hu, hneg]
  linear_combination (jacobiTheta (I * cexp u) / 2) * hsplit

/-! ## The real trace -/

theorem jacobiTheta_I_mul_ofReal {t : ℝ} (ht : 0 < t) :
    jacobiTheta (I * (t : ℂ)) - 1 = ((evenKernel 0 t - 1 : ℝ) : ℂ) := by
  have him : 0 < (I * (t : ℂ)).im := by
    rw [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_im, Complex.ofReal_re]
    simpa using ht
  have hsum := hasSum_nat_jacobiTheta him
  have hsumR : HasSum (fun n : ℕ => 2 * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * t))
      (evenKernel 0 t - 1) := by
    have hs := hasSum_nat_cosKernel₀ (0 : ℝ) ht
    have heq := congrFun evenKernel_eq_cosKernel_of_zero t
    rw [heq]
    simpa using hs
  have hterm : ∀ n : ℕ, cexp (↑π * I * ((n : ℂ) + 1) ^ 2 * (I * (t : ℂ)))
      = ((Real.exp (-π * ((n : ℝ) + 1) ^ 2 * t) : ℝ) : ℂ) := by
    intro n
    have hexp : (↑π * I * ((n : ℂ) + 1) ^ 2 * (I * (t : ℂ)))
        = ((-π * ((n : ℝ) + 1) ^ 2 * t : ℝ) : ℂ) := by
      have h1 : (↑π * I * ((n : ℂ) + 1) ^ 2 * (I * (t : ℂ)))
          = I ^ 2 * ((π : ℂ) * ((n : ℂ) + 1) ^ 2 * (t : ℂ)) := by ring
      rw [h1, Complex.I_sq]
      push_cast
      ring
    rw [hexp, ← Complex.ofReal_exp]
  have hC : HasSum (fun n : ℕ => ((2 * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * t) : ℝ) : ℂ))
      (((evenKernel 0 t - 1 : ℝ) : ℂ)) := by
    exact (Complex.ofRealCLM.hasSum hsumR)
  have hC2 : HasSum (fun n : ℕ => cexp (↑π * I * ((n : ℂ) + 1) ^ 2 * (I * (t : ℂ))))
      ((jacobiTheta (I * (t : ℂ)) - 1) / 2) := hsum
  have hcongr : (fun n : ℕ => ((2 * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * t) : ℝ) : ℂ))
      = fun n : ℕ => 2 * cexp (↑π * I * ((n : ℂ) + 1) ^ 2 * (I * (t : ℂ))) := by
    funext n
    rw [hterm n]
    push_cast
    ring
  rw [hcongr] at hC
  have huniq := (hC2.mul_left 2).unique hC
  linear_combination huniq

/-- The source and mathlib's logarithmic theta source differ by the elementary even kernel. -/
theorem xiThetaLogSource_eq_hardySource {a : ℝ} (ha : 0 < a) :
    xiThetaLogSource a = 2 * hardySource (a : ℂ) + ((Real.exp (-a / 4) : ℝ) : ℂ) := by
  have hexp : cexp ((a : ℂ)) = ((Real.exp a : ℝ) : ℂ) := by
    rw [← Complex.ofReal_exp]
  have hpos : (0 : ℝ) < Real.exp a := Real.exp_pos a
  rw [xiThetaLogSource_eq_positiveFormula ha, xiThetaPositiveFormula, hardySource, hexp,
    ← jacobiTheta_I_mul_ofReal hpos]
  have h4 : cexp ((a : ℂ) / 4) = ((Real.exp (a / 4) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  have h4' : cexp (-(a : ℂ) / 4) = ((Real.exp (-a / 4) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [h4, h4']
  ring

/-! ## Holomorphy -/

theorem differentiableAt_hardySource {u : ℂ} (hu : u ∈ hardyStrip) :
    DifferentiableAt ℂ hardySource u := by
  have hmap : DifferentiableAt ℂ (fun z : ℂ => I * cexp z) u := by
    exact (differentiable_exp.differentiableAt).const_mul I
  have hθ : DifferentiableAt ℂ jacobiTheta (I * cexp u) :=
    differentiableAt_jacobiTheta (im_I_mul_exp_pos hu)
  have hcomp : DifferentiableAt ℂ (fun z : ℂ => jacobiTheta (I * cexp z)) u :=
    hθ.comp u hmap
  have h1 : DifferentiableAt ℂ (fun z : ℂ => cexp (z / 4)) u := by
    exact (differentiable_exp.differentiableAt).comp u (by fun_prop)
  have h2 : DifferentiableAt ℂ (fun z : ℂ => cexp (-z / 4)) u := by
    exact (differentiable_exp.differentiableAt).comp u (by fun_prop)
  exact (((h1.mul (hcomp.sub (differentiableAt_const 1))).sub h2).div_const 2)

/-! ## The horizontal decay bound -/

/-- The explicit horizontal decay constant on the sub-strip `|Im u| ≤ c`. -/
def hardySourceBound (c : ℝ) : ℝ :=
  ((2 / (1 - Real.exp (-π * Real.cos c))) * Real.exp (1 / (4 * π * Real.cos c)) + 1) / 2

theorem cos_pos_of_lt_pi_div_two {c : ℝ} (hc0 : 0 ≤ c) (hc : c < π / 2) : 0 < Real.cos c := by
  refine Real.cos_pos_of_mem_Ioo ⟨?_, hc⟩
  linarith [Real.pi_pos]

private theorem exp_sq_le {a : ℝ} (ha : 0 ≤ a) : a ^ 2 / 4 ≤ Real.exp a := by
  have h1 : 1 + a / 2 ≤ Real.exp (a / 2) := by
    have := Real.add_one_le_exp (a / 2)
    linarith
  have h2 : (0 : ℝ) ≤ 1 + a / 2 := by linarith
  have hsq : (1 + a / 2) ^ 2 ≤ Real.exp (a / 2) ^ 2 := by
    exact pow_le_pow_left₀ h2 h1 2
  have hexp : Real.exp (a / 2) ^ 2 = Real.exp a := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  nlinarith [hsq, hexp]

/-- **Horizontal exponential decay of the source.**  On every closed sub-strip the source decays
like `e^{-|Re u|/4}`. -/
theorem norm_hardySource_le {c : ℝ} (hc0 : 0 ≤ c) (hc : c < π / 2) {u : ℂ} (hu : |u.im| ≤ c) :
    ‖hardySource u‖ ≤ hardySourceBound c * Real.exp (-(|u.re| / 4)) := by
  have hcos : 0 < Real.cos c := cos_pos_of_lt_pi_div_two hc0 hc
  -- reduce to nonnegative real part
  have key : ∀ v : ℂ, |v.im| ≤ c → 0 ≤ v.re →
      ‖hardySource v‖ ≤ hardySourceBound c * Real.exp (-(v.re / 4)) := by
    intro v hvim hvre
    have hvstrip : v ∈ hardyStrip := by
      rw [mem_hardyStrip]
      exact lt_of_le_of_lt hvim hc
    have hcosv : Real.cos c ≤ Real.cos v.im := by
      rcases le_or_gt 0 v.im with hpos | hneg
      · refine Real.cos_le_cos_of_nonneg_of_le_pi hpos ?_ ?_
        · linarith [Real.pi_pos, (abs_le.1 hvim).2]
        · exact le_trans (le_abs_self v.im) hvim
      · have hcosneg : Real.cos v.im = Real.cos (-v.im) := (Real.cos_neg v.im).symm
        rw [hcosneg]
        refine Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) ?_ ?_
        · linarith [Real.pi_pos, (abs_le.1 hvim).1]
        · have := (abs_le.1 hvim).1
          linarith
    have hImτ : Real.exp v.re * Real.cos c ≤ (I * cexp v).im := by
      rw [im_I_mul_exp]
      exact mul_le_mul_of_nonneg_left hcosv (Real.exp_pos _).le
    have hImpos : 0 < (I * cexp v).im := im_I_mul_exp_pos hvstrip
    have hgeq : Real.cos c ≤ (I * cexp v).im := by
      have hone : (1 : ℝ) ≤ Real.exp v.re := Real.one_le_exp hvre
      nlinarith [hImτ, hcos]
    -- the theta tail bound
    have htail : ‖jacobiTheta (I * cexp v) - 1‖
        ≤ (2 / (1 - Real.exp (-π * Real.cos c))) *
          Real.exp (-π * (Real.exp v.re * Real.cos c)) := by
      have hb := norm_jacobiTheta_sub_one_le hImpos
      refine hb.trans ?_
      have hlt : Real.exp (-π * (I * cexp v).im) < 1 := by
        rw [Real.exp_lt_one_iff]
        nlinarith [Real.pi_pos, hImpos]
      have hltc : Real.exp (-π * Real.cos c) < 1 := by
        rw [Real.exp_lt_one_iff]
        nlinarith [Real.pi_pos, hcos]
      have hmono1 : Real.exp (-π * (I * cexp v).im) ≤ Real.exp (-π * Real.cos c) := by
        rw [Real.exp_le_exp]
        nlinarith [Real.pi_pos, hgeq]
      have hmono2 : Real.exp (-π * (I * cexp v).im)
          ≤ Real.exp (-π * (Real.exp v.re * Real.cos c)) := by
        rw [Real.exp_le_exp]
        nlinarith [Real.pi_pos, hImτ]
      have hden : 0 < 1 - Real.exp (-π * (I * cexp v).im) := by linarith
      have hdenc : 0 < 1 - Real.exp (-π * Real.cos c) := by linarith
      have hfac : 2 / (1 - Real.exp (-π * (I * cexp v).im))
          ≤ 2 / (1 - Real.exp (-π * Real.cos c)) := by
        rw [div_le_div_iff₀ hden hdenc]
        nlinarith [hmono1]
      have hpos2 : 0 ≤ 2 / (1 - Real.exp (-π * (I * cexp v).im)) := by positivity
      calc 2 / (1 - Real.exp (-π * (I * cexp v).im)) * Real.exp (-π * (I * cexp v).im)
          ≤ 2 / (1 - Real.exp (-π * (I * cexp v).im)) *
              Real.exp (-π * (Real.exp v.re * Real.cos c)) :=
            mul_le_mul_of_nonneg_left hmono2 hpos2
        _ ≤ 2 / (1 - Real.exp (-π * Real.cos c)) *
              Real.exp (-π * (Real.exp v.re * Real.cos c)) :=
            mul_le_mul_of_nonneg_right hfac (Real.exp_pos _).le
    -- assemble
    have hnorm1 : ‖cexp (v / 4)‖ = Real.exp (v.re / 4) := by
      rw [Complex.norm_exp]
      congr 1
      simp [Complex.div_re]
      ring
    have hnorm2 : ‖cexp (-v / 4)‖ = Real.exp (-(v.re / 4)) := by
      rw [Complex.norm_exp]
      congr 1
      simp [Complex.div_re, Complex.neg_re]
      ring
    have hsplit : ‖hardySource v‖
        ≤ (Real.exp (v.re / 4) * ‖jacobiTheta (I * cexp v) - 1‖ + Real.exp (-(v.re / 4))) / 2 := by
      rw [hardySource, norm_div, Complex.norm_two]
      refine div_le_div_of_nonneg_right ?_ (by norm_num) |>.trans_eq rfl
      refine le_trans (norm_sub_le _ _) ?_
      rw [norm_mul, hnorm1, hnorm2]
    -- the double-exponential factor is bounded
    have hquad : Real.exp v.re * Real.cos c ≥ v.re ^ 2 / 4 * Real.cos c := by
      nlinarith [exp_sq_le hvre, hcos]
    have hexpbound : Real.exp (v.re / 4) * Real.exp (-π * (Real.exp v.re * Real.cos c))
        ≤ Real.exp (1 / (4 * π * Real.cos c)) * Real.exp (-(v.re / 4)) := by
      rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
      have hkey : v.re / 2 - π * (Real.exp v.re * Real.cos c) ≤ 1 / (4 * π * Real.cos c) := by
        have hstep : π * (Real.exp v.re * Real.cos c) ≥ π * (v.re ^ 2 / 4 * Real.cos c) := by
          nlinarith [Real.pi_pos, hquad]
        have hfinal : v.re / 2 - π * (v.re ^ 2 / 4 * Real.cos c) ≤ 1 / (4 * π * Real.cos c) := by
          rw [ge_iff_le, ← sub_nonneg] at *
          have hprod : 0 < 4 * π * Real.cos c := by positivity
          rw [le_div_iff₀ hprod] at *
          nlinarith [sq_nonneg (1 - π * Real.cos c * v.re), Real.pi_pos, hcos]
        linarith
      linarith
    have hK : 0 ≤ 2 / (1 - Real.exp (-π * Real.cos c)) := by
      have hltc : Real.exp (-π * Real.cos c) < 1 := by
        rw [Real.exp_lt_one_iff]
        nlinarith [Real.pi_pos, hcos]
      have : 0 < 1 - Real.exp (-π * Real.cos c) := by linarith
      positivity
    calc ‖hardySource v‖
        ≤ (Real.exp (v.re / 4) * ‖jacobiTheta (I * cexp v) - 1‖ + Real.exp (-(v.re / 4))) / 2 :=
          hsplit
      _ ≤ (Real.exp (v.re / 4) * ((2 / (1 - Real.exp (-π * Real.cos c))) *
            Real.exp (-π * (Real.exp v.re * Real.cos c))) + Real.exp (-(v.re / 4))) / 2 := by
          have := mul_le_mul_of_nonneg_left htail (Real.exp_pos (v.re / 4)).le
          linarith
      _ ≤ hardySourceBound c * Real.exp (-(v.re / 4)) := by
          rw [hardySourceBound]
          have hmul : Real.exp (v.re / 4) * ((2 / (1 - Real.exp (-π * Real.cos c))) *
              Real.exp (-π * (Real.exp v.re * Real.cos c)))
              ≤ (2 / (1 - Real.exp (-π * Real.cos c))) *
                (Real.exp (1 / (4 * π * Real.cos c)) * Real.exp (-(v.re / 4))) := by
            have := mul_le_mul_of_nonneg_left hexpbound hK
            linarith [this]
          linarith
  rcases le_or_gt 0 u.re with hpos | hneg
  · rw [abs_of_nonneg hpos]
    exact key u hu hpos
  · have hstrip : u ∈ hardyStrip := by
      rw [mem_hardyStrip]
      exact lt_of_le_of_lt hu hc
    have hneg' : ((-u).im) = -u.im := Complex.neg_im u
    have habs : |(-u).im| ≤ c := by
      rw [hneg', abs_neg]
      exact hu
    have hre : (0 : ℝ) ≤ (-u).re := by
      rw [Complex.neg_re]
      linarith
    have h := key (-u) habs hre
    rw [hardySource_neg hstrip] at h
    rw [abs_of_neg hneg]
    rw [Complex.neg_re] at h
    exact h

theorem integrable_hardySource_line {c : ℝ} (hc0 : 0 ≤ c) (hc : c < π / 2) :
    Integrable (fun a : ℝ => hardySource ((a : ℂ) + (c : ℂ) * I)) := by
  have hmeas : AEStronglyMeasurable (fun a : ℝ => hardySource ((a : ℂ) + (c : ℂ) * I)) := by
    refine Continuous.aestronglyMeasurable ?_
    have hcont : ContinuousOn hardySource hardyStrip := by
      intro z hz
      exact ((differentiableAt_hardySource hz).continuousAt).continuousWithinAt
    refine ContinuousAt.continuous fun a => ?_
    have hmem : ((a : ℂ) + (c : ℂ) * I) ∈ hardyStrip := by
      rw [mem_hardyStrip]
      simp [Complex.add_im, Complex.ofReal_im, Complex.mul_im]
      rw [abs_of_nonneg hc0]
      exact hc
    exact ((differentiableAt_hardySource hmem).continuousAt).comp (by fun_prop)
  refine Integrable.mono' (g := fun a : ℝ => hardySourceBound c * Real.exp (-(1 / 4 * |a|)))
    ?_ hmeas ?_
  · exact (integrable_exp_neg_mul_abs' (by norm_num)).const_mul _
  · filter_upwards with a
    have him : |((a : ℂ) + (c : ℂ) * I).im| ≤ c := by
      simp [Complex.add_im, Complex.ofReal_im, Complex.mul_im]
      rw [abs_of_nonneg hc0]
    have hre : ((a : ℂ) + (c : ℂ) * I).re = a := by
      simp [Complex.add_re, Complex.mul_re]
    have h := norm_hardySource_le hc0 hc him
    rw [hre] at h
    refine h.trans ?_
    have : -(|a| / 4) = -(1 / 4 * |a|) := by ring
    rw [this]

end

end RHTower
