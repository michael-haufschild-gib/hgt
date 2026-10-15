import GaloisForLFunctions.RHTower.WeilOddConeMinorantRigidity
import GaloisForLFunctions.RHTower.EvenSectorPoleWeightWindow

/-!
# The pole-weight windows of `Λ` on even and on odd tests

For a pole weight `β` put `W_β = W + (β − 1) P` (`WeilPoleWeight.weilPoleWeightFunctional`), where
`P(k) = k̂(i/2) + k̂(−i/2)` is the pole term.  On the autocorrelation of an odd test
`P = −2 |f̂(i/2)|² ≤ 0` (`re_weilPoleTerm_weilTest_of_odd`), so odd positivity is antitone in `β`
(`weilPositiveOddAt_anti`); on even tests `P ≥ 0` and even positivity is monotone.

**Theorem** (`not_weilPositiveOddAt_vonMangoldt_of_one_lt`, unconditional).  For `β > 1` the
functional `W_β` with the weights `Λ` is negative on some odd test.

**Theorem** (`riemannHypothesis_iff_forall_weilPositiveOddAt_vonMangoldt_iff`).  RH holds iff `W_β`
with the weights `Λ` is nonnegative on all odd tests exactly for `β ≤ 1`.  Without RH there is no
such `β` at all (`not_weilPositiveOddAt_vonMangoldt_of_not_riemannHypothesis`).

**Theorem** (`riemannHypothesis_iff_forall_weilPositiveEvenAt_vonMangoldt_iff`).  RH holds iff `W_β`
with the weights `Λ` is nonnegative on all even tests exactly for `β ≥ 1`; without RH there is no
such `β`.

So the odd window of `Λ` is `(−∞, 1]` or empty, the even window is `[1, ∞)` or empty, both are
nonempty exactly under RH, and they meet only at the pole weight `1`
(`eq_one_of_weilPositiveEvenAt_of_weilPositiveOddAt`).

Proofs.
* `β > 1`.  With `c = 2 log 2` the odd translate `Φχ_L(· + c/2) − Φχ_L(· − c/2)` has the
  autocorrelation of `Φχ_L − Φχ_L(· − c)`.  Its zero side tends to `0`, because `Φ̂ = Ξ` vanishes at
  every zero.  Its pole term is `2 (A_L/2)(−A_L) = −A_L²` with `A_L = ∫ Φχ_L e^{−u/2}`, which is
  bounded below for `L ≥ 2`.  So `W_β ≤ o(1) − (β − 1) A_L² < 0` for large `L`.
* Without RH, odd tests.  Take an even `u` with `û(±i/2) = 0` and `W(u) < 0`.  Its odd shifts
  `(u(· − h/2) − u(· + h/2))/2` are pole-free, so `W_β = W` on them for every `β`.  Averaging them
  against Riemann's kernel, whose transform vanishes at every zero, gives one with `W < 0`.
* Without RH, even tests.  The test `u` itself is even and pole-free with `W(u) < 0`.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate
open Zeta23

namespace RHTower

noncomputable section

open WeilPoleWeight

/-! ## Odd tests and the pole weight -/

/-- Weil positivity at pole weight `β` on the autocorrelations of odd tests. -/
def WeilPositiveOddAt (β : ℝ) (lam : ℕ → ℝ) : Prop :=
  ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f → (∀ x, f (-x) = -f x) →
    0 ≤ (weilPoleWeightFunctional β lam (EF.weilTest f f)).re

theorem re_weilPoleWeightFunctional_eq_add (β : ℝ) (lam : ℕ → ℝ) (k : ℝ → ℂ) :
    (weilPoleWeightFunctional β lam k).re =
      (weilFullFunctional lam k).re + (β - 1) * (weilPoleTerm k).re := by
  unfold weilPoleWeightFunctional weilPoleTerm
  rw [Complex.add_re, show ((β : ℂ) - 1) = ((β - 1 : ℝ) : ℂ) by push_cast; ring,
    Complex.re_ofReal_mul]

/-- The transform of an odd test is odd. -/
theorem paperFT_neg_of_odd {f : ℝ → ℂ} (hodd : ∀ x, f (-x) = -f x) (z : ℂ) :
    paperFT f (-z) = -paperFT f z := by
  rw [← paperFT_comp_neg]
  have e : (fun u => f (-u)) = fun u => (-1 : ℂ) * f u := by
    funext u; rw [hodd]; ring
  rw [e, paperFT_const_mul]
  ring

/-- On the autocorrelation of an odd test the pole term is `−2 |f̂(i/2)|²`. -/
theorem re_weilPoleTerm_weilTest_of_odd {f : ℝ → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hodd : ∀ x, f (-x) = -f x) :
    (weilPoleTerm (EF.weilTest f f)).re = -2 * ‖paperFT f (I / 2)‖ ^ 2 := by
  rw [weilPoleTerm_weilTest_eq hf hfc, show (-I / 2 : ℂ) = -(I / 2) by ring,
    paperFT_neg_of_odd hodd, map_neg]
  have e : paperFT f (I / 2) * -(starRingEnd ℂ) (paperFT f (I / 2)) +
      -paperFT f (I / 2) * (starRingEnd ℂ) (paperFT f (I / 2)) =
      -(2 * (paperFT f (I / 2) * (starRingEnd ℂ) (paperFT f (I / 2)))) := by ring
  rw [e, Complex.mul_conj, Complex.normSq_eq_norm_sq,
    show (-(2 * ((‖paperFT f (I / 2)‖ ^ 2 : ℝ) : ℂ))) =
      ((-2 * ‖paperFT f (I / 2)‖ ^ 2 : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]

/-- **Odd Weil positivity is antitone in the pole weight.** -/
theorem weilPositiveOddAt_anti {β β' : ℝ} (h : β ≤ β') {lam : ℕ → ℝ}
    (hβ' : WeilPositiveOddAt β' lam) : WeilPositiveOddAt β lam := fun f hf hfc hodd => by
  have h1 := hβ' f hf hfc hodd
  rw [re_weilPoleWeightFunctional_eq_add, re_weilPoleTerm_weilTest_of_odd hf.continuous hfc hodd]
    at h1 ⊢
  have h2 := mul_nonneg (sub_nonneg.mpr h) (sq_nonneg ‖paperFT f (I / 2)‖)
  nlinarith

theorem weilPositiveOddAt_one_iff {lam : ℕ → ℝ} :
    WeilPositiveOddAt 1 lam ↔ WeilPositiveOdd lam := by
  unfold WeilPositiveOddAt WeilPositiveOdd
  simp only [weilPoleWeightFunctional, Complex.ofReal_one, sub_self, zero_mul, add_zero]

/-! ## Pole weights above `1` fail on odd tests -/

/-- The truncated Riemann kernel has equal exponential moments at `±1/2`. -/
theorem integral_truncatedRiemannKernelReal_mul_exp_half (L : ℝ) :
    ∫ u, truncatedRiemannKernelReal L u * Real.exp (u / 2) =
      ∫ u, truncatedRiemannKernelReal L u * Real.exp (-u / 2) := by
  rw [← integral_neg_eq_self (fun u => truncatedRiemannKernelReal L u * Real.exp (-u / 2))]
  congr 1; funext u
  rw [truncatedRiemannKernelReal_neg, neg_neg]

theorem cexp_I_mul_I_div_two_mul_two_log_two :
    cexp (I * (I / 2) * ((2 * Real.log 2 : ℝ) : ℂ)) = 1 / 2 := by
  have e : I * (I / 2) * ((2 * Real.log 2 : ℝ) : ℂ) = ((-Real.log 2 : ℝ) : ℂ) := by
    push_cast
    rw [show I * (I / 2) * (2 * (Real.log 2 : ℂ)) = (I * I) * (Real.log 2 : ℂ) by ring,
      Complex.I_mul_I]
    ring
  rw [e, ← Complex.ofReal_exp, Real.exp_neg, Real.exp_log two_pos]
  push_cast; ring

theorem cexp_I_mul_neg_I_div_two_mul_two_log_two :
    cexp (I * (-I / 2) * ((2 * Real.log 2 : ℝ) : ℂ)) = 2 := by
  have e : I * (-I / 2) * ((2 * Real.log 2 : ℝ) : ℂ) = ((Real.log 2 : ℝ) : ℂ) := by
    push_cast
    rw [show I * (-I / 2) * (2 * (Real.log 2 : ℂ)) = -(I * I) * (Real.log 2 : ℂ) by ring,
      Complex.I_mul_I]
    ring
  rw [e, ← Complex.ofReal_exp, Real.exp_log two_pos]
  norm_num

/-- The moment `∫ f e^{−u/2}` of the log-shift difference with `c = 2 log 2`. -/
theorem integral_logShiftTwoLogTwo_mul_exp_neg_half (L : ℝ) :
    ∫ u, (truncatedRiemannKernelReal L u - truncatedRiemannKernelReal L (u - 2 * Real.log 2)) *
      Real.exp (-u / 2) = (∫ u, truncatedRiemannKernelReal L u * Real.exp (-u / 2)) / 2 := by
  have h := paperFT_logShiftRiemannDifference L (2 * Real.log 2) (I / 2)
  rw [logShiftRiemannDifference_eq, paperFT_ofRealFun_I_div_two,
    cexp_I_mul_I_div_two_mul_two_log_two, truncatedRiemannKernel_eq_ofReal,
    paperFT_ofRealFun_I_div_two] at h
  apply Complex.ofReal_injective
  rw [h]; push_cast; ring

/-- The moment `∫ f e^{u/2}` of the log-shift difference with `c = 2 log 2`. -/
theorem integral_logShiftTwoLogTwo_mul_exp_half (L : ℝ) :
    ∫ u, (truncatedRiemannKernelReal L u - truncatedRiemannKernelReal L (u - 2 * Real.log 2)) *
      Real.exp (u / 2) = -∫ u, truncatedRiemannKernelReal L u * Real.exp (-u / 2) := by
  have h := paperFT_logShiftRiemannDifference L (2 * Real.log 2) (-I / 2)
  rw [logShiftRiemannDifference_eq, paperFT_ofRealFun_neg_I_div_two,
    cexp_I_mul_neg_I_div_two_mul_two_log_two, truncatedRiemannKernel_eq_ofReal,
    paperFT_ofRealFun_neg_I_div_two, integral_truncatedRiemannKernelReal_mul_exp_half] at h
  apply Complex.ofReal_injective
  rw [h]; push_cast; ring

/-- **Pole weights above `1` fail for `Λ` on odd tests**, unconditionally. -/
theorem not_weilPositiveOddAt_vonMangoldt_of_one_lt {β : ℝ} (hβ : 1 < β) :
    ¬ WeilPositiveOddAt β fun n => (ArithmeticFunction.vonMangoldt n : ℝ) := by
  intro h
  set c : ℝ := 2 * Real.log 2 with hcdef
  have hc : 0 ≤ c := by have := Real.log_pos one_lt_two; positivity
  have hec : Real.exp (c / 2) = 2 := by
    rw [hcdef, show 2 * Real.log 2 / 2 = Real.log 2 by ring, Real.exp_log two_pos]
  obtain ⟨κ, hκ, hA⟩ := exists_integral_truncatedRiemannKernelReal_exp_ge
  obtain ⟨Λc, -, hΛc⟩ := GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition
  have hβ1 : 0 < β - 1 := by linarith
  set ε : ℝ := (β - 1) * κ ^ 2 / 18 with hε
  have hε0 : 0 < ε := by positivity
  obtain ⟨L₀, hL₀⟩ := exists_exp_mul_nearRadicalEnergy_le hε0
  set L : ℝ := max L₀ 2 with hL
  have hL2 : 2 ≤ L := le_max_right _ _
  set F : ℝ → ℝ := fun u => truncatedRiemannKernelReal L u - truncatedRiemannKernelReal L (u - c)
    with hF
  have hFeq : logShiftRiemannDifference L c = fun u => (F u : ℂ) := logShiftRiemannDifference_eq L c
  have hFd : ContDiff ℝ 2 fun u => (F u : ℂ) := hFeq ▸ contDiff_logShiftRiemannDifference L c
  have hFr : Continuous F := (continuous_truncatedRiemannKernelReal L).sub
    ((continuous_truncatedRiemannKernelReal L).comp (continuous_id.sub continuous_const))
  have hFc : HasCompactSupport F := by
    have h1 := hasCompactSupport_logShiftRiemannDifference L c
    rw [hFeq] at h1
    exact (hasCompactSupport_comp_left (g := fun x : ℝ => (x : ℂ))
      Complex.ofReal_eq_zero).mp h1
  have hpos := h (oddLogShiftRiemannDifference L c) (contDiff_oddLogShiftRiemannDifference L c)
    (hasCompactSupport_oddLogShiftRiemannDifference L c) (oddLogShiftRiemannDifference_neg L c)
  rw [weilTest_oddLogShiftRiemannDifference, hFeq,
    re_weilPoleWeightFunctional_ofReal β _ hFd hFr hFc] at hpos
  have hap : atomPairing (fun n => (ArithmeticFunction.vonMangoldt n : ℝ) -
      ArithmeticFunction.vonMangoldt n) (crossCorr F F) = 0 := by
    unfold atomPairing; simp
  rw [hap, hF, integral_logShiftTwoLogTwo_mul_exp_neg_half,
    integral_logShiftTwoLogTwo_mul_exp_half] at hpos
  set A := ∫ u, truncatedRiemannKernelReal L u * Real.exp (-u / 2) with hAdef
  have hAκ : κ ≤ A := by
    have e : (fun u => truncatedRiemannKernelReal L u * Real.exp (-u / 2)) =
        fun u => truncatedRiemannKernelReal L u * Real.exp (-(u / 2)) := by
      funext u; rw [neg_div]
    rw [hAdef, e]; exact hA L hL2
  have hW : (zetaZeroConfig.W (fun u => (F u : ℂ)) fun u => (F u : ℂ)).re ≤ 9 * ε := by
    have hb := norm_W_logShiftRiemannDifference_le L hc hΛc
    rw [hFeq, hec] at hb
    have hq := hL₀ L (le_max_left _ _)
    have he : 1 ≤ Real.exp (2 * L) := Real.one_le_exp (by linarith)
    have hnn : 0 ≤ (5 / 4) * zetaInvSqSum * truncatedRiemannTailEnergy L ^ 2 := by
      have := zetaInvSqSum_nonneg; positivity
    have hq' : (5 / 4) * zetaInvSqSum * truncatedRiemannTailEnergy L ^ 2 ≤ ε := by nlinarith
    calc (zetaZeroConfig.W (fun u => (F u : ℂ)) fun u => (F u : ℂ)).re
        ≤ ‖zetaZeroConfig.W (fun u => (F u : ℂ)) fun u => (F u : ℂ)‖ := Complex.re_le_norm _
      _ ≤ (1 + 2) ^ 2 * ((5 / 4) * zetaInvSqSum * truncatedRiemannTailEnergy L ^ 2) := hb
      _ ≤ (1 + 2) ^ 2 * ε := by gcongr
      _ = 9 * ε := by norm_num
  have hA2 : κ ^ 2 ≤ A ^ 2 := pow_le_pow_left₀ hκ.le hAκ 2
  have key : (β - 1) * (2 * (A / 2 * -A)) = -((β - 1) * A ^ 2) := by ring
  have h3 := mul_le_mul_of_nonneg_left hA2 hβ1.le
  have h4 : 0 < (β - 1) * κ ^ 2 := by positivity
  rw [sub_zero, key] at hpos
  linarith

/-! ## Without RH no pole weight works -/

/-- **Without RH there is a pole-free odd test of negative Weil energy.** -/
theorem exists_odd_poleFree_negative_of_not_riemannHypothesis (hRH : ¬ RiemannHypothesis) :
    ∃ f : ℝ → ℝ, ContDiff ℝ 2 f ∧ HasCompactSupport f ∧ (∀ x, f (-x) = -f x) ∧
      paperFT (fun x => (f x : ℂ)) (I / 2) = 0 ∧
      (zetaZeroConfig.W (fun x => (f x : ℂ)) (fun x => (f x : ℂ))).re < 0 := by
  obtain ⟨u, hu, hcpt, heven, hp, hneg⟩ :=
    exists_even_poleFree_negative_of_not_riemannHypothesis hRH
  have hpole : ∀ h : ℝ, paperFT (fun x => (oddShift u h x : ℂ)) (I / 2) = 0 := fun h => by
    rw [paperFT_oddShift hu.continuous hcpt, hp, mul_zero]
  by_contra hcon
  push Not at hcon
  have hall : ∀ h : ℝ, 0 ≤ (zetaZeroConfig.W (fun x => (oddShift u h x : ℂ))
      (fun x => (oddShift u h x : ℂ))).re := fun h =>
    hcon _ (contDiff_oddShift hu h) (hasCompactSupport_oddShift hcpt h) (oddShift_neg heven h)
      (hpole h)
  obtain ⟨hI, hval⟩ := integral_W_oddShift_mul_riemannPhiKernel hu hcpt
  have hre := integral_re hI
  have hnn : 0 ≤ ∫ h : ℝ, RCLike.re (zetaZeroConfig.W (fun x => (oddShift u h x : ℂ))
      (fun x => (oddShift u h x : ℂ)) * riemannPhiKernel h) := by
    refine integral_nonneg fun h => ?_
    show 0 ≤ (zetaZeroConfig.W (fun x => (oddShift u h x : ℂ)) (fun x => (oddShift u h x : ℂ)) *
      riemannPhiKernel h).re
    rw [riemannPhiKernel_eq_ofReal, Complex.re_mul_ofReal]
    exact mul_nonneg (hall h) (riemannKernelReal_pos h).le
  rw [hre, hval] at hnn
  have hΦ : (∫ h : ℝ, riemannPhiKernel h) = ((∫ h, riemannKernelReal h : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    exact integral_congr_ae (Eventually.of_forall fun h => riemannPhiKernel_eq_ofReal h)
  rw [hΦ] at hnn
  have hpos := integral_riemannKernelReal_pos
  have e : RCLike.re (((∫ h, riemannKernelReal h : ℝ) : ℂ) / 2 *
      zetaZeroConfig.W (fun x => (u x : ℂ)) (fun x => (u x : ℂ))) =
      (∫ h, riemannKernelReal h) / 2 * (zetaZeroConfig.W (fun x => (u x : ℂ))
        (fun x => (u x : ℂ))).re := by
    show (((∫ h, riemannKernelReal h : ℝ) : ℂ) / 2 * _).re = _
    rw [show ((∫ h, riemannKernelReal h : ℝ) : ℂ) / 2 = (((∫ h, riemannKernelReal h) / 2 : ℝ) : ℂ)
      by push_cast; ring, Complex.re_ofReal_mul]
  rw [e] at hnn
  have : (∫ h, riemannKernelReal h) / 2 * (zetaZeroConfig.W (fun x => (u x : ℂ))
      (fun x => (u x : ℂ))).re < 0 := mul_neg_of_pos_of_neg (by positivity) hneg
  linarith

/-- The functional with pole weight `β` and the weights `Λ` on a real pole-free test is its zeta
side. -/
theorem re_weilPoleWeightFunctional_vonMangoldt_of_poleFree (β : ℝ) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hp : paperFT (fun x => (f x : ℂ)) (I / 2) = 0) :
    (weilPoleWeightFunctional β (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
      (EF.weilTest (fun x => (f x : ℂ)) fun x => (f x : ℂ))).re =
      (zetaZeroConfig.W (fun x => (f x : ℂ)) fun x => (f x : ℂ)).re := by
  have hfC : ContDiff ℝ 2 fun x => (f x : ℂ) := Complex.ofRealCLM.contDiff.comp hf
  rw [re_weilPoleWeightFunctional_ofReal β _ hfC hf.continuous hfc]
  have hap : atomPairing (fun n => (ArithmeticFunction.vonMangoldt n : ℝ) -
      ArithmeticFunction.vonMangoldt n) (crossCorr f f) = 0 := by
    unfold atomPairing; simp
  have h0 : ∫ u, f u * Real.exp (-u / 2) = 0 := by
    have h1 := paperFT_ofRealFun_I_div_two f
    rw [hp] at h1
    exact_mod_cast h1.symm
  rw [hap, h0]
  ring

/-- **Without RH, `Λ` is Weil-positive on odd tests at no pole weight.** -/
theorem not_weilPositiveOddAt_vonMangoldt_of_not_riemannHypothesis (hRH : ¬ RiemannHypothesis)
    (β : ℝ) : ¬ WeilPositiveOddAt β fun n => (ArithmeticFunction.vonMangoldt n : ℝ) := by
  intro h
  obtain ⟨f, hf, hfc, hodd, hp, hneg⟩ := exists_odd_poleFree_negative_of_not_riemannHypothesis hRH
  have hpos := h (fun x => (f x : ℂ)) (Complex.ofRealCLM.contDiff.comp hf)
    (hfc.comp_left Complex.ofReal_zero) (fun x => by simp only [hodd, Complex.ofReal_neg])
  rw [re_weilPoleWeightFunctional_vonMangoldt_of_poleFree β hf hfc hp] at hpos
  linarith

/-- **Without RH, `Λ` is Weil-positive on even tests at no pole weight.** -/
theorem not_weilPositiveEvenAt_vonMangoldt_of_not_riemannHypothesis (hRH : ¬ RiemannHypothesis)
    (β : ℝ) :
    ¬ EvenSector.WeilPositiveEvenAt β fun n => (ArithmeticFunction.vonMangoldt n : ℝ) := by
  intro h
  obtain ⟨u, hu, hcpt, heven, hp, hneg⟩ :=
    exists_even_poleFree_negative_of_not_riemannHypothesis hRH
  have hpos := h (fun x => (u x : ℂ)) (Complex.ofRealCLM.contDiff.comp hu)
    (hcpt.comp_left Complex.ofReal_zero) (fun x => by simp only [heven])
  rw [re_weilPoleWeightFunctional_vonMangoldt_of_poleFree β hu hcpt hp] at hpos
  linarith

/-! ## The two windows -/

/-- **RH is odd Weil positivity of `Λ` at any pole weight `β ≤ 1`.** -/
theorem riemannHypothesis_iff_weilPositiveOddAt_vonMangoldt {β : ℝ} (hβ : β ≤ 1) :
    RiemannHypothesis ↔ WeilPositiveOddAt β fun n => (ArithmeticFunction.vonMangoldt n : ℝ) := by
  constructor
  · intro hRH
    exact weilPositiveOddAt_anti hβ (weilPositiveOddAt_one_iff.mpr
      (riemannHypothesis_iff_weilPositiveOdd_vonMangoldt.mp hRH))
  · intro h
    by_contra hRH
    exact not_weilPositiveOddAt_vonMangoldt_of_not_riemannHypothesis hRH β h

/-- **The odd window of `Λ` is `(−∞, 1]` exactly under RH.** -/
theorem riemannHypothesis_iff_forall_weilPositiveOddAt_vonMangoldt_iff :
    RiemannHypothesis ↔ ∀ β : ℝ,
      WeilPositiveOddAt β (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) ↔ β ≤ 1 := by
  constructor
  · intro hRH β
    refine ⟨fun h => ?_, fun hβ => (riemannHypothesis_iff_weilPositiveOddAt_vonMangoldt hβ).mp hRH⟩
    by_contra hβ
    exact not_weilPositiveOddAt_vonMangoldt_of_one_lt (not_le.mp hβ) h
  · intro h
    exact (riemannHypothesis_iff_weilPositiveOddAt_vonMangoldt le_rfl).mpr ((h 1).mpr le_rfl)

theorem one_le_of_weilPositiveEvenAt_vonMangoldt {β : ℝ}
    (h : EvenSector.WeilPositiveEvenAt β fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) :
    1 ≤ β :=
  EvenSector.one_le_of_primeBlindPositiveEvenAt
    (EvenSector.primeBlindPositiveEvenAt_of_weilPositiveEvenAt h)

/-- **The even window of `Λ` is `[1, ∞)` exactly under RH.** -/
theorem riemannHypothesis_iff_forall_weilPositiveEvenAt_vonMangoldt_iff :
    RiemannHypothesis ↔ ∀ β : ℝ,
      EvenSector.WeilPositiveEvenAt β (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) ↔
        1 ≤ β := by
  constructor
  · intro hRH β
    refine ⟨one_le_of_weilPositiveEvenAt_vonMangoldt, fun hβ =>
      EvenSector.weilPositiveEvenAt_mono hβ
        (EvenSector.weilPositiveEvenAt_one_iff.mpr ⟨hRH, fun _ _ => rfl⟩)⟩
  · intro h
    exact (EvenSector.weilPositiveEvenAt_one_iff.mp ((h 1).mpr le_rfl)).1

/-- **The parity windows meet only at pole weight `1`.**  Even and odd Weil positivity of `Λ` at
the same pole weight force that weight to be `1`, and RH. -/
theorem eq_one_of_weilPositiveEvenAt_of_weilPositiveOddAt {β : ℝ}
    (he : EvenSector.WeilPositiveEvenAt β fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
    (ho : WeilPositiveOddAt β fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) :
    β = 1 ∧ RiemannHypothesis := by
  have h1 := one_le_of_weilPositiveEvenAt_vonMangoldt he
  have h2 : β ≤ 1 := by
    by_contra hβ
    exact not_weilPositiveOddAt_vonMangoldt_of_one_lt (not_le.mp hβ) ho
  exact ⟨le_antisymm h2 h1, (riemannHypothesis_iff_weilPositiveOddAt_vonMangoldt h2).mpr ho⟩

end

end RHTower
