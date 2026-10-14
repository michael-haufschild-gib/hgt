import GaloisForLFunctions.RHTower.WeilMarkovOneBoundState
import GaloisForLFunctions.RHTower.WeilConditionalConstantSignRigidity
import GaloisForLFunctions.RHTower.RiemannAutocorrFourier
import GaloisForLFunctions.RHTower.WeilFullConeBochnerMeasure

/-!
# RH is positivity of the archimedean-minus-prime form on odd tests

Let `M(f) = Re[(1/2π) ∫ k̂ γ − Σ_{n ≥ 2} Λ(n) n^{−1/2}(k(log n) + k(−log n))]`, `k = f ⋆ f̃`, be the
Weil functional of `ζ` without its pole term (`markovEnergy`).

**Theorem** (`riemannHypothesis_iff_forall_odd_markovEnergy_nonneg`). RH holds if and only if
`M(f) ≥ 0` for every odd real `C²` compactly supported `f`.

There is no pole and no index in this statement. Together with `exists_markovEnergy_neg`, it
says that the single negative square of `M` lies in the even sector.

* Under RH, `W(f) ≥ 0`. For odd real `f`, `f̂(−i/2) = −f̂(i/2)` and `f̂(i/2)` is real, so the pole term is
  `−2 f̂(i/2)² ≤ 0` and `M(f) = W(f) − P(f) ≥ 0`.
* Without RH, take a smooth even real `u` with `û(±i/2) = 0` and `Re W(u, u) < 0`, and its odd
  shifts `O_h(x) = (u(x − h/2) − u(x + h/2))/2`. Each `O_h` is pole-free, so `M(O_h) = W(O_h)`. At a
  zero, `Ô_h = i sin(γh/2) û`, so `W(O_h) = Σ_ρ ¼(2 − e^{iγh} − e^{−iγh}) W_ρ(u)`. Integrating against
  Riemann's kernel `Φ > 0`, whose transform `Ξ` vanishes at every zero, kills the oscillating
  terms: `∫ W(O_h) Φ(h) dh = ½ (∫ Φ) W(u)`, which has negative real part. So some `O_h` has
  `M(O_h) < 0`.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate
open Zeta23

namespace RHTower

noncomputable section

/-! ## The pole term on odd tests -/

theorem paperFT_ofReal_neg_of_odd {f : ℝ → ℝ} (hodd : ∀ x, f (-x) = -f x) (z : ℂ) :
    paperFT (fun x => (f x : ℂ)) (-z) = -paperFT (fun x => (f x : ℂ)) z := by
  rw [← paperFT_comp_neg]
  have : (fun u => ((f (-u) : ℝ) : ℂ)) = fun u => (-1 : ℂ) * (f u : ℂ) := by
    funext u; rw [hodd]; push_cast; ring
  rw [this, paperFT_const_mul]
  ring

/-- **Under RH the archimedean-minus-prime form is nonnegative on odd tests.** -/
theorem odd_markovEnergy_nonneg_of_riemannHypothesis (hRH : RiemannHypothesis) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hodd : ∀ x, f (-x) = -f x) :
    0 ≤ markovEnergy (fun x => (f x : ℂ)) := by
  set F : ℝ → ℂ := fun x => (f x : ℂ) with hF
  have hFd : ContDiff ℝ 2 F := Complex.ofRealCLM.contDiff.comp hf
  have hFc : HasCompactSupport F := hfc.comp_left Complex.ofReal_zero
  have hW := (riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mp hRH) F hFd hFc
  rw [← zeta_W_eq_weilFullFunctional hFd hFc] at hW
  set r : ℝ := ∫ x, f x * Real.exp (-(x / 2)) with hr
  have h1 : paperFT F (I / 2) = (r : ℂ) := paperFT_ofReal_I_half_eq_integral f
  have h2 : paperFT F (-I / 2) = -(r : ℂ) := by
    rw [neg_div, hF, paperFT_ofReal_neg_of_odd hodd, ← hF, h1]
  have hpole : (weilPoleTerm (EF.weilTest F F)).re = -(2 * r ^ 2) := by
    rw [weilPoleTerm_weilTest_eq hFd.continuous hFc, h1, h2, map_neg, Complex.conj_ofReal]
    rw [show (r : ℂ) * -(r : ℂ) + -(r : ℂ) * (r : ℂ) = ((-(2 * r ^ 2) : ℝ) : ℂ) by push_cast; ring,
      Complex.ofReal_re]
  rw [markovEnergy_eq_W_sub hFd hFc, hpole]
  nlinarith [sq_nonneg r]

/-! ## Odd shifts -/

/-- The odd part of the translate of `u` by `h/2`: `O_h(x) = (u(x − h/2) − u(x + h/2))/2`. -/
def oddShift (u : ℝ → ℝ) (h x : ℝ) : ℝ := (u (x - h / 2) - u (x + h / 2)) / 2

theorem oddShift_neg {u : ℝ → ℝ} (heven : ∀ x, u (-x) = u x) (h x : ℝ) :
    oddShift u h (-x) = -oddShift u h x := by
  unfold oddShift
  rw [show -x - h / 2 = -(x + h / 2) by ring, show -x + h / 2 = -(x - h / 2) by ring, heven, heven]
  ring

theorem contDiff_oddShift {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u) (h : ℝ) :
    ContDiff ℝ 2 (oddShift u h) := by
  unfold oddShift
  exact ((hu.comp (contDiff_id.sub contDiff_const)).sub
    (hu.comp (contDiff_id.add contDiff_const))).div_const 2

theorem hasCompactSupport_oddShift {u : ℝ → ℝ} (hcpt : HasCompactSupport u) (h : ℝ) :
    HasCompactSupport (oddShift u h) := by
  have h1 : HasCompactSupport (fun x => u (x - h / 2)) :=
    hcpt.comp_homeomorph (Homeomorph.subRight (h / 2))
  have h2 : HasCompactSupport (fun x => u (x + h / 2)) :=
    hcpt.comp_homeomorph (Homeomorph.addRight (h / 2))
  have h3 := (h1.sub h2).comp_left (g := fun y : ℝ => y / 2) (by norm_num)
  convert h3 using 1
  funext x
  simp [oddShift, Function.comp]

/-- The transform of an odd shift: `Ô_h(z) = ((e^{izh/2} − e^{−izh/2})/2) û(z)`. -/
theorem paperFT_oddShift {u : ℝ → ℝ} (hu : Continuous u) (hcpt : HasCompactSupport u) (h : ℝ)
    (z : ℂ) :
    paperFT (fun x => (oddShift u h x : ℂ)) z =
      (cexp (I * z * (h / 2 : ℝ)) - cexp (I * z * (-(h / 2) : ℝ))) / 2 *
        paperFT (fun x => (u x : ℂ)) z := by
  set U : ℝ → ℂ := fun x => (u x : ℂ) with hU
  have hUc : Continuous U := Complex.continuous_ofReal.comp hu
  have hUs : HasCompactSupport U := hcpt.comp_left Complex.ofReal_zero
  have e : (fun x => (oddShift u h x : ℂ)) = fun x =>
      (1 / 2 : ℂ) * WeilSpectral.transl (h / 2) U x + (-1 / 2 : ℂ) *
        WeilSpectral.transl (-(h / 2)) U x := by
    funext x
    simp only [oddShift, WeilSpectral.transl, hU, sub_neg_eq_add]
    push_cast; ring
  have hT : ∀ y : ℝ, Integrable fun x : ℝ => WeilSpectral.transl y U x * cexp (I * z * x) := by
    intro y
    refine integrable_mul_cexp_of_compact (hUc.comp (continuous_id.sub continuous_const)) ?_ z
    exact hUs.comp_homeomorph (Homeomorph.subRight y)
  rw [e, paperFT_smul_add_smul _ _ z (hT _) (hT _), WeilSpectral.paperFT_transl,
    WeilSpectral.paperFT_transl]
  ring

/-- The odd-shift multiplier `s(z) = (e^{izh/2} − e^{−izh/2})/2`. -/
def oddShiftMult (h : ℝ) (z : ℂ) : ℂ :=
  (cexp (I * z * (h / 2 : ℝ)) - cexp (I * z * (-(h / 2) : ℝ))) / 2

theorem conj_oddShiftMult_conj (h : ℝ) (z : ℂ) :
    (starRingEnd ℂ) (oddShiftMult h ((starRingEnd ℂ) z)) = -oddShiftMult h z := by
  unfold oddShiftMult
  rw [map_div₀, map_sub, ← Complex.exp_conj, ← Complex.exp_conj, map_ofNat]
  simp only [map_mul, Complex.conj_I, Complex.conj_conj, Complex.conj_ofReal]
  rw [show -I * z * ((h / 2 : ℝ) : ℂ) = I * z * ((-(h / 2) : ℝ) : ℂ) by push_cast; ring,
    show -I * z * ((-(h / 2) : ℝ) : ℂ) = I * z * ((h / 2 : ℝ) : ℂ) by push_cast; ring]
  ring

theorem neg_oddShiftMult_sq (h : ℝ) (z : ℂ) :
    -oddShiftMult h z ^ 2 = (2 - cexp (I * z * h) - cexp (-(I * z * h))) / 4 := by
  unfold oddShiftMult
  set E := cexp (I * z * (h / 2 : ℝ))
  set F := cexp (I * z * (-(h / 2) : ℝ))
  have hEF : E * F = 1 := by
    rw [← Complex.exp_add, show I * z * ((h / 2 : ℝ) : ℂ) + I * z * ((-(h / 2) : ℝ) : ℂ) = 0 by
      push_cast; ring, Complex.exp_zero]
  have hE2 : cexp (I * z * h) = E ^ 2 := by
    rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have hF2 : cexp (-(I * z * h)) = F ^ 2 := by
    rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  rw [hE2, hF2]
  linear_combination (1 / 2 : ℂ) * hEF

/-- At a zero, `W_ρ(O_h) = ¼(2 − e^{iγh} − e^{−iγh}) W_ρ(u)`. -/
theorem Wsummand_oddShift {u : ℝ → ℝ} (hu : Continuous u) (hcpt : HasCompactSupport u) (h : ℝ)
    (ρ : ℂ) :
    zetaZeroConfig.Wsummand (fun x => (oddShift u h x : ℂ)) (fun x => (oddShift u h x : ℂ)) ρ =
      (2 - cexp (I * gammaOf ρ * h) - cexp (-(I * gammaOf ρ * h))) / 4 *
        zetaZeroConfig.Wsummand (fun x => (u x : ℂ)) (fun x => (u x : ℂ)) ρ := by
  have hP : ∀ z, paperFT (fun x => (oddShift u h x : ℂ)) z =
      oddShiftMult h z * paperFT (fun x => (u x : ℂ)) z := fun z => by
    rw [paperFT_oddShift hu hcpt h z]; rfl
  simp only [ZeroConfig.Wsummand, hP, map_mul, conj_oddShiftMult_conj]
  rw [← neg_oddShiftMult_sq]
  ring

/-! ## Averaging the odd shifts against Riemann's kernel -/

/-- `Φ̂` vanishes at the spectral point `γ_ρ` of every zero and at `−γ_ρ`. -/
theorem paperFT_riemannPhiKernel_gammaOf (ρ : zetaZeroConfig.carrier) :
    paperFT riemannPhiKernel (gammaOf ρ) = 0 ∧ paperFT riemannPhiKernel (-gammaOf ρ) = 0 := by
  have hmem : IsNontrivialZero (ρ : ℂ) := ρ.2
  have hpt : (1 / 2 : ℂ) + I * gammaOf (ρ : ℂ) = ρ := by
    rw [gammaOf, mul_div_cancel₀ _ I_ne_zero]; ring
  have h0 : paperFT riemannPhiKernel (gammaOf ρ) = 0 := by
    rw [paperFT_riemannPhiKernel, hpt]
    exact riemannPhiTransform_eq_zero_of_nontrivial hmem.1 hmem.2.1 hmem.2.2
  refine ⟨h0, ?_⟩
  rw [← paperFT_comp_neg]
  have : (fun u => riemannPhiKernel (-u)) = riemannPhiKernel := by
    funext u
    rw [riemannPhiKernel_eq_ofReal, riemannPhiKernel_eq_ofReal, WeilExcess.riemannKernelReal_neg]
  rw [this]
  exact h0

theorem abs_im_gammaOf_le (ρ : zetaZeroConfig.carrier) : |(gammaOf (ρ : ℂ)).im| ≤ 1 / 2 := by
  have hmem : IsNontrivialZero (ρ : ℂ) := ρ.2
  exact (WeilEF.abs_gammaOf_im_lt ⟨hmem.2.1, hmem.2.2⟩).le

theorem norm_cexp_I_mul_le {γ : ℂ} (hγ : |γ.im| ≤ 1 / 2) (h : ℝ) :
    ‖cexp (I * γ * h)‖ ≤ Real.exp (|h| / 2) ∧ ‖cexp (-(I * γ * h))‖ ≤ Real.exp (|h| / 2) := by
  have hre : (I * γ * (h : ℂ)).re = -(γ.im * h) := by
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_im]
    ring
  have hb : |γ.im * h| ≤ |h| / 2 := by
    rw [abs_mul]
    nlinarith [abs_nonneg h, abs_nonneg γ.im]
  constructor
  · rw [Complex.norm_exp, hre]
    exact Real.exp_le_exp.mpr (by linarith [neg_abs_le (γ.im * h)])
  · rw [Complex.norm_exp, Complex.neg_re, hre, neg_neg]
    exact Real.exp_le_exp.mpr (le_trans (le_abs_self _) hb)

/-- The averaging weight multiplier is bounded by `e^{|h|/2}` in the critical strip. -/
theorem norm_oddShiftWeight_le {γ : ℂ} (hγ : |γ.im| ≤ 1 / 2) (h : ℝ) :
    ‖(2 - cexp (I * γ * h) - cexp (-(I * γ * h))) / 4‖ ≤ Real.exp (|h| / 2) := by
  obtain ⟨e1, e2⟩ := norm_cexp_I_mul_le hγ h
  have h1 : 1 ≤ Real.exp (|h| / 2) := Real.one_le_exp (by positivity)
  rw [norm_div, show ‖(4 : ℂ)‖ = 4 by norm_num, div_le_iff₀ (by norm_num)]
  calc ‖2 - cexp (I * γ * h) - cexp (-(I * γ * h))‖
      ≤ ‖(2 : ℂ)‖ + ‖cexp (I * γ * h)‖ + ‖cexp (-(I * γ * h))‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        exact norm_sub_le _ _
    _ ≤ 2 + Real.exp (|h| / 2) + Real.exp (|h| / 2) := by
        rw [show ‖(2 : ℂ)‖ = 2 by norm_num]; linarith
    _ ≤ Real.exp (|h| / 2) * 4 := by linarith

/-- `‖Φ(h)‖ e^{|h|/2} ≤ C e^{−|h|/2}`. -/
theorem exists_riemannPhiKernel_weight_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℝ, ‖riemannPhiKernel h‖ * Real.exp (|h| / 2) ≤
      C * Real.exp (-(1 / 2 * |h|)) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_riemannPhiKernel_le_exp (B := 1) zero_le_one
  refine ⟨C, hC0, fun h => ?_⟩
  have := mul_le_mul_of_nonneg_right (hC h) (Real.exp_pos (|h| / 2)).le
  calc ‖riemannPhiKernel h‖ * Real.exp (|h| / 2)
      ≤ C * Real.exp (-(1 * |h|)) * Real.exp (|h| / 2) := this
    _ = C * Real.exp (-(1 / 2 * |h|)) := by
        rw [mul_assoc, ← Real.exp_add]; congr 2; ring

theorem summable_norm_of_zeroBound {x : zetaZeroConfig.carrier → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hx : ∀ ρ : zetaZeroConfig.carrier,
      ‖x ρ‖ ≤ (zetaZeroConfig.mult ρ : ℝ) * (C / (1 + |(ρ : ℂ).im|) ^ 2)) :
    Summable fun ρ => ‖x ρ‖ := by
  have hb : ∀ ρ : zetaZeroConfig.carrier, ‖x ρ‖ ≤
      (5 / 4) * C * ((zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf (ρ : ℂ)))) := by
    intro ρ
    have hq := one_div_one_add_abs_im_sq_le (zetaZeroConfig.strip _ ρ.2)
    have hm : (0 : ℝ) ≤ zetaZeroConfig.mult ρ := Nat.cast_nonneg _
    have h1 : C / (1 + |(ρ : ℂ).im|) ^ 2 ≤ (5 / 4) * C *
        (1 / (1 + Complex.normSq (gammaOf (ρ : ℂ)))) := by
      rw [div_eq_mul_one_div]
      calc C * (1 / (1 + |(ρ : ℂ).im|) ^ 2)
          ≤ C * ((5 / 4) * (1 / (1 + Complex.normSq (gammaOf (ρ : ℂ))))) :=
            mul_le_mul_of_nonneg_left hq hC
        _ = _ := by ring
    calc ‖x ρ‖ ≤ (zetaZeroConfig.mult ρ : ℝ) * (C / (1 + |(ρ : ℂ).im|) ^ 2) := hx ρ
      _ ≤ (zetaZeroConfig.mult ρ : ℝ) *
          ((5 / 4) * C * (1 / (1 + Complex.normSq (gammaOf (ρ : ℂ))))) :=
          mul_le_mul_of_nonneg_left h1 hm
      _ = _ := by ring
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb (summable_zeroSumZ.mul_left _)

/-- The zero summands of a real test are summable in norm. -/
theorem summable_norm_Wsummand_ofReal {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u)
    (hcpt : HasCompactSupport u) :
    Summable fun ρ : zetaZeroConfig.carrier =>
      ‖zetaZeroConfig.Wsummand (fun x => (u x : ℂ)) (fun x => (u x : ℂ)) ρ‖ := by
  refine summable_norm_of_zeroBound (sq_nonneg (testEnergy u)) fun ρ => ?_
  have h1 := (test_zero_bound hu hcpt ρ).1
  have h2 := (test_zero_bound hu hcpt ρ).2
  set D := 1 + |(ρ : ℂ).im|
  have hD0 : 0 < D := by positivity
  simp only [ZeroConfig.Wsummand]
  rw [norm_mul, norm_mul, Complex.norm_natCast, RCLike.norm_conj, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  rw [le_div_iff₀ (by positivity)]
  calc ‖paperFT (fun x => (u x : ℂ)) (gammaOf ↑ρ)‖ *
        ‖paperFT (fun x => (u x : ℂ)) ((starRingEnd ℂ) (gammaOf ↑ρ))‖ * D ^ 2
      = (D * ‖paperFT (fun x => (u x : ℂ)) (gammaOf ↑ρ)‖) *
          (D * ‖paperFT (fun x => (u x : ℂ)) ((starRingEnd ℂ) (gammaOf ↑ρ))‖) := by ring
    _ ≤ testEnergy u * testEnergy u := mul_le_mul h1 h2 (by positivity) (testEnergy_nonneg u)
    _ = testEnergy u ^ 2 := by ring

/-- **The averaging identity.** For a real `C²` compactly supported `u`,
`∫ W(O_h, O_h) Φ(h) dh = ½ (∫ Φ) W(u, u)`: the oscillating terms are `Φ̂(±γ_ρ) = 0`. -/
theorem integral_W_oddShift_mul_riemannPhiKernel {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u)
    (hcpt : HasCompactSupport u) :
    Integrable (fun h : ℝ => zetaZeroConfig.W (fun x => (oddShift u h x : ℂ))
        (fun x => (oddShift u h x : ℂ)) * riemannPhiKernel h) ∧
      ∫ h : ℝ, zetaZeroConfig.W (fun x => (oddShift u h x : ℂ)) (fun x => (oddShift u h x : ℂ)) *
          riemannPhiKernel h =
        (∫ h : ℝ, riemannPhiKernel h) / 2 *
          zetaZeroConfig.W (fun x => (u x : ℂ)) (fun x => (u x : ℂ)) := by
  haveI : Countable zetaZeroConfig.carrier := WeilConditional.countable_carrier.to_subtype
  set S : zetaZeroConfig.carrier → ℂ := fun ρ =>
    zetaZeroConfig.Wsummand (fun x => (u x : ℂ)) (fun x => (u x : ℂ)) ρ with hS
  set F : zetaZeroConfig.carrier → ℝ → ℂ := fun ρ h =>
    (2 - cexp (I * gammaOf (ρ : ℂ) * h) - cexp (-(I * gammaOf (ρ : ℂ) * h))) / 4 * S ρ *
      riemannPhiKernel h with hF
  have hSs : Summable fun ρ => ‖S ρ‖ := summable_norm_Wsummand_ofReal hu hcpt
  obtain ⟨C, hC0, hCb⟩ := exists_riemannPhiKernel_weight_bound
  have hK : Integrable fun h : ℝ => C * Real.exp (-(1 / 2 * |h|)) :=
    (integrable_exp_neg_mul_abs (by norm_num : (0 : ℝ) < 1 / 2)).const_mul C
  have hFb : ∀ ρ h, ‖F ρ h‖ ≤ ‖S ρ‖ * (C * Real.exp (-(1 / 2 * |h|))) := by
    intro ρ h
    have hw := norm_oddShiftWeight_le (abs_im_gammaOf_le ρ) h
    simp only [hF]
    rw [norm_mul, norm_mul]
    calc ‖(2 - cexp (I * gammaOf ↑ρ * ↑h) - cexp (-(I * gammaOf ↑ρ * ↑h))) / 4‖ * ‖S ρ‖ *
          ‖riemannPhiKernel h‖
        ≤ Real.exp (|h| / 2) * ‖S ρ‖ * ‖riemannPhiKernel h‖ := by gcongr
      _ = ‖S ρ‖ * (‖riemannPhiKernel h‖ * Real.exp (|h| / 2)) := by ring
      _ ≤ ‖S ρ‖ * (C * Real.exp (-(1 / 2 * |h|))) :=
          mul_le_mul_of_nonneg_left (hCb h) (norm_nonneg _)
  have hFc : ∀ ρ, Continuous (F ρ) := fun ρ => by
    simp only [hF]
    exact ((continuous_const.sub (by fun_prop)).sub (by fun_prop)).div_const _
      |>.mul continuous_const |>.mul continuous_riemannPhiKernel
  have hFi : ∀ ρ, Integrable (F ρ) := fun ρ =>
    (hK.const_mul ‖S ρ‖).mono' (hFc ρ).aestronglyMeasurable
      (Eventually.of_forall fun h => hFb ρ h)
  -- the pointwise expansion
  have hpt : ∀ h : ℝ, zetaZeroConfig.W (fun x => (oddShift u h x : ℂ))
      (fun x => (oddShift u h x : ℂ)) * riemannPhiKernel h = ∑' ρ, F ρ h := by
    intro h
    unfold ZeroConfig.W
    rw [← tsum_mul_right]
    refine tsum_congr fun ρ => ?_
    simp only [hF, hS]
    rw [Wsummand_oddShift hu.continuous hcpt h]
  -- the sum is continuous and dominated
  have hM : ∀ ρ h, ‖F ρ h‖ ≤ ‖S ρ‖ * C := fun ρ h =>
    (hFb ρ h).trans (mul_le_mul_of_nonneg_left (by
      have := Real.exp_le_one_iff.mpr (show -(1 / 2 * |h|) ≤ 0 by
        have := abs_nonneg h; linarith)
      nlinarith) (norm_nonneg _))
  have hcont : Continuous fun h => ∑' ρ, F ρ h :=
    continuous_tsum hFc (hSs.mul_right C) hM
  have hint : Integrable fun h => ∑' ρ, F ρ h := by
    refine (hK.const_mul (∑' ρ, ‖S ρ‖)).mono' hcont.aestronglyMeasurable
      (Eventually.of_forall fun h => ?_)
    have hs : Summable fun ρ => ‖F ρ h‖ :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ρ => hFb ρ h)
        (hSs.mul_right _)
    calc ‖∑' ρ, F ρ h‖ ≤ ∑' ρ, ‖F ρ h‖ := norm_tsum_le_tsum_norm hs
      _ ≤ ∑' ρ, ‖S ρ‖ * (C * Real.exp (-(1 / 2 * |h|))) :=
          Summable.tsum_le_tsum (fun ρ => hFb ρ h) hs (hSs.mul_right _)
      _ = (∑' ρ, ‖S ρ‖) * (C * Real.exp (-(1 / 2 * |h|))) := tsum_mul_right
  -- each term integrates to `S_ρ (∫Φ)/2`
  have hΦi : Integrable riemannPhiKernel :=
    hK.mono' continuous_riemannPhiKernel.aestronglyMeasurable (Eventually.of_forall fun h => by
      have := hCb h
      have he : 1 ≤ Real.exp (|h| / 2) := Real.one_le_exp (by positivity)
      nlinarith [norm_nonneg (riemannPhiKernel h)])
  have hEi : ∀ ρ : zetaZeroConfig.carrier, ∀ s : ℂ, (s = gammaOf (ρ : ℂ) ∨ s = -gammaOf (ρ : ℂ)) →
      Integrable fun h : ℝ => riemannPhiKernel h * cexp (I * s * h) := by
    intro ρ s hs
    refine hK.mono' (continuous_riemannPhiKernel.mul (by fun_prop)).aestronglyMeasurable
      (Eventually.of_forall fun h => ?_)
    obtain ⟨e1, e2⟩ := norm_cexp_I_mul_le (abs_im_gammaOf_le ρ) h
    rw [norm_mul]
    have he : ‖cexp (I * s * h)‖ ≤ Real.exp (|h| / 2) := by
      rcases hs with rfl | rfl
      · exact e1
      · rw [show I * -gammaOf (ρ : ℂ) * (h : ℂ) = -(I * gammaOf (ρ : ℂ) * h) by ring]; exact e2
    calc ‖riemannPhiKernel h‖ * ‖cexp (I * s * h)‖ ≤ ‖riemannPhiKernel h‖ * Real.exp (|h| / 2) :=
          mul_le_mul_of_nonneg_left he (norm_nonneg _)
      _ ≤ C * Real.exp (-(1 / 2 * |h|)) := hCb h
  have hterm : ∀ ρ : zetaZeroConfig.carrier,
      ∫ h, F ρ h = S ρ * ((∫ h : ℝ, riemannPhiKernel h) / 2) := by
    intro ρ
    obtain ⟨h0, h1⟩ := paperFT_riemannPhiKernel_gammaOf ρ
    have i1 := hEi ρ _ (Or.inl rfl)
    have i2 := hEi ρ _ (Or.inr rfl)
    have e : (fun h => F ρ h) = fun h => S ρ / 4 * (2 * riemannPhiKernel h -
        riemannPhiKernel h * cexp (I * gammaOf (ρ : ℂ) * h) -
        riemannPhiKernel h * cexp (I * (-gammaOf (ρ : ℂ)) * h)) := by
      funext h
      simp only [hF]
      rw [show I * -gammaOf (ρ : ℂ) * (h : ℂ) = -(I * gammaOf (ρ : ℂ) * h) by ring]
      ring
    have j1 : Integrable fun h : ℝ => 2 * riemannPhiKernel h := hΦi.const_mul 2
    have j2 : Integrable fun h : ℝ => 2 * riemannPhiKernel h -
        riemannPhiKernel h * cexp (I * gammaOf (ρ : ℂ) * h) := j1.sub i1
    rw [e, integral_const_mul, integral_sub j2 i2, integral_sub j1 i1, integral_const_mul]
    have p1 : ∫ h : ℝ, riemannPhiKernel h * cexp (I * gammaOf (ρ : ℂ) * h) = 0 := h0
    have p2 : ∫ h : ℝ, riemannPhiKernel h * cexp (I * (-gammaOf (ρ : ℂ)) * h) = 0 := h1
    rw [p1, p2]
    ring
  refine ⟨?_, ?_⟩
  · exact hint.congr (Eventually.of_forall fun h => (hpt h).symm)
  · rw [show (fun h : ℝ => zetaZeroConfig.W (fun x => (oddShift u h x : ℂ))
        (fun x => (oddShift u h x : ℂ)) * riemannPhiKernel h) = fun h => ∑' ρ, F ρ h from
        funext hpt]
    rw [← integral_tsum_of_summable_integral_norm hFi]
    · rw [tsum_congr hterm, tsum_mul_right]
      unfold ZeroConfig.W
      ring
    · refine Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _)
        (fun ρ => ?_) ((hSs.mul_right (∫ h, C * Real.exp (-(1 / 2 * |h|)))))
      calc ∫ h, ‖F ρ h‖ ≤ ∫ h, ‖S ρ‖ * (C * Real.exp (-(1 / 2 * |h|))) :=
            integral_mono (hFi ρ).norm (hK.const_mul _) (fun h => hFb ρ h)
        _ = ‖S ρ‖ * ∫ h, C * Real.exp (-(1 / 2 * |h|)) := integral_const_mul _ _

/-! ## The equivalence -/

theorem integral_riemannKernelReal_pos : 0 < ∫ x, riemannKernelReal x := by
  rw [integral_pos_iff_support_of_nonneg (fun x => (riemannKernelReal_pos x).le)
    WeilExcess.integrable_riemannKernelReal]
  have : Function.support riemannKernelReal = Set.univ :=
    Set.eq_univ_of_forall fun x => (riemannKernelReal_pos x).ne'
  rw [this, Real.volume_univ]
  exact ENNReal.zero_lt_top

/-- **Without RH some odd test has negative archimedean-minus-prime energy**: an odd shift of a
pole-free even test of negative Weil energy. -/
theorem exists_odd_markovEnergy_neg_of_not_riemannHypothesis (hRH : ¬ RiemannHypothesis) :
    ∃ f : ℝ → ℝ, ContDiff ℝ 2 f ∧ HasCompactSupport f ∧ (∀ x, f (-x) = -f x) ∧
      markovEnergy (fun x => (f x : ℂ)) < 0 := by
  obtain ⟨u, hu, hcpt, heven, hp, hneg⟩ :=
    exists_even_poleFree_negative_of_not_riemannHypothesis hRH
  have hp' : paperFT (fun x => (u x : ℂ)) (-I / 2) = 0 := by
    rw [neg_div, paperFT_ofReal_neg_of_even heven]; exact hp
  have hmarkov : ∀ h : ℝ, markovEnergy (fun x => (oddShift u h x : ℂ)) =
      (zetaZeroConfig.W (fun x => (oddShift u h x : ℂ)) (fun x => (oddShift u h x : ℂ))).re := by
    intro h
    have hd : ContDiff ℝ 2 fun x => (oddShift u h x : ℂ) :=
      Complex.ofRealCLM.contDiff.comp (contDiff_oddShift hu h)
    have hc : HasCompactSupport fun x => (oddShift u h x : ℂ) :=
      (hasCompactSupport_oddShift hcpt h).comp_left Complex.ofReal_zero
    rw [markovEnergy_eq_W_sub hd hc, weilPoleTerm_weilTest_eq hd.continuous hc,
      paperFT_oddShift hu.continuous hcpt, paperFT_oddShift hu.continuous hcpt, hp, hp']
    simp
  by_contra hcon
  push Not at hcon
  have hall : ∀ h : ℝ, 0 ≤ (zetaZeroConfig.W (fun x => (oddShift u h x : ℂ))
      (fun x => (oddShift u h x : ℂ))).re := fun h => by
    rw [← hmarkov]
    exact hcon _ (contDiff_oddShift hu h) (hasCompactSupport_oddShift hcpt h) (oddShift_neg heven h)
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
  have : RCLike.re (((∫ h, riemannKernelReal h : ℝ) : ℂ) / 2 *
      zetaZeroConfig.W (fun x => (u x : ℂ)) (fun x => (u x : ℂ))) =
      (∫ h, riemannKernelReal h) / 2 * (zetaZeroConfig.W (fun x => (u x : ℂ))
        (fun x => (u x : ℂ))).re := by
    show (((∫ h, riemannKernelReal h : ℝ) : ℂ) / 2 * _).re = _
    rw [show ((∫ h, riemannKernelReal h : ℝ) : ℂ) / 2 = (((∫ h, riemannKernelReal h) / 2 : ℝ) : ℂ) by
      push_cast; ring, Complex.re_ofReal_mul]
  rw [this] at hnn
  have : (∫ h, riemannKernelReal h) / 2 * (zetaZeroConfig.W (fun x => (u x : ℂ))
      (fun x => (u x : ℂ))).re < 0 := mul_neg_of_pos_of_neg (by positivity) hneg
  linarith

/-- **RH is positivity of the archimedean-minus-prime form on odd tests.** -/
theorem riemannHypothesis_iff_forall_odd_markovEnergy_nonneg :
    RiemannHypothesis ↔ ∀ f : ℝ → ℝ, ContDiff ℝ 2 f → HasCompactSupport f →
      (∀ x, f (-x) = -f x) → 0 ≤ markovEnergy (fun x => (f x : ℂ)) := by
  constructor
  · intro hRH f hf hfc hodd
    exact odd_markovEnergy_nonneg_of_riemannHypothesis hRH hf hfc hodd
  · intro h
    by_contra hRH
    obtain ⟨f, hf, hfc, hodd, hneg⟩ := exists_odd_markovEnergy_neg_of_not_riemannHypothesis hRH
    exact absurd (h f hf hfc hodd) (not_le.mpr hneg)

end

end RHTower
