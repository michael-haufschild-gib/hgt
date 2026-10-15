import GaloisForLFunctions.RHTower.WeilFullConeMinorantRigidity
import GaloisForLFunctions.RHTower.WeilMarkovOddPositivity

/-!
# Odd Weil positivity admits no minorant of `Λ` other than `Λ`

`WeilPositiveOdd lam` asks for nonnegativity of the full Weil functional (pole weight `1`,
`weilFullFunctional`) on the autocorrelations of odd `C²` compactly supported tests.  Odd tests have
`f̂(0) = 0`, so the odd functional does not see the value of the spectral side at `r = 0`; in
particular every system that is Weil-positive modulo constants (`WeilPositiveModConst`, an
arbitrary multiple of `|f̂(0)|²` added) is odd Weil-positive.

**Theorem** (`eq_vonMangoldt_of_weilPositiveOdd_of_le`, unconditional).  If `lam` is odd
Weil-positive and `lam(n) ≤ Λ(n)` for all `n ≥ 2`, then `lam(n) = Λ(n)` for all `n ≥ 2`.  No sign,
growth or summability condition on `lam` is assumed.

**Corollaries.**
* `riemannHypothesis_iff_weilPositiveOdd_vonMangoldt`: RH holds iff `Λ` is odd Weil-positive.
* `riemannHypothesis_iff_exists_weilPositiveOdd_le`: RH holds iff some odd Weil-positive
  `lam ≤ Λ` exists; it then equals `Λ`.
* `eq_vonMangoldt_of_weilPositiveModConst_of_le` and
  `riemannHypothesis_iff_exists_weilPositiveModConst_le`: the same statements for Weil positivity
  modulo constants.

Proof.  The log-shift difference `f = Φχ_L − Φχ_L(· − c)` detects every coefficient deficit below
`Λ` (`weilLogShiftMinorantFiber_iff`).  Since `Φχ_L` is even, its translate
`f(· + c/2) = Φχ_L(· + c/2) − Φχ_L(· − c/2)` is odd (`oddLogShiftRiemannDifference_neg`), and
translation does not change the autocorrelation `f ⋆ f̃` (`weilTest_comp_add_const`).  So odd
positivity already gives nonnegativity on the whole log-shift family.  For the corollaries: on odd
real tests the pole term is `−2 f̂(i/2)² ≤ 0`, so odd Weil positivity of `Λ` gives nonnegativity of
the pole-free form on odd tests, which is RH
(`riemannHypothesis_iff_forall_odd_markovEnergy_nonneg`).
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate
open Zeta23

namespace RHTower

noncomputable section

/-! ## The odd and the modulo-constants cones -/

/-- Weil positivity with the pole term on the autocorrelations of odd tests. -/
def WeilPositiveOdd (lam : ℕ → ℝ) : Prop :=
  ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f → (∀ x, f (-x) = -f x) →
    0 ≤ (weilFullFunctional lam (EF.weilTest f f)).re

/-- Weil positivity modulo constants: the full Weil functional plus some multiple of `|f̂(0)|²`
is nonnegative on every autocorrelation. -/
def WeilPositiveModConst (lam : ℕ → ℝ) : Prop :=
  ∃ κ : ℝ, ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f →
    0 ≤ (weilFullFunctional lam (EF.weilTest f f)).re + κ * ‖paperFT f 0‖ ^ 2

theorem weilPositiveOdd_of_weilPositiveFull {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    WeilPositiveOdd lam :=
  fun f hf hfc _ => hW f hf hfc

/-- An odd test has `f̂(0) = 0`. -/
theorem paperFT_zero_of_odd {f : ℝ → ℂ} (hodd : ∀ x, f (-x) = -f x) : paperFT f 0 = 0 := by
  have h := paperFT_comp_neg f 0
  rw [neg_zero] at h
  have e : (fun u => f (-u)) = fun u => (-1 : ℂ) * f u := by
    funext u; rw [hodd]; ring
  rw [e, paperFT_const_mul] at h
  linear_combination -h / 2

theorem weilPositiveOdd_of_weilPositiveModConst {lam : ℕ → ℝ} (hW : WeilPositiveModConst lam) :
    WeilPositiveOdd lam := by
  obtain ⟨κ, hκ⟩ := hW
  intro f hf hfc hodd
  have h := hκ f hf hfc
  rwa [paperFT_zero_of_odd hodd, norm_zero, sq, mul_zero, mul_zero, add_zero] at h

/-! ## Translation invariance of the autocorrelation -/

/-- Translating a test does not change its autocorrelation. -/
theorem weilTest_comp_add_const (f : ℝ → ℂ) (a : ℝ) :
    EF.weilTest (fun t => f (t + a)) (fun t => f (t + a)) = EF.weilTest f f := by
  funext x
  simp only [EF.weilTest, EF.tilde, convolution_def, ContinuousLinearMap.mul_apply']
  rw [← integral_add_right_eq_self (μ := volume) (fun t => f t * conj (f (-(x - t)))) a]
  congr 1
  funext t
  rw [show -(x - t) + a = -(x - (t + a)) by ring]

/-! ## The odd log-shift test -/

/-- The odd log-shift difference `Φχ_L(· + c/2) − Φχ_L(· − c/2)`, the translate by `c/2` of
`logShiftRiemannDifference`. -/
def oddLogShiftRiemannDifference (L c : ℝ) (u : ℝ) : ℂ :=
  logShiftRiemannDifference L c (u + c / 2)

theorem oddLogShiftRiemannDifference_neg (L c u : ℝ) :
    oddLogShiftRiemannDifference L c (-u) = -oddLogShiftRiemannDifference L c u := by
  simp only [oddLogShiftRiemannDifference, logShiftRiemannDifference, truncatedRiemannKernel_eq]
  rw [show -u + c / 2 = -(u - c / 2) by ring, show -(u - c / 2) - c = -(u + c / 2) by ring,
    truncatedRiemannKernelReal_neg, truncatedRiemannKernelReal_neg,
    show u + c / 2 - c = u - c / 2 by ring]
  ring

theorem contDiff_oddLogShiftRiemannDifference (L c : ℝ) :
    ContDiff ℝ 2 (oddLogShiftRiemannDifference L c) :=
  (contDiff_logShiftRiemannDifference L c).comp (contDiff_id.add contDiff_const)

theorem hasCompactSupport_oddLogShiftRiemannDifference (L c : ℝ) :
    HasCompactSupport (oddLogShiftRiemannDifference L c) :=
  (hasCompactSupport_logShiftRiemannDifference L c).comp_homeomorph (Homeomorph.addRight (c / 2))

theorem weilTest_oddLogShiftRiemannDifference (L c : ℝ) :
    EF.weilTest (oddLogShiftRiemannDifference L c) (oddLogShiftRiemannDifference L c) =
      EF.weilTest (logShiftRiemannDifference L c) (logShiftRiemannDifference L c) :=
  weilTest_comp_add_const _ _

/-- Odd Weil positivity gives nonnegativity on the integer-window log-shift family. -/
theorem weilLogShiftTestsPositive_of_weilPositiveOdd {lam : ℕ → ℝ} (hW : WeilPositiveOdd lam) :
    WeilLogShiftTestsPositive lam := by
  intro windowIndex m _ _
  have h := hW (oddLogShiftRiemannDifference windowIndex (Real.log m))
    (contDiff_oddLogShiftRiemannDifference _ _) (hasCompactSupport_oddLogShiftRiemannDifference _ _)
    (oddLogShiftRiemannDifference_neg _ _)
  rwa [weilTest_oddLogShiftRiemannDifference] at h

/-! ## Order rigidity from below -/

/-- **Odd Weil positivity admits no minorant of `Λ` other than `Λ`.** -/
theorem eq_vonMangoldt_of_weilPositiveOdd_of_le {lam : ℕ → ℝ} (hW : WeilPositiveOdd lam)
    (hle : ∀ n, 2 ≤ n → lam n ≤ (ArithmeticFunction.vonMangoldt n : ℝ)) :
    ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n :=
  ((weilLogShiftMinorantFiber_iff lam).mp
    ⟨hle, weilLogShiftTestsPositive_of_weilPositiveOdd hW⟩).1

/-- Under odd Weil positivity of `Λ`, the pole-free form is nonnegative on odd real tests. -/
theorem odd_markovEnergy_nonneg_of_weilPositiveOdd
    (hW : WeilPositiveOdd fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hodd : ∀ x, f (-x) = -f x) :
    0 ≤ markovEnergy (fun x => (f x : ℂ)) := by
  set F : ℝ → ℂ := fun x => (f x : ℂ) with hF
  have hFd : ContDiff ℝ 2 F := Complex.ofRealCLM.contDiff.comp hf
  have hFc : HasCompactSupport F := hfc.comp_left Complex.ofReal_zero
  have hFo : ∀ x, F (-x) = -F x := fun x => by simp only [hF, hodd, Complex.ofReal_neg]
  have hWF := hW F hFd hFc hFo
  set r : ℝ := ∫ x, f x * Real.exp (-(x / 2)) with hr
  have h1 : paperFT F (I / 2) = (r : ℂ) := paperFT_ofReal_I_half_eq_integral f
  have h2 : paperFT F (-I / 2) = -(r : ℂ) := by
    rw [neg_div, hF, paperFT_ofReal_neg_of_odd hodd, ← hF, h1]
  have hpole : (weilPoleTerm (EF.weilTest F F)).re = -(2 * r ^ 2) := by
    rw [weilPoleTerm_weilTest_eq hFd.continuous hFc, h1, h2, map_neg, Complex.conj_ofReal]
    rw [show (r : ℂ) * -(r : ℂ) + -(r : ℂ) * (r : ℂ) = ((-(2 * r ^ 2) : ℝ) : ℂ) by push_cast; ring,
      Complex.ofReal_re]
  have hM : markovEnergy F = (weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
      (EF.weilTest F F)).re - (weilPoleTerm (EF.weilTest F F)).re := by
    unfold markovEnergy
    rw [Complex.sub_re]
  rw [hM, hpole]
  nlinarith [sq_nonneg r]

/-- **RH is odd Weil positivity of `Λ`.** -/
theorem riemannHypothesis_iff_weilPositiveOdd_vonMangoldt :
    RiemannHypothesis ↔ WeilPositiveOdd fun n => (ArithmeticFunction.vonMangoldt n : ℝ) :=
  ⟨fun hRH => weilPositiveOdd_of_weilPositiveFull
      (riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mp hRH),
    fun hW => riemannHypothesis_iff_forall_odd_markovEnergy_nonneg.mpr fun _ hf hfc hodd =>
      odd_markovEnergy_nonneg_of_weilPositiveOdd hW hf hfc hodd⟩

/-- **RH is the existence of an odd Weil-positive minorant of `Λ`.** Such a minorant equals `Λ`. -/
theorem riemannHypothesis_iff_exists_weilPositiveOdd_le :
    RiemannHypothesis ↔ ∃ lam : ℕ → ℝ, WeilPositiveOdd lam ∧
      ∀ n, 2 ≤ n → lam n ≤ (ArithmeticFunction.vonMangoldt n : ℝ) := by
  constructor
  · intro hRH
    exact ⟨_, riemannHypothesis_iff_weilPositiveOdd_vonMangoldt.mp hRH, fun _ _ => le_rfl⟩
  · rintro ⟨lam, hW, hle⟩
    have h := eq_vonMangoldt_of_weilPositiveOdd_of_le hW hle
    refine riemannHypothesis_iff_weilPositiveOdd_vonMangoldt.mpr fun f hf hfc hodd => ?_
    rw [weilFullFunctional_congr (lam' := lam) (fun n hn => (h n hn).symm)]
    exact hW f hf hfc hodd

/-- **Weil positivity modulo constants admits no minorant of `Λ` other than `Λ`.** -/
theorem eq_vonMangoldt_of_weilPositiveModConst_of_le {lam : ℕ → ℝ}
    (hW : WeilPositiveModConst lam)
    (hle : ∀ n, 2 ≤ n → lam n ≤ (ArithmeticFunction.vonMangoldt n : ℝ)) :
    ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n :=
  eq_vonMangoldt_of_weilPositiveOdd_of_le (weilPositiveOdd_of_weilPositiveModConst hW) hle

/-- **RH is the existence of a minorant of `Λ` that is Weil-positive modulo constants.** -/
theorem riemannHypothesis_iff_exists_weilPositiveModConst_le :
    RiemannHypothesis ↔ ∃ lam : ℕ → ℝ, WeilPositiveModConst lam ∧
      ∀ n, 2 ≤ n → lam n ≤ (ArithmeticFunction.vonMangoldt n : ℝ) := by
  constructor
  · intro hRH
    refine ⟨_, ⟨0, fun f hf hfc => ?_⟩, fun _ _ => le_rfl⟩
    rw [zero_mul, add_zero]
    exact riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mp hRH f hf hfc
  · rintro ⟨lam, hW, hle⟩
    exact riemannHypothesis_iff_exists_weilPositiveOdd_le.mpr
      ⟨lam, weilPositiveOdd_of_weilPositiveModConst hW, hle⟩

end

end RHTower
