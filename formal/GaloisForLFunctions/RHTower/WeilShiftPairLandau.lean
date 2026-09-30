import GaloisForLFunctions.RHTower.WeilFullConeCompactness
import GaloisForLFunctions.RHTower.WeilLagFunctionOneSided
import GaloisForLFunctions.RHTower.VisibleCoprimeZetaZeroJet
import GaloisForLFunctions.RHTower.LandauSingularAtAbscissa
import GaloisForLFunctions.RHTower.NymanBeurlingCriterion

/-!
# Shift-pair Weil positivity of `Λ` and Landau's theorem

Fix a real, nonnegative `C²` bump `g` supported in `[−¼, ¼]`, with autocorrelation `ρ` and
Laplace transform `ρ̃(z) = ∫ ρ(v) e^{zv} dv`, and put `P₊P₋ = ∫ g e^{−u/2} · ∫ g e^{u/2}`.

**Theorem** (`autoLaplace_eq_zero_of_shiftPair_nonneg`). If the Weil functional of `Λ` is
nonnegative on every shift pair `g + g(· − L)`, `L > 0`, then `ρ̃(ρ − ½) = 0` for every zero `ρ` of
`ζ` with `Re ρ > ½`.

**Criterion** (`riemannHypothesis_iff_dilatedShiftPair_nonneg`). RH holds iff the Weil functional
of `Λ` is nonnegative on `g_λ + g_λ(· − L)` for all `½ ≤ λ ≤ 1`, `L > 0`, where `g_λ(u) = g(u/λ)`
and `∫ g ≠ 0`. Only these tests are needed out of the full Weil cone of test functions.

**Proof.**
- **Density.** Positivity bounds the smoothed prime window `S(L) = Σ Λ(n)(ρ(log n − L) +
  ρ(log n + L))/√n` from above by `M(L) = P₊P₋(e^{L/2} + e^{−L/2}) + C`
  (`primeWindow_le_of_shiftPair`). So `M − S` is a nonnegative density on `(0, ∞)`.
- **Laplace transform.** For real `σ > ½`, Tonelli gives `∫ S e^{−σL} = ρ̃(σ) Σ Λ(n) n^{−½−σ}`
  (`integral_primeWindow_mul_exp`), so the transform of `M − S` is
  `P₊P₋/(σ − ½) + P₊P₋/(σ + ½) + C/σ + ρ̃(σ) ζ'/ζ(σ + ½)`. With `ζ_u(s) = (s − 1)ζ(s)` and
  `ρ̃(½) = P₊P₋` the pole at `½` cancels, leaving `shiftContinuation`, analytic at every real
  `z > 0` because `ζ_u` has no positive real zero.
- **Landau.** The abscissa of the measure is therefore `0` (`abscissa_shiftMeasure_eq_zero`).
- **Residue.** On `Re z > 0` the transform is analytic, so
  `ζ_u(z + ½)(transform − analytic terms) − ρ̃(z) ζ_u'(z + ½)` vanishes identically. At a zero
  `ρ` of multiplicity `m`, multiplying by `z − (ρ − ½)` and letting `z → ρ − ½` gives
  `m ρ̃(ρ − ½) = 0`.
- **Dilations.** `ρ̃_{g_λ}(z) = λ² ρ̃_g(λz)`, so an off-line zero makes `ρ̃_g` vanish on the segment
  `[½, 1](ρ − ½)`, hence everywhere; but `ρ̃_g(0) = (∫ g)² ≠ 0`.
-/

open Complex MeasureTheory Filter Topology Set Finsupp
open scoped Real ComplexConjugate ContDiff ENNReal
open Zeta23 GaloisForLFunctions.RHTower

namespace RHTower.WeilOneSided

noncomputable section

variable {g : ℝ → ℝ}

/-! ## The shift-pair upper bound -/

/-- The product `P₊P₋ = ∫ g e^{−u/2} · ∫ g e^{u/2}`. -/
def poleConst (g : ℝ → ℝ) : ℝ :=
  (∫ u, g u * Real.exp (-u / 2)) * (∫ u, g u * Real.exp (u / 2))

/-- The archimedean constant `∫ ‖ρ̂ μ‖`. -/
def archConst (g : ℝ → ℝ) : ℝ :=
  ∫ τ : ℝ, ‖paperFT (EF.weilTest (liftC g) (liftC g)) τ * (mu τ : ℂ)‖

/-- **Shift-pair positivity bounds the prime window from above.** -/
theorem windowSum_le_of_shiftPair (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hsupp : ∀ u, 1 / 4 < |u| → g u = 0) {lam : ℕ → ℝ} {L : ℝ}
    (h0 : 0 ≤ (weilFullFunctional lam (EF.weilTest (shiftPair g 1 L) (shiftPair g 1 L))).re) :
    windowSum hg hgc hsupp lam L ≤
      poleConst g * (Real.exp (L / 2) + Real.exp (-L / 2)) + 2 * poleConst g +
        2 * archConst g := by
  have e := re_weilFullFunctional_eq lam (shiftPairFn hg hgc 1 L)
  change (weilFullFunctional lam (EF.weilTest (shiftPair g 1 L) (shiftPair g 1 L))).re =
    weilArchRe (EF.weilTest (shiftPair g 1 L) (shiftPair g 1 L)) -
      linearCombination ℝ (fun j : LogIndex => lam j) (logVector (shiftPairFn hg hgc 1 L)) at e
  rw [e, logVector_shiftPairFn hg hgc hsupp, map_smul, smul_eq_mul, weilArchRe,
    Complex.add_re, pole_shiftPair hg.continuous hgc, Complex.ofReal_re] at h0
  have ha := (abs_le.mp (abs_arch_shiftPair_le hg hgc (σ := 1) (by norm_num) L)).2
  have hab : Real.exp (-L / 2) * Real.exp (L / 2) = 1 := by
    rw [← Real.exp_add, show -L / 2 + L / 2 = 0 by ring, Real.exp_zero]
  have hprod : poleConst g * ((1 + 1 * Real.exp (-L / 2)) * (1 + 1 * Real.exp (L / 2))) =
      poleConst g * (Real.exp (L / 2) + Real.exp (-L / 2)) + 2 * poleConst g := by
    linear_combination poleConst g * hab
  unfold windowSum
  unfold poleConst at hprod ⊢
  unfold archConst
  nlinarith [hprod]

/-! ## The prime window as a series -/

/-- The smoothed prime window `S(L) = Σ_{n≥2} Λ(n)(ρ(log n − L) + ρ(log n + L))/√n`. -/
def primeWindow (g : ℝ → ℝ) (L : ℝ) : ℝ :=
  ∑' n : ℕ, (if 2 ≤ n then (ArithmeticFunction.vonMangoldt n : ℝ) else 0) * windowValue g L n

theorem windowSum_vonMangoldt_eq (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hsupp : ∀ u, 1 / 4 < |u| → g u = 0) (L : ℝ) :
    windowSum hg hgc hsupp (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) L =
      primeWindow g L := by
  classical
  set W := windowVector hg hgc hsupp L with hW
  have hWv : ∀ j : LogIndex, W j = windowValue g L j := fun j => by
    simp [hW, windowVector, Finsupp.ofSupportFinite_coe]
  unfold windowSum primeWindow
  rw [← hW, linearCombination_apply, Finsupp.sum,
    tsum_eq_sum (s := W.support.map ⟨Subtype.val, Subtype.val_injective⟩), Finset.sum_map]
  · refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Function.Embedding.coeFn_mk, if_pos j.2, hWv, smul_eq_mul, mul_comm]
  · intro n hn
    by_cases h2 : 2 ≤ n
    · have : W ⟨n, h2⟩ = 0 := by
        by_contra hne
        exact hn (Finset.mem_map.mpr ⟨⟨n, h2⟩, Finsupp.mem_support_iff.mpr hne, rfl⟩)
      rw [hWv] at this
      simp [this]
    · simp [h2]

theorem autoCorr_nonneg (hg0 : ∀ u, 0 ≤ g u) (x : ℝ) : 0 ≤ autoCorr g x :=
  integral_nonneg fun t => mul_nonneg (hg0 t) (hg0 _)

theorem windowValue_nonneg (hg0 : ∀ u, 0 ≤ g u) (L : ℝ) (n : ℕ) : 0 ≤ windowValue g L n :=
  div_nonneg (add_nonneg (autoCorr_nonneg hg0 _) (autoCorr_nonneg hg0 _)) (Real.sqrt_nonneg _)

theorem primeWindow_term_nonneg (hg0 : ∀ u, 0 ≤ g u) (L : ℝ) (n : ℕ) :
    0 ≤ (if 2 ≤ n then (ArithmeticFunction.vonMangoldt n : ℝ) else 0) * windowValue g L n := by
  refine mul_nonneg ?_ (windowValue_nonneg hg0 L n)
  split_ifs
  · exact ArithmeticFunction.vonMangoldt_nonneg
  · exact le_rfl

/-! ## The autocorrelation and its Laplace transform -/

theorem autoCorr_eq_re (g : ℝ → ℝ) (x : ℝ) :
    autoCorr g x = (EF.weilTest (liftC g) (liftC g) x).re := by
  rw [weilTest_liftC, Complex.ofReal_re]

theorem contDiff_autoCorr (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) :
    ContDiff ℝ 2 (autoCorr g) := by
  have h := EF.weilTest_contDiff (contDiff_liftC hg) (contDiff_liftC hg).continuous
    (hasCompactSupport_liftC hgc)
  have e : autoCorr g = fun x => (EF.weilTest (liftC g) (liftC g) x).re :=
    funext (autoCorr_eq_re g)
  rw [e]
  exact reCLM.contDiff.comp h

theorem hasCompactSupport_autoCorr (hsupp : ∀ u, 1 / 4 < |u| → g u = 0) :
    HasCompactSupport (autoCorr g) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := -(1 / 2)) (b := 1 / 2)) fun x hx => ?_
  apply autoCorr_eq_zero hsupp
  rw [mem_Icc, not_and_or, not_le, not_le] at hx
  rcases hx with h | h
  · linarith [neg_abs_le x]
  · linarith [le_abs_self x]

/-- The Laplace transform `ρ̃(z) = ∫ ρ(v) e^{zv} dv` of the autocorrelation. -/
def autoLaplace (g : ℝ → ℝ) (z : ℂ) : ℂ := ∫ v, (autoCorr g v : ℂ) * Complex.exp (z * v)

theorem autoLaplace_eq_paperFT (g : ℝ → ℝ) (z : ℂ) :
    autoLaplace g z = paperFT (fun v => (autoCorr g v : ℂ)) (-I * z) := by
  unfold autoLaplace paperFT
  congr 1; funext v
  congr 2
  rw [show I * (-I * z) = -(I * I) * z by ring, Complex.I_mul_I]; ring

theorem differentiable_autoLaplace (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hsupp : ∀ u, 1 / 4 < |u| → g u = 0) : Differentiable ℂ (autoLaplace g) := by
  have hk : Continuous fun v => (autoCorr g v : ℂ) :=
    Complex.continuous_ofReal.comp (contDiff_autoCorr hg hgc).continuous
  have hkc : HasCompactSupport fun v => (autoCorr g v : ℂ) :=
    (hasCompactSupport_autoCorr hsupp).comp_left Complex.ofReal_zero
  have hP := Zeta23.WeilEF.differentiable_paperFT hk hkc
  have e : autoLaplace g = fun z => paperFT (fun v => (autoCorr g v : ℂ)) (-I * z) :=
    funext (autoLaplace_eq_paperFT g)
  rw [e]
  exact hP.comp (by fun_prop : Differentiable ℂ fun z : ℂ => -I * z)

/-- The real Laplace transform of the autocorrelation. -/
def autoLaplaceReal (g : ℝ → ℝ) (σ : ℝ) : ℝ := ∫ v, autoCorr g v * Real.exp (σ * v)

theorem autoLaplace_ofReal (g : ℝ → ℝ) (σ : ℝ) :
    autoLaplace g σ = (autoLaplaceReal g σ : ℂ) := by
  rw [autoLaplace, autoLaplaceReal, ← integral_complex_ofReal]
  congr 1; funext v
  push_cast; rfl

/-- **`ρ̃(σ) = ∫ g e^{−σu} · ∫ g e^{σu}`** (Fubini). -/
theorem autoLaplaceReal_eq (hg : ContDiff ℝ 2 g) (hsupp : ∀ u, 1 / 4 < |u| → g u = 0) (σ : ℝ) :
    autoLaplaceReal g σ = (∫ u, g u * Real.exp (-σ * u)) * (∫ u, g u * Real.exp (σ * u)) := by
  have hgcont := hg.continuous
  set F : ℝ → ℝ → ℝ := fun v t => g t * g (t - v) * Real.exp (σ * v) with hF
  have hFi : Integrable (Function.uncurry F) (volume.prod volume) := by
    refine (Continuous.integrable_of_hasCompactSupport ?_ ?_)
    · simp only [hF]
      fun_prop
    · refine HasCompactSupport.intro
        ((isCompact_Icc (a := -(1 / 2 : ℝ)) (b := 1 / 2)).prod
          (isCompact_Icc (a := -(1 / 4 : ℝ)) (b := 1 / 4))) fun p hp => ?_
      simp only [hF, Function.uncurry]
      rw [mem_prod, not_and_or, mem_Icc, mem_Icc, not_and_or, not_and_or, not_le, not_le, not_le,
        not_le] at hp
      by_cases ht : 1 / 4 < |p.2|
      · rw [hsupp _ ht]; ring
      · rw [not_lt] at ht
        have hv : 1 / 4 < |p.2 - p.1| := by
          rcases hp with (h | h) | (h | h)
          · have := abs_sub_abs_le_abs_sub p.1 p.2
            rw [abs_sub_comm] at this
            linarith [neg_abs_le p.1]
          · have := abs_sub_abs_le_abs_sub p.1 p.2
            rw [abs_sub_comm] at this
            linarith [le_abs_self p.1]
          · linarith [neg_abs_le p.2]
          · linarith [le_abs_self p.2]
        rw [hsupp _ hv]; ring
  have h1 : autoLaplaceReal g σ = ∫ v, ∫ t, F v t := by
    unfold autoLaplaceReal autoCorr
    congr 1; funext v
    rw [← integral_mul_const]
  rw [h1, integral_integral_swap hFi]
  have h2 : ∀ t, ∫ v, F v t = g t * Real.exp (σ * t) * ∫ s, g s * Real.exp (-σ * s) := by
    intro t
    have := integral_sub_left_eq_self (μ := volume)
      (fun s => g t * g s * Real.exp (σ * (t - s))) t
    simp only [sub_sub_cancel] at this
    rw [show (∫ v, F v t) = ∫ v, g t * g (t - v) * Real.exp (σ * v) from rfl, this,
      ← integral_const_mul]
    congr 1; funext s
    rw [show σ * (t - s) = σ * t + -σ * s by ring, Real.exp_add]; ring
  simp_rw [h2]
  rw [integral_mul_const, mul_comm]

/-- **`ρ̃(½) = P₊P₋`.** -/
theorem autoLaplaceReal_half (hg : ContDiff ℝ 2 g) (hsupp : ∀ u, 1 / 4 < |u| → g u = 0) :
    autoLaplaceReal g (1 / 2) = poleConst g := by
  rw [autoLaplaceReal_eq hg hsupp, poleConst]
  congr 1 <;> congr 1 <;> funext u <;> congr 2 <;> ring

/-- **`ρ̃(0) = (∫ g)²`.** -/
theorem autoLaplaceReal_zero (hg : ContDiff ℝ 2 g) (hsupp : ∀ u, 1 / 4 < |u| → g u = 0) :
    autoLaplaceReal g 0 = (∫ u, g u) ^ 2 := by
  rw [autoLaplaceReal_eq hg hsupp]
  simp only [neg_zero, zero_mul, Real.exp_zero, mul_one]
  ring

/-! ## The Laplace transform of the prime window -/

/-- Each window term transforms to `n^{−½−σ} ρ̃(σ)`. -/
theorem integral_windowValue_mul_exp (hsupp : ∀ u, 1 / 4 < |u| → g u = 0) {n : ℕ} (hn : 2 ≤ n) (σ : ℝ) :
    ∫ L in Ioi (0 : ℝ), windowValue g L n * Real.exp (-σ * L) =
      (n : ℝ) ^ (-(1 / 2 + σ)) * autoLaplaceReal g σ := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlog : 1 / 2 < Real.log n := by
    have := Real.log_le_log two_pos (by exact_mod_cast hn : (2 : ℝ) ≤ n)
    linarith [WeilExcess.seventeen_div_twentyfive_lt_log_two]
  have hpt : ∀ L ∈ Ioi (0 : ℝ), windowValue g L n * Real.exp (-σ * L) =
      (Real.sqrt n)⁻¹ * (autoCorr g (Real.log n - L) * Real.exp (-σ * L)) := by
    intro L hL
    have hz : autoCorr g (Real.log n + L) = 0 :=
      autoCorr_eq_zero hsupp (by
        rw [abs_of_pos (by linarith [mem_Ioi.mp hL])]; linarith [mem_Ioi.mp hL])
    unfold windowValue; rw [hz]; ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul]
  have hzero : ∀ L ∉ Ioi (0 : ℝ), autoCorr g (Real.log n - L) * Real.exp (-σ * L) = 0 := by
    intro L hL
    rw [mem_Ioi, not_lt] at hL
    rw [autoCorr_eq_zero hsupp (by rw [abs_of_pos (by linarith)]; linarith), zero_mul]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  have hsub := integral_sub_left_eq_self (μ := volume)
    (fun v => autoCorr g v * Real.exp (-σ * (Real.log n - v))) (Real.log n)
  simp only [sub_sub_cancel] at hsub
  rw [hsub]
  have hexp : ∀ v, autoCorr g v * Real.exp (-σ * (Real.log n - v)) =
      Real.exp (-σ * Real.log n) * (autoCorr g v * Real.exp (σ * v)) := by
    intro v
    rw [show -σ * (Real.log n - v) = -σ * Real.log n + σ * v by ring, Real.exp_add]; ring
  simp_rw [hexp]
  rw [integral_const_mul, ← autoLaplaceReal]
  have e1 : Real.exp (-σ * Real.log n) = (n : ℝ) ^ (-σ) := by
    rw [Real.rpow_def_of_pos hn', mul_comm]
  have e2 : (Real.sqrt n)⁻¹ = (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_neg hn'.le]
  rw [e1, e2, ← mul_assoc, ← Real.rpow_add hn']
  congr 2; ring


theorem continuous_windowValue (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (n : ℕ) :
    Continuous fun L => windowValue g L n := by
  have hc := (contDiff_autoCorr hg hgc).continuous
  exact ((hc.comp (continuous_const.sub continuous_id)).add
    (hc.comp (continuous_const.add continuous_id))).div_const _

theorem hasCompactSupport_windowValue (hsupp : ∀ u, 1 / 4 < |u| → g u = 0) (n : ℕ) :
    HasCompactSupport fun L => windowValue g L n := by
  refine HasCompactSupport.intro
    (isCompact_Icc (a := -(|Real.log n| + 1)) (b := |Real.log n| + 1)) fun L hL => ?_
  have hL' : |Real.log n| + 1 < |L| := by
    rw [mem_Icc, not_and_or, not_le, not_le] at hL
    rcases hL with h | h
    · rw [abs_of_neg (a := L) (by linarith [abs_nonneg (Real.log n)])]; linarith
    · rw [abs_of_pos (a := L) (by linarith [abs_nonneg (Real.log n)])]; linarith
  have h1 : 1 / 2 < |Real.log n - L| := by
    have := abs_sub_abs_le_abs_sub L (Real.log n)
    rw [abs_sub_comm] at this
    linarith
  have h2 : 1 / 2 < |Real.log n + L| := by
    have := abs_sub_abs_le_abs_sub L (-Real.log n)
    rw [abs_neg, show L - -Real.log n = Real.log n + L by ring] at this
    linarith
  unfold windowValue
  rw [autoCorr_eq_zero hsupp h1, autoCorr_eq_zero hsupp h2, add_zero, zero_div]

theorem measurable_primeWindow (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) :
    Measurable (primeWindow g) :=
  Measurable.tsum fun n => measurable_const.mul (continuous_windowValue hg hgc n).measurable

theorem vonMangoldt_rpow_le_norm_term (s : ℝ) (n : ℕ) :
    (if 2 ≤ n then (ArithmeticFunction.vonMangoldt n : ℝ) else 0) * (n : ℝ) ^ (-s) ≤
      ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s n‖ := by
  rw [LSeries.norm_term_eq]
  split_ifs with h2 h0 h0
  · omega
  · rw [Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
      Complex.ofReal_re, Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]
  · simp
  · rw [zero_mul]; positivity

theorem vonMangoldt_rpow_nonneg (s : ℝ) (n : ℕ) :
    0 ≤ (if 2 ≤ n then (ArithmeticFunction.vonMangoldt n : ℝ) else 0) * (n : ℝ) ^ (-s) := by
  refine mul_nonneg ?_ (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  split_ifs
  · exact ArithmeticFunction.vonMangoldt_nonneg
  · exact le_rfl

theorem summable_vonMangoldt_rpow {s : ℝ} (hs : 1 < s) :
    Summable fun n : ℕ =>
      (if 2 ≤ n then (ArithmeticFunction.vonMangoldt n : ℝ) else 0) * (n : ℝ) ^ (-s) := by
  have h := ArithmeticFunction.LSeriesSummable_vonMangoldt (s := (s : ℂ)) (by simpa using hs)
  exact Summable.of_nonneg_of_le (vonMangoldt_rpow_nonneg s) (vonMangoldt_rpow_le_norm_term s)
    (summable_norm_iff.mpr h)

/-- **The prime Dirichlet series.** `Σ_{n≥2} Λ(n) n^{−s} = −ζ'/ζ(s)` for real `s > 1`. -/
theorem tsum_vonMangoldt_rpow_eq {s : ℝ} (hs : 1 < s) :
    ((∑' n : ℕ, (if 2 ≤ n then (ArithmeticFunction.vonMangoldt n : ℝ) else 0) *
        (n : ℝ) ^ (-s) : ℝ) : ℂ) = -deriv riemannZeta s / riemannZeta s := by
  rw [← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by simpa using hs),
    LSeries, Complex.ofReal_tsum]
  congr 1; funext n
  rw [LSeries.term_def]
  rcases Nat.lt_or_ge n 2 with h | h
  · rw [if_neg (by omega)]
    split_ifs with h0
    · simp
    · have : n = 1 := by omega
      subst this; simp
  · rw [if_pos h, if_neg (by omega), Complex.ofReal_mul,
      Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_neg, Complex.cpow_neg,
      div_eq_mul_inv]
    push_cast; rfl

/-- **Laplace transform of the prime window.** For `σ > ½`,
`∫_0^∞ S(L) e^{−σL} dL = ρ̃(σ) Σ_{n≥2} Λ(n) n^{−½−σ}`. -/
theorem integral_primeWindow_mul_exp (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hsupp : ∀ u, 1 / 4 < |u| → g u = 0) (hg0 : ∀ u, 0 ≤ g u) {σ : ℝ} (hσ : 1 / 2 < σ) :
    ∫ L in Ioi (0 : ℝ), primeWindow g L * Real.exp (-σ * L) =
      autoLaplaceReal g σ * ∑' n : ℕ, (if 2 ≤ n then (ArithmeticFunction.vonMangoldt n : ℝ)
        else 0) * (n : ℝ) ^ (-(1 / 2 + σ)) := by
  let c : ℕ → ℝ := fun n => if 2 ≤ n then (ArithmeticFunction.vonMangoldt n : ℝ) else 0
  let F : ℕ → ℝ → ℝ := fun n L => c n * windowValue g L n * Real.exp (-σ * L)
  have hFc : ∀ n, HasCompactSupport (F n) := fun n =>
    (hasCompactSupport_windowValue hsupp n).mono (Function.support_subset_iff'.mpr fun L hL => by
      simp only [Function.mem_support, not_not] at hL
      simp only [F, hL, mul_zero, zero_mul])
  have hFint : ∀ n, Integrable (F n) (volume.restrict (Ioi 0)) := fun n =>
    (Continuous.integrable_of_hasCompactSupport
      ((continuous_const.mul (continuous_windowValue hg hgc n)).mul (by fun_prop))
      (hFc n)).integrableOn
  have hFval : ∀ n, ∫ L in Ioi (0 : ℝ), F n L =
      c n * (n : ℝ) ^ (-(1 / 2 + σ)) * autoLaplaceReal g σ := by
    intro n
    simp only [F, mul_assoc]
    rw [integral_const_mul]
    by_cases h2 : 2 ≤ n
    · rw [integral_windowValue_mul_exp hsupp h2]
    · simp [c, h2]
  have hFnorm : ∀ n, ∫ L in Ioi (0 : ℝ), ‖F n L‖ = ∫ L in Ioi (0 : ℝ), F n L := fun n =>
    integral_congr_ae (ae_of_all _ fun L => Real.norm_of_nonneg
      (mul_nonneg (primeWindow_term_nonneg hg0 L n) (Real.exp_pos _).le))
  have hsum : Summable fun n => ∫ L in Ioi (0 : ℝ), ‖F n L‖ := by
    simp_rw [hFnorm, hFval]
    exact (summable_vonMangoldt_rpow (by linarith)).mul_right _
  have hswap := integral_tsum_of_summable_integral_norm hFint hsum
  have hpt : ∀ L, primeWindow g L * Real.exp (-σ * L) = ∑' n, F n L := fun L => by
    rw [primeWindow, ← tsum_mul_right]
  simp_rw [hpt]
  rw [← hswap]
  simp_rw [hFval]
  rw [tsum_mul_right, mul_comm]

/-! ## The Landau measure -/

/-- The majorant `P₊P₋(e^{L/2} + e^{−L/2}) + C` of the prime window. -/
def shiftMajorant (g : ℝ → ℝ) (C L : ℝ) : ℝ :=
  poleConst g * (Real.exp (L / 2) + Real.exp (-L / 2)) + C

/-- The clipped density `max(M(L) − S(L), 0)`. -/
def shiftDensity (g : ℝ → ℝ) (C L : ℝ) : NNReal :=
  Real.toNNReal (shiftMajorant g C L - primeWindow g L)

theorem measurable_shiftDensity (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (C : ℝ) :
    Measurable (shiftDensity g C) := by
  unfold shiftDensity shiftMajorant
  exact ((Continuous.measurable (by fun_prop)).sub (measurable_primeWindow hg hgc)).real_toNNReal

/-- `(M − S) dL` on `(0, ∞)` plus Lebesgue measure. -/
def shiftMeasure (g : ℝ → ℝ) (C : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi (0 : ℝ))).withDensity (fun L => (shiftDensity g C L : ENNReal)) + volume

theorem poleConst_nonneg (hg0 : ∀ u, 0 ≤ g u) : 0 ≤ poleConst g :=
  mul_nonneg (integral_nonneg fun u => mul_nonneg (hg0 u) (Real.exp_pos _).le)
    (integral_nonneg fun u => mul_nonneg (hg0 u) (Real.exp_pos _).le)

theorem archConst_nonneg (g : ℝ → ℝ) : 0 ≤ archConst g :=
  integral_nonneg fun _ => norm_nonneg _

theorem primeWindow_nonneg (hg0 : ∀ u, 0 ≤ g u) (L : ℝ) : 0 ≤ primeWindow g L :=
  tsum_nonneg fun n => primeWindow_term_nonneg hg0 L n

theorem shiftDensity_le (hg0 : ∀ u, 0 ≤ g u) {C : ℝ} (hC : 0 ≤ C) {L : ℝ} (hL : 0 ≤ L) :
    (shiftDensity g C L : ℝ) ≤ (2 * poleConst g + C) * Real.exp (L / 2) := by
  unfold shiftDensity shiftMajorant
  rw [Real.coe_toNNReal']
  have hP := poleConst_nonneg hg0
  have hS := primeWindow_nonneg hg0 L
  have h1 : Real.exp (-L / 2) ≤ Real.exp (L / 2) := Real.exp_le_exp.mpr (by linarith)
  have h2 : 1 ≤ Real.exp (L / 2) := Real.one_le_exp (by linarith)
  refine max_le ?_ (mul_nonneg (by linarith) (Real.exp_pos _).le)
  nlinarith [mul_le_mul_of_nonneg_left h1 hP, mul_le_mul_of_nonneg_left h2 hC]

theorem integrableOn_shiftMajorant {σ : ℝ} (K : ℝ) (hσ : 1 / 2 < σ) :
    IntegrableOn (fun L : ℝ => K * Real.exp (L / 2) * Real.exp (-σ * L)) (Ioi 0) := by
  have h2 := (exp_neg_integrableOn_Ioi 0 (by linarith : (0 : ℝ) < σ - 1 / 2)).const_mul K
  refine IntegrableOn.congr_fun h2 (fun L _ => ?_) measurableSet_Ioi
  rw [show Real.exp (-(σ - 1 / 2) * L) = Real.exp (L / 2) * Real.exp (-σ * L) by
    rw [← Real.exp_add]; ring_nf]
  ring

theorem integrable_shiftDensity_smul (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hg0 : ∀ u, 0 ≤ g u) {C : ℝ} (hC : 0 ≤ C) {σ : ℝ} (hσ : 1 / 2 < σ) :
    Integrable (fun L : ℝ => shiftDensity g C L • Real.exp (-σ * L)) (volume.restrict (Ioi 0)) := by
  refine (integrableOn_shiftMajorant (2 * poleConst g + C) hσ).mono' ?_ ?_
  · exact ((measurable_shiftDensity hg hgc C).coe_nnreal_real.aestronglyMeasurable.smul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)).aestronglyMeasurable)
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with L hL
    rw [NNReal.smul_def, norm_smul, Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _),
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_right (shiftDensity_le hg0 hC (le_of_lt hL)) (Real.exp_pos _).le

theorem laplaceMass_shiftDensity_ne_top (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hg0 : ∀ u, 0 ≤ g u) {C : ℝ} (hC : 0 ≤ C) {σ : ℝ} (hσ : 1 / 2 < σ) :
    laplaceMass ((volume.restrict (Ioi (0 : ℝ))).withDensity
      (fun L => (shiftDensity g C L : ENNReal))) σ ≠ ⊤ := by
  unfold laplaceMass
  have hm : Measurable (fun L : ℝ => ENNReal.ofReal (Real.exp (-σ * L))) := by measurability
  rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    inter_self, lintegral_withDensity_eq_lintegral_mul _
      (measurable_shiftDensity hg hgc C).coe_nnreal_ennreal hm]
  refine ne_top_of_le_ne_top
    (integrableOn_shiftMajorant (2 * poleConst g + C) hσ).lintegral_lt_top.ne ?_
  refine lintegral_mono_ae ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with L hL
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_right (shiftDensity_le hg0 hC (le_of_lt hL)) (Real.exp_pos _).le

theorem laplaceMass_shiftMeasure_eq (g : ℝ → ℝ) (C σ : ℝ) :
    laplaceMass (shiftMeasure g C) σ =
      laplaceMass ((volume.restrict (Ioi (0 : ℝ))).withDensity
        (fun L => (shiftDensity g C L : ENNReal))) σ + laplaceMass volume σ := by
  unfold laplaceMass shiftMeasure
  rw [Measure.restrict_add, lintegral_add_measure]

/-- The convergence set lies in `(0, ∞)` and contains `(½, ∞)`; its infimum is the abscissa. -/
theorem isAbscissa_shiftMeasure (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hg0 : ∀ u, 0 ≤ g u) {C : ℝ} (hC : 0 ≤ C) :
    IsAbscissa (shiftMeasure g C) (sInf {σ : ℝ | laplaceMass (shiftMeasure g C) σ ≠ ⊤}) ∧
      0 ≤ sInf {σ : ℝ | laplaceMass (shiftMeasure g C) σ ≠ ⊤} ∧
      sInf {σ : ℝ | laplaceMass (shiftMeasure g C) σ ≠ ⊤} ≤ 3 / 4 := by
  set S := {σ : ℝ | laplaceMass (shiftMeasure g C) σ ≠ ⊤} with hS
  have hpos : ∀ σ ∈ S, 0 < σ := by
    intro σ hσ
    by_contra hle
    apply hσ
    rw [laplaceMass_shiftMeasure_eq]
    rcases lt_or_eq_of_le (not_lt.mp hle) with h | h
    · rw [laplaceMass_volume_eq_top h, add_top]
    · rw [h, laplaceMass_volume_zero_eq_top, add_top]
  have hbdd : BddBelow S := ⟨0, fun σ hσ => (hpos σ hσ).le⟩
  have hmem : ∀ σ : ℝ, 1 / 2 < σ → σ ∈ S := by
    intro σ hσ
    show laplaceMass (shiftMeasure g C) σ ≠ ⊤
    rw [laplaceMass_shiftMeasure_eq]
    exact ENNReal.add_ne_top.mpr ⟨laplaceMass_shiftDensity_ne_top hg hgc hg0 hC hσ,
      laplaceMass_volume_ne_top (by linarith)⟩
  have hne : S.Nonempty := ⟨1, hmem 1 (by norm_num)⟩
  refine ⟨⟨fun σ hσ => ?_, fun σ hσ => ?_⟩, Real.sInf_nonneg fun σ hσ => (hpos σ hσ).le,
    csInf_le hbdd (hmem _ (by norm_num))⟩
  · obtain ⟨σ', hσ'S, hlt⟩ := exists_lt_of_csInf_lt hne hσ
    exact ne_top_of_le_ne_top hσ'S (laplaceMass_antitone _ hlt.le)
  · by_contra h
    exact absurd (csInf_le hbdd (show σ ∈ S from h)) (not_le.mpr hσ)

/-! ## The continuation -/

theorem analyticAt_dslope_autoLaplace (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hsupp : ∀ u, 1 / 4 < |u| → g u = 0) (z : ℂ) :
    AnalyticAt ℂ (dslope (autoLaplace g) (1 / 2)) z := by
  have h := (Complex.differentiableOn_dslope (s := univ) (c := 1 / 2) (f := autoLaplace g)
    Filter.univ_mem).mpr (differentiable_autoLaplace hg hgc hsupp).differentiableOn
  exact (differentiableOn_univ.mp h).analyticAt z

/-- The candidate continuation
`−(ρ̃(z) − ρ̃(½))/(z − ½) + P₊P₋/(z + ½) + (C + 1)/z + ρ̃(z) ζ_u'/ζ_u(z + ½)`,
with `ζ_u(s) = (s − 1)ζ(s)`. -/
def shiftContinuation (g : ℝ → ℝ) (C : ℝ) (z : ℂ) : ℂ :=
  -dslope (autoLaplace g) (1 / 2) z + poleConst g / (z + 1 / 2) + (C + 1) / z +
    autoLaplace g z * logDeriv zetaResidueUnit (z + 1 / 2)

theorem analyticAt_shiftContinuation (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hsupp : ∀ u, 1 / 4 < |u| → g u = 0) (C : ℝ) {z : ℂ} (hz0 : z ≠ 0) (hz1 : z + 1 / 2 ≠ 0)
    (hζ : zetaResidueUnit (z + 1 / 2) ≠ 0) :
    AnalyticAt ℂ (shiftContinuation g C) z := by
  unfold shiftContinuation
  have hshift : AnalyticAt ℂ (fun w : ℂ => w + 1 / 2) z := by fun_prop
  have hζan : AnalyticAt ℂ (fun w : ℂ => zetaResidueUnit (w + 1 / 2)) z :=
    AnalyticAt.comp (f := fun w : ℂ => w + 1 / 2) (analyticAt_zetaResidueUnit (z + 1 / 2)) hshift
  have hdζ : AnalyticAt ℂ (fun w : ℂ => deriv zetaResidueUnit (w + 1 / 2)) z :=
    AnalyticAt.comp (f := fun w : ℂ => w + 1 / 2) (analyticAt_zetaResidueUnit (z + 1 / 2)).deriv
      hshift
  have hlog : AnalyticAt ℂ (fun w : ℂ => logDeriv zetaResidueUnit (w + 1 / 2)) z := by
    simp only [logDeriv_apply]
    exact hdζ.div hζan hζ
  have hρ : AnalyticAt ℂ (autoLaplace g) z :=
    (differentiable_autoLaplace hg hgc hsupp).analyticAt z
  exact (((analyticAt_dslope_autoLaplace hg hgc hsupp z).neg.add
    (analyticAt_const.div hshift hz1)).add (analyticAt_const.div analyticAt_id hz0)).add
      (hρ.mul hlog)

theorem shiftDensity_eq {C : ℝ} (hB : ∀ L : ℝ, 0 < L → primeWindow g L ≤ shiftMajorant g C L)
    {L : ℝ} (hL : 0 < L) :
    (shiftDensity g C L : ℝ) = shiftMajorant g C L - primeWindow g L := by
  unfold shiftDensity
  exact Real.coe_toNNReal _ (sub_nonneg.mpr (hB L hL))

theorem integral_shiftMajorant_mul_exp (C : ℝ) {σ : ℝ} (hσ : 1 / 2 < σ) :
    IntegrableOn (fun L => shiftMajorant g C L * Real.exp (-σ * L)) (Ioi 0) ∧
      ∫ L in Ioi (0 : ℝ), shiftMajorant g C L * Real.exp (-σ * L) =
        poleConst g / (σ - 1 / 2) + poleConst g / (σ + 1 / 2) + C / σ := by
  have hσ0 : 0 < σ := by linarith
  have hpt : ∀ L : ℝ, shiftMajorant g C L * Real.exp (-σ * L) =
      poleConst g * Real.exp (-(σ - 1 / 2) * L) + poleConst g * Real.exp (-(σ + 1 / 2) * L) +
        C * Real.exp (-σ * L) := by
    intro L
    unfold shiftMajorant
    have e1 : Real.exp (L / 2) * Real.exp (-σ * L) = Real.exp (-(σ - 1 / 2) * L) := by
      rw [← Real.exp_add]; ring_nf
    have e2 : Real.exp (-L / 2) * Real.exp (-σ * L) = Real.exp (-(σ + 1 / 2) * L) := by
      rw [← Real.exp_add]; ring_nf
    rw [← e1, ← e2]; ring
  have hi1 : IntegrableOn (fun L => Real.exp (-(σ - 1 / 2) * L)) (Ioi 0) :=
    exp_neg_integrableOn_Ioi 0 (by linarith)
  have hi2 : IntegrableOn (fun L => Real.exp (-(σ + 1 / 2) * L)) (Ioi 0) :=
    exp_neg_integrableOn_Ioi 0 (by linarith)
  have hi3 : IntegrableOn (fun L => Real.exp (-σ * L)) (Ioi 0) := exp_neg_integrableOn_Ioi 0 hσ0
  simp_rw [hpt]
  refine ⟨((hi1.const_mul _).add (hi2.const_mul _)).add (hi3.const_mul _), ?_⟩
  rw [integral_add (f := fun L => poleConst g * Real.exp (-(σ - 1 / 2) * L) +
      poleConst g * Real.exp (-(σ + 1 / 2) * L)) ((hi1.const_mul _).add (hi2.const_mul _))
      (hi3.const_mul _),
    integral_add (hi1.const_mul _) (hi2.const_mul _), integral_const_mul, integral_const_mul,
    integral_const_mul, integral_exp_neg_mul_Ioi_real (by linarith),
    integral_exp_neg_mul_Ioi_real (by linarith), integral_exp_neg_mul_Ioi_real hσ0]
  ring

/-- On real `σ > ½` the Laplace transform of the shift measure is the continuation. -/
theorem laplaceReal_shiftMeasure_eq (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hsupp : ∀ u, 1 / 4 < |u| → g u = 0) (hg0 : ∀ u, 0 ≤ g u) {C : ℝ} (hC : 0 ≤ C)
    (hB : ∀ L : ℝ, 0 < L → primeWindow g L ≤ shiftMajorant g C L) {σ : ℝ} (hσ : 1 / 2 < σ) :
    ((laplaceReal (shiftMeasure g C) σ : ℝ) : ℂ) = shiftContinuation g C (σ : ℂ) := by
  have hσ0 : 0 < σ := by linarith
  have hexpInt : IntegrableOn (fun L : ℝ => Real.exp (-σ * L)) (Ioi 0) :=
    exp_neg_integrableOn_Ioi 0 hσ0
  have hd := integrable_shiftDensity_smul hg hgc hg0 hC hσ
  have hdensInt : Integrable (fun L : ℝ => Real.exp (-σ * L))
      (((volume.restrict (Ioi (0 : ℝ))).withDensity
        (fun L => (shiftDensity g C L : ENNReal))).restrict (Ioi 0)) := by
    rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
      inter_self, integrable_withDensity_iff_integrable_smul (measurable_shiftDensity hg hgc C)]
    exact hd
  have hsplit : laplaceReal (shiftMeasure g C) σ =
      (∫ L in Ioi (0 : ℝ), Real.exp (-σ * L) ∂((volume.restrict (Ioi (0 : ℝ))).withDensity
        (fun L => (shiftDensity g C L : ENNReal)))) + 1 / σ := by
    unfold laplaceReal shiftMeasure
    rw [Measure.restrict_add, integral_add_measure hdensInt hexpInt,
      integral_exp_neg_mul_Ioi_real hσ0]
  obtain ⟨hMint, hMval⟩ := integral_shiftMajorant_mul_exp (g := g) C hσ
  have hdens : (∫ L in Ioi (0 : ℝ), Real.exp (-σ * L) ∂((volume.restrict (Ioi (0 : ℝ))).withDensity
        (fun L => (shiftDensity g C L : ENNReal)))) =
      (∫ L in Ioi (0 : ℝ), shiftMajorant g C L * Real.exp (-σ * L)) -
        ∫ L in Ioi (0 : ℝ), primeWindow g L * Real.exp (-σ * L) := by
    rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
      inter_self, integral_withDensity_eq_integral_smul (measurable_shiftDensity hg hgc C)]
    have hpt : ∀ L ∈ Ioi (0 : ℝ), shiftDensity g C L • Real.exp (-σ * L) =
        shiftMajorant g C L * Real.exp (-σ * L) - primeWindow g L * Real.exp (-σ * L) := by
      intro L hL
      rw [NNReal.smul_def, smul_eq_mul, shiftDensity_eq hB hL]; ring
    have hSint : IntegrableOn (fun L => primeWindow g L * Real.exp (-σ * L)) (Ioi 0) := by
      refine (hMint.sub hd).congr_fun (fun L hL => ?_) measurableSet_Ioi
      simp only [Pi.sub_apply]
      rw [hpt L hL]; ring
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_sub hMint hSint]
  set D := ∑' n : ℕ, (if 2 ≤ n then (ArithmeticFunction.vonMangoldt n : ℝ) else 0) *
    (n : ℝ) ^ (-(1 / 2 + σ)) with hDdef
  set R := autoLaplaceReal g σ with hRdef
  have hD := tsum_vonMangoldt_rpow_eq (s := 1 / 2 + σ) (by linarith)
  rw [← hDdef, show (((1 / 2 + σ : ℝ)) : ℂ) = (σ : ℂ) + 1 / 2 by push_cast; ring] at hD
  have hs1 : (σ : ℂ) + 1 / 2 ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hζ : zetaResidueUnit ((σ : ℂ) + 1 / 2) ≠ 0 := by
    have h := zetaResidueUnit_ne_zero_of_ofReal_pos (u := σ + 1 / 2) (by linarith)
    simpa using h
  have hlog := logDeriv_zeta_eq hs1 hζ
  rw [logDeriv_apply] at hlog
  have hD' : (D : ℂ) = -(logDeriv zetaResidueUnit ((σ : ℂ) + 1 / 2) - ((σ : ℂ) - 1 / 2)⁻¹) := by
    rw [hD, neg_div, hlog, show (σ : ℂ) + 1 / 2 - 1 = (σ : ℂ) - 1 / 2 by ring]
  have hR : autoLaplace g (σ : ℂ) = (R : ℂ) := autoLaplace_ofReal g σ
  have hhalf : autoLaplace g (1 / 2 : ℂ) = (poleConst g : ℂ) := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, autoLaplace_ofReal,
      autoLaplaceReal_half hg hsupp]
  have hne : (σ : ℂ) ≠ 1 / 2 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hne' : (σ : ℂ) - 1 / 2 ≠ 0 := sub_ne_zero.mpr hne
  have hσc : (σ : ℂ) ≠ 0 := by exact_mod_cast hσ0.ne'
  have hσh : (σ : ℂ) + 1 / 2 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  rw [hsplit, hdens, hMval, integral_primeWindow_mul_exp hg hgc hsupp hg0 hσ, ← hRdef, ← hDdef]
  unfold shiftContinuation
  rw [dslope_of_ne _ hne, slope_def_field, hR, hhalf]
  push_cast
  rw [hD']
  field_simp
  ring

/-! ## Landau: the abscissa is zero -/

theorem abscissa_shiftMeasure_eq_zero (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hsupp : ∀ u, 1 / 4 < |u| → g u = 0) (hg0 : ∀ u, 0 ≤ g u) {C : ℝ} (hC : 0 ≤ C)
    (hB : ∀ L : ℝ, 0 < L → primeWindow g L ≤ shiftMajorant g C L) :
    IsAbscissa (shiftMeasure g C) 0 := by
  obtain ⟨hc, hc0, hc34⟩ := isAbscissa_shiftMeasure hg hgc hg0 hC
  set c : ℝ := sInf {σ : ℝ | laplaceMass (shiftMeasure g C) σ ≠ ⊤} with hcdef
  rcases hc0.lt_or_eq with hpos | hzero
  · exfalso
    have hζc : zetaResidueUnit ((c : ℂ) + 1 / 2) ≠ 0 := by
      have h := zetaResidueUnit_ne_zero_of_ofReal_pos (u := c + 1 / 2) (by linarith)
      simpa using h
    have hopen : IsOpen {z : ℂ | zetaResidueUnit (z + 1 / 2) ≠ 0} :=
      isOpen_ne_fun ((analyticOnNhd_univ_iff_differentiable.mp
        (fun z _ => analyticAt_zetaResidueUnit z)).continuous.comp
          (continuous_id.add continuous_const)) continuous_const
    obtain ⟨d, hd, hball⟩ := Metric.isOpen_iff.mp hopen _ hζc
    set δ : ℝ := min c d / 2 with hδdef
    have hδ : 0 < δ := by rw [hδdef]; exact half_pos (lt_min hpos hd)
    have hδc : δ ≤ c / 2 := by rw [hδdef]; linarith [min_le_left c d]
    have hδd : δ ≤ d / 2 := by rw [hδdef]; linarith [min_le_right c d]
    refine false_of_analyticAt_abscissa hc hδ (Φ := shiftContinuation g C) ?_ ?_
    · intro z hz
      rw [Metric.mem_ball, Complex.dist_eq] at hz
      have hzre : c / 2 < z.re := by
        have := Complex.abs_re_le_norm (z - c)
        rw [Complex.sub_re, Complex.ofReal_re] at this
        have := abs_le.mp this
        linarith
      have hz0 : z ≠ 0 := fun h => by rw [h] at hzre; simp at hzre; linarith
      have hz1 : z + 1 / 2 ≠ 0 := by
        intro h
        have hre := congrArg Complex.re h
        simp at hre
        linarith
      have hzζ : zetaResidueUnit (z + 1 / 2) ≠ 0 :=
        hball (show z ∈ Metric.ball (c : ℂ) d from by
          rw [Metric.mem_ball, Complex.dist_eq]; linarith)
      exact analyticAt_shiftContinuation hg hgc hsupp C hz0 hz1 hzζ
    · intro σ hσc _
      have hV : IsOpen {z : ℂ | c < z.re} := isOpen_lt continuous_const Complex.continuous_re
      have hTdiff : DifferentiableOn ℂ (complexLaplace (shiftMeasure g C)) {z : ℂ | c < z.re} :=
        fun z hz => (hasDerivAt_complexLaplace hc hz).differentiableAt.differentiableWithinAt
      have hT : AnalyticOnNhd ℝ (fun t : ℝ => complexLaplace (shiftMeasure g C) (t : ℂ))
          (Ioi c) := by
        intro t ht
        have h1 : AnalyticAt ℂ (complexLaplace (shiftMeasure g C)) (t : ℂ) :=
          hTdiff.analyticAt (hV.mem_nhds (by simpa using ht))
        exact h1.restrictScalars.comp (Complex.ofRealCLM.analyticAt t)
      have hH : AnalyticOnNhd ℝ (fun t : ℝ => shiftContinuation g C (t : ℂ)) (Ioi c) := by
        intro t ht
        have ht0 : 0 < t := lt_trans hpos ht
        have h1 : AnalyticAt ℂ (shiftContinuation g C) (t : ℂ) := by
          refine analyticAt_shiftContinuation hg hgc hsupp C (by exact_mod_cast ht0.ne') ?_ ?_
          · intro h; have hre := congrArg Complex.re h; simp at hre; linarith
          · have h := zetaResidueUnit_ne_zero_of_ofReal_pos (u := t + 1 / 2) (by linarith)
            simpa using h
        exact h1.restrictScalars.comp (Complex.ofRealCLM.analyticAt t)
      have h1mem : (1 : ℝ) ∈ Ioi c := by show c < 1; linarith
      have hfg : (fun t : ℝ => complexLaplace (shiftMeasure g C) (t : ℂ)) =ᶠ[𝓝 (1 : ℝ)]
          (fun t : ℝ => shiftContinuation g C (t : ℂ)) := by
        refine Filter.eventuallyEq_of_mem
          (Ioo_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1) (by norm_num : (1 : ℝ) < 3 / 2))
          fun t ht => ?_
        rw [RHTower.complexLaplace_ofReal]
        exact laplaceReal_shiftMeasure_eq hg hgc hsupp hg0 hC hB ht.1
      have heq := hT.eqOn_of_preconnected_of_eventuallyEq hH isPreconnected_Ioi h1mem hfg
      have hσ' : complexLaplace (shiftMeasure g C) (σ : ℂ) = shiftContinuation g C (σ : ℂ) :=
        heq (show σ ∈ Ioi c from hσc)
      rw [← hσ', RHTower.complexLaplace_ofReal]
  · rw [← hzero] at hc
    exact hc

/-! ## Off-line zeros are zeros of `ρ̃` -/

/-- `ζ_u = (s − 1)ζ` is not locally zero anywhere. -/
theorem not_eventually_zetaResidueUnit_eq_zero (ρ : ℂ) :
    ¬ ∀ᶠ z in 𝓝 ρ, zetaResidueUnit z = 0 := by
  intro hev
  have hana : AnalyticOnNhd ℂ zetaResidueUnit univ := fun z _ => analyticAt_zetaResidueUnit z
  have heq := hana.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (mem_univ ρ) hev
  have h2 : zetaResidueUnit ((2 : ℝ) : ℂ) ≠ 0 :=
    zetaResidueUnit_ne_zero_of_ofReal_pos (u := 2) (by norm_num)
  exact h2 (heq (mem_univ _))

/-- **A one-sided bound on the prime window forces `ρ̃(ρ − ½) = 0` at off-line zeros.** If
`S(L) ≤ P₊P₋(e^{L/2} + e^{−L/2}) + C` for all `L > 0`, then every zero `ρ` of `ζ` with
`Re ρ > ½` satisfies `ρ̃(ρ − ½) = 0`. -/
theorem autoLaplace_eq_zero_of_primeWindow_le (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hsupp : ∀ u, 1 / 4 < |u| → g u = 0) (hg0 : ∀ u, 0 ≤ g u) {C : ℝ} (hC : 0 ≤ C)
    (hB : ∀ L : ℝ, 0 < L → primeWindow g L ≤ shiftMajorant g C L) {ρ : ℂ}
    (hρ : riemannZeta ρ = 0) (hre : 1 / 2 < ρ.re) : autoLaplace g (ρ - 1 / 2) = 0 := by
  have hc := abscissa_shiftMeasure_eq_zero hg hgc hsupp hg0 hC hB
  set ν := shiftMeasure g C with hν
  let U : Set ℂ := {z : ℂ | 0 < z.re}
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hLap : AnalyticOnNhd ℂ (complexLaplace ν) U := by
    have hdiff : DifferentiableOn ℂ (complexLaplace ν) U :=
      fun z hz => (hasDerivAt_complexLaplace hc hz).differentiableAt.differentiableWithinAt
    exact hdiff.analyticOnNhd hUopen
  have hρan : ∀ z, AnalyticAt ℂ (autoLaplace g) z :=
    (differentiable_autoLaplace hg hgc hsupp).analyticAt
  let A : ℂ → ℂ := fun z => complexLaplace ν z + dslope (autoLaplace g) (1 / 2) z -
    poleConst g / (z + 1 / 2) - (C + 1) / z
  have hA : AnalyticOnNhd ℂ A U := by
    intro z hz
    change 0 < z.re at hz
    have hz0 : z ≠ 0 := by rintro rfl; simp at hz
    have hz1 : z + 1 / 2 ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    exact (((hLap z hz).add (analyticAt_dslope_autoLaplace hg hgc hsupp z)).sub
      (analyticAt_const.div (by fun_prop) hz1)).sub (analyticAt_const.div analyticAt_id hz0)
  have hζs : ∀ z, AnalyticAt ℂ (fun w : ℂ => zetaResidueUnit (w + 1 / 2)) z := fun z =>
    AnalyticAt.comp (f := fun w : ℂ => w + 1 / 2) (analyticAt_zetaResidueUnit (z + 1 / 2))
      (by fun_prop)
  have hdζs : ∀ z, AnalyticAt ℂ (fun w : ℂ => deriv zetaResidueUnit (w + 1 / 2)) z := fun z =>
    AnalyticAt.comp (f := fun w : ℂ => w + 1 / 2) (analyticAt_zetaResidueUnit (z + 1 / 2)).deriv
      (by fun_prop)
  let G : ℂ → ℂ := fun z =>
    zetaResidueUnit (z + 1 / 2) * A z - autoLaplace g z * deriv zetaResidueUnit (z + 1 / 2)
  have hG : AnalyticOnNhd ℂ G U := fun z hz =>
    ((hζs z).mul (hA z hz)).sub ((hρan z).mul (hdζs z))
  have hGreal : ∀ r : ℝ, 1 / 2 < r → G r = 0 := by
    intro r hr
    have hlap := laplaceReal_shiftMeasure_eq hg hgc hsupp hg0 hC hB hr
    rw [← RHTower.complexLaplace_ofReal] at hlap
    have hζ : zetaResidueUnit ((r : ℂ) + 1 / 2) ≠ 0 := by
      have h := zetaResidueUnit_ne_zero_of_ofReal_pos (u := r + 1 / 2) (by linarith)
      simpa using h
    have hAr : A r = autoLaplace g r *
        (deriv zetaResidueUnit ((r : ℂ) + 1 / 2) / zetaResidueUnit ((r : ℂ) + 1 / 2)) := by
      simp only [A]
      rw [hlap]
      unfold shiftContinuation
      rw [logDeriv_apply]
      ring
    simp only [G]
    rw [hAr]
    set Z := zetaResidueUnit ((r : ℂ) + 1 / 2)
    set D := deriv zetaResidueUnit ((r : ℂ) + 1 / 2)
    rw [show Z * (autoLaplace g r * (D / Z)) = autoLaplace g r * D * (Z / Z) by ring, div_self hζ,
      mul_one, sub_self]
  have hGzero : EqOn G 0 U := by
    have htwo : (2 : ℂ) ∈ U := by change 0 < (2 : ℂ).re; norm_num
    refine hG.eqOn_zero_of_preconnected_of_frequently_eq_zero
      (convex_halfSpace_re_gt 0).isPreconnected htwo ?_
    have htend : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝[>] (2 : ℝ)) (𝓝[≠] (2 : ℂ)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have h : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝 (2 : ℝ)) (𝓝 (2 : ℂ)) := by
          simpa using Complex.continuous_ofReal.tendsto (2 : ℝ)
        exact h.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with r hr
        simp only [mem_compl_iff, mem_singleton_iff]
        intro hcon
        have : r = 2 := by exact_mod_cast hcon
        exact absurd this (ne_of_gt hr)
    refine htend.frequently (Filter.Eventually.frequently ?_)
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact hGreal r (by linarith [mem_Ioi.mp hr])
  -- the residue at `ρ`
  set z₀ := ρ - 1 / 2 with hz₀def
  have hz₀ : z₀ ∈ U := by change 0 < (ρ - 1 / 2).re; simp; linarith
  have hρ1 : ρ ≠ 1 := riemannZeta_zero_ne_one hρ
  have hζuρ : zetaResidueUnit ρ = 0 := by
    rw [(zetaResidueUnit_eventuallyEq hρ1).eq_of_nhds, hρ, mul_zero]
  obtain ⟨n, h, hh, hh0, hfac0⟩ :=
    (analyticAt_zetaResidueUnit ρ).exists_eventuallyEq_pow_smul_nonzero_iff.mpr
      (not_eventually_zetaResidueUnit_eq_zero ρ)
  have hfac : zetaResidueUnit =ᶠ[𝓝 ρ] fun z => (z - ρ) ^ n • h z := hfac0
  have hn : n ≠ 0 := by
    intro hn0
    have := hfac.eq_of_nhds
    rw [hn0, sub_self, pow_zero, one_smul, hζuρ] at this
    exact hh0 this.symm
  have hres := logDeriv_residue_of_factorization hh hh0 hfac
  have hζne : ∀ᶠ s in 𝓝[≠] ρ, zetaResidueUnit s ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hfac,
      nhdsWithin_le_nhds (hh.continuousAt.eventually_ne hh0)] with s hs hfs hhs
    rw [hfs, smul_eq_mul]
    exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hs)) hhs
  have hshiftc : Continuous fun s : ℂ => s - 1 / 2 := by fun_prop
  have hUnhds : ∀ᶠ s in 𝓝[≠] ρ, s - 1 / 2 ∈ U :=
    nhdsWithin_le_nhds ((hUopen.preimage hshiftc).mem_nhds hz₀)
  have hAc : ContinuousAt (fun s : ℂ => A (s - 1 / 2)) ρ :=
    ContinuousAt.comp (g := A) (f := fun s : ℂ => s - 1 / 2) (x := ρ) (hA z₀ hz₀).continuousAt
      hshiftc.continuousAt
  have hρc : ContinuousAt (fun s : ℂ => autoLaplace g (s - 1 / 2)) ρ :=
    ContinuousAt.comp (g := autoLaplace g) (f := fun s : ℂ => s - 1 / 2) (x := ρ)
      (hρan z₀).continuousAt hshiftc.continuousAt
  have hlim0 : Tendsto (fun s => (s - ρ) * A (s - 1 / 2)) (𝓝[≠] ρ) (𝓝 0) := by
    have h1 : Tendsto (fun s : ℂ => s - ρ) (𝓝[≠] ρ) (𝓝 0) :=
      ((continuous_id.sub continuous_const).tendsto' ρ 0 (by simp)).mono_left nhdsWithin_le_nhds
    simpa using h1.mul (hAc.tendsto.mono_left nhdsWithin_le_nhds)
  have hlim1 : Tendsto (fun s => (s - ρ) * A (s - 1 / 2)) (𝓝[≠] ρ)
      (𝓝 (autoLaplace g z₀ * n)) := by
    refine ((hρc.tendsto.mono_left nhdsWithin_le_nhds).mul hres).congr' ?_
    filter_upwards [hUnhds, hζne] with s hsU hsζ
    have hGs := hGzero hsU
    simp only [G, Pi.zero_apply, sub_add_cancel] at hGs
    have hAeq : A (s - 1 / 2) =
        autoLaplace g (s - 1 / 2) * deriv zetaResidueUnit s / zetaResidueUnit s := by
      rw [eq_div_iff hsζ]
      linear_combination hGs
    rw [hAeq, logDeriv_apply]
    ring
  have hprod := tendsto_nhds_unique hlim1 hlim0
  rcases mul_eq_zero.mp hprod with h0 | h0
  · exact h0
  · exact absurd (by exact_mod_cast h0) hn

/-- **Shift-pair positivity bounds the prime window.** -/
theorem primeWindow_le_of_shiftPair (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hsupp : ∀ u, 1 / 4 < |u| → g u = 0) {L : ℝ}
    (h0 : 0 ≤ (weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
      (EF.weilTest (shiftPair g 1 L) (shiftPair g 1 L))).re) :
    primeWindow g L ≤ shiftMajorant g (2 * poleConst g + 2 * archConst g) L := by
  have h := windowSum_le_of_shiftPair hg hgc hsupp h0
  rw [windowSum_vonMangoldt_eq] at h
  unfold shiftMajorant
  linarith

/-- **Shift-pair positivity of `Λ` forces `ρ̃(ρ − ½) = 0` at every off-line zero.** -/
theorem autoLaplace_eq_zero_of_shiftPair_nonneg (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hsupp : ∀ u, 1 / 4 < |u| → g u = 0) (hg0 : ∀ u, 0 ≤ g u)
    (hpos : ∀ L : ℝ, 0 < L → 0 ≤ (weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
      (EF.weilTest (shiftPair g 1 L) (shiftPair g 1 L))).re)
    {ρ : ℂ} (hρ : riemannZeta ρ = 0) (hre : 1 / 2 < ρ.re) : autoLaplace g (ρ - 1 / 2) = 0 :=
  autoLaplace_eq_zero_of_primeWindow_le hg hgc hsupp hg0
    (by have := poleConst_nonneg hg0; have := archConst_nonneg g; positivity)
    (fun L hL => primeWindow_le_of_shiftPair hg hgc hsupp (hpos L hL)) hρ hre

/-! ## Dilations and the criterion -/

theorem hasCompactSupport_of_quarter_supp {f : ℝ → ℝ} (hf : ∀ u, 1 / 4 < |u| → f u = 0) :
    HasCompactSupport f := by
  refine HasCompactSupport.intro (isCompact_Icc (a := -(1 / 4 : ℝ)) (b := 1 / 4))
    fun u hu => hf u ?_
  rw [mem_Icc, not_and_or, not_le, not_le] at hu
  rcases hu with h | h
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

/-- The dilate `g_λ(u) = g(u/λ)`. -/
def dilateBump (g : ℝ → ℝ) (lam : ℝ) (u : ℝ) : ℝ := g (u / lam)

theorem contDiff_dilateBump (hg : ContDiff ℝ 2 g) (lam : ℝ) : ContDiff ℝ 2 (dilateBump g lam) :=
  hg.comp (contDiff_id.div_const lam)

theorem dilateBump_supp (hsupp : ∀ u, 1 / 4 < |u| → g u = 0) {lam : ℝ} (hl0 : 0 < lam)
    (hl1 : lam ≤ 1) : ∀ u, 1 / 4 < |u| → dilateBump g lam u = 0 := by
  intro u hu
  apply hsupp
  rw [abs_div, abs_of_pos hl0, lt_div_iff₀ hl0]
  nlinarith

/-- `ρ_{g_λ}(v) = λ ρ_g(v/λ)`. -/
theorem autoCorr_dilateBump (g : ℝ → ℝ) {lam : ℝ} (hl : 0 < lam) (v : ℝ) :
    autoCorr (dilateBump g lam) v = lam * autoCorr g (v / lam) := by
  unfold autoCorr dilateBump
  have h := Measure.integral_comp_div (fun s => g s * g (s - v / lam)) lam
  rw [abs_of_pos hl, smul_eq_mul] at h
  rw [← h]
  congr 1; funext t
  rw [sub_div]

/-- `ρ̃_{g_λ}(z) = λ² ρ̃_g(λz)`. -/
theorem autoLaplace_dilateBump (g : ℝ → ℝ) {lam : ℝ} (hl : 0 < lam) (z : ℂ) :
    autoLaplace (dilateBump g lam) z = (lam : ℂ) ^ 2 * autoLaplace g (lam * z) := by
  have hlc : (lam : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
  unfold autoLaplace
  simp_rw [autoCorr_dilateBump g hl]
  have h := Measure.integral_comp_div
    (fun w : ℝ => (autoCorr g w : ℂ) * Complex.exp ((lam : ℂ) * z * w)) lam
  rw [abs_of_pos hl, Complex.real_smul] at h
  have hpt : ∀ v : ℝ, ((lam * autoCorr g (v / lam) : ℝ) : ℂ) * Complex.exp (z * v) =
      (lam : ℂ) * ((autoCorr g (v / lam) : ℂ) *
        Complex.exp ((lam : ℂ) * z * ((v / lam : ℝ) : ℂ))) := by
    intro v
    have e : (lam : ℂ) * z * ((v / lam : ℝ) : ℂ) = z * v := by
      push_cast; field_simp
    rw [e]; push_cast; ring
  simp_rw [hpt]
  rw [integral_const_mul, h]
  ring

/-- **Shift-pair positivity of `Λ` on the dilates `g_λ`, `½ ≤ λ ≤ 1`, implies RH.** -/
theorem riemannHypothesis_of_dilatedShiftPair_nonneg (hg : ContDiff ℝ 2 g)
    (hsupp : ∀ u, 1 / 4 < |u| → g u = 0) (hg0 : ∀ u, 0 ≤ g u) (hint : ∫ u, g u ≠ 0)
    (hpos : ∀ lam ∈ Icc (1 / 2 : ℝ) 1, ∀ L : ℝ, 0 < L →
      0 ≤ (weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest (shiftPair (dilateBump g lam) 1 L)
          (shiftPair (dilateBump g lam) 1 L))).re) :
    RiemannHypothesis := by
  by_contra hRH
  obtain ⟨ρ, hρ, hre, -⟩ := exists_zetaZero_re_gt_half_of_not_riemannHypothesis hRH
  set z₀ := ρ - 1 / 2 with hz₀
  have hz₀ne : z₀ ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp [hz₀] at this; linarith
  have hgc := hasCompactSupport_of_quarter_supp hsupp
  have hzero : ∀ lam ∈ Icc (1 / 2 : ℝ) 1, autoLaplace g (lam * z₀) = 0 := by
    intro lam hlam
    have hl0 : 0 < lam := by linarith [hlam.1]
    have hsuppl := dilateBump_supp hsupp hl0 hlam.2
    have h := autoLaplace_eq_zero_of_shiftPair_nonneg (contDiff_dilateBump hg lam)
      (hasCompactSupport_of_quarter_supp hsuppl) hsuppl (fun u => hg0 _) (hpos lam hlam) hρ hre
    rw [autoLaplace_dilateBump g hl0] at h
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero 2 (by exact_mod_cast hl0.ne'))
  have hall : EqOn (autoLaplace g) 0 univ := by
    have han : AnalyticOnNhd ℂ (autoLaplace g) univ := fun z _ =>
      (differentiable_autoLaplace hg hgc hsupp).analyticAt z
    refine han.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
      (mem_univ z₀) ?_
    have htend : Tendsto (fun lam : ℝ => (lam : ℂ) * z₀) (𝓝[<] (1 : ℝ)) (𝓝[≠] z₀) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have h : Tendsto (fun lam : ℝ => (lam : ℂ) * z₀) (𝓝 (1 : ℝ)) (𝓝 z₀) := by
          have hc : Continuous fun lam : ℝ => (lam : ℂ) * z₀ := by fun_prop
          have := hc.tendsto 1
          rwa [Complex.ofReal_one, one_mul] at this
        exact h.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with lam hlam
        simp only [mem_compl_iff, mem_singleton_iff]
        intro hcon
        have h1 : ((lam : ℂ) - 1) * z₀ = 0 := by rw [sub_mul, hcon, one_mul, sub_self]
        rcases mul_eq_zero.mp h1 with h | h
        · have : lam = 1 := by exact_mod_cast sub_eq_zero.mp h
          exact absurd this (ne_of_lt hlam)
        · exact hz₀ne h
    refine htend.frequently (Filter.Eventually.frequently ?_)
    filter_upwards [Ioo_mem_nhdsLT (show (1 / 2 : ℝ) < 1 by norm_num)] with lam hlam
    exact hzero lam ⟨hlam.1.le, hlam.2.le⟩
  have h0 := hall (mem_univ 0)
  rw [Pi.zero_apply, show (0 : ℂ) = ((0 : ℝ) : ℂ) by simp, autoLaplace_ofReal,
    autoLaplaceReal_zero hg hsupp] at h0
  exact hint (pow_eq_zero_iff two_ne_zero |>.mp (by exact_mod_cast h0))

/-- **RH is Weil positivity of `Λ` on the dilated shift pairs.** For a nonnegative `C²` bump `g`
supported in `[−¼, ¼]` with `∫ g ≠ 0`, RH holds iff the Weil functional of `Λ` is nonnegative on
`g_λ + g_λ(· − L)` for all `½ ≤ λ ≤ 1` and `L > 0`. -/
theorem riemannHypothesis_iff_dilatedShiftPair_nonneg (hg : ContDiff ℝ 2 g)
    (hsupp : ∀ u, 1 / 4 < |u| → g u = 0) (hg0 : ∀ u, 0 ≤ g u) (hint : ∫ u, g u ≠ 0) :
    RiemannHypothesis ↔ ∀ lam ∈ Icc (1 / 2 : ℝ) 1, ∀ L : ℝ, 0 < L →
      0 ≤ (weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest (shiftPair (dilateBump g lam) 1 L)
          (shiftPair (dilateBump g lam) 1 L))).re := by
  refine ⟨fun hRH lam hlam L _ => ?_, riemannHypothesis_of_dilatedShiftPair_nonneg hg hsupp hg0 hint⟩
  have hl0 : 0 < lam := by linarith [hlam.1]
  exact riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mp hRH _
    (contDiff_shiftPair (contDiff_dilateBump hg lam) 1 L)
    (hasCompactSupport_shiftPair
      (hasCompactSupport_of_quarter_supp (dilateBump_supp hsupp hl0 hlam.2)) 1 L)

/-- The criterion for the concrete bump `narrowG 0`. -/
theorem riemannHypothesis_iff_dilatedShiftPair_narrowG :
    RiemannHypothesis ↔ ∀ lam ∈ Icc (1 / 2 : ℝ) 1, ∀ L : ℝ, 0 < L →
      0 ≤ (weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest (shiftPair (dilateBump (narrowG 0) lam) 1 L)
          (shiftPair (dilateBump (narrowG 0) lam) 1 L))).re :=
  riemannHypothesis_iff_dilatedShiftPair_nonneg (contDiff_narrowG 0) (narrowG_supp 0)
    (fun _ => (narrowBump 0).nonneg) (narrowBump 0).integral_pos.ne'

end

end RHTower.WeilOneSided
