import GaloisForLFunctions.RHTower.ThetaCuspComplexStrip
import GaloisForLFunctions.RHTower.StripHorizontalShift
import GaloisForLFunctions.RHTower.KreinCompletionPinning
import GaloisForLFunctions.RHTower.RiemannKernelCuspSeries

/-!
# Tilted Riemann kernels

For `0 ≤ θ < π/4` the horizontal slice `Φ_θ(u) = Φ(u + iθ)` of the complexified theta-cusp source
is an exactly radical kernel: a contour shift inside the strip `|Im w| < π/4` gives
`Φ̂_θ(z) = e^{zθ} Ξ(z)`.  The tilt `e^{τθ}` undoes the archimedean decay `|Ξ(τ)| ≍ e^{-πτ/4}` of
the untilted kernel, while `Φ_θ` keeps the double-exponential decay `e^{-π cos(2θ) e^{2|u|}}`.

* `paperFT_tiltedPhi`: `Φ̂_θ(z) = e^{zθ} Ξ(z)` for `|Im z| ≤ 1/2`.
* `norm_tiltedPhi_le_of_le_abs`: `‖Φ_θ(u)‖ ≤ M e^{9|u|/2} e^{-π cos(2θ) e^{2|u|}}` once
  `π cos(2θ) e^{2|u|} ≥ 1`.
* `integral_norm_tiltedTail_mul_exp_le`: the part of `Φ_θ` beyond `|u| = U` has weighted mass
  `∫ |Φ_{θ,>U}| e^{|u|/2} ≤ 2M e^{6U} e^{-π cos(2θ) e^{2U}}`.
* `paperFT_tiltedCore_at_zero`: at every nontrivial zero both Weil evaluation points of the
  truncated kernel see only the tail.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real
open Bottcher Zeta23

namespace RHTower

noncomputable section

local notation "Φ" => riemannPhiKernel

/-! ## The complexified source on the real line is Riemann's kernel -/

theorem eval_riemannCuspPoly (X : ℝ) :
    riemannCuspPoly.eval X = 4 * π ^ 2 * X ^ 2 - 6 * π * X := by
  simp only [riemannCuspPoly, cuspDeriv, Polynomial.eval_sub, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.derivative_one, Polynomial.eval_zero,
    Polynomial.derivative_sub, Polynomial.derivative_mul, Polynomial.derivative_C,
    Polynomial.derivative_X, zero_mul, zero_add, mul_zero, add_zero, mul_one]
  ring

theorem thetaCuspSourceTerm_succ_eq_cuspTerm (x : ℝ) (n : ℕ) :
    thetaCuspSourceTerm x (n + 1) = cuspTerm riemannCuspPoly (n + 1) x := by
  rw [thetaCuspSourceTerm, cuspTerm, eval_riemannCuspPoly, thetaCuspSeed]
  have h2 : Real.exp (2 * x) = Real.exp x ^ 2 := by
    rw [sq, ← Real.exp_add]; ring_nf
  rw [h2]
  push_cast
  ring_nf

theorem thetaCuspFullSource_eq_cuspSeries (x : ℝ) :
    thetaCuspFullSource x = cuspSeries riemannCuspPoly x := by
  rw [thetaCuspFullSource, cuspSeries, (summable_thetaCuspSourceTerm x).tsum_eq_zero_add]
  have h0 : thetaCuspSourceTerm x 0 = 0 := by simp [thetaCuspSourceTerm, thetaCuspSeed]
  rw [h0, zero_add]
  exact tsum_congr fun n => thetaCuspSourceTerm_succ_eq_cuspTerm x n

/-- On the real line the complexified theta-cusp source is Riemann's kernel `Φ`. -/
theorem thetaCuspStripSource_ofReal_eq (x : ℝ) : thetaCuspStripSource (x : ℂ) = Φ x := by
  rw [thetaCuspStripSource_ofReal, riemannPhiKernel_eq_cuspSeries, thetaCuspFullSource_eq_cuspSeries]

/-! ## The tilted kernel -/

/-- The tilted Riemann kernel `Φ_θ(u) = Φ(u + iθ)`. -/
def tiltedPhi (θ u : ℝ) : ℂ := thetaCuspStripSource ((u : ℂ) + (θ : ℂ) * I)

theorem continuous_tiltedPhi {θ : ℝ} (hθ : |θ| < π / 4) : Continuous (tiltedPhi θ) :=
  continuous_thetaCuspStripSource_horizontal hθ

theorem exists_norm_tiltedPhi_le {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : 2 * θ < π / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, ‖tiltedPhi θ u‖ ≤ C * Real.exp (-|u|) := by
  obtain ⟨C, hC, hb⟩ := exists_norm_thetaCuspStripSource_le hθ0 hθ
  refine ⟨C, hC, fun u => ?_⟩
  have h := hb ((u : ℂ) + (θ : ℂ) * I) (by simp [abs_of_nonneg hθ0])
  simpa [tiltedPhi] using h

theorem norm_cexp_I_mul_mul_le (z w : ℂ) {θ : ℝ} (hw : |w.im| ≤ θ) :
    ‖cexp (I * z * w)‖ ≤ Real.exp (‖z‖ * θ) * Real.exp (|z.im| * |w.re|) := by
  rw [Complex.norm_exp, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hre : (I * z * w).re = -(z.re * w.im) - z.im * w.re := by
    simp [Complex.mul_re, Complex.mul_im]; ring
  rw [hre]
  have h1 : -(z.re * w.im) ≤ ‖z‖ * θ := by
    calc -(z.re * w.im) ≤ |z.re * w.im| := neg_le_abs _
      _ = |z.re| * |w.im| := abs_mul _ _
      _ ≤ ‖z‖ * θ := mul_le_mul (Complex.abs_re_le_norm z) hw (abs_nonneg _) (norm_nonneg _)
  have h2 : -(z.im * w.re) ≤ |z.im| * |w.re| := by
    calc -(z.im * w.re) ≤ |z.im * w.re| := neg_le_abs _
      _ = |z.im| * |w.re| := abs_mul _ _
  linarith

/-- **The transform of the tilted kernel.**  For `0 ≤ θ < π/4` and `|Im z| ≤ 1/2`,
`Φ̂_θ(z) = e^{zθ} Ξ(z)`: the integrand `Φ(w) e^{izw}` is holomorphic on the strip and decays like
`e^{-|Re w|/2}`, so its line integral does not depend on the height. -/
theorem paperFT_tiltedPhi {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : 2 * θ < π / 2) {z : ℂ}
    (hz : |z.im| ≤ 1 / 2) :
    paperFT (tiltedPhi θ) z = cexp (z * θ) * riemannPhiTransform (1 / 2 + I * z) := by
  obtain ⟨C, hC, hb⟩ := exists_norm_thetaCuspStripSource_le hθ0 hθ
  set F : ℂ → ℂ := fun w => thetaCuspStripSource w * cexp (I * z * w) with hF
  have hθ4 : θ < π / 4 := by linarith
  have hdiff : ∀ w : ℂ, |w.im| ≤ θ → DifferentiableAt ℂ F w := by
    intro w hw
    have hmem : w ∈ thetaCuspStrip := by
      show |w.im| < π / 4
      linarith
    exact (differentiableAt_thetaCuspStripSource hmem).mul (by fun_prop)
  have hbound : ∀ w : ℂ, |w.im| ≤ θ →
      ‖F w‖ ≤ (C * Real.exp (‖z‖ * θ)) * Real.exp (-(1 / 2 * |w.re|)) := by
    intro w hw
    rw [hF, norm_mul]
    have h1 := hb w hw
    have h2 := norm_cexp_I_mul_mul_le z w hw
    have h3 : Real.exp (|z.im| * |w.re|) ≤ Real.exp (1 / 2 * |w.re|) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hz (abs_nonneg _))
    calc ‖thetaCuspStripSource w‖ * ‖cexp (I * z * w)‖
        ≤ (C * Real.exp (-|w.re|)) * (Real.exp (‖z‖ * θ) * Real.exp (1 / 2 * |w.re|)) :=
          mul_le_mul h1 (h2.trans (mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le))
            (norm_nonneg _) (by positivity)
      _ = (C * Real.exp (‖z‖ * θ)) * Real.exp (-(1 / 2 * |w.re|)) := by
          rw [show (C * Real.exp (-|w.re|)) * (Real.exp (‖z‖ * θ) * Real.exp (1 / 2 * |w.re|)) =
            (C * Real.exp (‖z‖ * θ)) * (Real.exp (-|w.re|) * Real.exp (1 / 2 * |w.re|)) by ring,
            ← Real.exp_add]
          congr 2; ring
  have hshift := integral_horizontal_shift_of_decay (c := θ) (r := 1 / 2) hθ0 (by norm_num)
    hdiff hbound
  have hL : (∫ x : ℝ, F ((x : ℂ) + (θ : ℂ) * I)) = cexp (-(z * θ)) * paperFT (tiltedPhi θ) z := by
    rw [paperFT_def, ← integral_const_mul]
    congr 1; funext x
    simp only [hF, tiltedPhi]
    have e : cexp (I * z * ((x : ℂ) + (θ : ℂ) * I)) = cexp (-(z * θ)) * cexp (I * z * x) := by
      rw [← Complex.exp_add]; congr 1; ring_nf; rw [Complex.I_sq]; ring
    rw [e]; ring
  have hR : (∫ x : ℝ, F (x : ℂ)) = riemannPhiTransform (1 / 2 + I * z) := by
    rw [← paperFT_riemannPhiKernel, paperFT_def]
    congr 1; funext x
    simp only [hF, thetaCuspStripSource_ofReal_eq]
  rw [hL, hR] at hshift
  have hne : cexp (-(z * θ)) ≠ 0 := Complex.exp_ne_zero _
  calc paperFT (tiltedPhi θ) z = cexp (z * θ) * (cexp (-(z * θ)) * paperFT (tiltedPhi θ) z) := by
        rw [← mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul]
    _ = cexp (z * θ) * riemannPhiTransform (1 / 2 + I * z) := by rw [hshift]

/-! ## Double-exponential decay of the tilted kernel -/

/-- `M = 2π (2π + 3) e ∑ n⁴ e^{-n²}`. -/
def tiltedPhiTailConst : ℝ :=
  2 * π * (2 * π + 3) * Real.exp 1 * ∑' n : ℕ, (n : ℝ) ^ 4 * Real.exp (-1 * (n : ℝ) ^ 2)

theorem tiltedPhiTailConst_nonneg : 0 ≤ tiltedPhiTailConst := by
  unfold tiltedPhiTailConst
  have : 0 ≤ ∑' n : ℕ, (n : ℝ) ^ 4 * Real.exp (-1 * (n : ℝ) ^ 2) :=
    tsum_nonneg fun n => by positivity
  have := Real.pi_pos
  positivity

/-- A Gaussian with rate `X ≥ 1` is dominated by `e^{-X}` times the unit Gaussian profile. -/
theorem pow_four_mul_exp_neg_le {X : ℝ} (hX : 1 ≤ X) (n : ℕ) :
    (n : ℝ) ^ 4 * Real.exp (-(X * (n : ℝ) ^ 2)) ≤
      Real.exp (-X) * (Real.exp 1 * ((n : ℝ) ^ 4 * Real.exp (-1 * (n : ℝ) ^ 2))) := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · have hn : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
      have : (1 : ℝ) ≤ n := by exact_mod_cast h
      nlinarith
    have hexp : Real.exp (-(X * (n : ℝ) ^ 2)) ≤ Real.exp (-X) * (Real.exp 1 * Real.exp (-1 * (n : ℝ) ^ 2)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith
    calc (n : ℝ) ^ 4 * Real.exp (-(X * (n : ℝ) ^ 2))
        ≤ (n : ℝ) ^ 4 * (Real.exp (-X) * (Real.exp 1 * Real.exp (-1 * (n : ℝ) ^ 2))) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = _ := by ring

/-- **Decay of the complexified source to the right of the origin.**  If `|Im z| ≤ θ`,
`0 ≤ Re z` and `X = π cos(2θ) e^{2 Re z} ≥ 1`, then `‖Φ(z)‖ ≤ M e^{9 Re z/2} e^{-X}`. -/
theorem norm_thetaCuspStripSource_le_of_rate {θ : ℝ} (hθ : 2 * θ ≤ π / 2) {z : ℂ}
    (hz : |z.im| ≤ θ) (hre : 0 ≤ z.re)
    (hX : 1 ≤ π * Real.cos (2 * θ) * Real.exp (2 * z.re)) :
    ‖thetaCuspStripSource z‖ ≤
      tiltedPhiTailConst * Real.exp (9 / 2 * z.re) *
        Real.exp (-(π * Real.cos (2 * θ) * Real.exp (2 * z.re))) := by
  set X := π * Real.cos (2 * θ) * Real.exp (2 * z.re) with hXdef
  set g : ℕ → ℝ := fun n => (n : ℝ) ^ 4 * Real.exp (-1 * (n : ℝ) ^ 2) with hg
  have hgs : Summable g := summable_pow_mul_exp_neg_nat_sq 4 (by norm_num : (0 : ℝ) < 1)
  set K : ℝ := 2 * π * (2 * π + 3) * Real.exp (9 / 2 * z.re) * Real.exp (-X) * Real.exp 1
    with hK
  have hK0 : 0 ≤ K := by rw [hK]; have := Real.pi_pos; positivity
  have hterm : ∀ n : ℕ, ‖thetaCuspComplexTerm z n‖ ≤ K * g n := by
    intro n
    have h := norm_thetaCuspComplexTerm_le_pointwise hθ hz n
    have he4 : Real.exp (2 * z.re) ≤ Real.exp (4 * z.re) := Real.exp_le_exp.mpr (by linarith)
    have hn2 : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 4 := by
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · subst h0; simp
      · have : (1 : ℝ) ≤ n := by exact_mod_cast h0
        have h1 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := one_le_pow₀ this
        have e : (n : ℝ) ^ 4 = (n : ℝ) ^ 2 * (n : ℝ) ^ 2 := by ring
        rw [e]; nlinarith
    have hpoly : 2 * π * (n : ℝ) ^ 4 * Real.exp (4 * z.re) + 3 * (n : ℝ) ^ 2 * Real.exp (2 * z.re) ≤
        (2 * π + 3) * (n : ℝ) ^ 4 * Real.exp (4 * z.re) := by
      have : 3 * (n : ℝ) ^ 2 * Real.exp (2 * z.re) ≤ 3 * (n : ℝ) ^ 4 * Real.exp (4 * z.re) := by
        have := mul_le_mul hn2 he4 (Real.exp_pos _).le (by positivity)
        nlinarith
      nlinarith
    have hgauss : Real.exp (-(π * Real.cos (2 * θ)) * (n : ℝ) ^ 2 * Real.exp (2 * z.re)) =
        Real.exp (-(X * (n : ℝ) ^ 2)) := by
      rw [hXdef]; congr 1; ring
    have hpw := pow_four_mul_exp_neg_le hX n
    calc ‖thetaCuspComplexTerm z n‖
        ≤ Real.exp (z.re / 2) * (2 * π) *
            ((2 * π + 3) * (n : ℝ) ^ 4 * Real.exp (4 * z.re)) *
            Real.exp (-(X * (n : ℝ) ^ 2)) := by
          rw [← hgauss]
          refine h.trans ?_
          gcongr
      _ = 2 * π * (2 * π + 3) * (Real.exp (z.re / 2) * Real.exp (4 * z.re)) *
            ((n : ℝ) ^ 4 * Real.exp (-(X * (n : ℝ) ^ 2))) := by ring
      _ ≤ 2 * π * (2 * π + 3) * (Real.exp (z.re / 2) * Real.exp (4 * z.re)) *
            (Real.exp (-X) * (Real.exp 1 * g n)) := by
          have := Real.pi_pos
          exact mul_le_mul_of_nonneg_left hpw (by positivity)
      _ = K * g n := by
          rw [hK, ← Real.exp_add]
          rw [show z.re / 2 + 4 * z.re = 9 / 2 * z.re by ring]
          ring
  have hsum : Summable (fun n => ‖thetaCuspComplexTerm z n‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm (hgs.mul_left K)
  calc ‖thetaCuspStripSource z‖ = ‖∑' n, thetaCuspComplexTerm z n‖ := rfl
    _ ≤ ∑' n, ‖thetaCuspComplexTerm z n‖ := norm_tsum_le_tsum_norm hsum
    _ ≤ ∑' n, K * g n := hsum.tsum_le_tsum hterm (hgs.mul_left K)
    _ = K * ∑' n, g n := tsum_mul_left
    _ = tiltedPhiTailConst * Real.exp (9 / 2 * z.re) * Real.exp (-X) := by
        rw [hK, tiltedPhiTailConst]; ring

/-- **Double-exponential decay of the tilted kernel in both directions.**  For `0 ≤ θ < π/4`, once
`π cos(2θ) e^{2|u|} ≥ 1`: `‖Φ_θ(u)‖ ≤ M e^{9|u|/2} e^{-π cos(2θ) e^{2|u|}}`. -/
theorem norm_tiltedPhi_le_of_rate {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : 2 * θ < π / 2) {u : ℝ}
    (hX : 1 ≤ π * Real.cos (2 * θ) * Real.exp (2 * |u|)) :
    ‖tiltedPhi θ u‖ ≤
      tiltedPhiTailConst * Real.exp (9 / 2 * |u|) *
        Real.exp (-(π * Real.cos (2 * θ) * Real.exp (2 * |u|))) := by
  rcases le_total 0 u with hu | hu
  · rw [abs_of_nonneg hu] at hX ⊢
    have h := norm_thetaCuspStripSource_le_of_rate hθ.le (z := (u : ℂ) + (θ : ℂ) * I)
      (by simp [abs_of_nonneg hθ0]) (by simpa using hu) (by simpa using hX)
    simpa [tiltedPhi] using h
  · rw [abs_of_nonpos hu] at hX ⊢
    have hmem : ((u : ℂ) + (θ : ℂ) * I) ∈ thetaCuspStrip := by
      show |((u : ℂ) + (θ : ℂ) * I).im| < π / 4
      simp [abs_of_nonneg hθ0]; linarith
    have hneg : tiltedPhi θ u = thetaCuspStripSource (-((u : ℂ) + (θ : ℂ) * I)) := by
      rw [tiltedPhi, thetaCuspStripSource_neg hmem]
    have h := norm_thetaCuspStripSource_le_of_rate hθ.le (z := -((u : ℂ) + (θ : ℂ) * I))
      (by simp [abs_of_nonneg hθ0]) (by simpa using hu) (by simpa using hX)
    rw [hneg]
    simpa using h

/-! ## Truncation -/

/-- The tail of the tilted kernel beyond `|u| = U`. -/
def tiltedTail (U θ : ℝ) : ℝ → ℂ := {u : ℝ | U < |u|}.indicator (tiltedPhi θ)

/-- The tilted kernel truncated to `[-U, U]`. -/
def tiltedCore (U θ : ℝ) : ℝ → ℂ := (Icc (-U) U).indicator (tiltedPhi θ)

theorem tiltedCore_add_tail (U θ u : ℝ) : tiltedCore U θ u + tiltedTail U θ u = tiltedPhi θ u := by
  unfold tiltedCore tiltedTail
  by_cases h : U < |u|
  · have h' : u ∉ Icc (-U) U := fun hm => by
      have := abs_le.mpr ⟨hm.1, hm.2⟩; linarith
    rw [indicator_of_notMem h', indicator_of_mem (show u ∈ {u : ℝ | U < |u|} from h), zero_add]
  · push Not at h
    have h' : u ∈ Icc (-U) U := ⟨(abs_le.mp h).1, (abs_le.mp h).2⟩
    rw [indicator_of_mem h', indicator_of_notMem (show u ∉ {u : ℝ | U < |u|} from not_lt.mpr h),
      add_zero]

theorem measurableSet_tiltedTailSet (U : ℝ) : MeasurableSet {u : ℝ | U < |u|} :=
  measurableSet_lt measurable_const measurable_norm

theorem integrable_norm_tiltedPhi_mul_exp {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : 2 * θ < π / 2) :
    Integrable (fun u : ℝ => ‖tiltedPhi θ u‖ * Real.exp (1 / 2 * |u|)) := by
  obtain ⟨C, hC, hb⟩ := exists_norm_tiltedPhi_le hθ0 hθ
  have hθ4 : |θ| < π / 4 := by rw [abs_of_nonneg hθ0]; linarith
  refine Integrable.mono' ((integrable_exp_neg_mul_abs' (c := 1 / 2) (by norm_num)).const_mul C)
    (((continuous_tiltedPhi hθ4).norm.mul (by fun_prop)).aestronglyMeasurable)
    (Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc ‖tiltedPhi θ u‖ * Real.exp (1 / 2 * |u|) ≤ C * Real.exp (-|u|) * Real.exp (1 / 2 * |u|) :=
        mul_le_mul_of_nonneg_right (hb u) (Real.exp_pos _).le
    _ = C * Real.exp (-(1 / 2 * |u|)) := by
        rw [mul_assoc, ← Real.exp_add]; congr 2; ring

theorem integrable_tiltedPhi_mul_cexp {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : 2 * θ < π / 2) {z : ℂ}
    (hz : |z.im| ≤ 1 / 2) :
    Integrable (fun u : ℝ => tiltedPhi θ u * cexp (I * z * u)) := by
  have hθ4 : |θ| < π / 4 := by rw [abs_of_nonneg hθ0]; linarith
  refine Integrable.mono' (integrable_norm_tiltedPhi_mul_exp hθ0 hθ)
    (((continuous_tiltedPhi hθ4).mul (by fun_prop)).aestronglyMeasurable)
    (Eventually.of_forall fun u => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_cexp_I_mul_le_exp hz u) (norm_nonneg _)

theorem integrable_tiltedTail_mul_cexp {U θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : 2 * θ < π / 2) {z : ℂ}
    (hz : |z.im| ≤ 1 / 2) :
    Integrable (fun u : ℝ => tiltedTail U θ u * cexp (I * z * u)) := by
  have h := (integrable_tiltedPhi_mul_cexp hθ0 hθ hz).indicator (measurableSet_tiltedTailSet U)
  refine h.congr (Eventually.of_forall fun u => ?_)
  simp only [tiltedTail, indicator]
  split_ifs <;> simp

theorem integrable_tiltedCore_mul_cexp {U θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : 2 * θ < π / 2) (z : ℂ) :
    Integrable (fun u : ℝ => tiltedCore U θ u * cexp (I * z * u)) := by
  have hθ4 : |θ| < π / 4 := by rw [abs_of_nonneg hθ0]; linarith
  have hc : ContinuousOn (fun u : ℝ => tiltedPhi θ u * cexp (I * z * u)) (Icc (-U) U) :=
    ((continuous_tiltedPhi hθ4).mul (by fun_prop)).continuousOn
  have h := (hc.integrableOn_Icc (μ := (volume : Measure ℝ))).integrable_indicator
    measurableSet_Icc
  refine h.congr (Eventually.of_forall fun u => ?_)
  simp only [tiltedCore, indicator]
  split_ifs <;> simp

theorem integrable_tiltedCore {U θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : 2 * θ < π / 2) :
    Integrable (tiltedCore U θ) := by
  have h := integrable_tiltedCore_mul_cexp (U := U) hθ0 hθ 0
  simpa using h

theorem paperFT_tiltedCore_eq {U θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : 2 * θ < π / 2) {z : ℂ}
    (hz : |z.im| ≤ 1 / 2) :
    paperFT (tiltedCore U θ) z =
      cexp (z * θ) * riemannPhiTransform (1 / 2 + I * z) - paperFT (tiltedTail U θ) z := by
  rw [← paperFT_tiltedPhi hθ0 hθ hz]
  unfold paperFT
  rw [eq_sub_iff_add_eq, ← integral_add (integrable_tiltedCore_mul_cexp hθ0 hθ z)
    (integrable_tiltedTail_mul_cexp hθ0 hθ hz)]
  congr 1; funext x
  rw [← add_mul, tiltedCore_add_tail]

/-- At a nontrivial zero both Weil evaluation points of the truncated tilted kernel see only the
tail. -/
theorem paperFT_tiltedCore_at_zero {U θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : 2 * θ < π / 2) {ρ : ℂ}
    (hρ : ρ ∈ zetaZeroConfig.carrier) :
    paperFT (tiltedCore U θ) (gammaOf ρ) = -paperFT (tiltedTail U θ) (gammaOf ρ) ∧
      paperFT (tiltedCore U θ) ((starRingEnd ℂ) (gammaOf ρ)) =
        -paperFT (tiltedTail U θ) ((starRingEnd ℂ) (gammaOf ρ)) := by
  have hz : ∀ σ ∈ zetaZeroConfig.carrier, riemannPhiTransform σ = 0 := by
    intro σ hσ
    rw [zetaZeroConfig_carrier] at hσ
    exact riemannPhiTransform_eq_zero_of_nontrivial hσ.1 hσ.2.1 hσ.2.2
  have hstrip : 0 < ρ.re ∧ ρ.re < 1 := by
    have h : IsNontrivialZero ρ := hρ
    exact ⟨h.2.1, h.2.2⟩
  have hIm : |(gammaOf ρ).im| ≤ 1 / 2 := (WeilEF.abs_gammaOf_im_lt hstrip).le
  have hIm' : |((starRingEnd ℂ) (gammaOf ρ)).im| ≤ 1 / 2 := by
    rw [Complex.conj_im, abs_neg]; exact hIm
  have h1 : 1 / 2 + I * gammaOf ρ = ρ := by
    unfold gammaOf; field_simp; ring
  have h2 : 1 / 2 + I * (starRingEnd ℂ) (gammaOf ρ) = Zeta23.reflect ρ := by
    unfold gammaOf Zeta23.reflect
    apply Complex.ext
    · simp; ring
    · simp
  refine ⟨?_, ?_⟩
  · rw [paperFT_tiltedCore_eq hθ0 hθ hIm, h1, hz ρ hρ, mul_zero, zero_sub]
  · rw [paperFT_tiltedCore_eq hθ0 hθ hIm', h2, hz _ (zetaZeroConfig.reflect_mem ρ hρ), mul_zero,
      zero_sub]

theorem norm_paperFT_tiltedTail_le {U θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : 2 * θ < π / 2) {z : ℂ}
    (hz : |z.im| ≤ 1 / 2) :
    ‖paperFT (tiltedTail U θ) z‖ ≤ ∫ u : ℝ, ‖tiltedTail U θ u‖ * Real.exp (1 / 2 * |u|) := by
  have hθ4 : |θ| < π / 4 := by rw [abs_of_nonneg hθ0]; linarith
  unfold paperFT
  refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
    (Eventually.of_forall fun u => norm_nonneg _) ?_ (Eventually.of_forall fun u => ?_))
  · refine Integrable.mono' (integrable_norm_tiltedPhi_mul_exp hθ0 hθ)
      ((show AEStronglyMeasurable (tiltedTail U θ) volume from
        (continuous_tiltedPhi hθ4).aestronglyMeasurable.indicator
          (measurableSet_tiltedTailSet U)).norm.mul
        (by fun_prop : Continuous fun u : ℝ => Real.exp (1 / 2 * |u|)).aestronglyMeasurable)
      (Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    simp only [tiltedTail, indicator]; split_ifs <;> simp
  · simp only
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_cexp_I_mul_le_exp hz u) (norm_nonneg _)

/-- Past the point where `2 π c e^{2U} ≥ 6`, the profile `v ↦ 6v - π c e^{2v}` decreases. -/
theorem six_mul_sub_rate_le {c U v : ℝ} (hc : 0 ≤ c) (hU : 3 ≤ π * c * Real.exp (2 * U))
    (hv : U ≤ v) :
    6 * v - π * c * Real.exp (2 * v) ≤ 6 * U - π * c * Real.exp (2 * U) := by
  have hexp : Real.exp (2 * U) * (1 + 2 * (v - U)) ≤ Real.exp (2 * v) := by
    have h := Real.add_one_le_exp (2 * (v - U))
    have e : Real.exp (2 * v) = Real.exp (2 * U) * Real.exp (2 * (v - U)) := by
      rw [← Real.exp_add]; ring_nf
    rw [e]
    exact mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
  have hpc : 0 ≤ π * c := by have := Real.pi_pos; positivity
  have h1 : π * c * (Real.exp (2 * U) * (1 + 2 * (v - U))) ≤ π * c * Real.exp (2 * v) :=
    mul_le_mul_of_nonneg_left hexp hpc
  nlinarith

/-- **The weighted tail mass of the tilted kernel.**  If `U ≥ 0` and `π cos(2θ) e^{2U} ≥ 3`, then
`∫ ‖Φ_{θ,>U}‖ e^{|u|/2} ≤ 2M e^{6U} e^{-π cos(2θ) e^{2U}}`. -/
theorem integral_norm_tiltedTail_mul_exp_le {U θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : 2 * θ < π / 2)
    (hU : 3 ≤ π * Real.cos (2 * θ) * Real.exp (2 * U)) :
    ∫ u : ℝ, ‖tiltedTail U θ u‖ * Real.exp (1 / 2 * |u|) ≤
      2 * tiltedPhiTailConst * Real.exp (6 * U) *
        Real.exp (-(π * Real.cos (2 * θ) * Real.exp (2 * U))) := by
  have hθ4 : |θ| < π / 4 := by rw [abs_of_nonneg hθ0]; linarith
  set c := Real.cos (2 * θ) with hcdef
  have hc : 0 ≤ c := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith⟩
  set K := tiltedPhiTailConst * Real.exp (6 * U) * Real.exp (-(π * c * Real.exp (2 * U))) with hK
  have hM := tiltedPhiTailConst_nonneg
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hpt : ∀ u : ℝ, ‖tiltedTail U θ u‖ * Real.exp (1 / 2 * |u|) ≤ K * Real.exp (-|u|) := by
    intro u
    simp only [tiltedTail, indicator]
    split_ifs with h
    · have hu : U < |u| := h
      have hX : 1 ≤ π * c * Real.exp (2 * |u|) := by
        have : Real.exp (2 * U) ≤ Real.exp (2 * |u|) := Real.exp_le_exp.mpr (by linarith)
        have hpc : 0 ≤ π * c := by have := Real.pi_pos; positivity
        nlinarith [mul_le_mul_of_nonneg_left this hpc]
      have hb := norm_tiltedPhi_le_of_rate hθ0 hθ hX
      have hmono := six_mul_sub_rate_le hc hU hu.le
      calc ‖tiltedPhi θ u‖ * Real.exp (1 / 2 * |u|)
          ≤ tiltedPhiTailConst * Real.exp (9 / 2 * |u|) *
              Real.exp (-(π * c * Real.exp (2 * |u|))) * Real.exp (1 / 2 * |u|) :=
            mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le
        _ = tiltedPhiTailConst * Real.exp (6 * |u| - π * c * Real.exp (2 * |u|)) *
              Real.exp (-|u|) := by
            have e1 : Real.exp (9 / 2 * |u|) * Real.exp (-(π * c * Real.exp (2 * |u|))) *
                Real.exp (1 / 2 * |u|) =
                Real.exp (6 * |u| - π * c * Real.exp (2 * |u|)) * Real.exp (-|u|) := by
              rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
            calc tiltedPhiTailConst * Real.exp (9 / 2 * |u|) *
                  Real.exp (-(π * c * Real.exp (2 * |u|))) * Real.exp (1 / 2 * |u|)
                = tiltedPhiTailConst * (Real.exp (9 / 2 * |u|) *
                    Real.exp (-(π * c * Real.exp (2 * |u|))) * Real.exp (1 / 2 * |u|)) := by ring
              _ = _ := by rw [e1]; ring
        _ ≤ tiltedPhiTailConst * Real.exp (6 * U - π * c * Real.exp (2 * U)) *
              Real.exp (-|u|) := by gcongr
        _ = K * Real.exp (-|u|) := by
            rw [hK, sub_eq_add_neg, Real.exp_add]; ring
    · simp only [norm_zero, zero_mul]; positivity
  have hint : Integrable (fun u : ℝ => K * Real.exp (-|u|)) :=
    (integrable_exp_neg_mul_abs' (c := 1) (by norm_num)).const_mul K |>.congr
      (Eventually.of_forall fun u => by simp)
  have hmeas : AEStronglyMeasurable (fun u : ℝ => ‖tiltedTail U θ u‖ * Real.exp (1 / 2 * |u|))
      volume :=
    ((continuous_tiltedPhi hθ4).aestronglyMeasurable.indicator
      (measurableSet_tiltedTailSet U)).norm.mul (by fun_prop : Continuous fun u : ℝ =>
        Real.exp (1 / 2 * |u|)).aestronglyMeasurable
  have hle := integral_mono_of_nonneg (Eventually.of_forall fun u => by positivity) hint
    (Eventually.of_forall hpt)
  have hexpint : ∫ u : ℝ, Real.exp (-|u|) = 2 := integral_exp_neg_abs
  refine hle.trans (le_of_eq ?_)
  rw [integral_const_mul, hexpint, hK]; ring

end

end RHTower
