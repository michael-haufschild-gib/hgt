import GaloisForLFunctions.GrowingWindowsOfSpecZ.TheSchurParametersOfSpecZ
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.WeilsFormIsContinuousInTheLevyNorm
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Topology.Instances.Matrix

/-!
# The continuum canonical system of a bump is its jet Hankel system

DRAFT
-/

open MeasureTheory Set Filter Topology
open scoped ContDiff

noncomputable section

namespace GaloisForLFunctions.SignedWindowCriticality

open ArithmeticCastelnuovoSeveri SpacingScaleHarmonicAnalysis GrowingWindowsOfSpecZ
open DimensionZeroGeometryOfSpecZ
open _root_.RHTower (levyEnergy primeSum gammaHardyPhaseRate coshHalfMoment sinhHalfMoment)

/-! ### Forward differences -/


/-- The iterated forward difference of a translate is the translate of the difference. -/
theorem fwdDiff_iter_comp_add' (h : ℝ) (g : ℝ → ℝ) (c : ℝ) (k : ℕ) (u : ℝ) :
    (fwdDiff h)^[k] (fun x => g (x + c)) u = (fwdDiff h)^[k] g (u + c) :=
  fwdDiff_iter_comp_add h g c k u

/-- One forward difference of a `C^k` function is `C^k`. -/
theorem contDiff_fwdDiff {k : ℕ} {g : ℝ → ℝ} (hg : ContDiff ℝ k g) (h : ℝ) :
    ContDiff ℝ k (fwdDiff h g) :=
  (hg.comp (contDiff_id.add contDiff_const)).sub hg

/-- The iterated derivative of a forward difference is the forward difference of the iterated
derivative. -/
theorem iteratedDeriv_fwdDiff {k : ℕ} {g : ℝ → ℝ} (hg : ContDiff ℝ k g) (h u : ℝ) :
    iteratedDeriv k (fwdDiff h g) u = iteratedDeriv k g (u + h) - iteratedDeriv k g u := by
  have e : fwdDiff h g = (fun x => g (x + h)) - g := rfl
  have h1 : ContDiff ℝ k (fun x => g (x + h)) := hg.comp (contDiff_id.add contDiff_const)
  rw [e, iteratedDeriv_sub h1.contDiffAt hg.contDiffAt, iteratedDeriv_comp_add_const]

/-- **Mean value theorem for iterated forward differences.** For a `C^k` function and a step
`h > 0`, `Δ_h^k g(u) = h^k g^{(k)}(ξ)` for some `ξ ∈ [u, u + kh]`. -/
theorem exists_fwdDiff_iter_eq (k : ℕ) :
    ∀ {g : ℝ → ℝ}, ContDiff ℝ k g → ∀ {h : ℝ}, 0 < h → ∀ u : ℝ,
      ∃ ξ ∈ Icc u (u + k * h), (fwdDiff h)^[k] g u = h ^ k * iteratedDeriv k g ξ := by
  induction k with
  | zero =>
    intro g _ h _ u
    exact ⟨u, ⟨le_rfl, by simp⟩, by simp⟩
  | succ k ih =>
    intro g hg h hh u
    have hgk : ContDiff ℝ k g := hg.of_le (by exact_mod_cast Nat.le_succ k)
    obtain ⟨ξ', hξ', e⟩ := ih (contDiff_fwdDiff hgk h) hh u
    have hdiff : Differentiable ℝ (iteratedDeriv k g) :=
      hg.differentiable_iteratedDeriv k (by exact_mod_cast Nat.lt_succ_self k)
    obtain ⟨ξ, hξ, hmv⟩ := exists_deriv_eq_slope (iteratedDeriv k g) (by linarith : ξ' < ξ' + h)
      hdiff.continuous.continuousOn hdiff.differentiableOn
    rw [← iteratedDeriv_succ, add_sub_cancel_left] at hmv
    refine ⟨ξ, ⟨by linarith [hξ'.1, hξ.1], ?_⟩, ?_⟩
    · have := hξ'.2
      have := hξ.2
      push_cast
      nlinarith
    · rw [Function.iterate_succ_apply, e, iteratedDeriv_fwdDiff hgk, hmv]
      field_simp
      ring


/-- A function with derivative bounded by `M` is `M`-Lipschitz. -/
theorem abs_sub_le_of_abs_deriv_le {G : ℝ → ℝ} (hG : Differentiable ℝ G) {M : ℝ}
    (hM : ∀ x, |deriv G x| ≤ M) (x y : ℝ) : |G y - G x| ≤ M * |y - x| := by
  have := convex_univ.norm_image_sub_le_of_norm_deriv_le (f := G) (fun z _ => hG z)
    (fun z _ => by simpa only [Real.norm_eq_abs] using hM z) (mem_univ x) (mem_univ y)
  simpa only [Real.norm_eq_abs] using this

/-- The iterated forward difference is additive. -/
theorem fwdDiff_iter_sub (h : ℝ) (k : ℕ) :
    ∀ f g : ℝ → ℝ, (fwdDiff h)^[k] (f - g) = (fwdDiff h)^[k] f - (fwdDiff h)^[k] g := by
  induction k with
  | zero => intro f g; rfl
  | succ k ih =>
    intro f g
    have e : fwdDiff h (f - g) = fwdDiff h f - fwdDiff h g := by
      funext x; simp only [fwdDiff, Pi.sub_apply]; ring
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply, e,
      ih]

/-- `|Δ_h^k g(u)| ≤ h^k M` when `|g^{(k)}| ≤ M`. -/
theorem abs_fwdDiff_iter_le {k : ℕ} {g : ℝ → ℝ} (hg : ContDiff ℝ k g) {h : ℝ} (hh : 0 < h)
    {M : ℝ} (hM : ∀ x, |iteratedDeriv k g x| ≤ M) (u : ℝ) :
    |(fwdDiff h)^[k] g u| ≤ h ^ k * M := by
  obtain ⟨ξ, -, e⟩ := exists_fwdDiff_iter_eq k hg hh u
  rw [e, abs_mul, abs_of_pos (pow_pos hh k)]
  exact mul_le_mul_of_nonneg_left (hM ξ) (pow_pos hh k).le

/-- **The difference quotient approximates the derivative**:
`|Δ_h^k g(u)/h^k − g^{(k)}(u)| ≤ M k h` when `|g^{(k+1)}| ≤ M`. -/
theorem abs_fwdDiff_iter_div_sub_le {k : ℕ} {g : ℝ → ℝ} (hg : ContDiff ℝ (k + 1) g) {h : ℝ}
    (hh : 0 < h) {M : ℝ} (hM : ∀ x, |iteratedDeriv (k + 1) g x| ≤ M) (u : ℝ) :
    |(fwdDiff h)^[k] g u / h ^ k - iteratedDeriv k g u| ≤ M * (k * h) := by
  obtain ⟨ξ, hξ, e⟩ := exists_fwdDiff_iter_eq k (hg.of_le (by exact_mod_cast Nat.le_succ k)) hh u
  have hpow : h ^ k ≠ 0 := (pow_pos hh k).ne'
  rw [e, mul_div_cancel_left₀ _ hpow]
  have hdiff : Differentiable ℝ (iteratedDeriv k g) :=
    hg.differentiable_iteratedDeriv k (by exact_mod_cast Nat.lt_succ_self k)
  have hb := abs_sub_le_of_abs_deriv_le hdiff (fun x => by rw [← iteratedDeriv_succ]; exact hM x)
    u ξ
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hd : |ξ - u| ≤ k * h := by
    rw [abs_of_nonneg (by linarith [hξ.1])]; linarith [hξ.2]
  exact hb.trans (mul_le_mul_of_nonneg_left hd hM0)

/-- **The iterated forward difference is Lipschitz**: `|Δ_h^k g(u) − Δ_h^k g(v)| ≤ h^k M |u − v|`
when `|g^{(k+1)}| ≤ M`. -/
theorem abs_fwdDiff_iter_sub_le {k : ℕ} {g : ℝ → ℝ} (hg : ContDiff ℝ (k + 1) g) {h : ℝ}
    (hh : 0 < h) {M : ℝ} (hM : ∀ x, |iteratedDeriv (k + 1) g x| ≤ M) (u v : ℝ) :
    |(fwdDiff h)^[k] g u - (fwdDiff h)^[k] g v| ≤ h ^ k * (M * |u - v|) := by
  have hgk : ContDiff ℝ k g := hg.of_le (by exact_mod_cast Nat.le_succ k)
  set c := v - u
  have hshift : ContDiff ℝ k (fun x => g (x + c)) := hgk.comp (contDiff_id.add contDiff_const)
  have hv : (fwdDiff h)^[k] g v = (fwdDiff h)^[k] (fun x => g (x + c)) u := by
    rw [fwdDiff_iter_comp_add', add_sub_cancel]
  rw [hv, ← Pi.sub_apply, ← fwdDiff_iter_sub]
  have hψ : ContDiff ℝ k (g - fun x => g (x + c)) := hgk.sub hshift
  refine abs_fwdDiff_iter_le hψ hh (fun x => ?_) u
  have hdiff : Differentiable ℝ (iteratedDeriv k g) :=
    hg.differentiable_iteratedDeriv k (by exact_mod_cast Nat.lt_succ_self k)
  rw [iteratedDeriv_sub hgk.contDiffAt hshift.contDiffAt, iteratedDeriv_comp_add_const]
  have hb := abs_sub_le_of_abs_deriv_le hdiff (fun y => by rw [← iteratedDeriv_succ]; exact hM y)
    (x + c) x
  rw [show x - (x + c) = u - v by simp only [c]; ring] at hb
  exact hb


/-! ### Weil's form on a window -/


/-! ### Weil's form is bounded by the Lévy norm on a window -/

/-- The **Weil norm** `‖a‖₂² + levyEnergy a + ‖a‖₁²`. -/
def weilNormSq (a : ℝ → ℝ) : ℝ := (∫ u, a u ^ 2) + levyEnergy a + (∫ u, |a u|) ^ 2

theorem weilNormSq_nonneg (a : ℝ → ℝ) : 0 ≤ weilNormSq a :=
  add_nonneg (add_nonneg (integral_nonneg fun _ => sq_nonneg _) (levyEnergy_nonneg' a))
    (sq_nonneg _)

/-- The window constant `K_R` of the bound `|Q(a)| ≤ K_R ‖a‖²` on tests supported in `[−R, R]`. -/
def weilWindowConst (R : ℝ) : ℝ :=
  2 * |gammaHardyPhaseRate 0| + 2 * primeMass R + 1 + 4 * Real.cosh (R / 2) ^ 2

theorem weilWindowConst_nonneg (R : ℝ) : 0 ≤ weilWindowConst R := by
  unfold weilWindowConst; have := primeMass_nonneg R; positivity

theorem abs_primeSum_le {R : ℝ} {a : ℝ → ℝ} (ha : Continuous a) (hac : HasCompactSupport a)
    (haR : SupportedIn R a) : |primeSum a| ≤ 2 * primeMass R * ∫ u, a u ^ 2 := by
  have h := abs_primeSum_add_sub_le (f := fun _ => (0 : ℝ)) continuous_const
    HasCompactSupport.zero ha hac (fun _ _ => rfl) haR
  have e1 : (fun u => (fun _ => (0 : ℝ)) u + a u) = a := funext fun u => zero_add _
  have e2 : primeSum (fun _ => (0 : ℝ)) = 0 := by simp [primeSum]
  rw [e1, e2, sub_zero] at h
  simpa using h

/-- **Weil's form is bounded by the Weil norm**: `|Q(a)| ≤ K_R ‖a‖²` for `a` supported in
`[−R, R]`. -/
theorem abs_weilQuad_le {R : ℝ} {a : ℝ → ℝ} (ha : ContDiff ℝ 2 a) (hac : HasCompactSupport a)
    (haR : SupportedIn R a) : |weilQuad a| ≤ weilWindowConst R * weilNormSq a := by
  rw [weilQuad_eq ha hac]
  have hP := abs_primeSum_le ha.continuous hac haR
  have hC := abs_moment_le ha.continuous hac haR (by fun_prop)
    (fun u hu => abs_cosh_half_le hu)
  have hS := abs_moment_le ha.continuous hac haR (by fun_prop)
    (fun u hu => abs_sinh_half_le hu)
  have hC2 := pow_le_pow_left₀ (abs_nonneg _) hC 2
  have hS2 := pow_le_pow_left₀ (abs_nonneg _) hS 2
  rw [sq_abs, mul_pow] at hC2 hS2
  set A2 := ∫ u, a u ^ 2
  set L := levyEnergy a
  set A1 := ∫ u, |a u|
  set ch := Real.cosh (R / 2)
  set θ := gammaHardyPhaseRate 0
  set P := primeMass R
  have hA2 : 0 ≤ A2 := integral_nonneg fun _ => sq_nonneg _
  have hL : 0 ≤ L := levyEnergy_nonneg' a
  have hA1 : 0 ≤ A1 := integral_nonneg fun _ => abs_nonneg _
  have hP0 : 0 ≤ P := primeMass_nonneg R
  have hθ : |2 * θ * A2| ≤ 2 * |θ| * A2 := by
    rw [abs_mul, abs_mul, abs_two, abs_of_nonneg hA2]
  have hC' : coshHalfMoment a ^ 2 ≤ ch ^ 2 * A1 ^ 2 := hC2
  have hS' : sinhHalfMoment a ^ 2 ≤ ch ^ 2 * A1 ^ 2 := hS2
  have hbound : |2 * θ * A2 + L - primeSum a + (2 * coshHalfMoment a ^ 2 - 2 * sinhHalfMoment a ^ 2)|
      ≤ 2 * |θ| * A2 + L + 2 * P * A2 + 4 * ch ^ 2 * A1 ^ 2 := by
    rw [abs_le]
    constructor
    · nlinarith [abs_le.mp hθ, abs_le.mp hP, sq_nonneg (coshHalfMoment a)]
    · nlinarith [abs_le.mp hθ, abs_le.mp hP, sq_nonneg (sinhHalfMoment a)]
  refine hbound.trans ?_
  unfold weilWindowConst weilNormSq
  have hch : 0 ≤ ch ^ 2 := sq_nonneg _
  have hθ0 : 0 ≤ |θ| := abs_nonneg _
  nlinarith [mul_nonneg hθ0 hL, mul_nonneg hθ0 (sq_nonneg A1), mul_nonneg hP0 hL,
    mul_nonneg hP0 (sq_nonneg A1), mul_nonneg hch hA2, mul_nonneg hch hL, mul_nonneg hA2 hA2]


/-! ### Bilinear bookkeeping -/

theorem weilPair_add_right {f g₁ g₂ : ℝ → ℝ} (hf : f ∈ realTests) (h₁ : g₁ ∈ realTests)
    (h₂ : g₂ ∈ realTests) : weilPair f (g₁ + g₂) = weilPair f g₁ + weilPair f g₂ := by
  rw [weilPair_comm, weilPair_add_left h₁ h₂ hf, weilPair_comm g₁, weilPair_comm g₂]

theorem weilPair_neg_left (f g : ℝ → ℝ) : weilPair (-f) g = -weilPair f g := by
  have := weilPair_smul_left (-1) f g
  rw [neg_one_smul, neg_one_mul] at this
  exact this

theorem weilPair_neg_right (f g : ℝ → ℝ) : weilPair f (-g) = -weilPair f g := by
  rw [weilPair_comm, weilPair_neg_left, weilPair_comm]

theorem weilQuad_add {a b : ℝ → ℝ} (ha : a ∈ realTests) (hb : b ∈ realTests) :
    weilQuad (a + b) = weilQuad a + 2 * weilPair a b + weilQuad b := by
  show weilPair (a + b) (a + b) = weilPair a a + 2 * weilPair a b + weilPair b b
  rw [weilPair_add_left ha hb (realTests.add_mem ha hb), weilPair_add_right ha ha hb,
    weilPair_add_right hb ha hb, weilPair_comm b a]
  ring

/-- **Polarization**: `W(a, b) = (Q(a + b) − Q(a − b))/4`. -/
theorem weilPair_eq_polar {a b : ℝ → ℝ} (ha : a ∈ realTests) (hb : b ∈ realTests) :
    weilPair a b = (weilQuad (a + b) - weilQuad (a - b)) / 4 := by
  have hnb : -b ∈ realTests := realTests.neg_mem hb
  rw [weilQuad_add ha hb, show a - b = a + -b from sub_eq_add_neg a b, weilQuad_add ha hnb]
  have e1 : weilQuad (-b) = weilQuad b := by
    show weilPair (-b) (-b) = weilPair b b
    rw [weilPair_neg_left, weilPair_neg_right, neg_neg]
  rw [e1, weilPair_neg_right]
  ring

/-! ### The Weil norm is a quadratic seminorm -/

theorem levyEnergy_smul_eq (c : ℝ) (a : ℝ → ℝ) :
    levyEnergy (fun u => c * a u) = c ^ 2 * levyEnergy a := by
  unfold levyEnergy
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  simp only
  rw [show (fun u => (c * a u - c * a (u + x)) ^ 2) = fun u => c ^ 2 * (a u - a (u + x)) ^ 2 by
    funext u; ring, integral_const_mul]
  ring

theorem weilNormSq_const_mul (c : ℝ) (a : ℝ → ℝ) :
    weilNormSq (fun u => c * a u) = c ^ 2 * weilNormSq a := by
  unfold weilNormSq
  rw [levyEnergy_smul_eq]
  have e1 : (fun u => (c * a u) ^ 2) = fun u => c ^ 2 * a u ^ 2 := funext fun u => by ring
  have e2 : (fun u => |c * a u|) = fun u => |c| * |a u| := funext fun u => abs_mul _ _
  rw [e1, e2, integral_const_mul, integral_const_mul, mul_pow, sq_abs]
  ring

theorem two_mul_sqrt_mul_sqrt_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    2 * (Real.sqrt x * Real.sqrt y) ≤ x + y := by
  nlinarith [sq_nonneg (Real.sqrt x - Real.sqrt y), Real.sq_sqrt hx, Real.sq_sqrt hy]

/-- `‖a + b‖² ≤ 2‖a‖² + 2‖b‖²` for the Weil norm. -/
theorem weilNormSq_add_le {a b : ℝ → ℝ} (ha : ContDiff ℝ 2 a) (hac : HasCompactSupport a)
    (hb : ContDiff ℝ 2 b) (hbc : HasCompactSupport b) :
    weilNormSq (fun u => a u + b u) ≤ 2 * weilNormSq a + 2 * weilNormSq b := by
  unfold weilNormSq
  have hai := integrable_sq_of_continuous ha.continuous hac
  have hbi := integrable_sq_of_continuous hb.continuous hbc
  have hsq : ∫ u, (a u + b u) ^ 2 ≤ 2 * (∫ u, a u ^ 2) + 2 * ∫ u, b u ^ 2 := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hai.const_mul 2)
      (hbi.const_mul 2)]
    refine integral_mono (integrable_sq_of_continuous (ha.continuous.add hb.continuous)
      (hac.add hbc)) ((hai.const_mul 2).add (hbi.const_mul 2)) fun u => ?_
    nlinarith [sq_nonneg (a u - b u)]
  have hL := levyEnergy_add_le ha hac hb hbc
  have hL' := two_mul_sqrt_mul_sqrt_le (levyEnergy_nonneg' a) (levyEnergy_nonneg' b)
  have hai1 : Integrable fun u => |a u| := (ha.continuous.integrable_of_hasCompactSupport hac).abs
  have hbi1 : Integrable fun u => |b u| := (hb.continuous.integrable_of_hasCompactSupport hbc).abs
  have h1 : ∫ u, |a u + b u| ≤ (∫ u, |a u|) + ∫ u, |b u| := by
    rw [← integral_add hai1 hbi1]
    exact integral_mono ((ha.continuous.add hb.continuous).integrable_of_hasCompactSupport
      (hac.add hbc)).abs (hai1.add hbi1) fun u => abs_add_le _ _
  have h0 : 0 ≤ ∫ u, |a u + b u| := integral_nonneg fun _ => abs_nonneg _
  have hA : 0 ≤ ∫ u, |a u| := integral_nonneg fun _ => abs_nonneg _
  have hB : 0 ≤ ∫ u, |b u| := integral_nonneg fun _ => abs_nonneg _
  have h2 : (∫ u, |a u + b u|) ^ 2 ≤ 2 * (∫ u, |a u|) ^ 2 + 2 * (∫ u, |b u|) ^ 2 := by
    nlinarith [sq_nonneg ((∫ u, |a u|) - ∫ u, |b u|)]
  linarith

/-- **The Weil pairing is bounded on a window**: `|W(a, b)| ≤ K_R(‖a‖² + ‖b‖²)`. -/
theorem abs_weilPair_le_add {R : ℝ} {a b : ℝ → ℝ} (ha : a ∈ realTests) (hb : b ∈ realTests)
    (haR : SupportedIn R a) (hbR : SupportedIn R b) :
    |weilPair a b| ≤ weilWindowConst R * (weilNormSq a + weilNormSq b) := by
  have hnb : -b ∈ realTests := realTests.neg_mem hb
  have hnbR : SupportedIn R (-b) := fun u hu => by simp [hbR u hu]
  have hp := abs_weilQuad_le (realTests.add_mem ha hb).1 (realTests.add_mem ha hb).2
    (supportedIn_add haR hbR)
  have hm := abs_weilQuad_le (realTests.add_mem ha hnb).1 (realTests.add_mem ha hnb).2
    (supportedIn_add haR hnbR)
  have hNp := weilNormSq_add_le ha.1 ha.2 hb.1 hb.2
  have hNm := weilNormSq_add_le ha.1 ha.2 hnb.1 hnb.2
  have hnbN : weilNormSq (-b) = weilNormSq b := by
    have e : (-b) = fun u => (-1) * b u := by funext u; simp
    rw [e, weilNormSq_const_mul]; norm_num
  have e1 : (fun u => a u + b u) = a + b := rfl
  have e2 : (fun u => a u + (-b) u) = a - b := by funext u; simp [sub_eq_add_neg]
  rw [e1] at hNp
  rw [e2, hnbN] at hNm
  rw [show a + -b = a - b from (sub_eq_add_neg a b).symm] at hm
  rw [weilPair_eq_polar ha hb]
  have hK := weilWindowConst_nonneg R
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4), div_le_iff₀ (by norm_num : (0 : ℝ) < 4)]
  calc |weilQuad (a + b) - weilQuad (a - b)| ≤ |weilQuad (a + b)| + |weilQuad (a - b)| :=
        abs_sub _ _
    _ ≤ weilWindowConst R * weilNormSq (a + b) + weilWindowConst R * weilNormSq (a - b) :=
        add_le_add hp hm
    _ ≤ weilWindowConst R * (2 * weilNormSq a + 2 * weilNormSq b) +
          weilWindowConst R * (2 * weilNormSq a + 2 * weilNormSq b) :=
        add_le_add (mul_le_mul_of_nonneg_left hNp hK) (mul_le_mul_of_nonneg_left hNm hK)
    _ = weilWindowConst R * (weilNormSq a + weilNormSq b) * 4 := by ring

/-- A real inequality `|x| ≤ K(sA + B/s)` for every `s > 0` gives `|x| ≤ 2K√A√B`. -/
theorem abs_le_of_forall_scale {x A B K : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (h : ∀ s : ℝ, 0 < s → |x| ≤ K * (s * A + B / s)) :
    |x| ≤ 2 * K * (Real.sqrt A * Real.sqrt B) := by
  by_contra hlt
  push Not at hlt
  have hx : 0 < |x| := lt_of_le_of_lt (by positivity) hlt
  rcases hA.eq_or_lt with hA0 | hApos
  · -- `A = 0`: let `s → ∞`
    have := h (2 * K * B / |x| + 1) (by positivity)
    rw [← hA0, mul_zero, zero_add] at this
    have hs : 0 < 2 * K * B / |x| + 1 := by positivity
    rw [mul_div_assoc', le_div_iff₀ hs] at this
    have : 2 * K * B / |x| * |x| = 2 * K * B := div_mul_cancel₀ _ hx.ne'
    nlinarith [mul_nonneg hK hB]
  rcases hB.eq_or_lt with hB0 | hBpos
  · -- `B = 0`: let `s → 0`
    have hs : 0 < |x| / (2 * (K * A + 1)) := by positivity
    have := h _ hs
    rw [← hB0, zero_div, add_zero] at this
    have hKA : 0 ≤ K * A := mul_nonneg hK hA
    have : K * (|x| / (2 * (K * A + 1)) * A) = |x| * (K * A) / (2 * (K * A + 1)) := by
      field_simp
    have hlt2 : |x| * (K * A) / (2 * (K * A + 1)) < |x| := by
      rw [div_lt_iff₀ (by positivity)]; nlinarith
    linarith
  · -- `A, B > 0`: take `s = √B/√A`
    obtain ⟨α, hα, rfl⟩ : ∃ α, 0 < α ∧ A = α ^ 2 := ⟨_, Real.sqrt_pos.mpr hApos,
      (Real.sq_sqrt hA).symm⟩
    obtain ⟨β, hβ, rfl⟩ : ∃ β, 0 < β ∧ B = β ^ 2 := ⟨_, Real.sqrt_pos.mpr hBpos,
      (Real.sq_sqrt hB).symm⟩
    rw [Real.sqrt_sq hα.le, Real.sqrt_sq hβ.le] at hlt
    have := h (β / α) (div_pos hβ hα)
    have e : β / α * α ^ 2 + β ^ 2 / (β / α) = 2 * (α * β) := by
      field_simp; ring
    rw [e] at this
    linarith

/-- **The Weil pairing is bounded in the Weil norm**: `|W(a, b)| ≤ 2K_R‖a‖‖b‖`. -/
theorem abs_weilPair_le {R : ℝ} {a b : ℝ → ℝ} (ha : a ∈ realTests) (hb : b ∈ realTests)
    (haR : SupportedIn R a) (hbR : SupportedIn R b) :
    |weilPair a b| ≤
      2 * weilWindowConst R * (Real.sqrt (weilNormSq a) * Real.sqrt (weilNormSq b)) := by
  refine abs_le_of_forall_scale (weilNormSq_nonneg a) (weilNormSq_nonneg b)
    (weilWindowConst_nonneg R) fun s hs => ?_
  set t := Real.sqrt s
  have ht : 0 < t := Real.sqrt_pos.mpr hs
  have ht2 : t ^ 2 = s := Real.sq_sqrt hs.le
  have hta : (fun u => t * a u) ∈ realTests := realTests.smul_mem t ha
  have htb : (fun u => t⁻¹ * b u) ∈ realTests := realTests.smul_mem t⁻¹ hb
  have hscale : weilPair a b = weilPair (fun u => t * a u) (fun u => t⁻¹ * b u) := by
    have e1 : weilPair (fun u => t * a u) (fun u => t⁻¹ * b u) =
        t * (t⁻¹ * weilPair a b) := by
      rw [show (fun u => t * a u) = t • a from rfl, show (fun u => t⁻¹ * b u) = t⁻¹ • b from rfl,
        weilPair_smul_left, weilPair_smul_right]
    rw [e1, ← mul_assoc, mul_inv_cancel₀ ht.ne', one_mul]
  have hR1 : SupportedIn R (fun u => t * a u) := fun u hu => by simp [haR u hu]
  have hR2 : SupportedIn R (fun u => t⁻¹ * b u) := fun u hu => by simp [hbR u hu]
  have := abs_weilPair_le_add hta htb hR1 hR2
  rw [weilNormSq_const_mul, weilNormSq_const_mul, ht2, inv_pow, ht2] at this
  rw [hscale]
  calc _ ≤ _ := this
    _ = weilWindowConst R * (s * weilNormSq a + weilNormSq b / s) := by ring

/-- **Continuity of the Weil pairing**: perturbations whose Weil norm tends to `0` move the
pairing by a vanishing amount. -/
theorem tendsto_weilPair_add {ι : Type*} {l : Filter ι} {R : ℝ} {a b : ℝ → ℝ}
    {d e : ι → ℝ → ℝ} (ha : a ∈ realTests) (hb : b ∈ realTests) (hd : ∀ i, d i ∈ realTests)
    (he : ∀ i, e i ∈ realTests) (haR : SupportedIn R a) (hbR : SupportedIn R b)
    (hdR : ∀ᶠ i in l, SupportedIn R (d i)) (heR : ∀ᶠ i in l, SupportedIn R (e i))
    (hdN : Tendsto (fun i => weilNormSq (d i)) l (𝓝 0))
    (heN : Tendsto (fun i => weilNormSq (e i)) l (𝓝 0)) :
    Tendsto (fun i => weilPair (a + d i) (b + e i)) l (𝓝 (weilPair a b)) := by
  have hexp : ∀ i, weilPair (a + d i) (b + e i) =
      weilPair a b + (weilPair a (e i) + weilPair (d i) b + weilPair (d i) (e i)) := fun i => by
    rw [weilPair_add_left ha (hd i) (realTests.add_mem hb (he i)), weilPair_add_right ha hb (he i),
      weilPair_add_right (hd i) hb (he i)]
    ring
  simp_rw [hexp]
  rw [show 𝓝 (weilPair a b) = 𝓝 (weilPair a b + 0) by rw [add_zero]]
  refine tendsto_const_nhds.add ?_
  set K := weilWindowConst R
  have hsd : Tendsto (fun i => Real.sqrt (weilNormSq (d i))) l (𝓝 0) := by
    simpa using hdN.sqrt
  have hse : Tendsto (fun i => Real.sqrt (weilNormSq (e i))) l (𝓝 0) := by
    simpa using heN.sqrt
  have hbound : Tendsto (fun i => 2 * K * (Real.sqrt (weilNormSq a) * Real.sqrt (weilNormSq (e i)))
      + 2 * K * (Real.sqrt (weilNormSq (d i)) * Real.sqrt (weilNormSq b)) +
      2 * K * (Real.sqrt (weilNormSq (d i)) * Real.sqrt (weilNormSq (e i)))) l (𝓝 0) := by
    have := (((hse.const_mul (Real.sqrt (weilNormSq a))).const_mul (2 * K)).add
      ((hsd.mul_const (Real.sqrt (weilNormSq b))).const_mul (2 * K))).add
      ((hsd.mul hse).const_mul (2 * K))
    simpa using this
  refine squeeze_zero_norm' ?_ hbound
  filter_upwards [hdR, heR] with i hdi hei
  rw [Real.norm_eq_abs]
  refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
  · exact abs_weilPair_le ha (he i) haR hei
  · exact abs_weilPair_le (hd i) hb hdi hbR
  · exact abs_weilPair_le (hd i) (he i) hdi hei


/-! ### Uniformly small, uniformly Lipschitz perturbations are small in the Weil norm -/

theorem lt_abs_of_notMem_Icc' {R x : ℝ} (hx : x ∉ Icc (-R) R) : R < |x| := by
  simp only [mem_Icc, not_and_or, not_le] at hx
  rcases hx with hx | hx
  · exact lt_of_lt_of_le (by linarith) (neg_le_abs x)
  · exact lt_of_lt_of_le hx (le_abs_self x)

theorem hasCompactSupport_of_supportedIn' {R : ℝ} {g : ℝ → ℝ} (hg : SupportedIn R g) :
    HasCompactSupport g :=
  HasCompactSupport.intro (isCompact_Icc (a := -R) (b := R)) fun _ hx =>
    hg _ (lt_abs_of_notMem_Icc' hx)

theorem supportedIn_mono' {R R' : ℝ} {g : ℝ → ℝ} (hg : SupportedIn R g) (hRR : R ≤ R') :
    SupportedIn R' g := fun u hu => hg u (lt_of_le_of_lt hRR hu)

theorem exists_supportedIn_of_hasCompactSupport {φ : ℝ → ℝ} (hφc : HasCompactSupport φ) :
    ∃ R, 0 ≤ R ∧ SupportedIn R φ := by
  obtain ⟨R, hR⟩ := hφc.isCompact.isBounded.subset_closedBall 0
  refine ⟨max R 0, le_max_right _ _, fun u hu => ?_⟩
  by_contra h
  have := hR (subset_tsupport φ h)
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
  linarith [le_max_left R 0]

theorem integral_sq_le_of_abs_le {R ε : ℝ} {d : ℝ → ℝ} (hd : Continuous d)
    (hdc : HasCompactSupport d) (hdR : SupportedIn R d) (hR : 0 ≤ R) (hε : ∀ u, |d u| ≤ ε) :
    ∫ u, d u ^ 2 ≤ 2 * R * ε ^ 2 := by
  have hind : ∀ u, d u ^ 2 ≤ (Icc (-R) R).indicator (fun _ => ε ^ 2) u := by
    intro u
    by_cases hu : u ∈ Icc (-R) R
    · rw [indicator_of_mem hu, ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hε u) 2
    · rw [indicator_of_notMem hu, hdR u (lt_abs_of_notMem_Icc' hu)]
      simp
  calc ∫ u, d u ^ 2 ≤ ∫ u, (Icc (-R) R).indicator (fun _ => ε ^ 2) u :=
        integral_mono (integrable_sq_of_continuous hd hdc)
          ((continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc) hind
    _ = 2 * R * ε ^ 2 := by
        rw [integral_indicator_const _ measurableSet_Icc, Real.volume_real_Icc_of_le (by linarith),
          smul_eq_mul]
        ring

theorem integral_abs_le_of_abs_le {R ε : ℝ} {d : ℝ → ℝ} (hd : Continuous d)
    (hdc : HasCompactSupport d) (hdR : SupportedIn R d) (hR : 0 ≤ R) (hε : ∀ u, |d u| ≤ ε) :
    ∫ u, |d u| ≤ 2 * R * ε := by
  have hind : ∀ u, |d u| ≤ (Icc (-R) R).indicator (fun _ => ε) u := by
    intro u
    by_cases hu : u ∈ Icc (-R) R
    · rw [indicator_of_mem hu]; exact hε u
    · rw [indicator_of_notMem hu, hdR u (lt_abs_of_notMem_Icc' hu)]; simp
  calc ∫ u, |d u| ≤ ∫ u, (Icc (-R) R).indicator (fun _ => ε) u :=
        integral_mono (hd.integrable_of_hasCompactSupport hdc).abs
          ((continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc) hind
    _ = 2 * R * ε := by
        rw [integral_indicator_const _ measurableSet_Icc, Real.volume_real_Icc_of_le (by linarith),
          smul_eq_mul]
        ring

theorem levyLipConstant_nonneg' : 0 ≤ levyLipConstant := by
  unfold levyLipConstant
  have : Real.exp (-2) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have : 0 < 1 - Real.exp (-2) := by linarith
  positivity

/-- **A uniformly small, uniformly Lipschitz test is small in the Weil norm.** -/
theorem weilNormSq_le_of_uniform {R ε K : ℝ} {d : ℝ → ℝ} (hd : ContDiff ℝ 2 d)
    (hdc : HasCompactSupport d) (hdR : SupportedIn R d) (hR : 0 ≤ R) (hε : ∀ u, |d u| ≤ ε)
    (hK : ∀ u v, |d u - d v| ≤ K * |u - v|) :
    weilNormSq d ≤ (1 + levyLipConstant) * (2 * R * ε ^ 2) + Real.exp (1 / 2) * K * (2 * R * ε) +
      (2 * R * ε) ^ 2 := by
  have h2 := integral_sq_le_of_abs_le hd.continuous hdc hdR hR hε
  have h1 := integral_abs_le_of_abs_le hd.continuous hdc hdR hR hε
  have hL := levyEnergy_le_lipschitz hd hdc hK one_pos le_rfl
  simp only [div_one, Real.log_one, mul_zero, zero_add, mul_one] at hL
  have hK0 : 0 ≤ K := by
    have := hK 1 0
    norm_num at this
    linarith [abs_nonneg (d 1 - d 0)]
  have hC := levyLipConstant_nonneg'
  have hA1 : 0 ≤ ∫ u, |d u| := integral_nonneg fun _ => abs_nonneg _
  have hA2 : 0 ≤ ∫ u, d u ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have he : 0 ≤ Real.exp (1 / 2) * K := mul_nonneg (Real.exp_pos _).le hK0
  unfold weilNormSq
  have hsq : (∫ u, |d u|) ^ 2 ≤ (2 * R * ε) ^ 2 := pow_le_pow_left₀ hA1 h1 2
  nlinarith [mul_le_mul_of_nonneg_left h1 he, mul_le_mul_of_nonneg_left h2 hC]

/-! ### Jets and difference quotients of a smooth bump -/

theorem contDiff_fwdDiff' {n : WithTop ℕ∞} {g : ℝ → ℝ} (hg : ContDiff ℝ n g) (h : ℝ) :
    ContDiff ℝ n (fwdDiff h g) :=
  (hg.comp (contDiff_id.add contDiff_const)).sub hg

theorem contDiff_fwdDiff_iter {n : WithTop ℕ∞} {g : ℝ → ℝ} (hg : ContDiff ℝ n g) (h : ℝ) (k : ℕ) :
    ContDiff ℝ n ((fwdDiff h)^[k] g) := by
  induction k generalizing g with
  | zero => exact hg
  | succ k ih => rw [Function.iterate_succ_apply]; exact ih (contDiff_fwdDiff' hg h)

/-- A forward difference of step `h ≤ 1` widens the support by at most `1`. -/
theorem supportedIn_fwdDiff_iter {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (k : ℕ) :
    ∀ {R : ℝ} {g : ℝ → ℝ}, SupportedIn R g → SupportedIn (R + k) ((fwdDiff h)^[k] g) := by
  induction k with
  | zero => intro R g hg; simpa using hg
  | succ k ih =>
    intro R g hg
    rw [Function.iterate_succ_apply]
    have h1 : SupportedIn (R + 1) (fwdDiff h g) := by
      intro u hu
      have hu0 : g u = 0 := hg u (by linarith)
      have hu1 : g (u + h) = 0 := hg (u + h) (by
        rcases le_or_gt 0 u with h0 | h0
        · rw [abs_of_nonneg h0] at hu; rw [abs_of_nonneg (by linarith)]; linarith
        · rw [abs_of_neg h0] at hu
          have := neg_abs_le (u + h)
          have : u + h < -R := by linarith
          linarith [neg_le_abs (u + h)])
      simp [fwdDiff, hu0, hu1]
    have := ih h1
    rw [show R + 1 + (k : ℝ) = R + ((k + 1 : ℕ) : ℝ) by push_cast; ring] at this
    exact this

theorem iteratedDeriv_supportedIn {R : ℝ} {φ : ℝ → ℝ} (hφR : SupportedIn R φ) (k : ℕ) :
    SupportedIn R (iteratedDeriv k φ) := by
  intro u hu
  have hev : φ =ᶠ[𝓝 u] fun _ => (0 : ℝ) := by
    have hopen : IsOpen {x : ℝ | R < |x|} := isOpen_lt continuous_const continuous_abs
    filter_upwards [hopen.mem_nhds hu] with x hx using hφR x hx
  rw [(hev.iteratedDeriv k).eq_of_nhds, iteratedDeriv_fun_const_zero]

theorem contDiff_iteratedDeriv_of_smooth {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (k : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv k φ) := by
  rw [iteratedDeriv_eq_iterate]; exact hφ.iterate_deriv k

/-- The **normalized difference** `Δ_h^kφ/h^k`. -/
def diffQuot (φ : ℝ → ℝ) (h : ℝ) (k : ℕ) : ℝ → ℝ := fun u => (fwdDiff h)^[k] φ u / h ^ k

/-- The **jet error** `Δ_h^kφ/h^k − φ^{(k)}`. -/
def jetError (φ : ℝ → ℝ) (h : ℝ) (k : ℕ) : ℝ → ℝ := fun u => diffQuot φ h k u - iteratedDeriv k φ u

theorem diffQuot_eq_add (φ : ℝ → ℝ) (h : ℝ) (k : ℕ) :
    diffQuot φ h k = iteratedDeriv k φ + jetError φ h k := by
  funext u; simp only [jetError, Pi.add_apply]; ring

variable {φ : ℝ → ℝ}

theorem iteratedDeriv_mem_realTests (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (k : ℕ) :
    iteratedDeriv k φ ∈ realTests := by
  obtain ⟨R, -, hR⟩ := exists_supportedIn_of_hasCompactSupport hφc
  exact ⟨by exact_mod_cast contDiff_infty.mp (contDiff_iteratedDeriv_of_smooth hφ k) 2,
    hasCompactSupport_of_supportedIn' (iteratedDeriv_supportedIn hR k)⟩

theorem fwdDiff_iter_mem_realTests (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (h : ℝ)
    (k : ℕ) : (fwdDiff h)^[k] φ ∈ realTests := by
  refine ⟨by exact_mod_cast contDiff_infty.mp (contDiff_fwdDiff_iter hφ h k) 2, ?_⟩
  induction k generalizing φ with
  | zero => exact hφc
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    exact ih (contDiff_fwdDiff' hφ h)
      ((hφc.comp_homeomorph (Homeomorph.addRight h)).sub hφc)

theorem diffQuot_mem_realTests (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (h : ℝ)
    (k : ℕ) : diffQuot φ h k ∈ realTests := by
  have := realTests.smul_mem (h ^ k)⁻¹ (fwdDiff_iter_mem_realTests hφ hφc h k)
  convert this using 1
  funext u; simp [diffQuot, div_eq_inv_mul]

theorem jetError_mem_realTests (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (h : ℝ)
    (k : ℕ) : jetError φ h k ∈ realTests :=
  realTests.sub_mem (diffQuot_mem_realTests hφ hφc h k) (iteratedDeriv_mem_realTests hφ hφc k)

/-- **The jet error vanishes in the Weil norm**: `‖Δ_h^kφ/h^k − φ^{(k)}‖ → 0` as `h → 0⁺`. -/
theorem tendsto_weilNormSq_jetError (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (k : ℕ) :
    Tendsto (fun h => weilNormSq (jetError φ h k)) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨R, hR0, hR⟩ := exists_supportedIn_of_hasCompactSupport hφc
  have hD : Continuous (iteratedDeriv (k + 1) φ) :=
    (contDiff_iteratedDeriv_of_smooth hφ (k + 1)).continuous
  obtain ⟨M, hM⟩ := hD.bounded_above_of_compact_support
    (hasCompactSupport_of_supportedIn' (iteratedDeriv_supportedIn hR (k + 1)))
  simp only [Real.norm_eq_abs] at hM
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hφk : ContDiff ℝ (k + 1) φ := by exact_mod_cast contDiff_infty.mp hφ (k + 1)
  set R' := R + k
  have hR' : 0 ≤ R' := by positivity
  set B : ℝ → ℝ := fun h => (1 + levyLipConstant) * (2 * R' * (M * (k * h)) ^ 2) +
    Real.exp (1 / 2) * (2 * M) * (2 * R' * (M * (k * h))) + (2 * R' * (M * (k * h))) ^ 2
  have hB : Tendsto B (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous B := by fun_prop
    have := tendsto_nhdsWithin_of_tendsto_nhds (s := Ioi (0 : ℝ)) (hc.tendsto 0)
    simpa [B] using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hB
    (Eventually.of_forall fun h => weilNormSq_nonneg _) ?_
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with h hh
  have hm := jetError_mem_realTests hφ hφc h k
  have hsupp : SupportedIn R' (jetError φ h k) := by
    intro u hu
    have h1 : (fwdDiff h)^[k] φ u = 0 := supportedIn_fwdDiff_iter hh.1 hh.2.le k hR u hu
    have h2 : iteratedDeriv k φ u = 0 :=
      supportedIn_mono' (iteratedDeriv_supportedIn hR k)
        (by simp only [R']; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]) u hu
    simp [jetError, diffQuot, h1, h2]
  have hε : ∀ u, |jetError φ h k u| ≤ M * (k * h) := fun u =>
    abs_fwdDiff_iter_div_sub_le hφk hh.1 hM u
  have hdiff : Differentiable ℝ (iteratedDeriv k φ) :=
    (contDiff_iteratedDeriv_of_smooth hφ k).differentiable (by simp)
  have hLip : ∀ u v, |jetError φ h k u - jetError φ h k v| ≤ 2 * M * |u - v| := by
    intro u v
    have hq := abs_fwdDiff_iter_sub_le hφk hh.1 hM u v
    have hpk : 0 < h ^ k := pow_pos hh.1 k
    have hq' : |diffQuot φ h k u - diffQuot φ h k v| ≤ M * |u - v| := by
      simp only [diffQuot]
      rw [← sub_div, abs_div, abs_of_pos hpk, div_le_iff₀ hpk]
      linarith
    have hd := abs_sub_le_of_abs_deriv_le hdiff (fun x => by rw [← iteratedDeriv_succ]; exact hM x)
      v u
    calc |jetError φ h k u - jetError φ h k v|
        = |(diffQuot φ h k u - diffQuot φ h k v) - (iteratedDeriv k φ u - iteratedDeriv k φ v)| := by
          simp only [jetError]; ring_nf
      _ ≤ |diffQuot φ h k u - diffQuot φ h k v| + |iteratedDeriv k φ u - iteratedDeriv k φ v| :=
          abs_sub _ _
      _ ≤ M * |u - v| + M * |u - v| := add_le_add hq' hd
      _ = 2 * M * |u - v| := by ring
  exact weilNormSq_le_of_uniform hm.1 hm.2 hsupp hR' hε hLip

/-- **The Gram entries of the normalized differences converge to the jet Gram**:
`W(Δ_h^iφ/h^i, Δ_h^jφ/h^j) → W(φ^{(i)}, φ^{(j)})` as `h → 0⁺`. -/
theorem tendsto_weilPair_diffQuot (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (i j : ℕ) :
    Tendsto (fun h => weilPair (diffQuot φ h i) (diffQuot φ h j)) (𝓝[>] 0)
      (𝓝 (weilPair (iteratedDeriv i φ) (iteratedDeriv j φ))) := by
  obtain ⟨R, hR0, hR⟩ := exists_supportedIn_of_hasCompactSupport hφc
  set R' := R + i + j
  have hsupp : ∀ k, k ≤ i + j → ∀ᶠ h in 𝓝[>] (0 : ℝ), SupportedIn R' (jetError φ h k) := by
    intro k hk
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with h hh
    intro u hu
    have hkR : R + k ≤ R' := by
      simp only [R']; have : (k : ℝ) ≤ i + j := by exact_mod_cast hk
      linarith
    have h1 : (fwdDiff h)^[k] φ u = 0 :=
      supportedIn_fwdDiff_iter hh.1 hh.2.le k hR u (lt_of_le_of_lt hkR hu)
    have h2 : iteratedDeriv k φ u = 0 :=
      supportedIn_mono' (iteratedDeriv_supportedIn hR k) (by simp only [R']; linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i), (Nat.cast_nonneg j : (0 : ℝ) ≤ j)]) u hu
    simp [jetError, diffQuot, h1, h2]
  have hRR : R ≤ R' := by
    simp only [R']; linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i), (Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  simp_rw [diffQuot_eq_add]
  exact tendsto_weilPair_add (iteratedDeriv_mem_realTests hφ hφc i)
    (iteratedDeriv_mem_realTests hφ hφc j) (fun h => jetError_mem_realTests hφ hφc h i)
    (fun h => jetError_mem_realTests hφ hφc h j) (supportedIn_mono' (iteratedDeriv_supportedIn hR i) hRR)
    (supportedIn_mono' (iteratedDeriv_supportedIn hR j) hRR) (hsupp i (by omega)) (hsupp j (by omega))
    (tendsto_weilNormSq_jetError hφ hφc i) (tendsto_weilNormSq_jetError hφ hφc j)

/-! ### The lattice determinant is the jet Gram determinant -/

/-- The **lattice Toeplitz matrix** `[κ(i − j)]_{i,j<n}`. -/
def latticeToeplitz (κ : ℤ → ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => κ ((i : ℤ) - j)

/-- The **jet Gram matrix** `[W(φ^{(i)}, φ^{(j)})]_{i,j<n}`. -/
def jetGram (φ : ℝ → ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => weilPair (iteratedDeriv i φ) (iteratedDeriv j φ)

/-- The Gram matrix of the normalized differences `Δ_h^iφ/h^i`, `i < n`. -/
def diffGram (φ : ℝ → ℝ) (h : ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => weilPair (diffQuot φ h i) (diffQuot φ h j)

/-- The binomial matrix `B_{ik} = (−1)^{i−k} C(i, k)` of the forward differences. -/
def binomMat (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i k => (-1 : ℝ) ^ ((i : ℕ) - k) * ((i : ℕ).choose k)

theorem det_binomMat (n : ℕ) : (binomMat n).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · simp [binomMat]
  · intro i j hij
    have hij' : (i : ℕ) < j := by
      have : i < j := OrderDual.toDual_lt_toDual.mp hij
      exact this
    simp [binomMat, Nat.choose_eq_zero_of_lt hij']

/-- `Δ_h^iφ = Σ_k (−1)^{i−k}C(i,k) φ(· + kh)`. -/
theorem fwdDiff_iter_eq_sum_latticeTranslate (φ : ℝ → ℝ) (h : ℝ) {n : ℕ} (i : Fin n) :
    (fwdDiff h)^[i] φ = ∑ k : Fin n, binomMat n i k • latticeTranslate φ h k := by
  funext y
  rw [fwdDiff_iter_eq_sum_shift, Finset.sum_apply]
  have hsub : Finset.range ((i : ℕ) + 1) ⊆ Finset.range n :=
    Finset.range_subset_range.mpr (by omega)
  rw [Finset.sum_subset hsub fun k _ hk => by
    simp only [Finset.mem_range, not_lt] at hk
    simp [Nat.choose_eq_zero_of_lt (show (i : ℕ) < k by omega)]]
  rw [← Fin.sum_univ_eq_sum_range (fun k => ((-1 : ℤ) ^ ((i : ℕ) - k) * ((i : ℕ).choose k)) •
    φ (y + k • h)) n]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [binomMat, latticeTranslate, zsmul_eq_mul, nsmul_eq_mul]

theorem weilPair_sum_right {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℝ}
    (hf : ∀ i, f i ∈ realTests) {g : ℝ → ℝ} (hg : g ∈ realTests) :
    weilPair g (∑ i ∈ s, f i) = ∑ i ∈ s, weilPair g (f i) := by
  rw [weilPair_comm, weilPair_sum_left s hf hg]
  exact Finset.sum_congr rfl fun i _ => weilPair_comm _ _

/-- **The Gram of the differences is a congruence of the lattice matrix**:
`[W(Δ^iφ, Δ^jφ)] = B T Bᵀ`. -/
theorem weilPair_fwdDiff_iter (hφ : φ ∈ realTests) (h : ℝ) {n : ℕ} (i j : Fin n) :
    weilPair ((fwdDiff h)^[i] φ) ((fwdDiff h)^[j] φ) =
      (binomMat n * latticeToeplitz (weilSeq φ h) n * (binomMat n).transpose) i j := by
  have hT : ∀ k : Fin n, binomMat n i k • latticeTranslate φ h k ∈ realTests := fun k =>
    realTests.smul_mem _ (latticeTranslate_mem hφ h k)
  have hT' : ∀ k : Fin n, binomMat n j k • latticeTranslate φ h k ∈ realTests := fun k =>
    realTests.smul_mem _ (latticeTranslate_mem hφ h k)
  rw [fwdDiff_iter_eq_sum_latticeTranslate φ h i, fwdDiff_iter_eq_sum_latticeTranslate φ h j,
    weilPair_sum_left _ hT (Submodule.sum_mem _ fun k _ => hT' k)]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [weilPair_smul_left, weilPair_sum_right _ hT' (latticeTranslate_mem hφ h k), Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [weilPair_smul_right, weilPair_latticeTranslate]
  have he := weilSeq_isEven φ h ((k : ℤ) - l)
  rw [neg_sub] at he
  simp only [latticeToeplitz, Matrix.of_apply, he]
  ring

/-- **The lattice determinant in jet coordinates**: for `h ≠ 0`,
`det[κ_h(i − j)]_{i,j<n} = h^{n(n−1)} det[W(Δ_h^iφ/h^i, Δ_h^jφ/h^j)]`. -/
theorem det_latticeToeplitz_eq (hφ : φ ∈ realTests) {h : ℝ} (hh : h ≠ 0) (n : ℕ) :
    (latticeToeplitz (weilSeq φ h) n).det = h ^ (n * (n - 1)) * (diffGram φ h n).det := by
  set d : Fin n → ℝ := fun i => h ^ (i : ℕ)
  have hD : ∀ i : Fin n, (fwdDiff h)^[i] φ = h ^ (i : ℕ) • diffQuot φ h i := fun i => by
    funext u
    simp only [diffQuot, Pi.smul_apply, smul_eq_mul]
    field_simp
  have hG : binomMat n * latticeToeplitz (weilSeq φ h) n * (binomMat n).transpose =
      Matrix.diagonal d * diffGram φ h n * Matrix.diagonal d := by
    ext i j
    rw [← weilPair_fwdDiff_iter hφ h i j, hD i, hD j, weilPair_smul_left, weilPair_smul_right,
      Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [diffGram, Matrix.of_apply, d]
    ring
  have hdet := congrArg Matrix.det hG
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, det_binomMat, one_mul, mul_one,
    Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal] at hdet
  rw [hdet]
  have hprod : ∏ i : Fin n, d i = h ^ (∑ i ∈ Finset.range n, i) := by
    simp only [d]
    rw [Finset.prod_pow_eq_pow_sum, Fin.sum_univ_eq_sum_range (fun i => i) n]
  rw [hprod, ← Finset.sum_range_id_mul_two]
  ring

/-- **The lattice determinant is born at order `h^{n(n−1)}` with the jet Gram determinant**:
`h^{−n(n−1)} det[κ_h(i − j)]_{i,j<n} → det[W(φ^{(i)}, φ^{(j)})]` as `h → 0⁺`. -/
theorem tendsto_det_latticeToeplitz (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (n : ℕ) :
    Tendsto (fun h => (latticeToeplitz (weilSeq φ h) n).det / h ^ (n * (n - 1))) (𝓝[>] 0)
      (𝓝 (jetGram φ n).det) := by
  have hφ2 : φ ∈ realTests := by
    simpa using iteratedDeriv_mem_realTests hφ hφc 0
  have hG : Tendsto (fun h => diffGram φ h n) (𝓝[>] 0) (𝓝 (jetGram φ n)) :=
    tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => by
      simpa [diffGram, jetGram] using tendsto_weilPair_diffQuot hφ hφc i j
  have hdet := ((continuous_id.matrix_det).tendsto _).comp hG
  refine hdet.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh0 : h ≠ 0 := (show 0 < h from hh).ne'
  simp only [Function.comp_apply, id]
  rw [det_latticeToeplitz_eq hφ2 hh0, mul_div_cancel_left₀ _ (pow_ne_zero _ hh0)]

/-! ### Lattice margins as determinant ratios -/

/-- **One Levinson step is one bordered determinant**: if `a` is a predictor of size `n`, then
`det T_{n+1} = E · det T_n`. -/
theorem det_latticeToeplitz_succ {κ : ℤ → ℝ} (hκ : IsEvenSeq κ) {n : ℕ} {a : Fin n → ℝ}
    (ha : IsPredictor κ n a) :
    (latticeToeplitz κ (n + 1)).det = predErr κ n a * (latticeToeplitz κ n).det := by
  set T := latticeToeplitz κ (n + 1)
  set v : Fin (n + 1) → ℝ := Fin.cons 1 a
  set P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
    Matrix.of fun i j => if j = 0 then v i else if i = j then 1 else 0
  have hP : P.det = 1 := by
    rw [Matrix.det_of_lowerTriangular]
    · refine Finset.prod_eq_one fun i _ => ?_
      by_cases hi : i = 0
      · subst hi; simp [P, v]
      · simp [P, hi]
    · intro i j hij
      have hij' : i < j := OrderDual.toDual_lt_toDual.mp hij
      have hj : j ≠ 0 := by
        intro hj; rw [hj] at hij'; exact absurd hij' (Fin.not_lt_zero _)
      simp [P, hj, hij'.ne]
  have hcol0 : ∀ i, (T * P) i 0 = ∑ k, T i k * v k := fun i => by
    simp [Matrix.mul_apply, P]
  have hcol : ∀ i (j : Fin n), (T * P) i j.succ = T i j.succ := fun i j => by
    rw [Matrix.mul_apply]
    simp only [P, Matrix.of_apply, Fin.succ_ne_zero, if_false]
    rw [Finset.sum_eq_single j.succ (fun k _ hk => by simp [hk]) (by simp)]
    simp
  have hTv0 : ∑ k, T 0 k * v k = predErr κ n a := by
    rw [Fin.sum_univ_succ]
    simp only [T, latticeToeplitz, Matrix.of_apply, v, Fin.cons_zero, Fin.cons_succ, predErr,
      Fin.val_zero, Fin.val_succ]
    push_cast
    congr 1
    · ring_nf
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [show (0 : ℤ) - ((k : ℤ) + 1) = -((k : ℤ) + 1) by ring, hκ]
  have hTvs : ∀ i : Fin n, ∑ k, T i.succ k * v k = 0 := fun i => by
    rw [Fin.sum_univ_succ]
    simp only [T, latticeToeplitz, Matrix.of_apply, v, Fin.cons_zero, Fin.cons_succ,
      Fin.val_zero, Fin.val_succ]
    push_cast
    have hp := ha i
    have e : ∀ k : Fin n, κ ((i : ℤ) + 1 - ((k : ℤ) + 1)) * a k = κ ((i : ℤ) - k) * a k :=
      fun k => by rw [show (i : ℤ) + 1 - ((k : ℤ) + 1) = (i : ℤ) - k by ring]
    rw [Finset.sum_congr rfl fun k _ => e k, hp]
    simp
  have hdet : (T * P).det = predErr κ n a * (latticeToeplitz κ n).det := by
    rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
    have hrest : ∑ i : Fin n, (-1) ^ (i.succ : ℕ) * (T * P) i.succ 0 *
        ((T * P).submatrix i.succ.succAbove Fin.succ).det = 0 :=
      Finset.sum_eq_zero fun i _ => by rw [hcol0, hTvs, mul_zero, zero_mul]
    rw [hrest, add_zero, hcol0, hTv0]
    simp only [Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero]
    congr 1
    congr 1
    ext i j
    rw [Matrix.submatrix_apply, hcol]
    simp only [T, latticeToeplitz, Matrix.of_apply, Fin.val_succ]
    push_cast
    ring_nf
  rw [Matrix.det_mul, hP, mul_one] at hdet
  exact hdet

/-- **Lattice margins are determinant ratios**: if the lattice minors `det T_1, …, det T_{n+1}` do
not vanish, then every margin `E_k`, `k ≤ n`, is nonzero and `E_n det T_n = det T_{n+1}`. -/
theorem levinsonErr_mul_det {κ : ℤ → ℝ} (hκ : IsEvenSeq κ) :
    ∀ n : ℕ, (∀ k ≤ n, (latticeToeplitz κ (k + 1)).det ≠ 0) →
      (∀ k ≤ n, levinsonErr κ k ≠ 0) ∧
        levinsonErr κ n * (latticeToeplitz κ n).det = (latticeToeplitz κ (n + 1)).det
  | 0, hdet => by
    have h1 : (latticeToeplitz κ 1).det = κ 0 := by
      rw [Matrix.det_unique]; simp [latticeToeplitz]
    have h0 : (latticeToeplitz κ 0).det = 1 := Matrix.det_isEmpty
    refine ⟨fun k hk => ?_, ?_⟩
    · have hk0 : k = 0 := by omega
      subst hk0
      rw [levinsonErr_zero, ← h1]; exact hdet 0 le_rfl
    · rw [h0, mul_one, h1, levinsonErr_zero]
  | n + 1, hdet => by
    obtain ⟨hne, -⟩ := levinsonErr_mul_det hκ n fun k hk => hdet k (by omega)
    have hlt : ∀ k < n + 1, levinsonErr κ k ≠ 0 := fun k hk => hne k (by omega)
    have hstep := det_latticeToeplitz_succ hκ (levinson_isPredictor hκ hlt)
    rw [predErr_levinson hκ hlt] at hstep
    refine ⟨fun k hk => ?_, hstep.symm⟩
    rcases Nat.lt_or_ge k (n + 1) with h | h
    · exact hlt k h
    · have hk : k = n + 1 := by omega
      subst hk
      intro h0
      rw [h0, zero_mul] at hstep
      exact hdet (n + 1) le_rfl hstep

theorem pow_succ_mul_eq (n : ℕ) : (n + 1) * (n + 1 - 1) = n * (n - 1) + 2 * n := by
  cases n with
  | zero => rfl
  | succ m => simp only [Nat.add_sub_cancel]; ring

/-- **The continuum limit of the lattice canonical system at order `n`**: if the jet Gram minors
`det J_1, …, det J_{n+1}` do not vanish, then `h^{−2n} E_n(φ, h) → det J_{n+1}/det J_n` as
`h → 0⁺`. -/
theorem tendsto_levinsonErr_div_pow (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (n : ℕ)
    (hJ : ∀ k ≤ n, (jetGram φ (k + 1)).det ≠ 0) :
    Tendsto (fun h => levinsonErr (weilSeq φ h) n / h ^ (2 * n)) (𝓝[>] 0)
      (𝓝 ((jetGram φ (n + 1)).det / (jetGram φ n).det)) := by
  have hφ2 : φ ∈ realTests := by simpa using iteratedDeriv_mem_realTests hφ hφc 0
  have hG : ∀ m, Tendsto (fun h => (diffGram φ h m).det) (𝓝[>] 0) (𝓝 (jetGram φ m).det) :=
    fun m => ((continuous_id.matrix_det).tendsto _).comp
      (tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => by
        simpa [diffGram, jetGram] using tendsto_weilPair_diffQuot hφ hφc i j)
  have hJn : (jetGram φ n).det ≠ 0 := by
    cases n with
    | zero => rw [Matrix.det_isEmpty]; exact one_ne_zero
    | succ m => exact hJ m (by omega)
  have hev : ∀ᶠ h in 𝓝[>] (0 : ℝ), ∀ k : Fin (n + 1), (diffGram φ h ((k : ℕ) + 1)).det ≠ 0 :=
    Filter.eventually_all.2 fun k => (hG ((k : ℕ) + 1)).eventually_ne (hJ k (by omega))
  have hlim := (hG (n + 1)).div (hG n) hJn
  refine hlim.congr' ?_
  filter_upwards [hev, self_mem_nhdsWithin] with h hne hh
  have hh0 : h ≠ 0 := (show 0 < h from hh).ne'
  have hdet : ∀ k ≤ n, (latticeToeplitz (weilSeq φ h) (k + 1)).det ≠ 0 := fun k hk => by
    rw [det_latticeToeplitz_eq hφ2 hh0]
    exact mul_ne_zero (pow_ne_zero _ hh0) (hne ⟨k, by omega⟩)
  obtain ⟨-, hE⟩ := levinsonErr_mul_det (weilSeq_isEven φ h) n hdet
  rw [det_latticeToeplitz_eq hφ2 hh0, det_latticeToeplitz_eq hφ2 hh0, pow_succ_mul_eq, pow_add]
    at hE
  have hdn : (diffGram φ h n).det ≠ 0 := by
    cases n with
    | zero => rw [Matrix.det_isEmpty]; exact one_ne_zero
    | succ m => exact hne ⟨m, by omega⟩
  have hpow : h ^ (n * (n - 1)) ≠ 0 := pow_ne_zero _ hh0
  have hpow2 : h ^ (2 * n) ≠ 0 := pow_ne_zero _ hh0
  show (diffGram φ h (n + 1)).det / (diffGram φ h n).det = levinsonErr (weilSeq φ h) n / h ^ (2 * n)
  rw [div_eq_div_iff hdn hpow2]
  apply mul_left_cancel₀ hpow
  linear_combination (-1 : ℝ) * hE

/-! ### Translation makes the jet Gram a Hankel matrix -/

theorem weilPair_sub_left {f₁ f₂ g : ℝ → ℝ} (h₁ : f₁ ∈ realTests) (h₂ : f₂ ∈ realTests)
    (hg : g ∈ realTests) : weilPair (f₁ - f₂) g = weilPair f₁ g - weilPair f₂ g := by
  rw [sub_eq_add_neg, weilPair_add_left h₁ (realTests.neg_mem h₂) hg, weilPair_neg_left,
    ← sub_eq_add_neg]

theorem weilPair_sub_right {f g₁ g₂ : ℝ → ℝ} (hf : f ∈ realTests) (h₁ : g₁ ∈ realTests)
    (h₂ : g₂ ∈ realTests) : weilPair f (g₁ - g₂) = weilPair f g₁ - weilPair f g₂ := by
  rw [weilPair_comm, weilPair_sub_left h₁ h₂ hf, weilPair_comm g₁, weilPair_comm g₂]

theorem supportedIn_jetError {R h : ℝ} (hR : SupportedIn R φ) (hh : 0 < h) (hh1 : h ≤ 1) (k : ℕ) :
    SupportedIn (R + k) (jetError φ h k) := by
  intro u hu
  have h1 : (fwdDiff h)^[k] φ u = 0 := supportedIn_fwdDiff_iter hh hh1 k hR u hu
  have h2 : iteratedDeriv k φ u = 0 :=
    supportedIn_mono' (iteratedDeriv_supportedIn hR k)
      (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]) u hu
  simp [jetError, diffQuot, h1, h2]

/-- One forward difference vanishes in the Weil norm as the step shrinks. -/
theorem tendsto_weilNormSq_fwdDiff {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    Tendsto (fun h => weilNormSq (fwdDiff h g)) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨R, hR0, hR⟩ := exists_supportedIn_of_hasCompactSupport hgc
  have hg1 : ContDiff ℝ 1 g := by exact_mod_cast contDiff_infty.mp hg 1
  have hD : Continuous (deriv g) := hg1.continuous_deriv le_rfl
  obtain ⟨M, hM⟩ := hD.bounded_above_of_compact_support hgc.deriv
  simp only [Real.norm_eq_abs] at hM
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hdg : Differentiable ℝ g := hg1.differentiable one_ne_zero
  set B : ℝ → ℝ := fun h => (1 + levyLipConstant) * (2 * (R + 1) * (h * M) ^ 2) +
    Real.exp (1 / 2) * (2 * M) * (2 * (R + 1) * (h * M)) + (2 * (R + 1) * (h * M)) ^ 2
  have hB : Tendsto B (𝓝[>] 0) (𝓝 0) := by
    have := tendsto_nhdsWithin_of_tendsto_nhds (s := Ioi (0 : ℝ))
      ((show Continuous B by fun_prop).tendsto 0)
    simpa [B] using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hB
    (Eventually.of_forall fun h => weilNormSq_nonneg _) ?_
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with h hh
  have hm : fwdDiff h g ∈ realTests := by
    simpa using fwdDiff_iter_mem_realTests hg hgc h 1
  have hsupp : SupportedIn (R + 1) (fwdDiff h g) := by
    simpa using supportedIn_fwdDiff_iter hh.1 hh.2.le 1 hR
  have hε : ∀ u, |fwdDiff h g u| ≤ h * M := fun u => by
    have := abs_fwdDiff_iter_le (k := 1) (by exact_mod_cast hg1) hh.1 (M := M)
      (fun x => by simpa using hM x) u
    simpa using this
  have hLip : ∀ u v, |fwdDiff h g u - fwdDiff h g v| ≤ 2 * M * |u - v| := by
    intro u v
    have h1 := abs_sub_le_of_abs_deriv_le hdg hM (v + h) (u + h)
    have h2 := abs_sub_le_of_abs_deriv_le hdg hM v u
    rw [show u + h - (v + h) = u - v by ring] at h1
    simp only [fwdDiff]
    calc |g (u + h) - g u - (g (v + h) - g v)| = |(g (u + h) - g (v + h)) - (g u - g v)| := by
          ring_nf
      _ ≤ |g (u + h) - g (v + h)| + |g u - g v| := abs_sub _ _
      _ ≤ M * |u - v| + M * |u - v| := add_le_add h1 h2
      _ = 2 * M * |u - v| := by ring
  exact weilNormSq_le_of_uniform hm.1 hm.2 hsupp (by linarith) hε hLip

/-- **Differentiation is skew for Weil's pairing**: `W(f', g) = −W(f, g')`, the infinitesimal
form of translation invariance. -/
theorem weilPair_deriv_left {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    weilPair (deriv f) g = -weilPair f (deriv g) := by
  have hf2 : f ∈ realTests := by simpa using iteratedDeriv_mem_realTests hf hfc 0
  have hg2 : g ∈ realTests := by simpa using iteratedDeriv_mem_realTests hg hgc 0
  have hdf : deriv f ∈ realTests := by simpa using iteratedDeriv_mem_realTests hf hfc 1
  have hdg : deriv g ∈ realTests := by simpa using iteratedDeriv_mem_realTests hg hgc 1
  obtain ⟨R, hR0, hRf⟩ := exists_supportedIn_of_hasCompactSupport hfc
  obtain ⟨R₂, hR₂0, hRg⟩ := exists_supportedIn_of_hasCompactSupport hgc
  set S := R + R₂ + 1
  have hS1 : R + 1 ≤ S := by simp only [S]; linarith
  have hS2 : R₂ + 1 ≤ S := by simp only [S]; linarith
  have hSf : SupportedIn S f := supportedIn_mono' hRf (by linarith)
  have hSg : SupportedIn S g := supportedIn_mono' hRg (by linarith)
  have hSdf : SupportedIn S (deriv f) :=
    supportedIn_mono' (by simpa using iteratedDeriv_supportedIn hRf 1) (by linarith)
  have hSdg : SupportedIn S (deriv g) :=
    supportedIn_mono' (by simpa using iteratedDeriv_supportedIn hRg 1) (by linarith)
  have hev01 := Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)
  have hjf : ∀ᶠ h in 𝓝[>] (0 : ℝ), SupportedIn S (jetError f h 1) := by
    filter_upwards [hev01] with h hh
    exact supportedIn_mono' (supportedIn_jetError hRf hh.1 hh.2.le 1) (by push_cast; linarith)
  have hjg : ∀ᶠ h in 𝓝[>] (0 : ℝ), SupportedIn S (jetError g h 1) := by
    filter_upwards [hev01] with h hh
    exact supportedIn_mono' (supportedIn_jetError hRg hh.1 hh.2.le 1) (by push_cast; linarith)
  have hfg : ∀ᶠ h in 𝓝[>] (0 : ℝ), SupportedIn S (fwdDiff h g) := by
    filter_upwards [hev01] with h hh
    exact supportedIn_mono' (by simpa using supportedIn_fwdDiff_iter hh.1 hh.2.le 1 hRg) hS2
  have hfgm : ∀ h, fwdDiff h g ∈ realTests := fun h => by
    simpa using fwdDiff_iter_mem_realTests hg hgc h 1
  -- the exact identity at every positive step
  have hexact : ∀ h : ℝ, h ≠ 0 →
      weilPair (diffQuot f h 1) (g + fwdDiff h g) = -weilPair f (diffQuot g h 1) := by
    intro h hh
    have hshift : g + fwdDiff h g = fun u => g (u + h) := by
      funext u; simp [fwdDiff]
    have htrans := weilPair_comp_sub f g (-h)
    simp only [sub_neg_eq_add] at htrans
    have hfs : (fun u => f (u + h)) ∈ realTests :=
      ⟨hf2.1.comp (contDiff_id.add contDiff_const), hf2.2.comp_homeomorph (Homeomorph.addRight h)⟩
    have hgs : (fun u => g (u + h)) ∈ realTests :=
      ⟨hg2.1.comp (contDiff_id.add contDiff_const), hg2.2.comp_homeomorph (Homeomorph.addRight h)⟩
    have hq : ∀ k : ℝ → ℝ, diffQuot k h 1 = h⁻¹ • ((fun u => k (u + h)) - k) := fun k => by
      funext u; simp [diffQuot, fwdDiff, div_eq_inv_mul]
    rw [hshift, hq f, hq g, weilPair_smul_left, weilPair_smul_right, weilPair_sub_left hfs hf2 hgs,
      weilPair_sub_right hf2 hgs hg2, htrans]
    ring
  have hL : Tendsto (fun h => weilPair (deriv f + jetError f h 1) (g + fwdDiff h g)) (𝓝[>] 0)
      (𝓝 (weilPair (deriv f) g)) :=
    tendsto_weilPair_add hdf hg2 (fun h => jetError_mem_realTests hf hfc h 1) hfgm hSdf hSg hjf hfg
      (tendsto_weilNormSq_jetError hf hfc 1) (tendsto_weilNormSq_fwdDiff hg hgc)
  have h0N : Tendsto (fun _ : ℝ => weilNormSq (fun _ : ℝ => (0 : ℝ))) (𝓝[>] 0) (𝓝 0) := by
    have : weilNormSq (fun _ : ℝ => (0 : ℝ)) = 0 := by simp [weilNormSq, levyEnergy]
    rw [this]; exact tendsto_const_nhds
  have hR' : Tendsto (fun h => weilPair (f + fun _ => 0) (deriv g + jetError g h 1)) (𝓝[>] 0)
      (𝓝 (weilPair f (deriv g))) :=
    tendsto_weilPair_add hf2 hdg (fun _ => realTests.zero_mem)
      (fun h => jetError_mem_realTests hg hgc h 1) hSf hSdg
      (Eventually.of_forall fun _ _ _ => rfl) hjg h0N (tendsto_weilNormSq_jetError hg hgc 1)
  have hR'' := hR'.neg
  refine tendsto_nhds_unique hL (hR''.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hq1 := diffQuot_eq_add f h 1
  have hq2 := diffQuot_eq_add g h 1
  rw [iteratedDeriv_one] at hq1 hq2
  have := hexact h (show 0 < h from hh).ne'
  rw [hq1, hq2] at this
  rw [show (f + fun _ => (0 : ℝ)) = f by funext u; simp]
  exact this.symm

/-- `W(φ^{(i)}, φ^{(j+1)}) = −W(φ^{(i+1)}, φ^{(j)})`. -/
theorem weilPair_iteratedDeriv_succ_right (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (i j : ℕ) :
    weilPair (iteratedDeriv i φ) (iteratedDeriv (j + 1) φ) =
      -weilPair (iteratedDeriv (i + 1) φ) (iteratedDeriv j φ) := by
  have := weilPair_deriv_left (contDiff_iteratedDeriv_of_smooth hφ i)
    (iteratedDeriv_mem_realTests hφ hφc i).2 (contDiff_iteratedDeriv_of_smooth hφ j)
    (iteratedDeriv_mem_realTests hφ hφc j).2
  rw [← iteratedDeriv_succ, ← iteratedDeriv_succ] at this
  linarith

/-- **The jet Gram is a Hankel matrix**: `W(φ^{(i)}, φ^{(j)}) = (−1)^i W(φ, φ^{(i+j)})`. -/
theorem weilPair_iteratedDeriv_eq (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (i : ℕ) :
    ∀ j : ℕ, weilPair (iteratedDeriv i φ) (iteratedDeriv j φ) =
      (-1) ^ i * weilPair φ (iteratedDeriv (i + j) φ) := by
  induction i with
  | zero => intro j; simp
  | succ i ih =>
    intro j
    have h1 := weilPair_iteratedDeriv_succ_right hφ hφc i j
    rw [ih (j + 1)] at h1
    rw [pow_succ, show i + 1 + j = i + (j + 1) by ring]
    linarith

/-- **Odd jet pairings vanish**: `W(φ^{(i)}, φ^{(j)}) = 0` when `i + j` is odd. -/
theorem weilPair_iteratedDeriv_eq_zero_of_odd (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    {i j : ℕ} (hij : Odd (i + j)) : weilPair (iteratedDeriv i φ) (iteratedDeriv j φ) = 0 := by
  obtain ⟨m, hm⟩ := hij
  have hmm : weilPair (iteratedDeriv m φ) (iteratedDeriv (m + 1) φ) = 0 := by
    have h := weilPair_iteratedDeriv_succ_right hφ hφc m m
    rw [weilPair_comm (iteratedDeriv (m + 1) φ)] at h
    linarith
  have h1 := weilPair_iteratedDeriv_eq hφ hφc m (m + 1)
  rw [hmm] at h1
  have h0 : weilPair φ (iteratedDeriv (2 * m + 1) φ) = 0 := by
    have hpow : ((-1 : ℝ) ^ m) ≠ 0 := pow_ne_zero _ (by norm_num)
    rw [show m + (m + 1) = 2 * m + 1 by ring] at h1
    exact (mul_eq_zero.mp h1.symm).resolve_left hpow
  rw [weilPair_iteratedDeriv_eq hφ hφc i j, hm, h0, mul_zero]

/-- **The first margin**: if `Q(φ) ≠ 0` and `Q(φ') ≠ 0`, then `h^{−2}E_1(φ, h) → Q(φ')`. -/
theorem tendsto_levinsonErr_one_div_sq' (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (h0 : weilQuad φ ≠ 0) (h1 : weilQuad (deriv φ) ≠ 0) :
    Tendsto (fun h => levinsonErr (weilSeq φ h) 1 / h ^ 2) (𝓝[>] 0)
      (𝓝 (weilQuad (deriv φ))) := by
  have hodd := weilPair_iteratedDeriv_eq_zero_of_odd hφ hφc (i := 0) (j := 1) (by decide)
  have hJ1 : (jetGram φ 1).det = weilQuad φ := by
    rw [Matrix.det_unique]; simp [jetGram]; rfl
  have hJ2 : (jetGram φ 2).det = weilQuad φ * weilQuad (deriv φ) := by
    rw [Matrix.det_fin_two]
    simp only [jetGram, Matrix.of_apply]
    have hodd' : weilPair (iteratedDeriv 1 φ) (iteratedDeriv 0 φ) = 0 := by
      rw [weilPair_comm]; exact hodd
    simp only [Fin.isValue, Fin.val_zero, Fin.val_one] at *
    rw [hodd, hodd', iteratedDeriv_zero, iteratedDeriv_one]
    simp only [mul_zero, sub_zero]
    rfl
  have hJ : ∀ k ≤ 1, (jetGram φ (k + 1)).det ≠ 0 := by
    intro k hk
    interval_cases k
    · rw [hJ1]; exact h0
    · rw [hJ2]; exact mul_ne_zero h0 h1
  have := tendsto_levinsonErr_div_pow hφ hφc 1 hJ
  rw [hJ2, hJ1, mul_div_cancel_left₀ _ h0] at this
  simpa using this

end GaloisForLFunctions.SignedWindowCriticality

end
