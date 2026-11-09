import GaloisForLFunctions.RHTower.ZetaChiNormalizedShiftBound
import GaloisForLFunctions.RHTower.ZetaConvexityBound
import GaloisForLFunctions.RHTower.HardyZ
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The conductor-normalized reflection of high zeta translates

The functional equation reflects a translated profile with a nonconstant Gamma
factor. Dividing by its critical-line phase and cancelling its conductor power
gives the conjugate reflected profile, with error tending uniformly to zero on
every bounded part of the open critical strip. The error estimate uses actual
zeta convexity and requires no boundedness or recurrence premise.
-/

open Complex ComplexConjugate Filter Topology
open RHTower

noncomputable section

namespace GaloisForLFunctions.EulerFETransportTheory

/-- Reflection across the critical line, retaining the ordinate. -/
def heightReflection (s : ℂ) : ℂ := 1 - conj s

/-- The conductor power divided by the critical-line functional-equation phase. -/
def heightNormalizer (t : ℝ) (s : ℂ) : ℂ :=
  Complex.exp ((s - (1 / 2 : ℂ)) * (Real.log (t / (2 * Real.pi)) : ℂ)) /
    zetaChi (linePt t)

/-- The defect between normalized translation and conjugate reflected translation. -/
def heightReflectionDefect (t : ℝ) (s : ℂ) : ℂ :=
  heightNormalizer t s * riemannZeta (s + (t : ℂ) * I) -
    conj (riemannZeta (heightReflection s + (t : ℂ) * I))

/-- The exact reflected functional equation at every real height in the open strip. -/
theorem zeta_height_reflection {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) (t : ℝ) :
    riemannZeta (s + (t : ℂ) * I) = zetaChi (s + (t : ℂ) * I) *
      conj (riemannZeta (heightReflection s + (t : ℂ) * I)) := by
  have hre : (s + (t : ℂ) * I).re = s.re := by simp
  have hne0 : s + (t : ℂ) * I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp only [hre, zero_re] at this
    linarith
  have hne1 : s + (t : ℂ) * I ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp only [hre, one_re] at this
    linarith
  rw [zeta_eq_zetaChi_mul hne0 hne1
    (Gammaℝ_ne_zero_of_re_pos (by simp only [sub_re, one_re, hre]; linarith))]
  have hr : (heightReflection s + (t : ℂ) * I).re = 1 - s.re := by
    simp [heightReflection]
  have heq : 1 - (s + (t : ℂ) * I) = conj (heightReflection s + (t : ℂ) * I) := by
    apply Complex.ext <;> simp [heightReflection, add_comm]
  rw [heq, riemannZeta_conj_of_re_pos (by rw [hr]; linarith) (by
    intro h
    have := congrArg Complex.re h
    rw [hr, one_re] at this
    linarith)]

/-- The full zeta error factors through the normalized Gamma error. -/
theorem heightReflectionDefect_eq {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) (t : ℝ) :
    heightReflectionDefect t s =
      ((zetaChi (s + (t : ℂ) * I) / zetaChi (linePt t)) *
        Complex.exp ((s - (1 / 2 : ℂ)) * (Real.log (t / (2 * Real.pi)) : ℂ)) - 1) *
      conj (riemannZeta (heightReflection s + (t : ℂ) * I)) := by
  rw [heightReflectionDefect, zeta_height_reflection hs0 hs1, heightNormalizer]
  ring

/-- Convexity controls the entire reflected profile uniformly up to the strip edges. -/
private theorem exists_reflected_profile_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : ℂ) (t : ℝ),
      0 < s.re → s.re < 1 → 16 ≤ t → 2 * |s.im| ≤ t →
      ‖conj (riemannZeta (heightReflection s + (t : ℂ) * I))‖ ≤
        C * t ^ (3 / 4 : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_riemannZeta_le_convexity
    (η := (1 / 2 : ℝ)) (by norm_num) le_rfl
  refine ⟨C * 2 ^ (3 / 4 : ℝ), by positivity, ?_⟩
  intro s t hs0 hs1 ht him
  have hy : 8 ≤ t + s.im := by linarith [neg_abs_le s.im]
  have hyt : t + s.im ≤ 2 * t := by linarith [le_abs_self s.im]
  have heq : heightReflection s + (t : ℂ) * I =
      ((1 - s.re : ℝ) : ℂ) + ((t + s.im : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp [heightReflection, add_comm]
  rw [norm_conj, heq]
  calc
    _ ≤ C * (t + s.im) ^ ((1 + 1 / 2 - (1 - s.re)) / 2) :=
      hbound _ _ (by linarith) (by linarith) hy
    _ ≤ C * (t + s.im) ^ (3 / 4 : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ hC.le
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    _ ≤ C * (2 * t) ^ (3 / 4 : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ hC.le
      exact Real.rpow_le_rpow (by linarith) hyt (by norm_num)
    _ = _ := by rw [Real.mul_rpow (by norm_num) (by linarith)]; ring

/-- An absolute error bound for the actual normalized reflection, uniform on bounded
parts of the open strip. Neither return times nor normality are assumed. -/
theorem exists_heightReflectionDefect_bound (D : ℝ) :
    ∃ C T : ℝ, 0 < C ∧ ∀ (t : ℝ) (s : ℂ), T ≤ t →
      0 < s.re → s.re < 1 → ‖s - (1 / 2 : ℂ)‖ ≤ D →
      ‖heightReflectionDefect t s‖ ≤ C * t ^ (-(1 / 4 : ℝ)) := by
  obtain ⟨K, hK, hprofile⟩ := exists_reflected_profile_bound
  let B := 52 * |D| + 20 * |D| ^ 2 + 1
  refine ⟨B * K, max 16 (max (2 * |D|) (26 * |D| + 10 * |D| ^ 2)),
    mul_pos (by dsimp [B]; positivity) hK, ?_⟩
  intro t s ht hs0 hs1 hsD
  have ht16 : 16 ≤ t := (le_max_left _ _).trans ht
  have ht0 : 0 < t := by linarith
  have hd : ‖s - (1 / 2 : ℂ)‖ ≤ |D| := hsD.trans (le_abs_self D)
  have hd2 : ‖s - (1 / 2 : ℂ)‖ ^ 2 ≤ |D| ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hd 2
  have himD : |s.im| ≤ |D| := by
    have h := Complex.abs_im_le_norm (s - (1 / 2 : ℂ))
    simpa using h.trans hd
  have him : 2 * |s.im| ≤ t := by
    have := (le_max_left (2 * |D|) _).trans ((le_max_right _ _).trans ht)
    linarith
  have hsize : 26 * ‖s - (1 / 2 : ℂ)‖ + 10 * ‖s - (1 / 2 : ℂ)‖ ^ 2 ≤ t := by
    have := (le_max_right (2 * |D|) _).trans ((le_max_right _ _).trans ht)
    linarith
  have hchi := norm_zetaChi_normalized_shift_sub_one_le hs0 hs1 (by linarith) him hsize
  have hchiB :
      ‖(zetaChi (s + (t : ℂ) * I) / zetaChi (linePt t)) *
        Complex.exp ((s - (1 / 2 : ℂ)) * (Real.log (t / (2 * Real.pi)) : ℂ)) - 1‖ ≤ B / t := by
    apply hchi.trans
    apply div_le_div_of_nonneg_right _ ht0.le
    dsimp [B]
    linarith
  rw [heightReflectionDefect_eq hs0 hs1, norm_mul]
  calc
    _ ≤ (B / t) * (K * t ^ (3 / 4 : ℝ)) :=
      mul_le_mul hchiB (hprofile s t hs0 hs1 ht16 him) (norm_nonneg _) (by positivity)
    _ = (B * K) * t ^ (-(1 / 4 : ℝ)) := by
      have hp : t ^ (-(1 / 4 : ℝ)) = t ^ (3 / 4 : ℝ) / t := by
        rw [show -(1 / 4 : ℝ) = 3 / 4 - 1 by norm_num,
          Real.rpow_sub ht0, Real.rpow_one]
      rw [hp]
      ring

/-- The conductor-normalized reflected-height law holds uniformly on every bounded
part of the open critical strip. -/
theorem tendstoUniformlyOn_heightReflectionDefect (D : ℝ) :
    TendstoUniformlyOn heightReflectionDefect (fun _ => 0) atTop
      {s : ℂ | 0 < s.re ∧ s.re < 1 ∧ ‖s - (1 / 2 : ℂ)‖ ≤ D} := by
  obtain ⟨C, T, hC, hbound⟩ := exists_heightReflectionDefect_bound D
  have hlim : Tendsto (fun t : ℝ => C * t ^ (-(1 / 4 : ℝ))) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).const_mul C
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [eventually_ge_atTop T, hlim.eventually (gt_mem_nhds hε)] with t ht hsmall
  intro s hs
  simpa only [dist_zero_left] using (hbound t s ht hs.1 hs.2.1 hs.2.2).trans_lt hsmall

end GaloisForLFunctions.EulerFETransportTheory

#print axioms GaloisForLFunctions.EulerFETransportTheory.tendstoUniformlyOn_heightReflectionDefect
