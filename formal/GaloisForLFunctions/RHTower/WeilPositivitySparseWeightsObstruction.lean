import GaloisForLFunctions.RHTower.WeilPositivityFiniteLevelExistence

/-!
# Weil positivity forces a pole: sparse weight systems are never Weil-positive

Let `ψ` be the flat-top Fejér test supported in `[-17/50, 17/50]`, whose archimedean energy
`∫ |ψ̂|² A` is negative, and let `R` be its autocorrelation (supported in `|y| < log 2`).

* **Far polar correction** (`farPolarTest`, `paperFT_farPolarTest`).  The test
  `f_X = ψ − c_X (ψ(· − X) + ψ(· + X))/2`, `c_X = 1/cosh(X/2)`, has transform
  `ψ̂(z)(1 − c_X cos(Xz))`, which vanishes at `z = ±i/2`.  On the real line the multiplier tends to
  `1` uniformly, so the archimedean energy of `f_X` tends to that of `ψ`
  (`integral_arch_farPolarTest_le`), while the atom at `log n` sees `f_X` only through the lags
  `log n − X` and `log n − 2X` (`integral_normSq_farPolarTest_mul_cos_log`).
* **Chebyshev inequality at every scale** (`weilPositive_farPolar_inequality`).  If `lam` is
  Weil-positive then for every `X ≥ 0`
  `−∫|ψ̂|²A − (2c_X + c_X²)∫|ψ̂|²|A| ≤ 4π Σ_n lam(n) n^{-1/2} (c_X R(log n − X) − (c_X²/4) R(log n − 2X))`.
  The left side tends to `−∫|ψ̂|²A > 0`, so the atoms near `e^X` and `e^{2X}` must carry mass of
  order `e^{X/2}` and `e^X`.
* **Sparse systems** (`not_weilPositive_of_localAtomMass`).  If the local atom mass
  `Σ_{|log n − X| ≤ 1} |lam(n)| n^{-1/2}` is `o(e^{X/2})`, then `lam` is not Weil-positive.
* **Sparse supports** (`not_weilPositive_of_sparse_support`).  If `lam` vanishes off a set `P` with
  `#(P ∩ [2, N]) ≤ C N^θ`, `θ < 1/2`, then `lam` is not Weil-positive (Weil positivity bounds
  `|lam(n)| ≤ √n (log n + C₀)`).
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped ComplexConjugate

noncomputable section
namespace RHTower

open Zeta23

/-- The amplitude `c_X = 1/cosh(X/2)` of the far polar correction. -/
def farPolarCoeff (X : ℝ) : ℝ := 1 / Real.cosh (X / 2)

theorem farPolarCoeff_nonneg (X : ℝ) : 0 ≤ farPolarCoeff X :=
  div_nonneg zero_le_one (Real.cosh_pos _).le

theorem farPolarCoeff_le (X : ℝ) : farPolarCoeff X ≤ 2 * Real.exp (-(X / 2)) := by
  unfold farPolarCoeff
  have hc := Real.cosh_pos (X / 2)
  rw [div_le_iff₀ hc, Real.cosh_eq]
  have h1 : Real.exp (-(X / 2)) * Real.exp (X / 2) = 1 := by
    rw [← Real.exp_add]; simp
  nlinarith [Real.exp_pos (-(X / 2)), Real.exp_pos (X / 2)]

/-- The Fejér test with a far polar correction:
`ψ(u) − c_X (ψ(u − X) + ψ(u + X))/2`, `c_X = 1/cosh(X/2)`. -/
def farPolarTest (X : ℝ) (u : ℝ) : ℂ :=
  fejerTest u - (farPolarCoeff X : ℂ) * ((fejerTest (u - X) + fejerTest (u + X)) / 2)

theorem fejerTest_eq_zero {v : ℝ} (hv : 17 / 50 < |v|) : fejerTest v = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro h
  have := tsupport_fejerTest h
  rw [mem_Icc] at this
  exact absurd (abs_le.mpr this) (not_le.mpr hv)

theorem continuous_fejerTest : Continuous fejerTest := contDiff_fejerTest.continuous

theorem hasCompactSupport_fejerTest : HasCompactSupport fejerTest :=
  IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) tsupport_fejerTest

theorem integrable_fejerTest_shift_mul_cexp (s : ℝ) (z : ℂ) :
    Integrable (fun y : ℝ => fejerTest (y - s) * cexp (I * z * y)) := by
  have hcs : HasCompactSupport (fun y : ℝ => fejerTest (y - s)) :=
    hasCompactSupport_fejerTest.comp_homeomorph (Homeomorph.subRight s)
  exact ((continuous_fejerTest.comp (continuous_id.sub continuous_const)).mul
    (by fun_prop)).integrable_of_hasCompactSupport hcs.mul_right

theorem paperFT_farPolarTest (X : ℝ) (z : ℂ) :
    paperFT (farPolarTest X) z =
      paperFT fejerTest z * (1 - (farPolarCoeff X : ℂ) * Complex.cos (X * z)) := by
  have i0 : Integrable (fun y : ℝ => fejerTest y * cexp (I * z * y)) := by
    simpa using integrable_fejerTest_shift_mul_cexp 0 z
  have i1 := integrable_fejerTest_shift_mul_cexp X z
  have i2 : Integrable (fun y : ℝ => fejerTest (y + X) * cexp (I * z * y)) := by
    simpa [sub_neg_eq_add] using integrable_fejerTest_shift_mul_cexp (-X) z
  have h1 := paperFT_translate' fejerTest X z
  have h2 := paperFT_translate' fejerTest (-X) z
  simp only [sub_neg_eq_add, ofReal_neg] at h2
  have hsplit : (fun y : ℝ => farPolarTest X y * cexp (I * z * y)) =
      fun y => fejerTest y * cexp (I * z * y) -
        ((farPolarCoeff X : ℂ) / 2) * (fejerTest (y - X) * cexp (I * z * y) +
          fejerTest (y + X) * cexp (I * z * y)) := by
    funext y; simp only [farPolarTest]; ring
  have h1' : (∫ y : ℝ, fejerTest (y - X) * cexp (I * z * y)) =
      cexp (I * z * X) * paperFT fejerTest z := h1
  have h2' : (∫ y : ℝ, fejerTest (y + X) * cexp (I * z * y)) =
      cexp (I * z * -(X : ℂ)) * paperFT fejerTest z := h2
  have i12 : Integrable (fun y : ℝ => ((farPolarCoeff X : ℂ) / 2) *
      (fejerTest (y - X) * cexp (I * z * y) + fejerTest (y + X) * cexp (I * z * y))) :=
    (i1.add i2).const_mul _
  rw [paperFT, hsplit, integral_sub i0 i12, integral_const_mul, integral_add i1 i2, h1', h2']
  have hp : (∫ y : ℝ, fejerTest y * cexp (I * z * y)) = paperFT fejerTest z := rfl
  rw [hp, Complex.cos]
  have e1 : cexp (I * z * X) = cexp (X * z * I) := by ring_nf
  have e2 : cexp (I * z * -(X : ℂ)) = cexp (-(X * z) * I) := by ring_nf
  rw [e1, e2]
  ring

theorem contDiff_farPolarTest (X : ℝ) : ContDiff ℝ 2 (farPolarTest X) := by
  unfold farPolarTest
  have h1 : ContDiff ℝ 2 (fun u : ℝ => fejerTest (u - X)) :=
    contDiff_fejerTest.comp (contDiff_id.sub contDiff_const)
  have h2 : ContDiff ℝ 2 (fun u : ℝ => fejerTest (u + X)) :=
    contDiff_fejerTest.comp (contDiff_id.add contDiff_const)
  exact contDiff_fejerTest.sub (contDiff_const.mul ((h1.add h2).div_const _))

theorem tsupport_farPolarTest {X : ℝ} (hX : 0 ≤ X) :
    tsupport (farPolarTest X) ⊆ Icc (-(X + 17 / 50)) (X + 17 / 50) := by
  apply closure_minimal _ isClosed_Icc
  intro u hu
  by_contra h
  apply hu
  have hu' : X + 17 / 50 < |u| := by
    rw [mem_Icc, not_and_or, not_le, not_le] at h
    rcases h with h | h
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  have h0 : fejerTest u = 0 := fejerTest_eq_zero (by linarith)
  have h1 : fejerTest (u - X) = 0 := by
    apply fejerTest_eq_zero
    have := abs_sub_abs_le_abs_sub u X
    rw [abs_of_nonneg hX] at this; linarith
  have h2 : fejerTest (u + X) = 0 := by
    apply fejerTest_eq_zero
    have := abs_sub_abs_le_abs_sub u (-X)
    rw [sub_neg_eq_add, abs_neg, abs_of_nonneg hX] at this; linarith
  simp [farPolarTest, h0, h1, h2]

theorem cos_mul_half_I (X : ℝ) : Complex.cos (X * (I / 2)) = (Real.cosh (X / 2) : ℂ) := by
  rw [show (X : ℂ) * (I / 2) = ((X / 2 : ℝ) : ℂ) * I by push_cast; ring, Complex.cos_mul_I,
    ← Complex.ofReal_cosh]

theorem farPolarCoeff_mul_cosh (X : ℝ) : (farPolarCoeff X : ℂ) * (Real.cosh (X / 2) : ℂ) = 1 := by
  rw [← Complex.ofReal_mul, farPolarCoeff, one_div, inv_mul_cancel₀ (Real.cosh_pos _).ne']
  simp

theorem paperFT_farPolarTest_half_I (X : ℝ) : paperFT (farPolarTest X) (I / 2) = 0 := by
  rw [paperFT_farPolarTest, cos_mul_half_I, farPolarCoeff_mul_cosh, sub_self, mul_zero]

theorem paperFT_farPolarTest_neg_half_I (X : ℝ) : paperFT (farPolarTest X) (-(I / 2)) = 0 := by
  rw [paperFT_farPolarTest, mul_neg, Complex.cos_neg, cos_mul_half_I, farPolarCoeff_mul_cosh,
    sub_self, mul_zero]

/-- On the real line the far polar correction is the real multiplier `1 − c_X cos(τX)`. -/
theorem normSq_paperFT_farPolarTest (X τ : ℝ) :
    ‖paperFT (farPolarTest X) τ‖ ^ 2 =
      ‖paperFT fejerTest τ‖ ^ 2 * (1 - farPolarCoeff X * Real.cos (τ * X)) ^ 2 := by
  rw [paperFT_farPolarTest, norm_mul, mul_pow]
  congr 1
  have : (1 - (farPolarCoeff X : ℂ) * Complex.cos (X * τ)) =
      ((1 - farPolarCoeff X * Real.cos (τ * X) : ℝ) : ℂ) := by
    push_cast; rw [mul_comm (X : ℂ)]
  rw [this, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-! ### The autocorrelation of the Fejér test -/

/-- The autocorrelation `R` of the Fejér test. -/
local notation "Rf" => flatBumpCorr (17 / 50) (17 / 1000)

theorem fejerCorr_nonneg (y : ℝ) : 0 ≤ Rf y :=
  integral_nonneg fun _ => mul_nonneg (flatBump_nonneg _) (flatBump_nonneg _)

theorem fejerCorr_le_one (y : ℝ) : Rf y ≤ 1 := by
  have hd : (0 : ℝ) < 17 / 1000 := by norm_num
  have hdb : (17 / 1000 : ℝ) ≤ 17 / 50 := by norm_num
  have hle : ∀ t : ℝ, flatBump (17 / 50) (17 / 1000) t * flatBump (17 / 50) (17 / 1000) (t - y) ≤
      (Icc (-(17 / 50 : ℝ)) (17 / 50)).indicator (fun _ => (1 : ℝ)) t := by
    intro t
    by_cases ht : t ∈ Icc (-(17 / 50 : ℝ)) (17 / 50)
    · rw [indicator_of_mem ht]
      have h1 := flatBump_le_one (b := 17 / 50) (d := 17 / 1000) t
      have h2 := flatBump_le_one (b := 17 / 50) (d := 17 / 1000) (t - y)
      have h3 := flatBump_nonneg (b := 17 / 50) (d := 17 / 1000) (t - y)
      nlinarith [flatBump_nonneg (b := 17 / 50) (d := 17 / 1000) t]
    · rw [indicator_of_notMem ht]
      have : 17 / 50 ≤ |t| := by
        rw [mem_Icc, not_and_or, not_le, not_le] at ht
        rcases ht with h | h
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; linarith
      rw [flatBump_eq_zero hd this, zero_mul]
  have hint : Integrable ((Icc (-(17 / 50 : ℝ)) (17 / 50)).indicator (fun _ => (1 : ℝ))) :=
    (integrableOn_const (by simp) (by simp)).integrable_indicator measurableSet_Icc
  calc Rf y ≤ ∫ t : ℝ, (Icc (-(17 / 50 : ℝ)) (17 / 50)).indicator (fun _ => (1 : ℝ)) t :=
        integral_mono (integrable_flatBump_mul_shift hd hdb y) hint hle
    _ = 17 / 25 := by
        rw [integral_indicator_const _ measurableSet_Icc]
        simp
        norm_num
    _ ≤ 1 := by norm_num

theorem fejerCorr_eq_zero {y : ℝ} (hy : 17 / 25 ≤ |y|) : Rf y = 0 :=
  flatBumpCorr_eq_zero (by norm_num) (by linarith)

theorem seventeen_div_twentyfive_le_log {n : ℕ} (hn : 2 ≤ n) : 17 / 25 ≤ Real.log n := by
  have h2 : Real.log 2 ≤ Real.log n :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have := Real.log_two_gt_d9
  linarith

/-! ### Cosine moments of the corrected test -/

theorem integral_normSq_farPolarTest_mul_cos (X y : ℝ) :
    ∫ τ : ℝ, ‖paperFT (farPolarTest X) τ‖ ^ 2 * Real.cos (τ * y) =
      2 * π * ((1 + farPolarCoeff X ^ 2 / 2) * Rf y -
        farPolarCoeff X * (Rf (y - X) + Rf (y + X)) +
        farPolarCoeff X ^ 2 / 4 * (Rf (y - 2 * X) + Rf (y + 2 * X))) := by
  set c := farPolarCoeff X with hc
  set G : ℝ → ℝ → ℝ := fun t τ => ‖paperFT fejerTest τ‖ ^ 2 * Real.cos (τ * t) with hG
  have hI : ∀ t, Integrable (G t) := fun t =>
    integrable_normSq_paperFT_mul_cos contDiff_fejerTest tsupport_fejerTest t
  have hE : ∀ t, ∫ τ : ℝ, G t τ = 2 * π * Rf t := fun t =>
    integral_normSq_paperFT_fejerTest_mul_cos t
  have hpt : (fun τ : ℝ => ‖paperFT (farPolarTest X) τ‖ ^ 2 * Real.cos (τ * y)) =
      fun τ => ((1 + c ^ 2 / 2) * G y τ - c * (G (y - X) τ + G (y + X) τ)) +
        c ^ 2 / 4 * (G (y - 2 * X) τ + G (y + 2 * X) τ) := by
    funext τ
    simp only [hG]
    rw [normSq_paperFT_farPolarTest]
    have h1 : Real.cos (τ * (y - X)) = Real.cos (τ * y) * Real.cos (τ * X) +
        Real.sin (τ * y) * Real.sin (τ * X) := by rw [mul_sub, Real.cos_sub]
    have h2 : Real.cos (τ * (y + X)) = Real.cos (τ * y) * Real.cos (τ * X) -
        Real.sin (τ * y) * Real.sin (τ * X) := by rw [mul_add, Real.cos_add]
    have h3 : Real.cos (τ * (y - 2 * X)) = Real.cos (τ * y) * (2 * Real.cos (τ * X) ^ 2 - 1) +
        Real.sin (τ * y) * (2 * Real.sin (τ * X) * Real.cos (τ * X)) := by
      rw [mul_sub, Real.cos_sub, show τ * (2 * X) = 2 * (τ * X) by ring, Real.cos_two_mul,
        Real.sin_two_mul]
    have h4 : Real.cos (τ * (y + 2 * X)) = Real.cos (τ * y) * (2 * Real.cos (τ * X) ^ 2 - 1) -
        Real.sin (τ * y) * (2 * Real.sin (τ * X) * Real.cos (τ * X)) := by
      rw [mul_add, Real.cos_add, show τ * (2 * X) = 2 * (τ * X) by ring, Real.cos_two_mul,
        Real.sin_two_mul]
    rw [h1, h2, h3, h4]
    ring
  have i1 : Integrable (fun τ => (1 + c ^ 2 / 2) * G y τ) := (hI y).const_mul _
  have i2 : Integrable (fun τ => c * (G (y - X) τ + G (y + X) τ)) :=
    ((hI _).add (hI _)).const_mul _
  have i3 : Integrable (fun τ => c ^ 2 / 4 * (G (y - 2 * X) τ + G (y + 2 * X) τ)) :=
    ((hI _).add (hI _)).const_mul _
  have i12 : Integrable (fun τ => (1 + c ^ 2 / 2) * G y τ - c * (G (y - X) τ + G (y + X) τ)) :=
    i1.sub i2
  rw [hpt, integral_add i12 i3, integral_sub i1 i2, integral_const_mul,
    integral_const_mul, integral_const_mul, integral_add (hI _) (hI _),
    integral_add (hI _) (hI _), hE, hE, hE, hE, hE]
  ring

/-- At an atom `y = log n` only the correction lags `log n − X` and `log n − 2X` survive. -/
theorem integral_normSq_farPolarTest_mul_cos_log {X : ℝ} (hX : 0 ≤ X) {n : ℕ} (hn : 2 ≤ n) :
    ∫ τ : ℝ, ‖paperFT (farPolarTest X) τ‖ ^ 2 * Real.cos (τ * Real.log n) =
      2 * π * (farPolarCoeff X ^ 2 / 4 * Rf (Real.log n - 2 * X) -
        farPolarCoeff X * Rf (Real.log n - X)) := by
  have hl := seventeen_div_twentyfive_le_log hn
  rw [integral_normSq_farPolarTest_mul_cos,
    fejerCorr_eq_zero (y := Real.log n) (by rw [abs_of_pos (by linarith)]; linarith),
    fejerCorr_eq_zero (y := Real.log n + X) (by rw [abs_of_pos (by linarith)]; linarith),
    fejerCorr_eq_zero (y := Real.log n + 2 * X) (by rw [abs_of_pos (by linarith)]; linarith)]
  ring

/-! ### The archimedean energy of the corrected test -/

/-- `∫ |ψ̂|² |A|`, the absolute archimedean energy of the Fejér test. -/
def fejerArchAbsEnergy : ℝ :=
  ∫ τ : ℝ, |‖paperFT fejerTest τ‖ ^ 2 * archimedeanWeilSymbol (τ / (2 * π))|

theorem abs_sq_sub_one_le {c C : ℝ} (hc : 0 ≤ c) (hC : |C| ≤ 1) :
    |(1 - c * C) ^ 2 - 1| ≤ 2 * c + c ^ 2 := by
  have h1 := abs_le.mp hC
  have hC2 : C ^ 2 ≤ 1 := by nlinarith
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg C, mul_nonneg hc (sq_nonneg C)]

/-- The far correction changes the archimedean energy by at most `(2c + c²) ∫ |ψ̂|² |A|`. -/
theorem integral_arch_farPolarTest_le {X : ℝ} (hX : 0 ≤ X) :
    ∫ τ : ℝ, ‖paperFT (farPolarTest X) τ‖ ^ 2 * archimedeanWeilSymbol (τ / (2 * π)) ≤
      (∫ τ : ℝ, ‖paperFT fejerTest τ‖ ^ 2 * archimedeanWeilSymbol (τ / (2 * π))) +
        (2 * farPolarCoeff X + farPolarCoeff X ^ 2) * fejerArchAbsEnergy := by
  set c := farPolarCoeff X with hc
  have hA := integrable_normSq_paperFT_mul_arch contDiff_fejerTest tsupport_fejerTest
  have hAf := integrable_normSq_paperFT_mul_arch (contDiff_farPolarTest X)
    (tsupport_farPolarTest hX)
  unfold fejerArchAbsEnergy
  rw [← integral_const_mul, ← integral_add hA (hA.abs.const_mul _)]
  refine integral_mono hAf (hA.add (hA.abs.const_mul _)) fun τ => ?_
  simp only
  rw [normSq_paperFT_farPolarTest]
  set F := ‖paperFT fejerTest τ‖ ^ 2 * archimedeanWeilSymbol (τ / (2 * π))
  have hm := abs_sq_sub_one_le (farPolarCoeff_nonneg X) (Real.abs_cos_le_one (τ * X))
  have e : ‖paperFT fejerTest τ‖ ^ 2 * (1 - c * Real.cos (τ * X)) ^ 2 *
      archimedeanWeilSymbol (τ / (2 * π)) = F + ((1 - c * Real.cos (τ * X)) ^ 2 - 1) * F := by
    simp only [F]; ring
  rw [e]
  have : ((1 - c * Real.cos (τ * X)) ^ 2 - 1) * F ≤ (2 * c + c ^ 2) * |F| := by
    calc ((1 - c * Real.cos (τ * X)) ^ 2 - 1) * F
        ≤ |((1 - c * Real.cos (τ * X)) ^ 2 - 1) * F| := le_abs_self _
      _ = |(1 - c * Real.cos (τ * X)) ^ 2 - 1| * |F| := abs_mul _ _
      _ ≤ (2 * c + c ^ 2) * |F| := mul_le_mul_of_nonneg_right hm (abs_nonneg _)
  linarith

/-! ### Weil positivity forces a Chebyshev inequality at every scale -/

/-- **The far-polar Chebyshev inequality.**  If `lam` is Weil-positive then for every `X ≥ 0`,
with `c = 1/cosh(X/2)` and `R` the autocorrelation of the Fejér test `ψ`,
`−∫|ψ̂|²A − (2c + c²)∫|ψ̂|²|A| ≤ 4π Σ_{n} lam(n) n^{-1/2} (c R(log n − X) − (c²/4) R(log n − 2X))`,
the sum over `2 ≤ n ≤ e^{2X + 17/25}`.  The left side tends to `−∫|ψ̂|²A > 0`: the atoms of `lam`
at the scales `e^X` and `e^{2X}` must reproduce the polar term that the Fejér test lacks. -/
theorem weilPositive_farPolar_inequality {lam : ℕ → ℝ} (hW : WeilPositive lam) {X : ℝ}
    (hX : 0 ≤ X) :
    -(∫ τ : ℝ, ‖paperFT fejerTest τ‖ ^ 2 * archimedeanWeilSymbol (τ / (2 * π))) -
        (2 * farPolarCoeff X + farPolarCoeff X ^ 2) * fejerArchAbsEnergy ≤
      4 * π * ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * (X + 17 / 50))⌋₊, lam n / Real.sqrt n *
        (farPolarCoeff X * Rf (Real.log n - X) -
          farPolarCoeff X ^ 2 / 4 * Rf (Real.log n - 2 * X)) := by
  have ha : 0 ≤ X + 17 / 50 := by linarith
  have hE := hW (X + 17 / 50) ha (farPolarTest X) (contDiff_farPolarTest X)
    (tsupport_farPolarTest hX) (paperFT_farPolarTest_half_I X)
    (paperFT_farPolarTest_neg_half_I X)
  rw [integral_weilAtomSymbol_eq_arch_sub (contDiff_farPolarTest X) (tsupport_farPolarTest hX)]
    at hE
  have hterm : ∀ n ∈ Finset.Icc 2 ⌊Real.exp (2 * (X + 17 / 50))⌋₊,
      lam n / Real.sqrt n * (EF.weilTest (farPolarTest X) (farPolarTest X) (Real.log n) +
        EF.weilTest (farPolarTest X) (farPolarTest X) (-Real.log n)).re =
      -(2 * (lam n / Real.sqrt n * (farPolarCoeff X * Rf (Real.log n - X) -
        farPolarCoeff X ^ 2 / 4 * Rf (Real.log n - 2 * X)))) := by
    intro n hn
    have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
    have h1 := integral_normSq_paperFT_mul_cos_eq (contDiff_farPolarTest X)
      (tsupport_farPolarTest hX) (Real.log n)
    rw [integral_normSq_farPolarTest_mul_cos_log hX hn2] at h1
    have hπ := Real.pi_pos
    have : (EF.weilTest (farPolarTest X) (farPolarTest X) (Real.log n) +
        EF.weilTest (farPolarTest X) (farPolarTest X) (-Real.log n)).re =
        2 * (farPolarCoeff X ^ 2 / 4 * Rf (Real.log n - 2 * X) -
          farPolarCoeff X * Rf (Real.log n - X)) := by
      field_simp at h1 ⊢; linarith
    rw [this]; ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib, ← Finset.mul_sum] at hE
  have hA := integral_arch_farPolarTest_le hX
  have hπ := Real.pi_pos
  nlinarith

/-! ### Sparse weight systems are never Weil-positive -/

/-- The local atom mass `Σ_{|log n − X| ≤ 1} |lam(n)| n^{-1/2}` of `lam` at the scale `e^X`. -/
def localAtomMass (lam : ℕ → ℝ) (X : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 2 ⌊Real.exp (X + 1)⌋₊,
    if |Real.log n - X| ≤ 1 then |lam n| / Real.sqrt n else 0

theorem localAtomMass_nonneg (lam : ℕ → ℝ) (X : ℝ) : 0 ≤ localAtomMass lam X :=
  Finset.sum_nonneg fun n _ => by split_ifs <;> positivity

/-- A kernel supported in `|y| < 1` and bounded by one sees only the local atom mass. -/
theorem abs_sum_mul_fejerCorr_le (lam : ℕ → ℝ) (N : ℕ) (X : ℝ) :
    |∑ n ∈ Finset.Icc 2 N, lam n / Real.sqrt n * Rf (Real.log n - X)| ≤ localAtomMass lam X := by
  set g : ℕ → ℝ := fun n => if |Real.log n - X| ≤ 1 then |lam n| / Real.sqrt n else 0 with hg
  have hg0 : ∀ n, 0 ≤ g n := fun n => by simp only [hg]; split_ifs <;> positivity
  have hterm : ∀ n, |lam n / Real.sqrt n * Rf (Real.log n - X)| ≤ g n := by
    intro n
    by_cases h : |Real.log n - X| ≤ 1
    · simp only [hg, if_pos h]
      rw [abs_mul, abs_div, abs_of_nonneg (Real.sqrt_nonneg _),
        abs_of_nonneg (fejerCorr_nonneg _)]
      exact mul_le_of_le_one_right (by positivity) (fejerCorr_le_one _)
    · rw [fejerCorr_eq_zero (by linarith), mul_zero, abs_zero]
      exact hg0 n
  calc |∑ n ∈ Finset.Icc 2 N, lam n / Real.sqrt n * Rf (Real.log n - X)|
      ≤ ∑ n ∈ Finset.Icc 2 N, |lam n / Real.sqrt n * Rf (Real.log n - X)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Finset.Icc 2 N, g n := Finset.sum_le_sum fun n _ => hterm n
    _ = ∑ n ∈ (Finset.Icc 2 N).filter (fun n => g n ≠ 0), g n :=
        (Finset.sum_filter_ne_zero _).symm
    _ ≤ ∑ n ∈ Finset.Icc 2 ⌊Real.exp (X + 1)⌋₊, g n := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => ?_) fun n _ _ => hg0 n
        rw [Finset.mem_filter] at hn
        obtain ⟨hn1, hn2⟩ := hn
        have hin : |Real.log n - X| ≤ 1 := by
          by_contra h; apply hn2; simp only [hg, if_neg h]
        have h2 : 2 ≤ n := (Finset.mem_Icc.mp hn1).1
        have hpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
        refine Finset.mem_Icc.mpr ⟨h2, Nat.le_floor ?_⟩
        rw [← Real.exp_log hpos]
        exact Real.exp_le_exp.mpr (by linarith [(abs_le.mp hin).2])
    _ = localAtomMass lam X := rfl

theorem tendsto_farPolarCoeff : Tendsto farPolarCoeff atTop (𝓝 0) := by
  have h : Tendsto (fun X : ℝ => 2 * Real.exp (-(X / 2))) atTop (𝓝 0) := by
    have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 2))).const_mul 2
    simpa [Function.comp_def] using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h farPolarCoeff_nonneg
    farPolarCoeff_le

/-- **Sparse weight systems are never Weil-positive.**  If the local atom mass of `lam` at the
scale `e^X` is `o(e^{X/2})`, then `lam` is not Weil-positive.  The polar constraint is carried by
the far corrections at `±X`, whose multiplier `1 − cos(τX)/cosh(X/2)` tends to `1` uniformly; the
archimedean negativity of the Fejér test then survives unless the atoms near `e^X` and `e^{2X}` have
mass of order `e^{X/2}` and `e^X`, the density of the prime powers. -/
theorem not_weilPositive_of_localAtomMass {lam : ℕ → ℝ}
    (hsparse : Tendsto (fun X => Real.exp (-(X / 2)) * localAtomMass lam X) atTop (𝓝 0)) :
    ¬ WeilPositive lam := by
  intro hW
  set η := -(∫ τ : ℝ, ‖paperFT fejerTest τ‖ ^ 2 * archimedeanWeilSymbol (τ / (2 * π))) with hη
  have hη0 : 0 < η := by rw [hη]; linarith [integral_normSq_paperFT_fejerTest_mul_arch_neg]
  set I := fejerArchAbsEnergy
  have hsparse2 : Tendsto (fun X => Real.exp (-X) * localAtomMass lam (2 * X)) atTop (𝓝 0) := by
    have := hsparse.comp (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
    refine this.congr fun X => ?_
    simp only [Function.comp_apply, id]
    congr 2; ring
  set F : ℝ → ℝ := fun X => (2 * farPolarCoeff X + farPolarCoeff X ^ 2) * I +
    4 * π * (2 * (Real.exp (-(X / 2)) * localAtomMass lam X) +
      Real.exp (-X) * localAtomMass lam (2 * X)) with hF
  have hFt : Tendsto F atTop (𝓝 ((2 * 0 + 0 ^ 2) * I + 4 * π * (2 * 0 + 0))) := by
    refine Tendsto.add ((((tendsto_farPolarCoeff.const_mul 2).add
      (tendsto_farPolarCoeff.pow 2))).mul_const I) ?_
    exact ((hsparse.const_mul 2).add hsparse2).const_mul _
  have hF0 : Tendsto F atTop (𝓝 0) := by simpa using hFt
  obtain ⟨X, hXF, hX0⟩ := ((hF0.eventually (gt_mem_nhds hη0)).and
    (eventually_ge_atTop (0 : ℝ))).exists
  have hB := weilPositive_farPolar_inequality hW hX0
  set N := ⌊Real.exp (2 * (X + 17 / 50))⌋₊
  set c := farPolarCoeff X with hc
  have hc0 : 0 ≤ c := farPolarCoeff_nonneg X
  have hcle : c ≤ 2 * Real.exp (-(X / 2)) := farPolarCoeff_le X
  have hsplit : ∑ n ∈ Finset.Icc 2 N, lam n / Real.sqrt n *
      (c * Rf (Real.log n - X) - c ^ 2 / 4 * Rf (Real.log n - 2 * X)) =
      c * (∑ n ∈ Finset.Icc 2 N, lam n / Real.sqrt n * Rf (Real.log n - X)) -
        c ^ 2 / 4 * (∑ n ∈ Finset.Icc 2 N, lam n / Real.sqrt n * Rf (Real.log n - 2 * X)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  have h1 := abs_sum_mul_fejerCorr_le lam N X
  have h2 := abs_sum_mul_fejerCorr_le lam N (2 * X)
  have hM1 := localAtomMass_nonneg lam X
  have hM2 := localAtomMass_nonneg lam (2 * X)
  have hc2 : c ^ 2 ≤ 4 * Real.exp (-X) := by
    have : Real.exp (-(X / 2)) ^ 2 = Real.exp (-X) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    nlinarith
  have hbound : ∑ n ∈ Finset.Icc 2 N, lam n / Real.sqrt n *
      (c * Rf (Real.log n - X) - c ^ 2 / 4 * Rf (Real.log n - 2 * X)) ≤
      2 * (Real.exp (-(X / 2)) * localAtomMass lam X) +
        Real.exp (-X) * localAtomMass lam (2 * X) := by
    rw [hsplit]
    have a1 := (abs_le.mp h1).2
    have a2 := (abs_le.mp h2).1
    have e1 : c * (∑ n ∈ Finset.Icc 2 N, lam n / Real.sqrt n * Rf (Real.log n - X)) ≤
        c * localAtomMass lam X := mul_le_mul_of_nonneg_left a1 hc0
    have e2 : -(c ^ 2 / 4 * (∑ n ∈ Finset.Icc 2 N, lam n / Real.sqrt n *
        Rf (Real.log n - 2 * X))) ≤ c ^ 2 / 4 * localAtomMass lam (2 * X) := by
      have := mul_le_mul_of_nonneg_left (neg_le.mp a2) (by positivity : 0 ≤ c ^ 2 / 4)
      linarith
    have e3 : c * localAtomMass lam X ≤ 2 * Real.exp (-(X / 2)) * localAtomMass lam X :=
      mul_le_mul_of_nonneg_right hcle hM1
    have e4 : c ^ 2 / 4 * localAtomMass lam (2 * X) ≤
        Real.exp (-X) * localAtomMass lam (2 * X) := by
      apply mul_le_mul_of_nonneg_right _ hM2; linarith
    linarith
  have hπ := Real.pi_pos
  have : η ≤ F X := by
    simp only [hF]
    nlinarith
  linarith

theorem tendsto_add_mul_exp_neg {ε : ℝ} (hε : 0 < ε) (K : ℝ) :
    Tendsto (fun X : ℝ => (X + K) * Real.exp (-(ε * X))) atTop (𝓝 0) := by
  have hlin : Tendsto (fun X : ℝ => ε * X) atTop atTop := tendsto_id.const_mul_atTop hε
  have h1 : Tendsto (fun X : ℝ => (ε * X) ^ 1 * Real.exp (-(ε * X))) atTop (𝓝 0) :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hlin
  have h2 : Tendsto (fun X : ℝ => Real.exp (-(ε * X))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hlin
  have h3 := (h1.const_mul (1 / ε)).add (h2.const_mul K)
  simp only [mul_zero, add_zero] at h3
  refine h3.congr fun X => ?_
  field_simp
  ring

/-- **Weight systems on sparse position sets are never Weil-positive.**  If `lam` vanishes off a
set `P` of integers with `#(P ∩ [2, N]) ≤ C N^θ` for some `θ < 1/2`, then `lam` is not
Weil-positive.  Weil positivity bounds `|lam(n)| ≤ √n (log n + C₀)`, so the local atom mass at
`e^X` is `O(X e^{θX}) = o(e^{X/2})`.  This covers, for instance, weights supported on the
`S`-units of a finite set of primes, on the `k`-th powers with `k ≥ 3`, or on any lacunary set. -/
theorem not_weilPositive_of_sparse_support {lam : ℕ → ℝ} {P : ℕ → Prop} [DecidablePred P]
    (hP : ∀ n, ¬ P n → lam n = 0) {C θ : ℝ} (hC : 0 ≤ C) (hθ0 : 0 ≤ θ) (hθ : θ < 1 / 2)
    (hcount : ∀ N : ℕ, (((Finset.Icc 2 N).filter P).card : ℝ) ≤ C * (N : ℝ) ^ θ) :
    ¬ WeilPositive lam := by
  intro hW
  have hbox : ∀ n, 2 ≤ n → |lam n| ≤ boxWidth n := fun n hn =>
    abs_le_boxWidth_of_weilPositiveUpTo (fun a ha _ => hW a ha) hn le_rfl
  refine not_weilPositive_of_localAtomMass ?_ hW
  set K : ℝ := 1 + |boxConst| with hK
  set ε : ℝ := 1 / 2 - θ with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hU := (tendsto_add_mul_exp_neg hε0 K).const_mul (C * Real.exp θ)
  rw [mul_zero] at hU
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hU
    (Eventually.of_forall fun X => mul_nonneg (Real.exp_pos _).le (localAtomMass_nonneg lam X)) ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with X hX
  set N' := ⌊Real.exp (X + 1)⌋₊ with hN'
  have hterm : ∀ n ∈ Finset.Icc 2 N', (if |Real.log n - X| ≤ 1 then |lam n| / Real.sqrt n else 0) ≤
      if P n then X + K else 0 := by
    intro n hn
    have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
    have hpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr hpos
    by_cases hPn : P n
    · rw [if_pos hPn]
      split_ifs with h
      · have hb := hbox n hn2
        unfold boxWidth at hb
        rw [abs_mul, abs_of_pos hsq] at hb
        rw [div_le_iff₀ hsq]
        have hlog : Real.log n ≤ X + 1 := by linarith [(abs_le.mp h).2]
        have hl0 : 0 ≤ Real.log n := Real.log_nonneg (by linarith [(by exact_mod_cast hn2 :
          (2 : ℝ) ≤ n)])
        have : |Real.log n + boxConst| ≤ X + K := by
          rw [hK]
          have := abs_add_le (Real.log n) boxConst
          rw [abs_of_nonneg hl0] at this; linarith
        nlinarith
      · rw [hK]; positivity
    · rw [if_neg hPn, hP n hPn]; simp
  have hM : localAtomMass lam X ≤ (X + K) * (((Finset.Icc 2 N').filter P).card : ℝ) := by
    unfold localAtomMass
    calc _ ≤ ∑ n ∈ Finset.Icc 2 N', (if P n then X + K else 0) :=
          Finset.sum_le_sum hterm
      _ = (X + K) * (((Finset.Icc 2 N').filter P).card : ℝ) := by
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]; ring
  have hN'le : (N' : ℝ) ≤ Real.exp (X + 1) := Nat.floor_le (Real.exp_pos _).le
  have hpow : (N' : ℝ) ^ θ ≤ Real.exp (θ * (X + 1)) := by
    rw [mul_comm, Real.exp_mul]
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) hN'le hθ0
  have hXK : 0 ≤ X + K := by rw [hK]; positivity
  have hcard := hcount N'
  calc Real.exp (-(X / 2)) * localAtomMass lam X
      ≤ Real.exp (-(X / 2)) * ((X + K) * (C * Real.exp (θ * (X + 1)))) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        calc localAtomMass lam X ≤ (X + K) * (((Finset.Icc 2 N').filter P).card : ℝ) := hM
          _ ≤ (X + K) * (C * (N' : ℝ) ^ θ) := mul_le_mul_of_nonneg_left hcard hXK
          _ ≤ (X + K) * (C * Real.exp (θ * (X + 1))) := by
              apply mul_le_mul_of_nonneg_left _ hXK
              exact mul_le_mul_of_nonneg_left hpow hC
    _ = C * Real.exp θ * ((X + K) * Real.exp (-(ε * X))) := by
        have : Real.exp (-(X / 2)) * Real.exp (θ * (X + 1)) =
            Real.exp θ * Real.exp (-(ε * X)) := by
          rw [← Real.exp_add, ← Real.exp_add]; congr 1; rw [hε]; ring
        calc Real.exp (-(X / 2)) * ((X + K) * (C * Real.exp (θ * (X + 1))))
            = C * (X + K) * (Real.exp (-(X / 2)) * Real.exp (θ * (X + 1))) := by ring
          _ = _ := by rw [this]; ring

end RHTower
