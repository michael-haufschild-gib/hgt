import GaloisForLFunctions.RHTower.WeilWorkExposingRayLogLocalMass

/-!
# Actual signed harmonic twists at logarithmic spectral cost

Positive-integer characters suffice for the actual finite polar resonator.
No multiplicativity or norm condition is imposed at zero. The resulting
harmonic ceiling is uniform in the real twist and retains coefficient signs.
This is a component of CRITICAL-ONE-POLE-PROOF.md; endpoint recovery is not
asserted by this leaf.
-/

open Complex Finset MeasureTheory
open scoped Real ComplexConjugate
noncomputable section
namespace RHTower.ExposingRayTransfer
open WeilSpectral WeilOneSided

/-- Finite signed harmonic density of integer-product pairs. -/
def signedHarmonicDensity (lam : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 2 N, ∑ m ∈ Finset.Icc 1 N,
    if n*m ≤ N then lam n / ((n : ℝ)*m) else 0

private theorem positive_twisted_harmonic_bound {lam : ℕ → ℝ} {N : ℕ} {B : ℝ}
    (hBound : ∀ c : ℕ → ℂ, (∀ m, N < m → c m = 0) →
      2 * ∑ n ∈ Finset.Icc 2 N, lam n / Real.sqrt n *
        (∑ m ∈ Finset.Icc 1 N, c (n*m)*conj (c m)).re ≤
          B * ∑ m ∈ Finset.Icc 1 N, ‖c m‖^2)
    (χ : ℕ → ℂ)
    (hmul : ∀ m n, 1 ≤ m → 1 ≤ n → χ (m*n)=χ m*χ n)
    (hnorm : ∀ m, 1 ≤ m → ‖χ m‖=1) :
    2 * ∑ n ∈ Finset.Icc 2 N, ∑ m ∈ Finset.Icc 1 N,
      (if n*m ≤ N then lam n*(χ n).re / (n*m) else 0) ≤
        B * ∑ m ∈ Finset.Icc 1 N, (1 : ℝ)/m := by
  set c : ℕ → ℂ := fun m => if m ≤ N then χ m * ((1 / Real.sqrt m : ℝ) : ℂ) else 0 with hcdef
  have hc : ∀ m, N < m → c m = 0 := fun m hm => by simp [hcdef, not_le.mpr hm]
  have h := hBound c hc
  have hχconj : ∀ m, 1 ≤ m → χ m * conj (χ m) = 1 := fun m hm => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm m hm]; simp
  have hlhs : ∀ n ∈ Finset.Icc 2 N, lam n / Real.sqrt n *
      (∑ m ∈ Finset.Icc 1 N, c (n * m) * conj (c m)).re =
      ∑ m ∈ Finset.Icc 1 N, (if n * m ≤ N then lam n * (χ n).re / (n * m) else 0) := by
    intro n hn
    have hn1 : (0 : ℝ) < n := by
      have := (Finset.mem_Icc.mp hn).1; exact_mod_cast (show 0 < n by omega)
    rw [Complex.re_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    obtain ⟨hm1, hmN⟩ := Finset.mem_Icc.mp hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    by_cases hnm : n * m ≤ N
    · rw [if_pos hnm]
      simp only [hcdef, if_pos hnm, if_pos hmN, map_mul, Complex.conj_ofReal, hmul n m (by have := (Finset.mem_Icc.mp hn).1; omega) hm1]
      have hsq : Real.sqrt ((n * m : ℕ) : ℝ) = Real.sqrt n * Real.sqrt m := by
        push_cast; exact Real.sqrt_mul hn1.le _
      rw [hsq]
      have hsm : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt hm0.le
      have hr : (1 / (Real.sqrt n * Real.sqrt m)) * (1 / Real.sqrt m) = 1 / (Real.sqrt n * m) := by
        rw [div_mul_div_comm, one_mul, mul_assoc, hsm]
      have e : χ n * χ m * ((1 / (Real.sqrt n * Real.sqrt m) : ℝ) : ℂ) *
          (conj (χ m) * ((1 / Real.sqrt m : ℝ) : ℂ)) =
          χ n * (χ m * conj (χ m)) * ((1 / (Real.sqrt n * m) : ℝ) : ℂ) := by
        rw [← hr]; push_cast; ring
      rw [e, hχconj m hm1, mul_one, Complex.re_mul_ofReal]
      have hsn : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn1.le
      have hsn0 : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn1
      calc lam n / Real.sqrt n * ((χ n).re * (1 / (Real.sqrt n * m)))
          = lam n * (χ n).re / ((Real.sqrt n * Real.sqrt n) * m) := by field_simp
        _ = lam n * (χ n).re / (n * m) := by rw [hsn]
    · rw [if_neg hnm]
      simp [hcdef, if_neg hnm]
  have hrhs : ∑ m ∈ Finset.Icc 1 N, ‖c m‖ ^ 2 = ∑ m ∈ Finset.Icc 1 N, (1 : ℝ) / m := by
    refine Finset.sum_congr rfl fun m hm => ?_
    obtain ⟨hm1, hmN⟩ := Finset.mem_Icc.mp hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    simp only [hcdef, if_pos hmN, norm_mul, hnorm m hm1, one_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos (by positivity), div_pow, one_pow, Real.sq_sqrt hm0.le]
  rw [Finset.sum_congr rfl hlhs, hrhs] at h
  exact h


/-- The literal real-frequency twist; its zero value is irrelevant. -/
def criticalLogTwist (t : ℝ) (n : ℕ) : ℂ :=
  Complex.exp (I * ((t*Real.log n : ℝ) : ℂ))

theorem criticalLogTwist_mul (t : ℝ) {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    criticalLogTwist t (m*n)=criticalLogTwist t m*criticalLogTwist t n := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  unfold criticalLogTwist
  rw [Nat.cast_mul,Real.log_mul hm0 hn0]
  have he : I * ((t*(Real.log m+Real.log n) : ℝ) : ℂ) =
      I*((t*Real.log m : ℝ) : ℂ)+I*((t*Real.log n : ℝ) : ℂ) := by
    push_cast; ring
  rw [he,Complex.exp_add]

theorem norm_criticalLogTwist (t : ℝ) (n : ℕ) : ‖criticalLogTwist t n‖=1 := by
  simp only [criticalLogTwist,Complex.norm_exp,Complex.mul_re,Complex.I_re,
    Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,mul_zero,sub_zero,Real.exp_zero]

theorem re_criticalLogTwist (t : ℝ) (n : ℕ) :
    (criticalLogTwist t n).re=Real.cos (t*Real.log n) := by
  simp only [criticalLogTwist,Complex.exp_re,Complex.mul_re,Complex.mul_im,Complex.I_re,
    Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,mul_zero,one_mul,sub_zero,
    zero_add,Real.exp_zero]

/-- Actual polar separators control every positive-integer multiplicative twist. -/
theorem log_twisted_harmonic_bound {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    {b : ℕ → ℝ} {ell : Lp ℝ 1 (volume : Measure ℝ) →L[ℝ] ℝ}
    (h : ∀ f : WeilTestFn, (∃ a, IsPolarTest a f.1) →
      atomValue b f.1 ≤ ell (logDensityL1 hβ hβ1 f))
    {N : ℕ} (hN : 1 ≤ N) (χ : ℕ → ℂ)
    (hmul : ∀ m n, 1 ≤ m → 1 ≤ n → χ (m*n)=χ m*χ n)
    (hnorm : ∀ m, 1 ≤ m → ‖χ m‖=1) :
    2 * signedHarmonicDensity (fun n => b n*Real.sqrt n*(χ n).re) N ≤
      (2*Real.pi*‖ell‖*(1+(Real.log N+sublogResonatorConstant)^β))*
        ∑ m ∈ Finset.Icc 1 N, (1 : ℝ)/m := by
  have hB : ∀ c : ℕ → ℂ, (∀ m, N < m → c m=0) →
      2 * ∑ n ∈ Finset.Icc 2 N, (b n*Real.sqrt n)/Real.sqrt n *
        (∑ m ∈ Finset.Icc 1 N, c (n*m)*conj (c m)).re ≤
      (2*Real.pi*‖ell‖*(1+(Real.log N+sublogResonatorConstant)^β))*
        ∑ m ∈ Finset.Icc 1 N, ‖c m‖^2 := by
    intro c hc
    have hb := log_toeplitz_of_polar_bound hβ hβ1 h N hN c hc
    convert hb using 1
    congr 1
    apply Finset.sum_congr rfl
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by have := (Finset.mem_Icc.mp hn).1; omega : 0 < n)
    rw [mul_div_cancel_right₀ _ (Real.sqrt_pos.mpr hn0).ne']
  exact positive_twisted_harmonic_bound hB χ hmul hnorm

/-- A quadratic harmonic ceiling uniform in every real twist, derived from
actual polar positivity at the critical logarithmic weight. -/
theorem critical_harmonic_cosine_ceiling
    {b : ℕ → ℝ} {ell : Lp ℝ 1 (volume : Measure ℝ) →L[ℝ] ℝ}
    (h : ∀ f : WeilTestFn, (∃ a, IsPolarTest a f.1) →
      atomValue b f.1 ≤ ell (logDensityL1 (by norm_num : (0 : ℝ) ≤ 1) le_rfl f)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N → ∀ t : ℝ,
      signedHarmonicDensity
        (fun n => b n*Real.sqrt n*Real.cos (t*Real.log n)) N ≤ C*(1+Real.log N)^2 := by
  let D := 2*Real.pi*‖ell‖
  let C := D*(1+sublogResonatorConstant)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hK : 0 ≤ sublogResonatorConstant := le_trans (by norm_num) one_le_sublogResonatorConstant
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C,hC,fun N hN t => ?_⟩
  have hu := log_twisted_harmonic_bound (by norm_num : (0 : ℝ) ≤ 1) le_rfl h hN
    (criticalLogTwist t) (fun m n hm hn => criticalLogTwist_mul t hm hn)
    (fun m _ => norm_criticalLogTwist t m)
  simp only [re_criticalLogTwist,Real.rpow_one] at hu
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hH := sum_Icc_inv_le_one_add_log N
  have hB0 : 0 ≤ D*(1+(Real.log N+sublogResonatorConstant)) := by positivity
  have hB : D*(1+(Real.log N+sublogResonatorConstant)) ≤ C*(1+Real.log N) := by
    dsimp [C]
    nlinarith [mul_nonneg hD (mul_nonneg hK hlog)]
  have h1 := mul_le_mul_of_nonneg_left hH hB0
  have h2 := mul_le_mul_of_nonneg_right hB (by linarith : 0 ≤ 1+Real.log (N : ℝ))
  change 2 * _ ≤ D*(1+(Real.log N+sublogResonatorConstant))*_ at hu
  have hpos : 0 ≤ C*(1+Real.log (N : ℝ))^2 := by positivity
  nlinarith only [hu,h1,h2,hpos]

end RHTower.ExposingRayTransfer
