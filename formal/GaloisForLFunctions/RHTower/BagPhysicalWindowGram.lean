import GaloisForLFunctions.RHTower.LogPhasePhysicalWindow
import GaloisForLFunctions.RHTower.Sieve.LogSeparation
import GaloisForLFunctions.RHTower.ZetaChiDualResonatorIntegral
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# Signed Gram form of the actual smooth physical window

The source window supplies its own Schwartz regularity and positive mass.
Exact Fourier scaling yields a quadratic shift envelope at literal product
frequencies. The full complex Gram identity retains every signed cross term;
the absolute error bound leaves the weighted shift sum explicit.
-/

noncomputable section
open Complex MeasureTheory Set Filter FourierTransform
open scoped Topology ContDiff FourierTransform ComplexConjugate
namespace RHTower
open GaloisForLFunctions.RHTower

/-- The source height window as an actual Schwartz function. -/
def bagPhysicalHeightSchwartz : SchwartzMap ℝ ℂ :=
  (bagPhysicalHeightWindow.hasCompactSupport.comp_left (g := Complex.ofReal) (by rfl)).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp bagPhysicalHeightWindow.contDiff)

/-- The complete signed zero-grade physical kernel. -/
def bagPhysicalLinearKernel (T L : ℝ) : ℂ :=
  ∫ t : ℝ, (bagPhysicalHeightWindow (t / T) : ℂ) * bourgainOscillation (t * L)

/-- Exact full-window Fourier transform, with the actual source cutoff. -/
theorem bagPhysicalLinearKernel_eq_fourier {T : ℝ} (hT : 0 < T) (L : ℝ) :
    bagPhysicalLinearKernel T L = (T : ℂ) *
      (𝓕 bagPhysicalHeightSchwartz) (-(T * L) / (2 * Real.pi)) := by
  let f : ℝ → ℂ := fun t => (bagPhysicalHeightWindow (t / T) : ℂ) * bourgainOscillation (t * L)
  have hs := MeasureTheory.Measure.integral_comp_mul_left f T
  rw [abs_of_pos (inv_pos.mpr hT), Complex.real_smul] at hs
  have hscale : bagPhysicalLinearKernel T L = (T : ℂ) * ∫ u : ℝ, f (T * u) := by
    rw [hs, Complex.ofReal_inv]
    change (∫ t, f t) = _
    field_simp [Complex.ofReal_ne_zero.mpr hT.ne']
  rw [hscale, SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with u
  have hphase : -2 * Real.pi * u * (-(T * L) / (2 * Real.pi)) = T * u * L := by
    field_simp [Real.pi_ne_zero]
  simp only [hphase, smul_eq_mul, bagPhysicalHeightSchwartz,
    HasCompactSupport.toSchwartzMap_toFun, Function.comp_apply, f, bourgainOscillation]
  rw [mul_div_cancel_left₀ _ hT.ne']
  ring_nf

/-- One source constant controls the full kernel and its quadratic frequency moment. -/
theorem exists_bagPhysicalLinearKernel_moment_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T → ∀ L : ℝ,
      ‖bagPhysicalLinearKernel T L‖ ≤ C * T ∧
      (T * L) ^ 2 * ‖bagPhysicalLinearKernel T L‖ ≤ C * T := by
  obtain ⟨C₀, hC₀, h₀⟩ := (𝓕 bagPhysicalHeightSchwartz).decay 0 0
  obtain ⟨C₂, hC₂, h₂⟩ := (𝓕 bagPhysicalHeightSchwartz).decay 2 0
  simp only [norm_iteratedFDeriv_zero, pow_zero, one_mul] at h₀
  simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs, sq_abs] at h₂
  refine ⟨C₀ + (2 * Real.pi) ^ 2 * C₂, by positivity, ?_⟩
  intro T hT L
  rw [bagPhysicalLinearKernel_eq_fourier hT, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hT]
  let x := -(T * L) / (2 * Real.pi)
  have hx : (T * L) ^ 2 = (2 * Real.pi) ^ 2 * x ^ 2 := by
    dsimp only [x]
    field_simp [Real.pi_ne_zero]
  constructor
  · have hh := mul_le_mul_of_nonneg_left (h₀ x) hT.le
    dsimp only [x] at hh
    nlinarith [mul_nonneg (by positivity : 0 ≤ (2 * Real.pi) ^ 2 * C₂) hT.le]
  · rw [hx]
    have hh := mul_le_mul_of_nonneg_left (h₂ x) (by positivity : 0 ≤ T * (2 * Real.pi) ^ 2)
    dsimp only [x] at hh
    nlinarith

private theorem real_gap_le_upper_mul_log_gap {x y R : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hxR : x ≤ R) (hyR : y ≤ R) :
    |x - y| ≤ R * |Real.log x - Real.log y| := by
  rcases le_total y x with h | h
  · have hl := Sieve.log_sub_ge hy h
    have hl0 : 0 ≤ Real.log x - Real.log y := sub_nonneg.mpr (Real.log_le_log hy h)
    rw [abs_of_nonneg (sub_nonneg.mpr h), abs_of_nonneg hl0]
    have hh := (div_le_iff₀ hx).mp hl
    nlinarith
  · have hl := Sieve.log_sub_ge hx h
    have hl0 : 0 ≤ Real.log y - Real.log x := sub_nonneg.mpr (Real.log_le_log hx h)
    rw [abs_of_nonpos (sub_nonpos.mpr h), abs_of_nonpos (by linarith : Real.log x - Real.log y ≤ 0)]
    have hh := (div_le_iff₀ hy).mp hl
    nlinarith

/-- Full actual shift decay at positive product frequencies bounded by T*Q. -/
theorem exists_bagPhysicalLinearKernel_shift_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ T Q : ℝ, 0 < T → 0 < Q →
      ∀ j k : ℕ, 0 < j → 0 < k → (j : ℝ) ≤ T * Q → (k : ℝ) ≤ T * Q → j ≠ k →
      ‖bagPhysicalLinearKernel T (Real.log j - Real.log k)‖ ≤
        C * T * min 1 ((Q / |(j : ℝ) - k|) ^ 2) := by
  obtain ⟨C, hC, hb⟩ := exists_bagPhysicalLinearKernel_moment_bound
  refine ⟨C, hC, ?_⟩
  intro T Q hT hQ j k hj hk hjR hkR hjk
  have hj' : (0 : ℝ) < j := by exact_mod_cast hj
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hgap : 0 < |(j : ℝ) - k| := abs_pos.mpr (sub_ne_zero.mpr (by exact_mod_cast hjk))
  have hh := real_gap_le_upper_mul_log_gap hj' hk' hjR hkR
  have hh2 : |(j : ℝ) - k| ^ 2 ≤ (T * Q * |Real.log j - Real.log k|) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) hh 2
  have hkb := hb T hT (Real.log j - Real.log k)
  rw [mul_min_of_nonneg _ _ (by positivity : 0 ≤ C * T)]
  apply le_min
  · simpa only [mul_one] using hkb.1
  · have hh3 := mul_le_mul_of_nonneg_right hh2 (norm_nonneg (bagPhysicalLinearKernel T (Real.log j - Real.log k)))
    have hh4 := mul_le_mul_of_nonneg_left hkb.2 (sq_nonneg Q)
    rw [div_pow, ← mul_div_assoc, le_div_iff₀ (sq_pos_of_pos hgap)]
    simp only [mul_pow, sq_abs] at hh3 ⊢
    nlinarith

/-- The full kernel equals its literal physical interval integral; the source
cutoff vanishes outside that interval, including its lower endpoint. -/
theorem bagPhysicalLinearKernel_eq_interval {T : ℝ} (hT : 0 < T) (L : ℝ) :
    bagPhysicalLinearKernel T L = ∫ t in T..2 * T,
      (bagPhysicalHeightWindow (t / T) : ℂ) * bourgainOscillation (t * L) := by
  symm
  apply intervalIntegral.integral_eq_integral_of_support_subset
  intro t ht
  have hw : bagPhysicalHeightWindow (t / T) ≠ 0 := by
    intro hh
    exact ht (by simp only [hh, Complex.ofReal_zero, zero_mul])
  have hm : t / T ∈ Metric.ball (3 / 2 : ℝ) bagPhysicalHeightWindow.rOut := by
    rw [← bagPhysicalHeightWindow.support_eq]
    exact hw
  have hb : |t / T - 3 / 2| < (1 / 2 : ℝ) := by simpa only [Metric.mem_ball, Real.dist_eq, bagPhysicalHeightWindow] using hm
  have hs := abs_lt.mp hb
  constructor
  · have hh : 1 < t / T := by linarith only [hs.1]
    simpa only [one_mul] using (lt_div_iff₀ hT).mp hh
  · have hh : t / T < 2 := by linarith only [hs.2]
    exact ((div_lt_iff₀ hT).mp hh).le

/-- The fixed positive physical window mass. -/
def bagPhysicalHeightMass : ℝ := ∫ u in (1 : ℝ)..2, bagPhysicalHeightWindow u

theorem bagPhysicalHeightMass_pos : 0 < bagPhysicalHeightMass := by
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
    (bagPhysicalHeightWindow.continuous.intervalIntegrable _ _) _ (by norm_num)
  intro u hu
  apply bagPhysicalHeightWindow.pos_of_mem_ball
  change |u - 3 / 2| < (1 / 2 : ℝ)
  rw [abs_lt]
  constructor <;> linarith only [hu.1, hu.2]

/-- The full diagonal mass is exactly T times the source window mass. -/
theorem bagPhysicalLinearKernel_zero {T : ℝ} (hT : 0 < T) :
    bagPhysicalLinearKernel T 0 = ((T * bagPhysicalHeightMass : ℝ) : ℂ) := by
  rw [bagPhysicalLinearKernel_eq_interval hT]
  simp only [mul_zero, bourgainOscillation, Complex.ofReal_zero, Complex.exp_zero, mul_one]
  rw [intervalIntegral.integral_comp_div (fun u => (bagPhysicalHeightWindow u : ℂ)) hT.ne']
  simp only [div_self hT.ne', mul_div_cancel_right₀ _ hT.ne', Complex.real_smul,
    intervalIntegral.integral_ofReal, Complex.ofReal_mul, bagPhysicalHeightMass]

/-- Exact signed physical Gram form for every finite complex resonator. -/
theorem integral_bagPhysicalWindow_resonator_sq {T : ℝ} (hT : 0 < T)
    (S : Finset ℕ) (c : ℕ → ℂ) (hS : ∀ j ∈ S, 0 < j) :
    (∫ t in T..2 * T, (bagPhysicalHeightWindow (t / T) : ℂ) *
      ((‖zetaChiDualResonator S c t‖ ^ 2 : ℝ) : ℂ)) =
      ∑ j ∈ S, ∑ k ∈ S, c j * conj (c k) *
        bagPhysicalLinearKernel T (Real.log j - Real.log k) := by
  have hc (j k : ℕ) : Continuous (fun t : ℝ => c j * conj (c k) *
      ((bagPhysicalHeightWindow (t / T) : ℂ) * bourgainOscillation (t * (Real.log j - Real.log k)))) := by
    unfold bourgainOscillation
    exact continuous_const.mul (((Complex.continuous_ofReal.comp
      (bagPhysicalHeightWindow.continuous.comp (continuous_id.div_const T)))).mul (by fun_prop))
  calc
    _ = ∫ t in T..2 * T, ∑ j ∈ S, ∑ k ∈ S, c j * conj (c k) *
        ((bagPhysicalHeightWindow (t / T) : ℂ) * bourgainOscillation (t * (Real.log j - Real.log k))) := by
      apply intervalIntegral.integral_congr
      intro t _
      dsimp only
      rw [zetaChiDualResonator_norm_sq_eq S c hS, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Real.log_div (by exact_mod_cast (hS j hj).ne') (by exact_mod_cast (hS k hk).ne')]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_finsetSum (fun j _ =>
        (continuous_finsetSum S (fun k _ => hc j k)).intervalIntegrable _ _)]
      apply Finset.sum_congr rfl
      intro j _
      rw [intervalIntegral.integral_finsetSum (fun k _ => (hc j k).intervalIntegrable _ _)]
      simp_rw [intervalIntegral.integral_const_mul, ← bagPhysicalLinearKernel_eq_interval hT]

/-- The full physical signed remainder after removing exactly the coefficient diagonal. -/
theorem integral_bagPhysicalWindow_resonator_sq_sub_diagonal {T : ℝ} (hT : 0 < T)
    (S : Finset ℕ) (c : ℕ → ℂ) (hS : ∀ j ∈ S, 0 < j) :
    (∫ t in T..2 * T, (bagPhysicalHeightWindow (t / T) : ℂ) *
      ((‖zetaChiDualResonator S c t‖ ^ 2 : ℝ) : ℂ)) -
        (((T * bagPhysicalHeightMass * ∑ j ∈ S, ‖c j‖ ^ 2 : ℝ)) : ℂ) =
      ∑ j ∈ S, ∑ k ∈ S.erase j, c j * conj (c k) *
        bagPhysicalLinearKernel T (Real.log j - Real.log k) := by
  classical
  rw [integral_bagPhysicalWindow_resonator_sq hT S c hS]
  have he (j : ℕ) (hj : j ∈ S) :
      ∑ k ∈ S, c j * conj (c k) * bagPhysicalLinearKernel T (Real.log j - Real.log k) =
      c j * conj (c j) * bagPhysicalLinearKernel T 0 +
        ∑ k ∈ S.erase j, c j * conj (c k) * bagPhysicalLinearKernel T (Real.log j - Real.log k) := by
    rw [← Finset.add_sum_erase S _ hj, sub_self]
  rw [Finset.sum_congr rfl he, Finset.sum_add_distrib]
  suffices hh : (∑ j ∈ S, c j * conj (c j) * bagPhysicalLinearKernel T 0) =
      (((T * bagPhysicalHeightMass * ∑ j ∈ S, ‖c j‖ ^ 2 : ℝ)) : ℂ) by rw [hh]; ring
  simp_rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, bagPhysicalLinearKernel_zero hT]
  rw [← Finset.sum_mul]
  push_cast
  ring

/-- The complete physical off-diagonal has summable squared-shift decay. The
coefficient-weighted shift sum remains explicit, without a false independence claim. -/
theorem exists_bagPhysicalWindow_resonator_shift_error_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ T Q : ℝ, 0 < T → 0 < Q →
      ∀ S : Finset ℕ, (∀ j ∈ S, 0 < j ∧ (j : ℝ) ≤ T * Q) → ∀ c : ℕ → ℂ,
      ‖(∫ t in T..2 * T, (bagPhysicalHeightWindow (t / T) : ℂ) *
          ((‖zetaChiDualResonator S c t‖ ^ 2 : ℝ) : ℂ)) -
        (((T * bagPhysicalHeightMass * ∑ j ∈ S, ‖c j‖ ^ 2 : ℝ)) : ℂ)‖ ≤
        C * T * ∑ j ∈ S, ∑ k ∈ S.erase j, ‖c j‖ * ‖c k‖ *
          min 1 ((Q / |(j : ℝ) - k|) ^ 2) := by
  classical
  obtain ⟨C, hC, hb⟩ := exists_bagPhysicalLinearKernel_shift_bound
  refine ⟨C, hC, ?_⟩
  intro T Q hT hQ S hS c
  rw [integral_bagPhysicalWindow_resonator_sq_sub_diagonal hT S c (fun j hj => (hS j hj).1)]
  calc
    _ ≤ ∑ j ∈ S, ∑ k ∈ S.erase j, ‖c j * conj (c k) *
        bagPhysicalLinearKernel T (Real.log j - Real.log k)‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ => norm_sum_le _ _))
    _ ≤ ∑ j ∈ S, ∑ k ∈ S.erase j, C * T * (‖c j‖ * ‖c k‖ * min 1 ((Q / |(j : ℝ) - k|) ^ 2)) := by
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum
      intro k hk
      obtain ⟨hkj, hkS⟩ := Finset.mem_erase.mp hk
      have hh := hb T Q hT hQ j k (hS j hj).1 (hS k hkS).1 (hS j hj).2 (hS k hkS).2 hkj.symm
      simp only [norm_mul, norm_conj]
      calc
        _ ≤ ‖c j‖ * ‖c k‖ * (C * T * min 1 ((Q / |(j : ℝ) - k|) ^ 2)) :=
          mul_le_mul_of_nonneg_left hh (by positivity)
        _ = _ := by ring
    _ = _ := by simp_rw [← Finset.mul_sum]

end RHTower
