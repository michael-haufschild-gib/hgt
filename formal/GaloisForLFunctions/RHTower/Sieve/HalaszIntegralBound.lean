import GaloisForLFunctions.RHTower.Sieve.HalaszLargeValueWindow
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# The Halász integral bound for the whole Dirichlet series

The series is continuous in the frequency, by the Weierstrass test against `∑_n n^{-σ}`.  Its
large-value set is therefore open, and the covering estimate bounds that set's measure.  Splitting the
integral over `[-T, T]` at the damped level then gives

`∫_{-T}^{T} ‖∑_n f(n)n^{-σ-it}‖ dt ≤ damped · 2T + trivial · measure(large values)`,

with `damped = (1 + 1/(σ−1)) e^{7/2+shift−δ²}` and `trivial = (1 + 1/(σ−1)) e^{7/2}`.  Both terms are
explicit, so the estimate is a genuine mean-value bound: the first term is the size off the exceptional
window, the second is the trivial size times the width of that window.
-/

namespace RHTower.Sieve

open Complex MeasureTheory Set

section

variable {f : ℕ → ℂ}

/-- **The series is continuous in the frequency.**  Weierstrass test against `∑_n n^{-σ}`. -/
theorem continuous_tsum_twistedSummand (hbdd : ∀ n, ‖f n‖ ≤ 1) {σ : ℝ} (hσ : 1 < σ) :
    Continuous (fun t : ℝ =>
      ∑' n : ℕ, twistedSummand f (((σ : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I) n) := by
  have hsne : ∀ t : ℝ, (((σ : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I) ≠ 0 := by
    intro t hzero
    have hre : (((σ : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I).re = σ := re_ofReal_add_mul_I σ t
    rw [hzero] at hre
    simp at hre
    linarith
  refine continuous_tsum (u := fun n : ℕ => ((n : ℝ)) ^ (-σ)) (fun n => ?_)
    (summable_nat_rpow_neg hσ) (fun n t => ?_)
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hzero : ∀ t : ℝ,
          twistedSummand f (((σ : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I) 0 = 0 :=
        fun t => twistedSummand_zero (hsne t)
      simpa [hzero] using continuous_const
    · have hne : ((n : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
      simp only [twistedSummand]
      refine continuous_const.mul (Continuous.const_cpow ?_ (Or.inl hne))
      fun_prop
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [twistedSummand_zero (hsne t), norm_zero]
      exact Real.rpow_nonneg (by norm_num) _
    · have h := norm_twistedSummand_le hbdd
        (s := ((σ : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I) hn
      rwa [re_ofReal_add_mul_I] at h

/-- **The Halász integral bound.**  Off one window the series obeys the damped bound; on the window it
obeys the trivial bound, and the window is thin. -/
theorem integral_norm_tsum_twistedSummand_le
    (hf1 : f 1 = 1) (hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n)
    (hbdd : ∀ n, ‖f n‖ ≤ 1) {σ : ℝ} (hσ : 1 < σ) {z : ℕ} (hz2 : 2 ≤ z)
    {δ : ℝ} (hδ : 0 ≤ δ) (hW : 0 < logSqWeight z) {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in Set.Icc (-T) T,
        ‖∑' n : ℕ, twistedSummand f (((σ : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I) n‖)
      ≤ (1 + 1 / (σ - 1)) *
            Real.exp (7 / 2 + 2 * (σ - 1) * (Real.log z + Real.log 4) - δ ^ 2) * (2 * T)
          + (1 + 1 / (σ - 1)) * Real.exp (7 / 2) *
            ((2 * T * Real.log (z : ℝ) / Real.pi + 1) *
              (2 * Real.sqrt (2 * Real.pi ^ 2 * δ ^ 2 / logSqWeight z))) := by
  classical
  set G : ℝ → ℝ := fun t =>
    ‖∑' n : ℕ, twistedSummand f (((σ : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I) n‖ with hG
  set damped : ℝ := (1 + 1 / (σ - 1)) *
    Real.exp (7 / 2 + 2 * (σ - 1) * (Real.log z + Real.log 4) - δ ^ 2) with hdamped
  set triv : ℝ := (1 + 1 / (σ - 1)) * Real.exp (7 / 2) with htriv
  have hcont : Continuous G := (continuous_tsum_twistedSummand hbdd hσ).norm
  have hGint : IntegrableOn G (Set.Icc (-T) T) := hcont.integrableOn_Icc
  set A : Set ℝ := {t : ℝ | damped < G t} with hA
  have hAopen : IsOpen A := isOpen_lt continuous_const hcont
  have hAmeas : MeasurableSet A := hAopen.measurableSet
  have hdamped0 : 0 ≤ damped := by
    rw [hdamped]
    have h1 : 0 < σ - 1 := by linarith
    positivity
  have htriv0 : 0 ≤ triv := by
    rw [htriv]
    have h1 : 0 < σ - 1 := by linarith
    positivity
  -- split at the damped level
  have hsplit : (∫ t in Set.Icc (-T) T ∩ A, G t) + ∫ t in Set.Icc (-T) T \ A, G t
      = ∫ t in Set.Icc (-T) T, G t :=
    setIntegral_inter_add_diff hAmeas hGint
  -- on the window, the trivial bound
  have hwindow : (∫ t in Set.Icc (-T) T ∩ A, G t)
      ≤ (volume (Set.Icc (-T) T ∩ A)).toReal * triv := by
    have hbound : ∀ t ∈ Set.Icc (-T) T ∩ A, G t ≤ triv := by
      intro t _
      have h := norm_tsum_twistedSummand_le_trivial hf1 hmul hbdd
        (s := ((σ : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I)
        (by rw [re_ofReal_add_mul_I]; exact hσ)
      rw [re_ofReal_add_mul_I] at h
      exact h
    have hmeas : MeasurableSet (Set.Icc (-T) T ∩ A) := measurableSet_Icc.inter hAmeas
    have hfin : volume (Set.Icc (-T) T ∩ A) ≠ ⊤ :=
      ne_top_of_le_ne_top (by simp [Real.volume_Icc]) (measure_mono inter_subset_left)
    have hint2 : IntegrableOn (fun _ : ℝ => triv) (Set.Icc (-T) T ∩ A) :=
      integrableOn_const_of_ne_top hfin
    refine le_trans (setIntegral_mono_on (hGint.mono_set inter_subset_left) hint2 hmeas hbound) ?_
    rw [setIntegral_const, measureReal_def, smul_eq_mul]
  -- off the window, the damped bound
  have hoff : (∫ t in Set.Icc (-T) T \ A, G t) ≤ damped * (2 * T) := by
    have hbound : ∀ t ∈ Set.Icc (-T) T \ A, G t ≤ damped := by
      intro t ht
      have : ¬ (damped < G t) := by
        intro hlt
        exact ht.2 hlt
      exact le_of_not_lt this
    have hmeas : MeasurableSet (Set.Icc (-T) T \ A) := measurableSet_Icc.diff hAmeas
    have hfin : volume (Set.Icc (-T) T \ A) ≠ ⊤ :=
      ne_top_of_le_ne_top (by simp [Real.volume_Icc]) (measure_mono diff_subset)
    have hint2 : IntegrableOn (fun _ : ℝ => damped) (Set.Icc (-T) T \ A) :=
      integrableOn_const_of_ne_top hfin
    refine le_trans (setIntegral_mono_on (hGint.mono_set diff_subset) hint2 hmeas hbound) ?_
    rw [setIntegral_const, measureReal_def, smul_eq_mul]
    have hvol : (volume (Set.Icc (-T) T \ A)).toReal ≤ 2 * T := by
      have hle : volume (Set.Icc (-T) T \ A) ≤ volume (Set.Icc (-T) T) :=
        measure_mono diff_subset
      have hIcc : (volume (Set.Icc (-T) T)).toReal = 2 * T := by
        rw [Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
        ring
      have hfin2 : volume (Set.Icc (-T) T) ≠ ⊤ := by simp [Real.volume_Icc]
      have := ENNReal.toReal_mono hfin2 hle
      rwa [hIcc] at this
    exact mul_le_mul_of_nonneg_right hvol hdamped0
  -- the measure of the window
  have hvolA : (volume (Set.Icc (-T) T ∩ A)).toReal ≤
      (2 * T * Real.log (z : ℝ) / Real.pi + 1) *
        (2 * Real.sqrt (2 * Real.pi ^ 2 * δ ^ 2 / logSqWeight z)) := by
    have hAeq : Set.Icc (-T) T ∩ A = A ∩ Set.Icc (-T) T := inter_comm _ _
    have hbound := volume_largeValues_le hf1 hmul hbdd hσ hz2 hδ hW hT
    rw [hAeq]
    have hfin : ENNReal.ofReal ((2 * T * Real.log (z : ℝ) / Real.pi + 1) *
        (2 * Real.sqrt (2 * Real.pi ^ 2 * δ ^ 2 / logSqWeight z))) ≠ ⊤ :=
      ENNReal.ofReal_ne_top
    have hmono := ENNReal.toReal_mono hfin hbound
    refine le_trans hmono (le_of_eq ?_)
    refine ENNReal.toReal_ofReal ?_
    have h1 : (0 : ℝ) ≤ Real.log (z : ℝ) := Real.log_natCast_nonneg z
    have h2 : (0 : ℝ) ≤ Real.sqrt (2 * Real.pi ^ 2 * δ ^ 2 / logSqWeight z) :=
      Real.sqrt_nonneg _
    have h3 : (0 : ℝ) ≤ 2 * T * Real.log (z : ℝ) / Real.pi := by positivity
    positivity
  -- assemble
  rw [← hsplit]
  have hfinal : (volume (Set.Icc (-T) T ∩ A)).toReal * triv ≤
      triv * ((2 * T * Real.log (z : ℝ) / Real.pi + 1) *
        (2 * Real.sqrt (2 * Real.pi ^ 2 * δ ^ 2 / logSqWeight z))) := by
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left hvolA htriv0
  linarith [hwindow, hoff, hfinal]

end

end RHTower.Sieve
