import GaloisForLFunctions.RHTower.Sieve.HalaszIntegralBound
import GaloisForLFunctions.RHTower.Sieve.HalaszGlobalLargeValueWindow

/-!
# The Halász integral bound with the window measure as a parameter

Splitting `∫_{-T}^{T}‖∑_n f(n)n^{-σ-it}‖dt` at the damped level uses nothing about the large-value set
beyond its measure:

`∫_{-T}^{T} ‖∑_n f(n)n^{-σ-it}‖ dt ≤ damped·2T + trivial·W`   whenever the large-value set has
measure at most `W` on `[-T, T]`.

`integral_norm_tsum_twistedSummand_le` is the instance at the cell-covering value
`W = (2T log z/π + 1)·2√(2π²δ²/logSqWeight z)`, of order `T·δ`.  The instance below takes `W = 2Δ`
for any `Δ` with `4δ² < charSepLower z Δ`, which for `T ≤ 1` removes the cell factor entirely: the
window term is then `≍ e^{4δ²}/log z` against the damped term `≍ (log z)e^{-δ²}·T`.
-/

noncomputable section
namespace RHTower.Sieve
open Complex MeasureTheory Set

section
variable {f : ℕ → ℂ}

/-- **The Halász split at the damped level.**  Only the measure of the large-value set enters. -/
theorem integral_norm_tsum_twistedSummand_le_of_volume
    (hf1 : f 1 = 1) (hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n)
    (hbdd : ∀ n, ‖f n‖ ≤ 1) {σ : ℝ} (hσ : 1 < σ) {z : ℕ}
    {δ : ℝ} {T : ℝ} (hT : 0 ≤ T) {W : ℝ} (hW0 : 0 ≤ W)
    (hvol : volume ({t : ℝ | (1 + 1 / (σ - 1)) *
              Real.exp (7 / 2 + 2 * (σ - 1) * (Real.log z + Real.log 4) - δ ^ 2) <
            ‖∑' n : ℕ, twistedSummand f (((σ : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I) n‖}
          ∩ Set.Icc (-T) T)
        ≤ ENNReal.ofReal W) :
    (∫ t in Set.Icc (-T) T,
        ‖∑' n : ℕ, twistedSummand f (((σ : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I) n‖)
      ≤ (1 + 1 / (σ - 1)) *
            Real.exp (7 / 2 + 2 * (σ - 1) * (Real.log z + Real.log 4) - δ ^ 2) * (2 * T)
          + (1 + 1 / (σ - 1)) * Real.exp (7 / 2) * W := by
  classical
  set G : ℝ → ℝ := fun t =>
    ‖∑' n : ℕ, twistedSummand f (((σ : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I) n‖ with hG
  set damped : ℝ := (1 + 1 / (σ - 1)) *
    Real.exp (7 / 2 + 2 * (σ - 1) * (Real.log z + Real.log 4) - δ ^ 2) with hdamped
  set triv : ℝ := (1 + 1 / (σ - 1)) * Real.exp (7 / 2) with htriv
  have hcont : Continuous G := (continuous_tsum_twistedSummand hbdd hσ).norm
  have hGint : IntegrableOn G (Set.Icc (-T) T) := hcont.integrableOn_Icc
  set A : Set ℝ := {t : ℝ | damped < G t} with hA
  have hAmeas : MeasurableSet A := (isOpen_lt continuous_const hcont).measurableSet
  have hdamped0 : 0 ≤ damped := by
    rw [hdamped]
    have h1 : 0 < σ - 1 := by linarith
    positivity
  have htriv0 : 0 ≤ triv := by
    rw [htriv]
    have h1 : 0 < σ - 1 := by linarith
    positivity
  have hsplit : (∫ t in Set.Icc (-T) T ∩ A, G t) + ∫ t in Set.Icc (-T) T \ A, G t
      = ∫ t in Set.Icc (-T) T, G t :=
    integral_inter_add_sdiff hAmeas hGint
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
      integrableOn_const hfin
    refine le_trans (setIntegral_mono_on (hGint.mono_set inter_subset_left) hint2 hmeas hbound) ?_
    rw [setIntegral_const, measureReal_def, smul_eq_mul]
  have hoff : (∫ t in Set.Icc (-T) T \ A, G t) ≤ damped * (2 * T) := by
    have hbound : ∀ t ∈ Set.Icc (-T) T \ A, G t ≤ damped := by
      intro t ht
      have hnot : ¬ (damped < G t) := fun hlt => ht.2 hlt
      exact not_lt.mp hnot
    have hmeas : MeasurableSet (Set.Icc (-T) T \ A) := measurableSet_Icc.diff hAmeas
    have hfin : volume (Set.Icc (-T) T \ A) ≠ ⊤ :=
      ne_top_of_le_ne_top (by simp [Real.volume_Icc]) (measure_mono sdiff_subset)
    have hint2 : IntegrableOn (fun _ : ℝ => damped) (Set.Icc (-T) T \ A) :=
      integrableOn_const hfin
    refine le_trans (setIntegral_mono_on (hGint.mono_set sdiff_subset) hint2 hmeas hbound) ?_
    rw [setIntegral_const, measureReal_def, smul_eq_mul]
    have hvolle : (volume (Set.Icc (-T) T \ A)).toReal ≤ 2 * T := by
      have hIcc : (volume (Set.Icc (-T) T)).toReal = 2 * T := by
        rw [Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
        ring
      have hfin2 : volume (Set.Icc (-T) T) ≠ ⊤ := by simp [Real.volume_Icc]
      have h := ENNReal.toReal_mono hfin2 (measure_mono (sdiff_subset (s := Set.Icc (-T) T) (t := A)))
      rwa [hIcc] at h
    exact le_trans (mul_le_mul_of_nonneg_right hvolle hdamped0) (le_of_eq (mul_comm _ _))
  have hvolA : (volume (Set.Icc (-T) T ∩ A)).toReal ≤ W := by
    have hAeq : Set.Icc (-T) T ∩ A = A ∩ Set.Icc (-T) T := inter_comm _ _
    rw [hAeq]
    have hmono := ENNReal.toReal_mono ENNReal.ofReal_ne_top hvol
    rwa [ENNReal.toReal_ofReal hW0] at hmono
  have hfinal : (volume (Set.Icc (-T) T ∩ A)).toReal * triv ≤ triv * W := by
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left hvolA htriv0
  rw [← hsplit]
  linarith [hwindow, hoff, hfinal]

/-- **The Halász integral bound with no cell covering.**  On a range of length at most `1` the
large-value set is a single window of width `Δ`, for every `Δ` with `4δ² < charSepLower z Δ`. -/
theorem integral_norm_tsum_twistedSummand_le_window
    (hf1 : f 1 = 1) (hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n)
    (hbdd : ∀ n, ‖f n‖ ≤ 1) {σ : ℝ} (hσ : 1 < σ) {z : ℕ} (hz : 3 ≤ z)
    {δ Δ : ℝ} (hδ : 0 ≤ δ) (hΔ0 : 0 < Δ) (hgap : 4 * δ ^ 2 < charSepLower z Δ)
    {T : ℝ} (hT : 0 ≤ T) (hT1 : T ≤ 1) :
    (∫ t in Set.Icc (-T) T,
        ‖∑' n : ℕ, twistedSummand f (((σ : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I) n‖)
      ≤ (1 + 1 / (σ - 1)) *
            Real.exp (7 / 2 + 2 * (σ - 1) * (Real.log z + Real.log 4) - δ ^ 2) * (2 * T)
          + (1 + 1 / (σ - 1)) * Real.exp (7 / 2) * (2 * Δ) :=
  integral_norm_tsum_twistedSummand_le_of_volume hf1 hmul hbdd hσ hT (by linarith)
    (volume_halaszLargeValues_le_window hf1 hmul hbdd hσ hz hδ hΔ0 hgap hT1)

end

end RHTower.Sieve
end
