import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicCofactorError
import GaloisForLFunctions.RHTower.Sieve.LogPolyWindowHMRecip

/-!
# Reciprocal Halasz--Montgomery bound for Menon's harmonic cofactor

The harmonic cofactor is bounded by the reciprocal of its index only on its displayed support.
The support-local Halasz--Montgomery receiver below preserves that reciprocal-square gain.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- Restricted coefficient energy, requiring a coefficient bound only on the actual support. -/
theorem sum_normSq_finCoeff_le_on {D : Finset ℕ} {N : ℕ} {a : ℕ → ℂ} {Ω : ℝ}
    (hΩ : 0 ≤ Ω) (ha : ∀ n ∈ D, ‖a n‖ ≤ Ω) :
    (∑ n : Fin N, ‖finCoeff D a N n‖ ^ 2) ≤ Ω ^ 2 * (D.card : ℝ) := by
  classical
  have hterm : ∀ n : Fin N, ‖finCoeff D a N n‖ ^ 2
      ≤ Ω ^ 2 * (if ((n : ℕ) + 1) ∈ D then (1 : ℝ) else 0) := by
    intro n
    rw [finCoeff, restrictCoeff]
    by_cases h : ((n : ℕ) + 1) ∈ D
    · rw [if_pos h, if_pos h, mul_one]
      have hn := ha ((n : ℕ) + 1) h
      nlinarith [norm_nonneg (a ((n : ℕ) + 1)), hΩ]
    · rw [if_neg h, if_neg h]
      simp
  refine (Finset.sum_le_sum fun n _ => hterm n).trans ?_
  rw [← Finset.mul_sum, Finset.sum_boole]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hcard : ((Finset.univ.filter (fun n : Fin N => ((n : ℕ) + 1) ∈ D)).card : ℕ)
      ≤ D.card := by
    refine Finset.card_le_card_of_injOn (fun n : Fin N => (n : ℕ) + 1) ?_ ?_
    · intro n hn
      exact (Finset.mem_filter.1 hn).2
    · intro x _ y _ hxy
      apply Fin.ext
      exact Nat.add_right_cancel hxy
  exact_mod_cast hcard

/-- Reciprocal-kernel HM with the coefficient bound required only on the displayed support. -/
theorem setIntegral_normSq_logPoly_le_HM_window_recip_on (a : ℕ → ℂ)
    {D : Finset ℕ} {N : ℕ} (hN : 1 ≤ N) (hD : D ⊆ Finset.Icc 1 N)
    {E : Set ℝ} (hE : MeasurableSet E) {W : ℝ} (hW : 1 ≤ W)
    (hEs : E ⊆ Set.Icc (-W) W) {Ω : ℝ} (hΩ : 0 ≤ Ω)
    (ha : ∀ n ∈ D, ‖a n‖ ≤ Ω) :
    (∫ w in E, ‖logPoly a D w‖ ^ 2)
      ≤ (2 * Real.pi)⁻¹
        * (hmMassRecip N (2 * Real.pi * W) (2 * Real.pi * volume.real E)
            * (Ω ^ 2 * (D.card : ℝ))) := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hinv : (0 : ℝ) < (2 * Real.pi)⁻¹ := by positivity
  have hne : (2 * Real.pi) ≠ 0 := ne_of_gt hpi
  have hT : (1 : ℝ) ≤ 2 * Real.pi * W := by
    have h3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
    nlinarith [hW, h3]
  set S : Set ℝ := (fun v : ℝ => (2 * Real.pi)⁻¹ * v) ⁻¹' E with hSdef
  have hSm : MeasurableSet S := (measurable_const_mul _) hE
  have hpre : (fun v : ℝ => 2 * Real.pi * v) ⁻¹' S = E := by
    ext w
    simp only [hSdef, Set.mem_preimage]
    rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  have hSs : S ⊆ Set.Icc (-(2 * Real.pi * W)) (2 * Real.pi * W) := by
    intro v hv
    have hmem : (2 * Real.pi)⁻¹ * v ∈ Set.Icc (-W) W := hEs hv
    rw [Set.mem_Icc] at hmem ⊢
    constructor
    · have := mul_le_mul_of_nonneg_left hmem.1 hpi.le
      rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul] at this
      linarith
    · have := mul_le_mul_of_nonneg_left hmem.2 hpi.le
      rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul] at this
      linarith
  have hvol : volume.real S = 2 * Real.pi * volume.real E := by
    rw [hSdef, volume_real_preimage_mul_left hinv, inv_inv]
  have hmass0 : 0 ≤ hmMassRecip N (2 * Real.pi * W) (volume.real S) := by
    have hvol0 : 0 ≤ volume.real S := ENNReal.toReal_nonneg
    have hfar0 : 0 ≤ plainKernelFarConst N (2 * Real.pi * W) :=
      plainKernelFarConst_nonneg N hT
    have hlog0 : 0 ≤ Real.log (2 + 2 * (2 * Real.pi * W)) :=
      Real.log_nonneg (by linarith)
    rw [hmMassRecip]
    positivity
  calc
    (∫ w in E, ‖logPoly a D w‖ ^ 2)
        = (∫ w in (fun v : ℝ => 2 * Real.pi * v) ⁻¹' S,
            ‖logPoly a D w‖ ^ 2) := by rw [hpre]
    _ = (2 * Real.pi)⁻¹ * ∫ t in S, ‖dirPoly N (finCoeff D a N) t‖ ^ 2 :=
      setIntegral_normSq_logPoly_eq a hD hSm
    _ ≤ (2 * Real.pi)⁻¹ *
          (hmMassRecip N (2 * Real.pi * W) (volume.real S) *
            ∑ n : Fin N, ‖finCoeff D a N n‖ ^ 2) := by
      refine mul_le_mul_of_nonneg_left ?_ hinv.le
      exact setIntegral_normSq_dirPoly_le_recip hN (finCoeff D a N) hT hSm hSs
    _ ≤ (2 * Real.pi)⁻¹ *
          (hmMassRecip N (2 * Real.pi * W) (volume.real S) *
            (Ω ^ 2 * (D.card : ℝ))) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (sum_normSq_finCoeff_le_on hΩ ha) hmass0) hinv.le
    _ = (2 * Real.pi)⁻¹
        * (hmMassRecip N (2 * Real.pi * W) (2 * Real.pi * volume.real E)
            * (Ω ^ 2 * (D.card : ℝ))) := by rw [hvol]

/-- Menon's harmonic cofactor HM bound with its reciprocal lower-support gain. -/
theorem setIntegral_normSq_harmonicRamareCofactor_le_HM_recip
    (P D : Finset ℕ) {L N : ℕ} (hL : 1 ≤ L) (hN : 1 ≤ N)
    (hD : D ⊆ Finset.Icc L N) {E : Set ℝ} (hE : MeasurableSet E)
    {W : ℝ} (hW : 1 ≤ W) (hEs : E ⊆ Set.Icc (-W) W) :
    (∫ w in E, ‖logPoly (harmonicRamareCofactorCoeff P) D w‖ ^ 2)
      ≤ (2 * Real.pi)⁻¹
        * (hmMassRecip N (2 * Real.pi * W) (2 * Real.pi * volume.real E)
            * ((1 / (L : ℝ)) ^ 2 * (D.card : ℝ))) := by
  have hDI : D ⊆ Finset.Icc 1 N := by
    intro n hn
    have hn' := Finset.mem_Icc.1 (hD hn)
    exact Finset.mem_Icc.2 ⟨le_trans hL hn'.1, hn'.2⟩
  refine setIntegral_normSq_logPoly_le_HM_window_recip_on
    (harmonicRamareCofactorCoeff P) hN hDI hE hW hEs (by positivity) ?_
  intro n hn
  have hn' := Finset.mem_Icc.1 (hD hn)
  have hLR : (0 : ℝ) < (L : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hL
  have hLn : (L : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn'.1
  exact (norm_harmonicRamareCofactorCoeff_le_inv P n).trans
    (one_div_le_one_div_of_le hLR hLn)

end

end RHTower.Sieve
