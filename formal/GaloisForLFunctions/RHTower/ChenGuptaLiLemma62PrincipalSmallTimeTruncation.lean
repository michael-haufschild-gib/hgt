import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62PrincipalSmallTimeDeepWindow
import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62InitialMellin
import GaloisForLFunctions.RHTower.Sieve.InghamUniformDetectorMellinFullTwoTail

/-!
# Chen–Gupta–Li Lemma 6.2, principal character: exact identity and uniform critical truncation

* **Exact identity** (principal mirror of `cglLemma62_nonprincipal_smoothedCharacterSum_eq_reflected`):
  `2π · e^{it log N} · Σ_n w(n/N)² (n/N)^{it} = 2π · Res + ∫ ReflectedLine`, from the initial Mellin
  representation and the principal contour shift past the pole at `1 + it`.
* **Uniform critical truncation**: in every principal small-time regime with parameter `ε`,
  `‖∫_ℝ F(1/2+iv) dv − ∫_{|v| ≤ X^{ε/2}} F(1/2+iv) dv‖ ≤ C_ε X^{−200}` with `C_ε` depending only on
  the bump and `ε`.  Mechanism: `‖F(1/2+iv)‖ ≤ ‖H(1/2+iv)‖ N^{1/2} (M+1)` (corpus),
  `N^{1/2}(M+1) ≤ 2X^{1+2ε}` (`M ≤ X^{2ε}q/N`, `q ≤ X`), Mellin decay of order
  `n = ⌈(402+4ε)/ε⌉ + 2`, and the corpus power-tail truncation `norm_integral_sub_interval_le_powerTail`.
-/

set_option autoImplicit false

open Complex MeasureTheory Set

noncomputable section

namespace RHTower

/-- **Exact principal identity.**
`2π · phase · SmoothedSum = 2π · Res + ∫ ReflectedLine` for the principal character. -/
theorem cglLemma62_principal_smoothedCharacterSum_eq_residue_add_reflected
    (w : CGLRealSmoothBump) (N : CGLPositiveLength) (Q : CGLPositiveModulus) (t : ℝ) :
    (2 * Real.pi : ℝ) •
        (cglMellinPhase t N.value * cglLemma62SmoothedCharacterSum w N Q 1 t) =
      (2 * Real.pi : ℝ) • cglLemma62PrincipalResidueCoefficient w N Q t +
        ∫ v : ℝ, cglLemma62PrincipalReflectedLineIntegrand w N Q t v := by
  rw [cglLemma62_smoothedCharacterSum_initialMellin_lfunction]
  have hint : (∫ u : ℝ, cglInitialLFunctionIntegrand w N Q 1 t u) =
      ∫ u : ℝ, cglLemma62PrincipalContourIntegrand w N Q t ((2 : ℝ) + (u : ℂ) * I) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp [cglInitialLFunctionIntegrand, cglLemma62PrincipalContourIntegrand,
      cglInitialMellinLinePoint]
  have hres := cglLemma62_principal_initialVerticalIntegral'_eq_residue_add_reflected w N Q t
  simp only [VerticalIntegral', VerticalIntegral, smul_eq_mul] at hres
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have e1 : ∀ X : ℂ, 1 / (2 * (Real.pi : ℂ) * I) * (I * X) = X / (2 * Real.pi) := by
    intro X; field_simp
  rw [e1, e1] at hres
  rw [hint, Complex.real_smul]
  set A := ∫ u : ℝ, cglLemma62PrincipalContourIntegrand w N Q t ((2 : ℝ) + (u : ℂ) * I)
  have hA : A = 2 * Real.pi * (A / (2 * Real.pi)) := by field_simp
  rw [hA, hres]
  push_cast
  field_simp

namespace CGLLemma62PrincipalSmallTimeSourceRegime

variable {N : CGLPositiveLength} {Q : CGLPositiveModulus} {t : ℝ}

/-- `N^{1/2} (M + 1) ≤ 2 X^{1+2ε}`. -/
theorem sqrt_length_mul_cutoff_le (S : CGLLemma62PrincipalSmallTimeSourceRegime N Q t) :
    (N.value : ℝ) ^ (1 / 2 : ℝ) * ((S.tailCutoff.value : ℝ) + 1) ≤
      2 * S.base ^ (1 + 2 * S.epsilon) := by
  have hX := S.base_pos
  have hN1 : (1 : ℝ) ≤ N.value := by exact_mod_cast N.positive
  have hM1 : (1 : ℝ) ≤ S.tailCutoff.value := by exact_mod_cast S.tailCutoff.one_le
  have hscale0 : 0 ≤ S.cutoffScale := by unfold cutoffScale; positivity
  have hMle : (S.tailCutoff.value : ℝ) ≤ S.cutoffScale := Nat.floor_le hscale0
  have hsqrt : (N.value : ℝ) ^ (1 / 2 : ℝ) ≤ N.value := by
    calc (N.value : ℝ) ^ (1 / 2 : ℝ) ≤ (N.value : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
      _ = N.value := Real.rpow_one _
  have hq : (Q.value : ℝ) ≤ S.base := S.modulus_le_base
  have hNM : (N.value : ℝ) * S.tailCutoff.value ≤ S.base ^ (2 * S.epsilon) * Q.value := by
    have := mul_le_mul_of_nonneg_left hMle (by linarith : (0 : ℝ) ≤ N.value)
    unfold cutoffScale at this
    rwa [mul_div_cancel₀ _ (by linarith : (N.value : ℝ) ≠ 0)] at this
  have hsq0 : 0 ≤ (N.value : ℝ) ^ (1 / 2 : ℝ) := by positivity
  calc (N.value : ℝ) ^ (1 / 2 : ℝ) * ((S.tailCutoff.value : ℝ) + 1)
      ≤ (N.value : ℝ) ^ (1 / 2 : ℝ) * (2 * S.tailCutoff.value) :=
        mul_le_mul_of_nonneg_left (by linarith) hsq0
    _ ≤ (N.value : ℝ) * (2 * S.tailCutoff.value) :=
        mul_le_mul_of_nonneg_right hsqrt (by positivity)
    _ = 2 * ((N.value : ℝ) * S.tailCutoff.value) := by ring
    _ ≤ 2 * (S.base ^ (2 * S.epsilon) * Q.value) := by linarith
    _ ≤ 2 * (S.base ^ (2 * S.epsilon) * S.base) := by gcongr
    _ = 2 * S.base ^ (1 + 2 * S.epsilon) := by
        rw [Real.rpow_add hX, Real.rpow_one]; ring

theorem one_le_truncationRadius (S : CGLLemma62PrincipalSmallTimeSourceRegime N Q t) :
    1 ≤ S.truncationRadius :=
  Real.one_le_rpow S.base_one (by linarith [S.epsilon_pos])

end CGLLemma62PrincipalSmallTimeSourceRegime

/-- The Mellin decay order of the critical truncation: `n = ⌈(402+4ε)/ε⌉ + 2`. -/
def cglPrincipalCriticalTruncationOrder (ε : ℝ) : ℕ := Nat.ceil ((402 + 4 * ε) / ε) + 2

theorem cglPrincipalCriticalTruncationOrder_spec {ε : ℝ} (hε : 0 < ε) :
    2 ≤ cglPrincipalCriticalTruncationOrder ε ∧
      1 + 2 * ε + ε / 2 * (1 - (cglPrincipalCriticalTruncationOrder ε : ℝ)) ≤ -200 := by
  refine ⟨by unfold cglPrincipalCriticalTruncationOrder; omega, ?_⟩
  have h := Nat.le_ceil ((402 + 4 * ε) / ε)
  rw [div_le_iff₀ hε] at h
  unfold cglPrincipalCriticalTruncationOrder
  push_cast
  nlinarith

/-- **Uniform critical truncation.**  For every `ε > 0` there is `C ≥ 0` such that in every
principal small-time regime with parameter `ε`,
`‖∫_ℝ F(1/2+iv) dv − ∫_{|v| ≤ X^{ε/2}} F(1/2+iv) dv‖ ≤ C X^{−200}`. -/
theorem cglLemma62_principal_smallTime_finiteCritical_truncation_uniform (w : CGLRealSmoothBump)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : CGLPositiveLength) (Q : CGLPositiveModulus) (t : ℝ)
      (S : CGLLemma62PrincipalSmallTimeSourceRegime N Q t), S.epsilon = ε →
      ‖(∫ v : ℝ, cglLemma62PrincipalRegularizedFiniteContourIntegrand w N Q t S.tailCutoff.value
            ((1 / 2 : ℂ) + (v : ℂ) * I)) -
          ∫ v : ℝ in -S.truncationRadius..S.truncationRadius,
            cglLemma62PrincipalRegularizedFiniteContourIntegrand w N Q t S.tailCutoff.value
              ((1 / 2 : ℂ) + (v : ℂ) * I)‖ ≤
        C * S.base ^ (-200 : ℝ) := by
  set n := cglPrincipalCriticalTruncationOrder ε with hn
  obtain ⟨hn2, hexp⟩ := cglPrincipalCriticalTruncationOrder_spec hε
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  set B := cglLemma62MellinLineDecayBudget w (1 / 2) n with hB
  have hB0 : 0 ≤ B := by
    have := cglLemma62_mellinTransform_vertical_rapidDecay w (1 / 2) n 1
    simp only [abs_one, one_pow, one_mul] at this
    exact (norm_nonneg _).trans this
  refine ⟨2 * (2 * B) / ((n : ℝ) - 1), by positivity, ?_⟩
  intro N Q t S hS
  have hX := S.base_pos
  have hR1 := S.one_le_truncationRadius
  have hR0 : 0 < S.truncationRadius := by linarith
  have hcut := S.sqrt_length_mul_cutoff_le
  have hpt : ∀ v : ℝ, S.truncationRadius ≤ |v| →
      ‖cglLemma62PrincipalRegularizedFiniteContourIntegrand w N Q t S.tailCutoff.value
          ((1 / 2 : ℂ) + (v : ℂ) * I)‖ ≤
        (2 * B * S.base ^ (1 + 2 * S.epsilon)) * |v| ^ (-(n : ℝ)) := by
    intro v hv
    have hv1 : 1 ≤ |v| := hR1.trans hv
    have hv0 : 0 < |v| := by linarith
    have h := norm_cglLemma62PrincipalRegularizedFiniteContourIntegrand_critical_le w N Q t
      S.tailCutoff.value v
    have hH := cglLemma62_mellinTransform_vertical_rapidDecay w (1 / 2) n v
    have hH' : ‖cglLemma62MellinTransform w ((1 / 2 : ℂ) + (v : ℂ) * I)‖ ≤ B * |v| ^ (-(n : ℝ)) := by
      rw [Real.rpow_neg hv0.le, Real.rpow_natCast, ← div_eq_mul_inv,
        le_div_iff₀ (pow_pos hv0 n), mul_comm]
      rw [← hB] at hH
      simpa using hH
    have hrest0 : 0 ≤ (N.value : ℝ) ^ (1 / 2 : ℝ) * ((S.tailCutoff.value : ℝ) + 1) := by
      positivity
    calc _ ≤ ‖cglLemma62MellinTransform w ((1 / 2 : ℂ) + (v : ℂ) * I)‖ *
          ((N.value : ℝ) ^ (1 / 2 : ℝ) * ((S.tailCutoff.value : ℝ) + 1)) := by
          rw [← mul_assoc]; exact h
      _ ≤ (B * |v| ^ (-(n : ℝ))) * (2 * S.base ^ (1 + 2 * S.epsilon)) :=
          mul_le_mul hH' hcut hrest0 (by positivity)
      _ = _ := by ring
  have htail := Sieve.norm_integral_sub_interval_le_powerTail
    (cglLemma62PrincipalRegularizedFinite_critical_integrable w N Q t S.tailCutoff.value)
    (by positivity) hn1 hR0 hpt
  have hRpow : S.truncationRadius ^ (1 - (n : ℝ)) = S.base ^ (S.epsilon / 2 * (1 - (n : ℝ))) := by
    unfold CGLLemma62PrincipalSmallTimeSourceRegime.truncationRadius
    rw [← Real.rpow_mul hX.le]
  have hfinal : S.base ^ (1 + 2 * S.epsilon) * S.base ^ (S.epsilon / 2 * (1 - (n : ℝ))) ≤
      S.base ^ (-200 : ℝ) := by
    rw [← Real.rpow_add hX]
    exact Real.rpow_le_rpow_of_exponent_le S.base_one (by rw [hS]; linarith)
  have hC0 : 0 ≤ 2 * (2 * B) / ((n : ℝ) - 1) := by
    have : (0 : ℝ) < (n : ℝ) - 1 := by linarith
    positivity
  calc _ ≤ 2 * (2 * B * S.base ^ (1 + 2 * S.epsilon)) *
        (S.truncationRadius ^ (1 - (n : ℝ)) / ((n : ℝ) - 1)) := htail
    _ = 2 * (2 * B) / ((n : ℝ) - 1) *
          (S.base ^ (1 + 2 * S.epsilon) * S.base ^ (S.epsilon / 2 * (1 - (n : ℝ)))) := by
        rw [hRpow]; ring
    _ ≤ 2 * (2 * B) / ((n : ℝ) - 1) * S.base ^ (-200 : ℝ) :=
        mul_le_mul_of_nonneg_left hfinal hC0

end RHTower

end
