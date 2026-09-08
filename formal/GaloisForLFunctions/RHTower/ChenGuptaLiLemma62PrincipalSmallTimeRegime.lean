import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62PrincipalReflectedReassembly

/-!
# Chen--Gupta--Li Lemma 6.2: principal small-time source regime

The literal small-time regime of CGL Lemma 6.2 for the principal character:
base `X ≥ max(1, q)`, ordinate `|t| ≤ X^ε`, cutoff `M = ⌊X^{2ε} q / N⌋`, deep
depth chosen so that the deep line saves `X^{-200}`, and the symmetric
truncation radius `X^{ε/2}`.  Both truncated windows of the reflected line
lose only a closed `X^{-200}` error.
-/

open Complex MeasureTheory Filter Set
open scoped Topology

namespace RHTower

noncomputable section

/-- CGL's small-time source regime for the principal character. -/
structure CGLLemma62PrincipalSmallTimeSourceRegime
    (N : CGLPositiveLength) (Q : CGLPositiveModulus) (t : ℝ) where
  base : ℝ
  base_one : 1 ≤ base
  modulus_le_base : (Q.value : ℝ) ≤ base
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  ordinate_small : |t| ≤ base ^ epsilon
  cutoff_scale_two : 2 ≤ base ^ (2 * epsilon) * (Q.value : ℝ) / N.value

namespace CGLLemma62PrincipalSmallTimeSourceRegime

variable {N : CGLPositiveLength} {Q : CGLPositiveModulus} {t : ℝ}

/-- The literal cutoff scale `X^(2ε) q / N`. -/
def cutoffScale (S : CGLLemma62PrincipalSmallTimeSourceRegime N Q t) : ℝ :=
  S.base ^ (2 * S.epsilon) * (Q.value : ℝ) / N.value

/-- The exact integer split point for the tail. -/
def tailCutoff (S : CGLLemma62PrincipalSmallTimeSourceRegime N Q t) : CGLLemma62TailCutoff where
  value := Nat.floor S.cutoffScale
  one_le := by
    apply (Nat.one_le_floor_iff S.cutoffScale).mpr
    have htwo : 2 ≤ S.cutoffScale := by
      simpa [cutoffScale] using S.cutoff_scale_two
    linarith

/-- Rounding the cutoff down loses at most a factor two. -/
theorem half_cutoffScale_le_tailCutoff (S : CGLLemma62PrincipalSmallTimeSourceRegime N Q t) :
    S.cutoffScale / 2 ≤ (S.tailCutoff.value : ℝ) := by
  have hlt : S.cutoffScale < (Nat.floor S.cutoffScale : ℝ) + 1 :=
    Nat.lt_floor_add_one S.cutoffScale
  have htwo : 2 ≤ S.cutoffScale := by
    simpa [cutoffScale] using S.cutoff_scale_two
  change S.cutoffScale / 2 ≤ (Nat.floor S.cutoffScale : ℝ)
  nlinarith

/-- The literal truncation radius `X^(ε/2)`. -/
def truncationRadius (S : CGLLemma62PrincipalSmallTimeSourceRegime N Q t) : ℝ :=
  S.base ^ (S.epsilon / 2)

/-- The least natural depth sufficient for the `X⁻²⁰⁰` deep-line target. -/
def decayDepth (S : CGLLemma62PrincipalSmallTimeSourceRegime N Q t) :
    CGLLemma62TailContourDepth where
  value := Nat.ceil ((202 + S.epsilon) / (2 * S.epsilon))
  positive := by
    apply Nat.ceil_pos.mpr
    exact div_pos (by linarith [S.epsilon_pos]) (by linarith [S.epsilon_pos])

/-- The certified depth forces its exact source exponent below `-200`. -/
theorem decayDepth_source_exponent_le (S : CGLLemma62PrincipalSmallTimeSourceRegime N Q t) :
    2 + S.epsilon - 2 * S.epsilon * (S.decayDepth.value : ℝ) ≤ -200 := by
  have hden : 0 < 2 * S.epsilon := by linarith [S.epsilon_pos]
  have hceil : (202 + S.epsilon) / (2 * S.epsilon) ≤ (S.decayDepth.value : ℝ) := Nat.le_ceil _
  have hmul := (div_le_iff₀ hden).mp hceil
  nlinarith [hmul]

/-- A Mellin-decay rate making the ordinate tails save `X⁻²⁰⁰` at radius `X^(ε/2)`. -/
def tailTruncationRate (S : CGLLemma62PrincipalSmallTimeSourceRegime N Q t) : ℕ :=
  Nat.ceil (2 + 400 / S.epsilon)

theorem tailTruncationRate_two (S : CGLLemma62PrincipalSmallTimeSourceRegime N Q t) :
    2 ≤ S.tailTruncationRate := by
  have hceil : 2 + 400 / S.epsilon ≤ (S.tailTruncationRate : ℝ) := Nat.le_ceil _
  have heps : 0 < S.epsilon := S.epsilon_pos
  have hnonneg : 0 ≤ 400 / S.epsilon := div_nonneg (by norm_num) heps.le
  have hrate : (2 : ℝ) ≤ (S.tailTruncationRate : ℝ) := by linarith
  exact_mod_cast hrate

theorem tailTruncation_exponent_le (S : CGLLemma62PrincipalSmallTimeSourceRegime N Q t) :
    (S.epsilon / 2) * (1 - (S.tailTruncationRate : ℝ)) ≤ -200 := by
  have hceil : 2 + 400 / S.epsilon ≤ (S.tailTruncationRate : ℝ) := Nat.le_ceil _
  have heps : 0 < S.epsilon := S.epsilon_pos
  have hmul := mul_le_mul_of_nonneg_left hceil heps.le
  have hdiv : S.epsilon * (400 / S.epsilon) = 400 := by
    field_simp
  rw [mul_add, hdiv] at hmul
  nlinarith

theorem tailTruncation_power_le (S : CGLLemma62PrincipalSmallTimeSourceRegime N Q t) :
    S.truncationRadius ^ (1 - (S.tailTruncationRate : ℝ)) ≤ S.base ^ (-200 : ℝ) := by
  have hbase : 0 ≤ S.base := le_trans zero_le_one S.base_one
  have hexponent := S.tailTruncation_exponent_le
  unfold truncationRadius
  rw [← Real.rpow_mul hbase]
  exact Real.rpow_le_rpow_of_exponent_le S.base_one hexponent

/-- The literal radius with a closed rate saving `X⁻²⁰⁰`. -/
def tailTruncation (S : CGLLemma62PrincipalSmallTimeSourceRegime N Q t) :
    CGLLemma62TailTruncationCertificate where
  radius := S.truncationRadius
  radius_one := by
    unfold truncationRadius
    apply Real.one_le_rpow S.base_one
    linarith [S.epsilon_pos]
  decayRate := S.tailTruncationRate
  decayRate_two := S.tailTruncationRate_two

end CGLLemma62PrincipalSmallTimeSourceRegime

/-- The deep-line ordinate tails omitted from the principal small-time window
have a closed `X⁻²⁰⁰` bound. -/
theorem cglLemma62_principal_smallTime_farTail_truncation_error_X200_bound
    {N : CGLPositiveLength} {Q : CGLPositiveModulus} {t : ℝ}
    (S : CGLLemma62PrincipalSmallTimeSourceRegime N Q t) (w : CGLRealSmoothBump) :
    ∃ C : ℝ, 0 ≤ C ∧
      ‖(∫ v : ℝ, cglLemma62PrincipalFarTailIntegrand w N Q t S.tailCutoff.value S.decayDepth v) -
          ∫ v : ℝ in -S.truncationRadius..S.truncationRadius,
            cglLemma62PrincipalFarTailIntegrand w N Q t S.tailCutoff.value S.decayDepth v‖ ≤
        C * S.base ^ (-200 : ℝ) := by
  obtain ⟨C, hC, htail⟩ := cglLemma62_principalFarTail_integral_sub_truncation_le_power
    w N Q t S.tailCutoff S.decayDepth S.tailTruncation
  have hrate : (1 : ℝ) < S.tailTruncationRate := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) S.tailTruncationRate_two)
  have hden : 0 < (S.tailTruncationRate : ℝ) - 1 := by linarith
  have hscalar : 0 ≤ 2 * C / ((S.tailTruncationRate : ℝ) - 1) :=
    div_nonneg (mul_nonneg (by norm_num) hC) hden.le
  have hpower := S.tailTruncation_power_le
  refine ⟨2 * C / ((S.tailTruncationRate : ℝ) - 1), hscalar, ?_⟩
  calc
    _ ≤ 2 * C * (S.truncationRadius ^ (1 - (S.tailTruncationRate : ℝ)) /
          ((S.tailTruncationRate : ℝ) - 1)) := htail
    _ = (2 * C / ((S.tailTruncationRate : ℝ) - 1)) *
        S.truncationRadius ^ (1 - (S.tailTruncationRate : ℝ)) := by ring
    _ ≤ (2 * C / ((S.tailTruncationRate : ℝ) - 1)) * S.base ^ (-200 : ℝ) :=
      mul_le_mul_of_nonneg_left hpower hscalar
    _ = _ := by ring

/-- The critical-line ordinate tails omitted from the principal small-time
finite window have a closed `X⁻²⁰⁰` bound. -/
theorem cglLemma62_principal_smallTime_finiteCritical_truncation_error_X200_bound
    {N : CGLPositiveLength} {Q : CGLPositiveModulus} {t : ℝ}
    (S : CGLLemma62PrincipalSmallTimeSourceRegime N Q t) (w : CGLRealSmoothBump) (M : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ‖(∫ v : ℝ, cglLemma62PrincipalRegularizedFiniteContourIntegrand w N Q t M
          ((1 / 2 : ℂ) + (v : ℂ) * I)) -
          ∫ v : ℝ in -S.truncationRadius..S.truncationRadius,
            cglLemma62PrincipalRegularizedFiniteContourIntegrand w N Q t M
              ((1 / 2 : ℂ) + (v : ℂ) * I)‖ ≤
        C * S.base ^ (-200 : ℝ) := by
  obtain ⟨C, hC, htail⟩ := cglLemma62_principal_finiteCritical_integral_sub_truncation_le_power
    w N Q t M S.tailTruncation
  have hrate : (1 : ℝ) < S.tailTruncationRate := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) S.tailTruncationRate_two)
  have hden : 0 < (S.tailTruncationRate : ℝ) - 1 := by linarith
  have hscalar : 0 ≤ 2 * C / ((S.tailTruncationRate : ℝ) - 1) :=
    div_nonneg (mul_nonneg (by norm_num) hC) hden.le
  have hpower := S.tailTruncation_power_le
  refine ⟨2 * C / ((S.tailTruncationRate : ℝ) - 1), hscalar, ?_⟩
  calc
    _ ≤ 2 * C * (S.truncationRadius ^ (1 - (S.tailTruncationRate : ℝ)) /
          ((S.tailTruncationRate : ℝ) - 1)) := htail
    _ = (2 * C / ((S.tailTruncationRate : ℝ) - 1)) *
        S.truncationRadius ^ (1 - (S.tailTruncationRate : ℝ)) := by ring
    _ ≤ (2 * C / ((S.tailTruncationRate : ℝ) - 1)) * S.base ^ (-200 : ℝ) :=
      mul_le_mul_of_nonneg_left hpower hscalar
    _ = _ := by ring

/-- At the principal small-time window, the complete reflected ζ-line differs
from its critical finite and deep-line tail windows by a closed `X⁻²⁰⁰` error. -/
theorem cglLemma62_principal_smallTime_reflected_truncation_error_X200_bound
    {N : CGLPositiveLength} {Q : CGLPositiveModulus} {t : ℝ}
    (S : CGLLemma62PrincipalSmallTimeSourceRegime N Q t) (w : CGLRealSmoothBump) :
    ∃ C : ℝ, 0 ≤ C ∧
      ‖(∫ v : ℝ, cglLemma62PrincipalReflectedLineIntegrand w N Q t v) -
          ((∫ v : ℝ in -S.truncationRadius..S.truncationRadius,
              cglLemma62PrincipalRegularizedFiniteContourIntegrand w N Q t S.tailCutoff.value
                ((1 / 2 : ℂ) + (v : ℂ) * I)) +
            ∫ v : ℝ in -S.truncationRadius..S.truncationRadius,
              cglLemma62PrincipalFarTailIntegrand w N Q t S.tailCutoff.value S.decayDepth v)‖ ≤
        C * S.base ^ (-200 : ℝ) := by
  obtain ⟨CF, hCF, hfinite⟩ :=
    cglLemma62_principal_smallTime_finiteCritical_truncation_error_X200_bound S w
      S.tailCutoff.value
  obtain ⟨CT, hCT, htail⟩ :=
    cglLemma62_principal_smallTime_farTail_truncation_error_X200_bound S w
  refine ⟨CF + CT, add_nonneg hCF hCT, ?_⟩
  rw [cglLemma62_principal_reflected_integral_eq_finiteCritical_add_farTail
    w N Q t S.tailCutoff S.decayDepth]
  set A := ∫ v : ℝ, cglLemma62PrincipalRegularizedFiniteContourIntegrand w N Q t
    S.tailCutoff.value ((1 / 2 : ℂ) + (v : ℂ) * I) with hA
  set A' := ∫ v : ℝ in -S.truncationRadius..S.truncationRadius,
    cglLemma62PrincipalRegularizedFiniteContourIntegrand w N Q t S.tailCutoff.value
      ((1 / 2 : ℂ) + (v : ℂ) * I) with hA'
  set B := ∫ v : ℝ, cglLemma62PrincipalFarTailIntegrand w N Q t S.tailCutoff.value
    S.decayDepth v with hB
  set B' := ∫ v : ℝ in -S.truncationRadius..S.truncationRadius,
    cglLemma62PrincipalFarTailIntegrand w N Q t S.tailCutoff.value S.decayDepth v with hB'
  calc
    ‖A + B - (A' + B')‖ = ‖(A - A') + (B - B')‖ := by congr 1; ring
    _ ≤ ‖A - A'‖ + ‖B - B'‖ := norm_add_le _ _
    _ ≤ CF * S.base ^ (-200 : ℝ) + CT * S.base ^ (-200 : ℝ) := add_le_add hfinite htail
    _ = (CF + CT) * S.base ^ (-200 : ℝ) := by ring

end

end RHTower
