import GaloisForLFunctions.RHTower.BourgainFejerMomentTransfer
import GaloisForLFunctions.RHTower.BourgainFinTonelli
import GaloisForLFunctions.RHTower.BourgainScaledParabolaDecoupling

open MeasureTheory

namespace RHTower

noncomputable section

def bourgainA6PhasePoint
    (H : ℕ) (z : BourgainPhaseSpace) : BourgainPhaseSpace :=
  ![z 0, z 1, z 2 / Real.sqrt H, z 3 / Real.sqrt H]

theorem bourgainShortCurveSum_eq_A6ExponentialSum
    {H : ℕ} (hH : 0 < H) (z : BourgainPhaseSpace) :
    bourgainShortCurveSum H (fun _ => 1) z =
      bourgainA6ExponentialSum H
        (z 0) (z 1) (z 2 / Real.sqrt H) (z 3 / Real.sqrt H) := by
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  have hsqrt : Real.sqrt (H : ℝ) ≠ 0 := (Real.sqrt_pos.2 hHr).ne'
  have hphase (n : Fin H) :
      bourgainDot z
          (bourgainMomentCurve (bourgainIndex n)) =
        (bourgainIndex n : ℝ) * z 0 +
          (bourgainIndex n : ℝ) ^ (2 : ℕ) * z 1 +
          bourgainA6HigherPhase H
            (z 2 / Real.sqrt H) (z 3 / Real.sqrt H) n := by
    unfold bourgainDot bourgainMomentCurve bourgainA6HigherPhase
    rw [Fin.sum_univ_four]
    have hc0 :
        ![(bourgainIndex n : ℝ),
            (bourgainIndex n : ℝ) ^ (2 : ℕ),
            (bourgainIndex n : ℝ) ^ (3 / 2 : ℝ),
            (bourgainIndex n : ℝ) ^ (1 / 2 : ℝ)] (0 : Fin 4) =
          (bourgainIndex n : ℝ) := rfl
    have hc1 :
        ![(bourgainIndex n : ℝ),
            (bourgainIndex n : ℝ) ^ (2 : ℕ),
            (bourgainIndex n : ℝ) ^ (3 / 2 : ℝ),
            (bourgainIndex n : ℝ) ^ (1 / 2 : ℝ)] (1 : Fin 4) =
          (bourgainIndex n : ℝ) ^ (2 : ℕ) := rfl
    have hc2 :
        ![(bourgainIndex n : ℝ),
            (bourgainIndex n : ℝ) ^ (2 : ℕ),
            (bourgainIndex n : ℝ) ^ (3 / 2 : ℝ),
            (bourgainIndex n : ℝ) ^ (1 / 2 : ℝ)] (2 : Fin 4) =
          (bourgainIndex n : ℝ) ^ (3 / 2 : ℝ) := rfl
    have hc3 :
        ![(bourgainIndex n : ℝ),
            (bourgainIndex n : ℝ) ^ (2 : ℕ),
            (bourgainIndex n : ℝ) ^ (3 / 2 : ℝ),
            (bourgainIndex n : ℝ) ^ (1 / 2 : ℝ)] (3 : Fin 4) =
          (bourgainIndex n : ℝ) ^ (1 / 2 : ℝ) := rfl
    rw [hc0, hc1, hc2, hc3]
    simp only [← Real.sqrt_eq_rpow]
    field_simp
    ring
  unfold bourgainShortCurveSum bourgainA6ExponentialSum
    bourgainAdditiveCharacter
  apply Fintype.sum_congr
  intro n
  rw [one_mul, hphase]

theorem norm_sq_bourgainSixfoldCharacterCloud_eq_A6_pow_twelve
    {H : ℕ} (hH : 0 < H) (z : BourgainPhaseSpace) :
    ‖bourgainSixfoldCharacterCloud H z‖ ^ (2 : ℕ) =
      ‖bourgainA6ExponentialSum H
        (z 0) (z 1) (z 2 / Real.sqrt H) (z 3 / Real.sqrt H)‖ ^
          (12 : ℕ) := by
  unfold bourgainSixfoldCharacterCloud
  rw [bourgainSixfoldFourierSum_eq_pow_six]
  rw [norm_pow, ← pow_mul]
  rw [bourgainShortCurveSum_eq_A6ExponentialSum hH]

theorem periodic_bourgainA6ExponentialSum_first
    (H : ℕ) (x₂ x₃ x₄ : ℝ) :
    Function.Periodic
      (fun x₁ => bourgainA6ExponentialSum H x₁ x₂ x₃ x₄) 1 := by
  intro x₁
  change
    bourgainA6ExponentialSum H (x₁ + 1) x₂ x₃ x₄ =
      bourgainA6ExponentialSum H x₁ x₂ x₃ x₄
  rw [← bourgainA6TwoTorusSum_unitCharacter_eq,
    ← bourgainA6TwoTorusSum_unitCharacter_eq,
    bourgainUnitCharacter_add_one]

theorem periodic_bourgainA6ExponentialSum_second
    (H : ℕ) (x₁ x₃ x₄ : ℝ) :
    Function.Periodic
      (fun x₂ => bourgainA6ExponentialSum H x₁ x₂ x₃ x₄) 1 := by
  intro x₂
  change
    bourgainA6ExponentialSum H x₁ (x₂ + 1) x₃ x₄ =
      bourgainA6ExponentialSum H x₁ x₂ x₃ x₄
  rw [← bourgainA6TwoTorusSum_unitCharacter_eq,
    ← bourgainA6TwoTorusSum_unitCharacter_eq,
    bourgainUnitCharacter_add_one]

theorem periodic_norm_bourgainA6ExponentialSum_pow_twelve_first
    (H : ℕ) (x₂ x₃ x₄ : ℝ) :
    Function.Periodic
      (fun x₁ =>
        ‖bourgainA6ExponentialSum H x₁ x₂ x₃ x₄‖ ^ (12 : ℕ)) 1 := by
  intro x₁
  change
    ‖bourgainA6ExponentialSum H (x₁ + 1) x₂ x₃ x₄‖ ^ (12 : ℕ) =
      ‖bourgainA6ExponentialSum H x₁ x₂ x₃ x₄‖ ^ (12 : ℕ)
  have hp :=
    periodic_bourgainA6ExponentialSum_first H x₂ x₃ x₄ x₁
  change
    bourgainA6ExponentialSum H (x₁ + 1) x₂ x₃ x₄ =
      bourgainA6ExponentialSum H x₁ x₂ x₃ x₄ at hp
  rw [hp]

theorem periodic_norm_bourgainA6ExponentialSum_pow_twelve_second
    (H : ℕ) (x₁ x₃ x₄ : ℝ) :
    Function.Periodic
      (fun x₂ =>
        ‖bourgainA6ExponentialSum H x₁ x₂ x₃ x₄‖ ^ (12 : ℕ)) 1 := by
  intro x₂
  change
    ‖bourgainA6ExponentialSum H x₁ (x₂ + 1) x₃ x₄‖ ^ (12 : ℕ) =
      ‖bourgainA6ExponentialSum H x₁ x₂ x₃ x₄‖ ^ (12 : ℕ)
  have hp :=
    periodic_bourgainA6ExponentialSum_second H x₁ x₃ x₄ x₂
  change
    bourgainA6ExponentialSum H x₁ (x₂ + 1) x₃ x₄ =
      bourgainA6ExponentialSum H x₁ x₂ x₃ x₄ at hp
  rw [hp]

theorem setLIntegral_bourgainFullBox_eq_iterated
    (X : BourgainPhaseSpace)
    (f : BourgainPhaseSpace → ENNReal) (hf : Measurable f) :
    (∫⁻ z in bourgainFullBox X, f z) =
      ∫⁻ z₀ in Set.Ioc (-X 0) (X 0),
        ∫⁻ z₁ in Set.Ioc (-X 1) (X 1),
          ∫⁻ z₂ in Set.Ioc (-X 2) (X 2),
            ∫⁻ z₃ in Set.Ioc (-X 3) (X 3),
              f ![z₀, z₁, z₂, z₃] := by
  have hbox := measurableSet_bourgainFullBox X
  rw [← lintegral_indicator hbox]
  rw [lintegral_fin_four _ (hf.indicator hbox)]
  simp_rw [← lintegral_indicator measurableSet_Ioc]
  have hmem (z₀ z₁ z₂ z₃ : ℝ) :
      ![z₀, z₁, z₂, z₃] ∈ bourgainFullBox X ↔
        ((z₀ ∈ Set.Ioc (-X 0) (X 0)) ∧
          (z₁ ∈ Set.Ioc (-X 1) (X 1)) ∧
          (z₂ ∈ Set.Ioc (-X 2) (X 2)) ∧
          (z₃ ∈ Set.Ioc (-X 3) (X 3))) := by
    simp only [bourgainFullBox, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro h
      exact ⟨h 0, h 1, h 2, h 3⟩
    · rintro ⟨h₀, h₁, h₂, h₃⟩ j
      fin_cases j
      · exact h₀
      · exact h₁
      · exact h₂
      · exact h₃
  simp only [Set.indicator, hmem]
  apply lintegral_congr
  intro z₀
  by_cases h₀ : z₀ ∈ Set.Ioc (-X 0) (X 0)
  · simp only [h₀, true_and, ↓reduceIte]
    apply lintegral_congr
    intro z₁
    by_cases h₁ : z₁ ∈ Set.Ioc (-X 1) (X 1)
    · simp only [h₁, true_and, ↓reduceIte]
      apply lintegral_congr
      intro z₂
      by_cases h₂ : z₂ ∈ Set.Ioc (-X 2) (X 2)
      · simp only [h₂, true_and, ↓reduceIte]
      · simp [h₂]
    · simp [h₁]
  · simp [h₀]

def bourgainA6FirstSpacingScale
    (H : ℕ) (δ Δ : ℝ) : BourgainPhaseSpace :=
  ![(1 / 2 : ℝ), (1 / 2 : ℝ),
    Real.sqrt H / (δ * (H : ℝ) ^ (2 : ℕ)),
    Real.sqrt H / (Δ * (H : ℝ))]

@[simp] theorem bourgainA6FirstSpacingScale_zero
    (H : ℕ) (δ Δ : ℝ) :
    bourgainA6FirstSpacingScale H δ Δ 0 = 1 / 2 := rfl

@[simp] theorem bourgainA6FirstSpacingScale_one
    (H : ℕ) (δ Δ : ℝ) :
    bourgainA6FirstSpacingScale H δ Δ 1 = 1 / 2 := rfl

@[simp] theorem bourgainA6FirstSpacingScale_two
    (H : ℕ) (δ Δ : ℝ) :
    bourgainA6FirstSpacingScale H δ Δ 2 =
      Real.sqrt H / (δ * (H : ℝ) ^ (2 : ℕ)) := rfl

@[simp] theorem bourgainA6FirstSpacingScale_three
    (H : ℕ) (δ Δ : ℝ) :
    bourgainA6FirstSpacingScale H δ Δ 3 =
      Real.sqrt H / (Δ * (H : ℝ)) := rfl

theorem bourgainFejerFullBoxMoment_firstSpacingScale_eq
    {H : ℕ} (hH : 0 < H) (δ Δ : ℝ) :
    bourgainFejerFullBoxMoment H
        (bourgainA6FirstSpacingScale H δ Δ) =
      ∫⁻ z₀ in Set.Ioc (-(1 / 2 : ℝ)) (1 / 2),
        ∫⁻ z₁ in Set.Ioc (-(1 / 2 : ℝ)) (1 / 2),
          ∫⁻ z₂ in Set.Ioc
              (-(Real.sqrt H / (δ * (H : ℝ) ^ (2 : ℕ))))
              (Real.sqrt H / (δ * (H : ℝ) ^ (2 : ℕ))),
            ∫⁻ z₃ in Set.Ioc
                (-(Real.sqrt H / (Δ * (H : ℝ))))
                (Real.sqrt H / (Δ * (H : ℝ))),
              ENNReal.ofReal
                (‖bourgainA6ExponentialSum H
                    z₀ z₁ (z₂ / Real.sqrt H) (z₃ / Real.sqrt H)‖ ^
                      (12 : ℕ)) := by
  unfold bourgainFejerFullBoxMoment
  rw [setLIntegral_bourgainFullBox_eq_iterated]
  · simp only [bourgainA6FirstSpacingScale, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    apply lintegral_congr
    intro z₀
    apply lintegral_congr
    intro z₁
    apply lintegral_congr
    intro z₂
    apply lintegral_congr
    intro z₃
    rw [norm_sq_bourgainSixfoldCharacterCloud_eq_A6_pow_twelve hH]
    change
      ENNReal.ofReal
          (‖bourgainA6ExponentialSum H
              z₀ z₁ (z₂ / Real.sqrt H) (z₃ / Real.sqrt H)‖ ^
                (12 : ℕ)) =
        ENNReal.ofReal
          (‖bourgainA6ExponentialSum H
              z₀ z₁ (z₂ / Real.sqrt H) (z₃ / Real.sqrt H)‖ ^
                (12 : ℕ))
    rfl
  · unfold bourgainSixfoldCharacterCloud bourgainAdditiveCharacter
      bourgainDot bourgainSixfoldMoment bourgainMomentCurve
    fun_prop

private theorem lintegral_Ioc_ofReal_eq_ofReal_intervalIntegral
    {a b : ℝ} (hab : a ≤ b) (f : ℝ → ℝ)
    (hf : Continuous f) (hn : ∀ x, 0 ≤ f x) :
    (∫⁻ x in Set.Ioc a b, ENNReal.ofReal (f x)) =
      ENNReal.ofReal (∫ x in a..b, f x) := by
  have hi : Integrable f (volume.restrict (Set.Ioc a b)) := by
    exact hf.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hae : 0 ≤ᵐ[volume.restrict (Set.Ioc a b)] f :=
    Filter.Eventually.of_forall hn
  rw [intervalIntegral.integral_of_le hab]
  exact (ofReal_integral_eq_lintegral_ofReal hi hae).symm

theorem intervalIntegral_intervalIntegral_swap
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (f : ℝ → ℝ → ℝ)
    (hf : Continuous (Function.uncurry f)) :
    (∫ x in a..b, ∫ y in c..d, f x y) =
      ∫ y in c..d, ∫ x in a..b, f x y := by
  have hi :
      Integrable (Function.uncurry f)
        ((volume.restrict (Set.Ioc a b)).prod
          (volume.restrict (Set.Ioc c d))) := by
    rw [Measure.prod_restrict]
    have hcompact :
        IsCompact (Set.Icc a b ×ˢ Set.Icc c d) :=
      isCompact_Icc.prod isCompact_Icc
    exact
      (hf.continuousOn.integrableOn_compact hcompact).mono_set
        (Set.prod_mono Set.Ioc_subset_Icc_self
          Set.Ioc_subset_Icc_self)
  simp_rw [intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_of_le hcd]
  exact integral_integral_swap hi

theorem intervalIntegral_four_reorder_two_three_one_zero
    {R₀ R₁ R₂ R₃ : ℝ}
    (hR₀ : 0 ≤ R₀) (hR₁ : 0 ≤ R₁)
    (hR₂ : 0 ≤ R₂) (hR₃ : 0 ≤ R₃)
    (f : BourgainPhaseSpace → ℝ) (hf : Continuous f) :
    (∫ z₀ in (-R₀)..R₀,
      ∫ z₁ in (-R₁)..R₁,
        ∫ z₂ in (-R₂)..R₂,
          ∫ z₃ in (-R₃)..R₃,
            f ![z₀, z₁, z₂, z₃]) =
      ∫ z₂ in (-R₂)..R₂,
        ∫ z₃ in (-R₃)..R₃,
          ∫ z₁ in (-R₁)..R₁,
            ∫ z₀ in (-R₀)..R₀,
              f ![z₀, z₁, z₂, z₃] := by
  have h₀ := neg_le_self hR₀
  have h₁ := neg_le_self hR₁
  have h₂ := neg_le_self hR₂
  have h₃ := neg_le_self hR₃
  calc
    (∫ z₀ in (-R₀)..R₀,
      ∫ z₁ in (-R₁)..R₁,
        ∫ z₂ in (-R₂)..R₂,
          ∫ z₃ in (-R₃)..R₃,
            f ![z₀, z₁, z₂, z₃]) =
        ∫ z₁ in (-R₁)..R₁,
          ∫ z₀ in (-R₀)..R₀,
            ∫ z₂ in (-R₂)..R₂,
              ∫ z₃ in (-R₃)..R₃,
                f ![z₀, z₁, z₂, z₃] := by
      apply intervalIntegral_intervalIntegral_swap h₀ h₁
      fun_prop
    _ =
        ∫ z₁ in (-R₁)..R₁,
          ∫ z₂ in (-R₂)..R₂,
            ∫ z₀ in (-R₀)..R₀,
              ∫ z₃ in (-R₃)..R₃,
                f ![z₀, z₁, z₂, z₃] := by
      apply intervalIntegral.integral_congr
      intro z₁ hz₁
      apply intervalIntegral_intervalIntegral_swap h₀ h₂
      fun_prop
    _ =
        ∫ z₂ in (-R₂)..R₂,
          ∫ z₁ in (-R₁)..R₁,
            ∫ z₀ in (-R₀)..R₀,
              ∫ z₃ in (-R₃)..R₃,
                f ![z₀, z₁, z₂, z₃] := by
      apply intervalIntegral_intervalIntegral_swap h₁ h₂
      fun_prop
    _ =
        ∫ z₂ in (-R₂)..R₂,
          ∫ z₁ in (-R₁)..R₁,
            ∫ z₃ in (-R₃)..R₃,
              ∫ z₀ in (-R₀)..R₀,
                f ![z₀, z₁, z₂, z₃] := by
      apply intervalIntegral.integral_congr
      intro z₂ hz₂
      apply intervalIntegral.integral_congr
      intro z₁ hz₁
      apply intervalIntegral_intervalIntegral_swap h₀ h₃
      fun_prop
    _ =
        ∫ z₂ in (-R₂)..R₂,
          ∫ z₃ in (-R₃)..R₃,
            ∫ z₁ in (-R₁)..R₁,
              ∫ z₀ in (-R₀)..R₀,
                f ![z₀, z₁, z₂, z₃] := by
      apply intervalIntegral.integral_congr
      intro z₂ hz₂
      apply intervalIntegral_intervalIntegral_swap h₁ h₃
      fun_prop

theorem lintegral_Ioc_four_ofReal_eq_ofReal_intervalIntegral
    {R₀ R₁ R₂ R₃ : ℝ}
    (hR₀ : 0 ≤ R₀) (hR₁ : 0 ≤ R₁)
    (hR₂ : 0 ≤ R₂) (hR₃ : 0 ≤ R₃)
    (f : BourgainPhaseSpace → ℝ)
    (hf : Continuous f) (hn : ∀ z, 0 ≤ f z) :
    (∫⁻ z₀ in Set.Ioc (-R₀) R₀,
      ∫⁻ z₁ in Set.Ioc (-R₁) R₁,
        ∫⁻ z₂ in Set.Ioc (-R₂) R₂,
          ∫⁻ z₃ in Set.Ioc (-R₃) R₃,
            ENNReal.ofReal (f ![z₀, z₁, z₂, z₃])) =
      ENNReal.ofReal
        (∫ z₀ in (-R₀)..R₀,
          ∫ z₁ in (-R₁)..R₁,
            ∫ z₂ in (-R₂)..R₂,
              ∫ z₃ in (-R₃)..R₃,
                f ![z₀, z₁, z₂, z₃]) := by
  have h₃ (z₀ z₁ z₂ : ℝ) :
      (∫⁻ z₃ in Set.Ioc (-R₃) R₃,
          ENNReal.ofReal (f ![z₀, z₁, z₂, z₃])) =
        ENNReal.ofReal
          (∫ z₃ in (-R₃)..R₃, f ![z₀, z₁, z₂, z₃]) := by
    apply lintegral_Ioc_ofReal_eq_ofReal_intervalIntegral
      (neg_le_self hR₃)
    · exact hf.comp (by fun_prop)
    · intro z₃
      exact hn _
  simp_rw [h₃]
  have h₂ (z₀ z₁ : ℝ) :
      (∫⁻ z₂ in Set.Ioc (-R₂) R₂,
          ENNReal.ofReal
            (∫ z₃ in (-R₃)..R₃, f ![z₀, z₁, z₂, z₃])) =
        ENNReal.ofReal
          (∫ z₂ in (-R₂)..R₂,
            ∫ z₃ in (-R₃)..R₃, f ![z₀, z₁, z₂, z₃]) := by
    apply lintegral_Ioc_ofReal_eq_ofReal_intervalIntegral
      (neg_le_self hR₂)
    · fun_prop
    · intro z₂
      apply intervalIntegral.integral_nonneg (neg_le_self hR₃)
      intro z₃ hz₃
      exact hn _
  simp_rw [h₂]
  have h₁ (z₀ : ℝ) :
      (∫⁻ z₁ in Set.Ioc (-R₁) R₁,
          ENNReal.ofReal
            (∫ z₂ in (-R₂)..R₂,
              ∫ z₃ in (-R₃)..R₃, f ![z₀, z₁, z₂, z₃])) =
        ENNReal.ofReal
          (∫ z₁ in (-R₁)..R₁,
            ∫ z₂ in (-R₂)..R₂,
              ∫ z₃ in (-R₃)..R₃, f ![z₀, z₁, z₂, z₃]) := by
    apply lintegral_Ioc_ofReal_eq_ofReal_intervalIntegral
      (neg_le_self hR₁)
    · fun_prop
    · intro z₁
      apply intervalIntegral.integral_nonneg (neg_le_self hR₂)
      intro z₂ hz₂
      apply intervalIntegral.integral_nonneg (neg_le_self hR₃)
      intro z₃ hz₃
      exact hn _
  simp_rw [h₁]
  apply lintegral_Ioc_ofReal_eq_ofReal_intervalIntegral
    (neg_le_self hR₀)
  · fun_prop
  · intro z₀
    apply intervalIntegral.integral_nonneg (neg_le_self hR₁)
    intro z₁ hz₁
    apply intervalIntegral.integral_nonneg (neg_le_self hR₂)
    intro z₂ hz₂
    apply intervalIntegral.integral_nonneg (neg_le_self hR₃)
    intro z₃ hz₃
    exact hn _

def bourgainA6CenteredFirstSpacingMoment
    (H : ℕ) (δ Δ : ℝ) : ℝ :=
  ∫ z₀ in (-(1 / 2 : ℝ))..(1 / 2),
    ∫ z₁ in (-(1 / 2 : ℝ))..(1 / 2),
      ∫ z₂ in
          (-(Real.sqrt H / (δ * (H : ℝ) ^ (2 : ℕ))))..
            (Real.sqrt H / (δ * (H : ℝ) ^ (2 : ℕ))),
        ∫ z₃ in
            (-(Real.sqrt H / (Δ * (H : ℝ))))..
              (Real.sqrt H / (Δ * (H : ℝ))),
          ‖bourgainA6ExponentialSum H
              z₀ z₁ (z₂ / Real.sqrt H) (z₃ / Real.sqrt H)‖ ^
                (12 : ℕ)

def bourgainA6FirstSpacingTailMoment
    (H : ℕ) (δ Δ : ℝ) : ℝ :=
  ∫ z₂ in
      (-(Real.sqrt H / (δ * (H : ℝ) ^ (2 : ℕ))))..
        (Real.sqrt H / (δ * (H : ℝ) ^ (2 : ℕ))),
    ∫ z₃ in
        (-(Real.sqrt H / (Δ * (H : ℝ))))..
          (Real.sqrt H / (Δ * (H : ℝ))),
      ∫ x₂ in (0 : ℝ)..1,
        ∫ x₁ in (0 : ℝ)..1,
          ‖bourgainA6ExponentialSum H
              x₁ x₂ (z₂ / Real.sqrt H) (z₃ / Real.sqrt H)‖ ^
                (12 : ℕ)

def bourgainA6RestrictedTailMoment
    (H : ℕ) (A B : ℝ) : ℝ :=
  ∫ x₃ in (-1 / A)..(1 / A),
    ∫ x₄ in (-1 / B)..(1 / B),
      ∫ x₂ in (0 : ℝ)..1,
        ∫ x₁ in (0 : ℝ)..1,
          ‖bourgainA6ExponentialSum H x₁ x₂ x₃ x₄‖ ^ (12 : ℕ)

theorem bourgainA6RescaledMoment_eq_restrictedTail
    (H : ℕ) {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    bourgainA6RescaledMoment H A B =
      A * B * bourgainA6RestrictedTailMoment H A B := by
  simpa [bourgainA6RestrictedTailMoment] using!
    (bourgainA6RescaledMoment_eq H hA hB)

theorem bourgainA6CenteredFirstSpacingMoment_eq_tail
    {H : ℕ} {δ Δ : ℝ} (hδ : 0 < δ) (hΔ : 0 < Δ) :
    bourgainA6CenteredFirstSpacingMoment H δ Δ =
      bourgainA6FirstSpacingTailMoment H δ Δ := by
  have hR₂ :
      0 ≤ Real.sqrt H / (δ * (H : ℝ) ^ (2 : ℕ)) := by
    positivity
  have hR₃ :
      0 ≤ Real.sqrt H / (Δ * (H : ℝ)) := by
    positivity
  let f : BourgainPhaseSpace → ℝ := fun z =>
    ‖bourgainA6ExponentialSum H
        (z 0) (z 1) (z 2 / Real.sqrt H) (z 3 / Real.sqrt H)‖ ^
          (12 : ℕ)
  have hf : Continuous f := by
    unfold f bourgainA6ExponentialSum bourgainA6HigherPhase
    fun_prop
  rw [bourgainA6CenteredFirstSpacingMoment]
  have hreorder :
      (∫ z₀ in (-(1 / 2 : ℝ))..(1 / 2),
        ∫ z₁ in (-(1 / 2 : ℝ))..(1 / 2),
          ∫ z₂ in
              (-(Real.sqrt H / (δ * (H : ℝ) ^ (2 : ℕ))))..
                (Real.sqrt H / (δ * (H : ℝ) ^ (2 : ℕ))),
            ∫ z₃ in
                (-(Real.sqrt H / (Δ * (H : ℝ))))..
                  (Real.sqrt H / (Δ * (H : ℝ))),
              ‖bourgainA6ExponentialSum H
                  z₀ z₁ (z₂ / Real.sqrt H) (z₃ / Real.sqrt H)‖ ^
                    (12 : ℕ)) =
        ∫ z₂ in
            (-(Real.sqrt H / (δ * (H : ℝ) ^ (2 : ℕ))))..
              (Real.sqrt H / (δ * (H : ℝ) ^ (2 : ℕ))),
          ∫ z₃ in
              (-(Real.sqrt H / (Δ * (H : ℝ))))..
                (Real.sqrt H / (Δ * (H : ℝ))),
            ∫ z₁ in (-(1 / 2 : ℝ))..(1 / 2),
              ∫ z₀ in (-(1 / 2 : ℝ))..(1 / 2),
                ‖bourgainA6ExponentialSum H
                    z₀ z₁ (z₂ / Real.sqrt H) (z₃ / Real.sqrt H)‖ ^
                      (12 : ℕ) := by
    simpa [f] using
      (intervalIntegral_four_reorder_two_three_one_zero
        (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (0 : ℝ) ≤ 1 / 2) hR₂ hR₃ f hf)
  rw [hreorder]
  have hfirst (z₂ z₃ x₂ : ℝ) :
      (∫ x₁ in (-(1 / 2 : ℝ))..(1 / 2),
          ‖bourgainA6ExponentialSum H
              x₁ x₂ (z₂ / Real.sqrt H) (z₃ / Real.sqrt H)‖ ^
                (12 : ℕ)) =
        ∫ x₁ in (0 : ℝ)..1,
          ‖bourgainA6ExponentialSum H
              x₁ x₂ (z₂ / Real.sqrt H) (z₃ / Real.sqrt H)‖ ^
                (12 : ℕ) := by
    have hp :=
      (periodic_norm_bourgainA6ExponentialSum_pow_twelve_first H
        x₂ (z₂ / Real.sqrt H) (z₃ / Real.sqrt H)).intervalIntegral_add_eq
          (-(1 / 2 : ℝ)) 0
    convert hp using 1 <;> norm_num
  simp_rw [hfirst]
  have hsecond (z₂ z₃ : ℝ) :
      Function.Periodic
        (fun x₂ =>
          ∫ x₁ in (0 : ℝ)..1,
            ‖bourgainA6ExponentialSum H
                x₁ x₂ (z₂ / Real.sqrt H) (z₃ / Real.sqrt H)‖ ^
                  (12 : ℕ)) 1 := by
    intro x₂
    apply intervalIntegral.integral_congr
    intro x₁ hx₁
    have hp :=
      periodic_norm_bourgainA6ExponentialSum_pow_twelve_second H
        x₁ (z₂ / Real.sqrt H) (z₃ / Real.sqrt H) x₂
    change
      ‖bourgainA6ExponentialSum H
          x₁ (x₂ + 1) (z₂ / Real.sqrt H) (z₃ / Real.sqrt H)‖ ^
            (12 : ℕ) =
        ‖bourgainA6ExponentialSum H
          x₁ x₂ (z₂ / Real.sqrt H) (z₃ / Real.sqrt H)‖ ^
            (12 : ℕ)
    exact hp
  unfold bourgainA6FirstSpacingTailMoment
  apply intervalIntegral.integral_congr
  intro z₂ hz₂
  apply intervalIntegral.integral_congr
  intro z₃ hz₃
  have hp :=
    (hsecond z₂ z₃).intervalIntegral_add_eq
      (-(1 / 2 : ℝ)) 0
  convert hp using 1 <;> norm_num

theorem bourgainA6FirstSpacingTailMoment_eq_restricted
    {H : ℕ} (hH : 0 < H) {δ Δ : ℝ}
    (hδ : 0 < δ) (hΔ : 0 < Δ) :
    bourgainA6FirstSpacingTailMoment H δ Δ =
      (H : ℝ) *
        bourgainA6RestrictedTailMoment H
          (δ * (H : ℝ) ^ (2 : ℕ)) (Δ * (H : ℝ)) := by
  let A : ℝ := δ * (H : ℝ) ^ (2 : ℕ)
  let B : ℝ := Δ * (H : ℝ)
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  have hsqrt : Real.sqrt (H : ℝ) ≠ 0 :=
    (Real.sqrt_pos.2 hHr).ne'
  have hA : 0 < A := by
    unfold A
    positivity
  have hB : 0 < B := by
    unfold B
    positivity
  let P : ℝ → ℝ → ℝ := fun x₃ x₄ =>
    ∫ x₂ in (0 : ℝ)..1,
      ∫ x₁ in (0 : ℝ)..1,
        ‖bourgainA6ExponentialSum H x₁ x₂ x₃ x₄‖ ^ (12 : ℕ)
  have hinner (z₂ : ℝ) :
      (∫ z₃ in (-(Real.sqrt H / B))..(Real.sqrt H / B),
          P (z₂ / Real.sqrt H) (z₃ / Real.sqrt H)) =
        Real.sqrt H *
          ∫ x₄ in (-1 / B)..(1 / B),
            P (z₂ / Real.sqrt H) x₄ := by
    have hchange :=
      intervalIntegral.integral_comp_div
        (fun x₄ : ℝ => P (z₂ / Real.sqrt H) x₄)
        hsqrt
        (a := -(Real.sqrt H / B))
        (b := Real.sqrt H / B)
    convert hchange using 1
    all_goals
      field_simp
      ring
  have houter :
      (∫ z₂ in (-(Real.sqrt H / A))..(Real.sqrt H / A),
          ∫ x₄ in (-1 / B)..(1 / B),
            P (z₂ / Real.sqrt H) x₄) =
        Real.sqrt H *
          ∫ x₃ in (-1 / A)..(1 / A),
            ∫ x₄ in (-1 / B)..(1 / B),
              P x₃ x₄ := by
    have hchange :=
      intervalIntegral.integral_comp_div
        (fun x₃ : ℝ =>
          ∫ x₄ in (-1 / B)..(1 / B), P x₃ x₄)
        hsqrt
        (a := -(Real.sqrt H / A))
        (b := Real.sqrt H / A)
    convert hchange using 1
    all_goals
      field_simp
      ring
  unfold bourgainA6FirstSpacingTailMoment
  change
    (∫ z₂ in (-(Real.sqrt H / A))..(Real.sqrt H / A),
      ∫ z₃ in (-(Real.sqrt H / B))..(Real.sqrt H / B),
        P (z₂ / Real.sqrt H) (z₃ / Real.sqrt H)) = _
  simp_rw [hinner]
  rw [intervalIntegral.integral_const_mul, houter]
  change
    Real.sqrt H * (Real.sqrt H *
      bourgainA6RestrictedTailMoment H A B) =
        (H : ℝ) *
          bourgainA6RestrictedTailMoment H
            (δ * (H : ℝ) ^ (2 : ℕ)) (Δ * (H : ℝ))
  rw [← mul_assoc, Real.mul_self_sqrt hHr.le]

theorem bourgainA6Scale_mul_centeredMoment_eq_rescaled
    {H : ℕ} (hH : 0 < H) {δ Δ : ℝ}
    (hδ : 0 < δ) (hΔ : 0 < Δ) :
    (δ * (H : ℝ) ^ (2 : ℕ)) * (Δ * (H : ℝ)) *
        bourgainA6CenteredFirstSpacingMoment H δ Δ =
      (H : ℝ) * bourgainA6FirstSpacingMoment H δ Δ := by
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  have hA : 0 < δ * (H : ℝ) ^ (2 : ℕ) := by positivity
  have hB : 0 < Δ * (H : ℝ) := by positivity
  rw [bourgainA6CenteredFirstSpacingMoment_eq_tail hδ hΔ]
  rw [bourgainA6FirstSpacingTailMoment_eq_restricted hH hδ hΔ]
  unfold bourgainA6FirstSpacingMoment
  rw [bourgainA6RescaledMoment_eq_restrictedTail H hA hB]
  ring

theorem bourgainA6CenteredFirstSpacingMoment_nonneg
    (H : ℕ) {δ Δ : ℝ} (hδ : 0 < δ) (hΔ : 0 < Δ) :
    0 ≤ bourgainA6CenteredFirstSpacingMoment H δ Δ := by
  have hR₂ :
      0 ≤ Real.sqrt H / (δ * (H : ℝ) ^ (2 : ℕ)) := by
    positivity
  have hR₃ :
      0 ≤ Real.sqrt H / (Δ * (H : ℝ)) := by
    positivity
  unfold bourgainA6CenteredFirstSpacingMoment
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro z₀ hz₀
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro z₁ hz₁
  apply intervalIntegral.integral_nonneg (neg_le_self hR₂)
  intro z₂ hz₂
  apply intervalIntegral.integral_nonneg (neg_le_self hR₃)
  intro z₃ hz₃
  positivity

theorem bourgainA6FirstSpacingScale_pos
    {H : ℕ} (hH : 0 < H) {δ Δ : ℝ}
    (hδ : 0 < δ) (hΔ : 0 < Δ) :
    ∀ j, 0 < bourgainA6FirstSpacingScale H δ Δ j := by
  intro j
  fin_cases j <;> simp [bourgainA6FirstSpacingScale] <;> positivity

theorem prod_bourgainA6FirstSpacingScale_eq
    {H : ℕ} (hH : 0 < H) {δ Δ : ℝ}
    (hδ : 0 < δ) (hΔ : 0 < Δ) :
    (∏ j : Fin 4, bourgainA6FirstSpacingScale H δ Δ j) =
      (H : ℝ) /
        (4 * (δ * (H : ℝ) ^ (2 : ℕ)) * (Δ * (H : ℝ))) := by
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  have hAne : δ * (H : ℝ) ^ (2 : ℕ) ≠ 0 := by positivity
  have hBne : Δ * (H : ℝ) ≠ 0 := by positivity
  rw [Fin.prod_univ_four]
  simp only [bourgainA6FirstSpacingScale_zero,
    bourgainA6FirstSpacingScale_one,
    bourgainA6FirstSpacingScale_two,
    bourgainA6FirstSpacingScale_three]
  field_simp
  nlinarith [Real.sq_sqrt hHr.le]

theorem bourgainFejerNearConstant_firstSpacingScale_eq
    {H : ℕ} (hH : 0 < H) {δ Δ : ℝ}
    (hδ : 0 < δ) (hΔ : 0 < Δ) :
    bourgainFejerNearConstant
        (bourgainA6FirstSpacingScale H δ Δ) =
      16 * (H : ℝ) ^ (2 : ℕ) /
        (Real.pi ^ (8 : ℕ) *
          (δ * (H : ℝ) ^ (2 : ℕ)) ^ (2 : ℕ) *
          (Δ * (H : ℝ)) ^ (2 : ℕ)) := by
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  have hAne : δ * (H : ℝ) ^ (2 : ℕ) ≠ 0 := by positivity
  have hBne : Δ * (H : ℝ) ≠ 0 := by positivity
  unfold bourgainFejerNearConstant
  rw [Fin.prod_univ_four]
  simp only [bourgainA6FirstSpacingScale_zero,
    bourgainA6FirstSpacingScale_one,
    bourgainA6FirstSpacingScale_two,
    bourgainA6FirstSpacingScale_three]
  field_simp [Real.pi_ne_zero]
  nlinarith [Real.sq_sqrt hHr.le]

theorem bourgainFejerFullBoxMoment_firstSpacingScale_eq_ofReal
    {H : ℕ} (hH : 0 < H) {δ Δ : ℝ}
    (hδ : 0 < δ) (hΔ : 0 < Δ) :
    bourgainFejerFullBoxMoment H
        (bourgainA6FirstSpacingScale H δ Δ) =
      ENNReal.ofReal (bourgainA6CenteredFirstSpacingMoment H δ Δ) := by
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  have hR₂ :
      0 ≤ Real.sqrt H / (δ * (H : ℝ) ^ (2 : ℕ)) := by
    positivity
  have hR₃ :
      0 ≤ Real.sqrt H / (Δ * (H : ℝ)) := by
    positivity
  rw [bourgainFejerFullBoxMoment_firstSpacingScale_eq hH]
  let f : BourgainPhaseSpace → ℝ := fun z =>
    ‖bourgainA6ExponentialSum H
        (z 0) (z 1) (z 2 / Real.sqrt H) (z 3 / Real.sqrt H)‖ ^
          (12 : ℕ)
  have hf : Continuous f := by
    unfold f bourgainA6ExponentialSum bourgainA6HigherPhase
    fun_prop
  have hn : ∀ z, 0 ≤ f z := by
    intro z
    unfold f
    positivity
  have hconvert :=
    lintegral_Ioc_four_ofReal_eq_ofReal_intervalIntegral
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) hR₂ hR₃ f hf hn
  simpa [f, bourgainA6CenteredFirstSpacingMoment] using hconvert

theorem bourgainFejerSpacingEnergy_le_scaleProduct_mul_centered
    {H : ℕ} (hH : 0 < H) {δ Δ : ℝ}
    (hδ : 0 < δ) (hΔ : 0 < Δ) :
    bourgainFejerSpacingEnergy H
        (bourgainA6FirstSpacingScale H δ Δ) ≤
      (∏ j : Fin 4, bourgainA6FirstSpacingScale H δ Δ j) *
        bourgainA6CenteredFirstSpacingMoment H δ Δ := by
  let X := bourgainA6FirstSpacingScale H δ Δ
  have hXpos : ∀ j, 0 < X j :=
    bourgainA6FirstSpacingScale_pos hH hδ hΔ
  have hXnonneg : ∀ j, 0 ≤ X j := fun j => (hXpos j).le
  have hMnonneg :
      0 ≤ bourgainA6CenteredFirstSpacingMoment H δ Δ :=
    bourgainA6CenteredFirstSpacingMoment_nonneg H hδ hΔ
  have hE :=
    ofReal_bourgainFejerSpacingEnergy_le_fullBox
      (H := H) (X := X) hXnonneg
  rw [bourgainFejerFullBoxMoment_firstSpacingScale_eq_ofReal
    hH hδ hΔ] at hE
  rw [← ENNReal.ofReal_prod_of_nonneg
      (fun j hj => hXnonneg j)] at hE
  rw [← ENNReal.ofReal_mul
      (Finset.prod_nonneg fun j hj => hXnonneg j)] at hE
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg
      (Finset.prod_nonneg fun j hj => hXnonneg j)
      hMnonneg)).mp hE

/-- Exact Fejér/A₆ first-spacing bound.  This is Bourgain's Corollary 3
connector before inserting the sharp `A₆` estimate. -/
theorem bourgainFirstSpacingCount_le_A6FirstSpacingMoment
    {H : ℕ} (hH : 0 < H) {δ Δ : ℝ}
    (hδ : 0 < δ) (hΔ : 0 < Δ) :
    (bourgainFirstSpacingCount H
        (bourgainA6FirstSpacingScale H δ Δ) : ℝ) ≤
      Real.pi ^ (8 : ℕ) / 64 *
        bourgainA6FirstSpacingMoment H δ Δ := by
  let X := bourgainA6FirstSpacingScale H δ Δ
  let A : ℝ := δ * (H : ℝ) ^ (2 : ℕ)
  let B : ℝ := Δ * (H : ℝ)
  let M : ℝ := bourgainA6CenteredFirstSpacingMoment H δ Δ
  let R : ℝ := bourgainA6FirstSpacingMoment H δ Δ
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  have hA : 0 < A := by
    unfold A
    positivity
  have hB : 0 < B := by
    unfold B
    positivity
  have hpi : 0 < Real.pi := Real.pi_pos
  have hX : ∀ j, 0 < X j :=
    bourgainA6FirstSpacingScale_pos hH hδ hΔ
  have hmajor :=
    bourgainFejerNearConstant_mul_firstSpacingCount_le
      (H := H) (X := X) hX
  have hupper :=
    bourgainFejerSpacingEnergy_le_scaleProduct_mul_centered
      hH hδ hΔ
  have hchain :
      bourgainFejerNearConstant X *
          (bourgainFirstSpacingCount H X : ℝ) ≤
        (∏ j : Fin 4, X j) * M := by
    exact hmajor.trans hupper
  have hnear :
      bourgainFejerNearConstant X =
        16 * (H : ℝ) ^ (2 : ℕ) /
          (Real.pi ^ (8 : ℕ) * A ^ (2 : ℕ) * B ^ (2 : ℕ)) := by
    simpa [X, A, B] using
      (bourgainFejerNearConstant_firstSpacingScale_eq
        hH hδ hΔ)
  have hprod :
      (∏ j : Fin 4, X j) =
        (H : ℝ) / (4 * A * B) := by
    simpa [X, A, B] using
      (prod_bourgainA6FirstSpacingScale_eq hH hδ hΔ)
  have hscale :
      A * B * M = (H : ℝ) * R := by
    simpa [A, B, M, R] using
      (bourgainA6Scale_mul_centeredMoment_eq_rescaled
        hH hδ hΔ)
  have hnearPos : 0 < bourgainFejerNearConstant X := by
    rw [hnear]
    positivity
  have hdiv :
      (bourgainFirstSpacingCount H X : ℝ) ≤
        ((∏ j : Fin 4, X j) * M) /
          bourgainFejerNearConstant X :=
    (le_div_iff₀ hnearPos).2 (by simpa [mul_comm] using hchain)
  calc
    (bourgainFirstSpacingCount H X : ℝ) ≤
        ((∏ j : Fin 4, X j) * M) /
          bourgainFejerNearConstant X := hdiv
    _ = Real.pi ^ (8 : ℕ) / 64 * R := by
      rw [hprod, hnear]
      field_simp
      nlinarith [hscale]

theorem bourgainFirstSpacingCount_subpower_of_A6
    (hA6 :
      ∀ {ε : ℝ}, 0 < ε →
        ∃ C : ℝ, 0 < C ∧
          ∀ H : ℕ,
            bourgainA6LiteralMoment H ≤
              C * (H : ℝ) ^ ε * (H : ℝ) ^ (6 : ℕ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (H : ℕ), 0 < H → ∀ {δ Δ : ℝ},
        0 < δ → 0 < Δ →
        1 / (H : ℝ) ^ (2 : ℕ) ≤ δ →
        1 / (H : ℝ) ≤ Δ →
        (bourgainFirstSpacingCount H
            (bourgainA6FirstSpacingScale H δ Δ) : ℝ) ≤
          δ * Δ *
            (C * (H : ℝ) ^ ε * (H : ℝ) ^ (9 : ℕ)) := by
  obtain ⟨C, hC, hmoment⟩ :=
    bourgainA6FirstSpacingMoment_subpower_of_A6 hA6 hε
  refine ⟨Real.pi ^ (8 : ℕ) / 64 * C, by positivity, ?_⟩
  intro H hH δ Δ hδ hΔ hδrange hΔrange
  have hfirst :=
    bourgainFirstSpacingCount_le_A6FirstSpacingMoment
      hH hδ hΔ
  have hsecond :=
    mul_le_mul_of_nonneg_left
      (hmoment H hH hδrange hΔrange)
      (by positivity : 0 ≤ Real.pi ^ (8 : ℕ) / 64)
  exact hfirst.trans (hsecond.trans_eq (by ring))

end

end RHTower
