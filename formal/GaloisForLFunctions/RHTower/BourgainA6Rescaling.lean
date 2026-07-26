/-
# Two-parameter rescaling of Bourgain's A₆ moment

This module proves the exact change of variables behind Bourgain's
Corollary 3.  Once the sharp `A₆ ≪ H^(6+ε)` theorem is available, rescaling
the two non-periodic coordinates gives
`A₆(H,δ,Δ) ≪ δ Δ H^(9+ε)` throughout its stated range.
-/
import GaloisForLFunctions.RHTower.BourgainA6TorusBaseline

open MeasureTheory

namespace RHTower

noncomputable section

def bourgainA6RescaledMoment
    (H : ℕ) (A B : ℝ) : ℝ :=
  ∫ x₃ in (-1 : ℝ)..1,
    ∫ x₄ in (-1 : ℝ)..1,
      ∫ x₂ in (0 : ℝ)..1,
        ∫ x₁ in (0 : ℝ)..1,
          ‖bourgainA6ExponentialSum H x₁ x₂
              (x₃ / A) (x₄ / B)‖ ^ (12 : ℕ)

private def bourgainA6TailMoment
    (H : ℕ) (x₃ x₄ : ℝ) : ℝ :=
  ∫ x₂ in (0 : ℝ)..1,
    ∫ x₁ in (0 : ℝ)..1,
      ‖bourgainA6ExponentialSum H x₁ x₂ x₃ x₄‖ ^ (12 : ℕ)

private theorem continuous_bourgainA6TailMoment
    (H : ℕ) :
    Continuous (Function.uncurry (bourgainA6TailMoment H)) := by
  unfold bourgainA6TailMoment bourgainA6ExponentialSum
    bourgainA6HigherPhase
  fun_prop

private theorem bourgainA6TailMoment_nonneg
    (H : ℕ) (x₃ x₄ : ℝ) :
    0 ≤ bourgainA6TailMoment H x₃ x₄ := by
  unfold bourgainA6TailMoment
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro x₂ hx₂
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro x₁ hx₁
  positivity

theorem bourgainA6RescaledMoment_eq
    (H : ℕ) {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    bourgainA6RescaledMoment H A B =
      A * B *
        ∫ x₃ in (-1 / A)..(1 / A),
          ∫ x₄ in (-1 / B)..(1 / B),
            bourgainA6TailMoment H x₃ x₄ := by
  have hA0 : A ≠ 0 := hA.ne'
  have hB0 : B ≠ 0 := hB.ne'
  have hinner (x₃ : ℝ) :
      (∫ x₄ in (-1 : ℝ)..1,
          bourgainA6TailMoment H (x₃ / A) (x₄ / B)) =
        B *
          ∫ x₄ in (-1 / B)..(1 / B),
            bourgainA6TailMoment H (x₃ / A) x₄ := by
    simpa using
      (intervalIntegral.integral_comp_div
        (fun x₄ : ℝ => bourgainA6TailMoment H (x₃ / A) x₄)
        hB0 (a := (-1 : ℝ)) (b := 1))
  have houter :
      (∫ x₃ in (-1 : ℝ)..1,
          (∫ x₄ in (-1 / B)..(1 / B),
            bourgainA6TailMoment H (x₃ / A) x₄)) =
        A *
          ∫ x₃ in (-1 / A)..(1 / A),
            ∫ x₄ in (-1 / B)..(1 / B),
              bourgainA6TailMoment H x₃ x₄ := by
    simpa using
      (intervalIntegral.integral_comp_div
        (fun x₃ : ℝ =>
          ∫ x₄ in (-1 / B)..(1 / B),
            bourgainA6TailMoment H x₃ x₄)
        hA0 (a := (-1 : ℝ)) (b := 1))
  unfold bourgainA6RescaledMoment
  change
    (∫ x₃ in (-1 : ℝ)..1,
      ∫ x₄ in (-1 : ℝ)..1,
        bourgainA6TailMoment H (x₃ / A) (x₄ / B)) = _
  simp_rw [hinner]
  rw [intervalIntegral.integral_const_mul, houter]
  ring

theorem bourgainA6RescaledMoment_le
    (H : ℕ) {A B : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B) :
    bourgainA6RescaledMoment H A B ≤
      A * B * bourgainA6LiteralMoment H := by
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hAinv : 1 / A ≤ 1 := by
    exact (div_le_one hApos).2 hA
  have hBinv : 1 / B ≤ 1 := by
    exact (div_le_one hBpos).2 hB
  have hAinv0 : 0 ≤ 1 / A := by positivity
  have hBinv0 : 0 ≤ 1 / B := by positivity
  have hinner (x₃ : ℝ) :
      (∫ x₄ in (-1 / B)..(1 / B),
          bourgainA6TailMoment H x₃ x₄) ≤
        ∫ x₄ in (-1 : ℝ)..1,
          bourgainA6TailMoment H x₃ x₄ := by
    apply intervalIntegral.integral_mono_interval
    · simpa only [neg_div] using neg_le_neg hBinv
    · simpa only [neg_div] using neg_le_self hBinv0
    · exact hBinv
    · filter_upwards with x₄
      exact bourgainA6TailMoment_nonneg H x₃ x₄
    · exact
        ((continuous_bourgainA6TailMoment H).comp
          (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
  have hsmallContinuous :
      Continuous fun x₃ : ℝ =>
        ∫ x₄ in (-1 / B)..(1 / B),
          bourgainA6TailMoment H x₃ x₄ := by
    unfold bourgainA6TailMoment bourgainA6ExponentialSum
      bourgainA6HigherPhase
    fun_prop
  have hfullContinuous :
      Continuous fun x₃ : ℝ =>
        ∫ x₄ in (-1 : ℝ)..1,
          bourgainA6TailMoment H x₃ x₄ := by
    unfold bourgainA6TailMoment bourgainA6ExponentialSum
      bourgainA6HigherPhase
    fun_prop
  have hcompare :
      (∫ x₃ in (-1 / A)..(1 / A),
          ∫ x₄ in (-1 / B)..(1 / B),
            bourgainA6TailMoment H x₃ x₄) ≤
        ∫ x₃ in (-1 : ℝ)..1,
          ∫ x₄ in (-1 : ℝ)..1,
            bourgainA6TailMoment H x₃ x₄ := by
    calc
      (∫ x₃ in (-1 / A)..(1 / A),
          ∫ x₄ in (-1 / B)..(1 / B),
            bourgainA6TailMoment H x₃ x₄) ≤
          ∫ x₃ in (-1 / A)..(1 / A),
            ∫ x₄ in (-1 : ℝ)..1,
              bourgainA6TailMoment H x₃ x₄ := by
        apply intervalIntegral.integral_mono_on
        · simpa only [neg_div] using neg_le_self hAinv0
        · exact hsmallContinuous.intervalIntegrable _ _
        · exact hfullContinuous.intervalIntegrable _ _
        · intro x₃ hx₃
          exact hinner x₃
      _ ≤
          ∫ x₃ in (-1 : ℝ)..1,
            ∫ x₄ in (-1 : ℝ)..1,
              bourgainA6TailMoment H x₃ x₄ := by
        apply intervalIntegral.integral_mono_interval
        · simpa only [neg_div] using neg_le_neg hAinv
        · simpa only [neg_div] using neg_le_self hAinv0
        · exact hAinv
        · filter_upwards with x₃
          apply intervalIntegral.integral_nonneg (by norm_num)
          intro x₄ hx₄
          exact bourgainA6TailMoment_nonneg H x₃ x₄
        · exact hfullContinuous.intervalIntegrable _ _
  rw [bourgainA6RescaledMoment_eq H hApos hBpos]
  apply mul_le_mul_of_nonneg_left
  · simpa [bourgainA6LiteralMoment, bourgainA6TailMoment] using hcompare
  · positivity

theorem bourgainA6RescaledMoment_subpower_of_A6
    (hA6 :
      ∀ {ε : ℝ}, 0 < ε →
        ∃ C : ℝ, 0 < C ∧
          ∀ H : ℕ,
            bourgainA6LiteralMoment H ≤
              C * (H : ℝ) ^ ε * (H : ℝ) ^ (6 : ℕ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (H : ℕ) {A B : ℝ}, 1 ≤ A → 1 ≤ B →
        bourgainA6RescaledMoment H A B ≤
          A * B *
            (C * (H : ℝ) ^ ε * (H : ℝ) ^ (6 : ℕ)) := by
  obtain ⟨C, hC, hbound⟩ := hA6 hε
  refine ⟨C, hC, ?_⟩
  intro H A B hA hB
  exact (bourgainA6RescaledMoment_le H hA hB).trans
    (mul_le_mul_of_nonneg_left (hbound H) (by positivity))

/-- Literal two-parameter moment in Bourgain's Corollary 3, written as the
exact rescaling of the `A₆` phase. -/
def bourgainA6FirstSpacingMoment
    (H : ℕ) (δ Δ : ℝ) : ℝ :=
  bourgainA6RescaledMoment H
    (δ * (H : ℝ) ^ (2 : ℕ)) (Δ * (H : ℝ))

/-- Bourgain's Corollary 3 follows unconditionally from the sharp `A₆`
theorem by the exact two-coordinate rescaling. -/
theorem bourgainA6FirstSpacingMoment_subpower_of_A6
    (hA6 :
      ∀ {ε : ℝ}, 0 < ε →
        ∃ C : ℝ, 0 < C ∧
          ∀ H : ℕ,
            bourgainA6LiteralMoment H ≤
              C * (H : ℝ) ^ ε * (H : ℝ) ^ (6 : ℕ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (H : ℕ), 0 < H → ∀ {δ Δ : ℝ},
        1 / (H : ℝ) ^ (2 : ℕ) ≤ δ →
        1 / (H : ℝ) ≤ Δ →
        bourgainA6FirstSpacingMoment H δ Δ ≤
          δ * Δ *
            (C * (H : ℝ) ^ ε * (H : ℝ) ^ (9 : ℕ)) := by
  obtain ⟨C, hC, hbound⟩ :=
    bourgainA6RescaledMoment_subpower_of_A6 hA6 hε
  refine ⟨C, hC, ?_⟩
  intro H hH δ Δ hδ hΔ
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  have hHne : (H : ℝ) ≠ 0 := hHr.ne'
  have hHsqne : (H : ℝ) ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hHne
  have hscale3 : 1 ≤ δ * (H : ℝ) ^ (2 : ℕ) := by
    calc
      (1 : ℝ) =
          (1 / (H : ℝ) ^ (2 : ℕ)) * (H : ℝ) ^ (2 : ℕ) := by
            field_simp
      _ ≤ δ * (H : ℝ) ^ (2 : ℕ) :=
        mul_le_mul_of_nonneg_right hδ (by positivity)
  have hscale4 : 1 ≤ Δ * (H : ℝ) := by
    calc
      (1 : ℝ) = (1 / (H : ℝ)) * (H : ℝ) := by
        field_simp
      _ ≤ Δ * (H : ℝ) :=
        mul_le_mul_of_nonneg_right hΔ hHr.le
  unfold bourgainA6FirstSpacingMoment
  refine (hbound H hscale3 hscale4).trans_eq ?_
  ring

end

end RHTower
