import GaloisForLFunctions.RHTower.ZetaNotchRampMainTerm

/-!
# Localizing the refined notch error

Only the square-root mass up to `2 * c * L` enters the central Gaussian
window. Outside that window the entire finite mass has an exponentially
small coefficient. This permits scale selection without a global
square-root mass envelope.
-/

noncomputable section
open Set Filter MeasureTheory

namespace RHTower.WeilSingularArithmetic
open WeilAbscissa ZetaNotch

private theorem log_div_sqrt_middle {L u : ℝ} (hL : 32 ≤ L)
    (hu : L / 2 ≤ u) (huL : u ≤ 2 * L) :
    Real.log u / Real.sqrt u ≤ 4 * Real.log L / Real.sqrt L := by
  have hL0 : 0 < L := by linarith
  have hu0 : 0 < u := by linarith
  have hsL := Real.sqrt_pos.mpr hL0
  have hsu := Real.sqrt_pos.mpr hu0
  have hlog : Real.log u ≤ 2 * Real.log L := by
    have h := Real.log_le_log hu0 (show u ≤ L * L by nlinarith)
    rwa [Real.log_mul hL0.ne' hL0.ne', ← two_mul] at h
  have hs : Real.sqrt L ≤ 2 * Real.sqrt u := by
    have h1 := Real.sq_sqrt hL0.le
    have h2 := Real.sq_sqrt hu0.le
    nlinarith
  have hl0 : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  calc
    Real.log u / Real.sqrt u ≤ (2 * Real.log L) / Real.sqrt u :=
      div_le_div_of_nonneg_right hlog hsu.le
    _ ≤ 4 * Real.log L / Real.sqrt L := by
      apply (div_le_div_iff₀ hsu hsL).mpr
      have h := mul_le_mul_of_nonneg_left hs (show 0 ≤ 2 * Real.log L by positivity)
      linarith

private theorem scaleWeight_far {L u : ℝ} (hL : 32 ≤ L)
    (hu : u < L / 2 ∨ 2 * L < u) :
    scaleWeight L u ≤ Real.exp (-(L ^ 2 / 8)) * Real.exp (-((u - L) ^ 2 / 2)) := by
  have hs : L ^ 2 / 4 ≤ (u - L) ^ 2 := by
    rcases hu with h | h
    · nlinarith [sq_nonneg (u - L / 2)]
    · nlinarith [sq_nonneg (u - 2 * L)]
  rw [scaleWeight, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith

/-- Gaussian localization of a nonnegative finite mass profile. -/
theorem scaleWeight_log_mass_le {L u B T C : ℝ} (hL : 32 ≤ L) (hu : 16 < u)
    (hB : 0 ≤ B) (hBT : B ≤ T) (hC : 0 ≤ C)
    (hBC : L / 2 ≤ u → u ≤ 2 * L → B ≤ C) :
    scaleWeight L u * (Real.log u / Real.sqrt u) * B ≤
      (4 * Real.log L / Real.sqrt L * C + 2 * Real.exp (-(L ^ 2 / 8)) * T) *
        Real.exp (-((u - L) ^ 2 / 2)) := by
  have hL0 : 0 < L := by linarith
  have hu0 : 0 < u := by linarith
  have hl0 : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  have hT : 0 ≤ T := hB.trans hBT
  have hG : 0 ≤ Real.exp (-((u - L) ^ 2 / 2)) := (Real.exp_pos _).le
  have hw : 0 ≤ scaleWeight L u := (scaleWeight_pos L u).le
  have hlogu : 0 ≤ Real.log u / Real.sqrt u := by
    exact div_nonneg (Real.log_nonneg (by linarith)) (Real.sqrt_nonneg _)
  by_cases hmid : L / 2 ≤ u ∧ u ≤ 2 * L
  · have h1 := mul_le_mul (scaleWeight_le_half L u)
      (log_div_sqrt_middle hL hmid.1 hmid.2) hlogu hG
    have h2 := mul_le_mul h1 (hBC hmid.1 hmid.2) hB
      (mul_nonneg hG (by positivity))
    calc
      scaleWeight L u * (Real.log u / Real.sqrt u) * B ≤
          (Real.exp (-((u - L) ^ 2 / 2)) * (4 * Real.log L / Real.sqrt L)) * C := h2
      _ ≤ _ := by
        have := mul_nonneg (mul_nonneg (show 0 ≤ 2 * Real.exp (-(L ^ 2 / 8)) by positivity) hT) hG
        nlinarith
  · have hfar : u < L / 2 ∨ 2 * L < u := by
      by_cases h : L / 2 ≤ u
      · exact Or.inr (lt_of_not_ge fun h' => hmid ⟨h, h'⟩)
      · exact Or.inl (lt_of_not_ge h)
    have hlog : Real.log u / Real.sqrt u ≤ 2 := by
      simpa only [div_eq_mul_inv] using log_div_sqrt_le (show 1 ≤ u by linarith)
    have h1 := mul_le_mul (scaleWeight_far hL hfar) hlog hlogu
      (mul_nonneg (Real.exp_pos _).le hG)
    have h2 := mul_le_mul h1 hBT hB (by positivity)
    calc
      scaleWeight L u * (Real.log u / Real.sqrt u) * B ≤
          (Real.exp (-(L ^ 2 / 8)) * Real.exp (-((u - L) ^ 2 / 2)) * 2) * T := h2
      _ ≤ _ := by
        have := mul_nonneg (show 0 ≤ 4 * Real.log L / Real.sqrt L * C by positivity) hG
        nlinarith

/-- The refined error uses only one local square-root mass bound. -/
theorem scaleWeight_refErrSum_local_le {L u : ℝ} (hL : 32 ≤ L) (hu : 16 < u)
    {v : ℕ → ℝ} {F : Finset ℕ} {c S C T CU : ℝ} {K : ℕ}
    (hc : 0 ≤ c) (hC : 0 ≤ C) (hCU : 0 ≤ CU)
    (hS : ∑ n ∈ F, |v n| * (Real.sqrt n)⁻¹ ≤ S)
    (hlocal : ∑ n ∈ F, |v n| * (if (n : ℝ) ≤ 2 * c * L then 1 else 0) ≤ C)
    (hT : ∑ n ∈ F, |v n| ≤ T)
    (hU : ∀ u : ℝ, 16 ≤ u →
      u ^ (5 / 2 : ℝ) * dualTailFactor u K + u ^ 2 * Real.exp (-(u ^ 2) / 32) ≤
        CU * (u * (u ^ (4 + 1))⁻¹)) :
    scaleWeight L u / u * refErrSum v F c K u ≤
      (S + 4 * Real.log L / Real.sqrt L * C +
        (2 * Real.exp (-(L ^ 2 / 8)) + 133 * CU / (1 + L)) * T) *
          Real.exp (-((u - L) ^ 2 / 2)) := by
  let W₁ := ∑ n ∈ F, |v n| * (Real.sqrt n)⁻¹
  let W₂ := ∑ n ∈ F, |v n| * (if (n : ℝ) ≤ c * u then 1 else 0)
  let W₃ := ∑ n ∈ F, |v n|
  let Uu := u ^ (5 / 2 : ℝ) * dualTailFactor u K + u ^ 2 * Real.exp (-(u ^ 2) / 32)
  let G := Real.exp (-((u - L) ^ 2 / 2))
  have hu0 : 0 < u := by linarith
  have hG : 0 ≤ G := (Real.exp_pos _).le
  have hw : 0 ≤ scaleWeight L u := (scaleWeight_pos L u).le
  have hW₁ : 0 ≤ W₁ := Finset.sum_nonneg fun n _ => by positivity
  have hW₂ : 0 ≤ W₂ := Finset.sum_nonneg fun n _ => by split_ifs <;> positivity
  have hW₃ : 0 ≤ W₃ := Finset.sum_nonneg fun n _ => abs_nonneg _
  have hT0 : 0 ≤ T := hW₃.trans hT
  have hW₂T : W₂ ≤ T := by
    apply le_trans (Finset.sum_le_sum fun n _ => ?_) hT
    split_ifs
    · exact le_of_eq (mul_one _)
    · simpa only [mul_zero] using abs_nonneg (v n)
  have hW₂C (_ : L / 2 ≤ u) (huL : u ≤ 2 * L) : W₂ ≤ C := by
    apply le_trans (Finset.sum_le_sum fun n _ => ?_) hlocal
    by_cases hn : (n : ℝ) ≤ c * u
    · have hn' : (n : ℝ) ≤ 2 * c * L := by
        have := mul_le_mul_of_nonneg_left huL hc
        nlinarith
      simp only [if_pos hn, if_pos hn', le_refl]
    · rw [if_neg hn, mul_zero]
      split_ifs <;> positivity
  have hsum : refErrSum v F c K u = u * W₁ + (Real.sqrt u * Real.log u) * W₂ + Uu * W₃ := by
    dsimp [refErrSum, W₁, W₂, W₃]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    dsimp [refWeight, Uu]
    ring
  have hfirst : scaleWeight L u / u * (u * W₁) ≤ S * G := by
    calc
      scaleWeight L u / u * (u * W₁) = scaleWeight L u * W₁ := by field_simp
      _ ≤ G * S := mul_le_mul (scaleWeight_le_half L u) hS hW₁ hG
      _ = S * G := mul_comm _ _
  have hsecond : scaleWeight L u / u * ((Real.sqrt u * Real.log u) * W₂) ≤
      (4 * Real.log L / Real.sqrt L * C + 2 * Real.exp (-(L ^ 2 / 8)) * T) * G := by
    have hs := Real.sq_sqrt hu0.le
    have hs0 := (Real.sqrt_pos.mpr hu0).ne'
    have he : scaleWeight L u / u * ((Real.sqrt u * Real.log u) * W₂) =
        scaleWeight L u * (Real.log u / Real.sqrt u) * W₂ := by
      field_simp [hu0.ne', hs0]
      rw [hs]
    rw [he]
    exact scaleWeight_log_mass_le hL hu hW₂ hW₂T hC hW₂C
  have hthird : scaleWeight L u / u * (Uu * W₃) ≤
      133 * CU * (T / (1 + L)) * G := by
    have hpoly := scaleWeight_mul_inv_pow_le (show (2 : ℝ) ≤ L by linarith) 4 hu
    obtain ⟨hsm, -⟩ := inv_one_add_bounds hL
    have hUb : scaleWeight L u / u * Uu ≤ CU * (133 / (1 + L)) * G := by
      calc
        scaleWeight L u / u * Uu ≤ scaleWeight L u / u * (CU * (u * (u ^ (4 + 1))⁻¹)) :=
          mul_le_mul_of_nonneg_left (hU u hu.le) (div_nonneg hw hu0.le)
        _ = CU * (scaleWeight L u * (u ^ (4 + 1))⁻¹) := by field_simp
        _ ≤ CU * ((((L / 2) ^ (4 + 1))⁻¹ + Real.exp (-(L ^ 2 / 8))) * G) :=
          mul_le_mul_of_nonneg_left hpoly hCU
        _ ≤ CU * (133 / (1 + L) * G) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ hG) hCU
          have := Real.exp_pos (-(L ^ 2 / 256))
          linarith
        _ = CU * (133 / (1 + L)) * G := by ring
    calc
      scaleWeight L u / u * (Uu * W₃) = (scaleWeight L u / u * Uu) * W₃ := by ring
      _ ≤ (CU * (133 / (1 + L)) * G) * T := mul_le_mul hUb hT hW₃ (by positivity)
      _ = 133 * CU * (T / (1 + L)) * G := by ring
  rw [hsum, mul_add, mul_add]
  apply (add_le_add (add_le_add hfirst hsecond) hthird).trans_eq
  dsimp [G]
  ring

/-- Integrated localization retains the single near-scale mass `C`. -/
theorem setIntegral_refErrSum_local_le {L : ℝ} (hL : 32 ≤ L)
    {v : ℕ → ℝ} {F : Finset ℕ} {c S C T CU : ℝ} {K : ℕ}
    (hc : 0 ≤ c) (hC : 0 ≤ C) (hCU : 0 ≤ CU)
    (hS : ∑ n ∈ F, |v n| * (Real.sqrt n)⁻¹ ≤ S)
    (hlocal : ∑ n ∈ F, |v n| * (if (n : ℝ) ≤ 2 * c * L then 1 else 0) ≤ C)
    (hT : ∑ n ∈ F, |v n| ≤ T)
    (hU : ∀ u : ℝ, 16 ≤ u →
      u ^ (5 / 2 : ℝ) * dualTailFactor u K + u ^ 2 * Real.exp (-(u ^ 2) / 32) ≤
        CU * (u * (u ^ (4 + 1))⁻¹)) :
    IntegrableOn (fun u => scaleWeight L u / u * refErrSum v F c K u) (Ioi 16) ∧
      (∫ u in Ioi 16, scaleWeight L u / u * refErrSum v F c K u) ≤
        (S + 4 * Real.log L / Real.sqrt L * C +
          (2 * Real.exp (-(L ^ 2 / 8)) + 133 * CU / (1 + L)) * T) * gaussHalf := by
  let E := S + 4 * Real.log L / Real.sqrt L * C +
    (2 * Real.exp (-(L ^ 2 / 8)) + 133 * CU / (1 + L)) * T
  have hpt (u : ℝ) (hu : u ∈ Ioi (16 : ℝ)) :
      scaleWeight L u / u * refErrSum v F c K u ≤ E * Real.exp (-((u - L) ^ 2 / 2)) :=
    scaleWeight_refErrSum_local_le hL hu hc hC hCU hS hlocal hT hU
  have hnn (u : ℝ) (hu : u ∈ Ioi (16 : ℝ)) :
      0 ≤ scaleWeight L u / u * refErrSum v F c K u := by
    have hu16 : 16 < u := hu
    apply mul_nonneg (div_nonneg (scaleWeight_pos L u).le (by linarith))
    exact Finset.sum_nonneg fun n _ =>
      mul_nonneg (abs_nonneg _) (refWeight_nonneg c K (by linarith) n)
  have hint : IntegrableOn (fun u => scaleWeight L u / u * refErrSum v F c K u) (Ioi 16) := by
    refine ((integrable_gaussShift L).const_mul E).integrableOn.mono' ?_ ?_
    · exact (((Real.continuous_exp.comp (by fun_prop)).measurable.div measurable_id).mul
        (measurable_refErrSum v F c K)).aestronglyMeasurable
    · rw [ae_restrict_iff' measurableSet_Ioi]
      refine Eventually.of_forall fun u hu => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (hnn u hu)]
      exact hpt u hu
  refine ⟨hint, ?_⟩
  have hE : 0 ≤ E := by
    have h1 : 0 ≤ ∑ n ∈ F, |v n| * (Real.sqrt n)⁻¹ := Finset.sum_nonneg fun n _ => by positivity
    have h2 : 0 ≤ ∑ n ∈ F, |v n| := Finset.sum_nonneg fun n _ => abs_nonneg _
    have hS0 : 0 ≤ S := h1.trans hS
    have hT0 : 0 ≤ T := h2.trans hT
    have hlog : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
    dsimp [E]
    positivity
  calc
    (∫ u in Ioi 16, scaleWeight L u / u * refErrSum v F c K u) ≤
        ∫ u in Ioi 16, E * Real.exp (-((u - L) ^ 2 / 2)) :=
      setIntegral_mono_on hint ((integrable_gaussShift L).const_mul E).integrableOn
        measurableSet_Ioi hpt
    _ = E * ∫ u in Ioi 16, Real.exp (-((u - L) ^ 2 / 2)) := integral_const_mul _ _
    _ ≤ E * gaussHalf := by
      apply mul_le_mul_of_nonneg_left _ hE
      rw [← integral_gaussShift L]
      exact setIntegral_le_integral (integrable_gaussShift L)
        (Eventually.of_forall fun _ => (Real.exp_pos _).le)

end RHTower.WeilSingularArithmetic
