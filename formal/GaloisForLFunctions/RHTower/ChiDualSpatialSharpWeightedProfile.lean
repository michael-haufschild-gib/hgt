import GaloisForLFunctions.RHTower.ChiDualMaskedMeanSquare

/-!
# Common spatial profiles under arbitrary bounded-frequency resonators

Sharp physical interval energy controls both complete transition bands. The
common profile error therefore pays the largest integer frequency Q, removing
the support-cardinality loss. Reversing the sharp upper interval estimate gives
the actual lower mass, hence normalized compact-uniform error O(m^-2 + Q/N)
on N=m^10 whenever 104Q<=N, for every nonzero coefficient family.
-/

open Complex Set Filter Topology MeasureTheory
open scoped BigOperators ENNReal
noncomputable section
namespace RHTower

private theorem continuous_zetaChiDualResonator_sq (S : Finset ℕ) (c : ℕ → ℂ) :
    Continuous (fun t => ‖zetaChiDualResonator S c t‖ ^ 2) := by
  have hD : Continuous (zetaChiDualResonator S c) := by
    unfold zetaChiDualResonator
    apply continuous_finsetSum
    intro a _
    unfold bourgainOscillation
    fun_prop
  exact hD.norm.pow 2

/-- The sharp lower physical mass bound follows from the same source upper
bound on the reversed interval, retaining every resonator coefficient. -/
theorem integral_zetaChiDualResonator_sq_sharp_ge {Q : ℕ} (hQ : 0 < Q)
    (S : Finset ℕ) (c : ℕ → ℂ) (hS : ∀ n ∈ S, 0 < n ∧ n ≤ Q) (T U : ℝ) :
    (U - 52 * (Q : ℝ)) * ∑ n ∈ S, ‖c n‖ ^ 2 ≤
      (∫ t in T..(T + U), ‖zetaChiDualResonator S c t‖ ^ 2) := by
  have h := integral_zetaChiDualResonator_sq_sharp_le hQ S c hS (T + U) (-U)
  rw [show T + U + -U = T by ring, intervalIntegral.integral_symm] at h
  linarith only [h]

private theorem weighted_spatial_band_bound {Q : ℕ} (hQ : 0 < Q)
    (S : Finset ℕ) (c : ℕ → ℂ) (hS : ∀ n ∈ S, 0 < n ∧ n ≤ Q)
    (b M N : ℝ) {h : ℝ} (hh : 0 ≤ h) :
    Integrable ((chiDualSpatialBand b h).indicator
      (fun t => M ^ 2 * ‖zetaChiDualResonator S c t‖ ^ 2)) volume ∧
    (∫ t in Icc N (2 * N), (chiDualSpatialBand b h).indicator
      (fun t => M ^ 2 * ‖zetaChiDualResonator S c t‖ ^ 2) t) ≤
        M ^ 2 * (4 * Real.pi * h + 52 * Q) * ∑ n ∈ S, ‖c n‖ ^ 2 := by
  have hcont := (continuous_zetaChiDualResonator_sq S c).const_mul (M ^ 2)
  have hi : IntegrableOn (fun t => M ^ 2 * ‖zetaChiDualResonator S c t‖ ^ 2)
      (chiDualSpatialBand b h) volume := hcont.integrableOn_Icc
  have hJ := hi.integrable_indicator (show MeasurableSet (chiDualSpatialBand b h) from measurableSet_Icc)
  refine ⟨hJ, ?_⟩
  have hb := setIntegral_le_integral (s := Icc N (2 * N)) hJ
    (Filter.Eventually.of_forall (fun t => Set.indicator_nonneg (fun _ _ => by positivity) t))
  apply hb.trans
  rw [integral_indicator (show MeasurableSet (chiDualSpatialBand b h) from measurableSet_Icc), integral_const_mul]
  have hab : 2 * Real.pi * (b - h) ≤ 2 * Real.pi * (b + h) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith only [hh]
  have hbound := integral_zetaChiDualResonator_sq_sharp_le hQ S c hS
    (2 * Real.pi * (b - h)) (4 * Real.pi * h)
  rw [show 2 * Real.pi * (b - h) + 4 * Real.pi * h = 2 * Real.pi * (b + h) by ring,
    intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc] at hbound
  exact (mul_le_mul_of_nonneg_left hbound (sq_nonneg M)).trans_eq (by ring)

/-- The common full-block spatial profile survives every physical resonator
with positive integer frequencies at most Q. The error pays Q, not support cardinality. -/
theorem exists_chiDual_integer_block_sharp_weighted_profile_envelope
    (z : ℂ) {r : ℝ} (hr : 0 ≤ r) (hz0 : 1 / 2 ≤ z.re - r) (hz1 : z.re + r < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ m : ℕ in atTop,
      ∀ A B : ℕ, (m : ℝ) ^ 10 / 5 ≤ A → (B : ℝ) ≤ 6 * (m : ℝ) ^ 10 / 25 → A ≤ B →
      ∃ G : ℝ → ℝ, Measurable G ∧ (∀ t, 0 ≤ G t) ∧
        (∀ t ∈ Icc ((m : ℝ) ^ 10) (2 * (m : ℝ) ^ 10), ∀ s ∈ Metric.closedBall z r,
          ‖chiDualIntegerBlock s ((m : ℝ) ^ 10) A B t -
            chiDualSpatialStepProfile ((m : ℝ) ^ 10) A B t‖ ^ 2 ≤ G t) ∧
        ∀ Q : ℕ, 0 < Q → ∀ (S : Finset ℕ) (c : ℕ → ℂ),
          (∀ n ∈ S, 0 < n ∧ n ≤ Q) →
          IntegrableOn (fun t => G t * ‖zetaChiDualResonator S c t‖ ^ 2)
            (Icc ((m : ℝ) ^ 10) (2 * (m : ℝ) ^ 10)) volume ∧
          (∫ t in Icc ((m : ℝ) ^ 10) (2 * (m : ℝ) ^ 10), G t * ‖zetaChiDualResonator S c t‖ ^ 2) ≤
            C * ((m : ℝ) ^ 10 / (m : ℝ) ^ 2 + Q) * ∑ n ∈ S, ‖c n‖ ^ 2 := by
  obtain ⟨E, M, hE, hM, hmajor⟩ := exists_chiDual_integer_block_profile_majorant z hr hz0 hz1
  let C : ℝ := (E ^ 2 + 8 * Real.pi * M ^ 2) + (52 * E ^ 2 + 104 * M ^ 2)
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  filter_upwards [hmajor, eventually_ge_atTop (1 : ℕ)] with m hmajor hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith only [hm1]
  let N : ℝ := (m : ℝ) ^ 10
  have hN0 : 0 < N := by dsimp only [N]; positivity
  intro A B hA hB hAB
  let J₀ : ℝ → ℝ := (chiDualSpatialBand ((A : ℝ) - 1 / 2) ((m : ℝ) ^ 6)).indicator (fun _ => M ^ 2)
  let J₁ : ℝ → ℝ := (chiDualSpatialBand ((B : ℝ) + 1 / 2) ((m : ℝ) ^ 6)).indicator (fun _ => M ^ 2)
  let G : ℝ → ℝ := fun t => (E / m) ^ 2 + J₀ t + J₁ t
  have hJ₀m : Measurable J₀ := measurable_const.indicator measurableSet_Icc
  have hJ₁m : Measurable J₁ := measurable_const.indicator measurableSet_Icc
  refine ⟨G, (measurable_const.add hJ₀m).add hJ₁m, ?_, ?_, ?_⟩
  · intro t
    exact add_nonneg (add_nonneg (sq_nonneg _) (Set.indicator_nonneg (fun _ _ => sq_nonneg M) t))
      (Set.indicator_nonneg (fun _ _ => sq_nonneg M) t)
  · intro t ht s hs
    exact hmajor s hs A B hA hB hAB t ht
  · intro Q hQ S c hS
    let D : ℝ → ℝ := fun t => ‖zetaChiDualResonator S c t‖ ^ 2
    let W := Icc N (2 * N)
    let en : ℝ := ∑ n ∈ S, ‖c n‖ ^ 2
    have hen : 0 ≤ en := by dsimp only [en]; positivity
    have hD : IntegrableOn D W volume := (continuous_zetaChiDualResonator_sq S c).integrableOn_Icc
    have hDmean : (∫ t in W, D t) ≤ (N + 52 * Q) * en := by
      have h := integral_zetaChiDualResonator_sq_sharp_le hQ S c hS N N
      rw [show N + N = 2 * N by ring, intervalIntegral.integral_of_le (by linarith only [hN0]),
        ← integral_Icc_eq_integral_Ioc] at h
      exact h
    have h₀ := weighted_spatial_band_bound hQ S c hS ((A : ℝ) - 1 / 2) M N
      (by positivity : (0 : ℝ) ≤ (m : ℝ) ^ 6)
    have h₁ := weighted_spatial_band_bound hQ S c hS ((B : ℝ) + 1 / 2) M N
      (by positivity : (0 : ℝ) ≤ (m : ℝ) ^ 6)
    have he₀ (t : ℝ) : J₀ t * D t = (chiDualSpatialBand ((A : ℝ) - 1 / 2) ((m : ℝ) ^ 6)).indicator
        (fun t => M ^ 2 * D t) t := by
      exact (Set.indicator_mul_left (i := t) _ (fun _ => M ^ 2) D).symm
    have he₁ (t : ℝ) : J₁ t * D t = (chiDualSpatialBand ((B : ℝ) + 1 / 2) ((m : ℝ) ^ 6)).indicator
        (fun t => M ^ 2 * D t) t := by
      exact (Set.indicator_mul_left (i := t) _ (fun _ => M ^ 2) D).symm
    have hI₀ : IntegrableOn (fun t => J₀ t * D t) W volume := by
      simp_rw [he₀]
      exact h₀.1.integrableOn
    have hI₁ : IntegrableOn (fun t => J₁ t * D t) W volume := by
      simp_rw [he₁]
      exact h₁.1.integrableOn
    have hsplit (t : ℝ) : G t * D t = ((E / m) ^ 2 * D t + J₀ t * D t) + J₁ t * D t := by
      dsimp only [G]; ring
    have hGD : IntegrableOn (fun t => G t * D t) W volume := by
      simp_rw [hsplit]
      exact Integrable.fun_add (Integrable.fun_add (hD.const_mul _) hI₀) hI₁
    refine ⟨hGD, ?_⟩
    have hj₀ : (∫ t in W, J₀ t * D t) ≤ M ^ 2 * (4 * Real.pi * (m : ℝ) ^ 6 + 52 * Q) * en := by
      simp_rw [he₀]; exact h₀.2
    have hj₁ : (∫ t in W, J₁ t * D t) ≤ M ^ 2 * (4 * Real.pi * (m : ℝ) ^ 6 + 52 * Q) * en := by
      simp_rw [he₁]; exact h₁.2
    have hraw : (∫ t in W, G t * D t) ≤
        ((E / m) ^ 2 * (N + 52 * Q) + 2 * M ^ 2 * (4 * Real.pi * (m : ℝ) ^ 6 + 52 * Q)) * en := by
      simp_rw [hsplit]
      rw [integral_add (Integrable.fun_add (hD.const_mul _) hI₀) hI₁,
        integral_add (hD.const_mul _) hI₀, integral_const_mul]
      have hd := mul_le_mul_of_nonneg_left hDmean (sq_nonneg (E / m))
      linarith only [hd, hj₀, hj₁]
    have hsmall : (E / m) ^ 2 ≤ E ^ 2 := by
      rw [div_pow]
      exact div_le_self (sq_nonneg E) (one_le_pow₀ hm1)
    have hscale : (m : ℝ) ^ 6 ≤ N / (m : ℝ) ^ 2 := by
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < (m : ℝ) ^ 2)).mpr
      change (m : ℝ) ^ 6 * (m : ℝ) ^ 2 ≤ (m : ℝ) ^ 10
      rw [← pow_add]
      exact pow_le_pow_right₀ hm1 (by decide)
    apply hraw.trans
    apply mul_le_mul_of_nonneg_right _ hen
    have b₀ := mul_le_mul_of_nonneg_right hsmall (by positivity : (0 : ℝ) ≤ 52 * Q)
    have b₁ := mul_le_mul_of_nonneg_left hscale (by positivity : 0 ≤ 8 * Real.pi * M ^ 2)
    have hid : (E / m) ^ 2 * N = E ^ 2 * (N / (m : ℝ) ^ 2) := by ring
    calc
      _ ≤ (E ^ 2 + 8 * Real.pi * M ^ 2) * (N / (m : ℝ) ^ 2) +
          (52 * E ^ 2 + 104 * M ^ 2) * Q := by nlinarith only [b₀, b₁, hid]
      _ ≤ C * (N / (m : ℝ) ^ 2) + C * Q :=
        add_le_add (mul_le_mul_of_nonneg_right (by dsimp only [C]; linarith only [sq_nonneg E, sq_nonneg M, mul_nonneg Real.pi_pos.le (sq_nonneg M)]) (by positivity))
          (mul_le_mul_of_nonneg_right (by dsimp only [C]; linarith only [sq_nonneg E, sq_nonneg M, mul_nonneg Real.pi_pos.le (sq_nonneg M)]) (by positivity))
      _ = _ := by ring

/-- Normalize by the actual positive physical mass. Every finite positive
frequency support below N/104 is admitted, with no cardinality loss and one
common profile envelope for the whole compact disc. -/
theorem exists_chiDual_integer_block_sharp_normalized_profile_envelope
    (z : ℂ) {r : ℝ} (hr : 0 ≤ r) (hz0 : 1 / 2 ≤ z.re - r) (hz1 : z.re + r < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ m : ℕ in atTop,
      ∀ A B : ℕ, (m : ℝ) ^ 10 / 5 ≤ A → (B : ℝ) ≤ 6 * (m : ℝ) ^ 10 / 25 → A ≤ B →
      ∃ G : ℝ → ℝ, Measurable G ∧ (∀ t, 0 ≤ G t) ∧
        (∀ t ∈ Icc ((m : ℝ) ^ 10) (2 * (m : ℝ) ^ 10), ∀ s ∈ Metric.closedBall z r,
          ‖chiDualIntegerBlock s ((m : ℝ) ^ 10) A B t -
            chiDualSpatialStepProfile ((m : ℝ) ^ 10) A B t‖ ^ 2 ≤ G t) ∧
        ∀ Q : ℕ, 0 < Q → 104 * (Q : ℝ) ≤ (m : ℝ) ^ 10 →
          ∀ (S : Finset ℕ) (c : ℕ → ℂ), (∀ n ∈ S, 0 < n ∧ n ≤ Q) →
          0 < (∑ n ∈ S, ‖c n‖ ^ 2) →
          IntegrableOn (fun t => G t * ‖zetaChiDualResonator S c t‖ ^ 2)
            (Icc ((m : ℝ) ^ 10) (2 * (m : ℝ) ^ 10)) volume ∧
          0 < (∫ t in Icc ((m : ℝ) ^ 10) (2 * (m : ℝ) ^ 10), ‖zetaChiDualResonator S c t‖ ^ 2) ∧
          (∫ t in Icc ((m : ℝ) ^ 10) (2 * (m : ℝ) ^ 10), G t * ‖zetaChiDualResonator S c t‖ ^ 2) /
            (∫ t in Icc ((m : ℝ) ^ 10) (2 * (m : ℝ) ^ 10), ‖zetaChiDualResonator S c t‖ ^ 2) ≤
            C * (1 / (m : ℝ) ^ 2 + (Q : ℝ) / (m : ℝ) ^ 10) := by
  obtain ⟨C, hC, henv⟩ := exists_chiDual_integer_block_sharp_weighted_profile_envelope z hr hz0 hz1
  refine ⟨2 * C, by positivity, ?_⟩
  filter_upwards [henv, eventually_ge_atTop (1 : ℕ)] with m henv hm
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  let N : ℝ := (m : ℝ) ^ 10
  have hN0 : 0 < N := by dsimp only [N]; positivity
  intro A B hA hB hAB
  obtain ⟨G, hGm, hG0, hGpoint, hGmean⟩ := henv A B hA hB hAB
  refine ⟨G, hGm, hG0, hGpoint, ?_⟩
  intro Q hQ hQN S c hS hen
  obtain ⟨hGi, hGiBound⟩ := hGmean Q hQ S c hS
  let W := Icc N (2 * N)
  let mass : ℝ := ∫ t in W, ‖zetaChiDualResonator S c t‖ ^ 2
  let en : ℝ := ∑ n ∈ S, ‖c n‖ ^ 2
  have hlo : (N - 52 * Q) * en ≤ mass := by
    have hb := integral_zetaChiDualResonator_sq_sharp_ge hQ S c hS N N
    rw [show N + N = 2 * N by ring, intervalIntegral.integral_of_le (by linarith only [hN0]),
      ← integral_Icc_eq_integral_Ioc] at hb
    exact hb
  have hmass : N / 2 * en ≤ mass :=
    (mul_le_mul_of_nonneg_right (by linarith only [hQN] : N / 2 ≤ N - 52 * Q) hen.le).trans hlo
  have hmass0 : 0 < mass := lt_of_lt_of_le (mul_pos (half_pos hN0) hen) hmass
  refine ⟨hGi, hmass0, ?_⟩
  change (∫ t in W, G t * ‖zetaChiDualResonator S c t‖ ^ 2) / mass ≤
    2 * C * (1 / (m : ℝ) ^ 2 + Q / N)
  apply (div_le_iff₀ hmass0).mpr
  calc
    _ ≤ C * (N / (m : ℝ) ^ 2 + Q) * en := hGiBound
    _ = (2 * C * (1 / (m : ℝ) ^ 2 + Q / N)) * (N / 2 * en) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hmass (by positivity)

end RHTower
