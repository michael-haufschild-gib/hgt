import GaloisForLFunctions.RHTower.ChiDualMaskedCompactEnvelope

/-!
# Common compact profile of the retained physical dual background

The full spatial-profile majorant already controls every compact-disc point at
the same height. Integrate its complete endpoint transition bands and combine it
with the actual prime-mask envelope. Exact finite subtraction gives one measurable
retained-background envelope with the complete logarithmic cofactor budget.
-/

open Complex Set Filter Topology MeasureTheory
open scoped BigOperators ENNReal
noncomputable section
namespace RHTower

private theorem integrable_chiDualSpatialBand (b h M : ℝ) :
    Integrable ((chiDualSpatialBand b h).indicator (fun _ => M ^ 2)) volume := by
  exact (integrableOn_const (by simp [chiDualSpatialBand]) :
    IntegrableOn (fun _ : ℝ => M ^ 2) (chiDualSpatialBand b h) volume).integrable_indicator measurableSet_Icc

private theorem integral_chiDualSpatialBand_le (b : ℝ) {h : ℝ} (hh : 0 ≤ h) (M N : ℝ) :
    (∫ t in Icc N (2 * N), (chiDualSpatialBand b h).indicator (fun _ => M ^ 2) t) ≤
      4 * Real.pi * h * M ^ 2 := by
  have hi := integrable_chiDualSpatialBand b h M
  have hb := setIntegral_le_integral (s := Icc N (2 * N)) hi
    (Filter.Eventually.of_forall (fun t => Set.indicator_nonneg (fun _ _ => sq_nonneg M) t))
  apply hb.trans_eq
  rw [integral_indicator_const (μ := volume) (s := chiDualSpatialBand b h)
    (M ^ 2) (show MeasurableSet (chiDualSpatialBand b h) from measurableSet_Icc)]
  have hab : 2 * Real.pi * (b - h) ≤ 2 * Real.pi * (b + h) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith only [hh]
  rw [show chiDualSpatialBand b h = Icc (2 * Real.pi * (b - h)) (2 * Real.pi * (b + h)) from rfl,
    Real.volume_real_Icc_of_le hab, smul_eq_mul]
  ring


/-- One measurable physical envelope controls the full spatial-profile error
at every point of the compact disc, including both complete transition bands. -/
theorem exists_chiDual_integer_block_common_profile_envelope
    (c : ℂ) {r : ℝ} (hr : 0 ≤ r) (hc0 : 1 / 2 ≤ c.re - r) (hc1 : c.re + r < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ m : ℕ in atTop,
      ∀ A B : ℕ, (m : ℝ) ^ 10 / 5 ≤ A → (B : ℝ) ≤ 6 * (m : ℝ) ^ 10 / 25 → A ≤ B →
      ∃ G : ℝ → ℝ≥0∞, Measurable G ∧
        (∀ t ∈ Icc ((m : ℝ) ^ 10) (2 * (m : ℝ) ^ 10), ∀ s ∈ Metric.closedBall c r,
          ENNReal.ofReal (‖chiDualIntegerBlock s ((m : ℝ) ^ 10) A B t -
            chiDualSpatialStepProfile ((m : ℝ) ^ 10) A B t‖ ^ 2) ≤ G t) ∧
        (∫⁻ t in Icc ((m : ℝ) ^ 10) (2 * (m : ℝ) ^ 10), G t) ≤
          ENNReal.ofReal (C * (m : ℝ) ^ 10 / (m : ℝ) ^ 2) := by
  obtain ⟨E, M, hE, hM, hmajor⟩ := exists_chiDual_integer_block_profile_majorant c hr hc0 hc1
  refine ⟨E ^ 2 + 8 * Real.pi * M ^ 2, by positivity, ?_⟩
  filter_upwards [hmajor, eventually_ge_atTop (1 : ℕ)] with m hmajor hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith only [hm1]
  have hN0 : (0 : ℝ) < (m : ℝ) ^ 10 := by positivity
  intro A B hA hB hAB
  let J₀ : ℝ → ℝ := (chiDualSpatialBand ((A : ℝ) - 1 / 2) ((m : ℝ) ^ 6)).indicator (fun _ => M ^ 2)
  let J₁ : ℝ → ℝ := (chiDualSpatialBand ((B : ℝ) + 1 / 2) ((m : ℝ) ^ 6)).indicator (fun _ => M ^ 2)
  let G : ℝ → ℝ := fun t => (E / m) ^ 2 + J₀ t + J₁ t
  let W := Icc ((m : ℝ) ^ 10) (2 * (m : ℝ) ^ 10)
  have hJ₀ : Integrable J₀ volume := integrable_chiDualSpatialBand _ _ M
  have hJ₁ : Integrable J₁ volume := integrable_chiDualSpatialBand _ _ M
  have hc : IntegrableOn (fun _ : ℝ => (E / m) ^ 2) W volume := integrableOn_const (by simp [W])
  have hG : IntegrableOn G W volume := Integrable.fun_add
    (Integrable.fun_add hc hJ₀.integrableOn) hJ₁.integrableOn
  have hJ₀m : Measurable J₀ := measurable_const.indicator measurableSet_Icc
  have hJ₁m : Measurable J₁ := measurable_const.indicator measurableSet_Icc
  have hGm : Measurable G := (measurable_const.add hJ₀m).add hJ₁m
  have hG0 (t : ℝ) : 0 ≤ G t := by
    exact add_nonneg (add_nonneg (sq_nonneg _) (Set.indicator_nonneg (fun _ _ => sq_nonneg M) t))
      (Set.indicator_nonneg (fun _ _ => sq_nonneg M) t)
  refine ⟨fun t => ENNReal.ofReal (G t), hGm.ennreal_ofReal, ?_, ?_⟩
  · intro t ht s hs
    exact ENNReal.ofReal_le_ofReal (hmajor s hs A B hA hB hAB t ht)
  · rw [← ofReal_integral_eq_lintegral_ofReal hG (Filter.Eventually.of_forall hG0)]
    apply ENNReal.ofReal_le_ofReal
    have hsum : (∫ t in W, G t) ≤
        (E / m) ^ 2 * (m : ℝ) ^ 10 + 8 * Real.pi * (m : ℝ) ^ 6 * M ^ 2 := by
      have hsplit : (∫ t in W, G t) =
          ((∫ t in W, (E / m) ^ 2) + ∫ t in W, J₀ t) + ∫ t in W, J₁ t := by
        calc
          _ = (∫ t in W, (E / m) ^ 2 + J₀ t) + ∫ t in W, J₁ t :=
            integral_add (Integrable.fun_add hc hJ₀.integrableOn) hJ₁.integrableOn
          _ = _ := congrArg (fun x : ℝ => x + ∫ t in W, J₁ t)
            (integral_add hc hJ₀.integrableOn)
      rw [hsplit, setIntegral_const]
      change ((volume.real (Icc ((m : ℝ) ^ 10) (2 * (m : ℝ) ^ 10))) • (E / m) ^ 2 +
        ∫ t in W, J₀ t) + ∫ t in W, J₁ t ≤ _
      rw [Real.volume_real_Icc_of_le (by linarith only [hN0]), smul_eq_mul]
      have hj0 := integral_chiDualSpatialBand_le ((A : ℝ) - 1 / 2)
        (by positivity : (0 : ℝ) ≤ (m : ℝ) ^ 6) M ((m : ℝ) ^ 10)
      have hj1 := integral_chiDualSpatialBand_le ((B : ℝ) + 1 / 2)
        (by positivity : (0 : ℝ) ≤ (m : ℝ) ^ 6) M ((m : ℝ) ^ 10)
      change (2 * (m : ℝ) ^ 10 - (m : ℝ) ^ 10) * (E / m) ^ 2 +
        (∫ t in W, J₀ t) + (∫ t in W, J₁ t) ≤ _
      linarith only [hj0, hj1]
    have hpow : (m : ℝ) ^ 2 ≤ (m : ℝ) ^ 4 := by
      have h2 : (1 : ℝ) ≤ (m : ℝ) ^ 2 := one_le_pow₀ hm1
      nlinarith only [mul_nonneg (sub_nonneg.mpr h2) (sq_nonneg (m : ℝ))]
    have hb : (∫ t in W, G t) / (m : ℝ) ^ 10 ≤
        (E ^ 2 + 8 * Real.pi * M ^ 2) / (m : ℝ) ^ 2 := by
      apply (div_le_div_of_nonneg_right hsum hN0.le).trans
      calc
        _ = E ^ 2 / (m : ℝ) ^ 2 + (8 * Real.pi * M ^ 2) / (m : ℝ) ^ 4 := by field_simp
        _ ≤ E ^ 2 / (m : ℝ) ^ 2 + (8 * Real.pi * M ^ 2) / (m : ℝ) ^ 2 :=
          add_le_add le_rfl (div_le_div_of_nonneg_left (by positivity) (by positivity) hpow)
        _ = _ := by ring
    calc
      _ ≤ ((E ^ 2 + 8 * Real.pi * M ^ 2) / (m : ℝ) ^ 2) * (m : ℝ) ^ 10 :=
        (div_le_iff₀ hN0).mp hb
      _ = _ := by ring

/-- The complete retained dual background has one measurable compact-uniform
profile envelope on the physical height window, paying the full prime mask. -/
theorem exists_chiDual_retained_common_profile_envelope
    (c : ℂ) {r : ℝ} (hr : 0 ≤ r) (hc0 : 1 / 2 ≤ c.re - r) (hc1 : c.re + r < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ m : ℕ in atTop,
      ∀ A B : ℕ, (m : ℝ) ^ 10 / 5 ≤ A → (B : ℝ) ≤ 6 * (m : ℝ) ^ 10 / 25 → A ≤ B →
      ∀ H : ℕ, 1 ≤ H → H ^ 2 ≤ m ^ 10 →
      ∃ G : ℝ → ℝ≥0∞, Measurable G ∧
        (∀ t ∈ Icc ((m : ℝ) ^ 10) (2 * (m : ℝ) ^ 10), ∀ s ∈ Metric.closedBall c r,
          ENNReal.ofReal (‖(∑ n ∈ Finset.Icc A B \ primeWindowSupported (Finset.Icc A B) (m ^ 10) H,
            smoothAFECutoff ((n : ℝ) / (m : ℝ) ^ 10) * zetaChiDualInteriorAtom s n t) -
              chiDualSpatialStepProfile ((m : ℝ) ^ 10) A B t‖ ^ 2) ≤ G t) ∧
        (∫⁻ t in Icc ((m : ℝ) ^ 10) (2 * (m : ℝ) ^ 10), G t) *
          ENNReal.ofReal (Real.log ((m : ℝ) ^ 10)) ≤
          ENNReal.ofReal (C * (m : ℝ) ^ 10 *
            (Real.log ((m : ℝ) ^ 10) / (m : ℝ) ^ 2 + 1 + Real.log H)) := by
  obtain ⟨C₀, hC₀, hfull⟩ := exists_chiDual_integer_block_common_profile_envelope c hr hc0 hc1
  obtain ⟨C₁, hC₁, hmask⟩ := exists_chiDual_prime_mask_common_envelope c hr hc0 hc1
  refine ⟨2 * (C₀ + C₁), by positivity, ?_⟩
  have hp : Tendsto (fun m : ℕ => m ^ 10) atTop atTop := tendsto_pow_atTop (by decide)
  filter_upwards [hfull, hp.eventually hmask, eventually_ge_atTop (2 : ℕ)] with m hfull hmask hm2
  norm_num only [Nat.cast_pow] at hmask
  have hm2R : (2 : ℝ) ≤ m := by exact_mod_cast hm2
  have hm0 : (0 : ℝ) < m := by linarith only [hm2R]
  let N : ℝ := (m : ℝ) ^ 10
  have hN0 : 0 < N := by dsimp only [N]; positivity
  have hN1 : 1 < N := one_lt_pow₀ (by linarith only [hm2R] : (1 : ℝ) < m) (by decide)
  have hlog : 0 < Real.log N := Real.log_pos hN1
  intro A B hA hB hAB H hH hHN
  let S := Finset.Icc A B
  let F := primeWindowSupported S (m ^ 10) H
  let W := Icc N (2 * N)
  have hgeom (n : ℕ) (hn : n ∈ S) : (m : ℝ) ^ 10 / 5 ≤ n ∧ (n : ℝ) ≤ 6 * (m : ℝ) ^ 10 / 25 := by
    obtain ⟨hnA, hnB⟩ := Finset.mem_Icc.mp hn
    have hlo : (A : ℝ) ≤ n := by exact_mod_cast hnA
    have hhi : (n : ℝ) ≤ B := by exact_mod_cast hnB
    exact ⟨hA.trans hlo, hhi.trans hB⟩
  obtain ⟨G₀, hG₀m, hG₀point, hG₀mean⟩ := hfull A B hA hB hAB
  obtain ⟨G₁, hG₁m, hG₁point, hG₁mean⟩ := hmask S hgeom H hH hHN
  let G : ℝ → ℝ≥0∞ := fun t => 2 * G₀ t + 2 * G₁ t
  refine ⟨G, (hG₀m.const_mul 2).add (hG₁m.const_mul 2), ?_, ?_⟩
  · intro t ht s hs
    let X := chiDualIntegerBlock s N A B t - chiDualSpatialStepProfile N A B t
    let Y := ∑ n ∈ F, smoothAFECutoff ((n : ℝ) / N) * zetaChiDualInteriorAtom s n t
    have hsum : (∑ n ∈ S \ F, smoothAFECutoff ((n : ℝ) / N) * zetaChiDualInteriorAtom s n t) + Y =
        chiDualIntegerBlock s N A B t := Finset.sum_sdiff (Finset.filter_subset _ _)
    have heq : (∑ n ∈ S \ F, smoothAFECutoff ((n : ℝ) / N) * zetaChiDualInteriorAtom s n t) -
        chiDualSpatialStepProfile N A B t = X - Y := by
      dsimp only [X]
      rw [← hsum]
      ring
    have hb : ‖X - Y‖ ^ 2 ≤ 2 * ‖X‖ ^ 2 + 2 * ‖Y‖ ^ 2 := by
      have hn := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le X Y) 2
      nlinarith only [hn, sq_nonneg (‖X‖ - ‖Y‖)]
    change ENNReal.ofReal (‖(∑ n ∈ S \ F, _) - chiDualSpatialStepProfile N A B t‖ ^ 2) ≤ _
    rw [heq]
    calc
      _ ≤ ENNReal.ofReal (2 * ‖X‖ ^ 2 + 2 * ‖Y‖ ^ 2) := ENNReal.ofReal_le_ofReal hb
      _ = 2 * ENNReal.ofReal (‖X‖ ^ 2) + 2 * ENNReal.ofReal (‖Y‖ ^ 2) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
      _ ≤ G t := add_le_add (mul_le_mul_right (hG₀point t ht s hs) 2)
        (mul_le_mul_right (hG₁point t ht s hs) 2)
  · change (∫⁻ t in W, 2 * G₀ t + 2 * G₁ t) * ENNReal.ofReal (Real.log N) ≤ _
    rw [lintegral_add_left (hG₀m.const_mul 2), lintegral_const_mul _ hG₀m,
      lintegral_const_mul _ hG₁m, add_mul, mul_assoc, mul_assoc]
    have h₀ : (∫⁻ t in W, G₀ t) * ENNReal.ofReal (Real.log N) ≤
        ENNReal.ofReal (C₀ * N / (m : ℝ) ^ 2 * Real.log N) := by
      calc
        _ ≤ ENNReal.ofReal (C₀ * N / (m : ℝ) ^ 2) * ENNReal.ofReal (Real.log N) := by gcongr
        _ = _ := (ENNReal.ofReal_mul (by positivity)).symm
    apply (add_le_add (mul_le_mul_right h₀ 2) (mul_le_mul_right hG₁mean 2)).trans
    rw [← show ENNReal.ofReal (2 : ℝ) = 2 by norm_num,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have ha : 0 ≤ Real.log N / (m : ℝ) ^ 2 := div_nonneg hlog.le (sq_nonneg _)
    have hb : 0 ≤ 1 + Real.log H := by linarith only [Real.log_natCast_nonneg H]
    calc
      _ = 2 * N * (C₀ * (Real.log N / (m : ℝ) ^ 2) + C₁ * (1 + Real.log H)) := by ring
      _ ≤ 2 * N * ((C₀ + C₁) * (Real.log N / (m : ℝ) ^ 2) + (C₀ + C₁) * (1 + Real.log H)) :=
        mul_le_mul_of_nonneg_left (add_le_add
          (mul_le_mul_of_nonneg_right (by linarith only [hC₁]) ha)
          (mul_le_mul_of_nonneg_right (by linarith only [hC₀]) hb)) (by positivity)
      _ = _ := by ring

end RHTower
