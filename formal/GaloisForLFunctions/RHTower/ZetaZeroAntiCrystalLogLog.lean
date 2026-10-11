import GaloisForLFunctions.RHTower.ZetaZeroAntiCrystalWindow
import GaloisForLFunctions.RHTower.MontgomeryPairCorrelationShortLength

/-!
# The anti-crystal law at depth `C / log log T`

For a scale `h > 0` put `c₂(h) = 4w e^{4w/h}` (upper normalized gap bound), `α(h) = min(π/(4c₂), 1/8)`,
`δ(h) = min(α e^{−2/h}/128, π/2)` and the block constant
`B(h) = 1 + 8/(2 sin(δ/2)) + 512 α c₂²/(h (2 sin(δ/2))²)`.

* `norm_lorentzZeroSumAll_le_of_rigidWindow`: an `h`-rigid window `[T^{1/2}, T³]` bounds the Lorentzian
  zero sum at `x = T^{α(h)}` by `B(h) + 1` on `[T^{3/4}, T]`, under explicit size conditions on `T`.
-/

open Complex Filter Topology Set Finset MeasureTheory

namespace RHTower

noncomputable section

/-- Upper normalized gap constant `4w e^{4w/h}`. -/
def acGapUpper (w h : ℝ) : ℝ := 4 * w * Real.exp (4 * w / h)

/-- The phase scale `α(h) = min(π/(4c₂(h)), 1/8)`. -/
def acAlpha (w h : ℝ) : ℝ := min (Real.pi / (4 * acGapUpper w h)) (1 / 8)

/-- The phase margin `δ(h) = min(α(h) e^{−2/h}/128, π/2)`. -/
def acDelta (w h : ℝ) : ℝ := min (acAlpha w h * (Real.exp (-(2 / h)) / 64) / 2) (Real.pi / 2)

/-- The block constant `B(h)`. -/
def acBlock (w h : ℝ) : ℝ := 1 + 8 / (2 * Real.sin (acDelta w h / 2)) +
  512 * acAlpha w h * acGapUpper w h ^ 2 / (h * (2 * Real.sin (acDelta w h / 2)) ^ 2)

/-- **The rigid Lorentzian sum bound with explicit constants.** -/
theorem norm_lorentzZeroSumAll_le_of_rigidWindow {w₁ w₂ T₂ T₂' : ℝ} (hw₁ : 0 < w₁) (hw₂ : 0 < w₂)
    (hU : ∀ h : ℝ, 0 < h → ∀ n, T₂ ≤ xiOrderedPositiveOrdinate n →
      (∀ k, n ≤ k → xiOrderedPositiveOrdinate k ≤ xiOrderedPositiveOrdinate n + 2 * w₂ →
        RigidAt h k) →
      ordinateGap n * Real.log (xiOrderedPositiveOrdinate n) ≤ 4 * w₂ * Real.exp (4 * w₂ / h))
    (hLo : ∀ h : ℝ, 0 < h → ∀ n, lowerGapThreshold w₁ T₂' h ≤ xiOrderedPositiveOrdinate n →
      (∀ k, n ≤ k → xiOrderedPositiveOrdinate k ≤ xiOrderedPositiveOrdinate n + 2 * w₁ + 2 →
        RigidAt h k) →
      Real.exp (-(2 / h)) / 64 ≤ ordinateGap n * Real.log (xiOrderedPositiveOrdinate n))
    {h T : ℝ} (hh : 0 < h)
    (hB : max T₂ (lowerGapThreshold w₁ T₂' h) ≤ T ^ (1 / 2 : ℝ))
    (hlogT : max (4 * acGapUpper w₂ h / h) (2 * (xiLineTwoLogDerivConstant + 2)) ≤ Real.log T)
    (hF : 1024 * Real.sqrt (T ^ acAlpha w₂ h) *
      (xiLineTwoLogDerivConstant + Real.log (2 * T ^ 2 + 5)) ≤ T ^ (3 / 4 : ℝ))
    (hT16 : 16 ≤ T) (hTw : 2 * w₁ + 2 * w₂ + 3 ≤ T) (hW : RigidWindow h T) :
    ∀ t ∈ Icc (T ^ (3 / 4 : ℝ)) T, ‖lorentzZeroSumAll (T ^ acAlpha w₂ h) t‖ ≤
      acBlock w₂ h + 1 := by
  classical
  intro t ht
  set c₂ := acGapUpper w₂ h with hc₂def
  have hc₂ : 0 < c₂ := by rw [hc₂def, acGapUpper]; positivity
  set c₁ : ℝ := Real.exp (-(2 / h)) / 64 with hc₁def
  have hc₁ : 0 < c₁ := by positivity
  set α : ℝ := acAlpha w₂ h with hαdef
  have hα0 : 0 < α := lt_min (by positivity) (by norm_num)
  have hα8 : α ≤ 1 / 8 := min_le_right _ _
  have hαc : α * c₂ ≤ Real.pi / 4 := by
    have := min_le_left (Real.pi / (4 * c₂)) (1 / 8)
    calc α * c₂ ≤ Real.pi / (4 * c₂) * c₂ := mul_le_mul_of_nonneg_right this hc₂.le
      _ = Real.pi / 4 := by field_simp
  set δ : ℝ := acDelta w₂ h with hδdef
  have hδ0 : 0 < δ := lt_min (by positivity) (by positivity)
  have hδ2 : δ ≤ Real.pi / 2 := min_le_right _ _
  have hδc : δ ≤ α * c₁ / 2 := min_le_left _ _
  set Cb : ℝ := acBlock w₂ h with hCb
  have hσ0 : 0 < 2 * Real.sin (δ / 2) :=
    GaloisForLFunctions.HTGeometry.two_sin_half_pos hδ0 (hδ2.trans (by linarith [Real.pi_pos]))
  have hCb1 : 1 ≤ Cb := by
    have : 0 ≤ 8 / (2 * Real.sin (δ / 2)) +
        512 * α * c₂ ^ 2 / (h * (2 * Real.sin (δ / 2)) ^ 2) := by positivity
    have e : Cb = 1 + 8 / (2 * Real.sin (δ / 2)) +
        512 * α * c₂ ^ 2 / (h * (2 * Real.sin (δ / 2)) ^ 2) := by rw [hCb, acBlock]
    rw [e]
    linarith
  have hU' : ∀ n, T₂ ≤ xiOrderedPositiveOrdinate n →
      (∀ k, n ≤ k → xiOrderedPositiveOrdinate k ≤ xiOrderedPositiveOrdinate n + 2 * w₂ →
        RigidAt h k) → ordinateGap n * Real.log (xiOrderedPositiveOrdinate n) ≤ c₂ :=
    hU h hh
  have hLo' := hLo h hh
  have hT0 : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hTop₁ : T ^ 2 + 2 * w₁ + 2 ≤ T ^ 3 := by nlinarith
  have hTop₂ : T ^ 2 + 2 * w₂ ≤ T ^ 3 := by nlinarith
  set L := Real.log T with hLdef
  have hL1 : 4 * c₂ / h ≤ L := le_trans (le_max_left _ _) hlogT
  have hL2 : 2 * (xiLineTwoLogDerivConstant + 2) ≤ L := le_trans (le_max_right _ _) hlogT
  have hC := xiLineTwoLogDerivConstant_nonneg
  have hL0 : 0 < L := by linarith
  have hx1 : 1 ≤ T ^ α := Real.one_le_rpow hT1 hα0.le
  have hlogx : Real.log (T ^ α) = α * L := Real.log_rpow hT0 α
  set a := (xiZeroCount (T ^ (1 / 2 : ℝ))).toNat with ha
  set b := (xiZeroCount (T ^ 2)).toNat with hb
  set s := (Finset.Ico a b).image xiOrderedPositiveZeroCopy with hs_def
  have hblockS : ‖∑ q ∈ s, zeroSumTerm (T ^ α) t q‖ ≤ Cb := by
    rw [hs_def, Finset.sum_image xiOrderedPositiveZeroCopy_injective.injOn]
    rcases le_or_gt b a with hba | hab
    · rw [Finset.Ico_eq_empty_of_le hba, Finset.sum_empty, norm_zero]; linarith
    have hbm : b - a = (b - a - 1) + 1 := by omega
    rw [Finset.sum_Ico_eq_sum_range, hbm]
    refine norm_block_le_local hh hα0 hL0 hc₂ hL1 hδ0 hδc hαc hδ2 (by positivity) hlogx a
      (b - a - 1) (fun n hn1 hn2 => ?_) ?_
    · have hin := (mem_Ico_toNat_iff (B := T ^ (1 / 2 : ℝ)) (T' := T ^ 2) n).mp
        (Finset.mem_Ico.mpr ⟨hn1, by omega⟩)
      exact block_gap_facts_window hT1 hLdef hL0 hU' hLo' hB hTop₁ hTop₂ hW hin.1 hin.2
    · refine (sum_lorentzWeight_orderedOrdinate_le t a _).trans ?_
      refine (lorentzMass_le_log t).trans ?_
      have ht0 : 0 ≤ t := le_trans (Real.rpow_nonneg hT0.le _) ht.1
      rw [abs_of_nonneg ht0]
      have h4 : Real.log (t + 4) ≤ 1 + L := by
        have h5 : Real.log (t + 4) ≤ Real.log (2 * T) :=
          Real.log_le_log (by linarith) (by linarith [ht.2])
        rw [Real.log_mul (by norm_num) hT0.ne'] at h5
        have := Real.log_two_lt_d9; linarith
      linarith
  have hs : ∀ q, q ∉ s → (q.1 : ℂ).im ≤ T ^ (1 / 2 : ℝ) ∨ T ^ 2 < (q.1 : ℂ).im := by
    intro q hq
    by_contra hcon
    push Not at hcon
    obtain ⟨hlo, hhi⟩ := hcon
    have hBpos : 0 < T ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hT0 _
    obtain ⟨n, hn⟩ := exists_xiOrderedPositiveZeroCopy_eq (q := q) (by linarith)
    have hγn : xiOrderedPositiveOrdinate n = (q.1 : ℂ).im := by
      rw [← hn, xiOrderedPositiveZeroCopy_im_eq]
    apply hq
    rw [hs_def, Finset.mem_image]
    exact ⟨n, (mem_Ico_toNat_iff (B := T ^ (1 / 2 : ℝ)) (T' := T ^ 2) n).mpr
      ⟨by rw [hγn]; exact hlo, by rw [hγn]; exact hhi⟩, hn⟩
  have hBt : T ^ (1 / 2 : ℝ) ≤ t :=
    le_trans (Real.rpow_le_rpow_of_exponent_le hT1 (by norm_num)) ht.1
  have hrest := norm_tsum_compl_zeroSumTerm_le hx1 s hs hBt (show t ≤ T ^ 2 by nlinarith [ht.2])
  have htails := tailMasses_le hT16 ht.1 ht.2
  have hQ0 : 0 < T ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos hT0 _
  have hrest1 : ‖∑' q : ↑((s : Set XiZeroCopy)ᶜ), zeroSumTerm (T ^ α) t q‖ ≤ 1 := by
    refine hrest.trans ?_
    calc 16 * Real.sqrt (T ^ α) * (lorentzMassW (Real.sqrt (1 + (t - T ^ (1 / 2 : ℝ)) ^ 2))
          (T ^ (1 / 2 : ℝ)) + lorentzMassW (Real.sqrt (1 + (T ^ 2 - t) ^ 2)) (T ^ 2))
        ≤ 16 * Real.sqrt (T ^ α) *
          (64 * (xiLineTwoLogDerivConstant + Real.log (2 * T ^ 2 + 5)) / T ^ (3 / 4 : ℝ)) :=
          mul_le_mul_of_nonneg_left htails (by positivity)
      _ = (1024 * Real.sqrt (T ^ α) * (xiLineTwoLogDerivConstant + Real.log (2 * T ^ 2 + 5))) /
            T ^ (3 / 4 : ℝ) := by ring
      _ ≤ 1 := by rw [div_le_one hQ0]; exact hF
  rw [lorentzZeroSumAll, ← (summable_zeroSumTerm hx1 t).sum_add_tsum_compl (s := s)]
  refine (norm_add_le _ _).trans ?_
  linarith



/-- **The Montgomery contradiction with explicit conditions.** A bounded Lorentzian zero sum on
`[T^{3/4}, T]` at `x = T^α` is incompatible with the pair-correlation lower bound. -/
theorem false_of_lorentzZeroSumAll_le {T α C : ℝ} (hT16 : 16 ≤ T) (hα0 : 0 < α)
    (hαL : 1 ≤ α * Real.log T)
    (hMont : 5 / 8 * ((T / 4) * (α * Real.log T)) ≤ Real.pi / 2 *
      (montgomeryForm (zeroWindow T) (fun q : XiZeroCopy => (q.1 : ℂ)) (T ^ α)).re)
    (htr : 131072 * T ^ α * (truncationLog T ^ 2 * (3 * Real.log (1 + T) + 2) + 64) ≤ T / 1024)
    (hlowH : T ^ (3 / 4 : ℝ) * (128 * Real.sqrt (T ^ α) *
      (xiLineTwoLogDerivConstant + Real.log (T + 4))) ^ 2 ≤ 1 / 100 * ((T / 4) * (α * Real.log T)))
    (hC : C ^ 2 * T ≤ 1 / 100 * ((T / 4) * (α * Real.log T)))
    (hS : ∀ t ∈ Icc (T ^ (3 / 4 : ℝ)) T, ‖lorentzZeroSumAll (T ^ α) t‖ ≤ C) : False := by
  have hT0 : 0 < T := by linarith
  set L := Real.log T with hL
  have hx1 : 1 ≤ T ^ α := Real.one_le_rpow (by linarith) hα0.le
  set Q := T ^ (3 / 4 : ℝ) with hQ
  have hQ0 : 0 ≤ Q := Real.rpow_nonneg hT0.le _
  have hQT : Q ≤ T := Real.rpow_le_self_of_one_le (by linarith) (by norm_num)
  have htrunc := integral_normSq_lorentzZeroSumAll_sub_montgomeryForm_le hx1 hT0.le
  have hint := integrableOn_normSq_lorentzZeroSumAll hx1 T
  have hi1 : IntervalIntegrable (fun t => ‖lorentzZeroSumAll (T ^ α) t‖ ^ 2) volume 0 Q :=
    (hint.mono_set (by rw [uIcc_of_le hQ0]; exact Icc_subset_Icc le_rfl hQT)).intervalIntegrable
  have hi2 : IntervalIntegrable (fun t => ‖lorentzZeroSumAll (T ^ α) t‖ ^ 2) volume Q T :=
    (hint.mono_set (by rw [uIcc_of_le hQT]; exact Icc_subset_Icc hQ0 le_rfl)).intervalIntegrable
  have hsplitI : (∫ t in Icc 0 T, ‖lorentzZeroSumAll (T ^ α) t‖ ^ 2) =
      (∫ t in (0 : ℝ)..Q, ‖lorentzZeroSumAll (T ^ α) t‖ ^ 2) +
        ∫ t in Q..T, ‖lorentzZeroSumAll (T ^ α) t‖ ^ 2 := by
    rw [setIntegral_Icc_normSq_lorentzZeroSumAll hT0.le,
      intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
  set A := 128 * Real.sqrt (T ^ α) * (xiLineTwoLogDerivConstant + Real.log (T + 4)) with hA
  have hlow : (∫ t in (0 : ℝ)..Q, ‖lorentzZeroSumAll (T ^ α) t‖ ^ 2) ≤ A ^ 2 * Q := by
    have hb : ∀ t ∈ uIoc 0 Q, ‖‖lorentzZeroSumAll (T ^ α) t‖ ^ 2‖ ≤ A ^ 2 := by
      intro t ht
      rw [uIoc_of_le hQ0] at ht
      have ht0 : 0 ≤ t := ht.1.le
      have htT : t ≤ T := le_trans ht.2 hQT
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have h1 := norm_lorentzZeroSumAll_le_mass hx1 t
      have h2 := lorentzMass_le_log t
      rw [abs_of_nonneg ht0] at h2
      have h3 : Real.log (t + 4) ≤ Real.log (T + 4) := Real.log_le_log (by linarith) (by linarith)
      have hS' : ‖lorentzZeroSumAll (T ^ α) t‖ ≤ A := by
        refine h1.trans ?_
        rw [hA]
        calc 16 * Real.sqrt (T ^ α) * lorentzMass t
            ≤ 16 * Real.sqrt (T ^ α) * (8 * (xiLineTwoLogDerivConstant + Real.log (|t| + 4))) := by
              gcongr; rw [abs_of_nonneg ht0]; exact h2
          _ ≤ 16 * Real.sqrt (T ^ α) * (8 * (xiLineTwoLogDerivConstant + Real.log (T + 4))) := by
              rw [abs_of_nonneg ht0]; gcongr
          _ = 128 * Real.sqrt (T ^ α) * (xiLineTwoLogDerivConstant + Real.log (T + 4)) := by ring
      exact pow_le_pow_left₀ (norm_nonneg _) hS' 2
    have := intervalIntegral.norm_integral_le_of_norm_le_const hb
    rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hQ0] at this
    exact (le_abs_self _).trans this
  have hhigh : (∫ t in Q..T, ‖lorentzZeroSumAll (T ^ α) t‖ ^ 2) ≤ C ^ 2 * T := by
    have hb : ∀ t ∈ uIoc Q T, ‖‖lorentzZeroSumAll (T ^ α) t‖ ^ 2‖ ≤ C ^ 2 := by
      intro t ht
      rw [uIoc_of_le hQT] at ht
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hS t ⟨ht.1.le, ht.2⟩) 2
    have := intervalIntegral.norm_integral_le_of_norm_le_const hb
    rw [Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ T - Q by linarith)] at this
    have h1 := (le_abs_self _).trans this
    have h2 : C ^ 2 * (T - Q) ≤ C ^ 2 * T := by nlinarith [sq_nonneg C]
    linarith
  have hlow' : A ^ 2 * Q ≤ 1 / 100 * ((T / 4) * (α * L)) := by
    rw [show A ^ 2 * Q = Q * A ^ 2 by ring]; exact hlowH
  have hN : T / 1024 ≤ 1 / 256 * ((T / 4) * (α * L)) := by
    have : T / 1024 * 1 ≤ T / 1024 * (α * L) := mul_le_mul_of_nonneg_left hαL (by positivity)
    linarith
  have htrunc' := (abs_le.mp (htrunc.trans (by unfold truncationLog at htr ⊢; exact htr))).1
  rw [hsplitI] at htrunc'
  have hN0 : 0 < (T / 4) * (α * L) := by nlinarith
  linarith

/-- `min(π/(16w), 1/8) e^{−4w/h} ≤ α(h)`. -/
theorem acAlpha_ge {w h : ℝ} (hw : 0 < w) (hh : 0 < h) :
    min (Real.pi / (16 * w)) (1 / 8) * Real.exp (-(4 * w / h)) ≤ acAlpha w h := by
  have he1 : Real.exp (-(4 * w / h)) ≤ 1 := Real.exp_le_one_iff.mpr (by
    have : 0 < 4 * w / h := by positivity
    linarith)
  have he0 : 0 < Real.exp (-(4 * w / h)) := Real.exp_pos _
  unfold acAlpha acGapUpper
  refine le_min ?_ ?_
  · have e : Real.pi / (4 * (4 * w * Real.exp (4 * w / h))) =
        Real.pi / (16 * w) * Real.exp (-(4 * w / h)) := by
      rw [Real.exp_neg]; field_simp; ring
    rw [e]
    exact mul_le_mul_of_nonneg_right (min_le_left _ _) he0.le
  · calc min (Real.pi / (16 * w)) (1 / 8) * Real.exp (-(4 * w / h))
        ≤ 1 / 8 * Real.exp (-(4 * w / h)) := mul_le_mul_of_nonneg_right (min_le_right _ _) he0.le
      _ ≤ 1 / 8 := by linarith

/-- `min(a₀/128, π/2) e^{−(4w+2)/h} ≤ δ(h)`, `a₀ = min(π/(16w), 1/8)`. -/
theorem acDelta_ge {w h : ℝ} (hw : 0 < w) (hh : 0 < h) :
    min (min (Real.pi / (16 * w)) (1 / 8) / 128) (Real.pi / 2) *
      Real.exp (-((4 * w + 2) / h)) ≤ acDelta w h := by
  set a₀ := min (Real.pi / (16 * w)) (1 / 8) with ha₀
  have ha₀0 : 0 < a₀ := lt_min (by positivity) (by norm_num)
  have he0 : 0 < Real.exp (-((4 * w + 2) / h)) := Real.exp_pos _
  have he1 : Real.exp (-((4 * w + 2) / h)) ≤ 1 := Real.exp_le_one_iff.mpr (by
    have : 0 < (4 * w + 2) / h := by positivity
    linarith)
  have hα := acAlpha_ge hw hh
  rw [← ha₀] at hα
  unfold acDelta
  refine le_min ?_ ?_
  · have e : Real.exp (-((4 * w + 2) / h)) = Real.exp (-(4 * w / h)) * Real.exp (-(2 / h)) := by
      rw [← Real.exp_add]; congr 1; field_simp; ring
    calc min (a₀ / 128) (Real.pi / 2) * Real.exp (-((4 * w + 2) / h))
        ≤ a₀ / 128 * Real.exp (-((4 * w + 2) / h)) :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) he0.le
      _ = (a₀ * Real.exp (-(4 * w / h))) * (Real.exp (-(2 / h)) / 64) / 2 := by rw [e]; ring
      _ ≤ acAlpha w h * (Real.exp (-(2 / h)) / 64) / 2 := by gcongr
  · calc min (a₀ / 128) (Real.pi / 2) * Real.exp (-((4 * w + 2) / h))
        ≤ Real.pi / 2 * Real.exp (-((4 * w + 2) / h)) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) he0.le
      _ ≤ Real.pi / 2 := by
          have := Real.pi_pos
          nlinarith


/-- **The block constant grows at most exponentially in `1/h`.** For `0 < h ≤ 1`,
`B(h) + 1 ≤ M e^{(16w+4)/h}/h` with `M = 2 + 4π/d₀ + 256π²w²/d₀²`,
`d₀ = min(min(π/(16w), 1/8)/128, π/2)`. -/
theorem acBlock_add_one_le {w h : ℝ} (hw : 0 < w) (hh : 0 < h) (hh1 : h ≤ 1) :
    acBlock w h + 1 ≤
      (2 + 4 * Real.pi / min (min (Real.pi / (16 * w)) (1 / 8) / 128) (Real.pi / 2) +
        256 * Real.pi ^ 2 * w ^ 2 / min (min (Real.pi / (16 * w)) (1 / 8) / 128) (Real.pi / 2) ^ 2) *
        (Real.exp ((16 * w + 4) / h) / h) := by
  set d₀ := min (min (Real.pi / (16 * w)) (1 / 8) / 128) (Real.pi / 2) with hd₀
  have hpi := Real.pi_pos
  have hd₀0 : 0 < d₀ := lt_min (by positivity) (by positivity)
  set δ := acDelta w h with hδ
  have hδge := acDelta_ge hw hh
  rw [← hd₀, ← hδ] at hδge
  set P := Real.exp ((4 * w + 2) / h) with hP
  set R := Real.exp ((16 * w + 4) / h) with hR
  have hP0 : 0 < P := Real.exp_pos _
  have hPm : Real.exp (-((4 * w + 2) / h)) * P = 1 := by rw [hP, ← Real.exp_add]; simp
  have hδ0 : 0 < δ := lt_min (by unfold acAlpha acGapUpper; positivity) (by positivity)
  have hδ2 : δ ≤ Real.pi / 2 := min_le_right _ _
  -- `1/(2 sin(δ/2)) ≤ (π/(2 d₀)) P`
  have hsin : 2 * δ / Real.pi ≤ 2 * Real.sin (δ / 2) := by
    have := Real.mul_le_sin (x := δ / 2) (by positivity) (by linarith)
    have e : 2 / Real.pi * (δ / 2) = δ / Real.pi := by field_simp
    rw [e] at this
    have e2 : 2 * δ / Real.pi = 2 * (δ / Real.pi) := by ring
    rw [e2]; linarith
  have hs0 : 0 < 2 * Real.sin (δ / 2) := lt_of_lt_of_le (by positivity) hsin
  have hδP : d₀ ≤ δ * P := by
    have := mul_le_mul_of_nonneg_right hδge hP0.le
    rwa [mul_assoc, hPm, mul_one] at this
  have hinv : 1 / (2 * Real.sin (δ / 2)) ≤ Real.pi / (2 * d₀) * P := by
    rw [div_le_iff₀ hs0]
    have h1 : 1 ≤ Real.pi / (2 * d₀) * P * (2 * δ / Real.pi) := by
      have e : Real.pi / (2 * d₀) * P * (2 * δ / Real.pi) = δ * P / d₀ := by field_simp
      rw [e, le_div_iff₀ hd₀0]; linarith
    calc (1 : ℝ) ≤ Real.pi / (2 * d₀) * P * (2 * δ / Real.pi) := h1
      _ ≤ Real.pi / (2 * d₀) * P * (2 * Real.sin (δ / 2)) := by gcongr
  have hinv0 : 0 ≤ 1 / (2 * Real.sin (δ / 2)) := by positivity
  -- `α ≤ 1/8`, `c₂² = 16 w² e^{8w/h}`
  have hα8 : acAlpha w h ≤ 1 / 8 := min_le_right _ _
  have hα0 : 0 < acAlpha w h := lt_min (by unfold acGapUpper; positivity) (by norm_num)
  have hc₂sq : acGapUpper w h ^ 2 = 16 * w ^ 2 * Real.exp (8 * w / h) := by
    unfold acGapUpper
    rw [mul_pow, mul_pow, ← Real.exp_nat_mul]
    push_cast
    ring_nf
  have hRP : R = Real.exp (8 * w / h) * P ^ 2 := by
    rw [hR, hP, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    push_cast
    field_simp
    ring
  have hP1 : 1 ≤ P := Real.one_le_exp (by positivity)
  have hE81 : 1 ≤ Real.exp (8 * w / h) := Real.one_le_exp (by positivity)
  have hPR : P ≤ R := by
    rw [hRP]
    calc P = 1 * P := (one_mul P).symm
      _ ≤ Real.exp (8 * w / h) * P ^ 2 := by nlinarith
  have hR1 : 1 ≤ R := hP1.trans hPR
  have hRh : R ≤ R / h := le_div_self (by linarith) hh hh1
  -- the three pieces
  have hT2 : 8 / (2 * Real.sin (δ / 2)) ≤ 4 * Real.pi / d₀ * (R / h) := by
    have e : 8 / (2 * Real.sin (δ / 2)) = 8 * (1 / (2 * Real.sin (δ / 2))) := by ring
    rw [e]
    calc 8 * (1 / (2 * Real.sin (δ / 2))) ≤ 8 * (Real.pi / (2 * d₀) * P) := by gcongr
      _ = 4 * Real.pi / d₀ * P := by field_simp; ring
      _ ≤ 4 * Real.pi / d₀ * (R / h) := by gcongr; exact hPR.trans hRh
  have hT3 : 512 * acAlpha w h * acGapUpper w h ^ 2 / (h * (2 * Real.sin (δ / 2)) ^ 2) ≤
      256 * Real.pi ^ 2 * w ^ 2 / d₀ ^ 2 * (R / h) := by
    have hsq : (1 / (2 * Real.sin (δ / 2))) ^ 2 ≤ (Real.pi / (2 * d₀) * P) ^ 2 :=
      pow_le_pow_left₀ hinv0 hinv 2
    have e : 512 * acAlpha w h * acGapUpper w h ^ 2 / (h * (2 * Real.sin (δ / 2)) ^ 2) =
        512 * acAlpha w h * (16 * w ^ 2 * Real.exp (8 * w / h)) / h *
          (1 / (2 * Real.sin (δ / 2))) ^ 2 := by
      rw [hc₂sq]; field_simp
    rw [e]
    calc 512 * acAlpha w h * (16 * w ^ 2 * Real.exp (8 * w / h)) / h *
          (1 / (2 * Real.sin (δ / 2))) ^ 2
        ≤ 512 * (1 / 8) * (16 * w ^ 2 * Real.exp (8 * w / h)) / h *
          (Real.pi / (2 * d₀) * P) ^ 2 := by gcongr
      _ = 256 * Real.pi ^ 2 * w ^ 2 / d₀ ^ 2 * ((Real.exp (8 * w / h) * P ^ 2) / h) := by
          field_simp; ring
      _ = 256 * Real.pi ^ 2 * w ^ 2 / d₀ ^ 2 * (R / h) := by rw [hRP]
  have h2 : (2 : ℝ) ≤ 2 * (R / h) := by
    have : 1 ≤ R / h := hR1.trans hRh
    linarith
  have hB : acBlock w h + 1 = 2 + 8 / (2 * Real.sin (δ / 2)) +
      512 * acAlpha w h * acGapUpper w h ^ 2 / (h * (2 * Real.sin (δ / 2)) ^ 2) := by
    rw [acBlock]; ring
  rw [hB]
  have : (2 + 4 * Real.pi / d₀ + 256 * Real.pi ^ 2 * w ^ 2 / d₀ ^ 2) * (R / h) =
      2 * (R / h) + 4 * Real.pi / d₀ * (R / h) + 256 * Real.pi ^ 2 * w ^ 2 / d₀ ^ 2 * (R / h) := by
    ring
  rw [this]
  linarith


/-- `e^{c/h} = L^{c/K}` for `h = K / log L`. -/
theorem exp_div_loglog {K L c : ℝ} (hK : 0 < K) (hL : 1 < L) :
    Real.exp (c / (K / Real.log L)) = L ^ (c / K) := by
  have hL0 : 0 < L := by linarith
  have hv : 0 < Real.log L := Real.log_pos hL
  rw [Real.rpow_def_of_pos hL0]
  congr 1
  field_simp

/-- `(log u)^n ≤ ε u^s` eventually, for `s > 0`, `ε > 0`. -/
theorem eventually_log_pow_le_rpow (n : ℕ) {s ε : ℝ} (hs : 0 < s) (hε : 0 < ε) :
    ∀ᶠ u : ℝ in atTop, Real.log u ^ n ≤ ε * u ^ s := by
  have := (tendsto_log_pow_div_rpow n hs).eventually (eventually_le_nhds hε)
  filter_upwards [this, eventually_gt_atTop (0 : ℝ)] with u hu hu0
  rwa [div_le_iff₀ (Real.rpow_pos_of_pos hu0 s)] at hu

/-- The lower-height part of the zero sum, uniformly in `α ≤ 1/8`. -/
theorem eventually_lowHeight_le_uniform :
    ∀ᶠ T : ℝ in atTop, 6553600 * (xiLineTwoLogDerivConstant + Real.log (T + 4)) ^ 2 ≤
      T ^ (1 / 8 : ℝ) := by
  set C := xiLineTwoLogDerivConstant
  have hC := xiLineTwoLogDerivConstant_nonneg
  have hC2 : 0 < C + 2 := by linarith
  have h2 := eventually_log_pow_le_rpow 2 (s := 1 / 8) (ε := 1 / (6553600 * (C + 2) ^ 2))
    (by norm_num) (by positivity)
  filter_upwards [h2, eventually_log_bounds, eventually_gt_atTop (1 : ℝ)] with T hT hb hT1
  obtain ⟨hl1, -, -, h4⟩ := hb
  have hle : C + Real.log (T + 4) ≤ (C + 2) * Real.log T := by nlinarith
  have hge : 0 ≤ C + Real.log (T + 4) := by
    have : 0 ≤ Real.log (T + 4) := Real.log_nonneg (by linarith)
    linarith
  have hsq : (C + Real.log (T + 4)) ^ 2 ≤ (C + 2) ^ 2 * Real.log T ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ hge hle 2
  have hK : 0 < 6553600 * (C + 2) ^ 2 := by positivity
  have e : (6553600 * (C + 2) ^ 2) * (1 / (6553600 * (C + 2) ^ 2) * T ^ (1 / 8 : ℝ)) =
      T ^ (1 / 8 : ℝ) := by
    rw [← mul_assoc, mul_one_div_cancel hK.ne', one_mul]
  calc 6553600 * (C + Real.log (T + 4)) ^ 2 ≤ 6553600 * ((C + 2) ^ 2 * Real.log T ^ 2) := by
        gcongr
    _ = (6553600 * (C + 2) ^ 2) * Real.log T ^ 2 := by ring
    _ ≤ (6553600 * (C + 2) ^ 2) * (1 / (6553600 * (C + 2) ^ 2) * T ^ (1 / 8 : ℝ)) := by gcongr
    _ = T ^ (1 / 8 : ℝ) := e

/-- Scale facts for `h = K / log L` with `e^K ≤ L`: `1 < L`, `K ≤ log L`, `0 < h ≤ 1`. -/
theorem loglog_scale_facts {K L : ℝ} (hK0 : 0 < K) (hL : Real.exp K ≤ L) :
    1 < L ∧ K ≤ Real.log L ∧ 0 < K / Real.log L ∧ K / Real.log L ≤ 1 := by
  have hL1 : 1 < L := lt_of_lt_of_le (by linarith [Real.add_one_le_exp K]) hL
  have hvK : K ≤ Real.log L := by
    have := Real.log_le_log (Real.exp_pos _) hL; rwa [Real.log_exp] at this
  have hv0 : 0 < Real.log L := lt_of_lt_of_le hK0 hvK
  exact ⟨hL1, hvK, by positivity, by rw [div_le_one hv0]; exact hvK⟩

/-- `a₀ L^{9/10} ≤ α(K/log L) · L`, `a₀ = min(π/(16w), 1/8)`, once `4w/K ≤ 1/10`. -/
theorem loglog_alpha_mul_ge {w K L : ℝ} (hw : 0 < w) (hK0 : 0 < K) (hq : 4 * w / K ≤ 1 / 10)
    (hL : Real.exp K ≤ L) :
    min (Real.pi / (16 * w)) (1 / 8) * L ^ (9 / 10 : ℝ) ≤ acAlpha w (K / Real.log L) * L := by
  obtain ⟨hL1, -, hh, -⟩ := loglog_scale_facts hK0 hL
  have hL0 : 0 < L := by linarith
  have ha := acAlpha_ge hw hh
  rw [show -(4 * w / (K / Real.log L)) = (-(4 * w)) / (K / Real.log L) by ring,
    exp_div_loglog hK0 hL1] at ha
  have h1 : L ^ (9 / 10 : ℝ) ≤ L ^ (-(4 * w) / K) * L := by
    have e : L ^ (-(4 * w) / K) * L = L ^ (-(4 * w) / K + 1) := by
      rw [Real.rpow_add hL0, Real.rpow_one]
    rw [e]
    apply Real.rpow_le_rpow_of_exponent_le hL1.le
    have : -(4 * w) / K = -(4 * w / K) := by ring
    rw [this]; linarith
  have ha0 : 0 < min (Real.pi / (16 * w)) (1 / 8) := lt_min (by positivity) (by norm_num)
  calc min (Real.pi / (16 * w)) (1 / 8) * L ^ (9 / 10 : ℝ)
      ≤ min (Real.pi / (16 * w)) (1 / 8) * (L ^ (-(4 * w) / K) * L) := by gcongr
    _ = (min (Real.pi / (16 * w)) (1 / 8) * L ^ (-(4 * w) / K)) * L := by ring
    _ ≤ acAlpha w (K / Real.log L) * L := by gcongr

/-- The lower gap threshold at `h = K/log L` is at most `e^{L/2}`. -/
theorem loglog_lowerGapThreshold_le {w K T₂ L : ℝ} (hw : 0 < w) (hK0 : 0 < K)
    (hq : 4 * w / K ≤ 1 / 10) (hL : Real.exp K ≤ L) (u1 : 16 * w ≤ L ^ (9 / 10 : ℝ))
    (hrest : max (max T₂ 4) (Real.exp (xiLineTwoLogDerivConstant + 1)) ≤ Real.exp (L / 2)) :
    lowerGapThreshold w T₂ (K / Real.log L) ≤ Real.exp (L / 2) := by
  obtain ⟨hL1, -, hh, -⟩ := loglog_scale_facts hK0 hL
  have hL0 : 0 < L := by linarith
  have hg : Real.exp (2 * (4 * w * Real.exp (4 * w / (K / Real.log L)))) ≤ Real.exp (L / 2) := by
    rw [exp_div_loglog hK0 hL1]
    apply Real.exp_le_exp.mpr
    have h1 : L ^ (4 * w / K) ≤ L ^ (1 / 10 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1.le hq
    have hL10 : L ^ (1 / 10 : ℝ) * L ^ (9 / 10 : ℝ) = L := by
      rw [← Real.rpow_add hL0]; norm_num
    have h3 : 0 ≤ L ^ (1 / 10 : ℝ) := by positivity
    have h4 : 8 * w * L ^ (1 / 10 : ℝ) ≤ L / 2 := by
      have := mul_le_mul_of_nonneg_left u1 h3
      linarith
    have h5 : 8 * w * L ^ (4 * w / K) ≤ 8 * w * L ^ (1 / 10 : ℝ) := by gcongr
    linarith
  unfold lowerGapThreshold
  refine max_le (le_trans (le_max_left _ _) hrest) (max_le hg (le_trans (le_max_right _ _) hrest))

/-- The logarithmic size condition at `h = K/log L`. -/
theorem loglog_logT_cond {w K L : ℝ} (hw : 0 < w) (hK0 : 0 < K) (hq : 4 * w / K ≤ 1 / 10)
    (hL : Real.exp K ≤ L) (u2 : Real.log L ^ 1 ≤ K / (16 * w) * L ^ (9 / 10 : ℝ))
    (u5 : 2 * (xiLineTwoLogDerivConstant + 2) ≤ L) :
    max (4 * acGapUpper w (K / Real.log L) / (K / Real.log L))
      (2 * (xiLineTwoLogDerivConstant + 2)) ≤ L := by
  obtain ⟨hL1, hvK, hh, -⟩ := loglog_scale_facts hK0 hL
  have hL0 : 0 < L := by linarith
  have hv0 : 0 < Real.log L := lt_of_lt_of_le hK0 hvK
  refine max_le ?_ u5
  set v := Real.log L
  have e : 4 * acGapUpper w (K / v) / (K / v) = L ^ (4 * w / K) * (16 * w * (v / K)) := by
    unfold acGapUpper; rw [exp_div_loglog hK0 hL1]; field_simp; ring
  rw [e]
  have h1 : L ^ (4 * w / K) ≤ L ^ (1 / 10 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1.le hq
  have h2 : 16 * w * (v / K) ≤ L ^ (9 / 10 : ℝ) := by
    have hv : v ≤ K / (16 * w) * L ^ (9 / 10 : ℝ) := by simpa using u2
    rw [show 16 * w * (v / K) = (16 * w / K) * v by ring]
    calc 16 * w / K * v ≤ 16 * w / K * (K / (16 * w) * L ^ (9 / 10 : ℝ)) := by gcongr
      _ = L ^ (9 / 10 : ℝ) := by field_simp
  have hL10 : L ^ (1 / 10 : ℝ) * L ^ (9 / 10 : ℝ) = L := by
    rw [← Real.rpow_add hL0]; norm_num
  have h3 : 0 ≤ 16 * w * (v / K) := by positivity
  calc L ^ (4 * w / K) * (16 * w * (v / K)) ≤ L ^ (1 / 10 : ℝ) * L ^ (9 / 10 : ℝ) := by gcongr
    _ = L := hL10

/-- **The block constant against `α L` at `h = K/log L`.** -/
theorem loglog_block_le {w K L : ℝ} (hw : 0 < w) (hK0 : 0 < K) (hq : 4 * w / K ≤ 1 / 10)
    (hq3 : (32 * w + 8) / K ≤ 8 / 10) (hL : Real.exp K ≤ L)
    (u4 : Real.log L ^ 2 ≤ min (Real.pi / (16 * w)) (1 / 8) * K ^ 2 /
      (400 * (2 + 4 * Real.pi / min (min (Real.pi / (16 * w)) (1 / 8) / 128) (Real.pi / 2) +
        256 * Real.pi ^ 2 * w ^ 2 /
          min (min (Real.pi / (16 * w)) (1 / 8) / 128) (Real.pi / 2) ^ 2) ^ 2) *
        L ^ (1 / 10 : ℝ)) :
    400 * (acBlock w (K / Real.log L) + 1) ^ 2 ≤ acAlpha w (K / Real.log L) * L := by
  obtain ⟨hL1, hvK, hh, hh1⟩ := loglog_scale_facts hK0 hL
  have hL0 : 0 < L := by linarith
  have hv0 : 0 < Real.log L := lt_of_lt_of_le hK0 hvK
  set a₀ := min (Real.pi / (16 * w)) (1 / 8) with ha₀
  have ha₀0 : 0 < a₀ := lt_min (by positivity) (by norm_num)
  set d₀ := min (a₀ / 128) (Real.pi / 2) with hd₀
  have hd₀0 : 0 < d₀ := lt_min (by positivity) (by positivity)
  set M := 2 + 4 * Real.pi / d₀ + 256 * Real.pi ^ 2 * w ^ 2 / d₀ ^ 2 with hM
  have hM0 : 0 < M := by positivity
  set v := Real.log L with hv
  set h := K / v with hhdef
  have hCb := acBlock_add_one_le hw hh hh1
  rw [← ha₀, ← hd₀, ← hM, exp_div_loglog hK0 hL1] at hCb
  set p := (16 * w + 4) / K with hp
  have hCb' : acBlock w h + 1 ≤ M * L ^ p * (v / K) := by
    calc acBlock w h + 1 ≤ M * (L ^ p / (K / v)) := hCb
      _ = M * L ^ p * (v / K) := by field_simp
  have hδ0 : 0 < acDelta w h := lt_min (by unfold acAlpha acGapUpper; positivity) (by positivity)
  have hs : 0 < 2 * Real.sin (acDelta w h / 2) :=
    GaloisForLFunctions.HTGeometry.two_sin_half_pos hδ0
      ((min_le_right _ _).trans (by linarith [Real.pi_pos]))
  have hα0 : 0 < acAlpha w h := lt_min (by unfold acGapUpper; positivity) (by norm_num)
  have hCb0 : 0 ≤ acBlock w h + 1 := by
    unfold acBlock
    have := hα0.le
    positivity
  have hαL := loglog_alpha_mul_ge hw hK0 hq hL
  rw [← ha₀] at hαL
  set q := 4 * w / K with hqdef
  have hexpo : (1 / 10 : ℝ) + (p + p) ≤ 9 / 10 := by
    have : p + p = (32 * w + 8) / K := by rw [hp]; ring
    rw [this]
    linarith
  have hLp : L ^ (1 / 10 : ℝ) * (L ^ p * L ^ p) ≤ L ^ (9 / 10 : ℝ) := by
    rw [← Real.rpow_add hL0, ← Real.rpow_add hL0]
    exact Real.rpow_le_rpow_of_exponent_le hL1.le hexpo
  have hLp0 : 0 ≤ L ^ p := by positivity
  calc 400 * (acBlock w h + 1) ^ 2 ≤ 400 * (M * L ^ p * (v / K)) ^ 2 := by
        have := pow_le_pow_left₀ hCb0 hCb' 2
        linarith
    _ = 400 * M ^ 2 / K ^ 2 * (L ^ p * L ^ p) * v ^ 2 := by ring
    _ ≤ 400 * M ^ 2 / K ^ 2 * (L ^ p * L ^ p) *
        (a₀ * K ^ 2 / (400 * M ^ 2) * L ^ (1 / 10 : ℝ)) := by gcongr
    _ = a₀ * (L ^ (1 / 10 : ℝ) * (L ^ p * L ^ p)) := by field_simp
    _ ≤ a₀ * L ^ (9 / 10 : ℝ) := by gcongr
    _ ≤ acAlpha w h * L := hαL

/-- The low-height part of the mean square against the main term, for `α ≤ 1/8`, `α log T ≥ 1`. -/
theorem lowHeight_le_of_bounds {T α C₀ : ℝ} (hT1 : 1 ≤ T) (hα8 : α ≤ 1 / 8)
    (hαL1 : 1 ≤ α * Real.log T)
    (hlowU : 6553600 * (C₀ + Real.log (T + 4)) ^ 2 ≤ T ^ (1 / 8 : ℝ)) :
    T ^ (3 / 4 : ℝ) * (128 * Real.sqrt (T ^ α) * (C₀ + Real.log (T + 4))) ^ 2 ≤
      1 / 100 * ((T / 4) * (α * Real.log T)) := by
  have hT0 : 0 < T := by linarith
  set D := (C₀ + Real.log (T + 4)) ^ 2 with hD
  have hD0 : 0 ≤ D := sq_nonneg _
  have hsq : Real.sqrt (T ^ α) ^ 2 = T ^ α := Real.sq_sqrt (by positivity)
  have e : T ^ (3 / 4 : ℝ) * (128 * Real.sqrt (T ^ α) * (C₀ + Real.log (T + 4))) ^ 2 =
      16384 * (T ^ (3 / 4 : ℝ) * T ^ α) * D := by
    rw [hD, mul_pow, mul_pow, hsq]; ring
  have h78 : T ^ (3 / 4 : ℝ) * T ^ α ≤ T ^ (7 / 8 : ℝ) := by
    rw [← Real.rpow_add hT0]
    exact Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)
  have hT78 : T ^ (7 / 8 : ℝ) * T ^ (1 / 8 : ℝ) = T := by
    rw [← Real.rpow_add hT0]; norm_num
  have h78p : 0 ≤ T ^ (7 / 8 : ℝ) := by positivity
  have h2 : 16384 * T ^ (7 / 8 : ℝ) * D ≤ T / 400 := by
    have h4 := mul_le_mul_of_nonneg_left hlowU h78p
    rw [hT78] at h4
    have e2 : 16384 * T ^ (7 / 8 : ℝ) * D * 400 = T ^ (7 / 8 : ℝ) * (6553600 * D) := by ring
    linarith
  have h1 : 16384 * (T ^ (3 / 4 : ℝ) * T ^ α) * D ≤ 16384 * T ^ (7 / 8 : ℝ) * D := by
    gcongr
  have h3 : T / 400 ≤ 1 / 100 * ((T / 4) * (α * Real.log T)) := by
    have : T / 400 * 1 ≤ T / 400 * (α * Real.log T) :=
      mul_le_mul_of_nonneg_left hαL1 (by positivity)
    linarith
  rw [e]; linarith

/-- **One height of the `log log` contradiction.** -/
theorem false_of_loglog {w₁ w₂ T₂ T₂' K T : ℝ} (hw₁ : 0 < w₁) (hw₂ : 0 < w₂)
    (hU : ∀ h : ℝ, 0 < h → ∀ n, T₂ ≤ xiOrderedPositiveOrdinate n →
      (∀ k, n ≤ k → xiOrderedPositiveOrdinate k ≤ xiOrderedPositiveOrdinate n + 2 * w₂ →
        RigidAt h k) →
      ordinateGap n * Real.log (xiOrderedPositiveOrdinate n) ≤ 4 * w₂ * Real.exp (4 * w₂ / h))
    (hLo : ∀ h : ℝ, 0 < h → ∀ n, lowerGapThreshold w₁ T₂' h ≤ xiOrderedPositiveOrdinate n →
      (∀ k, n ≤ k → xiOrderedPositiveOrdinate k ≤ xiOrderedPositiveOrdinate n + 2 * w₁ + 2 →
        RigidAt h k) →
      Real.exp (-(2 / h)) / 64 ≤ ordinateGap n * Real.log (xiOrderedPositiveOrdinate n))
    (hK0 : 0 < K) (hq1 : 4 * w₁ / K ≤ 1 / 10) (hq2 : 4 * w₂ / K ≤ 1 / 10)
    (hq3 : (32 * w₂ + 8) / K ≤ 8 / 10)
    (u0 : Real.exp K ≤ Real.log T) (u1 : 16 * w₁ ≤ Real.log T ^ (9 / 10 : ℝ))
    (u2 : Real.log (Real.log T) ^ 1 ≤ K / (16 * w₂) * Real.log T ^ (9 / 10 : ℝ))
    (u3 : Real.log (Real.log T) ^ 1 ≤
      min (Real.pi / (16 * w₂)) (1 / 8) / 8 * Real.log T ^ (9 / 10 : ℝ))
    (u3' : 2 ≤ min (Real.pi / (16 * w₂)) (1 / 8) / 2 * Real.log T ^ (9 / 10 : ℝ))
    (u4 : Real.log (Real.log T) ^ 2 ≤ min (Real.pi / (16 * w₂)) (1 / 8) * K ^ 2 /
      (400 * (2 + 4 * Real.pi / min (min (Real.pi / (16 * w₂)) (1 / 8) / 128) (Real.pi / 2) +
        256 * Real.pi ^ 2 * w₂ ^ 2 /
          min (min (Real.pi / (16 * w₂)) (1 / 8) / 128) (Real.pi / 2) ^ 2) ^ 2) *
        Real.log T ^ (1 / 10 : ℝ))
    (u5 : 2 * (xiLineTwoLogDerivConstant + 2) ≤ Real.log T)
    (hB0 : max (max T₂ (max T₂' 4)) (Real.exp (xiLineTwoLogDerivConstant + 1)) ≤
      T ^ (1 / 2 : ℝ))
    (htail : 1024 * Real.sqrt (T ^ (1 / 8 : ℝ)) *
      (xiLineTwoLogDerivConstant + Real.log (2 * T ^ 2 + 5)) ≤ T ^ (3 / 4 : ℝ))
    (hMont : ∀ x : ℝ, Real.log T ^ 3 ≤ x → x ≤ T ^ (1 / 8 : ℝ) →
      5 / 8 * ((T / 4) * Real.log x) ≤
        Real.pi / 2 * (montgomeryForm (zeroWindow T) (fun q : XiZeroCopy => (q.1 : ℂ)) x).re)
    (htr : 131072 * T ^ (1 / 8 : ℝ) *
      (truncationLog T ^ 2 * (3 * Real.log (1 + T) + 2) + 64) ≤ T / 1024)
    (hlowU : 6553600 * (xiLineTwoLogDerivConstant + Real.log (T + 4)) ^ 2 ≤ T ^ (1 / 8 : ℝ))
    (hT16 : 16 ≤ T) (hTw : 2 * w₁ + 2 * w₂ + 3 ≤ T)
    (hW : RigidWindow (K / Real.log (Real.log T)) T) : False := by
  set C₀ := xiLineTwoLogDerivConstant with hC₀
  have hT0 : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  set L := Real.log T with hLdef
  obtain ⟨hL1, hvK, hh, hh1⟩ := loglog_scale_facts hK0 u0
  have hL0 : 0 < L := by linarith
  set v := Real.log L with hvdef
  set h := K / v with hhdef
  set α := acAlpha w₂ h with hαdef
  have hα0 : 0 < α := lt_min (by unfold acGapUpper; positivity) (by norm_num)
  have hα8 : α ≤ 1 / 8 := min_le_right _ _
  have hαL : min (Real.pi / (16 * w₂)) (1 / 8) * L ^ (9 / 10 : ℝ) ≤ α * L :=
    loglog_alpha_mul_ge hw₂ hK0 hq2 u0
  have hv3 : 3 * v + 1 ≤ α * L := by
    have h1 : v ≤ min (Real.pi / (16 * w₂)) (1 / 8) / 8 * L ^ (9 / 10 : ℝ) := by simpa using u3
    linarith
  have hαL1 : 1 ≤ α * L := by
    have := Real.log_nonneg hL1.le
    linarith
  -- the window bound
  have hxT : T ^ α ≤ T ^ (1 / 8 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT1 hα8
  have hhalf : T ^ (1 / 2 : ℝ) = Real.exp (L / 2) := by
    rw [Real.rpow_def_of_pos hT0]; congr 1; ring
  have hrest : max (max T₂' 4) (Real.exp (C₀ + 1)) ≤ Real.exp (L / 2) := by
    rw [← hhalf]
    refine max_le (le_trans ?_ hB0) (le_trans (le_max_right _ _) hB0)
    exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hB : max T₂ (lowerGapThreshold w₁ T₂' h) ≤ T ^ (1 / 2 : ℝ) := by
    refine max_le (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hB0) ?_
    rw [hhalf]
    exact loglog_lowerGapThreshold_le hw₁ hK0 hq1 u0 u1 hrest
  have hlogT := loglog_logT_cond hw₂ hK0 hq2 u0 u2 u5
  have hF : 1024 * Real.sqrt (T ^ α) * (C₀ + Real.log (2 * T ^ 2 + 5)) ≤ T ^ (3 / 4 : ℝ) := by
    have hs : Real.sqrt (T ^ α) ≤ Real.sqrt (T ^ (1 / 8 : ℝ)) := Real.sqrt_le_sqrt hxT
    have hpos : 0 ≤ C₀ + Real.log (2 * T ^ 2 + 5) := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * T ^ 2 + 5 by nlinarith)
      have := xiLineTwoLogDerivConstant_nonneg
      linarith
    calc 1024 * Real.sqrt (T ^ α) * (C₀ + Real.log (2 * T ^ 2 + 5))
        ≤ 1024 * Real.sqrt (T ^ (1 / 8 : ℝ)) * (C₀ + Real.log (2 * T ^ 2 + 5)) := by gcongr
      _ ≤ T ^ (3 / 4 : ℝ) := htail
  have hS := norm_lorentzZeroSumAll_le_of_rigidWindow hw₁ hw₂ hU hLo hh hB hlogT hF hT16 hTw hW
  -- the Montgomery lower bound at `x = T^α`
  have hlogx : Real.log (T ^ α) = α * L := Real.log_rpow hT0 α
  have hx3 : Real.log T ^ 3 ≤ T ^ α := by
    have e1 : Real.log T ^ 3 = Real.exp (3 * v) := by
      rw [show 3 * v = (3 : ℕ) * v by norm_num, Real.exp_nat_mul, Real.exp_log hL0]
    have e2 : T ^ α = Real.exp (α * L) := by rw [Real.rpow_def_of_pos hT0, mul_comm]
    rw [e1, e2]
    exact Real.exp_le_exp.mpr (by linarith)
  have hMont' := hMont (T ^ α) hx3 hxT
  rw [hlogx] at hMont'
  -- truncation
  have htr' : 131072 * T ^ α * (truncationLog T ^ 2 * (3 * Real.log (1 + T) + 2) + 64) ≤
      T / 1024 := by
    have hP : 0 ≤ truncationLog T ^ 2 * (3 * Real.log (1 + T) + 2) + 64 := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ 1 + T by linarith)
      positivity
    calc 131072 * T ^ α * (truncationLog T ^ 2 * (3 * Real.log (1 + T) + 2) + 64)
        ≤ 131072 * T ^ (1 / 8 : ℝ) * (truncationLog T ^ 2 * (3 * Real.log (1 + T) + 2) + 64) := by
          gcongr
      _ ≤ T / 1024 := htr
  -- the low heights
  have hlowH := lowHeight_le_of_bounds hT1 hα8 hαL1 hlowU
  -- the block constant against `α L`
  have hkey : 400 * (acBlock w₂ h + 1) ^ 2 ≤ α * L := loglog_block_le hw₂ hK0 hq2 hq3 u0 u4
  have hC : (acBlock w₂ h + 1) ^ 2 * T ≤ 1 / 100 * ((T / 4) * (α * L)) := by
    have h1 : (acBlock w₂ h + 1) ^ 2 ≤ α * L / 400 := by linarith
    calc (acBlock w₂ h + 1) ^ 2 * T ≤ α * L / 400 * T := mul_le_mul_of_nonneg_right h1 hT0.le
      _ = 1 / 100 * ((T / 4) * (α * L)) := by ring
  exact false_of_lorentzZeroSumAll_le hT16 hα0 hαL1 hMont' htr' hlowH hC hS

/-- **The anti-crystal law at depth `K / log log T`.** There is `K > 0` such that, eventually in
`T`, the window `[T^{1/2}, T³]` of ordered zeta ordinates is not `(K / log log T)`-rigid. -/
theorem exists_eventually_not_rigidWindow_loglog :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ T : ℝ in atTop, ¬ RigidWindow (K / Real.log (Real.log T)) T := by
  obtain ⟨w₂, hw₂, T₂, hU⟩ := exists_gap_mul_log_le_uniform
  obtain ⟨w₁, hw₁, T₂', hLo⟩ := exists_le_gap_mul_log_uniform
  set K : ℝ := 40 * (w₁ + w₂ + 1) with hK
  have hK0 : 0 < K := by positivity
  refine ⟨K, hK0, ?_⟩
  have hq1 : 4 * w₁ / K ≤ 1 / 10 := by rw [div_le_iff₀ hK0, hK]; linarith
  have hq2 : 4 * w₂ / K ≤ 1 / 10 := by rw [div_le_iff₀ hK0, hK]; linarith
  have hq3 : (32 * w₂ + 8) / K ≤ 8 / 10 := by rw [div_le_iff₀ hK0, hK]; linarith
  set C₀ := xiLineTwoLogDerivConstant with hC₀
  set a₀ := min (Real.pi / (16 * w₂)) (1 / 8) with ha₀
  have ha₀0 : 0 < a₀ := lt_min (by positivity) (by norm_num)
  set d₀ := min (a₀ / 128) (Real.pi / 2) with hd₀
  have hd₀0 : 0 < d₀ := lt_min (by positivity) (by positivity)
  set M := 2 + 4 * Real.pi / d₀ + 256 * Real.pi ^ 2 * w₂ ^ 2 / d₀ ^ 2 with hM
  have hM0 : 0 < M := by positivity
  -- conditions on `u = log T`
  have U0 : ∀ᶠ u : ℝ in atTop, Real.exp K ≤ u := eventually_ge_atTop _
  have U1 : ∀ᶠ u : ℝ in atTop, 16 * w₁ ≤ u ^ (9 / 10 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num)).eventually_ge_atTop _
  have U2 := eventually_log_pow_le_rpow 1 (s := 9 / 10) (ε := K / (16 * w₂)) (by norm_num)
    (by positivity)
  have U3 := eventually_log_pow_le_rpow 1 (s := 9 / 10) (ε := a₀ / 8) (by norm_num)
    (by positivity)
  have U3' : ∀ᶠ u : ℝ in atTop, 2 ≤ a₀ / 2 * u ^ (9 / 10 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num)).const_mul_atTop (by positivity)).eventually_ge_atTop _
  have U4 := eventually_log_pow_le_rpow 2 (s := 1 / 10) (ε := a₀ * K ^ 2 / (400 * M ^ 2))
    (by norm_num) (by positivity)
  have U5 : ∀ᶠ u : ℝ in atTop, 2 * (C₀ + 2) ≤ u := eventually_ge_atTop _
  have hUu := Real.tendsto_log_atTop.eventually
    (U0.and (U1.and (U2.and (U3.and (U3'.and (U4.and U5))))))
  have eB := (tendsto_rpow_atTop (show (0 : ℝ) < 1 / 2 by norm_num)).eventually_ge_atTop
    (max (max T₂ (max T₂' 4)) (Real.exp (C₀ + 1)))
  filter_upwards [hUu, eB, eventually_tailFactor_le (α := 1 / 8) (by norm_num) le_rfl,
    eventually_montgomeryForm_lower_uniform, eventually_truncation_le_uniform,
    eventually_lowHeight_le_uniform, eventually_ge_atTop (16 : ℝ),
    eventually_ge_atTop (2 * w₁ + 2 * w₂ + 3)]
    with T hu hB0 htail hMont htr hlowU hT16 hTw hW
  obtain ⟨u0, u1, u2, u3, u3', u4, u5⟩ := hu
  exact false_of_loglog hw₁ hw₂ hU hLo hK0 hq1 hq2 hq3 u0 u1 u2 u3 u3' u4 u5 hB0 htail hMont htr
    hlowU hT16 hTw hW

end

end RHTower
