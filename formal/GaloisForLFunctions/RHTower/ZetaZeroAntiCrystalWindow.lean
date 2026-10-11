import GaloisForLFunctions.RHTower.ZetaRigidOrdinateWindow
import GaloisForLFunctions.RHTower.ZetaZeroAntiCrystalLaw

/-!
# The anti-crystal law in every window

`RigidWindow h T` says that every ordered ordinate `γ_k ∈ [T^{1/2}, T³]` is rigid at scale `h`
(`RigidAt h k`): strictly increasing, with consecutive gaps `g, g'` obeying `g' ≤ g e^{(g+g')/h}`
and `g ≤ g' e^{(g+g')/h}`.

**Theorem** (`eventually_not_rigidWindow`). For every `h > 0`, eventually in `T`, the window
`[T^{1/2}, T³]` is not `h`-rigid.

So non-rigidity of the zeros of ζ occurs at every large scale, not merely at infinitely many
indices. The proof of `not_rigidOrdinates` uses rigidity only inside `(T^{1/2}, T² + O(1)]`, and
its constants (`exists_gap_mul_log_le_local`, `exists_le_gap_mul_log_local`) are independent of the
window. Montgomery's pair-correlation asymptotic then contradicts the bounded Lorentzian zero sum
at that single height `T`.
-/

open Complex Filter Topology Set Finset MeasureTheory
open GaloisForLFunctions.HTGeometry (lorentzWeight norm_sum_lorentzWeight_phase_le)

namespace RHTower

noncomputable section

/-- **Rigidity on the window `[T^{1/2}, T³]`.** -/
def RigidWindow (h T : ℝ) : Prop :=
  ∀ k, T ^ (1 / 2 : ℝ) ≤ xiOrderedPositiveOrdinate k → xiOrderedPositiveOrdinate k ≤ T ^ 3 →
    RigidAt h k

/-- The block bound with local rigidity hypotheses. -/
theorem norm_block_le_local {h : ℝ} (hh : 0 < h)
    {α L c₁ c₂ δ x t : ℝ} (hα : 0 < α) (hL : 0 < L) (hc₂ : 0 < c₂) (hLc : 4 * c₂ / h ≤ L)
    (hδ0 : 0 < δ) (hδc : δ ≤ α * c₁ / 2) (hαc : α * c₂ ≤ Real.pi / 4) (hδ2 : δ ≤ Real.pi / 2)
    (hx : 0 < x) (hlogx : Real.log x = α * L) (a m : ℕ)
    (hgap : ∀ n, a ≤ n → n ≤ a + m →
      RigidAt h n ∧ ((xiOrderedPositiveZeroCopy n).1 : ℂ) =
        1 / 2 + (xiOrderedPositiveOrdinate n : ℂ) * I ∧
      c₁ / (2 * L) ≤ ordinateGap n ∧ ordinateGap n ≤ 2 * c₂ / L)
    (hmass : ∑ i ∈ Finset.range (m + 1), lorentzWeight t (xiOrderedPositiveOrdinate (a + i)) ≤
      16 * L) :
    ‖∑ i ∈ Finset.range (m + 1), zeroSumTerm x t (xiOrderedPositiveZeroCopy (a + i))‖ ≤
      1 + 8 / (2 * Real.sin (δ / 2)) + 512 * α * c₂ ^ 2 / (h * (2 * Real.sin (δ / 2)) ^ 2) := by
  have hδπ : δ ≤ Real.pi := hδ2.trans (by linarith [Real.pi_pos])
  have hterm : ∀ i ∈ Finset.range (m + 1), zeroSumTerm x t (xiOrderedPositiveZeroCopy (a + i)) =
      (lorentzWeight t (xiOrderedPositiveOrdinate (a + i)) : ℂ) *
        cexp (I * ((Real.log x * xiOrderedPositiveOrdinate (a + i) : ℝ) : ℂ)) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    exact zeroSumTerm_of_eq_half_add hx (hgap (a + i) (by omega) (by omega)).2.1
  rw [Finset.sum_congr rfl hterm]
  have hu : Monotone (fun i => xiOrderedPositiveOrdinate (a + i)) := fun i j hij =>
    xiOrderedPositiveOrdinate_monotone (by omega)
  have hθ : ∀ k < m, δ ≤ Real.log x * (xiOrderedPositiveOrdinate (a + (k + 1)) -
      xiOrderedPositiveOrdinate (a + k)) ∧ Real.log x * (xiOrderedPositiveOrdinate (a + (k + 1)) -
      xiOrderedPositiveOrdinate (a + k)) ≤ 2 * Real.pi - δ := by
    intro k hk
    obtain ⟨-, -, hg1, hg2⟩ := hgap (a + k) (by omega) (by omega)
    have e : xiOrderedPositiveOrdinate (a + (k + 1)) - xiOrderedPositiveOrdinate (a + k) =
        ordinateGap (a + k) := by rw [ordinateGap, show a + (k + 1) = a + k + 1 by ring]
    rw [e, hlogx]
    exact increment_mem_of_gap_bounds hα hL hδc hαc hδ2 hg1 hg2
  have hηb : ∀ k, k + 1 < m →
      |Real.log x * (xiOrderedPositiveOrdinate (a + (k + 2)) -
          xiOrderedPositiveOrdinate (a + (k + 1))) -
        Real.log x * (xiOrderedPositiveOrdinate (a + (k + 1)) -
          xiOrderedPositiveOrdinate (a + k))| ≤ 16 * α * c₂ ^ 2 / (h * L) := by
    intro k hk
    obtain ⟨hR0, -, -, hg0⟩ := hgap (a + k) (by omega) (by omega)
    obtain ⟨-, -, -, hg1⟩ := hgap (a + k + 1) (by omega) (by omega)
    have e0 : xiOrderedPositiveOrdinate (a + (k + 1)) - xiOrderedPositiveOrdinate (a + k) =
        ordinateGap (a + k) := by rw [ordinateGap, show a + (k + 1) = a + k + 1 by ring]
    have e1 : xiOrderedPositiveOrdinate (a + (k + 2)) - xiOrderedPositiveOrdinate (a + (k + 1)) =
        ordinateGap (a + k + 1) := by
      rw [ordinateGap, show a + (k + 2) = a + k + 1 + 1 by ring,
        show a + (k + 1) = a + k + 1 by ring]
    rw [e0, e1, hlogx, ← mul_sub, abs_mul, abs_of_pos (by positivity)]
    exact increment_variation_le hα hL hh hc₂ hLc (ordinateGap_nonneg _) (ordinateGap_nonneg _)
      hg0 hg1 hR0.2.1 hR0.2.2
  have hmain := norm_sum_lorentzWeight_phase_le hδ0 hδπ (t := t) (lam := Real.log x)
    (η := 16 * α * c₂ ^ 2 / (h * L)) (M := 16 * L) hu m hθ hηb (by positivity) hmass
  refine hmain.trans (le_of_eq ?_)
  field_simp
  ring

/-- Gap facts for block indices from window rigidity. -/
theorem block_gap_facts_window {h w₁ w₂ c₁ c₂ T₂ T₃ T L : ℝ} (hT1 : 1 ≤ T)
    (hL : L = Real.log T) (hL0 : 0 < L)
    (hU : ∀ n, T₂ ≤ xiOrderedPositiveOrdinate n →
      (∀ k, n ≤ k → xiOrderedPositiveOrdinate k ≤ xiOrderedPositiveOrdinate n + 2 * w₂ →
        RigidAt h k) → ordinateGap n * Real.log (xiOrderedPositiveOrdinate n) ≤ c₂)
    (hLo : ∀ n, T₃ ≤ xiOrderedPositiveOrdinate n →
      (∀ k, n ≤ k → xiOrderedPositiveOrdinate k ≤ xiOrderedPositiveOrdinate n + 2 * w₁ + 2 →
        RigidAt h k) → c₁ ≤ ordinateGap n * Real.log (xiOrderedPositiveOrdinate n))
    (hB : max T₂ T₃ ≤ T ^ (1 / 2 : ℝ))
    (hTop₁ : T ^ 2 + 2 * w₁ + 2 ≤ T ^ 3) (hTop₂ : T ^ 2 + 2 * w₂ ≤ T ^ 3)
    (hW : RigidWindow h T) {n : ℕ} (hn1 : T ^ (1 / 2 : ℝ) < xiOrderedPositiveOrdinate n)
    (hn2 : xiOrderedPositiveOrdinate n ≤ T ^ 2) :
    RigidAt h n ∧ ((xiOrderedPositiveZeroCopy n).1 : ℂ) =
        1 / 2 + (xiOrderedPositiveOrdinate n : ℂ) * I ∧
      c₁ / (2 * L) ≤ ordinateGap n ∧ ordinateGap n ≤ 2 * c₂ / L := by
  set γ := xiOrderedPositiveOrdinate
  have hT0 : 0 < T := by linarith
  have hBh0 : 0 < T ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hT0 _
  have hγ0 : 0 < γ n := by linarith
  have hT2T3 : T ^ 2 ≤ T ^ 3 := pow_le_pow_right₀ hT1 (by norm_num)
  have hRn : RigidAt h n := hW n hn1.le (le_trans hn2 hT2T3)
  have hS : ∀ k, T ^ (1 / 2 : ℝ) ≤ γ k → γ k ≤ T ^ 3 → γ k < γ (k + 1) := fun k h1 h2 =>
    (hW k h1 h2).1
  have hcopy := orderedPositiveZeroCopy_eq_of_strict_window hS hn1.le (le_trans hn2 hT2T3)
  have hmono : ∀ k, n ≤ k → γ n ≤ γ k := fun k hk => xiOrderedPositiveOrdinate_monotone hk
  have hu := hU n (le_trans (le_max_left _ _) (le_trans hB hn1.le)) fun k hk1 hk2 =>
    hW k (le_trans hn1.le (hmono k hk1)) (by linarith)
  have hlo := hLo n (le_trans (le_max_right _ _) (le_trans hB hn1.le)) fun k hk1 hk2 =>
    hW k (le_trans hn1.le (hmono k hk1)) (by linarith)
  have hl1 : L / 2 ≤ Real.log (γ n) := by
    have := Real.log_le_log hBh0 hn1.le
    rw [Real.log_rpow hT0, ← hL] at this; linarith
  have hl2 : Real.log (γ n) ≤ 2 * L := by
    have := Real.log_le_log hγ0 hn2
    rw [Real.log_pow, ← hL] at this; push_cast at this; linarith
  have hg0 := ordinateGap_nonneg n
  refine ⟨hRn, hcopy, ?_, ?_⟩
  · rw [div_le_iff₀ (by positivity)]
    calc c₁ ≤ ordinateGap n * Real.log (γ n) := hlo
      _ ≤ ordinateGap n * (2 * L) := mul_le_mul_of_nonneg_left hl2 hg0
  · rw [le_div_iff₀ hL0]
    have : ordinateGap n * (L / 2) ≤ c₂ :=
      le_trans (mul_le_mul_of_nonneg_left hl1 hg0) hu
    linarith


/-- **The windowed Lorentzian zero sum bound.** -/
theorem exists_norm_lorentzZeroSumAll_le_window {h : ℝ} (hh : 0 < h) :
    ∃ α : ℝ, 0 < α ∧ α ≤ 1 / 8 ∧ ∃ C : ℝ, ∀ᶠ T : ℝ in atTop, RigidWindow h T →
      ∀ t ∈ Icc (T ^ (3 / 4 : ℝ)) T, ‖lorentzZeroSumAll (T ^ α) t‖ ≤ C := by
  classical
  obtain ⟨w₂, hw₂, c₂, hc₂, T₂, hU⟩ := exists_gap_mul_log_le_local hh
  obtain ⟨w₁, hw₁, c₁, hc₁, T₃, hLo⟩ := exists_le_gap_mul_log_local hh
  set α : ℝ := min (Real.pi / (4 * c₂)) (1 / 8) with hαdef
  have hα0 : 0 < α := lt_min (by positivity) (by norm_num)
  have hα8 : α ≤ 1 / 8 := min_le_right _ _
  have hαc : α * c₂ ≤ Real.pi / 4 := by
    have := min_le_left (Real.pi / (4 * c₂)) (1 / 8)
    rw [← hαdef] at this
    calc α * c₂ ≤ Real.pi / (4 * c₂) * c₂ := mul_le_mul_of_nonneg_right this hc₂.le
      _ = Real.pi / 4 := by field_simp
  set δ : ℝ := min (α * c₁ / 2) (Real.pi / 2) with hδdef
  have hδ0 : 0 < δ := lt_min (by positivity) (by positivity)
  have hδ2 : δ ≤ Real.pi / 2 := min_le_right _ _
  have hδc : δ ≤ α * c₁ / 2 := min_le_left _ _
  set Cb : ℝ := 1 + 8 / (2 * Real.sin (δ / 2)) +
    512 * α * c₂ ^ 2 / (h * (2 * Real.sin (δ / 2)) ^ 2) with hCb
  have hσ0 : 0 < 2 * Real.sin (δ / 2) :=
    GaloisForLFunctions.HTGeometry.two_sin_half_pos hδ0 (hδ2.trans (by linarith [Real.pi_pos]))
  have hCb1 : 1 ≤ Cb := by
    have : 0 ≤ 8 / (2 * Real.sin (δ / 2)) +
        512 * α * c₂ ^ 2 / (h * (2 * Real.sin (δ / 2)) ^ 2) := by positivity
    linarith
  refine ⟨α, hα0, hα8, Cb + 1, ?_⟩
  have eB := (tendsto_rpow_atTop (show (0 : ℝ) < 1 / 2 by norm_num)).eventually_ge_atTop
    (max T₂ T₃)
  have eL := Real.tendsto_log_atTop.eventually_ge_atTop
    (max (4 * c₂ / h) (2 * (xiLineTwoLogDerivConstant + 2)))
  filter_upwards [eB, eL, eventually_tailFactor_le hα0 hα8, eventually_ge_atTop (16 : ℝ),
    eventually_ge_atTop (2 * w₁ + 2 * w₂ + 3)] with T hB hlogT hF hT16 hTw
  intro hW t ht
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
      exact block_gap_facts_window hT1 hLdef hL0 hU hLo hB hTop₁ hTop₂ hW hin.1 hin.2
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

/-- **The windowed anti-crystal law.** For every `h > 0`, eventually in `T`, the window
`[T^{1/2}, T³]` of ordered zeta ordinates is not `h`-rigid. -/
theorem eventually_not_rigidWindow {h : ℝ} (hh : 0 < h) :
    ∀ᶠ T : ℝ in atTop, ¬ RigidWindow h T := by
  obtain ⟨α, hα0, hα8, C, hev⟩ := exists_norm_lorentzZeroSumAll_le_window hh
  have hα1 : α < 1 := by linarith
  have hM := tendsto_montgomeryForm_div_leadingOrder hα0 hα1
  have hTr := tendsto_truncation_error_div hα0 hα1 xiLineTwoLogDerivConstant
    xiLineTwoLogDerivConstant_nonneg
  have e1 := hM.eventually (lt_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num))
  have e2 := hTr.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 100 by norm_num))
  have e3 := eventually_lowHeight_le hα0 hα8
  have e4 := Real.tendsto_log_atTop.eventually_ge_atTop (400 * C ^ 2 / α + 1)
  filter_upwards [hev, e1, e2, e3, e4, eventually_ge_atTop (16 : ℝ)]
    with T hTev hT1 hT2 hT3 hT4 hT16 hW
  have hTev := hTev hW
  have hT0 : 0 < T := by linarith
  set L := Real.log T with hL
  have hL0 : 0 < L := Real.log_pos (by linarith)
  have hN0 : 0 < (T / 4) * (α * L) := by positivity
  have hx1 : 1 ≤ T ^ α := Real.one_le_rpow (by linarith) hα0.le
  set Q := T ^ (3 / 4 : ℝ) with hQ
  have hQ0 : 0 ≤ Q := Real.rpow_nonneg hT0.le _
  have hQT : Q ≤ T := Real.rpow_le_self_of_one_le (by linarith) (by norm_num)
  have hF : (1 / 2 : ℝ) * ((T / (2 * Real.pi)) * (α * L)) <
      (montgomeryForm (zeroWindow T) (fun q : XiZeroCopy => (q.1 : ℂ)) (T ^ α)).re := by
    have hden : 0 < (T / (2 * Real.pi)) * (α * L) := by positivity
    rwa [lt_div_iff₀ hden] at hT1
  have htrunc := integral_normSq_lorentzZeroSumAll_sub_montgomeryForm_le hx1 hT0.le
  have hT2' : 131072 * T ^ α * ((xiLineTwoLogDerivConstant + Real.log (2 * T + 5)) ^ 2 *
      (3 * Real.log (1 + T) + 2) + 64) < 1 / 100 * ((T / 4) * (α * L)) := by
    rwa [div_lt_iff₀ hN0] at hT2
  have htr : |(∫ t in Icc 0 T, ‖lorentzZeroSumAll (T ^ α) t‖ ^ 2) - Real.pi / 2 *
      (montgomeryForm (zeroWindow T) (fun q : XiZeroCopy => (q.1 : ℂ)) (T ^ α)).re| <
      1 / 100 * ((T / 4) * (α * L)) := by
    refine lt_of_le_of_lt htrunc ?_
    unfold truncationLog
    exact hT2'
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
      have hS : ‖lorentzZeroSumAll (T ^ α) t‖ ≤ A := by
        refine h1.trans ?_
        rw [hA]
        calc 16 * Real.sqrt (T ^ α) * lorentzMass t
            ≤ 16 * Real.sqrt (T ^ α) * (8 * (xiLineTwoLogDerivConstant + Real.log (|t| + 4))) := by
              gcongr; rw [abs_of_nonneg ht0]; exact h2
          _ ≤ 16 * Real.sqrt (T ^ α) * (8 * (xiLineTwoLogDerivConstant + Real.log (T + 4))) := by
              rw [abs_of_nonneg ht0]; gcongr
          _ = 128 * Real.sqrt (T ^ α) * (xiLineTwoLogDerivConstant + Real.log (T + 4)) := by ring
      exact pow_le_pow_left₀ (norm_nonneg _) hS 2
    have := intervalIntegral.norm_integral_le_of_norm_le_const hb
    rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hQ0] at this
    exact (le_abs_self _).trans this
  have hhigh : (∫ t in Q..T, ‖lorentzZeroSumAll (T ^ α) t‖ ^ 2) ≤ C ^ 2 * T := by
    have hb : ∀ t ∈ uIoc Q T, ‖‖lorentzZeroSumAll (T ^ α) t‖ ^ 2‖ ≤ C ^ 2 := by
      intro t ht
      rw [uIoc_of_le hQT] at ht
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hS := hTev t ⟨ht.1.le, ht.2⟩
      exact pow_le_pow_left₀ (norm_nonneg _) hS 2
    have := intervalIntegral.norm_integral_le_of_norm_le_const hb
    rw [Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ T - Q by linarith)] at this
    have h1 := (le_abs_self _).trans this
    have h2 : C ^ 2 * (T - Q) ≤ C ^ 2 * T := by nlinarith [sq_nonneg C]
    linarith
  have hC2 : C ^ 2 * T ≤ 1 / 100 * ((T / 4) * (α * L)) := by
    have : 400 * C ^ 2 / α ≤ L := by linarith
    rw [div_le_iff₀ hα0] at this
    nlinarith
  have hlow' : A ^ 2 * Q ≤ 1 / 100 * ((T / 4) * (α * L)) := by
    have := hT3; rw [hA]; linarith [show Q * A ^ 2 = A ^ 2 * Q by ring]
  rw [hsplitI] at htr
  have hpi : Real.pi / 2 * ((1 / 2 : ℝ) * ((T / (2 * Real.pi)) * (α * L))) = (T / 8) * (α * L) := by
    field_simp; ring
  have hFpi : (T / 8) * (α * L) < Real.pi / 2 *
      (montgomeryForm (zeroWindow T) (fun q : XiZeroCopy => (q.1 : ℂ)) (T ^ α)).re := by
    rw [← hpi]
    exact mul_lt_mul_of_pos_left hF (by positivity)
  have habs := (abs_lt.mp htr).1
  nlinarith

end

end RHTower
