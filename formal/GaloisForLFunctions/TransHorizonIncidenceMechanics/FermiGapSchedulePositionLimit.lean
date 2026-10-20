import GaloisForLFunctions.TransHorizonIncidenceMechanics.FermiGapSchedulePositionLaw

/-!
# The position law as a limit

If the gap level `h(N) + 1` sits at relative depth `h(N)/⌊log₂ N⌋ → α` with `h(N) → ∞`, the
quarter-wave lower bounds and the two-chain upper bound squeeze the one-gap inverse constant:

`K_{h(N)+1}(N)/(log₂ N)² → 4 max(α, 1-α)²/π²`.
-/

open Finset Filter Topology RHTower GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

private theorem max_sq_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    max (a ^ 2) (b ^ 2) = max a b ^ 2 := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (pow_le_pow_left₀ ha h 2)]
  · rw [max_eq_left h, max_eq_left (pow_le_pow_left₀ hb h 2)]

private theorem tendsto_natLog_real :
    Tendsto (fun N : ℕ => (Nat.log 2 N : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp
    (tendsto_atTop_atTop.mpr fun M => ⟨2 ^ M, fun N hN => Nat.le_log_of_pow_le (by norm_num) hN⟩)

/-- `(2h + c)/L → 2α` and `(2(L - h) + c)/L → 2(1 - α)` when `h/L → α`. -/
private theorem tendsto_affine_ratios {α : ℝ} {h : ℕ → ℕ}
    (hratio : Tendsto (fun N => (h N : ℝ) / Nat.log 2 N) atTop (𝓝 α)) (c : ℝ) :
    Tendsto (fun N : ℕ => (2 * (h N : ℝ) + c) / Nat.log 2 N) atTop (𝓝 (2 * α)) ∧
      Tendsto (fun N : ℕ => (2 * ((Nat.log 2 N : ℝ) - h N) + c) / Nat.log 2 N) atTop
        (𝓝 (2 * (1 - α))) := by
  have hc : Tendsto (fun N : ℕ => c / (Nat.log 2 N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natLog_real
  have hpos : ∀ᶠ N : ℕ in atTop, (0 : ℝ) < Nat.log 2 N :=
    tendsto_natLog_real.eventually (eventually_gt_atTop 0)
  constructor
  · have := (hratio.const_mul 2).add hc
    rw [add_zero] at this
    refine this.congr' ?_
    filter_upwards [hpos] with N hN
    field_simp
  · have := ((tendsto_const_nhds (x := (2 : ℝ))).sub (hratio.const_mul 2)).add hc
    rw [add_zero, show 2 - 2 * α = 2 * (1 - α) by ring] at this
    refine this.congr' ?_
    filter_upwards [hpos] with N hN
    field_simp

/-- **Position law (normalized by `⌊log₂ N⌋`).** -/
theorem fermiGapInverseConstant_position_law_natLog {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    {h : ℕ → ℕ} (hlt : ∀ᶠ N in atTop, h N < Nat.log 2 N) (hinf : Tendsto h atTop atTop)
    (hratio : Tendsto (fun N => (h N : ℝ) / Nat.log 2 N) atTop (𝓝 α)) :
    Tendsto (fun N => fermiGapInverseConstant N (h N + 1) / (Nat.log 2 N : ℝ) ^ 2) atTop
      (𝓝 (max (2 * α) (2 * (1 - α)) ^ 2 / Real.pi ^ 2)) := by
  have hπ := Real.pi_pos
  have hLpos : ∀ᶠ N : ℕ in atTop, (0 : ℝ) < Nat.log 2 N :=
    tendsto_natLog_real.eventually (eventually_gt_atTop 0)
  set T := max (2 * α) (2 * (1 - α)) ^ 2 / Real.pi ^ 2 with hT
  rw [tendsto_order]
  constructor
  · -- lower: the two quarter waves
    intro a ha
    obtain ⟨hb3, -⟩ := tendsto_affine_ratios hratio 3
    obtain ⟨-, ht1⟩ := tendsto_affine_ratios hratio 1
    have hinvL : Tendsto (fun N : ℕ => 8 / (Nat.log 2 N : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natLog_real
    have hfb := ((hb3.pow 2).sub ((hb3).mul hinvL))
    have hft := ((ht1.pow 2).sub ((ht1).mul hinvL))
    simp only [mul_zero, sub_zero] at hfb hft
    have hlow := ((hfb.max hft).div_const (Real.pi ^ 2))
    rw [max_sq_of_nonneg (by linarith) (by linarith)] at hlow
    filter_upwards [hlow.eventually (eventually_gt_nhds ha), hlt, hLpos,
      eventually_ge_atTop 1] with N hN hNlt hL hN1
    set L := Nat.log 2 N
    have hLN : 2 ^ L ≤ N := Nat.pow_log_le_self 2 (by omega)
    have hbot := fermiGapInverseConstant_ge_bottom hLN hNlt
    have htop := fermiGapInverseConstant_ge_top hLN hNlt
    have hc1 : (((h N + 1 : ℕ) : ℝ)) = (h N : ℝ) + 1 := by push_cast; ring
    have hc2 : (((L - h N : ℕ) : ℝ)) = (L : ℝ) - h N := by
      rw [Nat.cast_sub hNlt.le]
    rw [hc1] at hbot
    rw [hc2] at htop
    set xb : ℝ := 2 * (h N : ℝ) + 3
    set xt : ℝ := 2 * ((L : ℝ) - h N) + 1
    have eb : 2 * ((h N : ℝ) + 1) + 1 = xb := by simp only [xb]; ring
    rw [eb] at hbot
    have hK : max (xb ^ 2 - 8 * xb) (xt ^ 2 - 8 * xt) / Real.pi ^ 2 ≤
        fermiGapInverseConstant N (h N + 1) := by
      rw [div_le_iff₀ (by positivity)]
      exact max_le ((div_le_iff₀ (by positivity)).mp hbot) ((div_le_iff₀ (by positivity)).mp htop)
    have e : max ((xb / L) ^ 2 - xb / L * (8 / L)) ((xt / L) ^ 2 - xt / L * (8 / L)) /
        Real.pi ^ 2 = max (xb ^ 2 - 8 * xb) (xt ^ 2 - 8 * xt) / Real.pi ^ 2 / (L : ℝ) ^ 2 := by
      have h1 : (xb / L) ^ 2 - xb / L * (8 / L) = (xb ^ 2 - 8 * xb) / (L : ℝ) ^ 2 := by
        field_simp
      have h2 : (xt / L) ^ 2 - xt / L * (8 / L) = (xt ^ 2 - 8 * xt) / (L : ℝ) ^ 2 := by
        field_simp
      rw [h1, h2, max_div_div_right (by positivity : (0 : ℝ) ≤ (L : ℝ) ^ 2)]
      ring
    rw [e] at hN
    calc a < max (xb ^ 2 - 8 * xb) (xt ^ 2 - 8 * xt) / Real.pi ^ 2 / (L : ℝ) ^ 2 := hN
      _ ≤ _ := div_le_div_of_nonneg_right hK (by positivity)
  · -- upper: the two-chain bound with a large fixed cutoff
    intro b hb
    set M2 := max (2 * α) (2 * (1 - α))
    have hM1 : 1 ≤ M2 := by
      rcases le_total α (1 / 2) with h' | h'
      · exact le_max_of_le_right (by linarith)
      · exact le_max_of_le_left (by linarith)
    have hT0 : 0 < T := by simp only [hT]; positivity
    have hbT : 1 < b / T := by rw [lt_div_iff₀ hT0]; linarith
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (show 0 < b / T - 1 by linarith)
      (show (1 / 2 : ℝ) < 1 by norm_num)
    have hfac : (1 + 1 / (2 : ℝ) ^ (m + 1)) * T < b := by
      have hle : 1 / (2 : ℝ) ^ (m + 1) ≤ (1 / 2 : ℝ) ^ m := by
        rw [one_div_pow]
        exact one_div_le_one_div_of_le (by positivity)
          (pow_le_pow_right₀ (by norm_num) (by omega))
      have : 1 + 1 / (2 : ℝ) ^ (m + 1) < b / T := by linarith
      rwa [lt_div_iff₀ hT0] at this
    obtain ⟨hb1, -⟩ := tendsto_affine_ratios hratio (2 * (m : ℝ) + 5)
    obtain ⟨-, ht7⟩ := tendsto_affine_ratios hratio 7
    have h2L : Tendsto (fun N : ℕ => 2 / (Nat.log 2 N : ℝ) ^ 2) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop ((tendsto_pow_atTop two_ne_zero).comp tendsto_natLog_real)
    have hup := ((((hb1.max ht7).pow 2).add h2L).const_mul (1 + 1 / (2 : ℝ) ^ (m + 1))).div_const
      (Real.pi ^ 2)
    rw [add_zero, mul_div_assoc] at hup
    have hlim : (1 + 1 / (2 : ℝ) ^ (m + 1)) * (M2 ^ 2 / Real.pi ^ 2) < b := by
      simpa [hT] using hfac
    filter_upwards [hup.eventually (eventually_lt_nhds hlim), hlt, hLpos,
      hinf.eventually (eventually_ge_atTop m), eventually_ge_atTop 1] with N hN hNlt hL hmN hN1
    set L := Nat.log 2 N
    have hK := fermiGapInverseConstant_le_explicit N hmN hNlt.le
    have hc1 : 2 * ((h N + m + 2 : ℕ) : ℝ) + 1 = 2 * (h N : ℝ) + (2 * (m : ℝ) + 5) := by
      push_cast; ring
    have hc2 : 2 * ((L - h N + 3 : ℕ) : ℝ) + 1 = 2 * ((L : ℝ) - h N) + 7 := by
      rw [Nat.cast_add, Nat.cast_sub hNlt.le]; push_cast; ring
    rw [hc1, hc2] at hK
    set A := 2 * (h N : ℝ) + (2 * (m : ℝ) + 5)
    set B := 2 * ((L : ℝ) - h N) + 7
    have e : (1 + 1 / (2 : ℝ) ^ (m + 1)) * (max (A / L) (B / L) ^ 2 + 2 / (L : ℝ) ^ 2) /
        Real.pi ^ 2 = (1 + 1 / (2 : ℝ) ^ (m + 1)) * (max A B ^ 2 + 2) / Real.pi ^ 2 /
          (L : ℝ) ^ 2 := by
      rw [max_div_div_right hL.le]
      field_simp
    rw [e] at hN
    calc fermiGapInverseConstant N (h N + 1) / (L : ℝ) ^ 2
        ≤ (1 + 1 / (2 : ℝ) ^ (m + 1)) * (max A B ^ 2 + 2) / Real.pi ^ 2 / (L : ℝ) ^ 2 :=
          div_le_div_of_nonneg_right hK (by positivity)
      _ < b := hN

private theorem tendsto_natLog_sq_div_logb_sq :
    Tendsto (fun N : ℕ => (Nat.log 2 N : ℝ) ^ 2 / (Real.logb 2 N) ^ 2) atTop (𝓝 1) := by
  have hlow : Tendsto (fun N : ℕ => (Nat.log 2 N : ℝ) / ((Nat.log 2 N : ℝ) + 1)) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).sub
      ((tendsto_const_nhds (x := (1 : ℝ))).div_atTop
        (tendsto_atTop_add_const_right _ 1 tendsto_natLog_real))
    rw [sub_zero] at h
    refine h.congr' ?_
    filter_upwards [tendsto_natLog_real.eventually (eventually_gt_atTop 0)] with N hN
    field_simp; ring
  have hratio : Tendsto (fun N : ℕ => (Nat.log 2 N : ℝ) / Real.logb 2 N) atTop (𝓝 1) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
    · filter_upwards [eventually_ge_atTop 2] with N hN
      have h1 : (2 : ℝ) ^ Nat.log 2 N ≤ N := by exact_mod_cast Nat.pow_log_le_self 2 (by omega)
      have h2 : (N : ℝ) < (2 : ℝ) ^ (Nat.log 2 N + 1) := by
        exact_mod_cast Nat.lt_pow_succ_log_self (by norm_num) N
      have hlb := Real.logb_lt_logb (b := 2) (by norm_num) (by positivity) h2
      rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at hlb
      push_cast at hlb
      have hpos : 0 < Real.logb 2 N := Real.logb_pos (by norm_num) (by exact_mod_cast hN)
      exact div_le_div_of_nonneg_left (by positivity) hpos hlb.le
    · filter_upwards [eventually_ge_atTop 2] with N hN
      have h1 : (2 : ℝ) ^ Nat.log 2 N ≤ N := by exact_mod_cast Nat.pow_log_le_self 2 (by omega)
      have hl := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) h1
      rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at hl
      have hpos : 0 < Real.logb 2 N := Real.logb_pos (by norm_num) (by exact_mod_cast hN)
      rw [div_le_one hpos]; exact hl
  have := hratio.pow 2
  rw [one_pow] at this
  refine this.congr' ?_
  filter_upwards with N
  rw [div_pow]

/-- **Position law of a one-gap Fermi schedule.** If the gap level `h(N) + 1` lies at relative
depth `h(N)/⌊log₂ N⌋ → α` with `h(N) → ∞`, then
`K_{h(N)+1}(N)/(log₂ N)² → 4 max(α, 1-α)²/π²`. -/
theorem fermiGapInverseConstant_position_law {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    {h : ℕ → ℕ} (hlt : ∀ᶠ N in atTop, h N < Nat.log 2 N) (hinf : Tendsto h atTop atTop)
    (hratio : Tendsto (fun N => (h N : ℝ) / Nat.log 2 N) atTop (𝓝 α)) :
    Tendsto (fun N => fermiGapInverseConstant N (h N + 1) / (Real.logb 2 N) ^ 2) atTop
      (𝓝 (4 * max α (1 - α) ^ 2 / Real.pi ^ 2)) := by
  have hlaw := (fermiGapInverseConstant_position_law_natLog hα0 hα1 hlt hinf hratio).mul
    tendsto_natLog_sq_div_logb_sq
  have hval : max (2 * α) (2 * (1 - α)) ^ 2 / Real.pi ^ 2 * 1 =
      4 * max α (1 - α) ^ 2 / Real.pi ^ 2 := by
    rw [mul_one, show 2 * (1 - α) = 2 * (1 - α) from rfl,
      ← mul_max_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]; ring
  rw [hval] at hlaw
  refine hlaw.congr' ?_
  filter_upwards [tendsto_natLog_real.eventually (eventually_gt_atTop 0)] with N hN
  field_simp

/-- **A quarter-depth gap.** At relative depth `1/4` the price is `9/(4π²)`, between the free
middle gap (`1/π²`) and the edge (`4/π²`). -/
theorem fermiQuarterGapInverseConstant_logb_limit :
    Tendsto (fun N : ℕ => fermiGapInverseConstant N (Nat.log 2 N / 4 + 1) / (Real.logb 2 N) ^ 2)
      atTop (𝓝 (9 / (4 * Real.pi ^ 2))) := by
  have hlaw := fermiGapInverseConstant_position_law (α := 1 / 4) (by norm_num) (by norm_num)
    (h := fun N => Nat.log 2 N / 4)
    (by filter_upwards [eventually_ge_atTop 2] with N hN
        have : 1 ≤ Nat.log 2 N := Nat.le_log_of_pow_le (by norm_num) (by simpa using hN)
        omega)
    ((Nat.tendsto_div_const_atTop (by norm_num)).comp
      (tendsto_atTop_atTop.mpr fun M => ⟨2 ^ M, fun N hN => Nat.le_log_of_pow_le (by norm_num) hN⟩))
    (by
      have hq : Tendsto (fun N : ℕ => (Nat.log 2 N : ℝ) / 4 / Nat.log 2 N - 1 / (Nat.log 2 N : ℝ))
          atTop (𝓝 (1 / 4 - 0)) := by
        refine Tendsto.sub ?_ (tendsto_const_nhds.div_atTop tendsto_natLog_real)
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [tendsto_natLog_real.eventually (eventually_gt_atTop 0)] with N hN
        field_simp
      rw [sub_zero] at hq
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hq tendsto_const_nhds ?_ ?_
      · filter_upwards [tendsto_natLog_real.eventually (eventually_gt_atTop 0)] with N hN
        rw [sub_le_iff_le_add, ← add_div, div_le_div_iff_of_pos_right hN]
        have := Nat.lt_div_mul_add (a := Nat.log 2 N) (show 0 < 4 by norm_num)
        have h4 : ((Nat.log 2 N / 4 : ℕ) : ℝ) * 4 + 4 > Nat.log 2 N := by exact_mod_cast this
        linarith
      · filter_upwards [tendsto_natLog_real.eventually (eventually_gt_atTop 0)] with N hN
        rw [div_le_iff₀ hN]
        have := Nat.div_mul_le_self (Nat.log 2 N) 4
        have h4 : ((Nat.log 2 N / 4 : ℕ) : ℝ) * 4 ≤ Nat.log 2 N := by exact_mod_cast this
        linarith)
  rw [show (4 : ℝ) * max (1 / 4) (1 - 1 / 4) ^ 2 / Real.pi ^ 2 = 9 / (4 * Real.pi ^ 2) by
    rw [max_eq_right (by norm_num)]; field_simp; ring] at hlaw
  exact hlaw

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
