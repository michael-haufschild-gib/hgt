import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TerminalPrimeBoundaryMassHasFiniteSupport

/-!
# Terminal upward-row replacement disappears

Retaining the finite boundary-prime mass gives an integrated row error
of order `c⁴/N`. The estimate is uniform over the overlap and horizon;
its constant depends only on the fixed profile, receiver and conductor.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Finset Filter Topology

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open RenormalizedArithmeticPotentialTheory
  RenormalizedArithmeticPotentialTheory.CompletedShell CriticalArithmeticCorrelationTheory

local notation "Λ" => ArithmeticFunction.vonMangoldt

private theorem upwardLinearError_le_cubic {φ : ℝ → ℝ}
    (hM : 0 ≤ ∫ u, φ u ^ 2) {c L : ℝ} (hc : 1 ≤ c) (hL : 0 ≤ L)
    {H : ℕ} (hH : (H : ℝ) ≤ 3 * c) :
    upwardLinearError φ c L H ≤ (12 * (∫ u, φ u ^ 2) + 72 * L) * c ^ 3 := by
  have hc0 : 0 ≤ c := zero_le_one.trans hc
  have hc23 : c ^ 2 ≤ c ^ 3 := by
    have hh := mul_le_mul_of_nonneg_left hc (sq_nonneg c)
    nlinarith only [hh]
  have hH2 := pow_le_pow_left₀ (Nat.cast_nonneg H) hH 2
  have h₁ := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hH (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hc0)) hM
  have h₂ := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hH2 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) hc0)) hL
  have h₃ := mul_le_mul_of_nonneg_left hc23 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 12) hM)
  unfold upwardLinearError
  nlinarith only [h₁, h₂, h₃]

private theorem abs_upward_log_factor_le {c : ℝ} (hc : 1 ≤ c) :
    |Real.log (2 / (1 / (2 * c))) + mertensWindowConstant| ≤
      (Real.log 4 + 1 + |mertensWindowConstant|) * c := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hlogc : 0 ≤ Real.log c := Real.log_nonneg hc
  have hlog4 : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
  have harg : 2 / (1 / (2 * c)) = 4 * c := by field_simp [hc0.ne']; ring
  rw [harg, Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hc0.ne']
  calc
    _ ≤ |Real.log 4| + |Real.log c| + |mertensWindowConstant| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ = Real.log 4 + Real.log c + |mertensWindowConstant| := by
      rw [abs_of_nonneg hlog4, abs_of_nonneg hlogc]
    _ ≤ _ := by
      have h₁ := mul_le_mul_of_nonneg_left hc hlog4
      have h₂ := mul_le_mul_of_nonneg_left hc (abs_nonneg mertensWindowConstant)
      have h₃ := Real.log_le_sub_one_of_pos hc0
      nlinarith only [h₁, h₂, h₃]

/-- The literal terminal row replacement has a quartic-over-horizon bound at every overlap. -/
theorem exists_terminal_upward_replacement_quartic_bound
    {φ F : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {B δ : ℝ} (hδ : 0 < δ) (hF : ∀ x, |F x| ≤ B)
    (hzero : ∀ x, x ≤ δ → F x = 0) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c : ℝ, 1 ≤ c → ∀ N H : ℕ, 1 ≤ N →
      2 * c ≤ H → (H : ℝ) ≤ 3 * c → 4 * c * H ≤ N → 2 * H ≤ N →
      |(∑ n ∈ Icc 1 N, F ((n : ℝ) / N) / n *
        (upwardModeRow φ c N m n - upwardModel φ c N m H n)) / c| ≤ C * c ^ 4 / N := by
  obtain ⟨L, hL, hGL⟩ := exists_shellAutocorr_lipschitz hφ hsupp
  let M : ℝ := ∫ u, φ u ^ 2
  let K : ℕ := ⌈2 / δ⌉₊
  let P : ℝ := ∑ k ∈ Icc 1 K, (Λ k : ℝ) / k
  let Cφ : ℝ := 12 * M + 72 * L
  let C₀ : ℝ := Real.log 4 + 1 + |mertensWindowConstant|
  let C₁ : ℝ := 6 * m.totient * Cφ * C₀ / M
  let C₂ : ℝ := 63 * B * m.totient * P / δ
  have hM0 : 0 < M := hM
  have hB : 0 ≤ B := (abs_nonneg _).trans (hF 0)
  have hP : 0 ≤ P := sum_nonneg fun k _ => vonMangoldt_div_nonneg k
  have hCφ : 0 ≤ Cφ := by dsimp only [Cφ, M]; positivity
  have hC₀ : 0 ≤ C₀ := by
    dsimp only [C₀]
    have hh : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
    positivity
  have hC₁ : 0 ≤ C₁ := by dsimp only [C₁]; positivity
  have hC₂ : 0 ≤ C₂ := by dsimp only [C₂]; positivity
  refine ⟨B / δ * C₁ + C₂, add_nonneg (mul_nonneg (div_nonneg hB hδ.le) hC₁) hC₂, ?_⟩
  intro c hc N H hN hHlo hHhi hNH hHN
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hH1 : 1 ≤ H := by
    have hh : (1 : ℝ) ≤ H := by linarith only [hc, hHlo]
    exact_mod_cast hh
  have ha : 0 < 1 / (2 * c) := by positivity
  have ha1 : 1 / (2 * c) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith only [hc])
  have hac : (1 / (2 * c)) * (2 * c) ≤ 1 := by field_simp [hc0.ne'] <;> norm_num
  have hb := abs_terminal_upward_row_sub_model_le (m := m) hφ hsupp hM hδ hF hzero hc0 hL hGL
    hN hH1 hHlo hNH hHN (show 2 / δ ≤ (K : ℝ) from Nat.le_ceil _) ha ha1 hac
  have hE : upwardLinearError φ c L H ≤ Cφ * c ^ 3 := upwardLinearError_le_cubic hM.le hc hL hHhi
  have hE0 : 0 ≤ upwardLinearError φ c L H := by unfold upwardLinearError; positivity
  have hlog := abs_upward_log_factor_le hc
  change |Real.log (2 / (1 / (2 * c))) + mertensWindowConstant| ≤ C₀ * c at hlog
  have hA : |H * m.totient * (2 * upwardLinearError φ c L H / (M * N)) *
      (Real.log (2 / (1 / (2 * c))) + mertensWindowConstant)| ≤ C₁ * c ^ 5 / N := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (H : ℝ) * m.totient *
      (2 * upwardLinearError φ c L H / (M * N)))]
    calc
      _ ≤ ((3 * c) * m.totient * (2 * (Cφ * c ^ 3) / (M * N))) * (C₀ * c) :=
        mul_le_mul
          (mul_le_mul (mul_le_mul_of_nonneg_right hHhi (Nat.cast_nonneg _))
            (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hE (by norm_num)) (by positivity))
            (by positivity) (by positivity)) hlog (abs_nonneg _) (by positivity)
      _ = _ := by dsimp only [C₁]; field_simp [hM.ne', hN0.ne'] <;> ring
  have hHb : (2 : ℝ) * H + 1 ≤ 7 * c := by linarith only [hHhi, hc]
  have hboundary : 3 * H * m.totient * (B * (2 * H + 1) / (δ * N)) * P ≤ C₂ * c ^ 2 / N := by
    calc
      _ ≤ (3 * (3 * c) * m.totient) * (B * (7 * c) / (δ * N)) * P :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hHhi (by norm_num)) (Nat.cast_nonneg _))
            (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hHb hB) (by positivity))
            (by positivity) (by positivity)) hP
      _ = _ := by dsimp only [C₂]; field_simp [hδ.ne', hN0.ne'] <;> ring
  have hraw := hb.trans (add_le_add (mul_le_mul_of_nonneg_left hA (div_nonneg hB hδ.le)) hboundary)
  rw [abs_div, abs_of_pos hc0]
  apply (div_le_div_of_nonneg_right hraw hc0.le).trans
  have hc14 : c ≤ c ^ 4 := by nlinarith only [hc, sq_nonneg (c ^ 2 - 1), sq_nonneg (c - 1)]
  calc
    _ = (B / δ * C₁) * c ^ 4 / N + C₂ * c / N := by field_simp [hc0.ne', hN0.ne'] <;> ring
    _ ≤ (B / δ * C₁) * c ^ 4 / N + C₂ * c ^ 4 / N :=
      add_le_add le_rfl (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hc14 hC₂) hN0.le)
    _ = _ := by ring

/-- Every subquartic overlap clock makes the terminal actual-to-model replacement vanish. -/
theorem tendsto_terminal_upward_row_sub_model
    {φ F : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {B δ : ℝ} (hδ : 0 < δ) (hF : ∀ x, |F x| ≤ B)
    (hzero : ∀ x, x ≤ δ → F x = 0) (m : ℕ)
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N)
    (hc4 : Tendsto (fun N : ℕ => c N ^ 4 / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Icc 1 N, F ((n : ℝ) / N) / n *
        (upwardModeRow φ (c N) N m n - upwardModel φ (c N) N m ⌈2 * c N⌉₊ n)) / c N)
      atTop (𝓝 0) := by
  obtain ⟨C, _, hbound⟩ := exists_terminal_upward_replacement_quartic_bound hφ hsupp hM hδ hF hzero m
  have hlim := hc4.const_mul C
  simp only [mul_zero] at hlim
  apply squeeze_zero_norm' _ hlim
  filter_upwards [eventually_ge_atTop 1,
    hc4.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 12))] with N hN hsmall
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hc0 : 0 < c N := zero_lt_one.trans_le (hc N)
  let H : ℕ := ⌈2 * c N⌉₊
  have hHlo : 2 * c N ≤ (H : ℝ) := Nat.le_ceil _
  have hHhi : (H : ℝ) ≤ 3 * c N := by
    have hh : (H : ℝ) < 2 * c N + 1 := Nat.ceil_lt_add_one (by positivity)
    linarith only [hh, hc N]
  have hc14 : c N ≤ c N ^ 4 := by
    nlinarith only [hc N, sq_nonneg (c N ^ 2 - 1), sq_nonneg (c N - 1)]
  have hc24 : c N ^ 2 ≤ c N ^ 4 := by
    nlinarith only [hc N, sq_nonneg (c N ^ 2 - 1), sq_nonneg (c N - 1)]
  have hsmallN : 12 * c N ^ 4 ≤ (N : ℝ) := by
    have hh := (div_lt_iff₀ hN0).mp hsmall
    linarith only [hh]
  have hNH : 4 * c N * H ≤ (N : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hHhi (by positivity : 0 ≤ 4 * c N)
    nlinarith only [hh, hc24, hsmallN]
  have hHN : 2 * H ≤ N := by
    have hh : (2 : ℝ) * H ≤ N := by
      nlinarith only [hHhi, hc14, hsmallN, pow_nonneg hc0.le 4]
    exact_mod_cast hh
  rw [Real.norm_eq_abs]
  exact (hbound (c N) (hc N) N H hN hHlo hHhi hNH hHN).trans_eq (by ring)

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.exists_terminal_upward_replacement_quartic_bound
#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.tendsto_terminal_upward_row_sub_model
