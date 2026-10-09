import GaloisForLFunctions.RHTower.Sieve.UnitBlockReflectionDualBlocks

/-!
# The twisted fourth moment of a unit block beyond the square-root range

Let `√T < N < T` and `Y = T/(2πN) ≥ 11`.  Put `M = ⌊T/(4π(N' + ¼))⌋`.  For `t ∈ [T/2, T]` the
reflection, the dual decomposition into the blocks `(M, 2M]`, `(2M, 4M]`, `(4M, 8M]` and Perron's
formula at height `U = T/4` give

`|U_N(t)| ≤ C₀((1 + log T)/N + T^{-1/2}) + 22 (Y/√T) ∑_B P_B(t)`,
`P_B(t) = ∫_{-U}^{U} |U_B(u − t)| du/|1 + iu|`  (`exists_norm_mtWattUnitBlock_le_perronMass`).

Hölder against the Perron weight (mass `W ≤ 4 log(1 + T/4)`), Fubini, the conjugation symmetry of
`U_B`, the shift-to-twist identity and the three-window cover then reduce
`∫_{T/2}^{T} |U_N|⁴|𝒜|²` to fourth moments of the short dual blocks `U_B`, `B² ≤ T/2`, against
twisted coefficient blocks on the windows `[T'/2, T']`, `T' ∈ {T/2, T, 5T/4}`
(`exists_integral_unitBlock_fourth_le_dual`).
-/

open Complex Set MeasureTheory Filter
open GaloisForLFunctions.HTGeometry
open scoped Real

namespace RHTower.Sieve

noncomputable section

/-- The Perron mass of the unit block `(B, 2B]` at height `t`. -/
def ubPerronMass (B : ℕ) (U t : ℝ) : ℝ :=
  ∫ u in (-U)..U, ‖mtWattUnitBlock B (2 * B) (u - t)‖ / ‖(1 : ℂ) + (u : ℂ) * I‖

theorem ubPerronMass_nonneg (B : ℕ) {U : ℝ} (hU : 0 ≤ U) (t : ℝ) : 0 ≤ ubPerronMass B U t :=
  intervalIntegral.integral_nonneg (by linarith) fun _ _ => by positivity

/-- The dual block length `M = ⌊T/(4π(N' + ¼))⌋`. -/
def ubDualBase (N' : ℕ) (T : ℝ) : ℕ := ⌊T / (4 * π * ((N' : ℝ) + 1 / 4))⌋₊

/-- **The dual sum by three Perron masses.**  If `M ≤ m₁`, `−1 ≤ m₂ ≤ 8M` and every cutoff weight
`(m₁ + min(m₂, 2B) + 1)/2π` is at most `c`, then the sum over `[m₁ + 1, m₂]` is bounded by `c`
times the three Perron masses plus `2100 M²/U`. -/
theorem norm_sum_Icc_le_perronMass {M : ℕ} (hM : 1 ≤ M) {m₁ m₂ : ℤ} (hm₁M : (M : ℤ) ≤ m₁)
    (hm₂M : m₂ ≤ 8 * M) (hm₂lo : -1 ≤ m₂) {c : ℝ}
    (hc : ∀ B : ℕ, ((m₁ : ℝ) + min (m₂ : ℝ) (2 * B) + 1) / (2 * π) ≤ c) {U t : ℝ} (hU : 0 < U) :
    ‖∑ k ∈ Finset.Icc (m₁ + 1) m₂, (k : ℂ) ^ ((t : ℂ) * I)‖ ≤
      c * (ubPerronMass M U t + ubPerronMass (2 * M) U t + ubPerronMass (4 * M) U t) +
        2100 * (M : ℝ) ^ 2 / U := by
  have hm₁0 : 0 ≤ m₁ := le_trans (by positivity) hm₁M
  rw [sum_Icc_eq_blocks (fun k : ℤ => (k : ℂ) ^ ((t : ℂ) * I)) hm₁M hm₂M]
  simp only [Int.cast_natCast]
  have b1 := norm_sum_filter_block_le (B := M) hM hm₁0 hm₂lo (U := U) (τ := t) hU
  have b2 := norm_sum_filter_block_le (B := 2 * M) (by omega) hm₁0 hm₂lo (U := U) (τ := t) hU
  have b3 := norm_sum_filter_block_le (B := 4 * M) (by omega) hm₁0 hm₂lo (U := U) (τ := t) hU
  rw [show 2 * (2 * M) = 4 * M by ring] at b2
  rw [show 2 * (4 * M) = 8 * M by ring] at b3
  have p1 := ubPerronMass_nonneg M hU.le t
  have p2 := ubPerronMass_nonneg (2 * M) hU.le t
  have p3 := ubPerronMass_nonneg (4 * M) hU.le t
  unfold ubPerronMass at p1 p2 p3 ⊢
  rw [show 2 * (2 * M) = 4 * M by ring] at p2 ⊢
  rw [show 2 * (4 * M) = 8 * M by ring] at p3 ⊢
  have c1 := mul_le_mul_of_nonneg_right (hc M) p1
  have c2 := mul_le_mul_of_nonneg_right (hc (2 * M)) p2
  have c3 := mul_le_mul_of_nonneg_right (hc (4 * M)) p3
  push_cast at b1 b2 b3 c1 c2 c3
  refine le_trans (norm_add_le _ _) (le_trans (add_le_add (norm_add_le _ _) le_rfl) ?_)
  have e : 2100 * (M : ℝ) ^ 2 / U = 100 * (M : ℝ) ^ 2 / U + 100 * (2 * (M : ℝ)) ^ 2 / U +
      100 * (4 * (M : ℝ)) ^ 2 / U := by ring
  rw [e, mul_add, mul_add]
  linarith

/-- The dual base sits between `2Y/9` and `Y/2`, `Y = T/(2πN)`. -/
theorem ubDualBase_bounds {T N N' : ℝ} (hT : 0 < T) (hN : 1 ≤ N) (hNN' : N + 1 ≤ N')
    (hN' : N' ≤ 2 * N) :
    2 * (T / (2 * π * N)) / 9 ≤ T / (4 * π * (N' + 1 / 4)) ∧
      T / (4 * π * (N' + 1 / 4)) ≤ T / (2 * π * N) / 2 := by
  have hπ := Real.pi_pos
  have hN0 : 0 < N := by linarith
  have hd : 0 < 4 * π * (N' + 1 / 4) := mul_pos (by positivity) (by linarith)
  constructor
  · rw [show 2 * (T / (2 * π * N)) / 9 = T / (9 * π * N) by field_simp]
    exact div_le_div_of_nonneg_left hT.le hd (by nlinarith)
  · rw [show T / (2 * π * N) / 2 = T / (4 * π * N) by field_simp; norm_num]
    exact div_le_div_of_nonneg_left hT.le (by positivity) (by nlinarith)

/-- The final arithmetic of the pointwise bound, over plain reals. -/
private theorem ub_pointwise_combine {C N Y P S u L lt sT st M2 : ℝ} (hC : 0 < C) (hN : 0 < N)
    (hY : 0 ≤ Y) (hst0 : 0 < st) (hsT : 0 < sT) (hst : sT / 2 ≤ st) (hlog : lt ≤ L)
    (hlt : 0 ≤ lt) (hP : 0 ≤ P) (hS0 : 0 ≤ S)
    (hmain : u ≤ C * ((1 + lt) / N + 1 / st) + 23 / st * S)
    (hS : S ≤ 3 * Y / (2 * π) * P + M2) (hM2 : M2 ≤ 525) :
    u ≤ (2 * C + 25000) * ((1 + L) / N + 1 / sT) + 23 * Y / sT * P := by
  have hπ : 3 < π := Real.pi_gt_three
  have hinv : 1 / st ≤ 2 / sT := by
    rw [div_le_div_iff₀ hst0 hsT]; linarith
  have hE : C * ((1 + lt) / N + 1 / st) ≤ 2 * C * ((1 + L) / N + 1 / sT) := by
    have a1 : (1 + lt) / N ≤ (1 + L) / N := div_le_div_of_nonneg_right (by linarith) hN.le
    have a2 : 0 ≤ (1 + L) / N := div_nonneg (by linarith) hN.le
    have a3 : (1 + lt) / N + 1 / st ≤ 2 * ((1 + L) / N + 1 / sT) := by
      have : 2 / sT = 2 * (1 / sT) := by ring
      linarith
    calc C * ((1 + lt) / N + 1 / st) ≤ C * (2 * ((1 + L) / N + 1 / sT)) :=
          mul_le_mul_of_nonneg_left a3 hC.le
      _ = 2 * C * ((1 + L) / N + 1 / sT) := by ring
  have h23 : 23 / st ≤ 46 / sT := by
    have := mul_le_mul_of_nonneg_left hinv (by norm_num : (0 : ℝ) ≤ 23)
    rw [mul_one_div, show (23 : ℝ) * (2 / sT) = 46 / sT by ring] at this
    exact this
  have hM20 : 0 ≤ 3 * Y / (2 * π) * P + M2 := le_trans hS0 hS
  have hR : 23 / st * S ≤ 23 * Y / sT * P + 25000 / sT := by
    refine le_trans (mul_le_mul h23 hS hS0 (by positivity)) ?_
    have e1 : 46 / sT * (3 * Y / (2 * π) * P) ≤ 23 * Y / sT * P := by
      rw [← mul_assoc]
      refine mul_le_mul_of_nonneg_right ?_ hP
      rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) hsT]
      have : 46 * (3 * Y) ≤ 23 * Y * (2 * π) := by nlinarith
      nlinarith
    have e2 : 46 / sT * M2 ≤ 25000 / sT := by
      rw [mul_comm, ← mul_div_assoc]
      exact div_le_div_of_nonneg_right (by linarith) hsT.le
    rw [mul_add]
    linarith
  have hfin : 25000 / sT ≤ 25000 * ((1 + L) / N + 1 / sT) := by
    have : 0 ≤ (1 + L) / N := div_nonneg (by linarith) hN.le
    rw [mul_add, mul_one_div]; linarith
  have e : (2 * C + 25000) * ((1 + L) / N + 1 / sT) =
      2 * C * ((1 + L) / N + 1 / sT) + 25000 * ((1 + L) / N + 1 / sT) := by ring
  rw [e]
  linarith

/-- **The moving dual edges.**  For `t ∈ [T/2, T]`, `√T < N < T`, `Y = T/(2πN) ≥ 11` and
`M = ubDualBase N' T`, the dual frequencies are `[m₁ + 1, m₂] ∩ ℤ` with `M ≤ m₁`, `−1 ≤ m₂ ≤ 8M`
and cutoff weights at most `3Y/2π`; moreover `1 ≤ M ≤ Y/2`. -/
theorem ub_dual_edges {N N' : ℕ} (hN : 1 ≤ N) (hNN' : N < N') (hN' : N' ≤ 2 * N) {T : ℝ}
    (hNT : (N : ℝ) < T) (hY : 11 ≤ T / (2 * π * N)) {t : ℝ} (ht1 : T / 2 ≤ t) (ht2 : t ≤ T) :
    1 ≤ ubDualBase N' T ∧ (ubDualBase N' T : ℝ) ≤ T / (2 * π * N) / 2 ∧
      ∃ m₁ m₂ : ℤ, ubDual N N' t = Finset.Icc (m₁ + 1) m₂ ∧ (ubDualBase N' T : ℤ) ≤ m₁ ∧
        m₂ ≤ 8 * ubDualBase N' T ∧ -1 ≤ m₂ ∧
        ∀ B : ℕ, ((m₁ : ℝ) + min (m₂ : ℝ) (2 * B) + 1) / (2 * π) ≤
          3 * (T / (2 * π * N)) / (2 * π) := by
  have hπ : 3 < π := Real.pi_gt_three
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hNN'r : (N : ℝ) + 1 ≤ N' := by exact_mod_cast hNN'
  have hN'2 : (N' : ℝ) ≤ 2 * N := by exact_mod_cast hN'
  have hT0 : 0 < T := by linarith
  have ht0 : 0 < t := by linarith
  obtain ⟨hxlo, hxhi⟩ := ubDualBase_bounds hT0 hN1 hNN'r hN'2
  obtain ⟨Y, hYdef⟩ : ∃ Y, Y = T / (2 * π * N) := ⟨_, rfl⟩
  rw [← hYdef] at hY hxlo hxhi ⊢
  obtain ⟨x, hx⟩ : ∃ x, x = T / (4 * π * ((N' : ℝ) + 1 / 4)) := ⟨_, rfl⟩
  rw [← hx] at hxlo hxhi
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  have hMx : (ubDualBase N' T : ℝ) ≤ x := by rw [ubDualBase, ← hx]; exact Nat.floor_le hx0
  have hMx' : x - 1 < ubDualBase N' T := by rw [ubDualBase, ← hx]; exact Nat.sub_one_lt_floor x
  have hM1 : 1 ≤ ubDualBase N' T := by
    rw [ubDualBase, ← hx]; exact Nat.le_floor (by norm_num; linarith)
  refine ⟨hM1, hMx.trans hxhi, ?_⟩
  obtain ⟨M, hMdef⟩ : ∃ M, M = ubDualBase N' T := ⟨_, rfl⟩
  rw [← hMdef] at hMx hMx' ⊢
  obtain ⟨k₁, hk₁⟩ : ∃ k, k = t / (2 * π * ((N' : ℝ) + 1 / 4)) := ⟨_, rfl⟩
  obtain ⟨k₂, hk₂⟩ : ∃ k, k = t / (2 * π * ((N : ℝ) + 3 / 4)) := ⟨_, rfl⟩
  have hk₁x : x ≤ k₁ := by
    have e : x = (T / 2) / (2 * π * ((N' : ℝ) + 1 / 4)) := by rw [hx]; field_simp; ring
    rw [e, hk₁]
    exact div_le_div_of_nonneg_right ht1 (by positivity)
  have hk₂Y : k₂ ≤ Y := by
    rw [hk₂, hYdef]
    exact div_le_div₀ hT0.le ht2 (by positivity) (by nlinarith)
  have hk₂0 : 0 ≤ k₂ := by rw [hk₂]; positivity
  have hk₁k₂ : k₁ ≤ k₂ := by
    rw [hk₁, hk₂]; exact div_le_div_of_nonneg_left ht0.le (by positivity) (by nlinarith)
  refine ⟨⌈k₁ + 1⌉ - 1, ⌊k₂ - 1⌋, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ubDual, ← hk₁, ← hk₂]; congr 1; ring
  · have h1 : k₁ + 1 ≤ (⌈k₁ + 1⌉ : ℝ) := Int.le_ceil _
    have h2 : (M : ℝ) < ⌈k₁ + 1⌉ := by linarith
    have : (M : ℤ) < ⌈k₁ + 1⌉ := by exact_mod_cast h2
    omega
  · have hm₂r : ((⌊k₂ - 1⌋ : ℤ) : ℝ) ≤ k₂ - 1 := Int.floor_le _
    have : ((⌊k₂ - 1⌋ : ℤ) : ℝ) ≤ 8 * M := by linarith
    exact_mod_cast this
  · exact Int.le_floor.2 (by push_cast; linarith)
  · intro B
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    have hm₁r : ((⌈k₁ + 1⌉ - 1 : ℤ) : ℝ) ≤ k₁ + 1 := by
      have : (⌈k₁ + 1⌉ : ℝ) < k₁ + 1 + 1 := Int.ceil_lt_add_one _
      push_cast; linarith
    have hm₂r : ((⌊k₂ - 1⌋ : ℤ) : ℝ) ≤ k₂ - 1 := Int.floor_le _
    have := min_le_left ((⌊k₂ - 1⌋ : ℤ) : ℝ) (2 * B)
    linarith

/-- `T ≥ 60` and `Y² ≤ T/4` in the reflection range. -/
private theorem ub_range_facts {N T : ℝ} (hN : 1 ≤ N) (hTN : T < N ^ 2)
    (hY : 11 ≤ T / (2 * π * N)) : 60 ≤ T ∧ (T / (2 * π * N)) ^ 2 ≤ T / 4 := by
  have hπ : 3 < π := Real.pi_gt_three
  have hN0 : 0 < N := by linarith
  have hT0 : 0 < T := by
    have : 0 < T / (2 * π * N) := by linarith
    exact (div_pos_iff_of_pos_right (by positivity)).1 this
  constructor
  · have e : T = 2 * π * N * (T / (2 * π * N)) := by field_simp
    have h1 : 3 ≤ π * N := by nlinarith
    have h2 : 33 ≤ π * N * (T / (2 * π * N)) := by nlinarith
    rw [e]; linarith
  · rw [div_pow, div_le_iff₀ (by positivity)]
    have h1 : T * T < T * N ^ 2 := mul_lt_mul_of_pos_left hTN hT0
    have h2 : T * N ^ 2 ≤ T * N ^ 2 * π ^ 2 := le_mul_of_one_le_right (by positivity) (by nlinarith)
    have e : T / 4 * (2 * π * N) ^ 2 = T * N ^ 2 * π ^ 2 := by ring
    rw [e]; nlinarith

/-- **The pointwise bound by three Perron masses.** -/
theorem exists_norm_mtWattUnitBlock_le_perronMass :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (N N' : ℕ), 1 ≤ N → N < N' → N' ≤ 2 * N → ∀ T : ℝ, (N : ℝ) < T →
      T < (N : ℝ) ^ 2 → 11 ≤ T / (2 * π * N) → ∀ t ∈ Icc (T / 2) T,
      ‖mtWattUnitBlock N N' t‖ ≤ C₀ * ((1 + Real.log T) / N + 1 / Real.sqrt T) +
        23 * (T / (2 * π * N)) / Real.sqrt T *
          (ubPerronMass (ubDualBase N' T) (T / 4) t + ubPerronMass (2 * ubDualBase N' T) (T / 4) t +
            ubPerronMass (4 * ubDualBase N' T) (T / 4) t) := by
  obtain ⟨C, hC, hdual⟩ := exists_norm_mtWattUnitBlock_le_dual
  refine ⟨2 * C + 25000, by positivity, fun N N' hN hNN' hN' T hNT hTN hY t ht => ?_⟩
  obtain ⟨ht1, ht2⟩ := ht
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  obtain ⟨hM1, hMY, m₁, m₂, hD, hm₁M, hm₂M, hm₂lo, hcoef⟩ := ub_dual_edges hN hNN' hN' hNT hY ht1 ht2
  obtain ⟨hT60, hY2⟩ := ub_range_facts hN1 hTN hY
  have hT0 : 0 < T := by linarith
  have ht0 : 0 < t := by linarith
  have hU : (0 : ℝ) < T / 4 := by positivity
  have hS := norm_sum_Icc_le_perronMass hM1 hm₁M hm₂M hm₂lo hcoef (t := t) hU
  rw [← hD] at hS
  have hMconst : 2100 * (ubDualBase N' T : ℝ) ^ 2 / (T / 4) ≤ 525 := by
    rw [div_le_iff₀ hU]
    have h1 : (ubDualBase N' T : ℝ) ^ 2 ≤ (T / (2 * π * N) / 2) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hMY 2
    have h2 : (T / (2 * π * N) / 2) ^ 2 = (T / (2 * π * N)) ^ 2 / 4 := by ring
    linarith only [h1, h2, hY2]
  have hsT : 0 < Real.sqrt T := Real.sqrt_pos.2 hT0
  have hst : Real.sqrt T / 2 ≤ Real.sqrt t := by
    have : Real.sqrt (T / 4) = Real.sqrt T / 2 := by
      rw [Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 4), show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]
    calc Real.sqrt T / 2 = Real.sqrt (T / 4) := this.symm
      _ ≤ Real.sqrt t := Real.sqrt_le_sqrt (by linarith only [ht1, hT0])
  have hlog : Real.log t ≤ Real.log T := Real.log_le_log ht0 ht2
  have hlt : 0 ≤ Real.log t := Real.log_nonneg (by linarith only [ht1, hT60])
  have hmain := hdual N N' hN hNN' hN' t (by linarith only [ht1, hT60])
    (by nlinarith only [ht2, hTN]) (by linarith only [hNT, ht1])
  have hY0 : 0 ≤ T / (2 * π * N) := by linarith only [hY]
  have hPnn : 0 ≤ ubPerronMass (ubDualBase N' T) (T / 4) t +
      ubPerronMass (2 * ubDualBase N' T) (T / 4) t + ubPerronMass (4 * ubDualBase N' T) (T / 4) t := by
    have p1 := ubPerronMass_nonneg (ubDualBase N' T) hU.le t
    have p2 := ubPerronMass_nonneg (2 * ubDualBase N' T) hU.le t
    have p3 := ubPerronMass_nonneg (4 * ubDualBase N' T) hU.le t
    linarith only [p1, p2, p3]
  exact ub_pointwise_combine hC hN0 hY0 (Real.sqrt_pos.2 ht0) hsT hst hlog hlt hPnn
    (norm_nonneg _) hmain hS hMconst

/-! ## Hölder, Fubini and the twisted windows -/

theorem continuous_inv_norm_one_add : Continuous fun u : ℝ => 1 / ‖(1 : ℂ) + (u : ℂ) * I‖ := by
  refine continuous_const.div (by fun_prop) fun u => ?_
  rw [norm_one_add_mul_I]; exact (Real.sqrt_pos.2 (by positivity)).ne'

theorem inv_norm_one_add_nonneg (u : ℝ) : 0 ≤ 1 / ‖(1 : ℂ) + (u : ℂ) * I‖ := by positivity

/-- The fourth-moment Perron integrand `J_B(t) = ∫_{-U}^{U} |U_B(u − t)|⁴ du/|1 + iu|`. -/
def ubPerronFourth (B : ℕ) (U t : ℝ) : ℝ :=
  ∫ u in (-U)..U, ‖mtWattUnitBlock B (2 * B) (u - t)‖ ^ 4 * (1 / ‖(1 : ℂ) + (u : ℂ) * I‖)

/-- **Hölder against the Perron weight.**  `P_B(t)⁴ ≤ (4 log(1 + U))³ J_B(t)`. -/
theorem ubPerronMass_pow_four_le (B : ℕ) {U : ℝ} (hU : 0 ≤ U) (t : ℝ) :
    ubPerronMass B U t ^ 4 ≤ (4 * Real.log (1 + U)) ^ 3 * ubPerronFourth B U t := by
  have hf : Continuous fun u : ℝ => ‖mtWattUnitBlock B (2 * B) (u - t)‖ :=
    ((continuous_mtWattUnitBlock B (2 * B)).comp (continuous_id.sub continuous_const)).norm
  have h := intervalIntegral_mul_pow_four_le (a := -U) (b := U) (by linarith) hf
    continuous_inv_norm_one_add (fun _ => norm_nonneg _) inv_norm_one_add_nonneg
  have e : ubPerronMass B U t = ∫ u in (-U)..U,
      ‖mtWattUnitBlock B (2 * B) (u - t)‖ * (1 / ‖(1 : ℂ) + (u : ℂ) * I‖) := by
    rw [ubPerronMass]; exact intervalIntegral.integral_congr fun u _ => by rw [mul_one_div]
  rw [e, ubPerronFourth]
  refine le_trans h (mul_le_mul_of_nonneg_right ?_ ?_)
  · exact pow_le_pow_left₀ (intervalIntegral.integral_nonneg (by linarith) fun u _ =>
      inv_norm_one_add_nonneg u) (integral_inv_norm_one_add_le hU) 3
  · exact intervalIntegral.integral_nonneg (by linarith) fun u _ =>
      mul_nonneg (by positivity) (inv_norm_one_add_nonneg u)

/-- **A twisted window.**  If the fourth moments of `U_B` against every twist `a·m^{-iu}`,
`|u| ≤ T/4`, are at most `G` on the windows `[T'/2, T']`, `T' ∈ {T/2, T, 5T/4}`, then
`∫_{T/2}^{T} |U_B(u − t)|⁴ |𝒜_a(t)|² dt ≤ 3G` for every such `u`. -/
theorem integral_unitBlock_shift_le {B : ℕ} {a : ℕ → ℂ} {A : ℕ} {T G : ℝ} (hT : 0 < T)
    (hG : ∀ u : ℝ, |u| ≤ T / 4 → ∀ T' : ℝ, (T' = T / 2 ∨ T' = T ∨ T' = 5 * T / 4) →
      ∫ τ in (T' / 2)..T', ‖mtWattUnitBlock B (2 * B) τ‖ ^ 4 *
        ‖mtWattCoefficientBlock (mtTwist a u) A τ‖ ^ 2 ≤ G)
    {u : ℝ} (hu : |u| ≤ T / 4) :
    ∫ t in (T / 2)..T, ‖mtWattUnitBlock B (2 * B) (u - t)‖ ^ 4 *
      ‖mtWattCoefficientBlock a A t‖ ^ 2 ≤ 3 * G := by
  set Φ : ℝ → ℝ := fun τ => ‖mtWattUnitBlock B (2 * B) τ‖ ^ 4 *
    ‖mtWattCoefficientBlock (mtTwist a u) A τ‖ ^ 2 with hΦ
  have hΦc : Continuous Φ :=
    ((continuous_mtWattUnitBlock B (2 * B)).norm.pow 4).mul
      ((continuous_perronPoly _ _ _ : Continuous (mtWattCoefficientBlock (mtTwist a u) A)).norm.pow 2)
  have hpt : ∀ t : ℝ, ‖mtWattUnitBlock B (2 * B) (u - t)‖ ^ 4 *
      ‖mtWattCoefficientBlock a A t‖ ^ 2 = Φ (t - u) := by
    intro t
    rw [hΦ]
    dsimp only
    rw [show u - t = -(t - u) by ring, norm_mtWattUnitBlock_neg,
      ← mtWattCoefficientBlock_add, sub_add_cancel]
  simp_rw [hpt]
  refine le_trans (integral_comp_sub_le_three_windows hΦc (fun x => by positivity) hT hu) ?_
  have g1 := hG u hu (T / 2) (Or.inl rfl)
  have g2 := hG u hu T (Or.inr (Or.inl rfl))
  have g3 := hG u hu (5 * T / 4) (Or.inr (Or.inr rfl))
  rw [show T / 2 / 2 = T / 4 by ring] at g1
  rw [show 5 * T / 4 / 2 = 5 * T / 8 by ring] at g3
  linarith

/-- **Fubini for the Perron integrand.**  Under the window hypothesis,
`∫_{T/2}^{T} J_B(t) |𝒜_a(t)|² dt ≤ 3G·4 log(1 + T/4)`. -/
theorem integral_ubPerronFourth_mul_le {B : ℕ} {a : ℕ → ℂ} {A : ℕ} {T G : ℝ} (hT : 0 < T)
    (hG0 : 0 ≤ G)
    (hG : ∀ u : ℝ, |u| ≤ T / 4 → ∀ T' : ℝ, (T' = T / 2 ∨ T' = T ∨ T' = 5 * T / 4) →
      ∫ τ in (T' / 2)..T', ‖mtWattUnitBlock B (2 * B) τ‖ ^ 4 *
        ‖mtWattCoefficientBlock (mtTwist a u) A τ‖ ^ 2 ≤ G) :
    ∫ t in (T / 2)..T, ubPerronFourth B (T / 4) t * ‖mtWattCoefficientBlock a A t‖ ^ 2 ≤
      3 * G * (4 * Real.log (1 + T / 4)) := by
  have hV := continuous_mtWattUnitBlock B (2 * B)
  have hA : Continuous (mtWattCoefficientBlock a A) := continuous_perronPoly _ _ _
  have hw := continuous_inv_norm_one_add
  obtain ⟨F, hF⟩ : ∃ F : ℝ → ℝ → ℝ, F = fun t u => ‖mtWattUnitBlock B (2 * B) (u - t)‖ ^ 4 *
      (1 / ‖(1 : ℂ) + (u : ℂ) * I‖) * ‖mtWattCoefficientBlock a A t‖ ^ 2 := ⟨_, rfl⟩
  have hFc : Continuous (Function.uncurry F) := by
    rw [hF]
    exact (((hV.comp (continuous_snd.sub continuous_fst)).norm.pow 4).mul
      (hw.comp continuous_snd)).mul ((hA.comp continuous_fst).norm.pow 2)
  have hFc' : Continuous (Function.uncurry fun u t => F t u) := by
    rw [hF]
    exact (((hV.comp (continuous_fst.sub continuous_snd)).norm.pow 4).mul
      (hw.comp continuous_fst)).mul ((hA.comp continuous_snd).norm.pow 2)
  have e1 : ∫ t in (T / 2)..T, ubPerronFourth B (T / 4) t * ‖mtWattCoefficientBlock a A t‖ ^ 2 =
      ∫ t in (T / 2)..T, ∫ u in (-(T / 4))..(T / 4), F t u := by
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [ubPerronFourth, ← intervalIntegral.integral_mul_const, hF]
  rw [e1, intervalIntegral_integral_swap_of_continuous hFc (by linarith) (by linarith)]
  have hinner : ∀ u ∈ Set.Icc (-(T / 4)) (T / 4), ∫ t in (T / 2)..T, F t u ≤
      (1 / ‖(1 : ℂ) + (u : ℂ) * I‖) * (3 * G) := by
    intro u hu
    have hu' : |u| ≤ T / 4 := abs_le.2 ⟨hu.1, hu.2⟩
    have e : ∫ t in (T / 2)..T, F t u = (1 / ‖(1 : ℂ) + (u : ℂ) * I‖) *
        ∫ t in (T / 2)..T, ‖mtWattUnitBlock B (2 * B) (u - t)‖ ^ 4 *
          ‖mtWattCoefficientBlock a A t‖ ^ 2 := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun t _ => ?_
      rw [hF]; ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (integral_unitBlock_shift_le hT hG hu')
      (inv_norm_one_add_nonneg u)
  have hcont : Continuous fun u => ∫ t in (T / 2)..T, F t u := by
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (μ := volume) (f := fun u t => F t u) (a₀ := T / 2) (s := fun _ => T) hFc' continuous_const
  have hgc : Continuous fun u : ℝ => 1 / ‖(1 : ℂ) + (u : ℂ) * I‖ * (3 * G) :=
    hw.mul continuous_const
  refine le_trans (intervalIntegral.integral_mono_on (by linarith) (hcont.intervalIntegrable _ _)
    (hgc.intervalIntegrable _ _) hinner) ?_
  rw [intervalIntegral.integral_mul_const, mul_comm]
  exact mul_le_mul_of_nonneg_left (integral_inv_norm_one_add_le (by linarith)) (by linarith)

/-- The pointwise fourth power: `(E + c(P₁ + P₂ + P₃))⁴ ≤ 64E⁴ + 64c⁴W³(J₁ + J₂ + J₃)` when
`Pᵢ⁴ ≤ W³Jᵢ`. -/
private theorem ub_fourth_pointwise {u E c P₁ P₂ P₃ J₁ J₂ J₃ W : ℝ} (hu0 : 0 ≤ u)
    (hu : u ≤ E + c * (P₁ + P₂ + P₃)) (h₁ : P₁ ^ 4 ≤ W ^ 3 * J₁) (h₂ : P₂ ^ 4 ≤ W ^ 3 * J₂)
    (h₃ : P₃ ^ 4 ≤ W ^ 3 * J₃) :
    u ^ 4 ≤ 64 * E ^ 4 + 64 * c ^ 4 * W ^ 3 * (J₁ + J₂ + J₃) := by
  have h0 : u ^ 4 ≤ (E + c * P₁ + c * P₂ + c * P₃) ^ 4 :=
    pow_le_pow_left₀ hu0 (by linarith) 4
  have h1 := add_pow_four_le_four E (c * P₁) (c * P₂) (c * P₃)
  have hc4 : 0 ≤ c ^ 4 := by positivity
  have e : (c * P₁) ^ 4 + (c * P₂) ^ 4 + (c * P₃) ^ 4 = c ^ 4 * (P₁ ^ 4 + P₂ ^ 4 + P₃ ^ 4) := by
    ring
  have h2 : c ^ 4 * (P₁ ^ 4 + P₂ ^ 4 + P₃ ^ 4) ≤ c ^ 4 * (W ^ 3 * J₁ + W ^ 3 * J₂ + W ^ 3 * J₃) :=
    mul_le_mul_of_nonneg_left (by linarith) hc4
  nlinarith

/-- **The twisted fourth moment of a reflected unit block.**  If the dual blocks `U_B`,
`B ∈ {M, 2M, 4M}`, have fourth moments at most `G` against every twist on the three windows, then

`∫_{T/2}^{T} |U_N|⁴|𝒜_a|² ≤ c₁((1 + log T)/N + T^{-1/2})⁴ ∫_{T/2}^{T} |𝒜_a|²
  + c₂ (Y⁴/T²) log⁴(1 + T/4) G`,  `Y = T/(2πN)`. -/
theorem exists_integral_unitBlock_fourth_le_dual :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ (a : ℕ → ℂ) (A N N' : ℕ) (T G : ℝ), 1 ≤ N → N < N' →
      N' ≤ 2 * N → (N : ℝ) < T → T < (N : ℝ) ^ 2 → 11 ≤ T / (2 * π * N) → 0 ≤ G →
      (∀ B : ℕ, (B = ubDualBase N' T ∨ B = 2 * ubDualBase N' T ∨ B = 4 * ubDualBase N' T) →
        ∀ u : ℝ, |u| ≤ T / 4 → ∀ T' : ℝ, (T' = T / 2 ∨ T' = T ∨ T' = 5 * T / 4) →
        ∫ τ in (T' / 2)..T', ‖mtWattUnitBlock B (2 * B) τ‖ ^ 4 *
          ‖mtWattCoefficientBlock (mtTwist a u) A τ‖ ^ 2 ≤ G) →
      ∫ t in (T / 2)..T, ‖mtWattUnitBlock N N' t‖ ^ 4 * ‖mtWattCoefficientBlock a A t‖ ^ 2 ≤
        c₁ * ((1 + Real.log T) / N + 1 / Real.sqrt T) ^ 4 *
            (∫ t in (T / 2)..T, ‖mtWattCoefficientBlock a A t‖ ^ 2) +
          c₂ * ((T / (2 * π * N)) ^ 4 / T ^ 2) * Real.log (1 + T / 4) ^ 4 * G := by
  obtain ⟨C₀, hC₀, hpt⟩ := exists_norm_mtWattUnitBlock_le_perronMass
  refine ⟨64 * C₀ ^ 4, 576 * 23 ^ 4 * 256, by positivity, by positivity,
    fun a A N N' T G hN hNN' hN' hNT hTN hY hG0 hG => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hT0 : 0 < T := by linarith
  have hU : (0 : ℝ) ≤ T / 4 := by positivity
  set M := ubDualBase N' T
  set X := (1 + Real.log T) / N + 1 / Real.sqrt T with hX
  set c := 23 * (T / (2 * π * N)) / Real.sqrt T with hc
  set W := 4 * Real.log (1 + T / 4) with hW
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hX0 : 0 ≤ X := by rw [hX]; positivity
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have hW0 : 0 ≤ W := by
    rw [hW]; exact mul_nonneg (by norm_num) (Real.log_nonneg (by linarith))
  have hVc := fun B : ℕ => continuous_mtWattUnitBlock B (2 * B)
  have hAc : Continuous (mtWattCoefficientBlock a A) := continuous_perronPoly _ _ _
  have hJc : ∀ B : ℕ, Continuous fun t => ubPerronFourth B (T / 4) t := by
    intro B
    unfold ubPerronFourth
    have hcont : Continuous (fun p : ℝ × ℝ => ‖mtWattUnitBlock B (2 * B) (p.2 - p.1)‖ ^ 4 *
        (1 / ‖(1 : ℂ) + (p.2 : ℂ) * I‖)) :=
      (((hVc B).comp (continuous_snd.sub continuous_fst)).norm.pow 4).mul
        (continuous_inv_norm_one_add.comp continuous_snd)
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (μ := volume) (f := fun t u => ‖mtWattUnitBlock B (2 * B) (u - t)‖ ^ 4 *
        (1 / ‖(1 : ℂ) + (u : ℂ) * I‖)) (a₀ := -(T / 4)) (s := fun _ => T / 4) hcont
      continuous_const
  -- the pointwise bound
  have hpoint : ∀ t ∈ Icc (T / 2) T,
      ‖mtWattUnitBlock N N' t‖ ^ 4 * ‖mtWattCoefficientBlock a A t‖ ^ 2 ≤
        64 * (C₀ * X) ^ 4 * ‖mtWattCoefficientBlock a A t‖ ^ 2 +
          64 * c ^ 4 * W ^ 3 * (ubPerronFourth M (T / 4) t * ‖mtWattCoefficientBlock a A t‖ ^ 2 +
            ubPerronFourth (2 * M) (T / 4) t * ‖mtWattCoefficientBlock a A t‖ ^ 2 +
            ubPerronFourth (4 * M) (T / 4) t * ‖mtWattCoefficientBlock a A t‖ ^ 2) := by
    intro t ht
    have h := hpt N N' hN hNN' hN' T hNT hTN hY t ht
    have h4 := ub_fourth_pointwise (norm_nonneg _) h (ubPerronMass_pow_four_le M hU t)
      (ubPerronMass_pow_four_le (2 * M) hU t) (ubPerronMass_pow_four_le (4 * M) hU t)
    have := mul_le_mul_of_nonneg_right h4 (sq_nonneg ‖mtWattCoefficientBlock a A t‖)
    linarith
  -- integrate
  have hcA : Continuous fun t => ‖mtWattCoefficientBlock a A t‖ ^ 2 := hAc.norm.pow 2
  have i0 : IntervalIntegrable (fun t => ‖mtWattUnitBlock N N' t‖ ^ 4 *
      ‖mtWattCoefficientBlock a A t‖ ^ 2) volume (T / 2) T :=
    (((continuous_mtWattUnitBlock N N').norm.pow 4).mul hcA).intervalIntegrable _ _
  have iJ : ∀ B : ℕ, IntervalIntegrable (fun t => ubPerronFourth B (T / 4) t *
      ‖mtWattCoefficientBlock a A t‖ ^ 2) volume (T / 2) T :=
    fun B => ((hJc B).mul hcA).intervalIntegrable _ _
  have iA : IntervalIntegrable (fun t => ‖mtWattCoefficientBlock a A t‖ ^ 2) volume (T / 2) T :=
    hcA.intervalIntegrable _ _
  have hmono := intervalIntegral.integral_mono_on (by linarith) i0
    (((iA.const_mul (64 * (C₀ * X) ^ 4)).add
      ((((iJ M).add (iJ (2 * M))).add (iJ (4 * M))).const_mul (64 * c ^ 4 * W ^ 3)))) hpoint
  rw [intervalIntegral.integral_add (iA.const_mul _) ((((iJ M).add (iJ (2 * M))).add
    (iJ (4 * M))).const_mul _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_add ((iJ M).add (iJ (2 * M)))
    (iJ (4 * M)), intervalIntegral.integral_add (iJ M) (iJ (2 * M))] at hmono
  have hGB := fun (B : ℕ) (hB : B = M ∨ B = 2 * M ∨ B = 4 * M) =>
    integral_ubPerronFourth_mul_le (B := B) (a := a) (A := A) hT0 hG0 (hG B hB)
  have g1 := hGB M (Or.inl rfl)
  have g2 := hGB (2 * M) (Or.inr (Or.inl rfl))
  have g3 := hGB (4 * M) (Or.inr (Or.inr rfl))
  rw [← hW] at g1 g2 g3
  have hsum : 64 * c ^ 4 * W ^ 3 * ((∫ t in (T / 2)..T, ubPerronFourth M (T / 4) t *
      ‖mtWattCoefficientBlock a A t‖ ^ 2) + (∫ t in (T / 2)..T, ubPerronFourth (2 * M) (T / 4) t *
      ‖mtWattCoefficientBlock a A t‖ ^ 2) + ∫ t in (T / 2)..T, ubPerronFourth (4 * M) (T / 4) t *
      ‖mtWattCoefficientBlock a A t‖ ^ 2) ≤ 64 * c ^ 4 * W ^ 3 * (9 * G * W) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hfin : 64 * c ^ 4 * W ^ 3 * (9 * G * W) = 576 * 23 ^ 4 * 256 *
      ((T / (2 * π * N)) ^ 4 / T ^ 2) * Real.log (1 + T / 4) ^ 4 * G := by
    have hs4 : Real.sqrt T ^ 4 = T ^ 2 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt hT0.le]
    rw [hc, hW, div_pow, mul_pow, hs4]; ring
  have e : 64 * (C₀ * X) ^ 4 = 64 * C₀ ^ 4 * X ^ 4 := by ring
  rw [e] at hmono
  linarith

end

end RHTower.Sieve
