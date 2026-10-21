import GaloisForLFunctions.RHTower.Sieve.HeathBrownPairSumUnitBlock

/-!
# Heath-Brown's pair sums: one dyadic shell of differences

Fix the block `U_N(t) = Σ_{N<n≤2N} n^{−1−it}` and a height `T` with `2 ≤ T < N²`.  On
`[T/2, T]` the corpus gives three pointwise bounds: Kuzmin–Landau above the height
(`T ≤ N`), the short-dual reflection (`Y = T/(2Real.piN) ≤ 11`) and the reflection into three Perron
masses (`Y ≥ 11`).  They combine into one inequality

`|U_N(t)| ≤ C ((1 + log T)/N + T^{−1/2}) + [Y ≥ 11] (23 Y/√T) Σ_{i<3} P_{2^i M}(t)`,

`M = ⌊T/(4Real.pi(2N + 1/4))⌋`, with a fixed absolute constant `C = hbReflConst`.

Summing its square over the pairs `(t₁, t₂)` of a `1`-separated set `W` with `T/2 ≤ |t₁−t₂| ≤ T`
(at most `2T + 1` partners per point; `|U_N|` is even) and bounding the Perron masses by
`sum_sq_ubPerronMass_abs_le` gives the **shell bound**

`Σ_{shell} |U_N(t₁−t₂)|² ≤ |W|(2T+1)·2C²E² + [Y ≥ 11] 3174 (Y²/T) Σ_{i<3} 2(4 log(1+T/4))² 𝒜₁((B_i, 2B_i])`,

`B_i = 2^i M`.  When `Y ≥ 11` the dual length satisfies `Y/9 ≤ M ≤ Y/2`.
-/

set_option autoImplicit false

namespace RHTower.Sieve

open Finset Complex
open scoped Real

noncomputable section

/-- The three regimes of the corpus reflection combine into one pointwise bound. -/
theorem exists_norm_mtWattUnitBlock_le_unified :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → ∀ T : ℝ, 2 ≤ T → T < (N : ℝ) ^ 2 →
      ∀ t ∈ Set.Icc (T / 2) T,
      ‖mtWattUnitBlock N (2 * N) t‖ ≤ C * ((1 + Real.log T) / N + 1 / Real.sqrt T) +
        if 11 ≤ T / (2 * Real.pi * N) then
          23 * (T / (2 * Real.pi * N)) / Real.sqrt T *
            ∑ i ∈ Finset.range 3, ubPerronMass (2 ^ i * ubDualBase (2 * N) T) (T / 4) t
        else 0 := by
  obtain ⟨C₁, hC₁, hshort⟩ := exists_norm_mtWattUnitBlock_le_short_dual
  obtain ⟨C₀, hC₀, hper⟩ := exists_norm_mtWattUnitBlock_le_perronMass
  refine ⟨C₁ + C₀ + 2 * (6 * Real.pi + 1), by positivity, fun N hN T hT2 hTN t ht => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hT0 : 0 < T := by linarith
  have hsT : 0 < Real.sqrt T := Real.sqrt_pos.2 hT0
  have hlog : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hE0 : 0 ≤ (1 + Real.log T) / N + 1 / Real.sqrt T := by positivity
  have hsum3 : ∀ s : ℝ, ∑ i ∈ Finset.range 3, ubPerronMass (2 ^ i * ubDualBase (2 * N) T) (T / 4) s
      = ubPerronMass (ubDualBase (2 * N) T) (T / 4) s +
        ubPerronMass (2 * ubDualBase (2 * N) T) (T / 4) s +
        ubPerronMass (4 * ubDualBase (2 * N) T) (T / 4) s := fun s => by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, one_mul,
      pow_one]
    norm_num
  have hif0 : 0 ≤ if 11 ≤ T / (2 * Real.pi * N) then
      23 * (T / (2 * Real.pi * N)) / Real.sqrt T *
        ∑ i ∈ Finset.range 3, ubPerronMass (2 ^ i * ubDualBase (2 * N) T) (T / 4) t
      else 0 := by
    split_ifs with hY
    · have := Finset.sum_nonneg fun i (_ : i ∈ Finset.range 3) =>
        ubPerronMass_nonneg (2 ^ i * ubDualBase (2 * N) T) (by linarith : (0 : ℝ) ≤ T / 4) t
      have hY0 : 0 ≤ T / (2 * Real.pi * N) := by linarith
      positivity
    · exact le_refl 0
  rcases le_or_gt T N with hTN' | hNT
  · -- Kuzmin–Landau above the height
    have h := norm_mtWattUnitBlock_le_over_height hN (by omega : N < 2 * N) le_rfl hT0 ht.1 ht.2
      hTN'
    have hs1 : 1 ≤ Real.sqrt T := Real.one_le_sqrt.mpr (by linarith)
    have hsT' : Real.sqrt T ≤ T := by
      calc Real.sqrt T ≤ Real.sqrt T * Real.sqrt T := le_mul_of_one_le_right hsT.le hs1
        _ = T := Real.mul_self_sqrt hT0.le
    have hc : 2 * (6 * Real.pi + 1) / T ≤ (C₁ + C₀ + 2 * (6 * Real.pi + 1)) *
        ((1 + Real.log T) / N + 1 / Real.sqrt T) := by
      calc 2 * (6 * Real.pi + 1) / T ≤ 2 * (6 * Real.pi + 1) * (1 / Real.sqrt T) := by
            rw [mul_one_div]
            exact div_le_div_of_nonneg_left (by positivity) hsT hsT'
        _ ≤ 2 * (6 * Real.pi + 1) * ((1 + Real.log T) / N + 1 / Real.sqrt T) :=
            mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by positivity)) (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hE0
    linarith
  · by_cases hY : 11 ≤ T / (2 * Real.pi * N)
    · rw [if_pos hY, hsum3]
      have h := hper N (2 * N) hN (by omega) le_rfl T hNT hTN hY t ht
      have hC : C₀ * ((1 + Real.log T) / N + 1 / Real.sqrt T) ≤
          (C₁ + C₀ + 2 * (6 * Real.pi + 1)) * ((1 + Real.log T) / N + 1 / Real.sqrt T) :=
        mul_le_mul_of_nonneg_right (by linarith [Real.pi_pos]) hE0
      linarith
    · rw [if_neg hY]
      have h := hshort N (2 * N) hN (by omega) le_rfl T hT2 hNT hTN (le_of_lt (not_le.mp hY)) t ht
      have hC : C₁ * ((1 + Real.log T) / N + 1 / Real.sqrt T) ≤
          (C₁ + C₀ + 2 * (6 * Real.pi + 1)) * ((1 + Real.log T) / N + 1 / Real.sqrt T) :=
        mul_le_mul_of_nonneg_right (by linarith [Real.pi_pos]) hE0
      linarith

/-- The absolute constant of the unified reflection bound. -/
def hbReflConst : ℝ := Classical.choose exists_norm_mtWattUnitBlock_le_unified

theorem hbReflConst_pos : 0 < hbReflConst :=
  (Classical.choose_spec exists_norm_mtWattUnitBlock_le_unified).1

/-- **The unified reflection bound** with the constant `hbReflConst`. -/
theorem norm_mtWattUnitBlock_le_unified {N : ℕ} (hN : 1 ≤ N) {T : ℝ} (hT2 : 2 ≤ T)
    (hTN : T < (N : ℝ) ^ 2) {t : ℝ} (ht : t ∈ Set.Icc (T / 2) T) :
    ‖mtWattUnitBlock N (2 * N) t‖ ≤ hbReflConst * ((1 + Real.log T) / N + 1 / Real.sqrt T) +
      if 11 ≤ T / (2 * Real.pi * N) then
        23 * (T / (2 * Real.pi * N)) / Real.sqrt T *
          ∑ i ∈ Finset.range 3, ubPerronMass (2 ^ i * ubDualBase (2 * N) T) (T / 4) t
      else 0 :=
  (Classical.choose_spec exists_norm_mtWattUnitBlock_le_unified).2 N hN T hT2 hTN t ht

/-- **The squared unified bound:**
`|U_N(t)|² ≤ 2C²E² + [Y ≥ 11] 3174 (Y²/T) Σ_{i<3} P_{2^i M}(t)²`. -/
theorem sq_norm_mtWattUnitBlock_le_unified {N : ℕ} (hN : 1 ≤ N) {T : ℝ} (hT2 : 2 ≤ T)
    (hTN : T < (N : ℝ) ^ 2) {t : ℝ} (ht : t ∈ Set.Icc (T / 2) T) :
    ‖mtWattUnitBlock N (2 * N) t‖ ^ 2 ≤
      2 * hbReflConst ^ 2 * ((1 + Real.log T) / N + 1 / Real.sqrt T) ^ 2 +
      if 11 ≤ T / (2 * Real.pi * N) then
        3174 * ((T / (2 * Real.pi * N)) ^ 2 / T) *
          ∑ i ∈ Finset.range 3, ubPerronMass (2 ^ i * ubDualBase (2 * N) T) (T / 4) t ^ 2
      else 0 := by
  have h := norm_mtWattUnitBlock_le_unified hN hT2 hTN ht
  have hT0 : 0 < T := by linarith
  have hsT : 0 < Real.sqrt T := Real.sqrt_pos.2 hT0
  have hlog : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  obtain ⟨a, ha⟩ : ∃ a, a = hbReflConst * ((1 + Real.log T) / N + 1 / Real.sqrt T) := ⟨_, rfl⟩
  have ha0 : 0 ≤ a := by rw [ha]; exact mul_nonneg hbReflConst_pos.le (by positivity)
  rw [← ha] at h
  split_ifs at h ⊢ with hY
  · obtain ⟨P, hP⟩ : ∃ P, P = ∑ i ∈ Finset.range 3,
        ubPerronMass (2 ^ i * ubDualBase (2 * N) T) (T / 4) t := ⟨_, rfl⟩
    rw [← hP] at h
    have hP0 : 0 ≤ P := hP ▸ Finset.sum_nonneg fun i _ =>
      ubPerronMass_nonneg _ (by linarith : (0 : ℝ) ≤ T / 4) t
    have hP2 : P ^ 2 ≤ 3 * ∑ i ∈ Finset.range 3,
        ubPerronMass (2 ^ i * ubDualBase (2 * N) T) (T / 4) t ^ 2 := by
      have := sq_sum_le_card_mul_sum_sq (s := Finset.range 3)
        (f := fun i => ubPerronMass (2 ^ i * ubDualBase (2 * N) T) (T / 4) t)
      simpa [hP] using this
    obtain ⟨Y, hYdef⟩ : ∃ Y, Y = T / (2 * Real.pi * N) := ⟨_, rfl⟩
    rw [← hYdef] at h hY ⊢
    have hb0 : 0 ≤ 23 * Y / Real.sqrt T * P := by
      have : 0 ≤ Y := by linarith
      positivity
    have hU0 := norm_nonneg (mtWattUnitBlock N (2 * N) t)
    have hsq : (23 * Y / Real.sqrt T) ^ 2 = 529 * (Y ^ 2 / T) := by
      rw [div_pow, Real.sq_sqrt hT0.le]
      ring
    calc ‖mtWattUnitBlock N (2 * N) t‖ ^ 2 ≤ (a + 23 * Y / Real.sqrt T * P) ^ 2 :=
          pow_le_pow_left₀ hU0 h 2
      _ ≤ 2 * a ^ 2 + 2 * ((23 * Y / Real.sqrt T) ^ 2 * P ^ 2) := by
          nlinarith [sq_nonneg (a - 23 * Y / Real.sqrt T * P)]
      _ ≤ 2 * a ^ 2 + 2 * (529 * (Y ^ 2 / T) * (3 * ∑ i ∈ Finset.range 3,
            ubPerronMass (2 ^ i * ubDualBase (2 * N) T) (T / 4) t ^ 2)) := by
          rw [hsq]
          have : 0 ≤ 529 * (Y ^ 2 / T) := by positivity
          nlinarith [mul_le_mul_of_nonneg_left hP2 this]
      _ = _ := by rw [ha]; ring
  · have hU0 := norm_nonneg (mtWattUnitBlock N (2 * N) t)
    rw [add_zero] at h ⊢
    calc ‖mtWattUnitBlock N (2 * N) t‖ ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ hU0 h 2
      _ ≤ 2 * a ^ 2 := by nlinarith [sq_nonneg a]
      _ = _ := by rw [ha]; ring

/-- **The dual length.**  For `N ≥ 1` and `Y = T/(2πN) ≥ 11`, `Y/9 ≤ ⌊T/(4π(2N + 1/4))⌋ ≤ Y/2`
(the corpus `ubDualBase_bounds` for the real length, then the floor). -/
theorem ubDualBase_two_mul_bounds {N : ℕ} (hN : 1 ≤ N) {T : ℝ}
    (hY : 11 ≤ T / (2 * Real.pi * N)) :
    T / (2 * Real.pi * N) / 9 ≤ (ubDualBase (2 * N) T : ℝ) ∧
      (ubDualBase (2 * N) T : ℝ) ≤ T / (2 * Real.pi * N) / 2 := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hT0 : 0 < T := by
    by_contra h
    have : T / (2 * Real.pi * N) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (not_lt.mp h) (by positivity)
    linarith
  have hcast : ((2 * N : ℕ) : ℝ) = 2 * N := by push_cast; ring
  have h := ubDualBase_bounds (N := N) (N' := ((2 * N : ℕ) : ℝ)) hT0 hN1
    (by rw [hcast]; linarith) (by rw [hcast])
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = T / (4 * Real.pi * (((2 * N : ℕ) : ℝ) + 1 / 4)) := ⟨_, rfl⟩
  rw [← hx] at h
  have hfl : (ubDualBase (2 * N) T : ℝ) = (⌊x⌋₊ : ℝ) := by rw [ubDualBase, hx]
  rw [hfl]
  refine ⟨?_, (Nat.floor_le (by linarith)).trans h.2⟩
  have h1 := Nat.lt_floor_add_one x
  linarith [h.1]

/-- **The shell bound.**  For `2 ≤ T < N²` and `W` `1`-separated, the pairs with
`T/2 ≤ |t₁ − t₂| ≤ T` contribute at most
`|W|(2T+1)·2C²E² + [Y ≥ 11] 3174 (Y²/T) Σ_{i<3} 2(4 log(1+T/4))² 𝒜₁((2^i M, 2^{i+1} M])`. -/
theorem sum_shell_sq_norm_mtWattUnitBlock_le (W : Finset ℝ) (hW : GuthMaynard.IsSeparated 1 W)
    {N : ℕ} (hN : 1 ≤ N) {T : ℝ} (hT2 : 2 ≤ T) (hTN : T < (N : ℝ) ^ 2) :
    ∑ t₁ ∈ W, ∑ t₂ ∈ W.filter (fun t₂ => T / 2 ≤ |t₁ - t₂| ∧ |t₁ - t₂| ≤ T),
        ‖mtWattUnitBlock N (2 * N) (t₁ - t₂)‖ ^ 2 ≤
      W.card * (2 * T + 1) * (2 * hbReflConst ^ 2 *
        ((1 + Real.log T) / N + 1 / Real.sqrt T) ^ 2) +
      if 11 ≤ T / (2 * Real.pi * N) then
        3174 * ((T / (2 * Real.pi * N)) ^ 2 / T) * ∑ i ∈ Finset.range 3,
          2 * (4 * Real.log (1 + T / 4)) ^ 2 *
            hbAmp W 1 (Finset.Ioc (2 ^ i * ubDualBase (2 * N) T)
              (2 * (2 ^ i * ubDualBase (2 * N) T)))
      else 0 := by
  classical
  have hT0 : 0 < T := by linarith
  obtain ⟨a, ha⟩ : ∃ a, a = 2 * hbReflConst ^ 2 * ((1 + Real.log T) / N + 1 / Real.sqrt T) ^ 2 :=
    ⟨_, rfl⟩
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  -- the even block, evaluated at `|t₁ − t₂| ∈ [T/2, T]`
  have hpt : ∀ t₁ t₂ : ℝ, T / 2 ≤ |t₁ - t₂| ∧ |t₁ - t₂| ≤ T →
      ‖mtWattUnitBlock N (2 * N) (t₁ - t₂)‖ ^ 2 ≤ a +
        if 11 ≤ T / (2 * Real.pi * N) then
          3174 * ((T / (2 * Real.pi * N)) ^ 2 / T) *
            ∑ i ∈ Finset.range 3, ubPerronMass (2 ^ i * ubDualBase (2 * N) T) (T / 4)
              |t₁ - t₂| ^ 2
        else 0 := by
    intro t₁ t₂ hs
    have heven : ‖mtWattUnitBlock N (2 * N) (t₁ - t₂)‖ =
        ‖mtWattUnitBlock N (2 * N) |t₁ - t₂|‖ := by
      rcases abs_choice (t₁ - t₂) with h | h <;> rw [h]
      rw [norm_mtWattUnitBlock_neg]
    rw [heven, ha]
    exact sq_norm_mtWattUnitBlock_le_unified hN hT2 hTN ⟨hs.1, hs.2⟩
  have hcount : ∀ t₁ ∈ W, (((W.filter fun t₂ => T / 2 ≤ |t₁ - t₂| ∧ |t₁ - t₂| ≤ T).card : ℕ) : ℝ)
      ≤ 2 * T + 1 := fun t₁ _ =>
    (Nat.cast_le.mpr (Finset.card_le_card fun x hx => Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2.2⟩)).trans
      (card_filter_abs_sub_le hW t₁ hT0.le)
  have hif0 : ∀ t₁ t₂ : ℝ, 0 ≤ if 11 ≤ T / (2 * Real.pi * N) then
      3174 * ((T / (2 * Real.pi * N)) ^ 2 / T) *
        ∑ i ∈ Finset.range 3, ubPerronMass (2 ^ i * ubDualBase (2 * N) T) (T / 4) |t₁ - t₂| ^ 2
      else 0 := fun t₁ t₂ => by
    split_ifs
    · have := Finset.sum_nonneg fun i (_ : i ∈ Finset.range 3) =>
        sq_nonneg (ubPerronMass (2 ^ i * ubDualBase (2 * N) T) (T / 4) |t₁ - t₂|)
      positivity
    · exact le_refl 0
  calc ∑ t₁ ∈ W, ∑ t₂ ∈ W.filter (fun t₂ => T / 2 ≤ |t₁ - t₂| ∧ |t₁ - t₂| ≤ T),
        ‖mtWattUnitBlock N (2 * N) (t₁ - t₂)‖ ^ 2
      ≤ ∑ t₁ ∈ W, ∑ t₂ ∈ W.filter (fun t₂ => T / 2 ≤ |t₁ - t₂| ∧ |t₁ - t₂| ≤ T),
          (a + if 11 ≤ T / (2 * Real.pi * N) then
            3174 * ((T / (2 * Real.pi * N)) ^ 2 / T) *
              ∑ i ∈ Finset.range 3, ubPerronMass (2 ^ i * ubDualBase (2 * N) T) (T / 4)
                |t₁ - t₂| ^ 2
          else 0) :=
        Finset.sum_le_sum fun t₁ _ => Finset.sum_le_sum fun t₂ ht₂ =>
          hpt t₁ t₂ (Finset.mem_filter.mp ht₂).2
    _ ≤ ∑ t₁ ∈ W, ((2 * T + 1) * a + ∑ t₂ ∈ W, if 11 ≤ T / (2 * Real.pi * N) then
            3174 * ((T / (2 * Real.pi * N)) ^ 2 / T) *
              ∑ i ∈ Finset.range 3, ubPerronMass (2 ^ i * ubDualBase (2 * N) T) (T / 4)
                |t₁ - t₂| ^ 2
          else 0) := by
        refine Finset.sum_le_sum fun t₁ ht₁ => ?_
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
        exact add_le_add (mul_le_mul_of_nonneg_right (hcount t₁ ht₁) ha0)
          (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun t₂ _ _ => hif0 t₁ t₂)
    _ = W.card * (2 * T + 1) * a + ∑ t₁ ∈ W, ∑ t₂ ∈ W, (if 11 ≤ T / (2 * Real.pi * N) then
            3174 * ((T / (2 * Real.pi * N)) ^ 2 / T) *
              ∑ i ∈ Finset.range 3, ubPerronMass (2 ^ i * ubDualBase (2 * N) T) (T / 4)
                |t₁ - t₂| ^ 2
          else 0) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
        ring
    _ ≤ _ := by
        rw [ha]
        refine add_le_add le_rfl ?_
        split_ifs with hY
        · obtain ⟨Q, hQ⟩ : ∃ Q : ℕ → ℝ → ℝ → ℝ, Q = fun i t₁ t₂ =>
              ubPerronMass (2 ^ i * ubDualBase (2 * N) T) (T / 4) |t₁ - t₂| ^ 2 := ⟨_, rfl⟩
          obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 3174 * ((T / (2 * Real.pi * N)) ^ 2 / T) := ⟨_, rfl⟩
          have hK0 : 0 ≤ K := by rw [hK]; positivity
          have hswap : ∑ t₁ ∈ W, ∑ t₂ ∈ W, K * ∑ i ∈ Finset.range 3, Q i t₁ t₂ =
              K * ∑ i ∈ Finset.range 3, ∑ t₁ ∈ W, ∑ t₂ ∈ W, Q i t₁ t₂ := by
            simp only [Finset.mul_sum]
            calc ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ i ∈ Finset.range 3, K * Q i t₁ t₂
                = ∑ t₁ ∈ W, ∑ i ∈ Finset.range 3, ∑ t₂ ∈ W, K * Q i t₁ t₂ :=
                  Finset.sum_congr rfl fun t₁ _ => Finset.sum_comm
              _ = _ := Finset.sum_comm
          have hgoal : ∑ t₁ ∈ W, ∑ t₂ ∈ W, K * ∑ i ∈ Finset.range 3, Q i t₁ t₂ ≤
              K * ∑ i ∈ Finset.range 3, 2 * (4 * Real.log (1 + T / 4)) ^ 2 *
                hbAmp W 1 (Finset.Ioc (2 ^ i * ubDualBase (2 * N) T)
                  (2 * (2 ^ i * ubDualBase (2 * N) T))) := by
            rw [hswap]
            refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) hK0
            rw [hQ]
            exact sum_sq_ubPerronMass_abs_le W _ (by linarith : (0 : ℝ) ≤ T / 4)
          rw [hQ, hK] at hgoal
          exact hgoal
        · simp

end

end RHTower.Sieve
