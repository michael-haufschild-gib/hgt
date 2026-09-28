import GaloisForLFunctions.RHTower.ChronologicalWeightedMellin

/-!
# Integer-scale transfer for sharply cut weighted Möbius sources

For `0 < θ < 1` and the weight `w = 1_{(0, θ]} H`, the source `Σ μ(n) w(nt)` is a finite sum.
If `H` is bounded by `B` and `L`-Lipschitz on `(0, θ]`, the source at any `t ∈ (0, 1]` differs from
its value at the integer scale `1/N`, `N = ⌊1/t⌋`, by at most `L + B`:

* on `n ≤ θN` both arguments lie in `(0, θ]` and differ by `n(1/N - t) ≤ 1/(N + 1)`;
* at most one `n` has `nt ≤ θ < n/N`, since `θ(1/t - N) < θ < 1`;
* otherwise both weights vanish.
-/

open Set Filter ArithmeticFunction
open scoped Moebius

namespace RHTower

/-- **Integer-scale transfer.** -/
theorem norm_chronologicalMobiusWeightedSource_sub_floor_le {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    {H : ℝ → ℂ} {L B : ℝ} (hL0 : 0 ≤ L) (hB0 : 0 ≤ B)
    (hB : ∀ x ∈ Ioc 0 θ, ‖H x‖ ≤ B)
    (hL : ∀ x ∈ Ioc 0 θ, ∀ y ∈ Ioc 0 θ, ‖H x - H y‖ ≤ L * |x - y|)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    ‖chronologicalMobiusWeightedSource ((Ioc 0 θ).indicator H) t -
      chronologicalMobiusWeightedSource ((Ioc 0 θ).indicator H) (1 / ⌊1 / t⌋₊)‖ ≤ L + B := by
  classical
  set w := (Ioc 0 θ).indicator H with hwdef
  set N := ⌊1 / t⌋₊ with hNdef
  have hX : 1 ≤ 1 / t := by rw [le_div_iff₀ ht0, one_mul]; exact ht1
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hX)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hNle : (N : ℝ) ≤ 1 / t := Nat.floor_le (by positivity)
  have hNlt : 1 / t < N + 1 := Nat.lt_floor_add_one _
  have htN : t ≤ 1 / N := by
    rw [le_div_iff₀ hNpos]; rw [le_div_iff₀ ht0] at hNle; linarith
  have htN1 : 1 < t * (N + 1) := by
    rw [div_lt_iff₀ ht0] at hNlt; linarith
  have hw : ∀ x, θ < x → w x = 0 := fun x hx =>
    Set.indicator_of_notMem (fun h => absurd h.2 (not_le.mpr hx)) _
  have hsum_t := chronologicalMobiusWeightedSource_eq_sum w N ht0 hw (by linarith)
  have hsum_N := chronologicalMobiusWeightedSource_eq_sum w N (by positivity : (0 : ℝ) < 1 / N) hw
    (by rw [← div_eq_mul_one_div, lt_div_iff₀ hNpos]; nlinarith)
  rw [hsum_t, hsum_N, ← Finset.sum_sub_distrib]
  set S := (Finset.range (N + 1)).filter (fun n : ℕ => (n : ℝ) * t ≤ θ ∧ θ < n * (1 / N)) with hS
  have hScard : S.card ≤ 1 := by
    refine Finset.card_le_one.mpr fun a ha b hb => ?_
    rw [hS, Finset.mem_filter] at ha hb
    by_contra hab
    have key : ∀ a b : ℕ, a < b → (b : ℝ) * t ≤ θ → θ < a * (1 / N) → False := by
      intro a b hlt hb ha
      have hb' : (a : ℝ) + 1 ≤ b := by exact_mod_cast hlt
      rw [← div_eq_mul_one_div, lt_div_iff₀ hNpos] at ha
      nlinarith
    rcases Nat.lt_or_gt_of_ne hab with h | h
    · exact key a b h hb.2.1 ha.2.2
    · exact key b a h ha.2.1 hb.2.2
  have hterm : ∀ n ∈ Finset.range (N + 1),
      ‖(μ n : ℂ) * w (n * t) - (μ n : ℂ) * w (n * (1 / N))‖ ≤
        L / (N + 1) + (if n ∈ S then B else 0) := by
    intro n hn
    have hnN : n ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp only [ArithmeticFunction.map_zero, Int.cast_zero, zero_mul, sub_zero, norm_zero]
      have : 0 ≤ L / (N + 1) := by positivity
      split_ifs <;> linarith
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
    have hnN' : (n : ℝ) ≤ N := by exact_mod_cast hnN
    have hμ : ‖(μ n : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]; exact_mod_cast abs_moebius_le_one
    have hat : 0 < (n : ℝ) * t := mul_pos hnpos ht0
    have hab : (n : ℝ) * t ≤ n * (1 / N) := mul_le_mul_of_nonneg_left htN hnpos.le
    rw [← mul_sub, norm_mul]
    refine (mul_le_of_le_one_left (norm_nonneg _) hμ).trans ?_
    by_cases hbθ : (n : ℝ) * (1 / N) ≤ θ
    · have hxa : (n : ℝ) * t ∈ Ioc 0 θ := ⟨hat, hab.trans hbθ⟩
      have hxb : (n : ℝ) * (1 / N) ∈ Ioc 0 θ := ⟨hat.trans_le hab, hbθ⟩
      rw [hwdef, Set.indicator_of_mem hxa, Set.indicator_of_mem hxb]
      refine (hL _ hxa _ hxb).trans ?_
      have hdiff : |(n : ℝ) * t - n * (1 / N)| ≤ 1 / (N + 1) := by
        rw [abs_of_nonpos (by linarith), neg_sub, ← mul_sub]
        have h1 : 1 / (N : ℝ) - t ≤ 1 / (N * (N + 1)) := by
          have : 1 / (N : ℝ) - 1 / (N * (N + 1)) = 1 / (N + 1) := by field_simp; ring
          have ht' : 1 / ((N : ℝ) + 1) < t := by
            rw [div_lt_iff₀ (by positivity)]; linarith
          linarith
        calc (n : ℝ) * (1 / N - t) ≤ N * (1 / (N * (N + 1))) :=
              mul_le_mul hnN' h1 (by linarith) hNpos.le
          _ = 1 / (N + 1) := by field_simp
      calc L * |(n : ℝ) * t - n * (1 / N)| ≤ L * (1 / (N + 1)) :=
            mul_le_mul_of_nonneg_left hdiff hL0
        _ = L / (N + 1) + 0 := by ring
        _ ≤ L / (N + 1) + (if n ∈ S then B else 0) := by
            gcongr; split_ifs <;> simp [hB0]
    · push Not at hbθ
      have hwb : w (n * (1 / N)) = 0 := hw _ hbθ
      by_cases haθ : (n : ℝ) * t ≤ θ
      · have hnS : n ∈ S := by
          rw [hS, Finset.mem_filter]; exact ⟨hn, haθ, hbθ⟩
        have hxa : (n : ℝ) * t ∈ Ioc 0 θ := ⟨hat, haθ⟩
        rw [hwb, sub_zero, if_pos hnS, hwdef, Set.indicator_of_mem hxa]
        have : 0 ≤ L / (N + 1) := by positivity
        linarith [hB _ hxa]
      · push Not at haθ
        rw [hwb, hw _ haθ, sub_zero, norm_zero]
        positivity
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    Finset.sum_ite_mem, Finset.inter_eq_right.mpr (Finset.filter_subset _ _), Finset.sum_const,
    nsmul_eq_mul]
  have h1 : ((N + 1 : ℕ) : ℝ) * (L / (N + 1)) = L := by push_cast; field_simp
  have h2 : (S.card : ℝ) * B ≤ B := by
    have : (S.card : ℝ) ≤ 1 := by exact_mod_cast hScard
    nlinarith
  linarith

end RHTower
