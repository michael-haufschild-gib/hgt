import GaloisForLFunctions.RHTower.FareyDiscrepancyExponentLaw
import GaloisForLFunctions.RHTower.MobiusMertensEvenConvolutionExactOrder

/-!
# Franel's square criterion and its exponent law

With `F_n = {f_1 < ⋯ < f_L}` the Farey fractions of order `n` and `δ_ν = f_ν - ν/L`,

* `Σ_ν δ_ν² ≤ (2n²/L²)(½ + 2 ∫_0^1 S_n²) + 2/n²` for the Farey sawtooth `S_n`;
* `Σ_ν δ_ν² = O(n^c)` for every `c > 2Θ - 2`, and `Σ_ν δ_ν² = O(n^{2b-2})` forces `Θ ≤ b`;
* hence the Riemann hypothesis holds iff `Σ_ν δ_ν² = O(n^{-1+δ})` for every `δ > 0` (Franel).

The local estimate is `|L f - rank f| ≤ |½ + S_n(x)| + L/n²` on `[f, f + 1/n²)`, squared and
averaged over these disjoint intervals; the converse uses `(Σ|δ_ν|)² ≤ L Σ δ_ν²` and the ℓ¹
exponent law.
-/

open Finset MeasureTheory

open RHTower.Sieve (fareySet mem_fareySet)

namespace RHTower

noncomputable section

/-- Franel's square discrepancy `Σ_ν (f_ν - ν/L)²`. -/
def fareyL2Discrepancy (n : ℕ) : ℝ :=
  ∑ p ∈ fareySet n, (fareyValue p - (fareyRank n p : ℝ) / ((fareySet n).card : ℝ)) ^ 2

theorem fareyValue_le_one {n : ℕ} {p : ℕ × ℕ} (hp : p ∈ fareySet n) : fareyValue p ≤ 1 := by
  obtain ⟨_, ⟨hq1, _⟩, hle, _⟩ := mem_fareySet.mp hp
  have hq0 : (0 : ℝ) < p.2 := by exact_mod_cast hq1
  unfold fareyValue; rw [div_le_one hq0]; exact_mod_cast hle

theorem fareyRank_eq_card_of_fareyValue_eq_one {n : ℕ} {p : ℕ × ℕ} (hp1 : fareyValue p = 1) :
    fareyRank n p = (fareySet n).card := by
  unfold fareyRank
  congr 1
  exact filter_true_of_mem fun r hr => by rw [hp1]; exact fareyValue_le_one hr

/-- **The pointwise local estimate.**  `|L f - rank f| ≤ |½ + S_n(x)| + L/n²` on `[f, f + 1/n²)`. -/
theorem abs_card_mul_sub_fareyRank_le {n : ℕ} (hn : 1 ≤ n) {p : ℕ × ℕ} (hp : p ∈ fareySet n)
    (hp1 : fareyValue p < 1) {x : ℝ}
    (hx : x ∈ Set.Ico (fareyValue p) (fareyValue p + 1 / (n : ℝ) ^ 2)) :
    |((fareySet n).card : ℝ) * fareyValue p - fareyRank n p|
      ≤ |1 / 2 + fareySawtooth n x| + ((fareySet n).card : ℝ) * (1 / (n : ℝ) ^ 2) := by
  set L : ℝ := ((fareySet n).card : ℝ)
  obtain ⟨hf0, hfh⟩ := fareyValue_pos_and_add_le hn hp hp1
  have hL0 : 0 ≤ L := by positivity
  have hcnt := fareyCount_eq_fareyRank hp hx.1 hx.2
  have hdef := card_mul_sub_fareyCount_eq hn (x := x) (by linarith [hx.1]) (by linarith [hx.2])
  rw [hcnt] at hdef
  have hS : L * x - fareyRank n p = 1 / 2 + fareySawtooth n x := hdef
  have e : L * fareyValue p - fareyRank n p
      = (1 / 2 + fareySawtooth n x) - L * (x - fareyValue p) := by linarith
  have h1 : 0 ≤ L * (x - fareyValue p) := mul_nonneg hL0 (by linarith [hx.1])
  have h2 : L * (x - fareyValue p) ≤ L * (1 / (n : ℝ) ^ 2) :=
    mul_le_mul_of_nonneg_left (by linarith [hx.2]) hL0
  rw [e]
  refine (abs_sub _ _).trans ?_
  rw [abs_of_nonneg h1]
  linarith

/-- The intervals `[f, f + 1/n²)` over the Farey fractions `f < 1` are disjoint subsets of `(0, 1]`,
so their integrals of a nonnegative function add up to at most the integral over `(0, 1]`. -/
theorem sum_setIntegral_fareyIco_le {n : ℕ} (hn : 1 ≤ n) {g : ℝ → ℝ} (hg : ∀ x, 0 ≤ g x)
    (hint : IntegrableOn g (Set.Ioc 0 1)) :
    ∑ p ∈ (fareySet n).filter (fun p => fareyValue p < 1),
        ∫ x in Set.Ico (fareyValue p) (fareyValue p + 1 / (n : ℝ) ^ 2), g x
      ≤ ∫ x in Set.Ioc (0 : ℝ) 1, g x := by
  set P := (fareySet n).filter (fun p => fareyValue p < 1) with hP
  set J : ℕ × ℕ → Set ℝ := fun p => Set.Ico (fareyValue p) (fareyValue p + 1 / (n : ℝ) ^ 2)
    with hJ
  have hsubJ : ∀ p ∈ P, J p ⊆ Set.Ioc 0 1 := by
    intro p hp x hx
    obtain ⟨hf0, hfh⟩ := fareyValue_pos_and_add_le hn (mem_filter.mp hp).1 (mem_filter.mp hp).2
    exact ⟨lt_of_lt_of_le hf0 hx.1, by linarith [hx.2]⟩
  have hdisj : Set.Pairwise (↑P) (Function.onFun Disjoint J) := by
    intro p hp r hr hpr
    have hp' := (mem_filter.mp (mem_coe.mp hp)).1
    have hr' := (mem_filter.mp (mem_coe.mp hr)).1
    have hne : fareyValue p ≠ fareyValue r := fun heq => hpr (fareyValue_injOn n hp' hr' heq)
    rw [Function.onFun, Set.disjoint_left]
    intro x hx1 hx2
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := one_div_sq_le_fareyValue_sub hp' hr' hlt
      linarith [hx1.2, hx2.1]
    · have := one_div_sq_le_fareyValue_sub hr' hp' hlt
      linarith [hx2.2, hx1.1]
  rw [← integral_biUnion_finset P (fun p _ => measurableSet_Ico) hdisj
    (fun p hp => hint.mono_set (hsubJ p hp))]
  exact setIntegral_mono_set hint (Filter.Eventually.of_forall fun x => hg x)
    (LE.le.eventuallyLE (Set.iUnion₂_subset fun p hp => hsubJ p hp))

/-- **The square transfer.**  `Σ_ν δ_ν² ≤ (2n²/L²)(½ + 2∫_0^1 S_n²) + 2L/n⁴`. -/
theorem fareyL2Discrepancy_le_meanSquare {n : ℕ} (hn : 1 ≤ n) :
    fareyL2Discrepancy n ≤ 2 * (n : ℝ) ^ 2 / ((fareySet n).card : ℝ) ^ 2
        * (1 / 2 + 2 * ∫ x in (0 : ℝ)..1, fareySawtooth n x ^ 2)
      + 2 * ((fareySet n).card : ℝ) / (n : ℝ) ^ 4 := by
  set L : ℝ := ((fareySet n).card : ℝ) with hL
  set h : ℝ := 1 / (n : ℝ) ^ 2 with hh
  set P := (fareySet n).filter (fun p => fareyValue p < 1) with hP
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hh0 : 0 < h := by positivity
  have hmem11 : ((1 : ℕ), (1 : ℕ)) ∈ fareySet n :=
    mem_fareySet.mpr ⟨⟨le_rfl, hn⟩, ⟨le_rfl, hn⟩, le_rfl, Nat.coprime_one_left 1⟩
  have hLpos : 0 < L := by
    rw [hL]; exact_mod_cast card_pos.mpr ⟨_, hmem11⟩
  set K := ∑ k ∈ Ioc 0 n, |(mertensIoc (n / k) : ℝ)| / 2 with hK
  have hKb : ∀ x, |fareySawtooth n x| ≤ K := abs_fareySawtooth_le n
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hKb 0)
  set g : ℝ → ℝ := fun x => (1 / 2 + fareySawtooth n x) ^ 2 with hg
  have hgint : IntegrableOn g (Set.Ioc 0 1) :=
    integrableOn_Ioc_zero_one_of_abs_le
      ((measurable_const.add (measurable_fareySawtooth n)).pow_const 2) ((1 / 2 + K) ^ 2)
      fun x => by
        simp only [hg]
        rw [abs_pow]
        refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
        refine (abs_add_le _ _).trans ?_
        rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
        linarith [hKb x]
  -- the fractions equal to `1` contribute nothing
  have hsplit : fareyL2Discrepancy n = ∑ p ∈ P, (L * fareyValue p - fareyRank n p) ^ 2 / L ^ 2 := by
    unfold fareyL2Discrepancy
    rw [← sum_filter_add_sum_filter_not (fareySet n) (fun p => fareyValue p < 1)]
    have hzero : ∑ p ∈ (fareySet n).filter (fun p => ¬ fareyValue p < 1),
        (fareyValue p - (fareyRank n p : ℝ) / ((fareySet n).card : ℝ)) ^ 2 = 0 := by
      refine sum_eq_zero fun p hp => ?_
      obtain ⟨hp0, hp1⟩ := mem_filter.mp hp
      have hfeq : fareyValue p = 1 := le_antisymm (fareyValue_le_one hp0) (not_lt.mp hp1)
      rw [hfeq, fareyRank_eq_card_of_fareyValue_eq_one hfeq, div_self hLpos.ne', sub_self]
      ring
    rw [hzero, add_zero]
    refine sum_congr rfl fun p _ => ?_
    rw [show fareyValue p - (fareyRank n p : ℝ) / L = (L * fareyValue p - fareyRank n p) / L by
      field_simp, div_pow]
  have hloc : ∀ p ∈ P, h * ((L * fareyValue p - fareyRank n p) ^ 2 / 2 - L ^ 2 * h ^ 2)
      ≤ ∫ x in Set.Ico (fareyValue p) (fareyValue p + h), g x := by
    intro p hp
    obtain ⟨hp0, hp1⟩ := mem_filter.mp hp
    obtain ⟨hf0, hfh⟩ := fareyValue_pos_and_add_le hn hp0 hp1
    have hsub : Set.Ico (fareyValue p) (fareyValue p + h) ⊆ Set.Ioc 0 1 := fun x hx =>
      ⟨lt_of_lt_of_le hf0 hx.1, by linarith [hx.2]⟩
    have hpt : ∀ x ∈ Set.Ico (fareyValue p) (fareyValue p + h),
        (L * fareyValue p - fareyRank n p) ^ 2 / 2 - L ^ 2 * h ^ 2 ≤ g x := by
      intro x hx
      have h1 := abs_card_mul_sub_fareyRank_le hn hp0 hp1 hx
      have h2 : (L * fareyValue p - fareyRank n p) ^ 2
          ≤ (|1 / 2 + fareySawtooth n x| + L * h) ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) h1 2
      have h3 : (|1 / 2 + fareySawtooth n x| + L * h) ^ 2
          ≤ 2 * (1 / 2 + fareySawtooth n x) ^ 2 + 2 * (L * h) ^ 2 := by
        have := sq_nonneg (|1 / 2 + fareySawtooth n x| - L * h)
        rw [← sq_abs (1 / 2 + fareySawtooth n x)]
        nlinarith
      simp only [hg]
      nlinarith
    have hint1 : IntegrableOn (fun _ : ℝ => (L * fareyValue p - fareyRank n p) ^ 2 / 2
        - L ^ 2 * h ^ 2) (Set.Ico (fareyValue p) (fareyValue p + h)) :=
      (integrableOn_Ioc_zero_one_of_abs_le measurable_const _ fun _ => le_rfl).mono_set hsub
    have hmono := setIntegral_mono_on hint1 (hgint.mono_set hsub) measurableSet_Ico hpt
    rw [setIntegral_const, Real.volume_real_Ico, smul_eq_mul,
      show max (fareyValue p + h - fareyValue p) 0 = h by
        rw [add_sub_cancel_left, max_eq_left hh0.le]] at hmono
    exact hmono
  have hunion := sum_setIntegral_fareyIco_le hn (g := g) (fun x => sq_nonneg _) hgint
  have hIoc : ∫ x in Set.Ioc (0 : ℝ) 1, g x
      ≤ 1 / 2 + 2 * ∫ x in (0 : ℝ)..1, fareySawtooth n x ^ 2 := by
    have hsq : IntegrableOn (fun x => fareySawtooth n x ^ 2) (Set.Ioc 0 1) :=
      integrableOn_Ioc_zero_one_of_abs_le ((measurable_fareySawtooth n).pow_const 2) (K ^ 2)
        fun x => by
          rw [abs_pow]
          exact pow_le_pow_left₀ (abs_nonneg _) (hKb x) 2
    have hint2 : IntegrableOn (fun x => 1 / 2 + 2 * fareySawtooth n x ^ 2) (Set.Ioc 0 1) :=
      (integrableOn_Ioc_zero_one_of_abs_le measurable_const _ fun _ => le_rfl).add
        (hsq.const_mul 2)
    refine (setIntegral_mono_on hgint hint2 measurableSet_Ioc fun x _ => ?_).trans_eq ?_
    · simp only [hg]
      nlinarith [sq_nonneg (1 / 2 - fareySawtooth n x)]
    · rw [integral_add (integrableOn_Ioc_zero_one_of_abs_le measurable_const _ fun _ => le_rfl)
        (hsq.const_mul 2), integral_const_mul, setIntegral_const, Real.volume_real_Ioc,
        intervalIntegral.integral_of_le zero_le_one]
      norm_num
  have hsum : h * ∑ p ∈ P, (L * fareyValue p - fareyRank n p) ^ 2 / 2
      - h * ((P.card : ℝ) * (L ^ 2 * h ^ 2))
        ≤ 1 / 2 + 2 * ∫ x in (0 : ℝ)..1, fareySawtooth n x ^ 2 := by
    have h1 := sum_le_sum hloc
    have e : ∑ p ∈ P, h * ((L * fareyValue p - fareyRank n p) ^ 2 / 2 - L ^ 2 * h ^ 2)
        = h * ∑ p ∈ P, (L * fareyValue p - fareyRank n p) ^ 2 / 2
          - h * ((P.card : ℝ) * (L ^ 2 * h ^ 2)) := by
      rw [← mul_sum, sum_sub_distrib, sum_const, nsmul_eq_mul]
      ring
    rw [e] at h1
    linarith
  have hPcard : (P.card : ℝ) ≤ L := by rw [hL]; exact_mod_cast card_filter_le _ _
  have hhn : (n : ℝ) ^ 2 * h = 1 := by rw [hh]; field_simp
  set Q : ℝ := 1 / 2 + 2 * ∫ x in (0 : ℝ)..1, fareySawtooth n x ^ 2 with hQ
  have hDsum : ∑ p ∈ P, (L * fareyValue p - fareyRank n p) ^ 2
      ≤ 2 * (n : ℝ) ^ 2 * Q + 2 * L ^ 3 * h ^ 2 := by
    have hcard : h * ((P.card : ℝ) * (L ^ 2 * h ^ 2)) ≤ h * (L * (L ^ 2 * h ^ 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hPcard (by positivity)) hh0.le
    have h1 : h * ∑ p ∈ P, (L * fareyValue p - fareyRank n p) ^ 2
        ≤ 2 * Q + 2 * h * (L * (L ^ 2 * h ^ 2)) := by
      rw [← sum_div] at hsum
      linarith
    have h2 := mul_le_mul_of_nonneg_left h1 (sq_nonneg (n : ℝ))
    calc ∑ p ∈ P, (L * fareyValue p - fareyRank n p) ^ 2
        = ((n : ℝ) ^ 2 * h) * ∑ p ∈ P, (L * fareyValue p - fareyRank n p) ^ 2 := by
          rw [hhn, one_mul]
      _ = (n : ℝ) ^ 2 * (h * ∑ p ∈ P, (L * fareyValue p - fareyRank n p) ^ 2) := by ring
      _ ≤ (n : ℝ) ^ 2 * (2 * Q + 2 * h * (L * (L ^ 2 * h ^ 2))) := h2
      _ = 2 * (n : ℝ) ^ 2 * Q + 2 * ((n : ℝ) ^ 2 * h) * (L ^ 3 * h ^ 2) := by ring
      _ = 2 * (n : ℝ) ^ 2 * Q + 2 * L ^ 3 * h ^ 2 := by rw [hhn]; ring
  rw [hsplit, ← sum_div]
  calc (∑ p ∈ P, (L * fareyValue p - fareyRank n p) ^ 2) / L ^ 2
      ≤ (2 * (n : ℝ) ^ 2 * Q + 2 * L ^ 3 * h ^ 2) / L ^ 2 :=
        div_le_div_of_nonneg_right hDsum (by positivity)
    _ = 2 * (n : ℝ) ^ 2 / L ^ 2 * Q + 2 * L / (n : ℝ) ^ 4 := by
        rw [hh]; field_simp


theorem fareyL2Discrepancy_nonneg (n : ℕ) : 0 ≤ fareyL2Discrepancy n :=
  sum_nonneg fun _ _ => sq_nonneg _

theorem fareyL2Discrepancy_le_card (n : ℕ) : fareyL2Discrepancy n ≤ (fareySet n).card := by
  unfold fareyL2Discrepancy
  calc ∑ p ∈ fareySet n, (fareyValue p - (fareyRank n p : ℝ) / ((fareySet n).card : ℝ)) ^ 2
      ≤ ∑ _p ∈ fareySet n, (1 : ℝ) := by
        refine sum_le_sum fun p hp => ?_
        obtain ⟨⟨ha1, _⟩, ⟨hq1, _⟩, _, _⟩ := mem_fareySet.mp hp
        have hq0 : (0 : ℝ) < p.2 := by exact_mod_cast hq1
        have hf0 : 0 ≤ fareyValue p := by unfold fareyValue; positivity
        have hf1 := fareyValue_le_one hp
        have hr0 : 0 ≤ (fareyRank n p : ℝ) / ((fareySet n).card : ℝ) := by positivity
        have hr1 : (fareyRank n p : ℝ) / ((fareySet n).card : ℝ) ≤ 1 := by
          have hc : fareyRank n p ≤ (fareySet n).card := card_filter_le _ _
          rcases Nat.eq_zero_or_pos (fareySet n).card with h0 | hpos
          · rw [h0, Nat.cast_zero, div_zero]; norm_num
          · rw [div_le_one (by exact_mod_cast hpos)]; exact_mod_cast hc
        nlinarith
    _ = (fareySet n).card := by simp

/-- `(Σ_ν |δ_ν|)² ≤ L Σ_ν δ_ν²`. -/
theorem sq_fareyL1Discrepancy_le (n : ℕ) :
    fareyL1Discrepancy n ^ 2 ≤ (fareySet n).card * fareyL2Discrepancy n := by
  unfold fareyL1Discrepancy fareyL2Discrepancy
  have h := sq_sum_le_card_mul_sum_sq (s := fareySet n)
    (f := fun p => |fareyValue p - (fareyRank n p : ℝ) / ((fareySet n).card : ℝ)|)
  simpa only [sq_abs] using h

theorem natCast_rpow_le_four_mul_succ_rpow {n : ℕ} (hn : 1 ≤ n) {e : ℝ} (he : -2 ≤ e) :
    (n : ℝ) ^ e ≤ 4 * ((n : ℝ) + 1) ^ e := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rcases le_or_gt 0 e with he0 | he0
  · calc (n : ℝ) ^ e ≤ ((n : ℝ) + 1) ^ e := Real.rpow_le_rpow hn0.le (by linarith) he0
      _ ≤ 4 * ((n : ℝ) + 1) ^ e := by
          have : 0 ≤ ((n : ℝ) + 1) ^ e := by positivity
          linarith
  · have hsplit : (n : ℝ) ^ e = ((n : ℝ) + 1) ^ e * ((n : ℝ) / ((n : ℝ) + 1)) ^ e := by
      rw [← Real.mul_rpow (by positivity) (by positivity)]
      congr 1
      field_simp
    have hq : ((n : ℝ) / ((n : ℝ) + 1)) ^ e = (((n : ℝ) + 1) / n) ^ (-e) := by
      rw [Real.rpow_neg (by positivity), ← Real.inv_rpow (by positivity), inv_div]
    have hle2 : ((n : ℝ) + 1) / n ≤ 2 := by
      rw [div_le_iff₀ hn0]; linarith
    have hge1 : (1 : ℝ) ≤ ((n : ℝ) + 1) / n := by
      rw [le_div_iff₀ hn0]; linarith
    have hbound : (((n : ℝ) + 1) / n) ^ (-e) ≤ 4 := by
      calc (((n : ℝ) + 1) / n) ^ (-e) ≤ (2 : ℝ) ^ (-e) :=
            Real.rpow_le_rpow (by positivity) hle2 (by linarith)
        _ ≤ (2 : ℝ) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 4 := by norm_num
    rw [hsplit, hq, mul_comm]
    exact mul_le_mul_of_nonneg_right hbound (by positivity)

/-- **Farey square discrepancy from a Mertens power bound.**  If `|M(N)| ≤ C (N+1)^a` with
`½ ≤ a ≤ 1`, then `Σ_ν δ_ν² = O(n^{2a-2+δ})` for every `δ > 0`. -/
theorem fareyL2Discrepancy_le_of_mertens_rpow_bound {a C : ℝ} (ha : 1 / 2 ≤ a) (ha1 : a ≤ 1)
    (hC0 : 0 ≤ C) (hC : ∀ N : ℕ, ‖mobiusMertensPartialSum N‖ ≤ C * ((N : ℝ) + 1) ^ a)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ n : ℕ,
      fareyL2Discrepancy n ≤ C' * ((n : ℝ) + 1) ^ (2 * a - 2 + δ) := by
  set B : ℝ := 2 * C with hB
  have hB0 : 0 ≤ B := by positivity
  set K : ℝ := (1 + 3 / δ) ^ 3 with hK
  set C₁ : ℝ := 4 * (258 + 256 * B ^ 2 * K / 3) with hC₁
  set e : ℝ := 2 * a - 2 + δ with he
  have he2 : -2 ≤ e := by rw [he]; linarith
  refine ⟨max C₁ (2 ^ 32), le_trans (by positivity) (le_max_right _ _), fun n => ?_⟩
  have hn1R : (0 : ℝ) ≤ n := n.cast_nonneg
  have hpowlow : ((n : ℝ) + 1) ^ (-2 : ℝ) ≤ ((n : ℝ) + 1) ^ e :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) he2
  rcases lt_or_ge n 256 with hn | hn
  · have h1 := fareyL2Discrepancy_le_card n
    have h2 : ((fareySet n).card : ℝ) ≤ 65536 := by
      have h3 : (fareySet n).card ≤ 65536 :=
        le_trans (card_fareySet_le n) (by
          have : n ^ 2 ≤ 256 ^ 2 := Nat.pow_le_pow_left hn.le 2
          simpa using this)
      exact_mod_cast h3
    have h4 : (1 : ℝ) / 65536 ≤ ((n : ℝ) + 1) ^ (-2 : ℝ) := by
      rw [Real.rpow_neg (by positivity), Real.rpow_two, one_div]
      have : ((n : ℝ) + 1) ^ 2 ≤ 65536 := by
        have : (n : ℝ) + 1 ≤ 256 := by exact_mod_cast (show n + 1 ≤ 256 from hn)
        nlinarith
      exact inv_anti₀ (by positivity) this
    calc fareyL2Discrepancy n ≤ 65536 := h1.trans h2
      _ = 2 ^ 32 * (1 / 65536) := by norm_num
      _ ≤ 2 ^ 32 * ((n : ℝ) + 1) ^ e := by
          gcongr
          exact h4.trans hpowlow
      _ ≤ max C₁ (2 ^ 32) * ((n : ℝ) + 1) ^ e :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  · have hn1 : 1 ≤ n := by omega
    have hn256 : (256 : ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (0 : ℝ) < n := by linarith
    have hnR1 : (1 : ℝ) ≤ n := by linarith
    have htr := fareyL2Discrepancy_le_meanSquare hn1
    have hQ := integral_sq_fareySawtooth_le hB0 ha n
      (fun k hk hkn => abs_mertensIoc_div_mul_rpow_le_of_bound (by linarith) ha1 hC hk hkn)
    have hL16 := card_fareySet_ge hn
    have hLpos : 0 < ((fareySet n).card : ℝ) := lt_of_lt_of_le (by positivity) hL16
    have hLle : ((fareySet n).card : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast card_fareySet_le n
    have hratio : 2 * (n : ℝ) ^ 2 / ((fareySet n).card : ℝ) ^ 2 ≤ 512 / (n : ℝ) ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : ((n : ℝ) ^ 2 / 16) ^ 2 ≤ ((fareySet n).card : ℝ) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hL16 2
      nlinarith
    have htail : 2 * ((fareySet n).card : ℝ) / (n : ℝ) ^ 4 ≤ 2 / (n : ℝ) ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have hlogle : 1 + Real.log n ≤ (1 + 3 / δ) * (n : ℝ) ^ (δ / 3) := by
      have h1 := Real.log_le_rpow_div (x := n) hn0.le (by positivity : 0 < δ / 3)
      have h2 : 1 ≤ (n : ℝ) ^ (δ / 3) := Real.one_le_rpow hnR1 (by positivity)
      have e1 : (n : ℝ) ^ (δ / 3) / (δ / 3) = 3 / δ * (n : ℝ) ^ (δ / 3) := by field_simp
      rw [e1] at h1
      nlinarith
    have hcube : (1 + Real.log n) ^ 3 ≤ K * (n : ℝ) ^ δ := by
      have h0 : 0 ≤ 1 + Real.log n := by linarith [Real.log_natCast_nonneg n]
      have h3 : ((n : ℝ) ^ (δ / 3)) ^ 3 = (n : ℝ) ^ δ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
        congr 1
        push_cast
        ring
      calc (1 + Real.log n) ^ 3 ≤ ((1 + 3 / δ) * (n : ℝ) ^ (δ / 3)) ^ 3 :=
            pow_le_pow_left₀ h0 hlogle 3
        _ = K * (n : ℝ) ^ δ := by rw [mul_pow, h3]
    have hna : ((n : ℝ) ^ a) ^ 2 = (n : ℝ) ^ (2 * a) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
      congr 1
      push_cast
      ring
    have hQ0 : 0 ≤ ∫ x in (0 : ℝ)..1, fareySawtooth n x ^ 2 :=
      intervalIntegral.integral_nonneg zero_le_one fun x _ => sq_nonneg _
    have hmain : 1 / 2 + 2 * ∫ x in (0 : ℝ)..1, fareySawtooth n x ^ 2
        ≤ 1 / 2 + B ^ 2 / 6 * K * (n : ℝ) ^ (2 * a + δ) := by
      have h1 : B ^ 2 / 12 * ((n : ℝ) ^ a) ^ 2 * (1 + Real.log n) ^ 3
          ≤ B ^ 2 / 12 * (n : ℝ) ^ (2 * a) * (K * (n : ℝ) ^ δ) := by
        rw [hna]
        exact mul_le_mul_of_nonneg_left hcube (by positivity)
      have h2 : (n : ℝ) ^ (2 * a) * (n : ℝ) ^ δ = (n : ℝ) ^ (2 * a + δ) :=
        (Real.rpow_add hn0 _ _).symm
      have h3 : B ^ 2 / 12 * (n : ℝ) ^ (2 * a) * (K * (n : ℝ) ^ δ)
          = B ^ 2 / 12 * K * (n : ℝ) ^ (2 * a + δ) := by rw [← h2]; ring
      linarith [hQ, h1, h3]
    have hpow : (n : ℝ) ^ (2 * a + δ) / (n : ℝ) ^ 2 = (n : ℝ) ^ e := by
      rw [he, show 2 * a - 2 + δ = (2 * a + δ) - 2 by ring, Real.rpow_sub hn0, Real.rpow_two]
    have hinv2 : 1 / (n : ℝ) ^ 2 ≤ (n : ℝ) ^ e := by
      have : (n : ℝ) ^ (-2 : ℝ) ≤ (n : ℝ) ^ e := Real.rpow_le_rpow_of_exponent_le hnR1 he2
      rwa [Real.rpow_neg hn0.le, Real.rpow_two, ← one_div] at this
    have h4 := natCast_rpow_le_four_mul_succ_rpow hn1 he2
    have hfin : fareyL2Discrepancy n ≤ (258 + 256 * B ^ 2 * K / 3) * (n : ℝ) ^ e := by
      have hA : 0 ≤ 1 / 2 + 2 * ∫ x in (0 : ℝ)..1, fareySawtooth n x ^ 2 := by positivity
      calc fareyL2Discrepancy n
          ≤ 2 * (n : ℝ) ^ 2 / ((fareySet n).card : ℝ) ^ 2
              * (1 / 2 + 2 * ∫ x in (0 : ℝ)..1, fareySawtooth n x ^ 2)
            + 2 * ((fareySet n).card : ℝ) / (n : ℝ) ^ 4 := htr
        _ ≤ 512 / (n : ℝ) ^ 2 * (1 / 2 + B ^ 2 / 6 * K * (n : ℝ) ^ (2 * a + δ))
            + 2 / (n : ℝ) ^ 2 :=
            add_le_add (mul_le_mul hratio hmain hA (by positivity)) htail
        _ = 258 * (1 / (n : ℝ) ^ 2)
            + 256 * B ^ 2 * K / 3 * ((n : ℝ) ^ (2 * a + δ) / (n : ℝ) ^ 2) := by
            field_simp; ring
        _ ≤ 258 * (n : ℝ) ^ e + 256 * B ^ 2 * K / 3 * (n : ℝ) ^ e := by
            rw [hpow]
            gcongr
        _ = (258 + 256 * B ^ 2 * K / 3) * (n : ℝ) ^ e := by ring
    calc fareyL2Discrepancy n ≤ (258 + 256 * B ^ 2 * K / 3) * (n : ℝ) ^ e := hfin
      _ ≤ (258 + 256 * B ^ 2 * K / 3) * (4 * ((n : ℝ) + 1) ^ e) :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = C₁ * ((n : ℝ) + 1) ^ e := by rw [hC₁]; ring
      _ ≤ max C₁ (2 ^ 32) * ((n : ℝ) + 1) ^ e :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)

/-- **Lower half of the square exponent law.**  `Σ_ν δ_ν² ≤ C (n+1)^{2b-2}` with `b ≥ 0` forces
`Θ ≤ b`. -/
theorem zetaZeroAbscissa_le_of_fareyL2Discrepancy_le {C b : ℝ} (hb : 0 ≤ b)
    (h : ∀ n : ℕ, fareyL2Discrepancy n ≤ C * ((n : ℝ) + 1) ^ (2 * b - 2)) :
    zetaZeroAbscissa ≤ b := by
  set C' : ℝ := max C 0 with hC'
  refine zetaZeroAbscissa_le_of_fareyL1Discrepancy_le (C := √C') hb fun n => ?_
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hL : ((fareySet n).card : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by
    have : ((fareySet n).card : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast card_fareySet_le n
    nlinarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  have h2 : fareyL2Discrepancy n ≤ C' * ((n : ℝ) + 1) ^ (2 * b - 2) :=
    (h n).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have hsq := sq_fareyL1Discrepancy_le n
  have hpow : ((n : ℝ) + 1) ^ 2 * ((n : ℝ) + 1) ^ (2 * b - 2) = (((n : ℝ) + 1) ^ b) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hn1, ← Real.rpow_natCast, ← Real.rpow_mul hn1.le]
    congr 1
    push_cast
    ring
  have hbound : fareyL1Discrepancy n ^ 2 ≤ (√C' * ((n : ℝ) + 1) ^ b) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (le_max_right _ _), ← hpow]
    calc fareyL1Discrepancy n ^ 2 ≤ ((fareySet n).card : ℝ) * fareyL2Discrepancy n := hsq
      _ ≤ ((n : ℝ) + 1) ^ 2 * (C' * ((n : ℝ) + 1) ^ (2 * b - 2)) :=
          mul_le_mul hL h2 (fareyL2Discrepancy_nonneg n) (by positivity)
      _ = C' * (((n : ℝ) + 1) ^ 2 * ((n : ℝ) + 1) ^ (2 * b - 2)) := by ring
  exact abs_le_of_sq_le_sq' hbound (by positivity) |>.2

/-- **Upper half of the square exponent law.**  `Σ_ν δ_ν² = O(n^{2b-2})` for every `b > Θ`. -/
theorem exists_fareyL2Discrepancy_le_rpow_of_zetaZeroAbscissa_lt {b : ℝ}
    (hb : zetaZeroAbscissa < b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, fareyL2Discrepancy n ≤ C * ((n : ℝ) + 1) ^ (2 * b - 2) := by
  set ε : ℝ := b - zetaZeroAbscissa with hε
  have hε0 : 0 < ε := by linarith
  have hΘ := half_le_zetaZeroAbscissa
  set a : ℝ := min (zetaZeroAbscissa + ε / 2) 1 with ha
  have ha1 : a ≤ 1 := min_le_right _ _
  have ha2 : a ≤ zetaZeroAbscissa + ε / 2 := min_le_left _ _
  have ha0 : 1 / 2 ≤ a := le_min (by linarith) (by norm_num)
  obtain ⟨C, hC0, hC⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      ‖mobiusMertensPartialSum N‖ ≤ C * ((N : ℝ) + 1) ^ a := by
    rcases le_total (zetaZeroAbscissa + ε / 2) 1 with hle | hle
    · obtain ⟨C, hC0, hC⟩ := mobiusMertens_subpower_zetaZeroAbscissa (ε / 2) (by positivity)
      refine ⟨C, hC0, fun N => ?_⟩
      rw [ha, min_eq_left hle]
      exact hC N
    · refine ⟨1, zero_le_one, fun N => ?_⟩
      rw [ha, min_eq_right hle, Real.rpow_one, one_mul]
      exact norm_mobiusMertensPartialSum_le_add_one N
  obtain ⟨C', hC'0, hC'⟩ := fareyL2Discrepancy_le_of_mertens_rpow_bound ha0 ha1 hC0 hC
    (δ := ε) hε0
  refine ⟨C', hC'0, fun n => (hC' n).trans ?_⟩
  refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le ?_ ?_) hC'0
  · linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  · rcases le_total (zetaZeroAbscissa + ε / 2) 1 with hle | hle
    · rw [ha, min_eq_left hle]; linarith
    · rw [ha, min_eq_right hle]; linarith

/-- **Franel's criterion.**  The Riemann hypothesis holds if and only if
`Σ_ν (f_ν - ν/L)² = O(n^{-1+δ})` for every `δ > 0`. -/
theorem riemannHypothesis_iff_fareyL2Discrepancy_le :
    RiemannHypothesis ↔ ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      fareyL2Discrepancy n ≤ C * ((n : ℝ) + 1) ^ (-1 + δ) := by
  constructor
  · intro hRH δ hδ
    have hΘ := zetaZeroAbscissa_eq_half_of_riemannHypothesis hRH
    obtain ⟨C, hC0, hC⟩ := exists_fareyL2Discrepancy_le_rpow_of_zetaZeroAbscissa_lt
      (b := 1 / 2 + δ / 2) (by rw [hΘ]; linarith)
    refine ⟨C, hC0, fun n => ?_⟩
    have := hC n
    rwa [show 2 * (1 / 2 + δ / 2) - 2 = -1 + δ by ring] at this
  · intro h
    refine riemannHypothesis_of_zetaZeroAbscissa_eq_half
      (le_antisymm ?_ half_le_zetaZeroAbscissa)
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨C, _, hC⟩ := h (2 * ε) (by positivity)
    have := zetaZeroAbscissa_le_of_fareyL2Discrepancy_le (C := C) (b := 1 / 2 + ε)
      (by positivity) fun n => by
        rw [show 2 * (1 / 2 + ε) - 2 = -1 + 2 * ε by ring]
        exact hC n
    linarith

end

end RHTower
